module core.internal.lifetime;

import core.lifetime : forward;

/+
emplaceRef is a package function for druntime internal use. It works like
emplace, but takes its argument by ref (as opposed to "by pointer").
This makes it easier to use, easier to be safe, and faster in a non-inline
build.
Furthermore, emplaceRef optionally takes a type parameter, which specifies
the type we want to build. This helps to build qualified objects on mutable
buffer, without breaking the type system with unsafe casts.
+/
void emplaceRef(T, UT, Args...)(ref UT chunk, auto ref Args args)
{
    static if (args.length == 0)
    {
        static assert(is(typeof({static T i;})),
            "Cannot emplace a " ~ T.stringof ~ " because " ~ T.stringof ~
            ".this() is annotated with @disable.");
        static if (is(T == class)) static assert(!__traits(isAbstractClass, T),
            T.stringof ~ " is abstract and it can't be emplaced");
        emplaceInitializer(chunk);
    }
    else static if (
        !is(T == struct) && Args.length == 1 /* primitives, enums, arrays */
        ||
        Args.length == 1 && is(typeof({T t = forward!(args[0]);})) /* conversions */
        ||
        is(typeof(T(forward!args))) /* general constructors */)
    {
        static struct S
        {
            T payload;
            this()(auto ref Args args)
            {
                static if (is(typeof(payload = forward!args)))
                    payload = forward!args;
                else
                    payload = T(forward!args);
            }
        }
        if (__ctfe)
        {
            static if (is(typeof(chunk = T(forward!args))))
                chunk = T(forward!args);
            else static if (args.length == 1 && is(typeof(chunk = forward!(args[0]))))
                chunk = forward!(args[0]);
            else assert(0, "CTFE emplace doesn't support "
                ~ T.stringof ~ " from " ~ Args.stringof);
        }
        else
        {
            S* p = () @trusted { return cast(S*) &chunk; }();
            static if (UT.sizeof > 0)
                emplaceInitializer(*p);
            p.__ctor(forward!args);
        }
    }
    else static if (is(typeof(chunk.__ctor(forward!args))))
    {
        // This catches the rare case of local types that keep a frame pointer
        emplaceInitializer(chunk);
        chunk.__ctor(forward!args);
    }
    else
    {
        //We can't emplace. Try to diagnose a disabled postblit.
        static assert(!(Args.length == 1 && is(Args[0] : T)),
            "Cannot emplace a " ~ T.stringof ~ " because " ~ T.stringof ~
            ".this(this) is annotated with @disable.");

        //We can't emplace.
        static assert(false,
            T.stringof ~ " cannot be emplaced from " ~ Args[].stringof ~ ".");
    }
}

// ditto
static import core.internal.traits;
void emplaceRef(UT, Args...)(ref UT chunk, auto ref Args args)
if (is(UT == core.internal.traits.Unqual!UT))
{
    emplaceRef!(UT, UT)(chunk, forward!args);
}

/+
Emplaces T.init.
In contrast to `emplaceRef(chunk)`, there are no checks for disabled default
constructors etc.
+/
void emplaceInitializer(T)(scope ref T chunk) nothrow pure @trusted
    if (!is(T == const) && !is(T == immutable) && !is(T == inout))
{
    static if (is(T U == shared U))
        alias Unshared = U;
    else
        alias Unshared = T;

    __emplaceInitializer!Unshared(chunk);
}

template __emplaceInitializer(T) {
    import core.internal.traits : hasElaborateAssign;
    static if (__traits(isZeroInit, T))
    {
        void __emplaceInitializer(T)(scope ref T chunk) nothrow pure @trusted @nogc {
            import core.stdc.string : memset;
            memset(cast(void*) &chunk, 0, T.sizeof);
        }
    }
    else static if (T.sizeof <= 16 && !hasElaborateAssign!T && __traits(compiles, (){ T chunk; chunk = T.init; }))
    {
        void __emplaceInitializer(T)(scope ref T chunk) nothrow pure @trusted @nogc {
            chunk = T.init;
        }
    }
    else static if (is(T U : U[N], size_t N)) // if isStaticArray
    {
        void __emplaceInitializer(T)(scope ref T chunk) nothrow pure @trusted @nogc
        {
            foreach (i; 0..N)
            {
                emplaceInitializer(chunk[i]);
            }
        }
    }
    else
    {
        // Avoid stack allocation by hacking to get to the init symbol.
         pragma(mangle, "_D" ~ T.mangleof[1..$] ~ "6__initZ")
        __gshared extern immutable typeof(T.init) initializer;

        void __emplaceInitializer(T)(scope ref T chunk) nothrow pure @trusted @nogc
        {
            import core.stdc.string : memcpy;
            memcpy(cast(void*)&chunk, &initializer, T.sizeof);
        }
    }
}

@safe unittest
{
    static void testInitializer(T)()
    {
        // mutable T
        {
            T dst = void;
            emplaceInitializer(dst);
            // Poor man's comparison solution here. Cannot do "==" or "is" because that is not generic enough.
            T init;
            import core.stdc.string;
            () @trusted { memcmp(&dst, &init, T.sizeof); }();
        }

        // shared T
        {
            shared T dst = void;
            emplaceInitializer(dst);
            // Poor man's comparison solution here. Cannot do "==" or "is" because that is not generic enough.
            T init;
            import core.stdc.string;
            () @trusted { memcmp(cast(void*)&dst, &init, T.sizeof); }();
        }

        // const T
        {
            const T dst = void;
            static assert(!__traits(compiles, emplaceInitializer(dst)));
        }
    }

    static struct ElaborateAndZero
    {
        int a;
        this(this) {}
    }

    static struct ElaborateAndNonZero
    {
        int a = 42;
        this(this) {}
    }

    testInitializer!int();
    testInitializer!double();
    testInitializer!(double[4])();
    testInitializer!(char[4])();
    testInitializer!ElaborateAndZero();
    testInitializer!ElaborateAndNonZero();
}

@safe unittest
{
    enum LARGE_ARRAY_SIZE = 10_000_000;
    // Test emplaceInitializer for very large data objects for which stack allocation cannot be used.
    {
        auto largeCharArray = new char[LARGE_ARRAY_SIZE];
        enum i = 10; // arbitrary index
        largeCharArray[i] = 55;
        emplaceInitializer!(char[LARGE_ARRAY_SIZE])(largeCharArray[0..LARGE_ARRAY_SIZE]);
        assert(largeCharArray[i] == 0xFF);
    }

    {
        static struct LargeNonElaborate
        {
            char[LARGE_ARRAY_SIZE] a;
        }
        auto p = new LargeNonElaborate();
        enum i = 11; // arbitrary index
        p.a[i] = 55;
        emplaceInitializer(*p);
        assert(p.a[i] == 0xFF);
    }

    {
        static struct LargeNonElaborateInitSymbol
        {
            char[LARGE_ARRAY_SIZE/2] a;
            int i;
            char[LARGE_ARRAY_SIZE/2] a;
        }
        auto p = new LargeNonElaborateInitSymbol();
        enum i = 11; // arbitrary index
        p.a[i] = 55;
        emplaceInitializer(*p);
        assert(p.a[i] == 0xFF);
    }
}