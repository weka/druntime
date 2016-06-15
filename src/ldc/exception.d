/**
 * Contains compiler-recognized user-defined attribute types.
 *
 * Copyright: Authors 2016
 * License:   $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Authors:   Johan Engelen
 */
module ldc.exception;


/**
 * E
 *
 * Example:
 * ---
 * import ldc.exception;
 * ---
 */
extern(C)
Throwable getCurrentException() nothrow @nogc;