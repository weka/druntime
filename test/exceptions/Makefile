# set from top makefile
OS:=
MODEL:=
DMD:=
DRUNTIME:=
DRUNTIMESO:=
QUIET:=
LINKDL:=

SRC:=src
ROOT:=./obj/$(OS)/$(MODEL)
TESTS:=stderr_msg unittest_assert
ifeq ($(OS)-$(BUILD),linux-debug)
	TESTS:=$(TESTS) line_trace
	DIFF:=diff
	SED:=sed
endif

ifneq (default,$(MODEL))
	MODEL_FLAG:=-m$(MODEL)
endif
CFLAGS:=$(MODEL_FLAG) -Wall
DFLAGS:=$(MODEL_FLAG) -w -I../../src -I../../import -I$(SRC) -L$(DRUNTIME) -defaultlib= -debuglib=

.PHONY: all clean
all: $(addprefix $(ROOT)/,$(addsuffix .done,$(TESTS)))

$(ROOT)/%.done: $(ROOT)/%
	@echo Testing $*
	$(QUIET)$(ROOT)/$* $(RUN_ARGS)
	@touch $@

$(ROOT)/stderr_msg.done: $(ROOT)/stderr_msg
	@echo Testing stderr_msg
	$(QUIET)./$(ROOT)/stderr_msg $(RUN_ARGS) 2>&1 1>/dev/null | grep -qF "stderr_msg msg"
	@touch $@

$(ROOT)/unittest_assert.done: $(ROOT)/unittest_assert
	@echo Testing unittest_assert
	$(QUIET)./$(ROOT)/unittest_assert $(RUN_ARGS) 2>&1 1>/dev/null | grep -qF "unittest_assert msg"
	@touch $@

$(ROOT)/line_trace.done: $(ROOT)/line_trace
	@echo Testing line_trace
	@rm -f line_trace.output
	$(QUIET)./$(ROOT)/line_trace $(RUN_ARGS) >line_trace.output
	$(QUIET)$(SED) "s/\[0x[0-9a-f]*\]/\[ADDR\]/g" line_trace.output | $(DIFF) line_trace.exp -
	@touch $@

$(ROOT)/unittest_assert: DFLAGS+=-unittest
$(ROOT)/line_trace: DFLAGS+=-L--export-dynamic
$(ROOT)/%: $(SRC)/%.d
	$(QUIET)$(DMD) $(DFLAGS) -of$@ $<

clean:
	rm -rf obj
