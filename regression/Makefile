TESTS=test001 test002 test003 test004 test005 test006 test007 test008 test009 test010 test011 test012 test013 test014 test015 test016 test017 test018 test019 test020 test021 test022 test023
ANALYSIS_TESTS=test106

RC=../src/rc.opt

.PHONY: check $(TESTS)
.PHONY: checkAnalysis $(ANALYSIS_TESTS)

check: $(TESTS)

$(TESTS): %: %.expr
	@$(RC) $< && cat $@.input | ./$@ > $@.log && diff $@.log orig/$@.log
	@cat $@.input | $(RC) -i $< > $@.log && diff $@.log orig/$@.log
	@cat $@.input | $(RC) -s $< > $@.log && diff $@.log orig/$@.log


checkAnalysis: $(ANALYSIS_TESTS)
$(ANALYSIS_TESTS): %: %.expr
	@cat $@.input | $(RC) -o $< > $@.log && diff $@.log orig/$@.log

clean:
	rm -f *.s *~ *.log $(TESTS)
	pushd expressions && make clean && popd
	pushd deep-expressions && make clean && popd
