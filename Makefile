DAY=10
CPP=c++
CPPFLAGS=-Wall -Wpedantic

.PHONY: default
default: soln_$(DAY) inputs/$(DAY).txt
	./$< inputs/$(DAY).txt

soln_%: solns/d%.cpp
	$(CPP) $(CPPFLAGS) $< -o $@

.PHONY: clean
clean:
	rm -f soln_*
