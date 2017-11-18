default: tests.log

test:
	@../test.pl -c ../../../src/fastsynth/fastsynth

tests.log: ../test.pl
	@../test.pl -c ../../../src/fastsynth/fastsynth

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
