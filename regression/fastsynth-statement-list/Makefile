default: tests.log

test:
	@../test.pl -c "../../../src/fastsynth/fastsynth --incremental"

tests.log: ../test.pl
	@../test.pl -c "../../../src/fastsynth/fastsynth --incremental"

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.awl" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
