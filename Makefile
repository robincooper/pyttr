.PHONY: check fresh-install test

check:
	python3 scripts/check.py

fresh-install:
	python3 scripts/check.py --fresh-install-only

test:
	python3 -B -m unittest discover -s tests
