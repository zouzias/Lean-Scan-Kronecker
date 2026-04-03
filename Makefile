.PHONY: update


update-mathlib:
	lake update mathlib

update:
	elan self update
