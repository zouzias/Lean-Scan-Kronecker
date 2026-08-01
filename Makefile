.PHONY: update-mathlib update

all:
	lake build

update-mathlib:
	lake update mathlib

update:
	elan self update
