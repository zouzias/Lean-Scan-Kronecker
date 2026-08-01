.PHONY: lint update-mathlib update

lint:
	lake lint

all: lint
	lake build

update-mathlib:
	lake update mathlib

update:
	elan self update
