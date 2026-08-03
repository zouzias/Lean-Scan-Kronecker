.PHONY: lint all update-mathlib update blueprint

lint:
	lake lint

all: lint
	lake build

update-mathlib:
	lake update mathlib

update:
	elan self update

blueprint:
	leanblueprint web
