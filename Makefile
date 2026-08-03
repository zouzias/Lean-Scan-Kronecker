.PHONY: lint all update-mathlib update blueprint

lint:
	lake lint
	lake exe mk_all

all: lint
	lake build

update-mathlib:
	lake update mathlib

update:
	elan self update

blueprint:
	leanblueprint web
