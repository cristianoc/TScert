# TScert: an independent checker, proved in Lean, for TypeScript type claims.
# `make help` lists the targets.

OUT ?= $(or $(TMPDIR),/tmp)/semantic-diff.html
REV ?= HEAD

.PHONY: help setup build build-lean build-producer test suite cases check lowering semantic-diff fmt \
  check-fmt setup-git-hooks

help: ## list the targets
	@grep -E '^[a-z-]+:.*## ' $(MAKEFILE_LIST) | sed -E 's/:.*## /\t/' | expand -t 16

setup: ## install the node dependencies (tools, the library fixture's Node types, Prettier)
	npm ci --prefix tools
	npm ci --prefix pipeline/library-project
	npm install --no-save

build: build-lean build-producer ## build the Lean verifier and the OCaml producer

build-lean: ## build the Lean verifier
	cd lean && lake build --log-level=warning

build-producer: ## build the OCaml producer
	dune build --root ocaml-producer

test: ## the fast checks: front-end types, JSON field names, assertions, documents, rule inventory
	@./test-all.sh

suite: build ## build, then the pipeline cases and the controls no case can make
	node pipeline/test.mts

cases: ## the pipeline cases whose file names contain P (all of them when P is empty)
	node pipeline/run-cases.mts $(P)

check: ## one source file through the pipeline: FILE=path.ts [PROJECT=dir]
	node pipeline/verify-source.mts $(FILE) $(if $(PROJECT),--project $(PROJECT))

lowering: ## the program graph a source lowers to: FILE=path.ts [FN=function]
	node tools/lowering-dump.mts $(FILE) $(FN)

semantic-diff: ## render the commit records of REV (a commit or base..tip, default HEAD) to OUT and open it
	node tools/commit-records.mts --out $(OUT) $(REV)
	@if command -v open >/dev/null; then open $(OUT); \
	elif command -v xdg-open >/dev/null; then xdg-open $(OUT); fi

fmt: ## format with Prettier
	npx prettier --write .

check-fmt: ## check formatting with Prettier
	npx prettier --check .

# the commit-record check on every commit
.git/hooks/commit-msg: bin/git_hooks/commit_record.sh
	ln -s $(PWD)/bin/git_hooks/commit_record.sh .git/hooks/commit-msg

setup-git-hooks: .git/hooks/commit-msg ## install the commit-record check
