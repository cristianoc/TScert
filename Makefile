# TScert: an independent checker, proved in Lean, for TypeScript type claims.
# `make help` lists the targets.

OUT ?= $(or $(TMPDIR),/tmp)/semantic-diff.html
REV ?= HEAD

.PHONY: help setup build build-lean build-producer test suite cases check lowering compiler-api-shapes semantic-diff deck fmt \
  check-fmt setup-git-hooks clean-store census build-runner

help: ## list the targets
	@grep -E '^[a-z-]+:.*## ' $(MAKEFILE_LIST) | sed -E 's/:.*## /\t/' | expand -t 16

setup: ## install the node dependencies (tools, the library fixture's Node types, Prettier) and link the fixtures' installations
	npm ci --prefix tools
	npm ci --prefix pipeline/library-project
	npm install --no-save
	node pipeline/fixture-links.mts

build: build-lean build-producer build-runner ## build the Lean verifier, the OCaml producer and the stage runner

RUNNER := pipeline/runner/_build/stage-runner

build-runner: $(RUNNER) ## build the stage runner, which reports the CPU time of process stages

$(RUNNER): pipeline/runner/stage-runner.c
	mkdir -p $(dir $@)
	cc -O2 -Wall -Wextra -Werror -o $@ $<

build-lean: ## build the Lean verifier
	cd lean && lake build --log-level=warning

build-producer: ## build the OCaml producer
	dune build --root ocaml-producer

test: build ## build, then the fast checks and the controls no case can make (replayed from the stage store)
	@./test-all.sh

suite: build ## build, then the pipeline cases
	node pipeline/run-cases.mts

cases: ## the pipeline cases whose file names contain P (all of them when P is empty)
	node pipeline/run-cases.mts $(P)

check: ## one source file through the pipeline: FILE=path.ts [PROJECT=dir]
	node pipeline/verify-source.mts $(FILE) $(if $(PROJECT),--project $(PROJECT))

clean-store: ## remove stage entries, timeouts and the source snapshots no running process holds; FORGET_HOST=h counts host h's owners stopped (TSCERT_STAGE_STORE, default ~/.cache/tscert/stages)
	node pipeline/stages.mts clean $(if $(FORGET_HOST),--forget-host=$(FORGET_HOST))

census: ## the census of a directory's functions: DIR=tools, FILES=a.mts,…, FUNCTIONS=f,…, SHARD=i/n; a record per run; each stage limited to 300 s unless TSCERT_STEP_LIMIT says otherwise; TSCERT_RETRY_TIMEOUTS=1 runs recorded timeouts again
	TSCERT_STEP_LIMIT=$${TSCERT_STEP_LIMIT:-300} node dev/census.mts $(if $(DIAGNOSTIC),--diagnostic) --dir $(or $(DIR),tools) $(if $(FILES),--files $(FILES)) $(if $(FUNCTIONS),--functions $(FUNCTIONS)) $(if $(SHARD),--shard $(SHARD))

lowering: ## the program graph a source lowers to: FILE=path.ts [FN=function]
	node dev/lowering-dump.mts $(FILE) $(FN)

compiler-api-shapes: ## C3: every node of the corpus holds the members its shape states required, or a correction covers them
	node tests/compiler-api-shapes.mts

deck: ## build the deep-dive deck NAME (docs/deep-dives/NAME/deck.mts): its project/ files, the format and layout checks, and a page to view it; OPEN=1 opens the page; SINCE=rev marks on the page what changed since rev
	node dev/deck-cli.mts $(NAME) $(if $(OPEN),--open) $(if $(SINCE),--since $(SINCE))

semantic-diff: ## render the commit records of REV (a commit or base..tip, default HEAD) to OUT and open it
	node dev/commit-records.mts --out $(OUT) $(REV)
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
