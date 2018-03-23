PROOF_PATH = tests/proofs
EVAL_PATH = tests/eval
CPUS = 2
BACKEND = dafny
PYTEST_ARGS = --tb=short -v -n $(CPUS) --backend $(BACKEND)

test: test-eval test-proof

test-eval:
	pytest $(PYTEST_ARGS) $(EVAL_PATH)

test-proof:
	pytest $(PYTEST_ARGS) $(PROOF_PATH)