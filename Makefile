.PHONY: default
default: build test

.PHONY: test fail
test:
	stack run -- examples/nat.agda

.PHONY: fail
fail: fail-type

.PHONY: fail-type
fail-type:
	-stack run -- examples/fail/self-app.agda

.PHONY: fail-scope
fail-scope:
	-stack run -- examples/fail/not-in-scope.agda

.PHONY: fail-nice
fail-nice:
	-stack run -- examples/fail/postulate-with-definition.agda
	-stack run -- examples/fail/definition-without-type.agda

.PHONY: build
build:
	make -C src
	stack build

# EOF
