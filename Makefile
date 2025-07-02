.PHONY: test fail
test:
	stack run -- examples/nat.agda

.PHONY: fail
fail:
	-stack run -- examples/fail/postulate-with-definition.agda
	-stack run -- examples/fail/definition-without-type.agda

.PHONY: build
build:
	make -C src

# EOF
