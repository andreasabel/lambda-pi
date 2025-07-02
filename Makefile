.PHONY: test
test:
	stack run -- examples/nat.agda

.PHONY: build
build:
	make -C src

# EOF
