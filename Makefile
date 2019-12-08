# Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
# SPDX-License-Identifier: ISC

.PHONY: all check test clean bench test_release

CARGO_EXEC := $(shell command -v cargo 2>/dev/null)
XARGO_EXEC := $(shell command -v xargo 2>/dev/null)

all: deps check

deps:
	# Ensure `cargo` is installed and executable.
	ifndef CARGO_EXEC
		$(error '`cargo` could not be found in your `$PATH`. Is `rust` properly installed?')
	endif

check:
	@${CARGO_EXEC} check

test: check
	@echo "Running tests..."
	# Run tests only on the library.
	# TODO: Ensure docblock tests can also be run.
	@${CARGO_EXEC} test --lib --features="std"

bench: check
	@echo "Running benchmarks..."
	@${CARGO_EXEC} bench --bench="bench" --features="std,nightly"

test_release: check
	@echo "Running tests..."
	@${CARGO_EXEC} test --lib --features="std,nightly" --release

clean:
	@echo "Cleaning up..."
	@${CARGO_EXEC} clean

build_cuda:
	ifndef XARGO_EXEC
		$(error '`xargo` must be installed to compile for CUDA target.')
	endif

	${XARGO_EXEC} rustc --target nvptx64-nvidia-cuda -- --emit=asm
