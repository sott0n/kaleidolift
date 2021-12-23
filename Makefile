test:
	cargo fmt -- --check
	cargo clippy -- -D warnings
	RUST_BACKTRACE=1 cargo test --all

clean:
	rm -rf .dsgit

.PHONY: test clean
