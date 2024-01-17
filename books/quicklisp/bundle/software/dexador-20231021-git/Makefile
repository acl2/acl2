all: test

.PHONY: build
build:
	docker build -t dexador-test-image -f t/Dockerfile .

.PHONY: test
test: build
	docker run --rm -i -v ${PWD}:/app dexador-test-image
