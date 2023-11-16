#!/bin/bash

pushd ../hand-proof-checker
tar -cf ../hand-proof-parser-xtext/checker.tar --exclude='*.core' .
popd
docker build . -t xtext-checker -f Dockerfile-server
