# Unicode Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

# An image with the implementations of Unicode that ../icu-oracle.py and
# ../python-oracle.py need for the three supported versions:
#
#   ICU 76.1 (Unicode 16.0.0), ICU 78.3 (Unicode 17.0.0) and
#   ICU 79.1 (Unicode 18.0.0), built from their sources by build-icu.sh;
#
#   the Python module unicodedata2 18.0.0 (Unicode 18.0.0).
#
# Build it from the directory validation of the library:
#
#   docker build -t unicode-oracles -f icu/Dockerfile .
#
# Run it on the directory in which ../run.sh has written its files
# (acl2-16.0.0.txt and so on); see compare-all.sh:
#
#   docker run --rm --user "$(id -u):$(id -g)" \
#          -v /tmp/unicode-validation:/work unicode-oracles
#
# See the section "Validation" of ../../README.md.

FROM ubuntu:24.04

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
               ca-certificates g++ git make python3 python3-venv \
    && rm -rf /var/lib/apt/lists/*

# The releases of ICU, each with the commit that its tag names.
COPY icu/build-icu.sh icu/data-filter.json /opt/unicode/validation/icu/
RUN /opt/unicode/validation/icu/build-icu.sh release-76-1 \
        8eca245c7484ac6cc179e3e5f7c1ea7680810f39 /opt/icu/16.0.0
RUN /opt/unicode/validation/icu/build-icu.sh release-78.3 \
        21d1eb0f306e1141c10931e914dfc038c06121da /opt/icu/17.0.0
RUN /opt/unicode/validation/icu/build-icu.sh release-79.1 \
        ddc6b66926bfac6036144ca9902992a0d6d50af9 /opt/icu/18.0.0

RUN python3 -m venv /opt/unicodedata2 \
    && /opt/unicodedata2/bin/pip install --no-cache-dir unicodedata2==18.0.0

COPY compare.py icu-oracle.py python-oracle.py /opt/unicode/validation/
COPY icu/compare-all.sh /opt/unicode/validation/icu/

CMD ["/opt/unicode/validation/icu/compare-all.sh", "/work"]
