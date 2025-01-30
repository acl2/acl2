# WGDT-MVP1-Backend

This directory contains the backend for MVP1 of WGDT.

# Prerequisites
- Python 3 and pip modules `flask` and `flask-cors`. You may wish to use a virtual environment.
- ACL2 + ACL2s, setup as described in the [scripts](https://gitlab.com/acl2s/external-tool-support/scripts) repo.
- `make`
- [Quicklisp](https://www.quicklisp.org)

# Usage
Whenever any of the ACL2 files change, the server image must be
recertified and rebuilt. This can be done by running `make` in this
directory. The first time this is run it may take a while, as it
requires several other community ACL2 books to be certified.

Then, run the `server.py` file using Python in this directory. e.g.,
`python3 server.py`.
