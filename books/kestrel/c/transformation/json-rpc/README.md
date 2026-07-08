This directory contains a JSON-RPC 2.0 interface to the Kestrel C-to-C
transformations.

It is built on the JSON-RPC library in `books/kestrel/jsonrpc` (see the
`jsonrpc` XDOC topic) and is the JSON-RPC analogue of the command-line/JSON
interface in `books/kestrel/c/transformation/command-line`.  Each supported
transformation is exposed as a JSON-RPC method.  Currently the only supported
method is `struct-type-split`; further methods will be added over time.

Setup:

0. Build and install ACL2.  (See https://acl2.org/doc/?topic=ACL2____INSTALLATION.  You probably want to install the latest development snapshot, not a release tarball, so you can easily get access to updated transformations).

1. Ensure you can run cert.pl.  (See https://acl2.org/doc/?topic=BUILD____PRELIMINARIES)

2. Certify the books in this directory: cert.pl -j8 *.lisp

Usage (socket transport):

3. Start the server (it builds a saved ACL2 image on the first run, which is
   slow; subsequent runs are fast):

     ./server.sh [PORT]

   PORT defaults to 7070.  The server binds to localhost only and accepts
   connections sequentially.  Filepaths in requests (`old-dir`, `new-dir`,
   `files`) are resolved relative to the current working directory of the
   server process.

4. Send a JSON-RPC 2.0 request.  Each message must be compact (single-line)
   JSON terminated by a newline.  For example (see tests/example-request.json
   for the multi-line, human-readable form of a struct-type-split request):

     {"jsonrpc": "2.0", "method": "struct-type-split", "params": {"old-dir": "input-files", "new-dir": "out", "files": ["test1.c"], "struct-tag": "point", "right-members": ["z"], "new-tag": "point_right", "preprocess": false}, "id": 1}

   A quick way to send it with netcat:

     cat tests/example-request.json | tr -d '\n' | (cat; echo) | nc localhost 7070

Methods:

Each supported transformation is a JSON-RPC method whose name matches the
transformation, and whose `params` is a JSON object whose member names mirror
the transformation's keyword arguments (and those of `input-files` /
`output-files`) as strings without leading colons.  See the XDOC for the
individual methods for their parameters; e.g. `struct-type-split-method`.

On success the JSON-RPC `result` is method-specific.  Malformed requests and
failures are reported as JSON-RPC errors.

The transformations themselves are documented here:
https://acl2.org/doc/?topic=C2C____TRANSFORMATION-TOOLS

Testing:

  - tests/struct-type-split.lsp is a manual unit-test script (not certified /
    not part of the build) for the struct-type-split method.
  - tests/test-malformed-requests.sh fires malformed (and one valid) requests
    at a running server and checks the returned error codes.  Start the server
    from the tests/ directory first (so request paths resolve), then run the
    script:

      cd tests && ../server.sh 7070      # in one terminal
      cd tests && ./test-malformed-requests.sh 7070   # in another

Updating:

After updating ACL2 (e.g., by doing a 'git pull'), rebuild ACL2, re-certify the
books (e.g. `cert.pl -j8 top.lisp`), and re-run the server (server.sh re-saves
the image automatically when the books change).
