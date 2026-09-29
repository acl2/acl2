This directory contains a JSON-RPC 2.0 interface to the Kestrel C-to-C
transformations.

It is built on the JSON-RPC library in `books/kestrel/jsonrpc` (see the
`jsonrpc` XDOC topic) and is the JSON-RPC analogue of the command-line/JSON
interface in `books/kestrel/c/transformation/command-line`.  Each supported
transformation is exposed as a JSON-RPC method.  Currently the only supported
transformation is `struct-type-split`; further methods will be added over time.

The server keeps an environment of named code ensembles, which persists across
requests and connections.  The `input-files` method reads C files into a named
code ensemble, each transformation method transforms a named code ensemble into
another, and the `output-files` method writes a named code ensemble to files.
Thus the files need to be read only once, however many transformations are
applied to them, and transformations can be chained without writing and
re-reading files.  The `list-ensembles` and `drop-ensemble` methods list and
remove code ensembles.

Setup:

0. Build and install ACL2.  (See https://acl2.org/doc/?topic=ACL2____INSTALLATION.  You probably want to install the latest development snapshot, not a release tarball, so you can easily get access to updated transformations).

1. Ensure you can run cert.pl.  (See https://acl2.org/doc/?topic=BUILD____PRELIMINARIES)

2. Certify the books in this directory: cert.pl -j8 *.lisp

Usage (socket transport):

3. Start the server (it builds a saved ACL2 image on the first run, which is
   slow; subsequent runs are fast):

     ./server.sh [PORT]

   PORT defaults to 7070.  The server binds to localhost only and accepts
   connections sequentially.  Filepaths in requests (`base-dir`, `files`) are
   resolved relative to the current working directory of the server process.

4. Send JSON-RPC 2.0 requests.  Each message must be compact (single-line)
   JSON terminated by a newline.  For example, these three requests read a
   file, split a struct type, and write the result:

     {"jsonrpc": "2.0", "method": "input-files", "params": {"target": "orig", "base-dir": "input-files", "files": ["test1.c"], "preprocess": false}, "id": 1}
     {"jsonrpc": "2.0", "method": "struct-type-split", "params": {"source": "orig", "target": "split", "struct-tag": "point", "right-members": ["z"], "new-tag": "point_right", "safety-checks": false}, "id": 2}
     {"jsonrpc": "2.0", "method": "output-files", "params": {"source": "split", "base-dir": "out"}, "id": 3}

   The server processes a batch (a JSON array of requests) in order, so the
   three steps can also be sent in one message.  See tests/example-request.json
   for the multi-line, human-readable form of such a batch.

   A quick way to send it with netcat:

     cat tests/example-request.json | tr -d '\n' | (cat; echo) | nc localhost 7070

  **NOTE**: This example assumes the server was started in the `tests` directory.
  The `tests/example-request.json` request contains relative paths
  which are resolved against the server's current working directory.

Methods:

  - `input-files`: read C files into a named code ensemble.
  - `output-files`: write a named code ensemble to files.
  - `list-ensembles`: list the names of the code ensembles in the environment.
  - `drop-ensemble`: remove a code ensemble from the environment.
  - One method per supported transformation, named after the transformation,
    which transforms the code ensemble named by `source` into one named by
    `target`.

The `params` of each method is a JSON object whose member names mirror the
keyword arguments of the corresponding event (`input-files`, `output-files`, or
the transformation) as strings without leading colons, plus `source`, `target`,
and `overwrite` where applicable.  Binding a name that is already bound is an
error unless `overwrite` is true.  See the XDOC for the individual methods for
their parameters; e.g. `input-files-method` and `struct-type-split-method`.

On success the JSON-RPC `result` is method-specific.  Malformed requests and
failures are reported as JSON-RPC errors.

The transformations themselves are documented here:
https://acl2.org/doc/?topic=C2C____TRANSFORMATION-TOOLS

Testing:

  - tests/methods.lisp is a certified test book for the methods.
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
