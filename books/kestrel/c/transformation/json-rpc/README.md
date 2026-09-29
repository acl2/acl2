This directory contains a JSON-RPC 2.0 interface to the Kestrel C-to-C
transformations.  It is built on the JSON-RPC library in `books/kestrel/jsonrpc`,
and supports the transformations of the command-line interface in
`books/kestrel/c/transformation/command-line`, and more.

The interface is documented in the `c-transformation-json-rpc` XDOC topic:
https://acl2.org/doc/?topic=C2C____C-TRANSFORMATION-JSON-RPC
That topic describes the model (the server keeps named "code ensembles", which
methods read, transform, and write), the common parameters, the error codes,
and has links to the documentation of each method.

Setup:

0. Build and install ACL2.  (See https://acl2.org/doc/?topic=ACL2____INSTALLATION.  You probably want to install the latest development snapshot, not a release tarball, so you can easily get access to updated transformations).

1. Ensure you can run cert.pl.  (See https://acl2.org/doc/?topic=BUILD____PRELIMINARIES)

2. Certify the books in this directory: cert.pl -j8 top.lisp

Usage:

3. Start the server (it builds a saved ACL2 image on the first run, which is
   slow; subsequent runs are fast):

     ./server.sh [PORT]

   PORT defaults to 7070.  The server binds to localhost only.  File paths in
   requests are resolved relative to the current working directory of the
   server process.

4. Send JSON-RPC 2.0 requests.  Each message must be compact (single-line)
   JSON terminated by a newline.  For example, with the server started in the
   `tests` directory, this sends the batch in tests/example-request.json, which
   reads a file, splits a struct type, and writes the result to `out`:

     cat tests/example-request.json | tr -d '\n' | (cat; echo) | nc localhost 7070

Testing:

  - tests/methods.lisp is a certified test book for the methods.
  - tests/test-malformed-requests.sh fires malformed (and valid) requests at a
    running server and checks the returned error codes.  Start the server
    from the tests/ directory first (so request paths resolve), then run the
    script:

      cd tests && ../server.sh 7070      # in one terminal
      cd tests && ./test-malformed-requests.sh 7070   # in another

Updating:

After updating ACL2 (e.g., by doing a 'git pull'), rebuild ACL2, re-certify the
books (e.g. `cert.pl -j8 top.lisp`), and re-run the server (server.sh re-saves
the image automatically when the books change).
