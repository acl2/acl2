; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/jsonrpc/top" :dir :system)

(include-book "code-env")
(include-book "drop-ensemble")
(include-book "input-files")
(include-book "list-ensembles")
(include-book "output-files")
(include-book "struct-type-split")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ c-transformation-json-rpc
  :parents (transformation-tools)
  :short "A JSON-RPC 2.0 interface to the Kestrel C-to-C transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a "
    (xdoc::seetopic "jsonrpc::jsonrpc" "JSON-RPC 2.0")
    " interface to the "
    (xdoc::seetopic "c2c::transformation-tools" "C-to-C transformations")
    ".  Each supported transformation is exposed as a JSON-RPC method.")
   (xdoc::p
    "The server keeps an environment of named code ensembles (see @(see
     code-env)), which persists across requests.  The @('input-files') method
     reads C files into a named code ensemble, each transformation method
     transforms a named code ensemble into another, and the @('output-files')
     method writes a named code ensemble to files.  Thus the files need to be
     read only once, however many transformations are applied to them, and
     transformations can be chained without writing and re-reading files.  The
     @('list-ensembles') and @('drop-ensemble') methods list and remove code
     ensembles.  Since the
     server processes a batch of requests in order, a batch of
     @('input-files'), a transformation, and @('output-files') requests
     performs all three steps in one round trip.")
   (xdoc::p
    "The normal way to serve requests over a TCP socket is the shell script
     @('server.sh') in @('books/kestrel/c/transformation/json-rpc').  It builds
     a saved ACL2 image (on the first run) and starts the server on the given
     port (default 7070):")
   (xdoc::codeblock
    "books/kestrel/c/transformation/json-rpc/server.sh [PORT]")
   (xdoc::p
    "The script ultimately calls @(see jsonrpc::run-jsonrpc-server) with the
     supported methods in the allowed-methods list; that function may also be
     invoked directly from within ACL2:")
   (xdoc::codeblock
    "(run-jsonrpc-server 7070 nil"
    "                    '(input-files output-files"
    "                      list-ensembles drop-ensemble"
    "                      struct-type-split)"
    "                    state)")
   (xdoc::p
    "See the documentation of each method (e.g. @(see struct-type-split-method))
     for its request @('params') format and an example request."))
  :order-subtopics t)
