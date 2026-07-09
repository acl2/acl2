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
    "(run-jsonrpc-server 7070 nil '(struct-type-split) state)")
   (xdoc::p
    "See the documentation of each method (e.g. @(see struct-type-split-method))
     for its request @('params') format and an example request."))
  :order-subtopics t)
