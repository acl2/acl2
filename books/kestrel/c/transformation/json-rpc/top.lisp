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

(include-book "add-section-attr")
(include-book "code-env")
(include-book "drop-ensemble")
(include-book "input-files")
(include-book "list-ensembles")
(include-book "output-files")
(include-book "simpadd0")
(include-book "split-fn")
(include-book "split-gso")
(include-book "struct-type-split")
(include-book "wrap-fn")

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
    ".  Clients send requests to a server to read C files,
     to transform them, and to write the results,
     each step being a separate request.
     No knowledge of ACL2 is needed to use it.")
   (xdoc::section
    "Code Ensembles"
    (xdoc::p
     "The server keeps an environment of named <i>code ensembles</i>.  A code
      ensemble is a set of C files that have been read, parsed, and checked
      together, along with the settings used to read them (such as the GCC or
      Clang extensions).  The environment persists across requests and
      connections, until the server stops.  See @(see code-env) for details.")
    (xdoc::p
     "The @('input-files') method reads C files into a new code ensemble, each
      transformation method transforms a code ensemble into a new one, and the
      @('output-files') method writes a code ensemble to files.  Thus the files
      need to be read only once, however many transformations are tried on
      them, and transformations can be chained without writing and re-reading
      files.  The @('list-ensembles') and @('drop-ensemble') methods list and
      remove code ensembles."))
   (xdoc::section
    "Common Parameters"
    (xdoc::p
     "The @('params') of each request must be a JSON Object (i.e. by-name
      parameters), except for @('list-ensembles'), which takes none.  Each
      parameter may appear at most once, and unknown parameters are rejected.
      The transformation methods share the following parameters.")
    (xdoc::desc
     "@('\"input-ensemble\"') &mdash; required"
     (xdoc::p
      "A string naming the code ensemble to transform."))
    (xdoc::desc
     "@('\"output-ensemble\"') &mdash; required"
     (xdoc::p
      "A string naming the transformed code ensemble.  It may be the same as
       @('\"input-ensemble\"'), in which case the transformed code ensemble
       replaces the original one.  If the transformation fails, the
       environment is unchanged."))
    (xdoc::desc
     "@('\"overwrite\"') &mdash; optional, default @('false')"
     (xdoc::p
      "A boolean that must be @('true') if @('\"output-ensemble\"') already
       names a code ensemble, which is then replaced.  This guards against
       replacing a code ensemble by mistake.")))
   (xdoc::section
    "Methods"
    (xdoc::p
     "The following methods manage the environment:")
    (xdoc::ul
     (xdoc::li (xdoc::seetopic "input-files-method" "@('input-files')")
               ": read C files into a code ensemble.")
     (xdoc::li (xdoc::seetopic "output-files-method" "@('output-files')")
               ": write a code ensemble to files.")
     (xdoc::li (xdoc::seetopic "list-ensembles-method" "@('list-ensembles')")
               ": list the names of the code ensembles.")
     (xdoc::li (xdoc::seetopic "drop-ensemble-method" "@('drop-ensemble')")
               ": remove a code ensemble."))
    (xdoc::p
     "Each supported transformation is a method of the same name, whose
      parameters, besides the common ones above, are the transformation's
      inputs, named as in the transformation's documentation:")
    (xdoc::ul
     (xdoc::li (xdoc::seetopic "add-section-attr-method"
                               "@('add-section-attr')"))
     (xdoc::li (xdoc::seetopic "simpadd0-method" "@('simpadd0')"))
     (xdoc::li (xdoc::seetopic "split-fn-method" "@('split-fn')"))
     (xdoc::li (xdoc::seetopic "split-gso-method" "@('split-gso')"))
     (xdoc::li (xdoc::seetopic "struct-type-split-method"
                               "@('struct-type-split')"))
     (xdoc::li (xdoc::seetopic "wrap-fn-method" "@('wrap-fn')"))))
   (xdoc::section
    "Batches"
    (xdoc::p
     "The server processes the requests in a batch (a JSON Array of requests)
      in order.  So a batch of an @('input-files'), a transformation, and an
      @('output-files') request performs all three steps in one round trip,
      e.g.:")
    (xdoc::codeblock
     "[{\"jsonrpc\": \"2.0\", \"method\": \"input-files\","
     "  \"params\": {\"output-ensemble\": \"orig\","
     "             \"base-dir\": \"input-files\", \"files\": [\"test1.c\"]},"
     "  \"id\": 1},"
     " {\"jsonrpc\": \"2.0\", \"method\": \"struct-type-split\","
     "  \"params\": {\"input-ensemble\": \"orig\", \"output-ensemble\": \"split\","
     "             \"struct-tag\": \"point\", \"right-members\": [\"z\"]},"
     "  \"id\": 2},"
     " {\"jsonrpc\": \"2.0\", \"method\": \"output-files\","
     "  \"params\": {\"input-ensemble\": \"split\", \"base-dir\": \"out\"},"
     "  \"id\": 3}]"))
   (xdoc::section
    "Errors"
    (xdoc::p
     "Failures are reported as JSON-RPC errors, whose codes are:")
    (xdoc::ul
     (xdoc::li "@('-32700'): the message is not valid JSON.")
     (xdoc::li "@('-32600'): the message is not a valid JSON-RPC request.")
     (xdoc::li "@('-32601'): the method does not exist or is not allowed.")
     (xdoc::li "@('-32602'): the parameters are invalid, e.g. a required
                parameter is missing, a parameter has the wrong type,
                @('\"input-ensemble\"') names no code ensemble,
                or @('\"output-ensemble\"') names one
                and @('\"overwrite\"') is not @('true').")
     (xdoc::li "@('-32603'): the request is well-formed but fails, e.g. a file
                cannot be read or the transformation's conditions do not
                hold; the message describes the failure.")))
   (xdoc::section
    "Running the Server"
    (xdoc::p
     "The shell script @('server.sh') in
      @('books/kestrel/c/transformation/json-rpc') builds a saved ACL2 image
      (on the first run) and starts the server on the given port (default
      7070), bound to localhost only:")
    (xdoc::codeblock
     "books/kestrel/c/transformation/json-rpc/server.sh [PORT]")
    (xdoc::p
     "File paths in requests are relative to the server's current working
      directory.  Each message must be compact (single-line) JSON terminated by
      a newline.  The script calls @(see jsonrpc::run-jsonrpc-server) with the
      supported methods as the allowed methods; that function may also be
      called directly from within ACL2.")))
  :order-subtopics t)
