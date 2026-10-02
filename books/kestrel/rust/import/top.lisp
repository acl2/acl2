; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "charon-hashcons-expand")
(include-book "ullbc-to-mir")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ mir-import
  :parents (mir)
  :short "Importing MIR from JSON into the MIR abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "The importer reads MIR that was extracted from rustc
     and serialized as JSON,
     and maps it into the "
    (xdoc::seetopic "mir-abstract-syntax" "MIR abstract syntax")
    " so that extracted programs can be run by the interpreter
     and reasoned about.
     The importer is untrusted tooling:
     anything proved is proved about
     the resulting ACL2-side MIR program.")
   (xdoc::p
    "Extraction runs in two stages.
     First, the serialized JSON is normalized by
     expanding the serializer's node sharing
     (see @(see hashcons-expansion)).
     Then the normalized JSON is mapped onto
     the MIR abstract syntax
     (see @(see ullbc-to-mir-mapping))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc mir-import-tests
  :parents (mir-import)
  :short "Tests of the MIR importer."
  :long
  (xdoc::topstring
   (xdoc::p
    "The importer is exercised by @('import/aes-import-test.lisp'),
     run by the ACL2 regression (@('make regression') in @('books/'))
     but deliberately not included by @('import/top'), so building the
     library does not require running it or fetching its input.")
   (xdoc::p
    "It decompresses the committed serialized AES-128 crate
     (see @(see ullbc-to-mir-mapping) and @('samples/README.md')),
     runs the importer, and checks that the resulting MIR program is
     exactly the committed fixture @('*aes-fixslice-program*') that the
     interpreter tests (see @(see mir-tests)) run on.  This ties the
     two together: the importer is validated against the very program
     the interpreter is tested on.")))
