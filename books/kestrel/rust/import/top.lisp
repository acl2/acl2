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
