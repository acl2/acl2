; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "grammar")
(include-book "concrete-syntax-trees")
(include-book "extra-grammatical-restrictions")
(include-book "parser")
(include-book "post-parsing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ concrete-syntax
  :parents (remora)
  :short "Concrete syntax of Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "The concrete syntax of Remora defines
     which Unicode character sequences
     form syntactically valid Remora code,
     and how such sequences are organized into constructs.")
   (xdoc::p
    "The concrete syntax of Remora is formalized via ABNF grammar rules,
     along with some side conditions (extra-grammatical constraints)
     that are mentioned in source code
     comments (in the file @('grammar.abnf')).
     The side conditions are enforced during or immediately after parsing.")
   (xdoc::p
    "Parsing in the narrow sense (see @(tsee parser)) means applying the
     grammar rules to an input sequence to create
     @(tsee concrete-syntax-trees).  During parsing some side conditions
     such as ``[SC1] max-munch tokenization'' are enforced.")
   (xdoc::p
    "The remaining side conditions are enforced by @(tsee post-parsing)."))
  :order-subtopics (; we may want to elaborate on unicode-characters
                    grammar
                    concrete-syntax-trees
                    extra-grammatical-restrictions
                    parser
                    post-parsing))
