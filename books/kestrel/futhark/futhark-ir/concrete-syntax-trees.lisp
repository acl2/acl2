; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ concrete-syntax-trees
  :parents (concrete-syntax parsing-and-printing)
  :short "Concrete syntax trees (CSTs) for Futhark IR."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ABNF library defines a notion of "
    (xdoc::seetopic "abnf::tree" "trees")
    ", whose leaves may be lists of natural numbers or rule names, and a
     notion of "
    (xdoc::seetopic "abnf::tree-terminatedp" "terminated trees")
    ", whose leaves are lists of natural numbers.")
   (xdoc::p
    "Futhark IR CSTs are ABNF trees produced by @(see parser) from lists of
     Unicode code points.  They preserve the grammar structure and the exact
     code points consumed for tokens, whitespace, and comments.")
   (xdoc::p
    "These CSTs are an internal representation in the parsing pipeline.
     @(see syntax-abstraction) maps them to the FTY ASTs used by the rest of
     the Futhark IR front end."))
  :order-subtopics t
  :default-parent t)
