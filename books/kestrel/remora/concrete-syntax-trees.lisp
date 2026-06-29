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

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc concrete-syntax-trees
  :parents (concrete-syntax parsing-and-printing)
  :short "Concrete syntax trees (CSTs)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our ABNF library defines a notion of "
    (xdoc::seetopic "abnf::tree" "trees")
    ", whose leaves may be either lists of natural numbers or rule names.
     It also defines a notion of "
    (xdoc::seetopic "abnf::tree-terminatedp" "terminated trees")
    ", i.e. trees whose leaves are
     lists of natural numbers and not rule names.")
   (xdoc::p
    "Remora CSTs are formalized as terminated trees from our ABNF library.")))
