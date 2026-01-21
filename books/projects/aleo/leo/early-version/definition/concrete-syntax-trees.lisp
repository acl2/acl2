; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc concrete-syntax-trees
  :parents (concrete-syntax)
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
    "Leo CSTs are formalized as terminated trees from our ABNF library.")))
