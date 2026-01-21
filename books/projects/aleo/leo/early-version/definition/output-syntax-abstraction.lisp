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

(include-book "output-files")
(include-book "syntax-abstraction")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ output-syntax-abstraction
  :parents (abstract-syntax)
  :short "Mapping from concrete to abstract syntax, for Leo output files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(see syntax-abstraction),
     and partly based on it,
     but for Leo output files instead of Leo code files."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-output-expression ((tree abnf::treep))
  :returns (outexpr output-expression-resultp)
  :short "Abstract an @('output-expression') to an output expression."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "output-expression"))
       ((okf expr) (abs-expression tree)))
    (output-expression expr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-output-item ((tree abnf::treep))
  :returns (outitem output-item-resultp)
  :short "Abstract an @('output-item') to an input item."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "output-item"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf outexpr) (abs-output-expression tree))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-ichars tree ";")))
    (output-item outexpr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-output-section ((tree abnf::treep))
  :returns (outsec output-section-resultp)
  :short "Abstract an @('output-section') to an output section."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "output-section"))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf outitem) (abs-output-item tree)))
    (output-section outitem))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-output-file ((tree abnf::treep))
  :returns (outfile output-file-resultp)
  :short "Abstract an @('output-file') to an output file."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "output-file"))
       ((okf outsec) (abs-output-section tree)))
    (output-file outsec))
  :hooks (:fix))
