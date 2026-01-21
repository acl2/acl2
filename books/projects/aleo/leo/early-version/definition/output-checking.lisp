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
(include-book "type-checking")
(include-book "value-expressions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ output-checking
  :parents (static-semantics)
  :short "Static checks on output files."
  :long
  (xdoc::topstring
   (xdoc::p
    "These check static semantic requirements on Leo output files.
     The checks also calculate information from the output file.")
   (xdoc::p
    "This is currently very simple,
     because an output file consists of, essentially, an expression.")
   (xdoc::p
    "An output file is checked in the context of
     the static environment of the program."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-output-expression ((outexpr output-expressionp) (env senvp))
  :returns (type type-resultp)
  :short "Check an output expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The expression must be a value expression.
     We type-check it in the initial (i.e. empty) static environment."))
  (b* ((expr (output-expression->get outexpr))
       ((unless (expression-valuep expr))
        (reserrf (list :not-value-expression expr)))
       ((okf etype) (typecheck-expression expr env)))
    (expr-type->type etype))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-output-item ((outitem output-itemp) (env senvp))
  :returns (type type-resultp)
  :short "Check an output item."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the underlying output expression, returning its type."))
  (check-output-expression (output-item->get outitem) env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-output-section ((outsec output-sectionp) (env senvp))
  :returns (type type-resultp)
  :short "Check an output section."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the underlying output item."))
  (check-output-item (output-section->item outsec) env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-output-file ((outfile output-filep) (env senvp))
  :returns (type type-resultp)
  :short "Check an output file."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the underlying output section."))
  (check-output-section (output-file->get outfile) env)
  :hooks (:fix))
