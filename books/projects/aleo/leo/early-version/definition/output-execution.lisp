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
(include-book "value-expressions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ output-execution
  :parents (dynamic-semantics)
  :short "Execution of output files."
  :long
  (xdoc::topstring
   (xdoc::p
    "Executing an output file amounts to evaluating its expression.
     This is not used for program execution,
     but rather to check correct program execution."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-output-expression ((outexpr output-expressionp) (curve curvep))
  :returns (val value-resultp)
  :short "Evaluate an output expression."
  (b* ((expr (output-expression->get outexpr))
       ((unless (expression-valuep expr))
        (reserrf (list :not-value-expression expr))))
    (value-expr-to-value expr curve))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-output-item ((outitem output-itemp) (curve curvep))
  :returns (val value-resultp)
  :short "Evaluate an output item."
  (eval-output-expression (output-item->get outitem) curve)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-output-section ((outsec output-sectionp) (curve curvep))
  :returns (val value-resultp)
  :short "Evaluate an output section."
  (eval-output-item (output-section->item outsec) curve)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-output-file ((outfile output-filep) (curve curvep))
  :returns (val value-resultp)
  :short "Evaluate an output file."
  (eval-output-section (output-file->get outfile) curve)
  :hooks (:fix))
