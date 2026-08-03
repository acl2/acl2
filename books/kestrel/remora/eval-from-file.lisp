; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "evaluation")
(include-book "parser-interface")
(include-book "type-checking")
(include-book "value-printing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the file-I/O entry point for evaluation.  It is kept in a separate
; book from evaluation.lisp so that the core evaluation logic does not have to
; depend on (and pay the certification-load cost of) the parser.

(define eval-from-file ((filename stringp) state &key ((limit natp) '1000000))
  :parents (evaluation)
  :returns (mv result state)
  :guard-hints (("Goal" :in-theory (enable exprp-when-result-not-error
                                           type+expr-p-when-result-not-error)))
  :short "Parse a Remora expression file, type-check it, evaluate it,
          and print the resulting value."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses the standalone Remora expression in @('filename')
     (via @(tsee parse-top-exp-from-file)),
     type-checks it (via @(tsee check-top-expr)),
     and evaluates it with @(tsee eval-top-expr), printing the resulting
     expression value in Remora concrete syntax via @(tsee print-expr-value).
     Returns @('(mv result state)'), where @('result') is the @(tsee expr-value)
     of the expression, or a @(tsee reserrp) when parsing, type checking,
     or evaluation fails.
     The expression that is evaluated is the one returned by the type checker
     (currently identical to the parsed one; see @(tsee check-top-expr)).")
   (xdoc::p
    "Printing the value fails only for float values with no literal syntax
     (see @(tsee float-value-to-float-lit)); in that case the raw value is
     printed instead, as an ACL2 object, and a message is emitted.")
   (xdoc::p
    "The @(':limit') keyword argument bounds the depth of the evaluation
     recursion, as explained in @(see eval-exprs/atoms/binds); evaluation
     fails with @('(reserr :limit)') if it is exhausted."))
  (b* (((mv ast state) (parse-top-exp-from-file filename state))
       ((when (reserrp ast))
        (b* ((- (cw "Parse error in ~s0: ~x1~%" filename ast)))
          (mv ast state)))
       (type+expr (check-top-expr ast))
       ((when (reserrp type+expr))
        (b* ((- (cw "Type checking ~s0 failed: ~x1~%" filename type+expr)))
          (mv type+expr state)))
       ((type+expr te) type+expr)
       (val (eval-top-expr te.expr limit))
       ((when (reserrp val))
        (b* ((- (cw "Evaluating ~s0 failed: ~x1~%" filename val)))
          (mv val state)))
       ((mv err str) (print-expr-value val))
       ((when err)
        (b* ((- (cw "Evaluating ~s0 produced an unprintable value: ~x1~%"
                   filename val)))
          (mv val state)))
       (- (cw "~s0~%" str)))
    (mv val state)))
