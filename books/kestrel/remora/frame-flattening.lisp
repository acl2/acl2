; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-structurals")

(local (include-book "std/typed-lists/nat-listp" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable* ast-corep-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ frame-flattening
  :parents (abstract-syntax)
  :short "Frame flattening."
  :long
  (xdoc::topstring
   (xdoc::p
    "This unnests nested frame and array expressions, under suitably conditions.
     It could be thought of as
     a normalizing transformation,
     or even a desugaring transformation,
     but it is not part of actual @(see desugaring),
     and may not be in fact necessary for most purposes.
     However, it is part of [impl]
     (part of desugaring in earlier versions, but not currently),
     and [tutor] describes it as syntactic sugar
     (but [tutor] is older than [impl])."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-same-len-p ((xss true-list-listp))
  :returns (yes/no booleanp)
  :short "Check whether all the lists in a list have the same length."
  :long
  (xdoc::topstring
   (xdoc::p
    "This belongs to a more general library."))
  (or (endp xss)
      (endp (cdr xss))
      (and (equal (len (car xss))
                  (len (cadr xss)))
           (all-same-len-p (cdr xss)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines flatten-frames-in-exprs
  :short "Flatten frames in expressions and lists of expressions."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define flatten-frames-in-expr ((expr exprp))
    :returns (flat-expr exprp)
    :short "Flatten frames in an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "The general idea is that
       an expression of the form")
     (xdoc::codeblock
      "(frame [a1 ... aN] (frame [b1 ... bM] x11 ... x1P)"
      "                   (frame [b1 ... bM] x21 ... x2P)"
      "                   ..."
      "                   (frame [b1 ... bM] xQ1 ... xQP))")
     (xdoc::p
      "is turned into")
     (xdoc::codeblock
      "(frame [a1 ... aN b1 ... bM] x11 ... xQP)")
     (xdoc::p
      "and that an expression of the form")
     (xdoc::codeblock
      "(frame [a1 ... aN] (array [b1 ... bM] x11 ... x1P)"
      "                   (array [b1 ... bM] x21 ... x2P)"
      "                   ..."
      "                   (array [b1 ... bM] xQ1 ... xQP))")
     (xdoc::p
      "is turned into")
     (xdoc::codeblock
      "(array [a1 ... aN b1 ... bM] x11 ... xQP)")
     (xdoc::p
      "More precisely, given an expression, we do the following.
       Unless the expression is a non-empty frame, we leave it unchanged.
       If it is a non-empty frame,
       let it be @('(frame [a1 ... aN] e1 ... eQ)').
       If @('Q') is 0, i.e. there are no expressions,
       we return the frame expression unchanged;
       this frame expression is statically malformed,
       but this is caught by the static semantics.
       If @('Q') is not 0, we recursively flatten @('e1') to @('eQ'),
       let the results be @('f1') to @('fQ').
       Then there are three cases:")
     (xdoc::ul
      (xdoc::li
       "If all of @('f1') to @('fQ') are frame expressions
        with identical dimensions
        and with the same number of sub-expressions,
        i.e. the first form above,
        we concatenate the dimensions and all the sub-expressions,
        as shown above.")
      (xdoc::li
       "If all of @('f1') to @('fQ') are array expressions
        with identical dimensions
        and with the same number of sub-expressions,
        i.e. the second form above,
        we concatenate the dimensions and all the sub-atoms,
        as shown above.")
      (xdoc::li
       "Otherwise, we return @('(frame [a1 ... aN] f1 ... fQ)'),
        which in our code is denoted @('no-further'),
        conveying that we do not further flatten it.")))
    (expr-case
     expr
     :frame
     (b* (((unless (consp expr.exprs)) (expr-fix expr))
          (exprs (flatten-frames-in-expr-list expr.exprs))
          (no-further (make-expr-frame :dims expr.dims :exprs exprs))
          ((when (expr-list-case-frame exprs))
           (b* ((dimss (expr-frame-list->dims exprs))
                (exprss (expr-frame-list->exprs exprs))
                (dims (car dimss))
                ((unless (all-equalp dims dimss)) no-further)
                ((unless (all-same-len-p exprss)) no-further))
             (make-expr-frame :dims (append expr.dims dims)
                              :exprs (expr-append-all exprss))))
          ((when (expr-list-case-array exprs))
           (b* ((dimss (expr-array-list->dims exprs))
                (atomss (expr-array-list->atoms exprs))
                (dims (car dimss))
                ((unless (all-equalp dims dimss)) no-further)
                ((unless (all-same-len-p atomss)) no-further))
             (make-expr-array :dims (append expr.dims dims)
                              :atoms (atom-append-all atomss)))))
       no-further)
     :otherwise (expr-fix expr))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define flatten-frames-in-expr-list ((exprs expr-listp))
    :returns (flat-exprs expr-listp)
    :short "Flatten frames in a list of expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "Each expression in the list is processed independently."))
    (cond ((endp exprs) nil)
          (t (cons (flatten-frames-in-expr (car exprs))
                   (flatten-frames-in-expr-list (cdr exprs)))))
    :measure (expr-list-count exprs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  :guard-hints (("Goal" :in-theory (enable
                                    true-list-listp-when-expr-list-listp
                                    true-list-listp-when-atom-list-listp)))

  :flag-local nil

  ///

  (fty::deffixequiv-mutual flatten-frames-in-exprs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection corep-of-flatten-frames
  :short "Frame flattening core ASTs yields core ASTs."

  (defret-mutual corep-of-flatten-frames
    (defret expr-corep-of-flatten-frame-in-expr
      (expr-corep flat-expr)
      :hyp (expr-corep expr)
      :fn flatten-frames-in-expr)
    (defret expr-list-corep-of-flatten-frames-in-expr-list
      (expr-list-corep flat-exprs)
      :hyp (expr-list-corep exprs)
      :fn flatten-frames-in-expr-list)
    :mutual-recursion flatten-frames-in-exprs
    :hints (("Goal" :in-theory (enable flatten-frames-in-expr
                                       flatten-frames-in-expr-list)))))
