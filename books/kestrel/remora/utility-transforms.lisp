; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(include-book "kestrel/fty/deffold-map" :dir :system)

(include-book "portcullis")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; General-purpose AST transformations on Remora @(':let') expressions, used by
; (and factored out of) the monomorphizer.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helper: right-nest a bind-list into single-bind :let expressions around a body.

(define nest-let-binds ((binds bind-listp) (body exprp))
  :parents (remora)
  :returns (new-expr exprp)
  :short "Right-nest a list of binds into single-bind @(':let') expressions
          wrapped around @('body')."
  (if (endp binds)
      (expr-fix body)
    (expr-let (list (bind-fix (car binds)))
              (nest-let-binds (cdr binds) body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fold: rewrite every multi-bind :let into nested single-bind :lets, recursing
; through the whole expression/atom/bind hierarchy.

(fty::deffold-map singletonize-let
  :parents (remora)
  :short "Rewrite multi-bind @(':let') expressions as nested single-bind @(':let')s."
  :types (shapes/ispaces
          ispace-list-option
          types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :override
  ((expr :let (nest-let-binds
                (bind-list-singletonize-let expr.binds)
                (expr-singletonize-let expr.body))))
  :name ast-singletonize-let)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helper: merge a bind list into a :let body, coalescing when the body is a :let.

(define coalesce-let ((binds bind-listp) (body exprp))
  :parents (remora)
  :returns (new-expr exprp)
  :short "Merge @('binds') into a @(':let') body, coalescing when the body is
          itself a @(':let')."
  (expr-case body
    :let (expr-let (bind-list-fix (append (bind-list-fix binds) body.binds))
                   body.body)
    :otherwise (expr-let (bind-list-fix binds) (expr-fix body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fold: collapse chains of :let expressions into single multi-bind :lets.
; This is the left inverse of singletonize-let on the latter's image.

(fty::deffold-map flatten-let
  :parents (remora)
  :short "Collapse chains of @(':let') expressions into single multi-bind @(':let')s."
  :types (shapes/ispaces
          ispace-list-option
          types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :override
  ((expr :let (coalesce-let (bind-list-flatten-let expr.binds)
                            (expr-flatten-let expr.body))))
  :name ast-flatten-let)
