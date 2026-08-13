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
(include-book "abstract-syntax-derived-fixtypes")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Files as expressions.
;
; The declarations of a file are a sequence of bindings whose scopes nest
; left to right, which is exactly the scoping of the nested single-bind
; :LETs built by NEST-LET-BINDS above.  So the tools that work on
; expressions can be lifted to whole files by folding the declarations
; into such a nest; the conversions between declarations and bindings
; that this needs are collected here.

(define decl-to-bind ((decl declp))
  :returns (bind bindp)
  :parents (remora)
  :short "Turn a declaration into the @('let') binding it corresponds to."
  :long
  (xdoc::topstring
   (xdoc::p
    "A definition is already a binding.  An entry point has the same
     components as a function binding (see @(tsee decl)), so it becomes
     one; @(tsee bind-to-decl) turns it back."))
  (decl-case decl
    :def decl.bind
    :entry (make-bind-fun :var decl.var
                          :params decl.params
                          :type? decl.type?
                          :expr decl.expr)))

(define decl-list-to-binds ((decls decl-listp))
  :returns (binds bind-listp)
  :parents (remora)
  :short "Turn a list of declarations into the @('let') bindings
          they correspond to."
  (if (endp decls)
      nil
    (cons (decl-to-bind (car decls))
          (decl-list-to-binds (cdr decls)))))

(define decl-list-entry-names ((decls decl-listp))
  :returns (names string-listp)
  :parents (remora)
  :short "The names declared by the entry points of a list of declarations."
  (b* (((when (endp decls)) nil)
       (decl (car decls))
       (rest (decl-list-entry-names (cdr decls))))
    (decl-case decl
      :entry (cons (str::str-fix decl.var) rest)
      :otherwise rest)))

(define bind-to-decl ((bind bindp) (entry-names string-listp))
  :returns (decl declp)
  :parents (remora)
  :short "Turn a @('let') binding back into a declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function bindings that came from entry points are recognized by
     their names, which @(tsee decl-list-entry-names) collects before the
     transformation; every other binding becomes a definition.  This
     assumes that the names declared by the file are distinct, and that
     none of them is also an entry point's name without being that entry
     point --- which holds of any file whose declarations are
     well-formed."))
  (bind-case bind
    :fun (if (member-equal bind.var (str::string-list-fix entry-names))
             (make-decl-entry :var bind.var
                              :params bind.params
                              :type? bind.type?
                              :expr bind.expr)
           (decl-def bind))
    :otherwise (decl-def bind)))

(define bind-list-to-decls ((binds bind-listp) (entry-names string-listp))
  :returns (decls decl-listp)
  :parents (remora)
  :short "Turn a list of @('let') bindings back into declarations."
  (if (endp binds)
      nil
    (cons (bind-to-decl (car binds) entry-names)
          (bind-list-to-decls (cdr binds) entry-names))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Running a file means running its MAIN entry point.  This is the
; semantic constraint noted in the grammar (the interpreter requires
; exactly one entry named MAIN); nothing else in the model imposes it,
; so it is imposed here, by the two functions below and FILE-TO-EXPR.

(define find-main-entry ((decls decl-listp))
  :returns (main decl-resultp)
  :parents (remora)
  :short "The first entry point named @('main') in a list of declarations."
  (b* (((when (endp decls)) (reserrf :no-main-entry))
       (decl (car decls))
       ((when (decl-case decl
                :entry (equal (decl-entry->var decl) "main")
                :otherwise nil))
        (decl-fix decl)))
    (find-main-entry (cdr decls))))

(define decls-before-main ((decls decl-listp))
  :returns (before decl-listp)
  :parents (remora)
  :short "The declarations preceding the first entry point named @('main')."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are exactly the declarations in scope in @('main')'s body:
     Remora @('let')s are non-recursive, so a declaration that follows
     @('main') is not visible to it."))
  (b* (((when (endp decls)) nil)
       (decl (car decls))
       ((when (decl-case decl
                :entry (equal (decl-entry->var decl) "main")
                :otherwise nil))
        nil))
    (cons (decl-fix decl) (decls-before-main (cdr decls)))))

(define file-to-expr ((file filep))
  :returns (expr expr-resultp)
  :parents (remora)
  :short "The expression that running an import-free Remora file evaluates."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the body of the file's @('main') entry point, wrapped in the
     declarations that precede it (see @(tsee decls-before-main)), so
     that evaluating it runs the file.")
   (xdoc::p
    "Fails with @(':imports-not-supported') if the file has imports, which
     would have to be resolved first by replacing them with the
     declarations of the imported files (see @(tsee file));
     @(':no-main-entry') if there is no entry point named @('main'); and
     @(':main-has-parameters') if @('main') has any, since there would be
     nothing to apply it to."))
  (b* (((file file) file)
       ((when (consp file.imports)) (reserrf :imports-not-supported))
       (main (find-main-entry file.decls))
       ((when (reserrp main)) main)
       ((unless (decl-case main :entry)) (reserrf :no-main-entry))
       ((unless (endp (decl-entry->params main))) (reserrf :main-has-parameters))
       (binds (decl-list-to-binds (decls-before-main file.decls))))
    (nest-let-binds binds (decl-entry->expr main))))
