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
(include-book "static-environments")
(include-book "type-checker")
(include-book "well-formedness-support")
(include-book "free-variable-operations")
(include-book "lists")
(include-book "osets")
(include-book "kestrel/fty/string-set" :dir :system)
(include-book "utility-transforms")

(include-book "portcullis")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-environments
  :parents (static-semantics)
  :short "Operations on type environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A type environment is a @(tsee string-type-mapp) from variable names to
     their types.  These operations look up, record, and restrict the types
     of locally bound variables, and turn a type environment into the
     @(tsee senv) the type checker checks against.  They are used by
     @(tsee lambda-lifting) and by @(tsee monomorphize)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Looking up the type recorded for a variable, and turning variable names
; into typed parameters.  A parameter whose type is not recorded is left
; untyped, which is still well formed but has no concrete syntax.

(define name-to-type-option ((name stringp) (tenv string-type-mapp))
  :returns (type? type-optionp)
  :short "The type recorded for a variable, if any."
  (b* ((pair (omap::assoc (str-fix name) (string-type-map-fix tenv)))
       ((unless pair) (type-option-none)))
    (type-option-some (cdr pair))))

(define names-to-params ((names string-listp) (tenv string-type-mapp))
  :returns (params var+type?-listp)
  :short "Turn variable names into parameters, typed where the type is known."
  :long
  (xdoc::topstring
   (xdoc::p
    "A parameter whose type is not recorded in @('tenv') is left untyped.
     That is still well formed, but it has no concrete syntax, so a
     definition with such a parameter cannot be printed; see @(tsee
     lambda-lifting)."))
  (if (endp names)
      nil
    (cons (make-var+type? :var (str-fix (car names))
                          :type? (name-to-type-option (car names) tenv))
          (names-to-params (cdr names) tenv)))

  ///

  (defret len-of-names-to-params
    (equal (len params) (len names))
    :hints (("Goal" :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Recording the types of the locally bound variables, i.e. those bound by
; binders within the current declaration.  This is both what decides which
; of a lambda's free variables it captures --- the local ones --- and what
; types the parameters it abstracts over.  It starts empty, so primitive
; operations and top-level definitions are never captured, and grows at
; each binder.

(define extend-tenv-with-var ((var stringp)
                              (type? type-optionp)
                              (tenv string-type-mapp))
  :returns (new-tenv string-type-mapp)
  :short "Record a variable's type, if it has one."
  (b* ((tenv (string-type-map-fix tenv))
       (type? (type-option-fix type?))
       ((unless (type-option-case type? :some)) tenv))
    (omap::update (str-fix var) (type-option-some->val type?) tenv)))

(define extend-tenv-with-params ((params var+type?-listp)
                                 (tenv string-type-mapp))
  :returns (new-tenv string-type-mapp)
  :short "Record the types of the parameters that state one."
  (b* (((when (endp params)) (string-type-map-fix tenv))
       ((var+type? p) (car params)))
    (extend-tenv-with-params (cdr params)
                             (extend-tenv-with-var p.var p.type? tenv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Restricting a type environment to a set of keys, and turning it into the
; static environment the checker checks against.

(define restrict-to-keys ((keys string-setp) (tenv string-type-mapp))
  :returns (new-tenv string-type-mapp)
  :short "The entries of a map whose keys are in a set."
  (b* ((tenv (string-type-map-fix tenv))
       ((when (omap::emptyp tenv)) nil)
       ((mv key val) (omap::head tenv))
       (rest (restrict-to-keys keys (omap::tail tenv))))
    (if (set::in key (string-sfix keys))
        (omap::update key val rest)
      rest))
  :measure (acl2-count (string-type-map-fix tenv))
  :verify-guards :after-returns)

(define tenv-to-senv ((tenv string-type-mapp))
  :returns (senv senvp)
  :short "The static environment for checking in the local environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variables in scope are the local ones over the primitive
     operations, with no ispace or type variables."))
  (make-senv :ispace-vars nil
             :type-vars nil
             :expr-vars (omap::update* (string-type-map-fix tenv)
                                       (primop-types))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Recording the types of the variables a list of bindings binds.  A binding
; does not in general state the type of the variable it binds, so the
; bindings are handed to the type checker, whose resulting environment has
; every bound variable typed; only the entries for the variables these
; bindings bind are taken from its result, so that the environment stays
; local.  The checker is run with no ispace or type variables in scope; if
; it fails, the environment is left as it was.  The types it supplies are
; also required to pass @(tsee type-map-all-wfp), which keeps the invariant
; that the environment holds only well-formed types provable without a
; theorem about the checker.

(define extend-tenv-with-binds ((binds bind-listp) (tenv string-type-mapp))
  :returns (new-tenv string-type-mapp)
  :short "Record the types of the variables a list of bindings binds."
  :long
  (xdoc::topstring
   (xdoc::p
    "A binding does not in general state the type of the variable it binds:
     a @(':fun') states its result type, and a @(':val') may state nothing.
     So the bindings are handed to the type checker, @(tsee
     check-bind-list), whose resulting environment has every bound variable
     typed --- a function by its function type, a value by its inferred
     type.  This is what lets a lambda that captures a locally defined
     function abstract over it with a type.")
   (xdoc::p
    "The checker sees the primitive operations too, since the bindings may
     use them; but only the entries for the variables these bindings bind
     are taken from its result, so that the environment stays local, and a
     primitive is never taken for a captured variable.  The checker is run
     with no ispace or type variables in scope; if it fails, as it will for
     bindings that mention those, the environment is left as it was.  The
     types it supplies are also required to pass @(tsee type-map-all-wfp),
     which they do; this keeps the invariant that the environment holds only
     well-formed types provable without a theorem about the checker."))
  (b* ((tenv (string-type-map-fix tenv))
       (sbs (check-bind-list binds (tenv-to-senv tenv)))
       ((when (reserrp sbs)) tenv)
       (new (restrict-to-keys (bind-list-bound-expr-vars binds)
                              (senv->expr-vars (senv+binds->senv sbs))))
       ((unless (type-map-all-wfp new)) tenv))
    (omap::update* new tenv))
  :guard-hints (("Goal" :in-theory (enable senv+binds-p-when-result-not-error))))