; FTY Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Eric McCarthy (mccarthy@kestrel.edu)
;          Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defxdoc defsubtype

  :parents (fty-extensions fty)

  :short "Introduce a <see topic='@(url fty)'>fixtype</see> that
          is a subtype of the given fixtype."

  :long
  (xdoc::topstring

   (xdoc::h3 "Introduction")

   (xdoc::p
    "@(tsee defsubtype) introduces fixtypes for an arbitrary subtype.
     A subtype @('SUB') of a type @('SUPER') is one that is either
     the same as or more restrictive than @('SUPER').  This is expressed
     by a restriction predicate.  The recognizer predicate for the subtype
     is the conjunction of the supertype's recognizer predicate and
     the restriction predicate:")

   (xdoc::codeblock
    "(iff (sub-p x)"
    "     (and (super-p x)"
    "          (sub-restriction-p x)))")

   (xdoc::p
    "The restriction predicate should be a total function of one argument.
     It can be a symbol or a lambda expression.
     The required @(':fix-value') argument specifies a value that will be returned by the
     new fixing function.  It must satisfy the new recognizer predicate.")

   (xdoc::h3 "Basic Example")

   (xdoc::codeblock
    "(defsubtype positive-even"
    "  :supertype pos"
    "  :restriction (lambda (x) (and (integerp x) (evenp x)))"
    "  :fix-value 2)")

   (xdoc::p
    "This example would produce:")
   (xdoc::ul
    (xdoc::li "A recognizer @('positive-even-p').")
    (xdoc::li "A fixing function @('positive-even-fix').")
    (xdoc::li "An equivalence relation @('positive-even-equiv').")
    )

   (xdoc::p
    "The reason the restriction predicate is not just @('evenp')
     is because @('evenp') has a guard of @('integerp') and therefore
     is not a total function.  Note that the restriction predicate
     does not need to define a subset of the supertype.
     It can be true on some values that are not in the supertype,
     in this case on negative even numbers.  This is not a problem
     because the subtype's recognizer predicate checks both the
     supertype's predicate and the restriction predicate.")

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(defsubtype subtype"
    "  :supertype ...     ;; required; must be defined using fty"
    "  :restriction ...   ;; required; can be named or a lambda expression"
    "  :fix-value ...     ;; required"
    "  :pred ...          ;; optional name of new predicate; default: subtype-p"
    "  :fix ...           ;; optional; default: subtype-fix"
    "  :equiv ...         ;; optional; default: subtype-equiv"
    "  :parents ...       ;; optional; XDOC parents"
    "  :short ...         ;; optional; XDOC short description."
    "  :long ...          ;; optional; XDOC long description."
    "  )")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('subtype')"
    (xdoc::p
     "A symbol that specifies the name of the new fixtype."))

   (xdoc::desc
    "@(':supertype')"
    (xdoc::p
     "A symbol that names a fixtype that is a supertype of the type being defined.")
    (xdoc::p
     "The recognizer, fixer, and equivalence function of the supertype
      must all be guard-verified."))

   (xdoc::desc
    "@(':restriction')"
    (xdoc::p
     "A predicate that is used, in conjunction with the supertype's predicate,
      to define @('pred'), which recognizes values of the subtype."))

   (xdoc::desc
    "@(':fix-value')"
    (xdoc::p
     "The value returned by the fixing function when passed a value for which
      @('pred') is false.  Also establishes that the subtype has at least one value."))

   (xdoc::desc
    "@(':pred')"
    (xdoc::p
     "A symbol that specifies the name of the generated recognizer for @('subtype').
      If this is @('nil') (the default),
      the name of the recognizer is @('subtype') followed by @('-p')."))

   (xdoc::desc
    "@(':fix')"
    (xdoc::p
     "A symbol that specifies the name of the generated fixer for @('subtype').
      If this is @('nil') (the default),
      the name of the fixer is @('subtype') followed by @('-fix')."))

   (xdoc::desc
    "@(':equiv')"
    (xdoc::p
     "A symbol that specifies the name of the generated equivalence checker for @('subtype').
      If this is @('nil') (the default),
      the name of the equivalence checker is @('subtype') followed by @('-equiv')."))

   (xdoc::desc
    (list
     "@(':parents')"
     "@(':short')"
     "@(':long')")
    (xdoc::p
     "These, if present, are added to
      the XDOC topic generated for the new fixtype."))

   (xdoc::h3 "Generated Events")

   (xdoc::desc
    "@('pred')"
    (xdoc::p
     "The recognizer for the fixtype, guard-verified."))

   (xdoc::desc
    "@('booleanp-of-pred')"
    (xdoc::p
     "A rewrite rule saying that @('pred') is boolean-valued."))

   (xdoc::desc
    (list
     "@('supertype-pred-when-pred-rewrite')"
     "@('supertype-pred-when-pred-forward')")
    (xdoc::p
     "A rewrite rule and a forward chaining rule
      saying that a value satisfies @('supertype-pred')
      when it satisfies @('pred')."))

   (xdoc::desc
    "@('fix')"
    (xdoc::p
     "The fixer for the fixtype, guard-verified.")
    (xdoc::p
     "It fixes values outside of @('pred') by returning
      @('fix-value').")

   (xdoc::desc
    "@('pred-of-fix')"
    (xdoc::p
     "A rewrite rule saying that @('fix') always returns
      a value that satisfies @('pred')."))

   (xdoc::desc
    "@('fix-when-pred')"
    (xdoc::p
     "A rewrite rule saying that @('fix') disappears
      when its argument satisfies @('pred')."))

   (xdoc::desc
    (list
     "@('type')"
     "@('equiv')")
    (xdoc::p
     "The fixtype, via a call of @(tsee fty::deffixtype)
      that also introduces the equivalence checker @('equiv')."))

   (xdoc::p
    "The above items are generated with XDOC documentation."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defxdoc+ defsubtype-implementation
  :parents (defsubtype)
  :short "Implementation of @(tsee defsubtype)."
  :order-subtopics t
  :default-parent t)

;; The restriction predicate must be a symbol or a lambda expression of one argument.
;;   [There are various system functions with good-sounding names like
;;    SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP but I haven't found a
;;    simple-enough one for this purpose. - Eric M.]
(defun possible-predicate-p (restriction)
  (or (symbolp restriction)
      (and (listp restriction)
           (eq (car restriction) 'lambda)
           (listp (cadr restriction))
           (symbolp (car (cadr restriction)))
           (null (cdr (cadr restriction)))
           (consp (cddr restriction)))))

(define defsubtype-fn (subtype
                       supertype
                       restriction
                       fix-value
                       pred
                       fix
                       equiv
                       parents
                       short
                       long
                       (wrld plist-worldp))
  :returns (event "A @(tsee acl2::maybe-pseudo-event-formp).")
  :mode :program
  :short "Events generated by @(tsee defsubtype)."
  :long
  (xdoc::topstring-p
   "For now we only perform partial validation of the inputs.
    Future implementations may perform a more thorough validation.")
  (b* (;; validate the SUBTYPE input:
       ((unless (symbolp subtype))
        (raise "The SUBTYPE input must be a symbol, ~
                but it is ~x0 instead." subtype))
       ;; validate the :SUPERTYPE input:
       ((unless (symbolp supertype))
        (raise "The :SUPERTYPE input must be a symbol, ~
                but it is ~x0 instead." supertype))

       ;; validate the RESTRICTION input.
       ;; Note, we don't prove anything about it here, we just make sure it is
       ;; the right shape.
       ;;    (possible-predicate-p restriction wrld)
       ((unless (possible-predicate-p restriction))
        (raise "The :RESTRICTION input must be either the name of a predicate, ~
                or a lambda expression predicate, but it is ~x0 instead." restriction))

       (fty-table (get-fixtypes-alist wrld))
       (fty-info (find-fixtype supertype fty-table))
       ((unless fty-info)
        (raise "The :SUPERTYPE input ~x0 must name a fixtype, ~
                but it does not." supertype))
       ;; retrieve the recognizer and fixer of the supertype
       (super-pred (fixtype->pred fty-info))
       ; We don't have a need of the super-fix now but if that changes, use this:
       ;(super-fix (fixtype->fix fty-info))

       ;; validate the :PRED input:
       ((unless (symbolp pred))
        (raise "The :PRED input must be a symbol, ~
                but it is ~x0 instead." pred))
       ;; validate the :FIX input:
       ((unless (symbolp fix))
        (raise "The :FIX input must be a symbol, ~
                but it is ~x0 instead." fix))
       ;; validate the :EQUIV input:
       ((unless (symbolp equiv))
        (raise "The :EQUIV input must be a symbol, ~
                but it is ~x0 instead." equiv))
       ;; package for the generated theorem and variable names:
       (pkg (symbol-package-name subtype))
       (pkg (if (equal pkg *main-lisp-package-name*) "ACL2" pkg))
       (pkg-witness (pkg-witness pkg))
       ;; names of the generated functions:
       (pred (or pred (acl2::add-suffix-to-fn subtype "-P")))
       (fix (or fix (acl2::add-suffix-to-fn subtype "-FIX")))
       (equiv (or equiv (acl2::add-suffix-to-fn subtype "-EQUIV")))
       ;; names of the generated theorems:
       (booleanp-of-pred (acl2::packn-pos (list 'booleanp-of- pred)
                                          pkg-witness))
       (super-pred-when-pred-rewrite (acl2::packn-pos (list super-pred
                                                           '-when-
                                                           pred
                                                           '-rewrite)
                                                     pkg-witness))
       (super-pred-when-pred-forward (acl2::packn-pos (list super-pred
                                                           '-when-
                                                           pred
                                                           '-forward)
                                                     pkg-witness))
       (pred-of-fix (acl2::packn-pos (list pred '-of- fix)
                                     pkg-witness))
       (fix-when-pred (acl2::packn-pos (list fix '-when- pred)
                                       pkg-witness))
       ;; variable to use in the generated functions and theorems:
       (x (intern-in-package-of-symbol "X" pkg-witness))
       ;; reference to the fixtype for the generated XDOC documentation:
       (type-ref (concatenate 'string
                              "@(tsee "
                              (acl2::string-downcase (symbol-package-name subtype))
                              "::"
                              (acl2::string-downcase (symbol-name subtype))
                              ")"))
       ;; generated events:
       (pred-event
        `(define ,pred (,x)
           :parents (,subtype)
           :short ,(concatenate 'string "Recognizer for " type-ref ".")
           (and (,super-pred ,x)
                (,restriction ,x))
           :no-function t
           ///
           (defrule ,booleanp-of-pred
             (booleanp (,pred ,x)))
           (defrule ,super-pred-when-pred-rewrite
             (implies (,pred ,x)
                      (,super-pred ,x)))
           (defrule ,super-pred-when-pred-forward
             (implies (,pred ,x)
                      (,super-pred ,x))
             :rule-classes :forward-chaining)
           ))
       (fix-event
        `(define ,fix ((,x ,pred))
           :parents (,subtype)
           :short ,(concatenate 'string "Fixer for " type-ref ".")
           (mbe :logic (if (,pred ,x)
                           ,x
                         ,fix-value)
                :exec ,x)
           :no-function t
           ///
           (defrule ,pred-of-fix
             (,pred (,fix ,x)))
           (defrule ,fix-when-pred
             (implies (,pred ,x)
                      (equal (,fix ,x) ,x)))))
       (type-event
        `(defsection ,subtype
           ,@(and parents (list :parents parents))
           ,@(and short (list :short short))
           ,@(and long (list :long long))
           (fty::deffixtype ,subtype
             :pred ,pred
             :fix ,fix
             :equiv ,equiv
             :define t
             :forward t))))
    ;; top-level event:
    `(encapsulate
       ()
       (logic)
       ,pred-event
       ,fix-event
       ,type-event)))

(defsection defsubtype-macro-definition
  :short "Definition of the @(tsee defsubtype) macro."
  :long "@(def defsubtype)"
  (defmacro defsubtype (subtype
                        &key
                        supertype
                        restriction
                        fix-value
                        pred
                        fix
                        equiv
                        parents
                        short
                        long)
    `(make-event (defsubtype-fn
                   ',subtype
                   ',supertype
                   ',restriction
                   ',fix-value
                   ',pred
                   ',fix
                   ',equiv
                   ',parents
                   ,short
                   ,long
                   (w state)))))
