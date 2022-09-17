; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../execution")

(include-book "syntaxp")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-pure-rules
  :short "Rules for @(tsee exec-expr-pure)."
  :long
  (xdoc::topstring
   (xdoc::p
    "For @('&&') and @('||'),
     we use the auxiliary function @('sint-from-boolean-with-error')
     as an intermediate rewriting stage.")
   (xdoc::p
    "We include the executable counterpart of @(tsee member-equal),
     needed to discharge the hypothesis of
     the rule for strict pure binary expressions.")
   (xdoc::p
    "We include executable counterparts of accessor functions for expressions,
     used to check the kind of expression and to retrieve its constituents."))

  (defruled exec-expr-pure-when-ident
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :ident))
             (equal (exec-expr-pure e compst)
                    (exec-ident (expr-ident->get e) compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-const
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :const))
             (equal (exec-expr-pure e compst)
                    (exec-const (expr-const->get e))))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-arrsub
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :arrsub)
                  (equal arr (expr-arrsub->arr e))
                  (not (expr-case arr :member))
                  (not (expr-case arr :memberp)))
             (equal (exec-expr-pure e compst)
                    (exec-arrsub (exec-expr-pure arr compst)
                                 (exec-expr-pure (expr-arrsub->sub e) compst)
                                 compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-member
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :member))
             (equal (exec-expr-pure e compst)
                    (exec-member (exec-expr-pure (expr-member->target e)
                                                 compst)
                                 (expr-member->name e))))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-memberp
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :memberp))
             (equal (exec-expr-pure e compst)
                    (exec-memberp (exec-expr-pure (expr-memberp->target e)
                                                  compst)
                                  (expr-memberp->name e)
                                  compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-arrsub-of-member
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :arrsub)
                  (equal arr (expr-arrsub->arr e))
                  (expr-case arr :member))
             (equal (exec-expr-pure e compst)
                    (exec-arrsub-of-member
                     (exec-expr-pure (expr-member->target arr) compst)
                     (expr-member->name arr)
                     (exec-expr-pure (expr-arrsub->sub e) compst))))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-arrsub-of-memberp
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :arrsub)
                  (equal arr (expr-arrsub->arr e))
                  (expr-case arr :memberp))
             (equal (exec-expr-pure e compst)
                    (exec-arrsub-of-memberp
                     (exec-expr-pure (expr-memberp->target arr) compst)
                     (expr-memberp->name arr)
                     (exec-expr-pure (expr-arrsub->sub e) compst)
                     compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-unary
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :unary)
                  (equal val (exec-expr-pure (expr-unary->arg e) compst))
                  (valuep val))
             (equal (exec-expr-pure e compst)
                    (exec-unary (expr-unary->op e) val)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-cast
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :cast))
             (equal (exec-expr-pure e compst)
                    (exec-cast (expr-cast->type e)
                               (exec-expr-pure (expr-cast->arg e) compst))))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-strict-pure-binary
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal op (expr-binary->op e))
                  (member-equal (binop-kind op)
                                '(:mul :div :rem :add :sub :shl :shr
                                  :lt :gt :le :ge :eq :ne
                                  :bitand :bitxor :bitior)))
             (equal (exec-expr-pure e compst)
                    (exec-binary-strict-pure op
                                             (exec-expr-pure (expr-binary->arg1 e)
                                                             compst)
                                             (exec-expr-pure (expr-binary->arg2 e)
                                                             compst))))
    :enable (exec-expr-pure binop-purep))

  (defund sint-from-boolean-with-error (test)
    (if (errorp test)
        test
      (if test
          (sint 1)
        (sint 0))))

  (defruled exec-expr-pure-when-binary-logand
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal op (expr-binary->op e))
                  (equal (binop-kind op) :logand)
                  (equal arg1 (exec-expr-pure (expr-binary->arg1 e) compst))
                  (valuep arg1)
                  (equal test1 (test-value arg1))
                  (booleanp test1))
             (equal (exec-expr-pure e compst)
                    (if test1
                        (sint-from-boolean-with-error
                         (b* ((arg2 (exec-expr-pure (expr-binary->arg2 e)
                                                    compst))
                              ((when (errorp arg2)) arg2))
                           (test-value arg2)))
                      (sint 0))))
    :enable (exec-expr-pure binop-purep sint-from-boolean-with-error))

  (defruled exec-expr-pure-when-binary-logor
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal op (expr-binary->op e))
                  (equal (binop-kind op) :logor)
                  (equal arg1 (exec-expr-pure (expr-binary->arg1 e) compst))
                  (valuep arg1)
                  (equal test1 (test-value arg1))
                  (booleanp test1))
             (equal (exec-expr-pure e compst)
                    (if test1
                        (sint 1)
                      (sint-from-boolean-with-error
                       (b* ((arg2 (exec-expr-pure (expr-binary->arg2 e)
                                                  compst))
                            ((when (errorp arg2)) arg2))
                         (test-value arg2))))))
    :enable (exec-expr-pure binop-purep sint-from-boolean-with-error))

  (make-event
   `(defruled sint-from-boolean-with-error-when-booleanp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'test)
                    (booleanp test))
               (equal (sint-from-boolean-with-error test)
                      (if test
                          (sint 1)
                        (sint 0))))
      :enable sint-from-boolean-with-error))

  (defruled exec-expr-pure-when-cond
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :cond)
                  (equal arg1 (exec-expr-pure (expr-cond->test e) compst))
                  (valuep arg1)
                  (equal test (test-value arg1))
                  (booleanp test))
             (equal (exec-expr-pure e compst)
                    (if test
                        (exec-expr-pure (expr-cond->then e) compst)
                      (exec-expr-pure (expr-cond->else e) compst))))
    :enable exec-expr-pure)

  (defval *atc-exec-expr-pure-rules*
    '(exec-expr-pure-when-ident
      exec-expr-pure-when-const
      exec-expr-pure-when-arrsub
      exec-expr-pure-when-member
      exec-expr-pure-when-memberp
      exec-expr-pure-when-arrsub-of-member
      exec-expr-pure-when-arrsub-of-memberp
      exec-expr-pure-when-unary
      exec-expr-pure-when-cast
      exec-expr-pure-when-strict-pure-binary
      exec-expr-pure-when-binary-logand
      exec-expr-pure-when-binary-logor
      sint-from-boolean-with-error-when-booleanp
      exec-expr-pure-when-cond
      (:e member-equal)
      (:e expr-kind)
      (:e expr-ident->get)
      (:e expr-const->get)
      (:e expr-arrsub->arr)
      (:e expr-arrsub->sub)
      (:e expr-member->target)
      (:e expr-member->name)
      (:e expr-memberp->target)
      (:e expr-memberp->name)
      (:e expr-unary->op)
      (:e expr-unary->arg)
      (:e expr-cast->type)
      (:e expr-cast->arg)
      (:e expr-binary->op)
      (:e expr-binary->arg1)
      (:e expr-binary->arg2)
      (:e binop-kind)
      (:e expr-cond->test)
      (:e expr-cond->then)
      (:e expr-cond->else))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-pure-list-rules
  :short "Rules for @(tsee exec-expr-pure-list)."

  (defruled exec-expr-pure-list-of-nil
    (equal (exec-expr-pure-list nil compst)
           nil)
    :enable exec-expr-pure-list)

  (defruled exec-expr-pure-list-when-consp
    (implies (and (syntaxp (quotep es))
                  (consp es)
                  (equal val (exec-expr-pure (car es) compst))
                  (valuep val)
                  (equal vals (exec-expr-pure-list (cdr es) compst))
                  (value-listp vals))
             (equal (exec-expr-pure-list es compst)
                    (cons val vals)))
    :enable exec-expr-pure-list)

  (defval *atc-exec-expr-pure-list-rules*
    '(exec-expr-pure-list-of-nil
      exec-expr-pure-list-when-consp)))
