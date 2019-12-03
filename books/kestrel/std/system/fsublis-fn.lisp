; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fsublis-var")

(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines fsublis-fn-rec
  :parents (std/system/term-transformations)
  :short "Variant of @('sublis-fn-rec') that performs no simplification."
  :long
  (xdoc::topstring
   (xdoc::p
    "@('sublis-fn-rec') is in the ACL2 source code.")
   (xdoc::p
    "The meaning of the starting @('f') in the name of this utility
     is analogous to @(tsee fcons-term) compared to @(tsee cons-term).")
   (xdoc::p
    "The definition of this utility is identical to @('sublis-fn-rec'),
     except that @(tsee cons-term) and @(tsee sublis-var)
     are replaced by @(tsee fcons-term) and @(tsee fsublis-var).
     We also use @(tsee endp) instead of @(tsee null)
     in the exit test of @('fsublis-fn-rec-lst')
     so that termination can be proved and the function is in logic mode.")
   (xdoc::@def "fsublis-fn-rec")
   (xdoc::@def "fsublis-fn-rec-lst"))
  :verify-guards nil

  (define fsublis-fn-rec ((alist symbol-alistp)
                          (term pseudo-termp)
                          (bound-vars symbol-listp)
                          (allow-freevars-p booleanp))
    :returns (mv (vars "A @(tsee symbol-listp).")
                 (new-term "A @(tsee pseudo-termp)."))
    (cond
     ((variablep term) (mv nil term))
     ((fquotep term) (mv nil term))
     ((flambda-applicationp term)
      (let ((old-lambda-formals (lambda-formals (ffn-symb term))))
        (mv-let
          (erp new-lambda-body)
          (fsublis-fn-rec alist
                          (lambda-body (ffn-symb term))
                          (append old-lambda-formals bound-vars)
                          allow-freevars-p)
          (cond
           (erp (mv erp new-lambda-body))
           (t (mv-let
                (erp args)
                (fsublis-fn-rec-lst alist (fargs term) bound-vars
                                    allow-freevars-p)
                (cond (erp (mv erp args))
                      (t (let* ((body-vars (all-vars new-lambda-body))
                                (extra-body-vars
                                 (set-difference-eq body-vars
                                                    old-lambda-formals)))
                           (mv nil
                               (fcons-term
                                (make-lambda
                                 (append old-lambda-formals extra-body-vars)
                                 new-lambda-body)
                                (append args extra-body-vars))))))))))))
     (t (let ((temp (assoc-eq (ffn-symb term) alist)))
          (cond
           (temp
            (cond ((symbolp (cdr temp))
                   (mv-let
                     (erp args)
                     (fsublis-fn-rec-lst alist (fargs term) bound-vars
                                         allow-freevars-p)
                     (cond (erp (mv erp args))
                           (t (mv nil
                                  (fcons-term (cdr temp) args))))))
                  (t
                   (let ((bad (if allow-freevars-p
                                  (intersection-eq
                                   (set-difference-eq
                                    (all-vars (lambda-body (cdr temp)))
                                    (lambda-formals (cdr temp)))
                                   bound-vars)
                                (set-difference-eq
                                 (all-vars (lambda-body (cdr temp)))
                                 (lambda-formals (cdr temp))))))
                     (cond
                      (bad (mv bad term))
                      (t (mv-let
                           (erp args)
                           (fsublis-fn-rec-lst alist (fargs term) bound-vars
                                               allow-freevars-p)
                           (cond (erp (mv erp args))
                                 (t (mv nil
                                        (fsublis-var
                                         (pairlis$ (lambda-formals (cdr temp))
                                                   args)
                                         (lambda-body (cdr temp)))))))))))))
           (t (mv-let (erp args)
                (fsublis-fn-rec-lst alist (fargs term) bound-vars
                                    allow-freevars-p)
                (cond (erp (mv erp args))
                      (t (mv nil
                             (fcons-term (ffn-symb term) args)))))))))))

  (define fsublis-fn-rec-lst ((alist symbol-alistp)
                              (terms pseudo-term-listp)
                              (bound-vars symbol-listp)
                              (allow-freevars-p booleanp))
    :returns (mv (vars "A @(tsee symbol-listp).")
                 (new-terms "A @(tsee pseudo-term-listp)."))
    (cond ((endp terms) (mv nil nil))
          (t (mv-let
               (erp term)
               (fsublis-fn-rec alist (car terms) bound-vars allow-freevars-p)
               (cond (erp (mv erp term))
                     (t (mv-let
                          (erp tail)
                          (fsublis-fn-rec-lst alist (cdr terms) bound-vars
                                              allow-freevars-p)
                          (cond (erp (mv erp tail))
                                (t (mv nil (cons term tail))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fsublis-fn ((alist symbol-alistp)
                    (term pseudo-termp)
                    (bound-vars symbol-listp))
  :returns (mv (vars "A @(tsee symbol-listp).")
               (new-term "A @(tsee pseudo-termp)."))
  :verify-guards nil
  :parents (std/system/term-transformations)
  :short "Variant of @(tsee sublis-fn) that performs no simplification."
  :long
  (xdoc::topstring-p
   "The meaning of the starting @('f') in the name of this utility
    is analogous to @(tsee fcons-term) compared to @(tsee cons-term).")
  (fsublis-fn-rec alist term bound-vars t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fsublis-fn-simple ((alist symbol-symbol-alistp)
                           (term pseudo-termp))
  :returns (new-term "A @(tsee pseudo-termp).")
  :verify-guards nil
  :parents (std/system/term-transformations)
  :short "Variant of @(tsee sublis-fn-simple) that performs no simplification."
  :long
  (xdoc::topstring-p
   "The meaning of the starting @('f') in the name of this utility
    is analogous to @(tsee fcons-term) compared to @(tsee cons-term).")
  (mv-let (vars result)
    (fsublis-fn-rec alist term nil t)
    (assert$ (null vars)
             result)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fsublis-fn-lst-simple ((alist symbol-symbol-alistp)
                               (terms pseudo-term-listp))
  :returns (new-terms "A @(tsee pseudo-term-listp).")
  :mode :program
  :parents (std/system/term-transformations)
  :short "Variant of @(tsee sublis-fn-lst-simple)
          that performs no simplification."
  :long
  (xdoc::topstring-p
   "The meaning of the starting @('f') in the name of this utility
    is analogous to @(tsee fcons-term) compared to @(tsee cons-term).")
  (mv-let (vars result)
    (sublis-fn-rec-lst alist terms nil t)
    (assert$ (null vars)
             result)))
