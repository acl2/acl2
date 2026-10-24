; Properties of terms preserved by cons-term
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; CONS-TERM (in basis-b.lisp) builds the term (fn . args) but evaluates calls
;; of primitives on constant arguments.  So its result is either (fn . args) or
;; a quoted constant, and it preserves any property of terms that holds for
;; all quoted constants.  These lemmas are about general-purpose functions and
;; could be moved to a library.

(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)
(include-book "kestrel/terms-light/lambda-free-termp" :dir :system)
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))

(defthm cons-term-cases
  (or (equal (cons-term fn args) (cons fn args))
      (and (equal (car (cons-term fn args)) 'quote)
           (consp (cdr (cons-term fn args)))
           (null (cddr (cons-term fn args)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable cons-term cons-term1))))

(local (in-theory (disable cons-term)))

(defthm pseudo-termp-of-cons-term
  (implies (pseudo-termp (cons fn args))
           (pseudo-termp (cons-term fn args)))
  :hints (("Goal" :use cons-term-cases)))

(defthm termp-of-cons-term
  (implies (termp (cons fn args) w)
           (termp (cons-term fn args) w))
  :hints (("Goal" :use cons-term-cases)))

(defthm no-nils-in-termp-of-cons-term
  (implies (no-nils-in-termp (cons fn args))
           (no-nils-in-termp (cons-term fn args)))
  :hints (("Goal" :use cons-term-cases)))

(defthm lambdas-closed-in-termp-of-cons-term
  (implies (lambdas-closed-in-termp (cons fn args))
           (lambdas-closed-in-termp (cons-term fn args)))
  :hints (("Goal" :use cons-term-cases
           :in-theory (enable lambdas-closed-in-termp))))

(defthm no-duplicate-lambda-formals-in-termp-of-cons-term
  (implies (no-duplicate-lambda-formals-in-termp (cons fn args))
           (no-duplicate-lambda-formals-in-termp (cons-term fn args)))
  :hints (("Goal" :use cons-term-cases
           :in-theory (enable no-duplicate-lambda-formals-in-termp))))

(defthm lambda-free-termp-of-cons-term
  (implies (lambda-free-termp (cons fn args))
           (lambda-free-termp (cons-term fn args)))
  :hints (("Goal" :use cons-term-cases
           :in-theory (enable lambda-free-termp))))

(defthm subsetp-equal-of-free-vars-in-term-of-cons-term
  (subsetp-equal (free-vars-in-term (cons-term fn args))
                 (free-vars-in-term (cons fn args)))
  :hints (("Goal" :use cons-term-cases
           :in-theory (enable free-vars-in-term))))

(defthm subsetp-equal-of-free-vars-in-term-of-cons-term-chain
  (implies (and (subsetp-equal (free-vars-in-terms args) x)
                (not (equal fn 'quote)))
           (subsetp-equal (free-vars-in-term (cons-term fn args)) x))
  :hints (("Goal" :use subsetp-equal-of-free-vars-in-term-of-cons-term
           :in-theory (e/d (free-vars-in-term) (subsetp-equal-of-free-vars-in-term-of-cons-term)))))
