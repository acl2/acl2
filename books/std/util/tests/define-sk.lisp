; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Jared Davis

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")
(include-book "../define-sk")
(include-book "utils")
(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/basic/defs" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#!STD ;; BOZO move to std/util/tests/utils
(encapsulate
  ()
  (defmacro assert-is-theorem (thm)
    `(make-event
      (b* ((thm (fgetprop ',thm 'acl2::theorem nil (w state)))
           ((when (consp thm))
            (value '(value-triple :success))))
        (er soft 'assert-is-theorem "~x0 is not a theorem!" ',thm))))

  (defmacro assert-is-not-theorem (thm)
    `(make-event
      (b* ((thm (fgetprop ',thm 'acl2::theorem nil (w state)))
           ((when (atom thm))
            (value '(value-triple :success))))
        (er soft 'assert-is-not-theorem "~x0 is a theorem!" ',thm))))

  (assert-is-theorem car-cons)
  (must-fail (assert-is-not-theorem car-cons))
  ;; nobody would prove a theorem named this, because they are gross together...
  (assert-is-not-theorem peanut-butter-belongs-near-chocolate)
  (must-fail (assert-is-theorem peanut-butter-belongs-near-chocolate))
  )

#!STD ;; BOZO move to std/util/tests/utils
(encapsulate
  ()
  (defmacro assert-enabled-rewrite (thm)
    `(progn
       (assert-is-theorem ,thm)
       (make-event
        (b* ((acl2::ens (acl2::ens state))
             ((when (active-runep '(:rewrite ,thm)))
              (value '(value-triple :success))))
          (er soft 'assert-enabled-rewrite "Rewrite ~x0 is disabled (expected enabled)!" ',thm)))))

  (defmacro assert-disabled-rewrite (thm)
    `(progn
       (assert-is-theorem ,thm)
       (make-event
        (b* ((acl2::ens (acl2::ens state))
             ((unless (active-runep '(:rewrite ,thm)))
              (value '(value-triple :success))))
          (er soft 'assert-disabled-rewrite "Rewrite ~x0 is enabled (expected disabled)!" ',thm)))))

  (local (defthmd disabled-rule
           (equal (consp x) (consp (if x x x)))))

  (assert-enabled-rewrite car-cons)
  (assert-disabled-rewrite disabled-rule))


(define-sk all-integerp (x)
  :verify-guards nil
  (forall elem
          (implies (member elem x)
                   (integerp x))))

(std::assert-disabled all-integerp)
(std::assert-disabled-rewrite all-integerp-necc)


(define-sk some-integerp (x)
  :verify-guards nil
  :enabled :all
  (exists elem
          (and (member elem x)
               (integerp x))))

(std::assert-enabled some-integerp)
(std::assert-enabled-rewrite some-integerp-suff)



(define-sk intersection-fully-naturalp ((x "First set.")
                                        (y "Second set."))
  :parents (define-sk)
  :short "Test case of define-sk documentation."
  :long "<p>Quantifiers are what I want @($\\forall$) my birthdays.</p>"
  :verify-guards nil
  :enabled :thm
  (forall elem (implies (and (member elem x)
                             (member elem y))
                        (natp elem))))

(std::assert-disabled intersection-fully-naturalp)
(std::assert-enabled-rewrite intersection-fully-naturalp-necc)

(encapsulate ;; Make sure that inferring :rewrite :direct works as we expect.
  ()
  (set-enforce-redundancy t) ;; implicitly local
  (defthm intersection-fully-naturalp-necc
    (implies (intersection-fully-naturalp x y)
             (implies (and (member elem x) (member elem y))
                      (natp elem)))))

(define-sk goofy-bad-rewrite-rule-p (x y)
  :verify-guards nil
  (forall elem (if (< elem x)
                   (integerp y)
                 (consp y))))

;; Originally, we made sure here that we don't infer :rewrite :direct for the
;; goofy one.  But Matt K. changed this 8/23/2016 when it became legal to have
;; rewrite rules for IF-expressions.
(encapsulate
  ()
  (set-enforce-redundancy t) ;; implicitly local
  (defthm goofy-bad-rewrite-rule-p-necc
    (implies (goofy-bad-rewrite-rule-p x y)
             (if (< elem x)
                 (integerp y)
               (consp y)))))

(define-sk positive-intersection-p
  :verbosep t
  :short "Basic test of macro arguments."
  (&key (first  integer-listp "First set.")
        (second integer-listp "Second set."))
  :enabled :fn
  ;; Notice that guard verification works even though we write IMPLIES here!
  (forall elem (implies (and (member elem first)
                             (member elem second))
                        (<= 0 elem)))
  :prepwork
  ((local (defthm integerp-when-member-of-integer-listp
            (implies (and (integer-listp x)
                          (member a x))
                     (integerp a))))
   (local (defthm real/rationalp-when-integerp
            (implies (integerp x)
                     (real/rationalp x))))
   (local (defthm eqlable-listp-when-integer-listp
            (implies (integer-listp x)
                     (eqlable-listp x)))))
  ///
  (defthm positive-intersection-p-when-atom
    (implies (atom first)
             (positive-intersection-p :first first
                                      :second second))))

(std::assert-enabled positive-intersection-p-fn)
(std::assert-disabled-rewrite positive-intersection-p-necc)

(assert!
 (b* ((guts1 (std::find-define-sk-guts 'positive-intersection-p (w state)))
      (guts2 (std::find-define-sk-guts 'positive-intersection-p-fn (w state))))
   (and (std::define-sk-guts-p guts1)
        (std::define-sk-guts-p guts2)
        (equal guts1 guts2))))


;; Basic tests of guard verification -----------------------------------------

(encapsulate
  ()
  (local (defthm crock
           (implies (and (nat-listp x)
                         (member elem x))
                    (natp elem))))

  (local (defthm crock2
           (implies (natp elem)
                    (eqlablep elem))))

  (local (defthm crock3
           (implies (natp elem)
                    (real/rationalp elem))))

  (local (defthm eqlable-listp-when-nat-listp
           (implies (nat-listp x)
                    (eqlable-listp x))))

  ;; defun-sk switches you into a tiny theory, so this fails:
  ;; Matt K. mod: The tiny-theory problem no longer applies as of mid-January
  ;; 2019, because of how defun-sk now always delays guard verification.  I've
  ;; replaced the commented-out event just below by the defun-sk below it.
  #||
  (must-fail (defun-sk all-greater-p (max x)
               (forall elem
                       (impliez (member elem x)
                                (<= elem max)))
               :witness-dcls ((declare (xargs :guard (and (natp max)
                                                          (nat-listp x))
                                              :verify-guards t)))))
  ||#
  (defun-sk all-greater-p-for-defun-sk (max x)
    (forall elem
            (impliez (member elem x)
                     (<= elem max)))
    :witness-dcls ((declare (xargs :guard (and (natp max)
                                               (nat-listp x))
                                   :verify-guards t))))

  ;; but define-sk is smart enough to make it work
  (define-sk all-greater-p ((max natp)
                            (x   nat-listp))
    (forall elem
            (implies (member elem x)
                     (<= elem max))))

  (std::assert-logic-mode all-greater-p)
  (std::assert-guard-verified all-greater-p)
  (std::assert-disabled all-greaterp-p))



;; Basic tests of return specifiers for weird quantifiers -------------------

(encapsulate
  ()
  (set-ignore-ok t) ;; implicitly local
  (defun-sk weird-quantifier (x)
    (forall elem 0))
  (defun-sk weirder-quantifier (x)
    (forall elem (mv x x))))

(define-sk weird-quantifier-returnspec (x)
  :ignore-ok t
  :irrelevant-formals-ok t
  :returns (zero (equal zero 0))
  (forall elem 0))

(define-sk weird-quantifier-2-returnspec (x)
  :ignore-ok t
  :returns nil ;; don't prove anything
  (forall elem (mv x x)))

(define-sk weird-quantifier-3-returnspec (x)
  :ignore-ok t
  :returns (mv (foo natp :hyp (natp x))
               (bar natp :hyp (natp x)))
  (forall elem (mv x x)))



;; Basic tests of stobjs -----------------------------------------------------

(defstobj foost
  (foo-x :type integer :initially 0))
(defstobj barst
  (bar-x :type integer :initially 0)
  :congruent-to foost)

(define-sk foo-non-infinite-p (foost)
  (exists a (implies (natp a)
                     (<= a (foo-x foost)))))

(define-sk bar-non-infinite-p (barst)
  (exists a (implies (natp a)
                     (<= a (bar-x barst)))))

(define-sk weird-stobj-modifying-quantifier (foost)
  ;; This has proper returns checking
  :returns (mv val foost)
  (forall x
          (if (integerp x)
              (let ((foost (update-foo-x x foost)))
                (mv x foost))
            (mv nil foost))))

;; BOZO the following should work, but it doesn't because we mark the whole
;; function as non-executable since it has stobjs.  Consider tweaking defun-sk
;; to make the wrap the call of the witness function in non-exec to avoid
;; needing to add this declaration, which should make this work:
;;
;; (must-fail
;;  ;; This should fail because it doesn't follow the proper
;;  ;; stobj discipline.  It returns foost in one case, but NIL
;;  ;; in another.
;;  (define-sk weird-stobj-modifying-quantifier2 (foost)
;;    :returns (mv val foost)
;;    (forall x
;;            (if (integerp x)
;;                (let ((foost (update-foo-x x foost)))
;;                  (mv x foost))
;;              nil))))

(define-sk weird-stobj-modifying-quantifier3 (foost)
  ;; Marking it as non-executable means that we shouldn't care
  ;; about stobj checking and this is perfectly fine.
  :returns (mv val foost)
  :non-executable t
  (forall x
          (if (integerp x)
              (let ((foost (update-foo-x x foost)))
                (mv x foost))
            nil)))


;; Primitive tests of other various options -----------------------------------

(define-sk qfmisc1 (x)
  (forall y (consp (cons x y)))
  :thm-name qfmisc1-special-name)

(std::assert-is-theorem qfmisc1-special-name)
(std::assert-is-not-theorem qfmisc1-necc)

(define-sk qfmisc2 (x)
  (forall y (consp (cons x y)))
  :skolem-name qfmisc2-murder-witness)

(std::assert-logic-mode qfmisc2-murder-witness)

(encapsulate
  ()
  (local (define forall (x) x))
  (local (define-sk quant-ok-test (x)
           :quant-ok t
           (forall y (if (and y (forall x))
                         t
                       nil)))))

(must-fail
 (define-sk quant-not-ok-test (x)
   (forall y (if (and y (forall x))
                 t
               nil))))

(define-sk qfmisc3 (x)
  (forall y (consp (cons x y)))
  :strengthen t)

(std::assert-is-theorem qfmisc3-witness-strengthen)
