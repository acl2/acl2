; Tests of the rewriter
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add more tests

(include-book "rewriter")
(include-book "kestrel/utilities/deftest" :dir :system)
(include-book "kestrel/utilities/assert-with-stobjs" :dir :system)
(include-book "basic-rules") ;for equal-same

;TODO: add these as tests:

;; ;;simple challenge: why doesn't the context simplify the if?:
;; (simplify-term '(if (eqz x y) (binary-+ (unary-- (if (eqz x y) '2 '3)) z) w) nil :use-internal-contextsp t :print t)

;; ;simpler example:
;; (simplify-term '(if (eqz x y) (if (eqz x y) '2 '3) w) nil :use-internal-contextsp t :print t)

;; ;this one has :irrelevant in the answer:
;; (simplify-term '(if (eqz x y) (if (eqz x y) '2 z) w) nil :use-internal-contextsp t :print t)

;; ;this one works because the context expr is negated, so it can be replaced by nil:
;; (simplify-term '(if (not (eqz x y)) (if (eqz x y) '2 '3) w) nil :use-internal-contextsp t :print t)


;todo: how can we assert that the first return value here is non-nil?
;; (mv-let (res state)
;;   (simplify-terms-to-new-terms '((car (cons x y))
;;                                  (+ 1 2) ;untranslated
;;                                  (car (cons x y)))
;;                                (make-rule-alist '(car-cons) state)
;;                                )
;;   (mv (equal res '(x '3 x))
;;       state))

;; TODO: Get this to work, even though x is not known to be boolean. We could
;; have add-equality-pairs pair (equal x nil) to nil and then look for that
;; when resolving an IF test...
;(simplify-term '(if x y z) nil :assumptions '(x))

;; Test that assumptions that are not known booleans can still be used to
;; relieve hyps of rules:
(deftest
  (defun consp2 (x) (consp x))
  (defthm test (implies (consp2 x) (< 0 (len x))) :hints (("Goal" :in-theory (enable len))))

  (assert-equal-with-stobjs2 (simp-term '(< '0 (len x)) :rules '(test) :assumptions '((consp2 x)))
                            ''t
                            :stobjs (state)))

;; Utility for testing the simplification functions.
;; FORM must return (mv erp result state).
(defmacro test-simp-form (form expected-result)
  `(assert!-stobj
    (mv-let (erp res state)
      ,form ;; example: (simp-term ''3 :rules nil)
      (mv (and (not erp)
               (equal res ,expected-result))
          state))
    state))

;; a constant simplifies to itself
(test-simp-form (simp-term ''3 :rules nil)
                ''3)

;; test a simple computation
(test-simp-form (simp-term '(binary-+ '1 '2) :rules nil)
                ''3)


(defstub foo (x) t)
(defstub bar (x) t)

;; Test that it replaces a variable with a constant, using an equality from the assumptions
(test-simp-form (simp-term '(foo x)
                           :rules nil
                           :assumptions '((equal x '3)))
                '((0 foo '3)))

;; Test that it replaces a term with a constant, using an equality from the assumptions
(test-simp-form (simp-term '(foo (bar x))
                           :rules nil
                           :assumptions '((equal (bar x) '3)))
                '((0 foo '3)))

;; Test that it replaces a variable with a constant, using an internal context equality
(test-simp-form (simp-term '(if (equal x '3) (foo x) '17)
                           :rules nil
                           :use-internal-contextsp t)
                '((3 IF 1 2 '17)
                  (2 FOO '3)
                  (1 EQUAL 0 '3)
                  (0 . X)))

;; Test that it replaces a term with a constant, using an internal context equality
(test-simp-form (simp-term '(if (equal (bar x) '3) (foo (bar x)) '17)
                           :rules nil
                           :use-internal-contextsp t)
                '((4 IF 2 3 '17)
                  (3 FOO '3)
                  (2 EQUAL 1 '3)
                  (1 BAR 0)
                  (0 . X)))

;todo: test whether it can follow chains of equalities in the assumptions..

(encapsulate ()
  (local (defun my-natp (x) (natp x)))

  (local
   (defthm integerp-when-my-natp
    (implies (my-natp x) (integerp x))))

  ;; A test with a non-known-boolean assumption
  (test-simp-form (simp-term '(integerp x)
                             :rules '(integerp-when-my-natp)
                             :assumptions '((my-natp x))
                             ;; :use-internal-contextsp t
                             :print t)
                  *t*))

;; ;; TODO:
;; ;; The result here includes :irrelevant, but we should get
;; ;; (myif (not (< a b)) y z)
;; (mv-let (erp res state)
;;   (simp-dag (dagify-term!
;;              '(myif (not (< a b))
;;                     (myif (booland (< a b) (w c d))
;;                           x
;;                           y)
;;                     z ;; could put (booland (< a b) (w c d)) here, to prevent context from helping rewrite the booland (if we get smarted about booland)
;;                     ))
;;             :rules nil
;;             :use-internal-contextsp t
;;             :memoizep nil)
;;   (mv erp (dag-to-term res) state))
