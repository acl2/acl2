; Make-flag -- Introduce induction scheme for mutually recursive functions.
; Copyright (C) 2008-2010 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original authors: Sol Swords and Jared Davis
;                   {sswords,jared}@centtech.com
;
; Additional tests added as indicated by Matt Kaufmann.

#||
;; For interactive testing:
(include-book
 "std/portcullis" :dir :system)
||#

(in-package "ACL2")
(include-book "flag")
(local (include-book "arithmetic-3/bind-free/top" :dir :system))
(logic) ;; so local events aren't skipped

; A couple tests to make sure things are working.

(FLAG::make-flag flag-pseudo-termp
                 pseudo-termp
                 :flag-var flag
                 :flag-mapping ((pseudo-termp . term)
                                (pseudo-term-listp . list))
                 ;; :hints {for the measure theorem}
                 :defthm-macro-name defthm-pseudo-termp
                 )

;; Same thing, but let it fill in the flag function name for us.

(encapsulate
  ()
  (set-enforce-redundancy t) ;; implicitly local
  (FLAG::make-flag pseudo-termp
                   :flag-var flag
                   ;; Matt K. mod: Use new syntax
                   :flag-mapping ((pseudo-termp term)
                                  (pseudo-term-listp list))
                   ;; :hints {for the measure theorem}
                   :defthm-macro-name defthm-pseudo-termp
                   ))

; This introduces (flag-pseudo-termp flag x lst)
; Theorems equating it with pseudo-termp and pseudo-term-listp
; And the macro shown below.

(in-theory (disable (:type-prescription pseudo-termp)
                    (:type-prescription pseudo-term-listp)))

;; A few syntactic variations on defining the same theorems:
(encapsulate
  nil
  (value-triple 1)
  (local (defthm-pseudo-termp type-of-pseudo-termp
           (term (booleanp (pseudo-termp x))
                 :rule-classes :rewrite
                 :doc nil)
           (list (booleanp (pseudo-term-listp lst))))))

(encapsulate
  nil
  (value-triple 2)
  (local (defthm-pseudo-termp type-of-pseudo-termp2
           (defthm booleanp-of-pseudo-termp
             (booleanp (pseudo-termp x))
             :rule-classes :rewrite
             :doc nil
             :flag term)
           :skip-others t)))


(encapsulate
  nil
  (value-triple 3)
  (local (in-theory (disable pseudo-termp pseudo-term-listp)))
  (local (defthm-pseudo-termp type-of-pseudo-termp
           (term (booleanp (pseudo-termp x))
                 :hints ('(:expand ((pseudo-termp x))))
                 :rule-classes :rewrite
                 :doc nil)
           (list (booleanp (pseudo-term-listp lst))
                 :hints ('(:expand ((pseudo-term-listp lst))))))))

(encapsulate
  nil
  (value-triple 4)
  (local (defthm-pseudo-termp
           (term (booleanp (pseudo-termp x))
                 :rule-classes :rewrite
                 :doc nil
                 :name type-of-pseudo-termp)
           (list (booleanp (pseudo-term-listp lst))
                 :skip t))))

(encapsulate
  nil
  (value-triple 5)
  (local (defthm-pseudo-termp
           (defthm type-of-pseudo-termp
             (booleanp (pseudo-termp x))
             :rule-classes :rewrite
             :doc nil
             :flag term)
           (defthm type-of-pseudo-term-listp
             (booleanp (pseudo-term-listp lst))
             :flag list
             :skip t))))

(encapsulate
  nil
  (value-triple 6)
  (local (defthm-pseudo-termp
           (defthm type-of-pseudo-termp
             (booleanp (pseudo-termp x))
             :rule-classes :type-prescription
             :doc nil
             :flag term)
           (defthm pseudo-termp-equal-t
             (equal (equal (pseudo-termp x) t)
                    (pseudo-termp x))
             :rule-classes :rewrite
             :doc nil
             :flag term)
           (list
            (booleanp (pseudo-term-listp lst))
            :skip t))))


(defstobj term-bucket
  (terms))

(mutual-recursion

 (defun terms-into-bucket (x term-bucket)
   ;; Returns (mv number of terms added, term-bucket)
   (declare (xargs :stobjs (term-bucket)
                   :verify-guards nil))
   (cond ((or (atom x)
              (quotep x))
          (let ((term-bucket (update-terms (cons x (terms term-bucket)) term-bucket)))
            (mv 1 term-bucket)))
         (t
          (mv-let (numterms term-bucket)
            (terms-into-bucket-list (cdr x) term-bucket)
            (let ((term-bucket (update-terms (cons x (terms term-bucket)) term-bucket)))
              (mv (+ numterms 1) term-bucket))))))

 (defun terms-into-bucket-list (x term-bucket)
   (declare (xargs :stobjs (term-bucket)))
   (if (atom x)
       (mv 0 term-bucket)
     (mv-let (num-car term-bucket)
       (terms-into-bucket (car x) term-bucket)
       (mv-let (num-cdr term-bucket)
         (terms-into-bucket-list (cdr x) term-bucket)
         (mv (+ num-car num-cdr) term-bucket))))))

(FLAG::make-flag flag-terms-into-bucket
                 terms-into-bucket)


;; previously this didn't work, now we set-ignore-ok to fix it.
(encapsulate
  ()
  (set-ignore-ok t)
  (mutual-recursion
   (defun ignore-test-f (x)
     (if (consp x)
         (let ((y (+ x 1)))
           (ignore-test-g (cdr x)))
       nil))
   (defun ignore-test-g (x)
     (if (consp x)
         (ignore-test-f (cdr x))
       nil))))

(FLAG::make-flag flag-ignore-test
                 ignore-test-f)


(mutual-recursion
 (defun my-evenp (x)
   (if (zp x)
       t
     (my-oddp (- x 1))))
 (defun my-oddp (x)
   (if (zp x)
       nil
     (my-evenp (- x 1)))))

(flag::make-flag flag-my-evenp
                 my-evenp
                 ;; Matt K. mod: Mix old and new syntax
                 :flag-mapping ((my-evenp :even)
                                (my-oddp  :odd)))

(encapsulate
  ()
  (defthm-flag-my-evenp defthmd-test
    (defthmd my-evenp-of-increment
      (implies (natp x)
               (equal (my-evenp (+ 1 x))
                      (my-oddp x)))
      :flag :even)
    (defthm my-oddp-of-increment
      (implies (natp x)
               (equal (my-oddp (+ 1 x))
                      (my-evenp x)))
      :flag :odd)))

(make-event
 (b* ((acl2::ens (acl2::ens state))
      ((when (active-runep '(:rewrite my-evenp-of-increment)))
       (er soft 'defthmd-test "Expected my-evenp-of-increment to be disabled."))
      ((unless (active-runep '(:rewrite my-oddp-of-increment)))
       (er soft 'defthmd-test "Expected my-oddp-of-increment to be enabled.")))
   (value '(value-triple :success))))


(local (in-theory (disable my-evenp my-oddp evenp oddp)))

(encapsulate
  ()
  (local
   (defthm-flag-my-evenp hints-test-1

     (defthm my-evenp-is-evenp
       (implies (natp x)
                (equal (my-evenp x)
                       (evenp x)))
       :flag :even)
     (defthm my-oddp-is-oddp
       (implies (natp x)
                (equal (my-oddp x)
                       (oddp x)))
       :flag :odd)
     :hints(("Goal"
             :in-theory (enable my-evenp my-oddp evenp oddp)
             :expand ((my-evenp x)
                      (my-oddp x)
                      (evenp x)
                      (oddp x)))))))

(encapsulate
  ()
  ;; Previously this failed because we didn't look for Goal except in
  ;; the very first hint.

  (local
   (defthm-flag-my-evenp hints-test-2

     (defthm my-evenp-is-evenp
       (implies (natp x)
                (equal (my-evenp x)
                       (evenp x)))
       :flag :even)
     (defthm my-oddp-is-oddp
       (implies (natp x)
                (equal (my-oddp x)
                       (oddp x)))
       :flag :odd)

     :hints(("Subgoal *1/3" :in-theory (enable natp))
            ("Goal"
             :in-theory (enable my-evenp my-oddp evenp oddp)
             :expand ((my-evenp x)
                      (my-oddp x)
                      (evenp x)
                      (oddp x)))))))



(local
 (progn

   (defun nat-list-equiv (x y)
     (if (atom x)
         (atom y)
       (and (consp y)
            (equal (nfix (car x)) (nfix (car y)))
            (nat-list-equiv (cdr x) (cdr y)))))

   (defun sum-pairs-list (x)
     (if (atom x)
         nil
       (if (atom (cdr x))
           (list (nfix (car x)))
         (cons (+ (nfix (car x)) (nfix (cadr x)))
               (sum-pairs-list (cddr x))))))

   ;; It is a *MIRACLE* that this works given how many sub-inductions it does.
   (defequiv nat-list-equiv)

   ;; ;; no hint fails
   ;; (defthm sum-pairs-list-nat-list-equiv-congruence
   ;;   (implies (nat-list-equiv x y)
   ;;            (equal (sum-pairs-list x) (sum-pairs-list y)))
   ;;   :rule-classes :congruence)

   ;; ;; induct equiv hint fails
   ;; (defthm sum-pairs-list-nat-list-equiv-congruence
   ;;   (implies (nat-list-equiv x y)
   ;;            (equal (sum-pairs-list x) (sum-pairs-list y)))
   ;;   :rule-classes :congruence
   ;;   :hints (("goal" :induct (nat-list-equiv x y))))

   ;; ;; induct both hint fails
   ;; (defthm sum-pairs-list-nat-list-equiv-congruence
   ;;   (implies (nat-list-equiv x y)
   ;;            (equal (sum-pairs-list x) (sum-pairs-list y)))
   ;;   :rule-classes :congruence
   ;;   :hints (("goal" :induct (list (sum-pairs-list x) (sum-pairs-list y)))))

   ;; (defun sum-pairs-list-double-manual (x y)
   ;;   (declare (ignorable y))
   ;;   (if (atom x)
   ;;       nil
   ;;     (if (atom (cdr x))
   ;;         (list (nfix (car x)))
   ;;       (cons (+ (nfix (car x)) (nfix (cadr x)))
   ;;             (sum-pairs-list-double-manual (cddr x) (cddr y))))))

   ;; ;; sum-pairs-list-double-manual works but is not what we want to test
   ;; (defthm sum-pairs-list-nat-list-equiv-congruence
   ;;   (implies (nat-list-equiv x y)
   ;;            (equal (sum-pairs-list x) (sum-pairs-list y)))
   ;;   :rule-classes :congruence
   ;;   :hints (("goal" :induct (sum-pairs-list-double-manual x y))))

   (flag::def-doublevar-induction sum-pairs-list-double
     :orig-fn sum-pairs-list
     :old-var x
     :new-var y)

   (defthm sum-pairs-list-nat-list-equiv-congruence ;; sum-pairs-list-double works
     (implies (nat-list-equiv x y)
              (equal (sum-pairs-list x) (sum-pairs-list y)))
     :rule-classes :congruence
     :hints (("goal" :induct (sum-pairs-list-double x y))))))

;;;;;;;;;;
;;; Tests of :body argument (by Matt Kaufmann).
;;;;;;;;;;

(include-book "misc/install-not-normalized" :dir :system)

(mutual-recursion ; adapted from :doc mutual-recursion
 (defun evenlp (x)
   (if (atom x) t (oddlp (cdr x))))
 (defun oddlp (x)
   (if (atom x) nil (evenlp (cdr x)))))

(install-not-normalized evenlp)

; Use the new body:
(make-flag evenlp :body :last)
(assert-event
 (equal (body 'flag-evenlp nil (w state))
        '(RETURN-LAST 'PROGN
                      (THROW-NONEXEC-ERROR 'FLAG-EVENLP
                                           (CONS FLAG (CONS X 'NIL)))
                      (IF (EQUAL FLAG 'EVENLP)
                          (IF (ATOM X)
                              'T
                              (FLAG-EVENLP 'ODDLP (CDR X)))
                          (IF (ATOM X)
                              'NIL
                              (FLAG-EVENLP 'EVENLP (CDR X)))))))

; Use the original body:
(make-flag flag2-evenlp evenlp)
(assert-event
 (equal (body 'flag2-evenlp nil (w state))
        '(RETURN-LAST 'PROGN
                      (THROW-NONEXEC-ERROR 'FLAG2-EVENLP
                                           (CONS FLAG (CONS X 'NIL)))
                      (IF (EQUAL FLAG 'EVENLP)
                          (IF (CONSP X)
                              (FLAG2-EVENLP 'ODDLP (CDR X))
                              'T)
                          (IF (CONSP X)
                              (FLAG2-EVENLP 'EVENLP (CDR X))
                              'NIL)))))

; Install the original body of evenlp:
(DEFTHM EVENLP$re-NORMALIZED
  (EQUAL (EVENLP X)
         (IF (CONSP X) (ODDLP (CDR X)) 'T))
  :RULE-CLASSES
  ((:DEFINITION :INSTALL-BODY T
                :CLIQUE (EVENLP ODDLP)
                :CONTROLLER-ALIST ((EVENLP T) (ODDLP T)))))

; Use the latest bodies.
(make-flag flag3-evenlp evenlp :body :last)
(assert-event
 (equal (body 'flag3-evenlp nil (w state))
        '(RETURN-LAST 'PROGN
                      (THROW-NONEXEC-ERROR 'FLAG3-EVENLP
                                           (CONS FLAG (CONS X 'NIL)))
                      (IF (EQUAL FLAG 'EVENLP)
                          (IF (CONSP X)
                              (FLAG3-EVENLP 'ODDLP (CDR X))
                              'T)
                          (IF (ATOM X)
                              'NIL
                              (FLAG3-EVENLP 'EVENLP (CDR X)))))))

; Go back to the normalized bodies, where for evenlp the normalized body is
; first and last among the def-bodies of evenlp.
(make-event
 `(make-flag flag4-evenlp evenlp
             :body
             ((evenlp ,(install-not-normalized-name 'evenlp))
              (oddlp ,(install-not-normalized-name 'oddlp)))))
(assert-event
 (equal (body 'flag4-evenlp nil (w state))
        '(RETURN-LAST 'PROGN
                      (THROW-NONEXEC-ERROR 'FLAG4-EVENLP
                                           (CONS FLAG (CONS X 'NIL)))
                      (IF (EQUAL FLAG 'EVENLP)
                          (IF (ATOM X)
                              'T
                              (FLAG4-EVENLP 'ODDLP (CDR X)))
                          (IF (ATOM X)
                              'NIL
                              (FLAG4-EVENLP 'EVENLP (CDR X)))))))
