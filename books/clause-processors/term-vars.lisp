; Term-vars.lisp -- 

; Copyright (C) 2010-2018 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

(include-book "std/util/defines" :dir :system)
(local (include-book "std/lists/sets" :dir :system))

(local (defthm member-of-union
         (iff (member x (union-eq a b))
              (or (member x a)
                  (member x b)))))

(local (defthm union-eq-associative
         (equal (union-eq (union-eq a b) c)
                (union-eq a (union-eq b c)))))


;; Historical note: We used to define this using symbol-<-merge instead of
;; union-eq in the simple-term-vars-lst, hoping for better performance.
;; However, we think that an accumulator-based version like ACL2's built-in
;; all-vars/all-vars1/all-vars1-lst is probably generally better since it does
;; the minimum amount of consing.  (However, we don't use that because it takes
;; NIL to be a variable, which doesn't comport with defevaluator semantics.)

(defines simple-term-vars-acc
  (define simple-term-vars-acc ((x pseudo-termp)
                                (acc symbol-listp))
    :returns (vars symbol-listp :hyp (symbol-listp acc))
    :verify-guards nil
    (cond ((atom x)
           (if (and x (mbt (symbolp x)))
               (add-to-set-eq x acc)
             acc))
          ((eq (car x) 'quote) acc)
          (t (simple-term-vars-lst-acc (cdr x) acc))))
  (define simple-term-vars-lst-acc ((x pseudo-term-listp)
                                    (acc symbol-listp))
    :returns (vars symbol-listp :hyp (symbol-listp acc))
    (if (atom x)
        acc
      (simple-term-vars-lst-acc (cdr x)
                                (simple-term-vars-acc (car x) acc))))
  ///
  (verify-guards simple-term-vars-acc))



(defines simple-term-vars
  :verify-guards nil
  :flag-local nil
  (define simple-term-vars ((x pseudo-termp))
    :returns (vars symbol-listp)
    (mbe :logic (cond ((atom x)
                       (and x (mbt (symbolp x))
                            (list x)))
                      ((eq (car x) 'quote) nil)
                      (t (simple-term-vars-lst (cdr x))))
         :exec (simple-term-vars-acc x nil)))
  (define simple-term-vars-lst ((x pseudo-term-listp))
    :returns (vars symbol-listp)
    (mbe :logic (if (atom x)
                    nil
                  (union-eq (simple-term-vars-lst (cdr x))
                            (simple-term-vars (car x))))
         :exec (simple-term-vars-lst-acc x nil)))
  ///


  (local (defun-sk simple-term-vars-acc-is-simple-term-vars-sk (x)
           (forall acc
                   (equal (simple-term-vars-acc x acc)
                          (union-eq (simple-term-vars x) acc)))
           :rewrite :direct))
  (local (defun-sk simple-term-vars-lst-acc-is-simple-term-vars-lst-sk (x)
           (forall acc
                   (equal (simple-term-vars-lst-acc x acc)
                          (union-eq (simple-term-vars-lst x) acc)))
           :rewrite :direct))
  (local (in-theory (disable simple-term-vars-acc-is-simple-term-vars-sk
                             simple-term-vars-lst-acc-is-simple-term-vars-lst-sk)))

  (local
   (defthm-simple-term-vars-flag
     (defthm simple-term-vars-acc-is-simple-term-vars-lemma
       (simple-term-vars-acc-is-simple-term-vars-sk x)
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause))
                               (simple-term-vars x)
                               (:free (acc) (simple-term-vars-acc x acc))
                               (:free (acc) (simple-term-vars-acc nil acc))))))
       :flag simple-term-vars
       :rule-classes nil)
     (defthm simple-term-vars-lst-acc-is-simple-term-vars-lst-lemma
       (simple-term-vars-lst-acc-is-simple-term-vars-lst-sk x)
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause))
                               (simple-term-vars-lst x)
                               (:free (acc) (simple-term-vars-lst-acc x acc))))))
       :flag simple-term-vars-lst
       :rule-classes nil)))

  (defthm simple-term-vars-acc-is-simple-term-vars
    (equal (simple-term-vars-acc x acc)
           (union-eq (simple-term-vars x) acc))
    :hints (("goal" :use simple-term-vars-acc-is-simple-term-vars-lemma)))
  (defthm simple-term-vars-lst-acc-is-simple-term-vars-lst
    (equal (simple-term-vars-lst-acc x acc)
           (union-eq (simple-term-vars-lst x) acc))
    :hints (("goal" :use simple-term-vars-lst-acc-is-simple-term-vars-lst-lemma)))


  (defthm simple-term-vars-lst-of-atom
    (implies (not (consp x))
             (equal (simple-term-vars-lst x) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))
  
  (defthm-simple-term-vars-flag
    (defthm true-listp-of-simple-term-vars
      (true-listp (simple-term-vars x))
      :hints ((and stable-under-simplificationp
                   '(:expand ((simple-term-vars x)))))
      :flag simple-term-vars
      :rule-classes :type-prescription)
    (defthm true-listp-of-simple-term-vars-lst
      (true-listp (simple-term-vars-lst x))
      :hints ((and stable-under-simplificationp
                   '(:expand ((simple-term-vars-lst x)))))
      :flag simple-term-vars-lst
      :rule-classes :type-prescription))

  (local (defthm union-eq-nil
           (implies (true-listp x)
                    (equal (union-eq x nil) x))))

  (verify-guards simple-term-vars)

  (defthm-simple-term-vars-flag
    (defthm simple-term-vars-nonnil
      (not (member nil (simple-term-vars x)))
      :hints ((and stable-under-simplificationp
                   '(:expand ((simple-term-vars x)))))
      :flag simple-term-vars)
    (defthm simple-term-vars-lst-nonnil
      (not (member nil (simple-term-vars-lst x)))
      :hints ((and stable-under-simplificationp
                   '(:expand ((simple-term-vars-lst x)))))
      :flag simple-term-vars-lst)))

(defines simple-free-vars-acc
  (define simple-free-vars-acc ((x pseudo-termp)
                                (bound-vars symbol-listp)
                                (acc symbol-listp))
    :returns (vars symbol-listp :hyp :guard)
    :verify-guards nil
    (cond ((atom x)
           (if (and x (mbt (symbolp x))
                    (not (member-eq x bound-vars)))
               (add-to-set-eq x acc)
             acc))
          ((eq (car x) 'quote) acc)
          (t (simple-free-vars-lst-acc (cdr x) bound-vars acc))))
  (define simple-free-vars-lst-acc ((x pseudo-term-listp)
                                    (bound-vars symbol-listp)
                                    (acc symbol-listp))
    :returns (vars symbol-listp :hyp :guard)
    (if (atom x)
        acc
      (simple-free-vars-lst-acc (cdr x)
                                bound-vars
                                (simple-free-vars-acc
                                 (car x) bound-vars acc))))
  ///
  (verify-guards simple-free-vars-acc))


(defines simple-free-vars
  :verify-guards nil
  :flag-local nil
  (define simple-free-vars ((x pseudo-termp)
                            (bound-vars symbol-listp))
    :returns (vars symbol-listp :hyp :guard)
    (mbe :logic (cond ((atom x)
                       (and x
                            (mbt (symbolp x))
                            (not (member-eq x bound-vars))
                            (list x)))
                      ((null x) nil)
                      ((eq (car x) 'quote) nil)
                      (t (simple-free-vars-lst (cdr x) bound-vars)))
         :exec (simple-free-vars-acc x bound-vars nil)))
  (define simple-free-vars-lst ((x pseudo-term-listp)
                                (bound-vars symbol-listp))
    :returns (vars symbol-listp :hyp :guard)
    (mbe :logic (if (atom x)
                    nil
                  (union-eq (simple-free-vars-lst (cdr x) bound-vars)
                            (simple-free-vars (car x) bound-vars)))
         :exec (simple-free-vars-lst-acc x bound-vars nil)))
  ///


  (local (defun-sk simple-free-vars-acc-is-simple-free-vars-sk (x bound-vars)
           (forall acc
                   (equal (simple-free-vars-acc x bound-vars acc)
                          (union-eq (simple-free-vars x bound-vars) acc)))
           :rewrite :direct))
  (local (defun-sk simple-free-vars-lst-acc-is-simple-free-vars-lst-sk (x bound-vars)
           (forall acc
                   (equal (simple-free-vars-lst-acc x bound-vars acc)
                          (union-eq (simple-free-vars-lst x bound-vars) acc)))
           :rewrite :direct))
  (local (in-theory (disable simple-free-vars-acc-is-simple-free-vars-sk
                             simple-free-vars-lst-acc-is-simple-free-vars-lst-sk)))

  (local
   (defthm-simple-free-vars-flag
     (defthm simple-free-vars-acc-is-simple-free-vars-lemma
       (simple-free-vars-acc-is-simple-free-vars-sk x bound-vars)
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause))
                               (simple-free-vars x bound-vars)
                               (:free (acc) (simple-free-vars-acc x bound-vars acc))
                               (:free (acc) (simple-free-vars-acc nil bound-vars acc))))))
       :flag simple-free-vars
       :rule-classes nil)
     (defthm simple-free-vars-lst-acc-is-simple-free-vars-lst-lemma
       (simple-free-vars-lst-acc-is-simple-free-vars-lst-sk x bound-vars)
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause))
                               (simple-free-vars-lst x bound-vars)
                               (:free (acc) (simple-free-vars-lst-acc x bound-vars acc))))))
       :flag simple-free-vars-lst
       :rule-classes nil)))

  (defthm simple-free-vars-acc-is-simple-free-vars
    (equal (simple-free-vars-acc x bound-vars acc)
           (union-eq (simple-free-vars x bound-vars) acc))
    :hints (("goal" :use simple-free-vars-acc-is-simple-free-vars-lemma)))
  (defthm simple-free-vars-lst-acc-is-simple-free-vars-lst
    (equal (simple-free-vars-lst-acc x bound-vars acc)
           (union-eq (simple-free-vars-lst x bound-vars) acc))
    :hints (("goal" :use simple-free-vars-lst-acc-is-simple-free-vars-lst-lemma)))

  (defthm-simple-free-vars-flag
    (defthm true-listp-of-simple-free-vars
      (true-listp (simple-free-vars x bound-vars))
      :hints ((and stable-under-simplificationp
                   '(:expand ((simple-free-vars x bound-vars)))))
      :flag simple-free-vars
      :rule-classes :type-prescription)
    (defthm true-listp-of-simple-free-vars-lst
      (true-listp (simple-free-vars-lst x bound-vars))
      :hints ((and stable-under-simplificationp
                   '(:expand ((simple-free-vars-lst x bound-vars)))))
      :flag simple-free-vars-lst
      :rule-classes :type-prescription))

  (local (defthm union-equal-nil
           (implies (true-listp x)
                    (equal (union-equal x nil) x))))

  (verify-guards simple-free-vars)

  (defthm-simple-free-vars-flag
    (defthm simple-free-vars-in-terms-of-simple-term-vars
      (equal (simple-free-vars x bound-vars)
             (set-difference-eq (simple-term-vars x) bound-vars))
      :hints ('(:expand ((simple-term-vars x))))
      :flag simple-free-vars)
    (defthm simple-free-vars-lst-in-terms-of-simple-term-vars
      (equal (simple-free-vars-lst x bound-vars)
             (set-difference-eq (simple-term-vars-lst x) bound-vars))
      :hints ('(:expand ((simple-term-vars-lst x))))
      :flag simple-free-vars-lst)))
