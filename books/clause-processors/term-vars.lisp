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
;; (include-book "std/lists/sets" :dir :system)

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
    :returns (vars symbol-listp :hyp :guard)
    :verify-guards nil
    (cond ((null x) acc)
          ((atom x) (add-to-set-eq x acc))
          ((eq (car x) 'quote) acc)
          (t (simple-term-vars-lst-acc (cdr x) acc))))
  (define simple-term-vars-lst-acc ((x pseudo-term-listp)
                                    (acc symbol-listp))
    :returns (vars symbol-listp :hyp :guard)
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
    :returns (vars symbol-listp :hyp :guard)
    (mbe :logic (cond ((null x) nil)
                      ((atom x) (list x))
                      ((eq (car x) 'quote) nil)
                      (t (simple-term-vars-lst (cdr x))))
         :exec (simple-term-vars-acc x nil)))
  (define simple-term-vars-lst ((x pseudo-term-listp))
    :returns (vars symbol-listp :hyp :guard)
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
