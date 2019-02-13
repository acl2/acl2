; Copyright (C) 2018 Centaur Technology
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

;; This defines eval-alists-agree and eval-alist-equiv, which are like
;; alists-agree and alist-equiv from std/alists/alist-equiv but don't
;; distinguish between an unbound key and a binding of NIL.  This is convenient
;; because defevaluator-style evaluators don't care about whether keys are
;; bound or not, just the (cdr (assoc)).  

;; Note: we normalize assoc to hons-assoc-equal to follow the convention of
;; std/alists.  Even though evaluators use assoc-equal, that can easily be
;; normalized to hons-assoc-equal because they only look up non-nil variables,
;; for which assoc-equal and hons-assoc-equal are the same, even if the alist
;; is not an alist.  So -- when using this book, you should enable the rule
;; ASSOC-IS-HONS-ASSOC-EQUAL-WHEN-KEY-NONNIL, and LOOKUP-WHEN-EVAL-ALISTS-AGREE
;; as appropriate.

(include-book "std/util/define" :dir :system)
(include-book "std/lists/mfc-utils" :dir :system)
(include-book "std/alists/alist-defuns" :dir :system)
(include-book "std/util/termhints" :dir :system)
(include-book "term-vars")


(defthmd assoc-is-hons-assoc-equal-when-key-nonnil
  (implies k
           (equal (assoc k x)
                  (hons-assoc-equal k x))))
(local (in-theory (enable assoc-is-hons-assoc-equal-when-key-nonnil)))

(define eval-alists-agree-bad-guy (keys x y)
  (if (atom keys)
      nil
    (if (equal (cdr (hons-assoc-equal (car keys) x))
               (cdr (hons-assoc-equal (car keys) y)))
        (eval-alists-agree-bad-guy (cdr keys) x y)
      (car keys)))
  ///
  (defthm eval-alists-agree-bad-guy-member-when-nonnil
    (b* ((k (eval-alists-agree-bad-guy keys x y)))
      (implies k
               (member k keys))))

  (defthm eval-alists-agree-bad-guy-differs-when-nonnil
    (b* ((k (eval-alists-agree-bad-guy keys x y)))
      (implies k
               (not (equal (cdr (hons-assoc-equal k x))
                           (cdr (hons-assoc-equal k y)))))))

  (defthm eval-alists-agree-bad-guy-member-when-bad-key
    (implies (and (member k keys)
                  (not (equal (cdr (hons-assoc-equal k x))
                              (cdr (hons-assoc-equal k y)))))
             (b* ((k (eval-alists-agree-bad-guy keys x y)))
               (member k keys))))

  (defthm eval-alists-agree-bad-guy-differs-when-bad-key
    (implies (and (member k keys)
                  (not (equal (cdr (hons-assoc-equal k x))
                              (cdr (hons-assoc-equal k y)))))
             (b* ((k (eval-alists-agree-bad-guy keys x y)))
               (not (equal (cdr (hons-assoc-equal k x))
                           (cdr (hons-assoc-equal k y))))))))

(define eval-alists-agree (keys x y)
  (if (atom keys)
      t
    (and (equal (cdr (hons-assoc-equal (car keys) x))
                (cdr (hons-assoc-equal (car keys) y)))
         (eval-alists-agree (cdr keys) x y)))
  ///
  (defthmd lookup-when-eval-alists-agree
    (implies (and (eval-alists-agree keys x y)
                  (member k keys))
             (equal (cdr (hons-assoc-equal k x))
                    (cdr (hons-assoc-equal k y))))
    :rule-classes ((:rewrite :match-free :all)))

  (defthm eval-alists-agree-reflexive
    (eval-alists-agree keys x x))

  (defthmd eval-alists-agree-symmetric
    (implies (eval-alists-agree keys y x)
             (eval-alists-agree keys x y)))

  (defthmd eval-alists-agree-transitive
    (implies (and (eval-alists-agree keys x y)
                  (eval-alists-agree keys y z))
             (eval-alists-agree keys x z)))

  (defthmd eval-alists-agree-by-bad-guy
    (implies (rewriting-positive-literal `(eval-alists-agree ,keys ,x ,y))
             (iff (eval-alists-agree keys x y)
                  (b* ((key (eval-alists-agree-bad-guy keys x y)))
                    (implies (member key keys)
                             (equal (cdr (hons-assoc-equal key x))
                                    (cdr (hons-assoc-equal key y)))))))
    :hints(("Goal" :in-theory (enable eval-alists-agree-bad-guy))))

  (defthm eval-alists-agree-when-subset
    (implies (and (eval-alists-agree keys2 x y)
                  (subsetp keys1 keys2))
             (eval-alists-agree keys1 x y))
    :hints(("Goal" :in-theory (enable lookup-when-eval-alists-agree)))))




(local (defthmd hons-assoc-equal-when-not-member-alist-keys
         (implies (not (member k (alist-keys x)))
                  (not (hons-assoc-equal k x)))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(define eval-alist-equiv-bad-guy (x y)
  (or (eval-alists-agree-bad-guy (alist-keys x) x y)
      (eval-alists-agree-bad-guy (alist-keys y) x y))
  ///

  (defthm eval-alist-equiv-bad-guy-differs-when-nonnil
    (b* ((k (eval-alist-equiv-bad-guy x y)))
      (implies k
               (not (equal (cdr (hons-assoc-equal k x))
                           (cdr (hons-assoc-equal k y)))))))

  (defthm eval-alist-equiv-bad-guy-differs-when-bad-key
    (implies (not (equal (cdr (hons-assoc-equal k x))
                         (cdr (hons-assoc-equal k y))))
             (b* ((k (eval-alist-equiv-bad-guy x y)))
               (not (equal (cdr (hons-assoc-equal k x))
                           (cdr (hons-assoc-equal k y))))))
    :hints (("goal" :use ((:instance eval-alists-agree-bad-guy-differs-when-bad-key
                           (keys (alist-keys x)))
                          (:instance eval-alists-agree-bad-guy-differs-when-bad-key
                           (keys (alist-keys y))))
             :in-theory (e/d (hons-assoc-equal-when-not-member-alist-keys)
                             (eval-alists-agree-bad-guy-differs-when-bad-key))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:cases ((eval-alists-agree-bad-guy (alist-keys y) x y)))))))


(define eval-alist-equiv (x y)
  (and (eval-alists-agree (alist-keys x) x y)
       (eval-alists-agree (alist-keys y) x y))
  ///

  (defthmd eval-alist-equiv-by-bad-guy
    (implies (rewriting-positive-literal `(eval-alist-equiv ,x ,y))
             (iff (eval-alist-equiv x y)
                  (b* ((key (eval-alist-equiv-bad-guy x y)))
                    (equal (cdr (hons-assoc-equal key x))
                           (cdr (hons-assoc-equal key y))))))
    :hints(("goal" :do-not-induct t
            :in-theory (enable lookup-when-eval-alists-agree))
           (use-termhint
            (b* ((k (eval-alist-equiv-bad-guy x y))
                 ((when (eval-alist-equiv x y))
                  (b* (((when (member k (alist-keys x)))
                        ''(:use ((:instance mark-clause-is-true (x 'equiv-and-bound-in-x)))))
                       ((when (member k (alist-keys y)))
                        ''(:use ((:instance mark-clause-is-true (x 'equiv-and-bound-in-y))))))
                    ''(:use ((:instance mark-clause-is-true (x 'equiv-and-unbound)))
                       :in-theory (enable hons-assoc-equal-when-not-member-alist-keys)))))
              ''(:use ((:instance mark-clause-is-true (x 'inequiv)))
                 :in-theory (enable eval-alists-agree-by-bad-guy)))))
    :otf-flg t)

  (defthm eval-alist-equiv-reflexive
    (eval-alist-equiv x x))

  (defthmd eval-alist-equiv-symmetric
    (implies (eval-alist-equiv y x)
             (eval-alist-equiv x y))
    :hints(("Goal" :in-theory (enable eval-alists-agree-symmetric))))

  (local
   (defthm lookup-congruence-when-eval-alist-equiv-pre
     (implies (eval-alist-equiv x y)
              (equal (cdr (hons-assoc-equal k x))
                     (cdr (hons-assoc-equal k y))))
     :hints(("Goal" :in-theory (enable lookup-when-eval-alists-agree) 
             :cases ((member k (alist-keys x))
                     (member k (alist-keys y)))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable hons-assoc-equal-when-not-member-alist-keys))))))

  (defthmd eval-alist-equiv-transitive
    (implies (and (eval-alist-equiv x y)
                  (eval-alist-equiv y z))
             (eval-alist-equiv x z))
    :hints(("Goal" :in-theory (e/d (eval-alist-equiv-by-bad-guy)
                                   (eval-alist-equiv)))))

  (defequiv eval-alist-equiv
    :hints(("Goal" :in-theory (e/d (eval-alist-equiv-symmetric
                                    eval-alist-equiv-transitive)
                                   (eval-alist-equiv)))))

  (defthm lookup-congruence-when-eval-alist-equiv
    (implies (eval-alist-equiv x y)
             (equal (cdr (hons-assoc-equal k x))
                    (cdr (hons-assoc-equal k y))))
    :hints(("Goal" :by lookup-congruence-when-eval-alist-equiv-pre))
    :rule-classes :congruence))



(defevaluator base-ev base-ev-list () :namedp t)


(local (in-theory (enable lookup-when-eval-alists-agree)))

(local (defthm not-member-when-subset
         (implies (and (subsetp a b)
                       (not (member x b)))
                  (not (member x a)))))


(local (in-theory (enable base-ev-of-nonsymbol-atom)))

;; (local (defthm member-of-union
;;          (iff (member x (union-eq a b))
;;               (or (member x a) (member x b)))
;;          :hints(("Goal" :induct (union-equal a b)))))

(local (defthm subsetp-of-union
         (iff (subsetp (union-eq a b) c)
              (and (subsetp a c)
                   (subsetp b c)))
         :hints(("Goal" :in-theory (enable subsetp union-eq)
                 :induct (union-equal a b)))))

(defthm-simple-term-vars-flag
  (defthm base-ev-when-eval-alists-agree
    (implies (and (eval-alists-agree vars a1 a2)
                  (subsetp (simple-term-vars x) vars))
             (equal (base-ev x a1)
                    (base-ev x a2)))
    :hints ('(:expand ((simple-term-vars x)))
            (and stable-under-simplificationp
                 '(:in-theory (enable base-ev-of-fncall-args))))
    :flag simple-term-vars)
  (defthm base-ev-list-when-eval-alists-agree
    (implies (and (eval-alists-agree vars a1 a2)
                  (subsetp (simple-term-vars-lst x) vars))
             (equal (base-ev-list x a1)
                    (base-ev-list x a2)))
    :hints ('(:expand ((simple-term-vars-lst x))))
    :flag simple-term-vars-lst))


(defthm-simple-term-vars-flag
  (defthm base-ev-when-eval-alist-equiv
    (implies (eval-alist-equiv a1 a2)
             (equal (base-ev x a1)
                    (base-ev x a2)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable base-ev-of-fncall-args))))
    :flag simple-term-vars
    :rule-classes :congruence)
  (defthm base-ev-list-when-eval-alist-equiv
    (implies (eval-alist-equiv a1 a2)
             (equal (base-ev-list x a1)
                    (base-ev-list x a2)))
    :flag simple-term-vars-lst
    :rule-classes :congruence))



