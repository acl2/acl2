; Copyright (C) 2022 Intel Corporation
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
; Original authors: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "clause-processors/pseudo-term-fty" :dir :System)
(include-book "tools/match-tree" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "std/alists/alist-keys" :dir :system)
(local (include-book "std/alists/fast-alist-clean" :dir :system))
(local (include-book "data-structures/no-duplicates" :dir :system))
(local (in-theory (disable fast-alist-clean)))


(define factor-out-trigger (factor a b)
  :verify-guards nil
  (declare (ignore factor))
  (+ a b))

(defevaluator collect-ev collect-ev-lst
  ((binary-+ x y)
   (unary-- x)
   (binary-* x y)
   (factor-out-trigger factor a b)
   (fix x))
  :namedp t)

(def-ev-pseudo-term-fty-support collect-ev collect-ev-lst)

(fty::defmap term-coeff-alist :key-type pseudo-termp :val-type acl2-numberp :true-listp t)

(local (defthm cdr-last-of-term-coeff-alist-fix
         (equal (cdr (last (term-coeff-alist-fix x))) nil)
         :hints(("Goal" :in-theory (enable term-coeff-alist-fix)))))


(local (defthm no-duplicate-keys-of-fast-alist-clean
         (no-duplicatesp-equal (alist-keys (fast-alist-clean x)))
         :hints(("Goal" :induct (fast-alist-clean x)
                 :expand ((fast-alist-clean x))
                 :in-theory (enable alist-keys no-duplicatesp-equal)))))

(local (defthm no-duplicate-keys-of-term-coeff-alist-fix
         (implies (no-duplicatesp-equal (alist-keys x))
                  (no-duplicatesp-equal (alist-keys (term-coeff-alist-fix x))))
         :hints(("Goal" 
                 :in-theory (enable term-coeff-alist-fix alist-keys no-duplicatesp-equal)))))

(local (defthm hons-remove-assoc-of-term-coeff-alist-fix
         (equal (term-coeff-alist-fix (hons-remove-assoc key x))
                (hons-remove-assoc key (term-coeff-alist-fix x)))
         :hints(("Goal" :in-theory (enable term-coeff-alist-fix hons-remove-assoc)))))

(local (defthm alistp-of-append
         (implies (alistp x)
                  (equal (alistp (append x y))
                         (alistp y)))))

(local (defthm cdr-last-when-true-listp
         (and (implies (true-listp x)
                       (equal (cdr (last x)) nil))
              (iff (cdr (last x))
                   (and (consp x)
                        (not (true-listp x)))))))

(local (defthm alistp-of-fast-alist-clean
         (equal (alistp (fast-alist-clean x))
                (true-listp x))
         :hints (("goal" :induct (fast-alist-clean x)
                  :expand ((fast-alist-clean x))))))

(local (defthmd term-coeff-alist-fix-when-not-consp
         (implies (not (consp x))
                  (equal (term-coeff-alist-fix x) nil))
         :hints(("Goal" :in-theory (enable term-coeff-alist-fix)))))

(local (defthm fast-alist-clean-of-term-coeff-alist-fix
         (equal (fast-alist-clean (term-coeff-alist-fix x))
                (term-coeff-alist-fix (fast-alist-clean x)))
         :hints(("Goal" :induct (fast-alist-clean x)
                 :in-theory (enable term-coeff-alist-fix-when-not-consp)
                 :expand ((term-coeff-alist-fix x)
                          (:free (a b) (fast-alist-clean (cons a b)))
                          (:free (a b) (term-coeff-alist-fix (cons a b)))
                          (term-coeff-alist-fix (cdr (last x)))
                          (fast-alist-clean x))))))

(local (defthm term-coeff-alist-p-of-hons-remove-assoc
         (implies (term-coeff-alist-p x)
                  (term-coeff-alist-p (hons-remove-assoc k x)))
         :hints(("Goal" :in-theory (enable hons-remove-assoc)))))

(local (defthm term-coeff-alist-p-of-append
         (implies (term-coeff-alist-p x)
                  (equal (term-coeff-alist-p (append x y))
                         (term-coeff-alist-p y)))))

(local (defthm term-coeff-alist-p-of-fast-alist-clean
         (implies (term-coeff-alist-p x)
                  (term-coeff-alist-p (fast-alist-clean x)))
         :hints (("goal" :induct (fast-alist-clean x)
                  :expand ((fast-alist-clean x))))))

(local (defthm alist-fix-when-term-coeff-alist-p
         (implies (term-coeff-alist-p x)
                  (equal (alist-fix x) x))
         :hints(("Goal" :in-theory (enable term-coeff-alist-p)))))


(local (defthm fix-when-acl2-numberp
         (implies (acl2-numberp x)
                  (equal (fix x) x))))

(local (fty::deffixequiv binary-* :args ((x acl2-numberp) (y acl2-numberp))))
(local (fty::deffixequiv binary-+ :args ((x acl2-numberp) (y acl2-numberp))
         :hints(("Goal" :in-theory (enable fix)))))

;; (local (defthm *-of-fix-1
;;          (equal (* (fix x) y)
;;                 (* x y))))

;; (local (defthm *-of-fix-2
;;          (equal (* x (fix y))
;;                 (* x y))))

(local (in-theory (disable fix
                           pseudo-termp
                           pseudo-term-listp)))

(local (defthm pseudo-term-listp-of-cons
         (equal (pseudo-term-listp (cons a x))
                (and (pseudo-termp a)
                     (pseudo-term-listp x)))
         :hints(("Goal" :in-theory (enable pseudo-term-listp)))))

;; note this isn't the correct evaluation by itself, needs to be cleaned first.
(define like-terms-alist-sum ((x term-coeff-alist-p)
                              (a alistp))
  :returns (sum)
  (if (atom x)
      0
    (if (mbt (and (consp (car x))
                  (pseudo-termp (caar x))))
        (+ (* (cdar x) (fix (collect-ev (caar x) a)))
           (like-terms-alist-sum (cdr x) a))
      (like-terms-alist-sum (cdr x) a)))
  ///
  (defthm like-terms-alist-sum-of-append
    (equal (like-terms-alist-sum (append x y) a)
           (+ (like-terms-alist-sum x a)
              (like-terms-alist-sum y a))))

  (defthm like-terms-alist-sum-nil
    (equal (like-terms-alist-sum nil a) 0))

  (fty::deffixequiv like-terms-alist-sum
    :omit (a)
    :hints(("Goal" :in-theory (enable term-coeff-alist-fix))))

  ;; (defthm like-terms-alist-sum-of-alist-fix
  ;;   (Equal (like-terms-alist-sum (alist-fix x) a)
  ;;          (like-terms-alist-sum x a)))

  (defthm like-terms-alist-sum-of-hons-remove-assoc
    (implies (and (no-duplicatesp-equal (alist-keys x))
                  (pseudo-termp term))
             (equal (like-terms-alist-sum (hons-remove-assoc term x) a)
                    (- (like-terms-alist-sum x a)
                       (let ((look (hons-assoc-equal term (term-coeff-alist-fix x))))
                         (if look (* (collect-ev term a) (cdr look)) 0)))))
    :hints (("goal" :induct (like-terms-alist-sum x a)
             :expand ((hons-remove-assoc term x)
                      (alist-keys x)
                      (:free (a b) (no-duplicatesp-equal (cons a b))))))))

(define like-terms-alist-pair-term ((key pseudo-termp)
                                    (coeff acl2-numberp))
  :returns (term pseudo-termp)
  (b* ((coeff (mbe :logic (fix coeff) :exec coeff)))
    (cond ((eql coeff 0) ''0)
          ((eql coeff 1) (pseudo-term-fix key))
          ((eql coeff -1) (pseudo-term-fncall 'unary-- (list key)))
          (t (pseudo-term-fncall 'binary-* (list (pseudo-term-quote coeff) key)))))
  ///
  (local (defthm *-when-fix-equal
           (implies (equal (fix a) c)
                    (equal (* a b)
                           (* c b)))
           :hints (("goal" :in-theory (enable fix)))))
  (defret collect-ev-of-<fn>
    (acl2::number-equiv (collect-ev term a)
                        (* coeff (collect-ev key a))))

  (fty::deffixequiv like-terms-alist-pair-term))


(local (defthm equal-of-fix-forward
         (implies (equal (fix x) y)
                  (acl2::number-equiv x y))
         :rule-classes :forward-chaining))

(define like-terms-alist-term ((x term-coeff-alist-p)
                               ;; Note. We don't really want to fix things to
                               ;; numbers in general, but if we happen to have
                               ;; just one term in our polynomial, that term
                               ;; happens to have a coeff of 1, and the term
                               ;; doesn't evaluate to a number, we need to fix
                               ;; it to one by adding 0.  This is what this top
                               ;; flag is for.
                               ;; E.g. this could happen if our term was
                               ;; (+ (* 1/2 'foo) (* 1/2 'foo)) -- this evaluates to 0 (i.e. (fix 'foo)) but
                               ;; if we don't take this case into account we'd reduce it to just 'foo
                               ;; since we'd ignore the coeff of 1.
                               top)
  :returns (sum pseudo-termp)
  (cond ((atom x) ''0)
        ((not (mbt (and (consp (car x))
                        (pseudo-termp (caar x)))))
         (like-terms-alist-term (cdr x) top))
        ((atom (term-coeff-alist-fix (cdr x)))
         (let ((pair-term (like-terms-alist-pair-term (caar x) (cdar x))))
           (if top
               (pseudo-term-fncall 'binary-+ (list ''0 pair-term))
             pair-term)))
        (t (pseudo-term-fncall 'binary-+ (list (like-terms-alist-pair-term (caar x) (cdar x))
                                               (like-terms-alist-term (cdr x) nil)))))
  ///

  (local (defthm like-terms-alist-sum-when-atom-when-fixed
           (implies (not (consp (term-coeff-alist-fix x)))
                    (equal (like-terms-alist-sum x a) 0))
           :hints(("Goal" :in-theory (enable like-terms-alist-sum
                                             term-coeff-alist-fix)))))
  
  (defret collect-ev-of-<fn>
    (acl2::number-equiv (collect-ev sum a)
                        (like-terms-alist-sum x a))
    :hints(("Goal" 
            :induct <call>
            :expand ((like-terms-alist-sum x a)
                     (:free (x) (like-terms-alist-sum (list x) a))))))

  (defret <fn>-acl2-numberp-when-top
    (implies top
             (acl2-numberp (collect-ev sum a)))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (term-coeff-alist-fix x)))))
    
  
  (defret collect-ev-of-<fn>-when-top
    (implies top
             (equal (collect-ev sum a)
                    (like-terms-alist-sum x a)))
    :hints (("goal" :use (<fn>-acl2-numberp-when-top
                          collect-ev-of-<fn>)
             :in-theory (disable <fn>-acl2-numberp-when-top
                                 collect-ev-of-<fn>
                                 <fn>))))

  (fty::deffixequiv like-terms-alist-term
    :hints(("Goal" :in-theory (enable term-coeff-alist-fix)))))

(local (in-theory (disable last)))

(define insert-term-in-alist ((term pseudo-termp)
                              (coeff acl2-numberp)
                              (tca term-coeff-alist-p))
  :returns (new-tca term-coeff-alist-p)
  (b* ((tca (term-coeff-alist-fix tca))
       (look (hons-get (pseudo-term-fix term) tca))
       (coeff (mbe :logic (fix coeff) :exec coeff))
       ((unless look)
        (hons-acons (pseudo-term-fix term) coeff tca)))
    (hons-acons (pseudo-term-fix term)
                (+ coeff (mbe :logic (fix (cdr look)) :exec (cdr look)))
                tca))
  ///

  (defret insert-term-in-alist-correct
    (equal (like-terms-alist-sum (fast-alist-clean new-tca) a)
           (+ (* coeff (collect-ev term a))
              (like-terms-alist-sum (fast-alist-clean tca) a)))
    :hints (("goal"
             :expand ((:free (a b) (fast-alist-clean (cons a b)))
                      (:free (x y) (like-terms-alist-sum (cons x y) a))))))

  ;; (defret len-of-<fn>
  ;;   (equal (len new-tca) (+ 1 (len (term-coeff-alist-fix tca)))))
  )



(define collect-like-terms-to-alist ((x pseudo-termp)
                                     (tca term-coeff-alist-p))
  :returns (new-tca term-coeff-alist-p)
  :prepwork ((local (in-theory (enable match-tree-obj-equals-subst-when-successful
                                       match-tree-alist-opener-theory)))
             (local (include-book "meta/pseudo-termp-lemmas" :dir :system))
             (local (include-book "arithmetic/top" :dir :system)))
  (treematch
   x
   ((binary-+ (unary-- (binary-* (quote (:? coeff)) (:? term))) (:? rest))
    (collect-like-terms-to-alist rest (insert-term-in-alist term (- (fix coeff)) tca)))
   ((binary-+ (unary-- (:? term)) (:? rest))
    (collect-like-terms-to-alist rest (insert-term-in-alist term -1 tca)))
   ((binary-+ (binary-* (quote (:? coeff)) (:? term)) (:? rest))
    (collect-like-terms-to-alist rest (insert-term-in-alist term (fix coeff) tca)))
   ((binary-+ (:? term) (:? rest))
    (collect-like-terms-to-alist rest (insert-term-in-alist term 1 tca)))
   ((unary-- (:? term))
    (insert-term-in-alist term -1 tca))
   (& (insert-term-in-alist x 1 tca)))
  ///

  (defret collect-like-terms-to-alist-correct
    (equal (like-terms-alist-sum (fast-alist-clean new-tca) a)
           (+ (collect-ev x a)
              (like-terms-alist-sum (fast-alist-clean tca) a)))
    :hints (("goal" :induct <call>))))



(define collect-like-terms-meta ((x pseudo-termp))
  :returns (new-x pseudo-termp :hyp (pseudo-termp x))
  :guard-hints ((and stable-under-simplificationp
                     '(:expand ((pseudo-termp x)))))
  (b* (((unless (and (consp x)
                     (equal (car x) 'binary-+)))
        ;; need to trigger this on + or it doesn't make sense, plus this
        ;; ensures that the term evaluates to a number
        x)
       (tca1 (collect-like-terms-to-alist x nil))
       (tca (fast-alist-clean tca1))
       (tca-len (len tca))
       ((when (or (equal (len tca1) tca-len)
                  (< tca-len 1)))
        ;; !! Heuristic -- if we haven't collected any like terms, then fail by just producing x.
        x))
    (like-terms-alist-term tca t))
  ///
  
  (defthmd collect-like-terms
    (equal (collect-ev x a)
           (collect-ev (collect-like-terms-meta x) a))
    :hints (("goal" :cases ((acl2-numberp (collect-ev x a)))))
    :rule-classes ((:meta :trigger-fns (binary-+)))))



(local (include-book "meta/pseudo-termp-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))    

(define mk-binary-+-for-factor-out ((x pseudo-termp)
                                    (y pseudo-termp))
  :returns (sum pseudo-termp)
  (cond ((equal x ''0) (pseudo-term-fix y))
        ((equal y ''0) (pseudo-term-fix x))
        (t `(binary-+ ,(pseudo-term-fix x)
                      ,(pseudo-term-fix y))))
  ///
  (defret <fn>-correct
    (number-equiv (collect-ev sum a)
                  (+ (collect-ev x a)
                     (collect-ev y a)))))

(define mk-binary-*-for-factor-out ((x pseudo-termp)
                                    (y pseudo-termp))
  :returns (prod pseudo-termp)
  (cond ((equal x ''1) (pseudo-term-fix y))
        ((equal y ''1) (pseudo-term-fix x))
        (t `(binary-* ,(pseudo-term-fix x)
                      ,(pseudo-term-fix y))))
  ///
  (defret <fn>-correct
    (number-equiv (collect-ev prod a)
                  (* (collect-ev x a)
                     (collect-ev y a)))))

(define mk-unary-minus-for-factor-out ((x pseudo-termp))
  :returns (neg pseudo-termp
                :hints (("Goal" :expand ((:free (val) (pseudo-termp (list 'quote val)))))))
  (cond ((and (consp x)
              (eq (car x) 'quote)
              (acl2-numberp (cadr x)))
         (kwote (- (cadr x))))
        (t `(unary-- ,(pseudo-term-fix x))))
  ///
  (defret <fn>-correct
    (number-equiv (collect-ev neg a)
                  (- (collect-ev x a)))))


(define factor-out-from-product ((factor pseudo-termp)
                                 (prod pseudo-termp))
  :returns (mv found (new-prod pseudo-termp))

  :prepwork ((local (in-theory (enable match-tree-obj-equals-subst-when-successful
                                       match-tree-alist-opener-theory))))
  :verify-guards nil
  (if (equal (pseudo-term-fix factor)
             (pseudo-term-fix prod))
      (mv t ''1)
    (treematch
     prod
     ((binary-* (:? a) (:? b))
      (b* (((mv found a1) (factor-out-from-product factor a))
           ((when found)
            (mv t (mk-binary-*-for-factor-out a1 b)))
           ((mv found b1) (factor-out-from-product factor b)))
        (if found
            (mv t (mk-binary-*-for-factor-out a b1))
          (mv nil nil))))
     ((unary-- (:? a))
      (b* (((mv found a1) (factor-out-from-product factor a)))
        (if found
            (mv t (mk-unary-minus-for-factor-out a1))
          (mv nil nil))))
     (& (mv nil nil))))
  ///

  (verify-guards factor-out-from-product)
  
  (defret factor-out-from-product-correct
    (implies found
             (number-equiv (* (collect-ev factor a)
                              (collect-ev new-prod a))
                           (collect-ev prod a)))
    :hints (("goal" :induct <call>
             :expand ((:free (factor) <call>)))
            (and stable-under-simplificationp
                 '(:IN-THEORY (ENABLE fix))))))


(define factor-out-from-sum ((factor pseudo-termp)
                             (sum pseudo-termp))
  :returns (mv (factored pseudo-termp)
               (unfactored pseudo-termp))
  :verify-guards nil
  :prepwork ((local (in-theory (enable match-tree-obj-equals-subst-when-successful
                                       match-tree-alist-opener-theory))))
  (treematch
   sum
   ((binary-+ (:? a) (:? b))
    (b* (((mv a-fact a-unfact) (factor-out-from-sum factor a))
         ((mv b-fact b-unfact) (factor-out-from-sum factor b)))
      (mv (mk-binary-+-for-factor-out a-fact b-fact)
          (mk-binary-+-for-factor-out a-unfact b-unfact))))
   (& (b* (((mv found new-term) (factor-out-from-product factor sum)))
        (if found
            (mv new-term ''0)
          (mv ''0 (pseudo-term-fix sum))))))
  ///
  (verify-guards factor-out-from-sum)
  
  (local
   (defret <fn>-correct-lemma
     (number-equiv (+ (collect-ev unfactored a)
                      (* (collect-ev factor a)
                         (collect-ev factored a)))
                   (collect-ev sum a))))
  (defret <fn>-correct
    (number-equiv (collect-ev unfactored a)
                  (- (collect-ev sum a)
                     (* (collect-ev factor a)
                        (collect-ev factored a))))
    :hints (("goal" :use <fn>-correct-lemma
             :in-theory (e/d (fix)
                             (<fn>-correct-lemma
                              <fn>))))))

(define mk-fix-for-factor ((x pseudo-termp))
  :returns (fix pseudo-termp)
  :prepwork ((local (in-theory (enable match-tree-obj-equals-subst-when-successful
                                       match-tree-alist-opener-theory))))
  (treematch
   x
   ((binary-+ (:? a) (:? b)) (pseudo-term-fix x))
   ((binary-* (:? a) (:? b)) (pseudo-term-fix x))
   ((unary-- (:? a)) (pseudo-term-fix x))
   (& `(fix ,(pseudo-term-fix x))))
  ///
  (defret <fn>-correct
    (equal (collect-ev fix a)
           (fix (collect-ev x a)))))
             


(define factor-out-metafn ((x pseudo-termp))
  :returns (new-x pseudo-termp)
  :prepwork ((local (in-theory (enable match-tree-obj-equals-subst-when-successful
                                       match-tree-alist-opener-theory))))
  (treematch
   x
   ((factor-out-trigger (:? factor) (:? a) (:? b))
    (b* (((mv a-fact a-unfact) (factor-out-from-sum factor a))
         ((mv b-fact b-unfact) (factor-out-from-sum factor b)))
      (mk-fix-for-factor
       (mk-binary-+-for-factor-out
        (mk-binary-*-for-factor-out factor (mk-binary-+-for-factor-out a-fact b-fact))
        (mk-binary-+-for-factor-out a-unfact b-unfact)))))
   (& (pseudo-term-fix x)))
  ///
  (defthm factor-out-meta
    (equal (collect-ev x a)
           (collect-ev (factor-out-metafn x) a))
    :hints (("goal" :in-theory (enable factor-out-trigger)))
    :rule-classes ((:meta :trigger-fns (factor-out-trigger)))))

;;; Example usage of factor-out-metafn -- needs to be triggered by some kind of
;;; bind-free rule.

(local
 (defthm factor-out-trigger-when-q-present
   (implies (bind-free
             (and (equal a 'a)
                  (b* (((mv b-fact ?b-unfact) (factor-out-from-sum 'q b)))
                    (and (not (equal b-fact ''0))
                         (prog2$ (cw "a: ~x0~%b: ~x1~%" a b)
                                 '((q . q))))))
             (q))
            (equal (+ a b)
                   (factor-out-trigger q a b)))
   :hints(("Goal" :in-theory (e/d (factor-out-trigger)
                                  (factor-out-meta))))))

(local
 (defthm prove-factor-out-of-q
   (equal (+ a
             (* b (- q) c d)
             (* e f q g)
             h i
             (* q k)
             (* l m q)
             n o p)
          (+ (* q (+ (* b -1 c d)
                     (* e f g)
                     k
                     (* l m)))
             a h i n o p))
   :hints (("goal" :in-theory '(factor-out-trigger-when-q-present
                                factor-out-meta)))))
    
  

        




  
