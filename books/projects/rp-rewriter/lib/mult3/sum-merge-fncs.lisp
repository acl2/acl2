; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020 Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "fnc-defs")

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (include-book "lemmas"))

(include-book "pp-flatten-meta-fncs")

(include-book "std/util/defines" :dir :system)

(include-book "equal-meta")

(local
 (in-theory (disable +-IS-SUM)))

(define valid-list-termp (term)
  (case-match term
    (('list . &)
     t)
    (''nil
     t)
    (&  (hard-error 'valid-list-termp
                    "Unexpected list term ~p0 ~%"
                    (list (cons #\0 term))))))

#|(define extract-from-list ((term valid-list-termp))
  (case-match term
    (('list . lst)
     lst)
    (''nil
     nil)
    (& term)))||#


(define cons-pp-to-pp-lst-lst ((pp valid-pp-p)
                               pp-lst-lst)
  (b* ((pp-lst (pp-to-pp-lst pp)))
    (if pp-lst
        (cons pp-lst pp-lst-lst)
      pp-lst-lst)))

(define append-pp-lst-lsts (l1 l2)
  ;;(append l1 l2)
  ;; same as append but "cons" is controlled so that it can be converted to
  ;; hons at will easily.
  (if (atom l1)
      l2
    (pp-cons (car l1)
             (append-pp-lst-lsts (cdr l1) l2))))

(acl2::defines
 s-order
 :flag-local nil
 :prepwork
 ((local
   (in-theory (e/d (rp::measure-lemmas)
                   (+-IS-SUM)))))
 (define s-order ((x rp-termp)
                  (y rp-termp))
   :measure (+ (cons-count x)
               (cons-count y))
   :returns (mv order equals)
   (b* ((x (ex-from-rp$ x))
        (y (ex-from-rp$ y)))
     (cond ((equal x y)
            (mv nil t))
           ((or (atom x)
                (atom y)
                (quotep x)
                (quotep y))
            (if (equal x y)
                (mv nil t)
              (mv (lexorder x y) nil)))
           (t (if (equal (car x) (car y))
                  (s-order-lst (cdr x) (cdr y))
                (mv (small-alphorder (car x) (car y)) nil))))))
 (define s-order-lst ((lst1 rp-term-listp)
                      (lst2 rp-term-listp))
   :measure (+ (cons-count lst1)
               (cons-count lst2))
   :returns (mv order equals)
   (cond ((or (atom lst1)
              (atom lst2))
          (if (equal lst1 lst2)
              (mv nil t)
            (mv (lexorder lst1 lst2) nil)))
         (t (b* (((mv car-order car-equal)
                  (s-order (car lst1) (car lst2)))
                 ((unless car-equal)
                  (mv car-order nil))
                 ((mv cdr-order cdr-equal)
                  (s-order-lst (cdr lst1) (cdr lst2))))
              (mv cdr-order cdr-equal))))))


(defret-mutual
  s-order-sanity
  (std::defretd s-order-sanity
    (and (implies (mv-nth 0 (s-order x y))
                  (not (mv-nth 0 (s-order y x))))
         (implies (mv-nth 1 (s-order x y))
                  (and (not (mv-nth 0 (s-order x y)))
                       (not (mv-nth 0 (s-order y x)))))
         (equal (mv-nth 1 (s-order y x))
                (mv-nth 1 (s-order x y)))) 
    :fn s-order)
  (std::defretd s-order-lst-sanity
    (and (implies (mv-nth 0 (s-order-lst lst1 lst2))
                  (not (mv-nth 0 (s-order-lst lst2 lst1))))
         (implies (mv-nth 1 (s-order-lst lst1 lst2))
                  (and (not (mv-nth 0 (s-order-lst lst2 lst1)))
                       (not (mv-nth 0 (s-order-lst lst1 lst2)))))
         (equal (mv-nth 1 (s-order-lst lst1 lst2))
                (mv-nth 1 (s-order-lst lst2 lst1))))
    :fn s-order-lst)
  :hints (("Goal"
           :in-theory (e/d (s-order
                            s-order-lst)
                           ()))))

(encapsulate
  nil
  (define ex-from-rp/--loose (x)
    :returns (res rp-termp :hyp (rp-termp x))
    (cond ((and (consp x)
                (consp (cdr x)))
           (if (or (equal (car x) '--))
               (ex-from-rp/--loose (cadr x))
             (if (and (equal (car x) 'rp)
                      (consp (cddr x)))
                 (ex-from-rp/--loose (caddr x))
               x)))
          (t x)))

  (define ex-from-rp/-- (x)
    :returns (res rp-termp :hyp (rp-termp x))
    :prepwork ((local
                (in-theory (enable is-rp))))
    (cond ((--.p x)
           (ex-from-rp/-- (cadr x)))
          ((is-rp x)
           (ex-from-rp/-- (caddr x)))
          (t x)))

  (define ex-from--- (x)
    :inline t
    (case-match x (('-- a) a) (& x)))

  (define pp-order ((x rp-termp)
                    (y rp-termp))
    :inline t
    :returns (mv (order)
                 (equals booleanp))
    (b* ((x (ex-from-rp$ x))
         (y (ex-from-rp$ y))
         ((when (equal y ''1))
          (mv nil (equal x y)))
         ((when (equal x ''1))
          (mv t (equal x y)))
         ((mv x-lst x-hash x-good-format)
          (case-match x
            (('and-list ('quote hash) ('list . lst))
             (mv lst (ifix hash) t))
            (&
             (mv (list x) 0 nil))))
         ((mv y-lst y-hash y-good-format)
          (case-match y
            (('and-list ('quote hash) ('list . lst))
             (mv lst (ifix hash) t))
            (&
             (mv (list y) 0 nil)))))
      (if (= x-hash y-hash)
          (b* (((mv order equals)
                (pp-list-order x-lst y-lst)))
            (if (and x-good-format y-good-format)
                (mv order equals)
              (mv order (equal x y))))
        (mv (> x-hash y-hash) nil)
        ;;(pp-list-order x-lst y-lst)
        )))

  #|(define pp-order (x y)
  :inline t
  :returns (mv (order)
  (equals booleanp))
  (b* (;;(x (ex-from--- x))
  ;;(y (ex-from--- y))
  (x-orig x)
  (y-orig y))
  (b* (((mv x atom-x len-x)
  (case-match x
  (('and-list & ('list . lst))
  (mv lst nil (len lst)))
  (('binary-and & &)
  (mv (cdr x) nil 2))
  (''1
  (mv x t 1))
  (('bit-of & &)
  (mv x t 1))
  (('rp ''bitp &)
  (mv x t 1))
  (& (mv x t -1))))
  ((mv y atom-y len-y)
  (case-match y
  (('and-list & ('list . lst))
  (mv lst nil (len lst)))
  (('binary-and & &)
  (mv (cdr y) nil 2))
  (''1
  (mv y t 1))
  (('rp ''bitp &)
  (mv y t 1))
  (('bit-of & &)
  (mv y t 1))
  (& (mv y t -1)))))
  (cond
  ((not (equal len-x len-y))
  (cond
  ((or (equal len-x -1)
  (equal len-y -1))
  (mv nil (equal x-orig y-orig)))
  ((equal len-y 2)
  (mv t nil))
  ((equal len-x 2)
  (mv nil nil))
  (t (mv (> len-x len-y) nil))))
  ((or atom-x atom-y)
  (cond ((not atom-x)
  (if (consp x)
  (if (equal (car x) y)
  (mv nil
  (equal x-orig y-orig)
;(atom (cdr x)) ; ;
  )
  (mv (not (lexorder y (car x))) nil))
  (mv t nil)))
  ((not atom-y)
  (if (consp y)
  (if (equal (car y) x)
  (mv (not (atom y))
  (equal x-orig y-orig)
;(atom y) ; ;
  )
  (mv (not (lexorder (car y) x)) nil))
  (mv nil nil)))
  (t (if (equal x y)
  (mv nil t)
  (mv (not (lexorder y x)) nil)))))
  (t (pp-list-order x y))))))||#

  (define pp-lst-orderedp ((lst rp-term-listp))
    (if (atom lst)
        t
      (if (atom (cdr lst))
          t
        (and (b* (((mv order &) (pp-order (ex-from-rp/-- (cadr lst))
                                          (ex-from-rp/-- (car lst)))))
               (not order))
             (pp-lst-orderedp (cdr lst))))))

  (define pp-orderedp ((pp rp-termp))
    (case-match pp
      (('list . lst)
       (pp-lst-orderedp lst))
      (''nil
       t)
      (& nil))))



(progn
  (define pp-order-and-negated-termsp ((term1 rp-termp)
                                       (term2 rp-termp))
    :returns (mv
              (order)
              (negated-terms booleanp)
              (equal-terms booleanp))
    (b* (((mv neg1 term1)
          (case-match term1 (('-- a) (mv t a)) (& (mv nil term1))))
         ((mv neg2 term2)
          (case-match term2 (('-- a) (mv t a)) (& (mv nil term2))))
         ((mv order equals)
          (pp-order term1 term2)))
      (mv  order
           (and (not (equal neg1 neg2))
                equals)
           equals)))

  (define pp-sum-merge-aux ((pp1-lst rp-term-listp)
                            (pp2-lst rp-term-listp))
    :measure (+ (cons-count pp1-lst)
                (cons-count pp2-lst))
    :hints (("Goal"
             :in-theory (e/d (measure-lemmas) ())))
    :returns (merged-pp-lst rp-term-listp
                            :hyp (and (rp-term-listp pp1-lst)
                                      (rp-term-listp pp2-lst)))

    (cond ((atom pp1-lst) pp2-lst)
          ((atom pp2-lst) pp1-lst)
          (t (b* ((cur1 (car pp1-lst))
                  (cur2 (car pp2-lst))
                  ((when (equal cur1 ''0))
                   (pp-sum-merge-aux (cdr pp1-lst) pp2-lst ))
                  ((when (equal cur2 ''0))
                   (pp-sum-merge-aux pp1-lst (cdr pp2-lst) ))
                  ((mv order negated-termsp &)
                   (pp-order-and-negated-termsp cur1 cur2)))
               (cond (negated-termsp
                      (pp-sum-merge-aux (cdr pp1-lst) (cdr pp2-lst) ))
                     (order
                      (b* ((rest (pp-sum-merge-aux (cdr pp1-lst) pp2-lst )))
                        (pp-cons cur1 rest)))
                     (t
                      (b* ((rest (pp-sum-merge-aux pp1-lst (cdr pp2-lst) )))
                        (pp-cons cur2 rest))))))))

  (define pp-sum-merge ((pp1 rp-termp)
                        (pp2 rp-termp))
    :returns (merged-pp rp-termp
                        :hyp (and (rp-termp pp1)
                                  (rp-termp pp2)))
    (b* (((when (equal pp1 ''nil))
          pp2)
         ((when (equal pp2 ''nil))
          pp1)
         ((when (or (not (case-match pp1 (('list . &) t)))
                    (not (case-match pp2 (('list . &) t)))))
          (progn$ (cw "pp-sum-merge-fail pp1=~p0~%pp2=~p1 ~%" pp1 pp2)
                  (hard-error 'pp-sum-merge "" nil)
                  `(binary-append ,pp1 ,pp2))))
      (b* ((res (pp-sum-merge-aux (cdr pp1) (cdr pp2))))
        (if (and res
                 (not (equal res (list ''0))))
            (create-list-instance res)
          ''nil))))

  ;;(memoize 'pp-sum-merge :condition '(and (not (equal pp1 'nil)) (not (equal
  ;;pp2 'nil))))
  )



;;(pp-lst-sum-merge '((a a a a b b b c d) (b c d e) (c d e m) (c f) (d f m))
;;:cough t)

(progn

  (define s-order-and-negated-termsp ((term1 rp-termp)
                                      (term2 rp-termp))
    (b* (;;(term1 (ex-from-rp-loose term1))
         ;;(term2 (ex-from-rp-loose term2))
         ((mv neg1 term1)
          (case-match term1 (('-- a) (mv t a)) (& (mv nil term1))))
         ((mv neg2 term2)
          (case-match term2 (('-- a) (mv t a)) (& (mv nil term2))))
         ((mv order terms-are-equal)
          (s-order term1 term2)))
      (mv order
          (and (not (equal neg1 neg2))
               terms-are-equal))))

  (define s-sum-ordered-listp ((lst rp-term-listp))
    (if (atom lst)
        (equal lst nil)
      (if (atom (cdr lst))
          t
        (and (b* (((mv order &) (s-order-and-negated-termsp (cadr lst) (car lst))))
               (not order))
             (s-sum-ordered-listp (cdr lst))))))
        
  (define s-sum-merge-aux ((s1-lst rp-term-listp)
                           (s2-lst rp-term-listp))
    :measure (+ (cons-count s1-lst)
                (cons-count s2-lst))
    :hints (("Goal"
             :in-theory (e/d (measure-lemmas) ())))
    :returns (merged-s-lst rp-term-listp
                           :hyp (and (rp-term-listp s1-lst)
                                     (rp-term-listp s2-lst)))
    (cond ((atom s1-lst)
           s2-lst)
          ((atom s2-lst)
           s1-lst)
          (t (b* ((cur1 (car s1-lst))
                  (cur2 (car s2-lst))
                  ((mv order should-cancel)
                   (s-order-and-negated-termsp cur1 cur2)))
               (cond (should-cancel
                      (s-sum-merge-aux (cdr s1-lst) (cdr s2-lst)))
                     ((equal cur1 ''0)
                      (s-sum-merge-aux (cdr s1-lst) s2-lst))
                     ((equal cur2 ''0)
                      (s-sum-merge-aux s1-lst (cdr s2-lst)))
                     (order
                      (b* ((rest (s-sum-merge-aux (cdr s1-lst) s2-lst)))
                        (cons cur1 rest)))
                     (t
                      (b* ((rest (s-sum-merge-aux s1-lst (cdr s2-lst))))
                        (cons cur2 rest))))))))

  (define s-sum-merge ((s1 rp-termp)
                       (s2 rp-termp))
    :returns (merged-s rp-termp
                       :hyp (and (rp-termp s1)
                                 (rp-termp s2)))

    (b* (((when (equal s1 ''nil))
          s2)
         ((when (equal s2 ''nil))
          s1)
         ((when (or (not (case-match s1 (('list . &) t)))
                    (not (case-match s2 (('list . &) t)))))
          (progn$ (cw "s-sum-merge-fail s1=~p0~%s2=~p1 ~%" s1 s2)
                  (hard-error 's-sum-merge "" nil)
                  `(binary-append ,s1 ,s2) )))
      (b* ((res (s-sum-merge-aux (cdr s1) (cdr s2))))
        (create-list-instance res)))))

(progn
  (define s-fix-pp-args-aux ((pp-lst rp-term-listp))
    :returns (cleaned-pp-lst rp-term-listp
                             :hyp (rp-term-listp pp-lst))
    (if (atom pp-lst)
        nil
      (b* ((cur (car pp-lst))
           (cur-orig cur)
           (cur (ex-from-rp$ cur))
           ((mv next next-present)
            (if (atom (cdr pp-lst)) (mv ''0 nil) (mv (cadr pp-lst) t))))
        (cond ((and next-present
                    (rp-equal-cnt cur next 0))
               (s-fix-pp-args-aux (cddr pp-lst)))
              ((case-match cur (('-- &) t))
               (pp-cons (cadr cur)
                        (s-fix-pp-args-aux (cdr pp-lst))))
              (t
               (pp-cons-with-hint cur-orig
                                  (s-fix-pp-args-aux (cdr pp-lst))
                                  pp-lst))))))

  ;; (s-pp-fix-aux '(a a b b f f g g))
  ;; (s-pp-fix-aux '(a b c d (-- e) f f g g))

  ;;(s-pp-fix '(list a a b b (-- c)))
  ;;(s-pp-fix '(list a a b b (-- c) (-- c)))

  (define s-fix-args ((pp rp-termp))
    :returns (cleaned-pp rp-termp
                         :hyp (rp-termp pp))
    ;; make every pp positive
    ;; remove duplicates.
    (case-match pp
      (('list . pp-lst)
       (b* ((res-lst (s-fix-pp-args-aux pp-lst)))
         (if res-lst
             (pp-cons-with-hint 'list res-lst pp)
           ''nil)))
      (''nil pp)
      (& (progn$ (cw "Unexpected pp form= ~p0 ~%" pp)
                 (hard-error 's-fix-args "" nil)
                 pp)))))

(defmacro cough-duplicates (lst)
  `(c-fix-arg-aux ,lst nil))


(progn

  (define c-fix-arg-aux ((arg-lst rp-term-listp)
                         (neg-flag booleanp))
    :returns (mv (coughed-lst rp-term-listp
                              :hyp (rp-term-listp arg-lst))
                 (cleaned-lst rp-term-listp
                              :hyp (rp-term-listp arg-lst)))
    (cond
     ((atom arg-lst)
      (mv nil nil))
     (t
      (b* ((cur (car arg-lst))
           (cur-orig cur)
           (cur (ex-from-rp$ cur))
           ((mv next next-present)
            (if (atom (cdr arg-lst)) (mv ''0 nil) (mv (cadr arg-lst) t))))
        (cond ((and next-present
                    (rp-equal-cnt cur next 0))
               (b* (((mv rest-coughed rest-pp)
                     (c-fix-arg-aux (cddr arg-lst) neg-flag )))
                 (mv (pp-cons cur-orig rest-coughed)
                     rest-pp)))
              ((and neg-flag
                    (case-match cur (('-- &) t)))
               (b* (((mv rest-coughed rest-pp)
                     (c-fix-arg-aux (cdr arg-lst) neg-flag )))
                 (mv (pp-cons cur-orig rest-coughed)
                     (pp-cons (cadr cur) rest-pp))))
              (t
               (b* (((mv rest-coughed rest-pp)
                     (c-fix-arg-aux (cdr arg-lst) neg-flag )))
                 (mv rest-coughed
                     (pp-cons-with-hint cur-orig rest-pp arg-lst)))))))))


  (define c-fix-arg-aux-with-cond ((arg-lst rp-term-listp)
                                   (neg-flag booleanp)
                                   cond)
    :inline t
    :returns (mv (coughed-lst rp-term-listp
                              :hyp (rp-term-listp arg-lst))
                 (cleaned-lst rp-term-listp
                              :hyp (rp-term-listp arg-lst)))
    (if cond
        (c-fix-arg-aux arg-lst neg-flag)
      (mv nil arg-lst)))
        
        
  
  (defmacro cough-lst (lst)
    `(c-fix-arg-aux ,lst t))

  ;; (c/d-pp-fix-aux '(a a (-- b) c d)) = (mv '(a (-- b)) '(b c d))
  ;; (c/d-pp-fix-aux '(a a (-- b))) = (mv '(a (-- b)) '(b))
  ;; (c/d-pp-fix-aux '(a a b b)) = (mv '(a b) nil)

  ;; (c/d-pp-fix '(list a a (-- b) c d)) = (mv '(list a (-- b)) '(list b c d))
  ;; (c/d-pp-fix '(list a a (-- b))) = (mv '(list a (-- b)) '(list b))
  ;; (c/d-pp-fix '(list a a b b)) = (mv '(list a b) ''nil)

  (define c-fix-pp-args ((pp rp-termp))
    ;; cough out the negatives (leaving positives behind)
    ;; cough out duplicates.
    :returns (mv (coughed-pp rp-termp
                             :hyp (rp-termp pp))
                 (cleaned-pp rp-termp
                             :hyp (rp-termp pp)))
    ;;(mv ''nil pp)
    (case-match pp
      (('list . pp-lst)
       (b* (((mv coughed-lst res-lst) (c-fix-arg-aux pp-lst t)))
         (mv (create-list-instance coughed-lst)
             (if res-lst (cons-with-hint 'list res-lst pp) ''nil))))
      (''nil (mv ''nil ''nil))
      (& (progn$ (cw "Unexpected pp form= ~p0 ~%" pp)
                 (hard-error 'c-fix-pp-args "" nil)
                 (mv ''nil pp)))))

  (encapsulate
    (((c/d-remove-repeated-s) => *))
    (local
     (defun c/d-remove-repeated-s ()
       nil)))

  (define return-t ()
    t)
  (define return-nil ()
    nil)

  (defmacro c/d-remove-repeated-s-enable ()
    `(defattach  c/d-remove-repeated-s return-t))

  (defmacro c/d-remove-repeated-s-disable ()
    `(defattach  c/d-remove-repeated-s return-nil))

  (c/d-remove-repeated-s-disable)

  (define c-fix-s-args ((s rp-termp))
    ;; same as c/d-pp-fix but don't touch the negated terms
    ;; cough out duplicates.
    :returns (mv (coughed-s rp-termp
                            :hyp (rp-termp s))
                 (cleaned-s rp-termp
                            :hyp (rp-termp s)))
    (if t ;(c/d-remove-repeated-s)
        (case-match s
          (('list . s-lst)
           (b* (((mv coughed-lst res-lst) (c-fix-arg-aux s-lst t )))
             (mv (create-list-instance coughed-lst)
                 (if res-lst (cons-with-hint 'list res-lst s) ''nil))))
          (''nil (mv ''nil ''nil))
          (& (progn$ (cw "Unexpected s form= ~p0 ~%" s)
                     (hard-error 'c-fix-s-args "" nil)
                     (mv ''nil s))))
      (if (equal s '(list))
          (mv ''nil ''nil)
        (mv ''nil s)))))

#|(progn

  (define safe-cons-to-coughed-lst (e coughed-lst)
    ;; (b* (((unless e) coughed-lst)
    ;;      ((when (atom coughed-lst)) (list e))
    ;;      (e2 (car coughed-lst))
    (b* ((res
          (pp-sum-merge-aux (list e) coughed-lst)))
      res))


  (defstobj pp-lst-array
    (mem  :type (array t (1)) :resizable t :initially nil))

  (define fill-pp-lst-array ((lst rp-term-listp)
                             pp-lst-array
                             (cnt natp))
    ;; :guard (and (array1p name arr)
    ;;             (equal (len lst) cnt)
    ;;             (<= (len lst) (CAR (DIMENSIONS NAME ARR))))
    :guard (and (= (len lst) cnt)
                (<= (len lst)
                    (mem-length pp-lst-array)))
    (b* ((cnt (mbe :exec cnt
                   :logic (len lst))))
      (cond ((atom lst)
             (mv pp-lst-array cnt))
            #|((<= (mem-length pp-lst-array) cnt)
            (mv pp-lst-array cnt))||#
            (t
             (b* ((cur (car lst))
                  (cur (if (or (equal cur (list ''0))
                               (equal cur ''nil))
                           nil
                         cur))
                  #|((unless cur)
                  (fill-pp-lst-array (cdr lst) pp-lst-array cnt))||#
                  (pp-lst-array (update-memi (1- cnt) cur pp-lst-array))
                  ;;(aset1 'pp-lst-array pp-lst-array cnt (car lst))
                  )
               (fill-pp-lst-array (cdr lst) pp-lst-array (1- cnt))))))
    ///
    #|(defthm fill-array-returns-array1p
    (implies (array1p name arr) ; ;
    (array1p name (fill-array lst arr name cnt))))||#)

  (define pp-lst-array-find-min (pp-lst-array (cnt natp))
    :guard (<= cnt (mem-length pp-lst-array))
    :verify-guards nil
    :returns (mv (min)
                 (min-i natp)
                 (valid-min booleanp)
                 (full-lst-cnt natp))
    (if (zp cnt)
        (mv nil 0 nil 0)
      (b* ((cnt (1- cnt))
           ((mv min min-i valid-min full-lst-cnt)
            (pp-lst-array-find-min pp-lst-array cnt))
           (cur-i cnt)
           (cur (memi cnt pp-lst-array))
           ((when (atom cur))
            (mv min min-i valid-min full-lst-cnt))
           (cur (car cur))
           ((unless valid-min)
            (mv cur cur-i t (1+ full-lst-cnt)))
           ((mv order & &)
            (pp-order-and-negated-termsp cur min)))
        (if order
            (mv cur cur-i t (1+ full-lst-cnt))
          (mv min min-i valid-min (1+ full-lst-cnt)))))
    ///
    (defthm valid-min-i-pp-lst-array-find-min
      (implies (and (<= cnt (mem-length pp-lst-array))
                    (PP-LST-ARRAYP PP-LST-ARRAY)
                    (natp cnt))
               (b* (((mv & min-i valid-min &)
                     (pp-lst-array-find-min pp-lst-array cnt)))
                 (implies valid-min
                          (< min-i (mem-length pp-lst-array)))))
      )

    (verify-guards pp-lst-array-find-min)
    )

  (skip-proofs
   (define pp-lst-sum-merge-per-pp (pp-lst-array size for-s for-c)

     (b* (((mv min min-i valid-min full-lst-cnt)
           (pp-lst-array-find-min pp-lst-array size))
          ((unless valid-min)
           (mv nil nil nil pp-lst-array))
          ((when (and  (equal full-lst-cnt 1)))
           (b* ((pp-lst (memi min-i pp-lst-array))
                ((mv coughed-pp-lst pp-lst)
                 (if for-c
                     (c-fix-arg-aux pp-lst t (expt 2 30))
                   (if for-s
                       (mv nil (s-fix-pp-args-aux pp-lst))
                     (mv nil pp-lst)))))
             (if (consp pp-lst)
                 (mv (car pp-lst) (cdr pp-lst) coughed-pp-lst pp-lst-array)
               (mv nil pp-lst coughed-pp-lst pp-lst-array))))

          (pp-lst-array (update-memi min-i
                                     (cdr (memi min-i pp-lst-array))
                                     pp-lst-array))
          ((mv first rest coughed-lst pp-lst-array)
           (pp-lst-sum-merge-per-pp pp-lst-array size for-s for-c))
          ((mv & negated-termsp equals)
           (pp-order-and-negated-termsp first min)))
       (cond (negated-termsp
              (mv nil rest coughed-lst pp-lst-array))
             ((and (or for-s for-c) equals)
              (if for-c
                  (mv nil rest (safe-cons-to-coughed-lst first coughed-lst) pp-lst-array)
                (mv nil rest coughed-lst pp-lst-array)))
             ((and (or for-s for-c)
                   (case-match min (('-- &) t)))
              (mv (cadr min)
                  (if first (pp-cons first rest) rest)
                  (if for-c (safe-cons-to-coughed-lst min coughed-lst) nil)
                  pp-lst-array))
             (t
              (mv min
                  (if first (pp-cons first rest) rest)
                  coughed-lst
                  pp-lst-array))))))

  (define pp-lst-sum-merge-aux (pp-lst-lst
                                pp-lst-array
                                (array-length natp)
                                for-c
                                for-s)
    :guard (and (= array-length (len pp-lst-lst)))

    (b* (((mv pp-lst-array &) (fill-pp-lst-array pp-lst-lst pp-lst-array array-length))
         ((mv first rest coughed-lst pp-lst-array)
          (pp-lst-sum-merge-per-pp pp-lst-array array-length for-s for-c))
         (pp-lst (if first (pp-cons first rest) rest)))
      (mv pp-lst coughed-lst pp-lst-array)))

  (skip-proofs
   (define pp-lst-sum-merge-old (pp-lst-lst &key (for-c 'nil) (for-s 'nil))
     (declare (ignorable pp-lst-lst for-c))

     (with-local-stobj
       pp-lst-array
       (mv-let (pp-lst coughed-pp-lst pp-lst-array)
         (b* ((array-length (len pp-lst-lst))
              (pp-lst-array (resize-mem array-length pp-lst-array))
              ((mv pp-lst coughed-pp-lst pp-lst-array)
               (pp-lst-sum-merge-aux pp-lst-lst pp-lst-array array-length
                                     for-c for-s)))
           (mv pp-lst coughed-pp-lst pp-lst-array))
         (mv pp-lst
             ;;(hons-copy pp-lst)
             coughed-pp-lst
             ;;(hons-copy coughed-lst)
             )))))

  ;;(memoize 'pp-lst-sum-merge :memo-table-init-size 100000)

  ;; (define pp-lst-sum-merge (pp-lst-lst &key (for-c 'nil) (for-s 'nil))
  ;;   (pp-lst-sum-merge- (hons-copy pp-lst-lst) :for-c for-c :for-s for-s))
  )||#

#|(define pp-lst-sum-merge (pp-lst-lst &key (for-c 'nil) (for-s 'nil))
  (b* (((mv pp-lst coughed-pp-lst)
        (pp-lst-sum-merge- pp-lst-lst :for-c for-c :for-s for-s))
       ((mv pp-lst2 coughed-pp-lst2)
        (pp-lst-sum-merge- (rev pp-lst-lst) :for-c for-c :for-s for-s))
       (- (and (or (not (equal pp-lst pp-lst2)))
               (hard-error 'pp-lst-sum-merge
                           "pp-lst-lst: ~p0 ~% pp-lst:~p1 ~% pp-lst2: ~p2 ~%"
                           (list (cons #\0 pp-lst-lst)
                                 (cons #\1 pp-lst)
                                 (cons #\2 pp-lst2)))))
       (- (and (or (not (equal coughed-pp-lst coughed-pp-lst2)))
               (hard-error 'pp-lst-sum-merge
                           "pp-lst-lst: ~p0 ~% coughed-pp-lst:~p1 ~% coughed-pp-lst2: ~p2 ~%"
                           (list (cons #\0 pp-lst-lst)
                                 (cons #\1 coughed-pp-lst)
                                 (cons #\2 coughed-pp-lst2))))))
    (mv pp-lst coughed-pp-lst)))||#

;; (define pp-sum-merge-aux-wrap1 (lst1 lst2)
;;   (pp-sum-merge-aux lst1 lst2 0))

;; #|(memoize 'pp-sum-merge-aux-wrap1
;;          :condition '(and (not (equal lst1 nil)) (not (equal lst2 nil))))||#

;; (define pp-sum-merge-aux-wrap2 (lst1 lst2)
;;   (pp-sum-merge-aux lst1 lst2 0))

;; #|(memoize 'pp-sum-merge-aux-wrap2
;;          :condition '(and (not (equal lst1 nil)) (not (equal lst2 nil))))||#

;; (define pp-sum-merge-aux-wrap3 (lst1 lst2)
;;   (pp-sum-merge-aux lst1 lst2 0))

;; #|(memoize 'pp-sum-merge-aux-wrap3
;;          :condition '(and (not (equal lst1 nil)) (not (equal lst2 nil))))||#

;; (define pp-sum-merge-aux-wrap4 (lst1 lst2)
;;   (pp-sum-merge-aux lst1 lst2 0))

;; #|(memoize 'pp-sum-merge-aux-wrap4
;;          :condition '(and (not (equal lst1 nil)) (not (equal lst2 nil))))||#

#|(progn
  (define pp-lst-sum-merge-aux2 (pp-lst-lst)
    (b* (((when (atom pp-lst-lst))
          nil)
         (pp-lst
          (pp-lst-sum-merge-aux2 (cdr pp-lst-lst)))
         (cur (car pp-lst-lst))
         (pp-lst (pp-sum-merge-aux cur pp-lst)))
      pp-lst))

  (define pp-lst-sum-merge (pp-lst-lst &key (for-c 'nil) (for-s 'nil))
    (b* ((pp-lst
          (pp-lst-sum-merge-aux2 pp-lst-lst))
         ((mv coughed-pp-lst pp-lst)
          (cond (for-c (c-fix-arg-aux pp-lst t))
                (for-s (mv nil (s-fix-pp-args-aux pp-lst)))
                (t (mv nil pp-lst)))))
      (mv pp-lst
          ;;(hons-copy pp-lst)
          coughed-pp-lst
          ;;(hons-copy coughed-lst)
          ))))||#
