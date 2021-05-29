; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
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

(local
 (in-theory (disable +-IS-SUM)))

(acl2::defines
 rp-order
 :flag-local nil
 :prepwork
 ((local
   (in-theory (e/d (rp::measure-lemmas)
                   (+-IS-SUM)))))
 (define rp-order (x y)
   :measure (+ (cons-count x)
               (cons-count y))
   (b* ((x (ex-from-rp-loose x))
        (y (ex-from-rp-loose y)))
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
                  (rp-order-lst (cdr x) (cdr y))
                (mv (small-alphorder (car x) (car y)) nil))))))
 (define rp-order-lst (lst1 lst2)
   :measure (+ (cons-count lst1)
               (cons-count lst2))
   (cond ((or (atom lst1)
              (atom lst2))
          (if (equal lst1 lst2)
              (mv nil t)
            (mv (lexorder lst1 lst2) nil)))
         (t (b* (((mv car-order car-equal)
                  (rp-order (car lst1) (car lst2)))
                 ((unless car-equal)
                  (mv car-order nil))
                 ((mv cdr-order cdr-equal)
                  (rp-order-lst (cdr lst1) (cdr lst2))))
              (mv cdr-order cdr-equal))))))

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
    (cond ((and (consp x)
                (consp (cdr x)))
           (if (and (equal (car x) '--)
                    (not (cddr x)))
               (ex-from-rp/-- (cadr x))
             (if (and (equal (car x) 'rp)
                      (consp (cddr x))
                      (not (cdddr x)))
                 (ex-from-rp/-- (caddr x))
               x)))
          (t x)))

  (define ex-from--- (x)
    :inline t
    (case-match x (('-- a) a) (& x)))

  (define pp-order (x y)
    :inline t
    :returns (mv (order)
                 (equals booleanp))
    (b* (;;(x (ex-from--- x))
         ;;(y (ex-from--- y))
         (x-orig x)
         (y-orig y))
      (b* (((mv x atom-x len-x)
            (case-match x
              (('and-list ('list . lst))
               (mv lst nil (len lst)))
              (('binary-and & &)
               (mv (cdr x) nil 2))
              (''1
               (mv x t 1))
              (('bit-of & &)
               (mv x t 1))
              (('rp ''bitp &)
               (mv x t 1))
              (& (mv x nil -1))))
           ((mv y atom-y len-y)
            (case-match y
              (('and-list ('list . lst))
               (mv lst nil (len lst)))
              (('binary-and & &)
               (mv (cdr y) nil 2))
              (''1
               (mv y t 1))
              (('rp ''bitp &)
               (mv y t 1))
              (('bit-of & &)
               (mv y t 1))
              (& (mv y nil -1))))

           #|((mv x y atom-x atom-y len-x len-y)
           (if (and (equal len-x 2)
           (equal len-y 2))
           (mv x y atom-x atom-y len-x len-y)
           (mv y x atom-x atom-y len-x len-y)))||#


           )
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
;(atom (cdr x))
                             )
                       (mv (not (lexorder y (car x))) nil))
                   (mv t nil)))
                ((not atom-y)
                 (if (consp y)
                     (if (equal (car y) x)
                         (mv (not (atom y))
                             (equal x-orig y-orig)
;(atom y)
                             )
                       (mv (not (lexorder (car y) x)) nil))
                   (mv nil nil)))
                (t (if (equal x y)
                       (mv nil t)
                     (mv (not (lexorder y x)) nil)))))
         (t (pp-list-order x y))))))

  (define pp-lst-orderedp (lst)
    (if (atom lst)
        t
      (if (atom (cdr lst))
          t
        (and (not (b* (((mv order &) (pp-order (cadr lst) (car lst)))) order) )
             (pp-lst-orderedp (cdr lst))))))

  (define pp-orderedp (pp)
    (case-match pp
      (('list . lst)
       (pp-lst-orderedp lst))
      (''nil
       t)
      (& nil)))

  (define s-order (x y)
    (b* ((x (ex-from-rp/--loose x))
         (y (ex-from-rp/--loose y)))
      (b* (((mv res &) (lexorder2 y x))) res)))

  (local
   (defthm s-order-sanity
     (implies (s-order x y)
              (not (s-order y x)))
     :hints (("Goal"
              :in-theory (e/d (s-order
                               lexorder2-sanity)
                              (lexorder2)))))))

(define pp-order-and-negated-termsp ((term1)
                                     (term2))
  :returns (mv
            (order)
            (negated-terms booleanp))
  (b* (((mv neg1 term1)
        (case-match term1 (('-- a) (mv t a)) (& (mv nil term1))))
       ((mv neg2 term2)
        (case-match term2 (('-- a) (mv t a)) (& (mv nil term2))))
       ((mv order equals)
        (pp-order term1 term2)))
    (mv  order
         (and (not (equal neg1 neg2))
              equals))))

(progn
  (define pp-sum-merge-aux ((pp1-lst)
                            (pp2-lst)
                            (cnt natp))
    :measure (+ (cons-count pp1-lst)
                (cons-count pp2-lst))
    :hints (("Goal"
             :in-theory (e/d (measure-lemmas) ())))
    :returns (mv (merged-pp-lst rp-term-listp
                                :hyp (and (rp-term-listp pp1-lst)
                                          (rp-term-listp pp2-lst)))
                 (res-cnt natp
                          "A hint for other functions to know how many elements have changed."
                          :hyp (natp cnt)))

    (cond ((atom pp1-lst)
           (mv pp2-lst cnt))
          ((atom pp2-lst)
           (mv pp1-lst cnt))
          (t (b* ((cur1 (car pp1-lst))
                  (cur2 (car pp2-lst))
                  ((when (equal cur1 ''0))
                   (pp-sum-merge-aux (cdr pp1-lst) pp2-lst cnt))
                  ((when (equal cur2 ''0))
                   (pp-sum-merge-aux pp1-lst (cdr pp2-lst) cnt))
                  ((mv order negated-termsp)
                   (pp-order-and-negated-termsp cur1 cur2)))
               (cond (negated-termsp
                      (pp-sum-merge-aux (cdr pp1-lst) (cdr pp2-lst) cnt))
                     (order
                      (b* (((mv rest cnt) (pp-sum-merge-aux (cdr pp1-lst) pp2-lst (1+ cnt))))
                        (mv (cons cur1 rest) cnt)))
                     (t
                      (b* (((mv rest cnt) (pp-sum-merge-aux pp1-lst (cdr pp2-lst) (1+ cnt))))
                        (mv (cons cur2 rest) cnt))))))))

  (define pp-sum-merge ((pp1)
                        (pp2))
    :returns (mv (merged-pp rp-termp
                            :hyp (and (rp-termp pp1)
                                      (rp-termp pp2)))
                 (res-cnt natp
                          "A hint for other functions to know how many elements
                        have changed."
                          :rule-classes :type-prescription))
    (b* (((when (equal pp1 ''nil))
          (mv pp2 0))
         ((when (equal pp2 ''nil))
          (mv pp1 0))
         ((when (or (not (case-match pp1 (('list . &) t)))
                    (not (case-match pp2 (('list . &) t)))))
          (progn$ (cw "pp-sum-merge-fail pp1=~p0~%pp2=~p1 ~%" pp1 pp2)
                  (hard-error 'pp-sum-merge "" nil)
                  (mv `(binary-append ,pp1 ,pp2) 0))))
      (b* (((mv res cnt) (pp-sum-merge-aux (cdr pp1) (cdr pp2) 0)))
        (if (and res
                 (not (equal res (list ''0))))
            (mv `(list . ,res) cnt)
          (mv ''nil 0)))))

  (memoize 'pp-sum-merge :condition '(and (not (equal pp1 'nil)) (not (equal pp2 'nil)))))

(progn

  (define s-order-and-negated-termsp ((term1)
                                      (term2))
    (b* (;;(term1 (ex-from-rp-loose term1))
         ;;(term2 (ex-from-rp-loose term2))
         ((mv neg1 term1)
          (case-match term1 (('-- a) (mv t a)) (& (mv nil term1))))
         ((mv neg2 term2)
          (case-match term2 (('-- a) (mv t a)) (& (mv nil term2))))
         ((mv order terms-are-equal)
          (rp-order term1 term2)))
      (mv order
          (and (not (equal neg1 neg2))
               terms-are-equal))))

  (define s-sum-merge-aux ((s1-lst)
                           (s2-lst))
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

  (define s-sum-merge ((s1)
                       (s2))
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
        (if (and res
                 (not (equal res (list ''0))))
            `(list . ,res)
          ''nil)))))

(progn
  (define s-fix-pp-args-aux ((pp-lst))
    :returns (cleaned-pp-lst rp-term-listp
                             :hyp (rp-term-listp pp-lst))
    (if (atom pp-lst)
        nil
      (b* ((cur (car pp-lst))
           (cur-orig cur)
           (cur (ex-from-rp-loose cur))
           ((mv next next-present)
            (if (atom (cdr pp-lst)) (mv ''0 nil) (mv (cadr pp-lst) t))))
        (cond ((and next-present
                    (rp-equal-cnt cur next 0))
               (s-fix-pp-args-aux (cddr pp-lst)))
              ((case-match cur (('-- &) t))
               (cons (cadr cur)
                     (s-fix-pp-args-aux (cdr pp-lst))))
              (t
               (cons-with-hint cur-orig
                               (s-fix-pp-args-aux (cdr pp-lst))
                               pp-lst))))))

  ;; (s-pp-fix-aux '(a a b b f f g g))
  ;; (s-pp-fix-aux '(a b c d (-- e) f f g g))

  ;;(s-pp-fix '(list a a b b (-- c)))
  ;;(s-pp-fix '(list a a b b (-- c) (-- c)))

  (define s-fix-args ((pp))
    :returns (cleaned-pp rp-termp
                         :hyp (rp-termp pp))
    ;; make every pp positive
    ;; remove duplicates.
    (case-match pp
      (('list . pp-lst)
       (b* ((res-lst (s-fix-pp-args-aux pp-lst)))
         (if res-lst
             (cons-with-hint 'list res-lst pp)
           ''nil)))
      (''nil pp)
      (& (progn$ (cw "Unexpected pp form= ~p0 ~%" pp)
                 (hard-error 's-fix-args "" nil)
                 pp)))))

(progn
  (define c/d-fix-arg-aux ((arg-lst)
                           (neg-flag booleanp)
                           (limit natp))
    :returns (mv (coughed-lst rp-term-listp
                              :hyp (rp-term-listp arg-lst))
                 (cleaned-lst rp-term-listp
                              :hyp (rp-term-listp arg-lst)))
    (cond
     ((zp limit)
      (mv nil arg-lst))
     ((atom arg-lst)
      (mv nil nil))
     (t
      (b* ((cur (car arg-lst))
           (cur-orig cur)
           (cur (ex-from-rp-loose cur))
           ((mv next next-present)
            (if (atom (cdr arg-lst)) (mv ''0 nil) (mv (cadr arg-lst) t))))
        (cond ((and next-present
                    (rp-equal-cnt cur next 0))
               (b* (((mv rest-coughed rest-pp)
                     (c/d-fix-arg-aux (cddr arg-lst) neg-flag (nfix (- limit 2)))))
                 (mv (cons cur-orig rest-coughed)
                     rest-pp)))
              ((and neg-flag
                    (case-match cur (('-- &) t)))
               (b* (((mv rest-coughed rest-pp)
                     (c/d-fix-arg-aux (cdr arg-lst) neg-flag (1- limit))))
                 (mv (cons cur-orig rest-coughed)
                     (cons (cadr cur) rest-pp))))
              (t
               (b* (((mv rest-coughed rest-pp)
                     (c/d-fix-arg-aux (cdr arg-lst) neg-flag (1- limit))))
                 (mv rest-coughed
                     (cons-with-hint cur-orig rest-pp arg-lst)))))))))

  ;; (c/d-pp-fix-aux '(a a (-- b) c d)) = (mv '(a (-- b)) '(b c d))
  ;; (c/d-pp-fix-aux '(a a (-- b))) = (mv '(a (-- b)) '(b))
  ;; (c/d-pp-fix-aux '(a a b b)) = (mv '(a b) nil)

  ;; (c/d-pp-fix '(list a a (-- b) c d)) = (mv '(list a (-- b)) '(list b c d))
  ;; (c/d-pp-fix '(list a a (-- b))) = (mv '(list a (-- b)) '(list b))
  ;; (c/d-pp-fix '(list a a b b)) = (mv '(list a b) ''nil)

  (define c/d-fix-pp-args ((pp) (limit natp))
    ;; cough out the negatives (leaving positives behind)
    ;; cough out duplicates.
    :returns (mv (coughed-pp rp-termp
                             :hyp (rp-termp pp))
                 (cleaned-pp rp-termp
                             :hyp (rp-termp pp)))
    ;;(mv ''nil pp)
    (case-match pp
      (('list . pp-lst)
       (b* (((mv coughed-lst res-lst) (c/d-fix-arg-aux pp-lst t limit)))
         (mv (if coughed-lst `(list . ,coughed-lst) ''nil)
             (if res-lst (cons-with-hint 'list res-lst pp) ''nil))))
      (''nil (mv ''nil ''nil))
      (& (progn$ (cw "Unexpected pp form= ~p0 ~%" pp)
                 (hard-error 'c/d-fix-pp-args "" nil)
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

  (define c/d-fix-s-args ((s))
    ;; same as c/d-pp-fix but don't touch the negated terms
    ;; cough out duplicates.
    :returns (mv (coughed-s rp-termp
                            :hyp (rp-termp s))
                 (cleaned-s rp-termp
                            :hyp (rp-termp s)))
    (if (c/d-remove-repeated-s)
        (case-match s
          (('list . s-lst)
           (b* (((mv coughed-lst res-lst) (c/d-fix-arg-aux s-lst nil (expt 2 30))))
             (mv (if coughed-lst `(list . ,coughed-lst) ''nil)
                 (if res-lst (cons-with-hint 'list res-lst s) ''nil))))
          (''nil (mv ''nil ''nil))
          (& (progn$ (cw "Unexpected s form= ~p0 ~%" s)
                     (hard-error 'c/d-fix-s-args "" nil)
                     (mv ''nil s))))
      (if (equal s '(list))
          (mv ''nil ''nil)
        (mv ''nil s)))))

(define get-c/d-args ((c/d))
  :inline t
  :returns (mv (s-args rp-termp
                       :hyp (rp-termp c/d))
               (pp-args rp-termp
                        :hyp (rp-termp c/d))
               (c/d-args rp-termp
                         :hyp (rp-termp c/d))
               (valid symbolp))
  (case-match c/d
    (('d ('rp ''evenpi ('d-sum s pp c/d)))
     (mv s pp c/d 'd))
    (('c s pp c/d)
     (mv s pp c/d 'c))
    (& (mv ''nil ''nil ''0 nil))))

(define create-c-instance (s pp c/d)
  :inline t
  :returns (c/d-res rp-termp :hyp (and (rp-termp pp)
                                       (rp-termp s)
                                       (rp-termp c/d)))
  (cond ((and (equal c/d ''0)
              (equal s ''nil)
              (case-match pp (('list ('binary-and & &)) t)))
         ''0)
        ((and (quotep pp)
              (consp (cdr pp))
              (quotep s)
              (consp (cdr s))
              (quotep c/d)
              (consp (cdr c/d)))
         `',(c (unquote s) (unquote pp) (unquote c/d)))
        (t
         `(c ,s ,pp ,c/d))))

(define d-to-c ((c/d))
  :returns (c/d-res rp-termp :hyp (rp-termp c/d))
  :inline t
  ;; try converting d to c.
  (case-match c/d
    (('d ('rp ''evenpi ('d-sum s pp1 c/d1)))
     (cond ((and (quotep s) (consp (cdr s))
                 (quotep pp1) (consp (cdr pp1))
                 (quotep c/d1) (consp (cdr c/d1)))
            `',(d (d-sum (unquote s)
                         (unquote pp1)
                         (unquote c/d1))))
           (t
            (case-match s
              (('list ('-- ('s pp2 c/d2)))
               (if (and (rp-equal-cnt pp1 pp2 1)
                        (rp-equal-cnt c/d1 c/d2 0))
                   (create-c-instance ''nil pp1 c/d1)
                 c/d))
              (& c/d)))))
    (('c arg1 arg2 arg3)
     (if (and (quotep arg1)
              (consp (cdr arg1))
              (quotep arg2)
              (consp (cdr arg2))
              (quotep arg3)
              (consp (cdr arg3)))
         `',(c (unquote arg1)
               (unquote arg2)
               (unquote arg3))
       c/d))
    (& c/d)))

(define c/d-cough ((c/d))
;:inline t
  :returns (mv (s-coughed rp-termp :hyp (rp-termp c/d))
               (pp-coughed rp-termp :hyp (rp-termp c/d))
               (c/d-cleaned rp-termp :hyp (rp-termp c/d)))
  :prepwork ((local
              (in-theory (e/d (is-rp) ()))))
  (b* (((mv s-arg pp-arg c/d-arg type)
        (get-c/d-args c/d)))
    (cond ((equal c/d ''0)
           (mv ''nil ''nil c/d))
          (type
           (b* (((mv s-coughed s)
                 (c/d-fix-s-args s-arg))
                ((mv pp-coughed pp)
                 (c/d-fix-pp-args pp-arg (expt 2 30)))
                (c/d-cleaned
                 (if (eq type 'c)
                     (create-c-instance s pp c/d-arg)
                   `(d (rp 'evenpi (d-sum ,s ,pp ,c/d-arg)))))
                (c/d-cleaned (d-to-c c/d-cleaned)))
             (mv s-coughed pp-coughed c/d-cleaned)))
          (t
           (progn$ (cw "c/d-cough is given a bad term ~p0 ~%" c/d)
                   (mv ''nil ''nil c/d))))))

;; (c/d-cough '(c (list (s 'nil (list (c 'nil (list a b) 'nil)))
;;                      (s 'nil (list (c 'nil (list a b) 'nil))))
;;                (list a a (-- b) (-- c))
;;                'nil))

(define can-c-merge-fast-aux (s-lst pp c/d)
  ;;:inline t
  (if (atom s-lst)
      nil
    (or (b* ((cur-s (ex-from-rp-loose (car s-lst))))
          (case-match cur-s
            (('s pp-arg c/d-arg)
             (progn$
              (and
               (equal pp-arg pp) (equal c/d-arg c/d)
               ;;(rp-equal-cnt c/d-arg c/d 10) (rp-equal-cnt pp-arg pp 10)
               )))))
        ;;(can-c-merge-fast-aux (cdr s-lst) pp c/d)
        )))

(define can-c-merge-fast (c/d1 c/d2)
  ;; returns nil, 0 or 1. 0 and 1 mean terms can merge fast, and 1 means flip c/d1
  ;; and c/d2
  (b* (((mv s-arg1 pp-arg1 c/d-arg1 type1) (get-c/d-args c/d1))
       ((mv s-arg2 pp-arg2 c/d-arg2 type2) (get-c/d-args c/d2))
       ((when (or (not (equal type1 'c))
                  (not (equal type2 'c))))
        nil)
       (match1 ;; possible match to (sum (f2 x) (f2 (sum (m2 x) y)))
        ;; c/d1 = (c 'nil arg-pp1 arg-c/d1)
        ;; c/d2 = (c (list (s arg-pp1 arg-c/d1) other-s) arg-pp2 arg-c/d2)
        (and (equal s-arg1 ''nil)
             (case-match s-arg2 (('list . &) t))))

       (match2 ;; possible match to (sum (f2 x) (f2 (sum (m2 x) y)))
        ;; c/d1 = (c (list (s arg-pp1 arg-c/d1) other-s) arg-pp2 arg-c/d2)
        ;; c/d2 = (c 'nil arg-pp1 arg-c/d1)
        (and (case-match s-arg1 (('list . &) t))
             (equal s-arg2 ''nil))))
    (cond (match1
           (if (can-c-merge-fast-aux (cdr s-arg2) pp-arg1 c/d-arg1)
               0
             nil))
          (match2
           (if (can-c-merge-fast-aux (cdr s-arg1) pp-arg2 c/d-arg2)
               1
             nil))
          (t
           nil))))

(define fast-merge-profile ()
  t)

(define swap-c/ds (c/d1 c/d2 swap)
  :inline t
  :returns (mv (res1 rp-termp
                     :hyp (and (rp-termp c/d1)
                               (rp-termp c/d2)))
               (res2 rp-termp
                     :hyp (and (rp-termp c/d1)
                               (rp-termp c/d2))))
  (if swap
      (mv c/d2 c/d1)
    (mv c/d1 c/d2)))

(define clean-c/d-args (s-arg pp-arg (pp-arg-cnt natp) clean-flg)
  :returns (mv (s-coughed rp-termp
                          :hyp (rp-termp s-arg))
               (s-arg-res rp-termp
                          :hyp (rp-termp s-arg))
               (pp-coughed rp-termp
                           :hyp (rp-termp pp-arg))
               (pp-arg-res rp-termp
                           :hyp (rp-termp pp-arg)))
  (b* (((mv s-coughed s-arg)
        (if clean-flg (c/d-fix-s-args s-arg) (mv ''nil s-arg)))
       ((mv pp-coughed pp-arg)
        (if clean-flg (c/d-fix-pp-args pp-arg pp-arg-cnt)
          (mv ''nil pp-arg))))
    (mv s-coughed s-arg pp-coughed pp-arg)))

(define remove-s-from-for-fast-merge (s-arg2 pp-arg1 c/d-arg1)
  (declare (ignorable pp-arg1 c/d-arg1 pp-arg1))
  :guard (and (consp s-arg2)
              (consp (cdr s-arg2)))
  :inline t
  (b* ((s-arg `(list . ,(cddr s-arg2)))
       ;;(s-arg (s-sum-merge s-arg2 `(list (-- (s ,pp-arg1 ,c/d-arg1)))))
       )
    s-arg))

(define extra-s-can-be-pp (pp c/d)
  :inline t
  (and (equal c/d ''0)
       (case-match pp (('list ('binary-and & &)) t)))
  ///
  (defthm extra-s-can-be-pp-implies
    (implies (extra-s-can-be-pp pp c/d)
             (and (equal c/d ''0)
                  (case-match pp (('list ('binary-and & &)) t))))
    :rule-classes :forward-chaining))

;; (mutual-recursion
;;  (defun search-pattern (term)
;;    (declare (xargs :guard t))
;;    (cond ((extra-s-can-be-pp term)
;;           (list term))
;;          ((or (atom term)
;;               (quotep term))
;;           nil)
;;          (t
;;           (search-pattern-lst (cdr term)))))
;;  (defun search-pattern-lst (lst)
;;    (if (atom lst)
;;        nil
;;      (append (search-pattern (car lst))
;;              (search-pattern-lst (cdr lst))))))

;; (make-flag search-pattern :defthm-macro-name defthm-search-pattern)

;; (memoize 'search-pattern)

(local
 (defthm is-rp-of-evenpi
   (IS-RP `(RP 'EVENPI ,x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(local
 (defthm is-rp-of-bitp
   (IS-RP `(RP 'bitp ,x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))


(local
 (defthm rp-termp-of-d
   (iff (rp-termp `(d ,x))
        (rp-termp x))))

(local
 (defthm rp-termp-of---
   (iff (rp-termp `(-- ,x))
        (rp-termp x))))

(local
 (defthm rp-termp-of-list
   (iff (rp-termp `(list . ,x))
        (rp-term-listp x))))


(local
 (defthm rp-termp-of-d-sum
   (iff (rp-termp `(d-sum ,x ,y ,z))
        (and (rp-termp x)
             (rp-termp y)
             (rp-termp z)))))

(local
 (defthm rp-termp-of-of-rp-evenpi
   (iff (rp-termp `(rp 'evenpi ,x))
        (rp-termp x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(define is-a-negated-minterm (term)
  :inline t
  (case-match term
    (('list ('-- ('binary-and & &))) t)))

(define c/d-merge-slow-aux (pp-arg1 pp-arg2 pp-coughed-from-arg
                                    s-arg1 s-arg2 s-coughed-from-arg
                                    extra-s-arg1
                                    extra-s-arg2
                                    c/d-arg
                                    clean-flg
                                    c/d1-is-c
                                    c/d2-is-c)
  :inline t
  :prepwork ((local
              (in-theory (disable falist-consistent
                                  (:TYPE-PRESCRIPTION RP-TERMP)
                                  (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                                  (:TYPE-PRESCRIPTION IS-RP$INLINE)
                                  (:TYPE-PRESCRIPTION FALIST-CONSISTENT)
                                  (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                                  (:FORWARD-CHAINING RP-TERMP-IMPLIES)
                                  (:FORWARD-CHAINING
                                   EXTRACT-FROM-SYNP-PSEUDO-TERM-LISTP)
                                  (:REWRITE DEFAULT-CDR)
                                  (:TYPE-PRESCRIPTION O<)
                                  (:REWRITE ACL2::O-P-O-INFP-CAR)
                                  (:REWRITE DEFAULT-CAR)
                                  (:REWRITE ACL2::O-P-DEF-O-FINP-1)
                                  (:TYPE-PRESCRIPTION O-P)
                                  rp-termp
                                  (:REWRITE ACL2::MV-NTH-OF-CONS)))))
  :returns (mv (s-coughed rp-termp
                          :hyp (and (rp-termp pp-arg1)
                                    (rp-termp pp-arg2)
                                    (rp-termp pp-coughed-from-arg)
                                    (rp-termp s-arg1)
                                    (rp-termp s-arg2)
                                    (rp-termp s-coughed-from-arg)
                                    (if c/d1-is-c (rp-termp extra-s-arg1) t)
                                    (if c/d2-is-c (rp-termp extra-s-arg2) t)
                                    (rp-termp c/d-arg)))
               (pp-coughed rp-termp
                           :hyp (and (rp-termp pp-arg1)
                                     (rp-termp pp-arg2)
                                     (rp-termp pp-coughed-from-arg)
                                     (rp-termp s-arg1)
                                     (rp-termp s-arg2)
                                     (rp-termp s-coughed-from-arg)
                                     (if c/d1-is-c (rp-termp extra-s-arg1) t)
                                     (if c/d2-is-c (rp-termp extra-s-arg2) t)
                                     (rp-termp c/d-arg)))
               (c/d-merged rp-termp
                           :hyp (and (rp-termp pp-arg1)
                                     (rp-termp pp-arg2)
                                     (rp-termp pp-coughed-from-arg)
                                     (rp-termp s-arg1)
                                     (rp-termp s-arg2)
                                     (rp-termp s-coughed-from-arg)
                                     (if c/d1-is-c (rp-termp extra-s-arg1) t)
                                     (if c/d2-is-c (rp-termp extra-s-arg2) t)
                                     (rp-termp c/d-arg))))
  (b* (((mv pp-arg pp-arg-cnt1) (pp-sum-merge pp-arg1 pp-arg2))
       ((mv pp-arg pp-arg-cnt2) (pp-sum-merge pp-coughed-from-arg pp-arg))

       (s-arg (s-sum-merge s-arg2 s-coughed-from-arg))
       (s-arg (s-sum-merge s-arg1 s-arg))
       ((mv s-arg pp-arg pp-arg-cnt3)
        (cond (c/d1-is-c
               (if (is-a-negated-minterm extra-s-arg1)
                   (b* (((mv pp-arg pp-arg-cnt3)
                         (pp-sum-merge pp-arg extra-s-arg1)))
                     (mv s-arg pp-arg pp-arg-cnt3))
                 (mv (s-sum-merge extra-s-arg1 s-arg)
                     pp-arg
                     0)))
              (t (mv s-arg pp-arg 0))))
       ((mv s-arg pp-arg pp-arg-cnt4)
        (cond (c/d2-is-c
               (if (is-a-negated-minterm extra-s-arg2)
                   (b* (((mv pp-arg pp-arg-cnt4)
                         (pp-sum-merge pp-arg extra-s-arg2)))
                     (mv s-arg pp-arg pp-arg-cnt4))
                 (mv (s-sum-merge extra-s-arg2 s-arg)
                     pp-arg
                     0)))
              (t (mv s-arg pp-arg 0))))
       (pp-arg-cnt (+ ;;(expt 2 20) ;;test and remove later when sure...
                    pp-arg-cnt1 pp-arg-cnt2 pp-arg-cnt3 pp-arg-cnt4))
       #|(s-arg (cond ((and c/d1-is-c c/d2-is-c)
       (s-sum-merge s-arg (s-sum-merge extra-s-arg1 extra-s-arg2)))
       (c/d1-is-c (s-sum-merge s-arg extra-s-arg1))
       (c/d2-is-c (s-sum-merge s-arg extra-s-arg2))
       (t s-arg)))||#
       ((mv s-coughed s-arg pp-coughed pp-arg)
        (clean-c/d-args s-arg pp-arg pp-arg-cnt clean-flg))
       (d-res `(d (rp 'evenpi (d-sum ,s-arg ,pp-arg ,c/d-arg))))
       (c/d-merged (if clean-flg (d-to-c d-res) d-res)))

    (mv s-coughed pp-coughed c/d-merged)))

(define c/d-merge-fast-aux (pp-arg1 pp-arg2 pp-coughed-from-arg
                                    s-arg2 s-coughed-from-arg
                                    c/d-arg
                                    clean-flg)
  :inline t
  :guard (and (consp s-arg2)
              (consp (cdr s-arg2)))
  (b* (((mv pp-arg pp-arg-cnt1) (pp-sum-merge pp-arg1 pp-arg2))
       ((mv pp-arg pp-arg-cnt2) (pp-sum-merge pp-coughed-from-arg pp-arg))
       (pp-arg-cnt (+ ;;(expt 2 20) ;;test and remove later when sure...
                    pp-arg-cnt1 pp-arg-cnt2))
       (s-arg `(list . ,(cddr s-arg2)))
       (s-arg (s-sum-merge s-arg s-coughed-from-arg))
       ((mv s-coughed s-arg pp-coughed pp-arg)
        (clean-c/d-args s-arg pp-arg pp-arg-cnt clean-flg))
       (c-merged
        (create-c-instance s-arg pp-arg c/d-arg)))
    (mv s-coughed pp-coughed c-merged)))

(acl2::defines
 c/d-merge
 :flag-defthm-macro defthm-c/d-merge
 :flag-local nil
 :prepwork ((local
             (defthm lemma1
               (implies (and (rp-termp x)
                             (rp-termp y)
                             (rp-termp z))
                        (rp-termp
                         (list 'd
                               (list 'rp ''evenpi
                                     (list 'd-sum x y z)))))
               :hints (("goal"
                        :in-theory (e/d (is-rp rp-termp) ())))))

            (local
             (defthm lemma2
               (implies (and (rp-termp x)
                             (rp-termp y))
                        (and (rp-termp
                              (list 'binary-sum x y))
                             (rp-termp (list 'binary-append x y))
                             (rp-termp (list 'cons x y))
                             (rp-termp
                              (list 'list
                                    (list '--
                                          (list 's x y))))))
               :hints (("goal"
                        :in-theory (e/d (is-rp rp-termp) ())))))

            (local
             (defthm lemma3
               (implies (and (rp-term-listp x))
                        (and
                         (rp-termp (cons 'list x))
                         (rp-termp (cons 'c x))
                         (rp-termp (cons 's x))))
               :hints (("goal"
                        :in-theory (e/d (is-rp rp-termp) ())))))

            (local
             (defthm lemma4
               (rp-termp
                (list 'list
                      (list 'quote x)))
               :hints (("goal"
                        :in-theory (e/d (rp-termp is-rp) ())))))

            (local
             (defthm lemma5
               (implies (and (consp lst)
                             (rp-term-listp lst))
                        (rp-term-listp (cdr lst)))
               :hints (("Goal"
                        :expand (rp-term-listp lst)
                        :in-theory (e/d () ())))))

            (local
             (defthm lemma6
               (implies (and (rp-termp term)
                             (consp term)
                             (equal (car term) 'list))
                        (rp-term-listp (cdr term)))))

            (local
             (defthm lemma7
               (implies
                (can-c-merge-fast c/d1 c/d2)
                (and (consp
                      (mv-nth
                       0
                       (get-c/d-args
                        (mv-nth 1
                                (swap-c/ds c/d1 c/d2
                                           (equal (can-c-merge-fast c/d1 c/d2)
                                                  1))))))
                     (consp
                      (cdr (mv-nth
                            0
                            (get-c/d-args
                             (mv-nth 1
                                     (swap-c/ds c/d1 c/d2
                                                (equal (can-c-merge-fast c/d1 c/d2)
                                                       1)))))))
                     (equal (car (mv-nth
                                  0
                                  (get-c/d-args
                                   (mv-nth 1
                                           (swap-c/ds c/d1 c/d2
                                                      (equal (can-c-merge-fast c/d1 c/d2)
                                                             1))))))
                            'list)))
               :hints (("goal"
                        :in-theory (e/d (can-c-merge-fast
                                         can-c-merge-fast-aux
                                         get-c/d-args
                                         swap-c/ds) ())))))

            (local
             (defthm natp-lemma1
               (implies (and (natp x)
                             (natp y))
                        (natp (+ x y)))))

            (local
             (defthm natp-lemma2
               (implies (natp x)
                        (acl2-numberp x))))

            (local
             (in-theory (e/d (remove-s-from-for-fast-merge
                              c/d-merge-fast-aux)
                             (falist-consistent
                              rp-termp
                              natp)))))

 (define s-of-s-fix-aux ((s-lst)
                         (pp)
                         (c/d)
                         (limit natp))
   :measure (nfix limit)
   :returns (mv (pp-res rp-termp
                        :hyp (and (rp-term-listp s-lst)
                                  (rp-termp pp)
                                  (rp-termp c/d)))
                (c/d-res rp-termp "A dirty c/d"
                         :hyp (and (rp-term-listp s-lst)
                                   (rp-termp pp)
                                   (rp-termp c/d))))
   ;; iterate on s,
   ;; extract its insides and merge them with pp and c/d
   (cond
    ((zp limit)
     (progn$ (cw "Limit exhausted! ~%")
             (hard-error 's-of-s-fix-aux "" nil)
             (mv `(binary-append (list . ,s-lst) ,pp)
                 c/d)))

    ((atom s-lst)
     (mv pp c/d))
    (t
     (b* (((mv pp c/d) (s-of-s-fix-aux (cdr s-lst) pp c/d (1- limit)))
          (cur-s (ex-from-rp/-- (car s-lst))))
       (case-match cur-s
         (('s pp-cur c/d-cur)
          (b* (((mv s-coughed pp-coughed c/d)
                (c/d-merge c/d c/d-cur nil  (1- limit) ;;--hereeeee
                           ))
               ((mv pp &) (pp-sum-merge pp pp-cur))
               ((mv pp &) (pp-sum-merge pp pp-coughed)))
            (case-match s-coughed
              (('list . s-lst)
               (s-of-s-fix-aux s-lst pp c/d (1- limit)))
              (''nil
               (mv pp c/d))
              (& (progn$ (cw "Unexpected s format ~p0 ~%" s-coughed)
                         (hard-error 's-of-s-fix-aux "" nil)
                         (mv `(binary-append ,pp ,s-coughed) c/d))))))
         (''nil
          (mv pp c/d))
         (&
          (progn$ (cw "Unexpected s term ~p0 ~%" cur-s)
                  (hard-error 's-of-s-fix-aux "" nil)
                  (mv `(cons ,cur-s ,pp) c/d))))))))

 (define s-of-s-fix ((s)
                     (pp)
                     (c/d)
                     (limit natp))
   ;; pp is expected to be dirty wrt s
   ;; c/d is expected to be clean.
   ;; remove nested s instances for (s (+ s pp c/d))
   :returns (mv (pp-res rp-termp :hyp (and (rp-termp s)
                                           (rp-termp pp)
                                           (rp-termp c/d)))
                (c/d-res rp-termp :hyp (and (rp-termp s)
                                            (rp-termp pp)
                                            (rp-termp c/d))))
   :measure (nfix limit)
   (cond
    ((zp limit)
     (progn$ (cw "Limit exhausted! ~%")
             (hard-error 's-of-s-fix "" nil)
             (mv `(binary-append ,pp ,s) c/d)))
    (t
     (case-match s
       (('list . s-lst)
        (b* (((mv pp c/d)
              (s-of-s-fix-aux s-lst pp c/d (1- limit)))
             ((mv s-coughed pp-coughed c/d) (c/d-cough c/d))
             ((mv pp &) (pp-sum-merge pp pp-coughed))
             (pp (s-fix-args pp)))
          (if (equal s-coughed ''nil)
              (mv pp c/d)
            (s-of-s-fix s-coughed pp c/d (1- limit)))))
       (''nil
        (mv (s-fix-args pp) c/d))
       (& (progn$ (cw "Unexpected s format ~p0 ~%" s)
                  (hard-error 's-of-s-fix "" nil)
                  (mv `(binary-append ,pp ,s) c/d)))))))

 (define get-extra-s-arg ((s-arg)
                          (pp-arg)
                          (c/d-arg)
                          (limit natp))
;:inline t
   :measure (nfix limit)
   :returns (extra-s-arg rp-termp
                         :hyp (and (rp-termp s-arg)
                                   (rp-termp pp-arg)
                                   (rp-termp c/d-arg)))
   (cond
    ((zp limit)
     (progn$ (cw "Limit exhausted! ~%")
             (hard-error 'get-extra-s-arg "" nil)
             `(list (-- (s (binary-append ,s-arg ,pp-arg) ,c/d-arg)))))
    (t (b* (((mv s-pp s-c/d)
             (s-of-s-fix s-arg pp-arg c/d-arg (1- limit)))
            (res
             (cond ((and (quotep s-pp)
                         (quotep s-c/d)
                         (consp (cdr s-pp))
                         (consp (cdr s-c/d)))
                    (b* ((res (-- (s (unquote s-pp)
                                     (unquote s-c/d)))))
;(if (equal res 0)
; ''nil
                      `(list ',res)
;)
                      ))
                   ((extra-s-can-be-pp s-pp s-c/d)
                    `(list (-- ,(cadr s-pp))))
                   (t
                    `(list (-- (s ,s-pp ,s-c/d)))))))
         res))))

 (define c/d-merge ((c/d1)
                    (c/d2)
                    (clean-flg booleanp)
                    (limit natp))
   ;; merges two c/d terms (c/d1 and c/d2)
   ;; returns coughed-s, coughed-pp and merged c/d
   :measure (nfix limit)
   :returns (mv (s-coughed rp-termp
                           :hyp (and (rp-termp c/d1)
                                     (rp-termp c/d2)))
                (pp-coughed rp-termp
                            :hyp (and (rp-termp c/d1)
                                      (rp-termp c/d2)))
                (c/d-merged rp-termp
                            :hyp (and (rp-termp c/d1)
                                      (rp-termp c/d2))))

   (b* (((when (zp limit))
         (progn$ (cw "Limit reached!~&")
                 (hard-error 'c/d-merge "" nil)
                 (mv ''nil ''nil `(binary-sum ,c/d1 ,c/d2))))
        (c/d1 (ex-from-rp c/d1))
        (c/d2 (ex-from-rp c/d2))
        ((when (equal c/d1 ''0))
         (mv ''nil ''nil c/d2))
        ((when (equal c/d2 ''0))
         (mv ''nil ''nil c/d1))
        ;; check if can be merged without converting to d.
        (c-merge-fast (can-c-merge-fast c/d1 c/d2))
        ((mv c/d1 c/d2) ;; maybe swap them
         (swap-c/ds c/d1 c/d2 (equal c-merge-fast 1)))

        ((mv s-arg1 pp-arg1 c/d-arg1 type1) (get-c/d-args c/d1))
        ((mv s-arg2 pp-arg2 c/d-arg2 type2) (get-c/d-args c/d2))
        ((when (or (not type1)
                   (not type2)))
         (progn$ (cw "c/d-merge error. Terms are not instances of c or d. ~%")
                 (cw "Term1 = ~p0 ~%" c/d1)
                 (cw "Term2 = ~p0 ~%" c/d2)
                 (hard-error 'c/d-merge "" nil)
                 (mv ''nil ''nil `(binary-sum ,c/d1 ,c/d2))))

        ((mv s-coughed-from-arg pp-coughed-from-arg c/d-arg)
         (c/d-merge c/d-arg1 c/d-arg2 t ;;(expt 2 40)))
                    (1- limit)));; --hereeeee

        )
     (cond
      (c-merge-fast
       (c/d-merge-fast-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                           s-arg2 s-coughed-from-arg
                           c/d-arg
                           clean-flg))
      (t
       (b* ((c/d1-is-c (eq type1 'c))
            (c/d2-is-c (eq type2 'c))
            (extra-s-arg1 (and c/d1-is-c
                               (get-extra-s-arg s-arg1 pp-arg1
                                                c/d-arg1 (1- limit))))
            (extra-s-arg2 (and c/d2-is-c
                               (get-extra-s-arg s-arg2 pp-arg2
                                                c/d-arg2 (1- limit)))))
         (c/d-merge-slow-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                             s-arg1 s-arg2 s-coughed-from-arg
                             extra-s-arg1
                             extra-s-arg2
                             c/d-arg
                             clean-flg
                             c/d1-is-c
                             c/d2-is-c)))))))

;; (define c/d-merge-aux (c/d1-is-c
;;                        c/d2-is-c
;;                        extra-s-arg1
;;                        extra-s-arg2

(define quote-all (lst)
  :returns (res rp-term-listp)
  (if (atom lst)
      nil
    (cons (list 'quote (car lst))
          (quote-all (cdr lst)))))

(local
 (in-theory (disable
             pp-term-p)))

(define good-4vec-term-p (term)
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((orig term)
       (term (ex-from-rp term)))
    (case-match term
      (('sv::4vec-bitand x y)
       (and (good-4vec-term-p x)
            (good-4vec-term-p y)))
      (('sv::4vec-bitxor x y)
       (and (good-4vec-term-p x)
            (good-4vec-term-p y)))
      (('sv::4vec-bitor x y)
       (and (good-4vec-term-p x)
            (good-4vec-term-p y)))
      (('sv::4vec-? x y z)
       (and (good-4vec-term-p x)
            (good-4vec-term-p y)
            (good-4vec-term-p z)))
      (('sv::4vec-?* x y z)
       (and (good-4vec-term-p x)
            (good-4vec-term-p y)
            (good-4vec-term-p z)))
      (('svl::4vec-bitnot$ ''1 x)
       (and (good-4vec-term-p x)
            ))
      (('svl::bits num start size)
       (and (equal size ''1)
            (case-match num
              (('rp ''integerp x)
               (atom (ex-from-rp x))))
            (case-match start
              (('quote x)
               (natp x)))))
      (('sv::4vec-fix$inline x)
       (and (good-4vec-term-p x)))
      (('sv::3vec-fix x)
       (and (good-4vec-term-p x)))
      (& (pp-term-p orig)))))

(define 4vec->pp-term ((term good-4vec-term-p))
  :returns (pp-term)
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :guard-hints (("Goal"
                 :in-theory (e/d (good-4vec-term-p) ())))
  (b* ((orig term)
       (term (ex-from-rp term)))
    (case-match term
      (('sv::4vec-bitand x y)
       (b* ((n1 (4vec->pp-term x))
            (n2 (4vec->pp-term y)))
         `(binary-and ,n1 ,n2)))
      (('sv::4vec-bitxor x y)
       (b* ((n1 (4vec->pp-term x))
            (n2 (4vec->pp-term y)))
         `(binary-xor ,n1 ,n2)))
      (('sv::4vec-bitor x y)
       (b* ((n1 (4vec->pp-term x))
            (n2 (4vec->pp-term y)))
         `(binary-or ,n1 ,n2)))
      (('sv::4vec-? x y z)
       (b* ((n1 (4vec->pp-term x))
            (n2 (4vec->pp-term y))
            (n3 (4vec->pp-term z)))
         `(binary-? ,n1 ,n2 ,n3)))
      (('sv::4vec-?* x y z)
       (b* ((n1 (4vec->pp-term x))
            (n2 (4vec->pp-term y))
            (n3 (4vec->pp-term z)))
         `(binary-? ,n1 ,n2 ,n3)))
      (('svl::4vec-bitnot$ ''1 x)
       `(binary-not ,(4vec->pp-term x)))
      (('svl::bits num start &)
       `(bit-of ,num ,start))
      (('sv::4vec-fix$inline x)
       (4vec->pp-term x))
      (('sv::3vec-fix x)
       (4vec->pp-term x))
      (& orig)))
  ///

  (acl2::defret
   rp-termp-of--<fn>
   (rp-termp pp-term)
   :hyp (rp-termp term)

   :hints (("Goal"
            :induct (4vec->pp-term term)
            :do-not-induct t
            :expand ((:free (rest) (RP-TERMP (cons 'BIT-OF rest)))
                     (:free (rest) (RP-TERMP (cons 'quote rest)))
                     (:free (rest) (RP-TERMP (cons 'binary-not rest)))
                     (:free (rest) (RP-TERMP (cons 'binary-and rest)))
                     (:free (rest) (RP-TERMP (cons 'binary-or rest)))
                     (:free (rest) (RP-TERMP (cons 'binary-? rest)))
                     (:free (rest) (RP-TERMP (cons 'binary-xor rest))))
            :in-theory (e/d () (rp-termp
                                falist-consistent
                                pp-term-p)))))

  #|(local
  (defthm lemma1
  (IMPLIES (AND (PP-HAS-BITP-RP TERM))
  (equal (PP-TERM-P TERM)
  (B* ((ORIG TERM) (TERM (EX-FROM-RP TERM)))
  (CASE-MATCH TERM
  (('BINARY-AND X Y)
  (AND (PP-TERM-P X) (PP-TERM-P Y)))
  (('BINARY-OR X Y)
  (AND (PP-TERM-P X) (PP-TERM-P Y)))
  (('BINARY-XOR X Y)
  (AND (PP-TERM-P X) (PP-TERM-P Y)))
  (('BINARY-? X Y Z)
  (AND (PP-TERM-P X)
  (PP-TERM-P Y)
  (PP-TERM-P Z)))
  (('BINARY-NOT X) (AND (PP-TERM-P X)))
  (('BIT-OF & &) T)
  (''1 T)
  (& (PP-HAS-BITP-RP ORIG))))))
  :hints (("goal"
  :do-not-induct t
  :expand (pp-term-p term)
  :in-theory (e/d () (pp-has-bitp-rp))))))||#

  (acl2::defret
   pp-term-p-of--<fn>
   :hyp (good-4vec-term-p term)
   (pp-term-p pp-term)
   :hints (("Goal"
            :induct (4vec->pp-term term)
            :do-not-induct t
            :expand ((:free (x y) (pp-term-p (cons x y)))
                     (:free (x y) (is-rp (cons x y))))
            :in-theory (e/d (good-4vec-term-p) (rp-termp pp-term-p))))))

(progn
  (define well-formed-new-sum (term)
    :returns (res booleanp)
    (case-match term
      (('cons x rest)
       (b* ((?orig x)
            (x (ex-from-rp-loose x))
            (rest-res (well-formed-new-sum rest)))
         (cond ((case-match x (('s & &) t))
                rest-res)
               ((case-match x (('c & & &) t))
                rest-res)
               ((case-match x (('d ('rp ''evenpi ('d-sum & & &))) t))
                rest-res)
               ((case-match x (('c-res & & &) t))
                rest-res)
               ((case-match x (('sum-list ('list . &)) t))
                rest-res)
               ((equal x ''0)
                rest-res)
               ((good-4vec-term-p orig)
                rest-res)
               (t
                nil))))
      (('quote x)
       (integer-listp x))
      (& nil)))

  (defmacro mv-nth-0-of-2 (term)
    `(b* (((mv x &) ,term))
       x))

  (define new-sum-merge-aux ((term well-formed-new-sum))
    ;; a term to be summed that came from rewrite rules e.g full-adder to s-spec
    ;; and c-spec

    ;; expected input should be a list of s/c/d/c-res terms
    ;; goal is to sum them and return (mv s pp c/d)
    :returns (mv s-res pp c/d-raw)
    ;;(s-res rp-termp
    ;;        :hyp (rp-termp term))
    ;; (pp rp-termp
    ;;     :hyp (rp-termp term))
    ;; (c/d rp-termp
    ;;      :hyp (rp-termp term)))
    :prepwork ((local
                (in-theory (e/d (well-formed-new-sum)
                                (rp-termp)))))
    (case-match term
      (('cons x rest)
       (b* (((mv s-rest pp-rest c/d-rest)
             (new-sum-merge-aux rest))
            (limit (expt 2 40))
            (x-orig x)
            (x (ex-from-rp-loose x)))
         (cond ((case-match x (('s & &) t))
                (mv (s-sum-merge `(list ,x-orig) s-rest)
                    pp-rest
                    c/d-rest))
               ((case-match x (('c & & &) t))
                (b* (((mv s pp c/d)
                      (c/d-merge c/d-rest x-orig nil limit)))
                  (mv (s-sum-merge s-rest s)
                      (mv-nth-0-of-2 (pp-sum-merge pp-rest pp))
                      c/d)))
               ((case-match x (('d ('rp ''evenpi ('d-sum & & &))) t))
                (b* (((mv s pp c/d)
                      (c/d-merge c/d-rest x-orig nil limit)))
                  (mv (s-sum-merge s-rest s)
                      (mv-nth-0-of-2 (pp-sum-merge pp-rest pp))
                      c/d)))
               ((case-match x (('c-res & & &) t))
                (b* (((mv s pp c/d)
                      (c/d-merge c/d-rest (cadddr x) nil limit)))
                  (mv (s-sum-merge
                       s-rest
                       (s-sum-merge s (cadr x)))
                      (mv-nth-0-of-2 (pp-sum-merge
                                      pp-rest
                                      (mv-nth-0-of-2 (pp-sum-merge pp (caddr x)))))
                      c/d)))
               ((case-match x (('sum-list ('list . &)) t))
                (mv s-rest
                    (mv-nth-0-of-2 (pp-sum-merge pp-rest (cadr x)))
                    c/d-rest))
               ((equal x ''0)
                (mv s-rest pp-rest c/d-rest))
               ((good-4vec-term-p x-orig) ;; (pp-term-p x)
                (b* ((x (4vec->pp-term x-orig)))
                  (mv s-rest
                      (mv-nth-0-of-2 (pp-sum-merge (pp-flatten x nil) pp-rest))
                      c/d-rest)))
               (t
                (progn$ (cw "not well-formed term for new sums= ~p0 ~%" x)
                        (mv ''nil ''nil ''0))))))
      (''nil
       (mv ''nil ''nil ''0))
      (('quote x)
       (mv ''nil `(list . ,(quote-all x)) ''0))
      (& (progn$ (cw "not well-formed term for new sums= ~p0 ~%" term)
                 ;; should never happen
                 (hard-error 'new-sum-merge-aux "" nil)
                 (mv ''nil ''nil ''0))))
    ///
    (local
     (defthm lemma1
       (implies (and (rp-termp x))
                (rp-termp (list 'list x)))
       :hints (("Goal"
                :in-theory (e/d (rp-termp
                                 is-rp) ())))))

    (local
     (defthm lemma2
       (implies (and (rp-term-listp x))
                (rp-termp (cons 'list x)))
       :hints (("Goal"
                :in-theory (e/d (rp-termp
                                 is-rp) ())))))

    (acl2::defret rp-termp-of--<fn>
                  :hyp (rp-termp term)
                  (and (rp-termp s-res)
                       (rp-termp pp)
                       (rp-termp c/d-raw))
                  :hints (("Goal"
                           :induct (new-sum-merge-aux term)
                           :do-not-induct t
                           :in-theory (e/d () (rp-termp
                                               (:DEFINITION PP-TERM-P)))))))

  (define new-sum-merge ((term well-formed-new-sum))
    :returns (mv (s-res rp-termp :hyp (rp-termp term))
                 (pp rp-termp :hyp (rp-termp term))
                 (c/d rp-termp :hyp (rp-termp term)))
    :inline t
    (b* (((mv s pp c/d)
          (new-sum-merge-aux term))
;(s (s-fix-args s))
         )
      (mv s pp c/d))))

(define light-pp-term-p (term)
  :inline t
  (or
   (pp-has-bitp-rp term)
   (b* ((term (ex-from-rp term)))
     (case-match term
       (('binary-not &)
        t)
       (('binary-and & &)
        t)
       (('binary-or & &)
        t)
       (('binary-xor & &)
        t)
       (('binary-? & & &)
        t)
       (('bit-of & &)
        t)))))

(define light-pp-term-list-p (lst)
  (if (atom lst)
      (equal lst nil)
    (and (light-pp-term-p (car lst))
         (light-pp-term-list-p (cdr lst)))))

(define quarternaryp-sum-aux ((term well-formed-new-sum))
  :returns (mv (res natp
                    :rule-classes (:rewrite :type-prescription))
               (valid booleanp))
  :verify-guards nil
  :prepwork ((local
              (in-theory (disable natp)))
             (local
              (defthm lemma1
                (implies (NAT-LISTP lst)
                         (natp (sum-list lst)))
                :hints (("Goal"
                         :induct (sum-list lst)
                         :do-not-induct t
                         :in-theory (e/d (sum-list
                                          nat-listp
                                          sum)
                                         (+-is-sum))))
                :rule-classes (:type-prescription :rewrite))))
  (case-match term
    (('cons x rest)
     (b* (((mv rest-sum valid) (quarternaryp-sum-aux rest))
          ((unless valid)
           (mv 0 nil))
          (x-orig x)
          (x (ex-from-rp-loose x)))
       (cond ((light-pp-term-p x)
              (mv (1+ rest-sum) t))
             ((case-match x (('s & &) t))
              (mv (1+ rest-sum) t))
             ((case-match x-orig (('rp ''bitp ('c & & &)) t))
              (mv (1+ rest-sum) t))
             ((case-match x-orig (('rp ''bitp ('c-res & & &)) t))
              (mv (1+ rest-sum) t))
             ((equal x ''0)
              (mv rest-sum t))
             ((equal x ''1)
              (mv (1+ rest-sum) t))
             #|((case-match x (('quote &) t))
             (cond ((natp (cadr x))
             (mv (+ (cadr x) rest-sum) t))
             (t
             (mv 0 nil))))||#
             ;; ((case-match x (('sum-list ''nil) t))
             ;;  (mv rest-sum t))
             ;; ((case-match x (('sum-list ('list . &)) t))
             ;;  (if (light-pp-term-list-p (cdr (cadr x)))
             ;;      (mv (+ rest-sum (len (cdr (cadr x)))) t))
             (t
              (mv 0 nil)))))
    (''nil
     (mv 0 t))
    (('quote x)
     (cond ((natp x)
            (mv x t))
           ((nat-listp x)
            (mv (sum-list x) t))
           (t (mv 0 nil))))
    (& (mv 0 nil)))
  ///
  (verify-guards quarternaryp-sum-aux
    :hints (("Goal"
             :in-theory (e/d (WELL-FORMED-NEW-SUM) ())))))

(local
 (defthm is-rp-of-bitp
   (is-rp `(rp 'bitp ,x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(define quarternaryp-sum ((sum well-formed-new-sum))
  :returns (res booleanp)
  (b* (((mv res valid)
        (quarternaryp-sum-aux sum)))
    (and valid
         (quarternaryp res))))

(define c-spec-meta-aux (s pp c/d quarternaryp)
  :returns (res rp-termp
                :hyp (and (rp-termp s)
                          (rp-termp pp)
                          (rp-termp c/d)))
  :prepwork ((local
              (in-theory (disable natp))))
  (b* (((mv s-coughed pp-coughed c/d)
        (c/d-cough c/d))
       (s (s-sum-merge s-coughed s))
       ((mv pp pp-limit) (pp-sum-merge pp-coughed pp))
       ((mv s-coughed s)
        (c/d-fix-s-args s))
       ((mv pp-coughed pp)
        (c/d-fix-pp-args pp pp-limit))
       (c-term
        (create-c-instance s pp c/d)))
    #|(cond
    ((and (equal s ''nil) ;
    (equal c/d ''0) ;
    (case-match pp (('list ('binary-and & &)) t))) ;
    ''0) ;
    (t ;
    `(c ,s ,pp ,c/d)))||#

    #|(- (and (not (pp-orderedp pp))
    (cw "This pp on c-spec-meta-aux is not ordered! ~p0 ~%" ; ; ;
    pp)))||#
    #|(- (and (not (pp-orderedp pp-coughed))
    (cw "This pp-coughed on c-spec-meta-aux is not ordered! ~p0 ~%" ; ; ;
    pp-coughed)))||#
    (cond ((and (equal s-coughed ''nil)
                (equal pp-coughed ''nil))
           (if (quotep c-term)
               c-term
             (if quarternaryp
                 `(rp 'bitp ,c-term)
               c-term)))
          (t
           (b* ((res `(c-res ,s-coughed ,pp-coughed ,c-term)))
             (if quarternaryp
                 `(rp 'bitp ,res)
               res))))))

(define c-spec-meta (term)
  ;; term should be `(c-spec well-formed-new-sum)
  ;; well-formed-new-sum should be given to new-sum-merge-aux
  ;; result of new-sum-merge-aux (mv s pp c/d)
  ;; this should be made into a c term and get  coughed-out
  ;; then returns `(c-res ,s-coughed ,pp-coughed ,c/d-cleaned)

  ;; later try to attach bitp to the returned value.
  :returns (mv (res rp-termp
                    :hyp (rp-termp term))
               (dont-rw dont-rw-syntaxp))
  (b* ((result
        (case-match term
          (('c-spec sum)
           (if (well-formed-new-sum sum)
               (b* (((mv s pp c/d)
                     (new-sum-merge sum))
                    (quarternaryp (quarternaryp-sum sum))
                    #|(- (and (not quarternarp)
                    (cw "s-c-spec This term is not quarternarp ~p0 ~&" sum)))||#)
                 (c-spec-meta-aux s pp c/d quarternaryp))
             (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                     term)))
          (& term))))
    (mv result t)))

;; (c-spec-meta `(c-spec (cons (binary-and (bit-of a 0) (bit-of b 0))
;;                             (cons (binary-or (binary-and (bit-of a 0) (bit-of b 0))
;;                                              (binary-and (bit-of a 0) (bit-of b 0)))
;;                                   'nil))))

(define create-s-instance (pp c/d)
  :inline t
  :returns (res rp-termp
                :hyp (and (rp-termp pp)
                          (rp-termp c/d)))
  (cond ((and (quotep pp)
              (quotep c/d)
              (consp (cdr pp))
              (consp (cdr c/d)))
         `',(s (unquote pp) (unquote c/d)))
        ((and (equal c/d ''0)
              (case-match pp (('list ('binary-and & &)) t)))
         (cadr pp))
        (t
         `(rp 'bitp (s ,pp ,c/d)))))

(define s-spec-meta-aux (s pp c/d)
  :returns (res rp-termp
                :hyp (and (rp-termp s)
                          (rp-termp pp)
                          (rp-termp c/d)))
  (b* ((limit (expt 2 40))
       ((mv pp c/d)
        (case-match s
          (''nil
           (b* (((mv s-coughed pp-coughed c/d) (c/d-cough c/d))
                ((mv pp &) (pp-sum-merge pp pp-coughed)))
             (s-of-s-fix s-coughed pp c/d limit)))
          (&
           (s-of-s-fix s pp c/d limit))))
       (pp (s-fix-args pp))
       #|(- (and (not (pp-orderedp pp))
       (cw "This pp in s-spec-meta-aux is not ordered! ~p0 ~%" ;
       pp)))||#)
    (create-s-instance pp c/d)))

(define s-spec-meta (term)

  ;; term should be `(s-pec well-formed-new-sum)
  ;; well-formed-new-sum should be given to new-sum-merge-aux
  ;; result of new-sum-merge-aux (mv s pp c/d)
  ;; s-of-s-fix should be called on s
  ;; result should be returned `(s pp-new c/d-new)

  ;; later try to attach bitp to the returned value.
  :returns (mv (res rp-termp
                    :hyp (rp-termp term))
               (dont-rw dont-rw-syntaxp))
  (b* ((result (case-match term
                 (('s-spec sum)
                  (cond ((well-formed-new-sum sum)
                         (b* (((mv s pp c/d)
                               (new-sum-merge sum)))
                           (s-spec-meta-aux s pp c/d)))
                        (t
                         (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                                 term))))
                 (& term))))
    (mv result t)))

(define s-c-spec-meta (term)
  :returns (mv (res rp-termp
                    :hyp (rp-termp term))
               (dont-rw dont-rw-syntaxp))
  :prepwork ((local
              (defthm lemma1
                (IS-RP (LIST 'RP ''BITP x))
                :hints (("Goal"
                         :in-theory (e/d (is-rp) ()))))))
  (b* ((result
        (case-match term
          (('s-c-spec sum)
           (if (well-formed-new-sum sum)
               (b* (((mv s pp c/d)
                     (new-sum-merge sum))
                    (quarternaryp (quarternaryp-sum sum))
                    #|(- (and (not quarternarp)
                    (cw "s-c-spec This term is not quarternarp ~p0 ~&" sum)))||#
                    (s-res (s-spec-meta-aux s pp c/d))
                    (c-res (c-spec-meta-aux s pp c/d quarternaryp))
                    (res `(cons ,s-res (cons ,c-res 'nil)))
                    #|(- (if (search-pattern res)
                    (cw "pattern found s-c-spec-meta ~%")
                    nil))||#)
                 res)
             (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                     term)))
          (('c-s-spec sum)
           (if (well-formed-new-sum sum)
               (b* (((mv s pp c/d)
                     (new-sum-merge sum))
                    (quarternaryp (quarternaryp-sum sum))
                    (s-res (s-spec-meta-aux s pp c/d))
                    #|(- (and (not quarternarp)
                    (cw "c-s-spec This term is not quarternarp ~p0 ~&" sum)))||#
                    (c-res (c-spec-meta-aux s pp c/d quarternaryp)))
                 `(cons ,c-res (cons ,s-res 'nil)))
             (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                     term)))
          (('s-spec sum)
           (cond ((well-formed-new-sum sum)
                  (b* (((mv s pp c/d)
                        (new-sum-merge sum)))
                    (s-spec-meta-aux s pp c/d)))
                 (t
                  (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                          term))))
          (('c-spec sum)
           (if (well-formed-new-sum sum)
               (b* (((mv s pp c/d)
                     (new-sum-merge sum))
                    (quarternaryp (quarternaryp-sum sum))
                    #|(- (and (not quarternarp)
                    (cw "s-c-spec This term is not quarternarp ~p0 ~&" sum)))||#)
                 (c-spec-meta-aux s pp c/d quarternaryp))
             (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                     term)))
          (& term))))
    (mv result t)))

#|

(s-spec-meta `(s-spec (cons (binary-and (bit-of a 0) (bit-of b 0))
                            (cons (binary-or (binary-and (bit-of a 0) (bit-of b 0))
                                             (binary-and (bit-of a 0) (bit-of b 0)))
                                  (cons (binary-and (bit-of a 0) (bit-of b 0))
                                        (cons (binary-and (bit-of a 1) (bit-of
                                                                        b 0))
                                              'nil
                                              ))))))
||#
;;;;;;;;;;;;;;;;;;;;

(encapsulate
  nil

  (local
   (defthm lemma1
     (EQUAL (NOT (ATOM Y)) (CONSP Y))))

  (local
   (in-theory (disable
               (:DEFINITION PP-TERM-P)
               (:DEFINITION rp-termp)
               (:DEFINITION ASSOC-EQUAL)
               (:DEFINITION NOT)
               (:definition assoc-equal)
               (:definition pairlis2)
               (:definition pairlis$)
               (:DEFINITION GLOBAL-TABLE)
               (:DEFINITION GET-GLOBAL)
               (:DEFINITION C/D-MERGE)
               (:DEFINITION W)
               (:REWRITE ACL2::MV-NTH-OF-CONS)

               +-is-SUM
               mod2-is-m2
               floor2-if-f2
               c-is-f2
               D-IS-D2
               s-is-m2
               s-spec-is-m2
               SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
               c-spec-is-f2
               s-c-spec-is-list-m2-f2
               c-s-spec-is-list-m2-f2
               S-OF-C-TRIG-def
               )))

  (local
   (defthm pairlis$-opener
     (equal (pairlis$ (cons x rest) y)
            (CONS (CONS x (car y))
                  (PAIRLIS$ rest
                            (cdr y))))
     :hints (("Goal"
              :in-theory (e/d (pairlis$) ())))))

  (local
   (defthm pairlis$-nil
     (equal (pairlis$ nil y)
            nil)
     :hints (("Goal"
              :in-theory (e/d (pairlis$) ())))))

  (local
   (defthm assoc-equal-opener
     (equal (assoc-equal x (cons (cons key val) b))
            (if (equal x key)
                (cons key val)
              (assoc-equal x b)))
     :hints (("Goal"
              :in-theory (e/d (assoc-equal) ())))))

  (local
   (defthm assoc-equal-nil
     (equal (assoc-equal key nil)
            nil)
     :hints (("Goal"
              :in-theory (e/d (assoc-equal) ())))))

  (local
   (defthm rp-evl-of-variable-redef
     (implies (and (SYMBOLP ACL2::X)
                   ACL2::X)
              (EQUAL (RP-EVL ACL2::X ACL2::A)
                     (CDR (ASSOC-EQUAL ACL2::X ACL2::A))))))

  (local
   (define if$ (x y z)
     (if x y z)
     ///
     (defthm if$-implies
       (implies (if$ x y z)
                (if x y z))
       :rule-classes :forward-chaining)
     (defthm rp-evl-of-if-call-redef
       (implies (and (consp acl2::x)
                     (equal (car acl2::x) 'if))
                (equal (rp-evl acl2::x acl2::a)
                       (if$ (rp-evl (cadr acl2::x) acl2::a)
                            (rp-evl (caddr acl2::x) acl2::a)
                            (rp-evl (cadddr acl2::x) acl2::a)))))

     (defthm if$-test-correct
       (implies x
                (equal (if$ x y z)
                       y)))

     (defthm if$-test-false
       (implies (not x)
                (equal (if$ x y z)
                       z)))

     (defthm if$-case-1
       (iff (if$ x x t)
            t))

     (defthm if$-case-2
       (equal (if$ x y y)
              y))

     (defthm eq-is-equal
       (equal (eq x y)
              (equal x y)))

     (defthm if$-of-repeated-boolean
       (implies (booleanp x)
                (equal (if$ x x nil)
                       x)))

     (defthm if$-test-of-constants
       (and (iff (if$ test t nil)
                 test)
            (implies (booleanp test)
                     (equal (if$ test t nil)
                            test))
            (equal (if$ test nil t)
                   (not test))
            (equal (if$ test t t)
                   t)
            (equal (if$ test nil nil)
                   nil)))))

  (local
   (in-theory (disable rp-evl-of-variable)))

  (local
   (defthm dummy-lemma2
     (implies (or (EQUAL (CAR (RP-EVL Y CMR::ENV))
                         'BINARY-AND)
                  (EQUAL (CAR (RP-EVL Y CMR::ENV))
                         'AND-LIST))
              (equal (EQUAL (RP-EVL Y CMR::ENV) ''1)
                     nil))))

  (local
   (in-theory (enable extra-s-can-be-pp)))

  (local
   (defthm EXTRA-S-CAN-BE-PP-def
     (equal (EXTRA-S-CAN-BE-PP pp c/d)
            (AND (EQUAL C/D ''0)
                 (CASE-MATCH PP (('LIST ('BINARY-AND & &)) T))))))

  (with-output
    :off :all
    :gag-mode nil

    (def-formula-checks
      mult-formula-checks
      (;pp-sum-merge
;s-sum-merge
       binary-append
;pp-lists-to-term-pp-lst
;pp-term-to-pp-lists
       --
       sum-list
;s-c-spec-meta
;s-spec-meta
;c-spec-meta
       binary-and
       and-list
       sort-sum
       rp::c-s-spec
       rp::s-c-spec
       rp::c-spec
       rp::s-spec
       bit-of
       svl::bits
       svl::4vec-bitand
       svl::4vec-bitor
       svl::4vec-?
       svl::4vec-?*
       sv::4vec-bitxor
       svl::4vec-bitnot
       svl::4vec-bitnot$
       adder-b+
       s-of-c-trig
       binary-?
       binary-xor
       binary-or
       binary-not
       bit-fix
       c-res
       d
       c
       m2 d2 f2 times2
       s
       binary-sum
;sort-sum-meta
       evenpi
       d-sum
       sv::3vec-fix
       sv::4vec-fix
;c-s-spec-meta
       ))))

(defmacro ss (&rest args)
  `(s-spec (list . ,args)))

(defmacro cc (&rest args)
  `(c-spec (list . ,args)))
