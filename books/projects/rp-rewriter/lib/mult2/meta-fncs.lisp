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

(acl2::defines
 rp-order
 :flag-local nil
 :prepwork
 ((local
   (in-theory (enable rp::measure-lemmas))))
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

  (define pp-order (x y)
    :inline t
    :returns (mv (order)
                 (equals booleanp))
    (b* ((x (case-match x (('-- a) a) (& x)))
         (y (case-match y (('-- a) a) (& y))))
      (b* (((mv x atom-x) (case-match x
                            (('and-list ('list . lst))
                             (mv lst nil))
                            (('binary-and & &)
                             (mv (cdr x) nil))
                            (& (mv x t))))
           ((mv y atom-y) (case-match y
                            (('and-list ('list . lst))
                             (mv lst nil))
                            (('binary-and & &)
                             (mv (cdr y) nil))
                            (& (mv y t)))))
        (cond ((or atom-x atom-y)
               (cond ((not atom-x)
                      (if (consp x)
                          (if (equal (car x) y)
                              (mv nil (atom (cdr x)))
                            (mv (not (lexorder y (car x))) nil))
                        (mv t nil)))
                     ((not atom-y)
                      (if (consp y)
                          (if (equal (car y) x)
                              (mv (not (atom y)) (atom y))
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
        (if res
            (mv `(list . ,res) cnt)
          (mv ''nil 0)))))

  (memoize 'pp-sum-merge :condition '(and (not (equal pp1 ''nil)) (not (equal pp2 ''nil)))))

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
        (if res `(list . ,res) ''nil)))))

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

  (define c/d-fix-s-args-disabled ()
    :inline t
    nil)
  
  (define c/d-fix-s-args ((s))
    ;; same as c/d-pp-fix but don't touch the negated terms
    ;; cough out duplicates.
    :returns (mv (coughed-s rp-termp
                            :hyp (rp-termp s))
                 (cleaned-s rp-termp
                            :hyp (rp-termp s)))
    (if (c/d-fix-s-args-disabled)
        (mv ''nil s)
      (case-match s
        (('list . s-lst)
         (b* (((mv coughed-lst res-lst) (c/d-fix-arg-aux s-lst nil (expt 2 30))))
           (mv (if coughed-lst `(list . ,coughed-lst) ''nil)
               (if res-lst (cons-with-hint 'list res-lst s) ''nil))))
        (''nil (mv ''nil ''nil))
        (& (progn$ (cw "Unexpected s form= ~p0 ~%" s)
                   (hard-error 'c/d-fix-s-args "" nil)
                   (mv ''nil s)))))))

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
    (('d ('rp ''evenp2 ('d-sum s pp c/d)))
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
    (('d ('rp ''evenp2 ('d-sum s pp1 c/d1)))
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
                   `(d (rp 'evenp2 (d-sum ,s ,pp ,c/d-arg)))))
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
  (if (atom s-lst)
      nil
    (or (b* ((cur-s (ex-from-rp-loose (car s-lst))))
          (case-match cur-s
            (('s pp-arg c/d-arg)
             (progn$
              (and
               ;;(equal c/d-arg c/d) (equal pp-arg pp)
               (rp-equal-cnt c/d-arg c/d 10) (rp-equal-cnt pp-arg pp 10)
               )))))
        (can-c-merge-fast-aux (cdr s-lst) pp c/d)
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
                               (list 'rp ''evenp2
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
             (defthm natp-lemma1
               (implies (and (natp x)
                             (natp y))
                        (natp (+ x y)))))

            (local
             (defthm natp-lemma2
               (implies (natp x)
                        (acl2-numberp x))))

            (local
             (in-theory (disable falist-consistent
                                 rp-termp
                                 natp))))

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
                (c/d-merge c/d c/d-cur nil (1- limit)))
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
             (s-of-s-fix s-arg pp-arg c/d-arg (1- limit))))
         (cond ((and (quotep s-pp)
                     (quotep s-c/d)
                     (consp (cdr s-pp))
                     (consp (cdr s-c/d)))
                (b* ((res (-- (s (unquote s-pp)
                                 (unquote s-c/d)))))
                  (if (equal res 0)
                      ''nil
                    `(list ',res))))
               (t
                `(list (-- (s ,s-pp ,s-c/d)))))))))

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
         (c/d-merge c/d-arg1 c/d-arg2 t (1- limit)))

        ((mv pp-arg pp-arg-cnt1) (pp-sum-merge pp-arg1 pp-arg2))
        ((mv pp-arg pp-arg-cnt2) (pp-sum-merge pp-coughed-from-arg pp-arg))
        (pp-arg-cnt (+ ;(expt 2 20) ;;test and remove later when sure...
                     pp-arg-cnt1 pp-arg-cnt2)))
     (cond
      (c-merge-fast
       (b* (;(- (fast-merge-profile))
            (s-arg (s-sum-merge s-arg2 `(list (-- (s ,pp-arg1 ,c/d-arg1)))))
            (s-arg (s-sum-merge s-arg s-coughed-from-arg))

            ((mv s-coughed s-arg pp-coughed pp-arg)
             (clean-c/d-args s-arg pp-arg pp-arg-cnt clean-flg))
            (c-merged
             (create-c-instance s-arg pp-arg c/d-arg))
            #|(if (and (equal s-arg ''nil)
            (equal c/d-arg ''0)
            (case-match pp (('list ('binary-and & &)) t)))
            ''0
            `(c ,s-arg ,pp-arg ,c/d-arg))||#)
         (mv s-coughed pp-coughed c-merged)))
      (t
       (b* ((c/d1-is-c (eq type1 'c))
            (c/d2-is-c (eq type2 'c))

            (s-arg (s-sum-merge s-arg2 s-coughed-from-arg))
            (s-arg (s-sum-merge s-arg1 s-arg))

            (extra-s-arg1 (and c/d1-is-c
                               (get-extra-s-arg s-arg1 pp-arg1
                                                c/d-arg1 (1- limit))))
            (extra-s-arg2 (and c/d2-is-c
                               (get-extra-s-arg s-arg2 pp-arg2
                                                c/d-arg2 (1- limit))))

            (s-arg (cond ((and c/d1-is-c c/d2-is-c)
                          (s-sum-merge s-arg (s-sum-merge extra-s-arg1 extra-s-arg2)))
                         (c/d1-is-c (s-sum-merge s-arg extra-s-arg1))
                         (c/d2-is-c (s-sum-merge s-arg extra-s-arg2))
                         (t s-arg)))

            ((mv s-coughed s-arg pp-coughed pp-arg)
             (clean-c/d-args s-arg pp-arg pp-arg-cnt clean-flg))

            (d-res `(d (rp 'evenp2 (d-sum ,s-arg ,pp-arg ,c/d-arg))))
            (c/d-merged (if clean-flg (d-to-c d-res) d-res)))

         (mv s-coughed pp-coughed c/d-merged)))))))

(define quote-all (lst)
  :returns (res rp-term-listp)
  (if (atom lst)
      nil
    (cons (list 'quote (car lst))
          (quote-all (cdr lst)))))

(progn
  (define well-formed-new-sum (term)
    :returns (res booleanp)
    (case-match term
      (('cons x rest)
       (b* ((x (ex-from-rp-loose x))
            (rest-res (well-formed-new-sum rest)))
         (cond ((pp-term-p x)
                rest-res)
               ((case-match x (('s & &) t))
                rest-res)
               ((case-match x (('c & & &) t))
                rest-res)
               ((case-match x (('d ('rp ''evenp2 ('d-sum & & &))) t))
                rest-res)
               ((case-match x (('c-res & & &) t))
                rest-res)
               ((case-match x (('sum-list ('list . &)) t))
                rest-res)
               ((equal x ''0)
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
         (cond ((pp-term-p x)
                (mv s-rest
                    (mv-nth-0-of-2 (pp-sum-merge (pp-flatten x) pp-rest))
                    c/d-rest))
               ((case-match x (('s & &) t))
                (mv (s-sum-merge `(list ,x-orig) s-rest)
                    pp-rest
                    c/d-rest))
               ((case-match x (('c & & &) t))
                (b* (((mv s pp c/d)
                      (c/d-merge c/d-rest x-orig nil limit)))
                  (mv (s-sum-merge s-rest s)
                      (mv-nth-0-of-2 (pp-sum-merge pp-rest pp))
                      c/d)))
               ((case-match x (('d ('rp ''evenp2 ('d-sum & & &))) t))
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
    (b* (((mv s pp c/d)
          (new-sum-merge-aux term))
         (s (s-fix-args s)))
      (mv s pp c/d))))

(define c-spec-meta-aux (s pp c/d)
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
    ((and (equal s ''nil)
    (equal c/d ''0)
    (case-match pp (('list ('binary-and & &)) t)))
    ''0)
    (t
    `(c ,s ,pp ,c/d)))||#

    #|(- (and (not (pp-orderedp pp))
    (cw "This pp on c-spec-meta-aux is not ordered! ~p0 ~%" ; ;
    pp)))||#
    #|(- (and (not (pp-orderedp pp-coughed))
    (cw "This pp-coughed on c-spec-meta-aux is not ordered! ~p0 ~%" ; ;
    pp-coughed)))||#
    (cond ((and (equal s-coughed ''nil)
                (equal pp-coughed ''nil))
           c-term)
          (t
           `(c-res ,s-coughed ,pp-coughed ,c-term)))))

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
                     (new-sum-merge sum)))
                 (c-spec-meta-aux s pp c/d))
             (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                     term)))
          (& term))))
    (mv result t)))

;; (c-spec-meta `(c-spec (cons (binary-and (bit-of a 0) (bit-of b 0))
;;                             (cons (binary-or (binary-and (bit-of a 0) (bit-of b 0))
;;                                              (binary-and (bit-of a 0) (bit-of b 0)))
;;                                   'nil))))

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
    (cond ((and (quotep pp)
                (quotep c/d)
                (consp (cdr pp))
                (consp (cdr c/d)))

           `',(s (unquote pp) (unquote c/d)))
          ((and (equal c/d ''0)
                (case-match pp (('list ('binary-and & &)) t)))
           (cadr pp))
          (t
           `(s ,pp ,c/d)))))

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
                    (s-res (s-spec-meta-aux s pp c/d))
                    (c-res (c-spec-meta-aux s pp c/d)))
                 `(cons (rp 'bitp ,s-res) (cons (rp 'bitp ,c-res) 'nil)))
             (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                     term)))
          (('c-s-spec sum)
           (if (well-formed-new-sum sum)
               (b* (((mv s pp c/d)
                     (new-sum-merge sum))
                    (s-res (s-spec-meta-aux s pp c/d))
                    (c-res (c-spec-meta-aux s pp c/d)))
                 `(cons (rp 'bitp ,c-res) (cons (rp 'bitp ,s-res) 'nil)))
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
               (:REWRITE ACL2::MV-NTH-OF-CONS))))

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

  (with-output
    :off :all
    :gag-mode nil

    (def-formula-checks
      mult-formula-checks
      (pp-sum-merge
       s-sum-merge
       binary-append
       pp-lists-to-term-pp-lst
       pp-term-to-pp-lists
       --
       sum-list
       s-c-spec-meta
       s-spec-meta
       c-spec-meta
       binary-and
       and-list
       c-s-spec-meta))))
