; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020 Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2022 Intel Corporation

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

;;(include-book "pp-flatten-meta-fncs")

(include-book "std/util/defines" :dir :system)

(include-book "equal-meta")

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arith-5
  :disabled t))

(local
 (in-theory (disable +-IS-SUM)))

(local
 (set-induction-depth-limit 1))

(define valid-list-termp (term)
  (case-match term
    (('list . &)
     t)
    (''nil
     t)
    (&  (hard-error 'valid-list-termp
                    "Unexpected list term ~p0 ~%"
                    (list (cons #\0 term))))))

(defmacro pp-cons (a b)
  `(cons ,a ,b))

(defmacro pp-cons-with-hint (a b hint)
  (declare (ignorable hint))
  `(cons-with-hint ,a ,b ,hint)
  ;;`(hons ,a ,b)
  )

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
    :returns (mv order equalsp)
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
    :returns (mv order equalsp)
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
               (mv cdr-order cdr-equal)))))

  ///
  (memoize 's-order) ;; for some reason it makes a difference especfially for
  ;; b16 multiplier
  )

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

(acl2::defsection create-and-list

  (local
   (defthm characterlistp-member-equal-lemma
     (implies (and (member-equal y x)
                   (character-listp x))
              (CHARACTERP y))
     :rule-classes (:forward-chaining :rewrite)))

  (define get-symbol-hash (x)
    :returns (hash (and (integerp hash)
                        (acl2-numberp hash)))
    (b* ((x (ex-from-rp x)))
      (if (symbolp x)
          (b* ((chars (explode (symbol-name x)))
               (hash (loop$ for x in chars sum
                            :guard (and ;;(character-listp chars)
                                    (CHARACTERP x))
                            (char-code x))))
            (ifix hash))
        0)))

  (memoize 'get-symbol-hash)

  (define and-list-hash-aux (lst)
    :returns (mv (hash )
                 (rest-size ))
    :verify-guards nil
    :prepwork
    ((local
      (use-arith-5 t)))
    (if (atom lst)
        (mv 0 0)
      (b* (((mv rest rest-size) (and-list-hash-aux (cdr lst)))
           (cur (ex-from-rp (car lst))))
        (case-match cur
          (('logbit$inline ('quote x) &)
           (mv (+ rest (* (+ 5 rest-size)
                          (1+ (ifix x))))
               (+ 55 rest-size)))
          (('s ('quote x) & &)
           (mv (+ rest (ifix x))
               (+ 6 rest-size)))
          (('c ('quote (x . y))  & & &)
           (mv (+ rest (ifix x) (ifix y))
               (+ 8 rest-size)))
          (& (mv rest rest-size)))))
    ///
    (defret result-type-of-of-<fn>
      (and (natp rest-size)
           (acl2-numberp rest-size)
           (integerp hash)
           (acl2-numberp hash)))
    (verify-guards and-list-hash-aux))

  (define and-list-hash (lst)
    :returns (hash integerp)
    (b* (((mv hash &)
          (and-list-hash-aux lst)))
      (logapp 4 (len lst) hash)))

  (define create-and-list-instance (lst)
    :returns (and-list-instance rp-termp
                                :hyp (rp-term-listp lst))
    (cond ((and*-exec
            (consp lst)
            (atom (cdr lst))
            (or*-exec (logbit-p (ex-from-rp (car lst)))
                      (has-bitp-rp (car lst))
                      (equal (car lst) ''1)))
           (car lst))
          ((atom lst)
           ''1)
          (t
           `(and-list ',(and-list-hash lst) (list . ,lst))))))

(acl2::defsection pp-order

  (define pp-list-order-aux ((x)
                             (y))
    :returns (mv (order)
                 (equalsp booleanp))
    (cond ((or (atom x)
               (atom y))
           (mv (not (atom x)) (rp-equal-cnt-subterms x y 0)))
          ((rp-equal-cnt (car x) (car y) 0)
           (pp-list-order-aux (cdr x) (cdr y)))
          (t
           ;; lexorder2- sort from small to large
           (mv (lexorder2- (car y) (car x)) nil))))

  (define len-compare (x y)
    (if (or (atom x)
            (atom y))
        (not (atom x))
      (len-compare (cdr x) (cdr y))))

  (define pp-list-order (x y
                           (x-has-hash booleanp)
                           (y-has-hash booleanp))
    :returns (mv (order)
                 (equalsp booleanp))
    (b* (((when (equal y '('1)))
          (mv nil (rp-equal-cnt-subterms x y 0)))
         ((when (equal x '('1)))
          (mv t (rp-equal-cnt-subterms x y 0)))

         ;;((when t) (pp-list-order-aux x y))

         ((when (not* (equal x-has-hash y-has-hash)))
          (mv (not* y-has-hash) (rp-equal-cnt-subterms x y 0)))
         
         (hash-x (or x-has-hash (and-list-hash x)))
         (hash-y (or y-has-hash (and-list-hash y)))
         ((unless (equal hash-x hash-y))
          (mv (> hash-x hash-y)
              (rp-equal-cnt-subterms x y 0)))
         ;;(len-x (len x))
         ;;(len-y (len y))
         )
      (if (len-compare x y)
          ;; (if (equal len-y 2)
          ;;     (mv t nil)
          ;;   (if (equal len-x 2)
          ;;       (mv nil nil)
          (mv t nil)
        ;;))
        ;;(if (and t (equal len-x 2))
        (pp-list-order-aux x y)
        ;;(pp-list-order-aux y x)
        ;;)
        )))

  #|(define ex-from-rp/--loose (x)
  :returns (res rp-termp :hyp (rp-termp x))
  (cond ((and (consp x)
  (consp (cdr x)))
  (if (or (equal (car x) '--))
  (ex-from-rp/--loose (cadr x))
  (if (and (equal (car x) 'rp)
  (consp (cddr x)))
  (ex-from-rp/--loose (caddr x))
  x)))
  (t x)))|#

  (define ex-from-rp/times (x)
    :returns (res rp-termp :hyp (rp-termp x))
    :prepwork ((local
                (in-theory (enable is-rp))))
    (cond ((times-p x)
           (ex-from-rp/times (caddr x)))
          ((is-rp x)
           (ex-from-rp/times (caddr x)))
          ((--.p x)
           (ex-from-rp/times (cadr x)))
          (t x)))

  (define pp-order ((x rp-termp)
                    (y rp-termp))
    ;;:inline t
    :returns (mv (order)
                 (equalsp booleanp))
    (b* ((x (ex-from-rp$ x))
         (y (ex-from-rp$ y))
         ((when (or (quotep x)
                    (quotep y)))
          (cond ((and (quotep x)
                      (quotep y))
                 (mv (not* (lexorder y x)) (equal x y)))
                ((quotep x)
                 (mv t (equal x y)))
                (t (mv nil (equal x y)))))
         #|((when (equal x ''1))
         (mv t (equal x y)))|#
         ((mv x-lst x-hash x-hash-has x-is-and-list)
          (case-match* x
            (('and-list ('quote hash) ('list . lst))
             (mv lst (ifix hash) t t))
            (('and-times-list ('quote hash) ('list . lst) x)
             (mv (cons x lst) (ifix hash) t nil))
            (&
             (mv (list x) 0 nil nil))))
         ((mv y-lst y-hash y-hash-has y-is-and-list)
          (case-match* y
            (('and-list ('quote hash) ('list . lst))
             (mv lst (ifix hash) t t))
            (('and-times-list ('quote hash) ('list . lst) x)
             (mv (cons x lst) (ifix hash) t nil))
            (&
             (mv (list y) 0 nil nil)))))
      (if (= x-hash y-hash)
          (b* (((mv order equalsp)
                (pp-list-order x-lst y-lst
                               x-hash-has y-hash-has)))
            (mv order (if (and*-exec x-is-and-list y-is-and-list)
                          equalsp
                        (rp-equal-cnt x y 0))))
        (mv (> x-hash y-hash) nil))))

  ;; (defthm pp-list-order-sanity
  ;;   (implies (mv-nth 0 (pp-list-order x y))
  ;;            (not (mv-nth 0 (pp-list-order x y))))
  ;;   :hints (("Goal"
  ;;            :in-theory (e/d (pp-list-order
  ;;                             lexorder2-sanity)
  ;;                            (lexorder2)))))

  #|(define get-pp-order-and-new-coef ((term1 rp-termp)
  (term2 rp-termp))
  :returns (mv
  (order)
  (equal-terms booleanp))
  (b* (;;((mv & term1) (get-pp-and-coef term1))
  ;;((mv & term2) (get-pp-and-coef term2))
  ((mv order equalsp)
  (pp-order term1 term2))
  (equalsp (or equalsp
  (rp-equal-cnt term1 term2 0))))
  (mv order
  equalsp)))|#

  (define pp-lst-orderedp ((lst rp-term-listp))
    (if (atom lst)
        t
      (if (atom (cdr lst))
          t
        (and (not (equal (ex-from-rp$ (car lst)) ''0))
             (b* (((mv & cur1) (get-pp-and-coef (cadr lst)))
                  ((mv & cur2) (get-pp-and-coef (car lst)))
                  ((mv order equals)
                   (pp-order cur1 cur2))
                  (equals (or* equals
                               (rp-equal-cnt cur1 cur2 0))))
               (and (not order)
                    (not equals)))
             (pp-lst-orderedp (cdr lst))))))

  (define pp-orderedp ((pp rp-termp))
    (case-match pp
      (('list . lst)
       (pp-lst-orderedp lst))
      (''nil
       t)
      (& nil))))

(define append-reverse (x y)
    (if (atom x)
        y
      (append-reverse (cdr x) (cons (car x) y))))

#|(define pp-sum-merge-aux ((pp1-lst rp-term-listp)
                          (pp2-lst rp-term-listp)
                          &key
                          ((acc rp-term-listp) 'nil))
  :measure (+ (cons-count pp1-lst)
              (cons-count pp2-lst))
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :returns (merged-pp-lst rp-term-listp
                          :hyp (and (rp-term-listp pp1-lst)
                                    (rp-term-listp pp2-lst)))
  (cond ((atom pp1-lst) (append-reverse acc pp2-lst))
        ((atom pp2-lst) (append-reverse acc pp1-lst))
        (t (b* (((mv coef1 cur1) (get-pp-and-coef (car pp1-lst)))
                ((mv coef2 cur2) (get-pp-and-coef (car pp2-lst)))
                ((when (or* (equal (ex-from-rp$ cur1) ''0)
                            (= coef1 0)))
                 (pp-sum-merge-aux (cdr pp1-lst) pp2-lst :acc acc ))
                ((when (or* (equal (ex-from-rp$ cur2) ''0)
                            (= coef2 0)))
                 (pp-sum-merge-aux pp1-lst (cdr pp2-lst)) :acc acc)
                ((mv order equals)
                 (pp-order cur1 cur2))
                (equals (or* equals
                             (rp-equal-cnt cur1 cur2 0))))
             (cond (equals
                    (pp-sum-merge-aux (cdr pp1-lst) (cdr pp2-lst)
                                      :acc  (cons-with-times (+ coef1 coef2)
                                                             cur1 acc)))
                   (order
                    (pp-sum-merge-aux (cdr pp1-lst) pp2-lst :acc (cons (car pp1-lst) acc)))
                   (t
                    (pp-sum-merge-aux pp1-lst (cdr pp2-lst) :acc (cons (car pp2-lst) acc))))))))|#

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
        (t (b* (((mv coef1 cur1) (get-pp-and-coef (car pp1-lst)))
                ((mv coef2 cur2) (get-pp-and-coef (car pp2-lst)))
                ((when (or* (equal (ex-from-rp$ cur1) ''0)
                            (= coef1 0)))
                 (pp-sum-merge-aux (cdr pp1-lst) pp2-lst ))
                ((when (or* (equal (ex-from-rp$ cur2) ''0)
                            (= coef2 0)))
                 (pp-sum-merge-aux pp1-lst (cdr pp2-lst)))
                ((mv order equals)
                 (pp-order cur1 cur2))
                (equals (or* equals
                             (rp-equal-cnt cur1 cur2 0))))
             (cond (equals
                    (cons-with-times (+ coef1 coef2)
                                     cur1
                                     (pp-sum-merge-aux (cdr pp1-lst) (cdr pp2-lst))))
                   (order
                    (b* ((rest (pp-sum-merge-aux (cdr pp1-lst) pp2-lst )))
                      (pp-cons (car pp1-lst) rest)))
                   (t
                    (b* ((rest (pp-sum-merge-aux pp1-lst (cdr pp2-lst) )))
                      (pp-cons (car pp2-lst) rest))))))))

(defthm cons-count-of-evens
  (implies (and (consp lst)
                (consp (cdr lst)))
           (< (cons-count (evens lst))
              (cons-count lst)))
  :hints (("Goal"
           :in-theory (e/d (cons-count
                            evens)
                           ()))))

(defthm cons-count-of-odds
  (implies (and (consp lst))
           (< (cons-count (odds lst))
              (cons-count lst)))
  :hints (("Goal"
           :use ((:instance cons-count-of-evens
                            (lst (cdr lst))))
           :do-not-induct t
           :in-theory (e/d (cons-count
                            evens odds)
                           (cons-count-of-evens)))))

(defthm rp-term-listp-of-evens
  (implies (rp-term-listp lst)
           (rp-term-listp (evens lst))))

(defthm rp-term-listp-of-odds
  (implies (rp-term-listp lst)
           (rp-term-listp (odds lst))))

(define pp-sum-sort-lst ((pp-lst rp-term-listp))
  :measure (cons-count pp-lst)
  :hints (("Goal"
           :in-theory (e/d () (evens odds))))
  :verify-guards :after-returns
  :returns (res-pp-lst rp-term-listp
                       :hyp (rp-term-listp pp-lst))
  (b* (((when (or (atom pp-lst)
                  (atom (cdr pp-lst))))
        pp-lst)
       (odds (odds pp-lst))
       (evens (evens pp-lst))
       (odds-sorted (pp-sum-sort-lst odds))
       (evens-sorted (pp-sum-sort-lst evens))
       (res (pp-sum-merge-aux odds-sorted evens-sorted)))
    res))

(local
 (in-theory (disable ACL2::EVENP-AND-ODDP-AS-LOGCAR)))

(define pp-sum-merge-lst-for-s ((pp1-lst rp-term-listp)
                                (pp2-lst rp-term-listp))
  :measure (+ (cons-count pp1-lst)
              (cons-count pp2-lst))
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :returns (merged-pp-lst rp-term-listp
                          :hyp (and (rp-term-listp pp1-lst)
                                    (rp-term-listp pp2-lst)))
  :verify-guards :after-returns

  (cond ((atom pp1-lst) pp2-lst)
        ((atom pp2-lst) pp1-lst)
        (t (b* (((mv coef1 cur1) (get-pp-and-coef (car pp1-lst)))
                ((mv coef2 cur2) (get-pp-and-coef (car pp2-lst)))
                ((when (or* (equal cur1 ''0)
                            (evenp coef1)))
                 (pp-sum-merge-lst-for-s (cdr pp1-lst) pp2-lst ))
                ((when (or* (equal cur2 ''0)
                            (evenp coef2)))
                 (pp-sum-merge-lst-for-s pp1-lst (cdr pp2-lst)))

                ((mv order equals)
                 (pp-order cur1 cur2))
                (equals (or* equals (rp-equal-cnt cur1 cur2 0)))
                )
             (cond (equals
                    (b* ((new-coef (+ coef1 coef2)))
                      (if (evenp new-coef)
                          (pp-sum-merge-lst-for-s (cdr pp1-lst) (cdr pp2-lst))
                        (cons cur1
                              (pp-sum-merge-lst-for-s (cdr pp1-lst) (cdr pp2-lst))))))
                   (order
                    (b* ((rest (pp-sum-merge-lst-for-s (cdr pp1-lst) pp2-lst )))
                      (pp-cons cur1 rest)))
                   (t
                    (b* ((rest (pp-sum-merge-lst-for-s pp1-lst (cdr pp2-lst) )))
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

;;(pp-lst-sum-merge '((a a a a b b b c d) (b c d e) (c d e m) (c f) (d f m))
;;:cough t)

(progn

  (define s-order-main ((term1 rp-termp)
                        (term2 rp-termp))
    :Returns (mv (order) (equalsp))
    (b* ((term1- (ex-from-rp$ term1))
         (term2- (ex-from-rp$ term2))

         ;;(terms-are-equal (rp-equal-cnt term1 term2 4))
         ;; ((when terms-are-equal)
         ;;  (mv nil (not (equal neg1 neg2)) t))
         ;; ((mv order &) (lexorder2 term2 term1))
         ((mv order terms-are-equal)
          (cond ((and ;;nil
                  (consp term1-)
                  (consp (cdr term1-))
                  (consp term2-)
                  (consp (cdr term2-)))
                 (if (rp-equal  (cadr term1-) ;;using rp-equal for proofs
                                (cadr term2-))
                     (s-order term1 term2)
                   (mv (lexorder (cadr term1-)
                                 (cadr term2-))
                       nil)))
                (t (s-order term1 term2)))))
      (mv order
          terms-are-equal)))

  (define s-sum-ordered-listp ((lst rp-term-listp))
    (if (atom lst)
        (equal lst nil)
      (if (atom (cdr lst))
          t
        (and (b* (((mv & cur1) (get-pp-and-coef (cadr lst)))
                  ((mv & cur2) (get-pp-and-coef (car lst)))
                  ((mv order &) (s-order-main cur1 cur2)))
               (not order))
             (s-sum-ordered-listp (cdr lst))))))

  #|(define s-sum-merge-aux ((s1-lst rp-term-listp)
                           (s2-lst rp-term-listp)
                           &key
                           ((acc rp-term-listp) 'nil) )
    :measure (+ (cons-count s1-lst)
                (cons-count s2-lst))
    :hints (("Goal"
             :in-theory (e/d (measure-lemmas) ())))
    :returns (merged-s-lst rp-term-listp
                           :hyp (and (rp-term-listp s1-lst)
                                     (rp-term-listp s2-lst)))
    (cond ((atom s1-lst)
           (append-reverse acc s2-lst))
          ((atom s2-lst)
           (append-reverse acc s1-lst))
          (t (b* ((cur1-orig (car s1-lst))
                  (cur2-orig (car s2-lst))
                  ((mv coef1 cur1) (get-pp-and-coef cur1-orig))
                  ((mv coef2 cur2) (get-pp-and-coef cur2-orig))

                  ((mv order equalsp)
                   (s-order-main cur1 cur2)))
               (cond (equalsp 
                      (s-sum-merge-aux (cdr s1-lst) (cdr s2-lst)
                                       :acc (cons-with-times (+ coef1 coef2)
                                                             cur1 acc)))
                     ((or* (equal cur1 ''0)
                           (= coef1 0))
                      (s-sum-merge-aux (cdr s1-lst) s2-lst :acc acc))
                     ((or* (equal cur2 ''0)
                           (= coef2 0))
                      (s-sum-merge-aux s1-lst (cdr s2-lst) :acc acc))
                     (order
                      (s-sum-merge-aux (cdr s1-lst) s2-lst :acc (cons cur1-orig acc)))
                     (t
                      (s-sum-merge-aux s1-lst (cdr s2-lst) :acc (cons cur2-orig acc))))))))|#

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
          (t (b* ((cur1-orig (car s1-lst))
                  (cur2-orig (car s2-lst))
                  ((mv coef1 cur1) (get-pp-and-coef cur1-orig))
                  ((mv coef2 cur2) (get-pp-and-coef cur2-orig))

                  ((mv order equalsp)
                   (s-order-main cur1 cur2)))
               (cond (equalsp
                      (cons-with-times (+ coef1 coef2)
                                       cur1
                                       (s-sum-merge-aux (cdr s1-lst) (cdr s2-lst))))
                     ((or* (equal cur1 ''0)
                           (= coef1 0))
                      (s-sum-merge-aux (cdr s1-lst) s2-lst))
                     ((or* (equal cur2 ''0)
                           (= coef2 0))
                      (s-sum-merge-aux s1-lst (cdr s2-lst)))
                     (order
                      (b* ((rest (s-sum-merge-aux (cdr s1-lst) s2-lst)))
                        (cons cur1-orig rest)))
                     (t
                      (b* ((rest (s-sum-merge-aux s1-lst (cdr s2-lst))))
                        (cons cur2-orig rest))))))))

  (define same-hash-dif-term (term1 term2)
    (declare (ignorable term1 term2))
    (hard-error 'same-hash-dif-term
                "term1: ~p0. term2: ~p1 ~%"
                (list (cons #\0 term1)
                      (cons #\1 term2))))

  (profile 'same-hash-dif-term)

  

  #|(define sum-merge-lst-for-s ((s1-lst rp-term-listp)
			       (s2-lst rp-term-listp)
			       &key
			       ((acc rp-term-listp) 'nil))
    :measure (+ (cons-count s1-lst)
                (cons-count s2-lst))
    :hints (("Goal"
             :in-theory (e/d (measure-lemmas) ())))
    :returns (merged-s-lst rp-term-listp
                           :hyp (and (rp-term-listp s1-lst)
				     (rp-term-listp acc)
                                     (rp-term-listp s2-lst)))
    (cond ((atom s1-lst)
	   (progn$ ;;(break$)
		   (append-reverse acc s2-lst)))
          ((atom s2-lst)
	   (progn$ ;;(break$)
		   (append-reverse acc  s1-lst)))
          (t (b* ((cur1-orig (car s1-lst))
                  (cur2-orig (car s2-lst))
                  ((mv coef1 cur1) (get-pp-and-coef cur1-orig))
                  ((mv coef2 cur2) (get-pp-and-coef cur2-orig))
                  ((mv order terms-are-equal)
                   (s-order-main cur1 cur2)))
               (cond (terms-are-equal
                      (b* ((new-coef (+ coef1 coef2)))
                        (if (evenp new-coef)
                            (sum-merge-lst-for-s (cdr s1-lst)
						 (cdr s2-lst)
						 :acc acc)
                          (sum-merge-lst-for-s (cdr s1-lst)
					       (cdr s2-lst)
					       :acc (cons cur1 acc)))))
                     ((or* (equal cur1 ''0)
                           (evenp coef1))
                      (sum-merge-lst-for-s (cdr s1-lst) s2-lst :acc acc))
                     ((or* (equal cur2 ''0)
                           (evenp coef2))
                      (sum-merge-lst-for-s s1-lst (cdr s2-lst) :acc acc))
                     (order
                      (sum-merge-lst-for-s (cdr s1-lst) s2-lst
					   :acc (cons cur1 acc)))
                     (t
                      (sum-merge-lst-for-s s1-lst
					   (cdr s2-lst)
					   :acc (cons cur2 acc))))))))|#
  
  (define sum-merge-lst-for-s ((s1-lst rp-term-listp)
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
          (t (b* ((cur1-orig (car s1-lst))
                  (cur2-orig (car s2-lst))
                  ((mv coef1 cur1) (get-pp-and-coef cur1-orig))
                  ((mv coef2 cur2) (get-pp-and-coef cur2-orig))
                  ((mv order terms-are-equal)
                   (s-order-main cur1 cur2)))
               (cond (terms-are-equal
                      (b* ((new-coef (+ coef1 coef2))
                           (rest (sum-merge-lst-for-s (cdr s1-lst) (cdr s2-lst))))
                        (if (evenp new-coef)
                            rest
                          (cons cur1 rest))))
                     ((or* (equal cur1 ''0)
                           (evenp coef1))
                      (sum-merge-lst-for-s (cdr s1-lst) s2-lst))
                     ((or* (equal cur2 ''0)
                           (evenp coef2))
                      (sum-merge-lst-for-s s1-lst (cdr s2-lst)))
                     (order
                      (b* ((rest (sum-merge-lst-for-s (cdr s1-lst) s2-lst)))
                        (cons cur1 rest)))
                     (t
                      (b* ((rest (sum-merge-lst-for-s s1-lst (cdr s2-lst))))
                        (cons cur2 rest))))))))

  (define s-sum-sort-lst ((s-lst rp-term-listp))
    :measure (cons-count s-lst)
    :hints (("Goal"
             :in-theory (e/d () (evens odds))))
    :verify-guards :after-returns
    :returns (res-pp-lst rp-term-listp
                         :hyp (rp-term-listp s-lst))
    (b* (((when (or (atom s-lst)
                    (atom (cdr s-lst))))
          s-lst)
         (odds (odds s-lst))
         (evens (evens s-lst))
         (odds-sorted (s-sum-sort-lst odds))
         (evens-sorted (s-sum-sort-lst evens))
         (res (s-sum-merge-aux odds-sorted evens-sorted)))
      res))

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
      (b* (((mv coef cur) (get-pp-and-coef (car pp-lst))))
        (cond ((evenp coef)
               (s-fix-pp-args-aux (cdr pp-lst)))
              (t (pp-cons-with-hint cur
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

  (define c-fix-arg-aux ((arg-lst rp-term-listp))
    :returns (mv (coughed-lst rp-term-listp
                              :hyp (rp-term-listp arg-lst))
                 (cleaned-lst rp-term-listp
                              :hyp (rp-term-listp arg-lst)))
    (cond
     ((atom arg-lst)
      (mv nil nil))
     (t
      (b* (((mv coef cur) (get-pp-and-coef (car arg-lst)))
           ((mv rest-coughed rest-pp)
            (c-fix-arg-aux (cdr arg-lst))))
        (cond
         ((= coef 0)
          (mv rest-coughed rest-pp))
         ((evenp coef)
          (mv (cons (create-times-instance (/ coef 2) cur)
                    rest-coughed)
              rest-pp))
         ((= coef 1)
          (mv rest-coughed
              (cons cur rest-pp)))
         (t
          (mv (cons (create-times-instance (floor coef 2) cur)
                    rest-coughed)
              (cons cur rest-pp))))))))

  (define c-fix-arg-aux-with-cond ((arg-lst rp-term-listp)
                                   cond)
    :inline t
    :returns (mv (coughed-lst rp-term-listp
                              :hyp (rp-term-listp arg-lst))
                 (cleaned-lst rp-term-listp
                              :hyp (rp-term-listp arg-lst)))
    (if cond
        (c-fix-arg-aux arg-lst)
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
       (b* (((mv coughed-lst res-lst) (c-fix-arg-aux pp-lst)))
         (mv (create-list-instance coughed-lst)
             (if res-lst (cons-with-hint 'list res-lst pp) ''nil))))
      (''nil (mv ''nil ''nil))
      (& (progn$ (cw "Unexpected pp form= ~p0 ~%" pp)
                 (hard-error 'c-fix-pp-args "" nil)
                 (mv ''nil pp)))))

  (define return-t ()
    t)
  (define return-nil ()
    nil)

  (define c-fix-s-args ((s rp-termp))
    ;; same as c/d-pp-fix but don't touch the negated terms
    ;; cough out duplicates. ;;OLD COMMENT?
    :returns (mv (coughed-s rp-termp
                            :hyp (rp-termp s))
                 (cleaned-s rp-termp
                            :hyp (rp-termp s)))
    (case-match s
      (('list . s-lst)
       (b* (((mv coughed-lst res-lst) (c-fix-arg-aux s-lst )))
         (mv (create-list-instance coughed-lst)
             (if res-lst (cons-with-hint 'list res-lst s) ''nil))))
      (''nil (mv ''nil ''nil))
      (& (progn$ (cw "Unexpected s form= ~p0 ~%" s)
                 (hard-error 'c-fix-s-args "" nil)
                 (mv ''nil s))))))

;; Better for measure proofs
(define shrinking-list-to-lst (term)
  :returns (res rp-term-listp :hyp (rp-termp term))
  (CASE-MATCH TERM
    (('LIST . LST) LST)
    (''NIL NIL)
    (&    (HARD-ERROR 'LIST-INSTANCE-TO-LST
                      "Unexpected list instance: ~p0 ~%"
                      (LIST (CONS #\0 TERM))))))

(define no-rep-p ((lst))
  (if (atom lst)
      t
    (if (atom (cdr lst))
        t
      (and (not (rp-equal-cnt
                 (ex-from-rp/times (car lst))
                 (ex-from-rp/times (cadr lst))
                 0))
           (no-rep-p (cdr lst))))))

(define list-of-only-s/c-p (lst fn)
  (if (atom lst)
      (equal lst nil)
    (b* ((x (ex-from-rp/times (car lst))))
      (and (consp x)
           (equal (car x) fn)
           (list-of-only-s/c-p (cdr lst) fn)))))

(acl2::defines
  ordered-s/c-p
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :prepwork ((local
              (include-book "lemmas"))
             (local
              (defthm dummy-lemma2
                (IMPLIES (< (cons-count term1) (cons-count term2))
                         (< (CONS-COUNT (SHRINKING-LIST-TO-LST term1))
                            (CONS-COUNT TERM2)))
                :hints (("Goal"
                         :in-theory (e/d (SHRINKING-LIST-TO-LST
                                          CONS-COUNT)
                                         ()))))))
  (define ordered-s/c-p ((term rp-termp))
    :measure (cons-count term)
    (b* ((term (ex-from-rp term)))
      (case-match term
        (('s & pp c)
         (and (pp-lst-orderedp (shrinking-list-to-lst pp))
              (no-rep-p (shrinking-list-to-lst pp))
              (s-sum-ordered-listp (shrinking-list-to-lst c))
              (no-rep-p (shrinking-list-to-lst c))
              (list-of-only-s/c-p (shrinking-list-to-lst c) 'c) 
              (ordered-s/c-p-lst (shrinking-list-to-lst c))))
        (('c & s pp c)
         (and (pp-lst-orderedp (shrinking-list-to-lst pp))
              (no-rep-p (shrinking-list-to-lst pp))
              (s-sum-ordered-listp (shrinking-list-to-lst s))
              (no-rep-p (shrinking-list-to-lst s))
              (list-of-only-s/c-p (shrinking-list-to-lst s) 's)
              (s-sum-ordered-listp (shrinking-list-to-lst c))
              (no-rep-p (shrinking-list-to-lst c))
              (list-of-only-s/c-p (shrinking-list-to-lst c) 'c)
              (ordered-s/c-p-lst (shrinking-list-to-lst s))
              (ordered-s/c-p-lst (shrinking-list-to-lst c))))
        (('s-c-res s pp c)
         (and (pp-lst-orderedp (shrinking-list-to-lst pp))
              (s-sum-ordered-listp (shrinking-list-to-lst s))
              (s-sum-ordered-listp (shrinking-list-to-lst c))
              (list-of-only-s/c-p (shrinking-list-to-lst s) 's)
              (list-of-only-s/c-p (shrinking-list-to-lst c) 'c)
              (ordered-s/c-p-lst (shrinking-list-to-lst s))
              (ordered-s/c-p-lst (shrinking-list-to-lst c))))
        (('-- term)
         (ordered-s/c-p term))
        (('times & term)
         (ordered-s/c-p term))
        (('and-list & ('list . lst))
         (ordered-s/c-p-lst lst))
        (('quote &)
         t)
        (& (if (or (binary-fnc-p term)
                   (and-list-p term)
                   (logbit-p term)
                   (atom term))
               t
             (hard-error 'ordered-s/c-p
                         "unexpected term: ~p0 ~%"
                         (list (cons #\0 term))))))))
  (define ordered-s/c-p-lst ((lst rp-term-listp))
    :measure (cons-count lst)
    (if (atom lst)
        (equal lst nil)
      (and (ordered-s/c-p (car lst))
           (ordered-s/c-p-lst (cdr lst))))))

(define ordered-s/c-p-lst-main ((lst rp-term-listp)
                                &key (rep-ok 't))
  (if (or (atom lst)
          (and-list-p (ex-from-rp/times (car lst)))
          (binary-fnc-p (ex-from-rp/times (car lst)))
          (logbit-p (ex-from-rp/times (car lst)))
          (quotep (ex-from-rp/times (car lst))))
      (and (pp-lst-orderedp lst)
           (or rep-ok (no-rep-p lst)))
    (and (or (single-s-p (ex-from-rp/times (car lst)))
             (s-sum-ordered-listp lst))
         (or rep-ok (no-rep-p lst))
         (ordered-s/c-p-lst lst))))

(defwarrant times-p)
(defwarrant EX-FROM-RP/TIMES)
(defwarrant list-to-lst)


(defines s/c-has-times
  (define s/c-has-times (term)
    :mode :program
    (b* ((term (ex-from-rp/times term)))
      (case-match term
        (('s & pp c)
         (or (loop$ for x in (list-to-lst pp) thereis
                    (times-p x))
             (loop$ for x in (list-to-lst c) thereis
                    (times-p x))
             (s/c-has-times-lst (list-to-lst c))))
        (('c & s pp c)
         (or (loop$ for x in (list-to-lst c) thereis
                    (times-p x))
             (loop$ for x in (list-to-lst pp) thereis
                    (times-p x))
             (loop$ for x in (list-to-lst c) thereis
                    (times-p x))
             (s/c-has-times-lst (list-to-lst s))
             (s/c-has-times-lst (list-to-lst c))))
        (('s-c-res s & c)
         (and (s/c-has-times-lst (list-to-lst s))
              (s/c-has-times-lst (list-to-lst c))))
        (& nil))))
  (define s/c-has-times-lst (lst)
    (if (atom lst)
        nil
      (or (s/c-has-times (car lst))
          (s/c-has-times-lst (cdr lst)))))
  ///
  (memoize 's/c-has-times))
  

(defthm rp-term-listp-of-append-wog
  (implies (and (rp-term-listp lst1)
                (rp-term-listp lst2))
           (rp-term-listp (append-wog lst1 lst2)))
  :hints (("Goal"
           :induct (append-wog lst1 lst2)
           :do-not-induct t
           :in-theory (e/d (append-wog) ()))))

(define ex-from-pp-lst-aux ((pp-lst rp-term-listp))
  :prepwork ((local
              (in-theory (disable ex-from-rp
                                  rp-termp)))
             (local
              (defthm rp-termp-of---
                (iff (rp-termp (list '-- x))
                     (rp-termp x))
                :hints (("Goal"
                         :in-theory (e/d (rp-termp) ())))))
             (local
              (defthm rp-termp-car-when-rp-term-listp
                (implies (and (consp x)
                              (rp-term-listp x))
                         (rp-termp (car x)))
                :hints (("Goal"
                         :in-theory (e/d (rp-term-listp) ()))))))
  :returns (mv (s-lst rp-term-listp :hyp (rp-term-listp pp-lst))
               (res-pp-lst rp-term-listp :hyp (rp-term-listp pp-lst))
               (c-lst rp-term-listp :hyp (rp-term-listp pp-lst)))
  :verify-guards :after-returns
  (if (atom pp-lst)
      (mv nil nil nil)
    (b* (((mv s-lst rest-pp-lst c-lst)
          (ex-from-pp-lst-aux (cdr pp-lst)))
         (cur-orig (car pp-lst))
         ((mv coef cur) (get-pp-and-coef cur-orig))
         (x (case-match cur
              (('and-list & ('list x))
               x)
              (& cur)))
         ((unless (has-bitp-rp x))
          (mv s-lst
              (cons-with-hint cur-orig rest-pp-lst pp-lst)
              c-lst))
         (x-extracted (ex-from-rp x)))
      (cond
       ((single-s-p x-extracted)
        (mv (cons-with-times coef x s-lst)
            rest-pp-lst
            c-lst))
       ((single-c-p x-extracted)
        (mv s-lst rest-pp-lst (cons-with-times coef x c-lst)))
       ((single-s-c-res-p x-extracted)
        ;;('s-c-res s pp c)
        (b* ((s (first (cdr x-extracted)))
             (pp (second (cdr x-extracted)))
             (c (third (cdr x-extracted))))
          (mv (append-with-times coef (list-to-lst s) s-lst)
              (append-with-times coef (list-to-lst pp) rest-pp-lst)
              (append-with-times coef (list-to-lst c) c-lst))))
       (t (mv s-lst
              (cons-with-hint cur-orig
                              rest-pp-lst
                              pp-lst)
              c-lst))))))

(define ex-from-pp-lst ((pp-lst rp-term-listp))
  :returns (mv (s-lst rp-term-listp :hyp (rp-term-listp pp-lst))
               (res-pp-lst rp-term-listp :hyp (rp-term-listp pp-lst))
               (c-lst rp-term-listp :hyp (rp-term-listp pp-lst)))
  (b* (((mv s-lst res-pp-lst c-lst)
        (ex-from-pp-lst-aux pp-lst)))
    (mv (if (s-sum-ordered-listp s-lst) s-lst (s-sum-sort-lst s-lst))
        (if (pp-lst-orderedp res-pp-lst) res-pp-lst (pp-sum-sort-lst res-pp-lst))
        (if (s-sum-ordered-listp c-lst) c-lst (s-sum-sort-lst c-lst)))))
