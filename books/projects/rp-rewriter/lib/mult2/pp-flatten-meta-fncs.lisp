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
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arith-5
  :disabled t))

(define pp-list-order-aux ((x)
                           (y))
  :returns (mv (order)
               (equals booleanp))
  (cond ((or (atom x)
             (atom y))
         (mv (not (atom y)) (equal x y)))
        ((equal (car x) (car y))
         (pp-list-order-aux (cdr x) (cdr y)))
        (t
         (mv
          #|(b* (((mv order &)
          (lexorder2 (car x) (car y)))) ;
          order)||#
          (not (lexorder (car y) (car x)))
          nil))))

(define pp-list-order (x y)
  :returns (mv (order)
               (equals booleanp))
  (b* ((len-x (len x))
       (len-y (len y)))
    (if (not (equal len-x len-y))
        (if (equal len-y 2)
            (mv t nil)
          (if (equal len-x 2)
              (mv nil nil)
            (mv (> len-x len-y) nil)))
      (pp-list-order-aux x y))))

;; (defthm pp-list-order-sanity
;;   (implies (mv-nth 0 (pp-list-order x y))
;;            (not (mv-nth 0 (pp-list-order x y))))
;;   :hints (("Goal"
;;            :in-theory (e/d (pp-list-order
;;                             lexorder2-sanity)
;;                            (lexorder2)))))

(define pp-lists-p (x)
  :enabled t
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (booleanp (caar x))
         (true-listp (cdar x))
         (pp-lists-p (cdr x)))))

(local
 (in-theory (disable lexorder)))

(define pp-has-bitp-rp (term)
  :guard-hints (("goal"
                 :in-theory (e/d (is-rp) ())))
  (if (is-rp term)
      (or (equal (cadr term)
                 ''bitp)
          (pp-has-bitp-rp (caddr term)))
    nil))

(define pp-term-p (term)
  :enabled t
  :measure (cons-count term)
  :hints (("goal"
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((orig term)
       (term (ex-from-rp term)))
    (case-match term
      (('binary-and x y)
       (and (pp-term-p x)
            (pp-term-p y)))
      (('binary-or x y)
       (and (pp-term-p x)
            (pp-term-p y)))
      (('binary-xor x y)
       (and (pp-term-p x)
            (pp-term-p y)))
      (('binary-? x y z)
       (and (pp-term-p x) ;
            (pp-term-p y) ;
            (pp-term-p z)))
      (('binary-not x)
       (and (pp-term-p x)))
      (('bit-of & &) t)
      (''1 t)
      (& (pp-has-bitp-rp orig)))))

(define cut-list-by-half ((lst true-listp)
                          (size natp))
  :returns (mv (first true-listp)
               (second true-listp :hyp (true-listp lst)))
  (if (zp size)
      (mv nil lst)
    (b* (((mv rest1 rest2)
          (cut-list-by-half (cdr lst) (1- size))))
      (mv (cons (car lst) rest1)
          rest2))))

(local
 (defthm cut-list-by-half-returns-pp-lists
   (implies (and (pp-lists-p lst)
                 (< size (len lst)))
            (and (pp-lists-p (mv-nth 0 (cut-list-by-half lst size)))
                 (pp-lists-p (mv-nth 1 (cut-list-by-half lst size)))))
   :hints (("Goal"
            :in-theory (e/d (cut-list-by-half) ())))))

(local
 (in-theory (disable floor len)))

(in-theory (disable pp-list-order))

(encapsulate
  nil

  (local
   (encapsulate
     nil

     (local
      (use-arith-5 t))

     (defthm sort-measure-lemma1
       (IMPLIES
        (AND (<= 0 size)
             (integerp size)
             (<= size (len lst)))
        (equal (LEN (MV-NTH 1 (CUT-LIST-BY-HALF LST size)))
               (- (len lst) size)))
       :hints (("goal"
                :induct (CUT-LIST-BY-HALF LST size)
                :do-not-induct t
                :in-theory (e/d (len cut-list-by-half) ()))))

     (defthm sort-measure-lemma1-v2
       (IMPLIES
        (AND (<= 0 size)
             (integerp size)
             (<= size (len lst)))
        (equal (LEN (MV-NTH 0 (CUT-LIST-BY-HALF LST size)))
               size))
       :hints (("goal"
                :induct (CUT-LIST-BY-HALF LST size)
                :do-not-induct t
                :in-theory (e/d (len cut-list-by-half) ()))))

     #|(defthm sort-measure-lemma1-v3
     (IMPLIES ;
     (AND (CONSP LST) ;
     (<= 1 (len lst)) ;
     (CONSP (CDR LST)) ;
     (< size lst) ;
     (CONSP (CDDR LST))) ;
     (O< (CONS-COUNT ;
     (MV-NTH 1 (CUT-LIST-BY-HALF LST size))) ;
     (CONS-COUNT LST))) ;
     :hints (("goal" ;
     :in-theory (e/d (cons-count cut-list-by-half) ()))))||#

     (defthmd sort-measure-lemma2
       (implies (and (<= 2 (len lst)))
                (and (consp lst)
                     (consp (cdr lst))))
       :hints (("goal"
                :in-theory (e/d (len) ()))))

     (defthmd sort-measure-lemma2-v2-
       (equal  (<= 1 (len lst))
               (and (consp lst)))
       :hints (("goal"
                :in-theory (e/d (len) ()))))

     (defthm sort-measure-lemma3
       (implies (and (<= 2 (len lst)))
                (< (floor (len lst) 2) (len lst)))
       :hints (("goal"
                :in-theory (e/d (len) ()))))

     (defthm sort-measure-lemma4
       (implies (and (<= 2 (len lst)))
                (not (zp (floor (len lst) 2))))
       :hints (("goal"
                :in-theory (e/d (len) ()))))

     (defthm len-of-cut-list-by-half-second
       (implies (and (<= 2 (len lst))
                     (< size (len lst))
                     (not (zp size)))
                (equal (len (mv-nth 1
                                    (cut-list-by-half lst size)))
                       (+ (len lst) (- size))))
       :hints (("goal"
                :in-theory (e/d (cut-list-by-half len) ()))))

     (defthm len-of-cut-list-by-half-first
       (implies (and (<= 2 (len lst))
                     (< size (len lst))
                     (not (zp size)))
                (equal (len (mv-nth 0
                                    (cut-list-by-half lst size)))
                       size))
       :hints (("goal"
                :in-theory (e/d (cut-list-by-half len) ()))))

     (defthm guard-lemma1
       (implies (<= 2 (len lst))
                (<= 0 (+ (len lst) (- (floor (len lst) 2))))))

     (defthm o<-floor
       (implies (and (< 0 x)
                     (integerp x))
                (O< (FLOOR x 2) x))
       :hints (("Goal"
                :in-theory (e/d (o<) ()))))

     (defthm o<-floor-2
       (implies (and (< 1 x)
                     (integerp x))
                (O< (+ x (- (FLOOR x 2)))
                    x))
       :hints (("Goal"
                :in-theory (e/d (o<) ()))))

     (defthm floor-is-pos
       (implies (and (< 0 x)
                     (integerp x))
                (<= 0 (FLOOR x 2)))
       :hints (("Goal"
                :in-theory (e/d () ()))))

     (defthm floor-is-less-than
       (implies (and (< 0 x)
                     (integerp x))
                (<= (FLOOR x 2) x))
       :hints (("Goal"
                :in-theory (e/d () ()))))

     (defthm consp-cdr-implies
       (implies (consp (cdr lst))
                (< 1 (LEN LST)))
       :hints (("Goal"
                :in-theory (e/d (len) ()))))

     (defthm pos-len-implies
       (implies (< 0 (LEN LST))
                (consp lst))
       :hints (("Goal"
                :in-theory (e/d (len) ()))))

     (defthm less-than-2-of-len-is
       (equal (< (LEN LST) 2)
              (Not (and (consp lst)
                        (consp (cdr lst)))))
       :hints (("Goal"
                :in-theory (e/d (len) ()))))))

  (progn
    (define merge-sorted-and$-lists ((first true-listp)
                                     (second true-listp))
      :measure (+ (acl2-count first)
                  (acl2-count second))
      :returns (res true-listp
                    :hyp (and (true-listp first)
                              (true-listp second))
                    :rule-classes :type-prescription)
      (cond
       ((atom first)
        second)
       ((atom second)
        first)
       (t
        (b* ((f (car first))
             (s (car second)))
          (cond ((equal f ''1)
                 (merge-sorted-and$-lists (cdr first)
                                          second))
                ((or (equal s ''1)
                     (equal f s))
                 (merge-sorted-and$-lists first
                                          (cdr second)))
                ((lexorder f s)
                 (cons (car first) ;;hons
                       (merge-sorted-and$-lists (cdr first)
                                                second)))
                (t
                 (cons (car second) ;;hons
                       (merge-sorted-and$-lists first
                                                (cdr second)))))))))

    (define sort-and$-list ((lst true-listp)
                            (len natp))
      ;; :prepwork
      ;; ((local
      ;;   (use-arith-5 t)))
      :guard (equal (len lst) len)
      :measure (nfix (len lst))
      :hints (("Goal"
               :in-theory (e/d ()
                               (floor))))
      :verify-guards nil
      :returns (res true-listp :hyp (true-listp lst))
      (b* ((len (mbe :logic (len lst) ;; I don't want to bother adding len to
                     ;; correctness proofs.
                     :exec len)))
        (cond
         ((zp len)
          lst)
         ((= len 1)
          lst)
         ((= len 2)
          (b* ((a (car lst)) (b (cadr lst)))
            (cond
             ((equal a ''1) (cdr lst))
             ((or (equal b ''1)
                  (equal b a))
              (list a))
             ((lexorder a b) lst)
             (t (list b a)))))
         (t (b* ((first-size (floor len 2))
                 (second-size (- len first-size))
                 ((mv first-half second-half)
                  (cut-list-by-half lst first-size))
                 (first-half (sort-and$-list first-half first-size))
                 (second-half (sort-and$-list second-half second-size)))
              (merge-sorted-and$-lists first-half second-half)))))
      ///
      (local
       (use-arith-5 t))
      (verify-guards sort-and$-list
        :hints (("Goal"
                 :in-theory (e/d () (floor len)))))))

  (local
   (defthm pp-lists-p-implies-alistp
     (implies (pp-lists-p x)
              (alistp x))))

  (progn
    (define merge-sorted-pp-lists ((first pp-lists-p)
                                   (second pp-lists-p))
      :measure (+ (acl2-count first)
                  (acl2-count second))
      :returns (res pp-lists-p
                    :hyp (and (pp-lists-p first)
                              (pp-lists-p second))
                    :hints (("Goal"
                             :in-theory (e/d ()
                                             ((:REWRITE
                                               RP-TERM-LISTP-IS-TRUE-LISTP)
                                              (:DEFINITION TRUE-LISTP)
                                              (:REWRITE
                                               RP-TERMP-IMPLIES-SUBTERMS)
                                              (:DEFINITION RP-TERM-LISTP)
                                              (:REWRITE SORT-MEASURE-LEMMA2)
                                              (:DEFINITION QUOTEP)

                                              (:DEFINITION ACL2::APPLY$-BADGEP)
                                              (:LINEAR
                                               ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                                              (:DEFINITION RP-TERMP)
                                              (:DEFINITION LEN)
                                              (:DEFINITION SUBSETP-EQUAL)
                                              (:DEFINITION MEMBER-EQUAL)
                                              (:REWRITE DEFAULT-CDR)
                                              (:REWRITE
                                               RP-TERMP-IMPLIES-CDR-LISTP)
                                              (:REWRITE
                                               ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                                              (:REWRITE IS-IF-RP-TERMP)
                                              (:REWRITE DEFAULT-CAR)
                                              (:REWRITE RP-TERMP-CADR)
                                              (:REWRITE DEFAULT-+-2))))))
      :verify-guards nil
      (cond
       ((atom first) second)
       ((atom second) first)
       (t (b* ((sign1 (caar first))
               (term1 (cdar first))
               (sign2 (caar second))
               (term2 (cdar second)))
            (cond
             ((and (not (equal sign1 sign2))
                   (equal term1 term2))
              (merge-sorted-pp-lists (cdr first) (cdr second)))
             ((b* (((mv order &) (pp-list-order term1 term2))) order)
              (acons sign1
                     term1
                     (merge-sorted-pp-lists (cdr first) second)))
             (t
              (acons sign2
                     term2
                     (merge-sorted-pp-lists first (cdr second))))))))
      ///
      (verify-guards merge-sorted-pp-lists
        :hints (("Goal"
                 :in-theory (e/d () (not
                                     (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                                     (:DEFINITION TRUE-LISTP)
                                     (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                                     (:DEFINITION RP-TERM-LISTP)
                                     (:DEFINITION QUOTEP)
                                     (:DEFINITION ACL2::APPLY$-BADGEP)
                                     (:REWRITE SORT-MEASURE-LEMMA2)
                                     (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)

                                     (:DEFINITION LEN)
                                     (:DEFINITION SUBSETP-EQUAL)
                                     (:DEFINITION RP-TERMP)
                                     (:DEFINITION MEMBER-EQUAL)
                                     (:REWRITE DEFAULT-CDR)
                                     (:REWRITE
                                      ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                                     (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                                     (:REWRITE IS-IF-RP-TERMP)
                                     (:DEFINITION ALISTP)
                                     (:REWRITE DEFAULT-CAR)))))))

    (define sort-pp-lists ((lst pp-lists-p)
                           (len natp))
      :guard (equal (len lst) len)
      :measure (nfix (len lst))
      :hints (("Goal"
               :in-theory (e/d (measure-lemmas
                                sort-measure-lemma2-v2-
                                sort-measure-lemma2)
                               (floor))))
      :verify-guards nil
      :returns (res pp-lists-p :hyp (pp-lists-p lst)
                    :hints (("Goal"
                             :in-theory (e/d () (floor)))))
      (b* ((len (mbe :logic (len lst) ;; I don't want to bother adding len to
                     ;; correctness proofs.
                     :exec len)))
        (cond
         ((zp len)
          lst)
         ((= len 1)
          lst
          #|(acons (caar lst)
          (sort-and$-list (cdar lst) (len (cdar lst)))

          nil)||#)
         ((= len 2)
          (b* ((f (car lst))
               (s (cadr lst))
               (sign1 (car f))
               (term1 (cdr f))
               (sign2 (car s))
               (term2 (cdr s)))
            (cond
             ((and (not (equal sign1 sign2))
                   (equal term1 term2))
              nil)

             ((b* (((mv order &) (pp-list-order term1 term2))) order)
              lst)
             (t
              `(,(cadr lst)
                ,(car lst))))))
         (t (b* ((first-size (floor len 2))
                 (second-size (- len first-size))
                 ((mv first-half second-half)
                  (cut-list-by-half lst first-size))
                 (first-half (sort-pp-lists first-half first-size))
                 (second-half (sort-pp-lists second-half second-size)))
              (merge-sorted-pp-lists first-half  second-half)))))
      ///
      (verify-guards sort-pp-lists
        :hints (("Goal"
                 :in-theory (e/d () (floor len))))))))

#|(sort-pp-lists '((t b x y a)
                 (nil b x a)
                 (nil b y a)
                 (nil a)
                 (t b y)
                 (t b x)
                 (nil b x y)
                 (t a))
               8)||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FLATTEN FUNCTIONS

(define and$-pp-lists-aux ((cur true-listp)
                           (lst2 pp-lists-p)
                           (acc pp-lists-p)
                           (sign booleanp))
  :returns (res-acc pp-lists-p :hyp (and (true-listp cur)
                                         (pp-lists-p lst2)
                                         (pp-lists-p acc)
                                         (booleanp sign))
                    :rule-classes :type-prescription)
  (if (atom lst2)
      acc
    (cons (cons (xor sign (caar lst2))
                (merge-sorted-and$-lists cur (cdar lst2))
;(append cur (cdar lst2)) ;; HERE!! replace with merge-sorted
                ;; and lists.
                )
          (and$-pp-lists-aux cur (cdr lst2) acc sign))))

(define and$-pp-lists ((lst1 pp-lists-p)
                       (lst2 pp-lists-p)
                       (acc pp-lists-p)
                       (sign booleanp))
  :returns (res-acc pp-lists-p :hyp (and (pp-lists-p lst1)
                                         (pp-lists-p lst2)
                                         (pp-lists-p acc)
                                         (booleanp sign))
                    :rule-classes :type-prescription)
  (if (atom lst1)
      acc
    (b* ((acc (and$-pp-lists (cdr lst1) lst2 acc sign)))
      (and$-pp-lists-aux (cdar lst1) lst2 acc (xor sign (caar lst1))))))

(local
 (defthm append-of-pp-list-p
   (implies (and (pp-lists-p x)
                 (pp-lists-p y))
            (pp-lists-p (append x y)))
   :rule-classes :type-prescription))

(local
 (in-theory (disable ex-from-rp)))

(local
 (defthmd pp-lists-p-implies-true-listp
   (implies (pp-lists-p x)
            (true-listp x))))

(local
 ;; auxilary function used only in the local lemmas for correctness proofs.
 (define apply-sign-to-pp-lists (lst sign)
   :returns (res pp-lists-p
                 :hyp (pp-lists-p lst))
   :verify-guards nil
   (if (atom lst)
       nil
     (acons (xor sign (caar lst))
            (cdar lst)
            (apply-sign-to-pp-lists (cdr lst) sign)))))

(define pp-term-to-pp-lists ((term pp-term-p)
                             (sign booleanp))
  :measure (cons-count term)
  :hints (("goal"
           :in-theory (e/d (measure-lemmas) ())))
  :returns (result pp-lists-p
                   :hyp (booleanp sign)
                   :rule-classes :type-prescription)
  :verify-guards nil
  (b* ((orig term)
       (term (ex-from-rp term)))
    (case-match term
      (('binary-and x y)
       (b* ((lst1 (pp-term-to-pp-lists x nil))
            (lst2 (pp-term-to-pp-lists y nil))
            (anded (and$-pp-lists lst1 lst2 nil sign))
            (anded (sort-pp-lists anded (len anded))))
         anded))
      (('binary-or x y)
       (b* ((lst1 (pp-term-to-pp-lists x sign))
            (lst2 (pp-term-to-pp-lists y sign))
            (x (merge-sorted-pp-lists lst1  lst2 ))
            (y (and$-pp-lists lst1 lst2 nil (not sign)))
            (y (sort-pp-lists y (len y))))
         (merge-sorted-pp-lists x  y )))
      (('binary-xor x y)
       (b* ((lst1 (pp-term-to-pp-lists x sign))
            (lst2 (pp-term-to-pp-lists y sign))
            (acc (merge-sorted-pp-lists lst1  lst2 ))
            (minus-x-and-y (and$-pp-lists lst1 lst2 nil (not sign)))
            (minus-x-and-y (sort-pp-lists minus-x-and-y (len minus-x-and-y))))
         (merge-sorted-pp-lists
          acc
          (merge-sorted-pp-lists  minus-x-and-y  minus-x-and-y ))))
      (('binary-? test x y)
       (b* ((test-lst (pp-term-to-pp-lists test sign))

            (x-lst (pp-term-to-pp-lists x sign))
            (x-and-test (and$-pp-lists test-lst x-lst nil sign))
            (x-and-test (sort-pp-lists x-and-test (len x-and-test)))

            (y-lst (pp-term-to-pp-lists y sign))
            (--y-and-test (and$-pp-lists test-lst y-lst nil (not sign)))
            (--y-and-test (sort-pp-lists --y-and-test (len --y-and-test))))
         (merge-sorted-pp-lists x-and-test
                                (merge-sorted-pp-lists --y-and-test  y-lst))))
      (('binary-not x)
       (b* ((lst1 (pp-term-to-pp-lists x (not sign))))
         (merge-sorted-pp-lists (list (cons sign (list ''1)))
                                lst1)))
      (('bit-of & &)
       (list (cons sign (list term))))
      #|(''0
      (list (cons sign (list term))))||#
      (''1
       (list (cons sign (list term))))
      (&
       (if (pp-has-bitp-rp orig)
           (list (cons sign (list orig)))
         (progn$
          (cw "unexpected term ~p0 ~%" orig)
          (hard-error 'pp-term-to-pp-lists
                      "unexpected term ~p0 ~%"
                      (list (cons #\0 orig))))))))
  ///

  (verify-guards pp-term-to-pp-lists
    :hints (("goal"
             :in-theory (e/d () ())))))

;; (pp-term-to-pp-lists `(binary-not (binary-or (bit-of a 1) (bit-of b 1))) nil)

;; (pp-term-to-pp-lists `(binary-or (binary-and b (binary-or x y)) a) t)
;; =
;; (+ xb yb - xyb + a -axb -ayb - axyb)

;; (pp-term-to-pp-lists '(binary-or x y) t)

;; (pp-term-to-pp-lists `(binary-or (binary-and b (binary-or x y)) (binary-not a)) nil)
;; =
;; -xby by bx 1 -a axb -xb aby -by -axby xby

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CONVERT PP-LISTS TO TERMS

;; (define pp-lists-to-term-and-list ((cur true-listp))
;;   :returns (res rp-term-listp
;;                 :hyp
;;   (cond ((atom cur)
;;          nil)
;;         (t
;;          (cons (car cur)
;;                (pp-lists-to-term-and-list (cdr cur))))))

(define pp-lists-to-term-pp-lst ((lst pp-lists-p))
  (cond ((atom lst)
         nil)
        (t
         (b* ((cur (cdar lst))
              (cur (cond ((atom cur) ''1)
                         ((atom (cdr cur)) (car cur))
                         ((atom (cddr cur)) `(binary-and . ,cur))
                         (t `(and-list (list . ,cur))))))
           (if (caar lst)
               (cons `(-- ,cur)
                     (pp-lists-to-term-pp-lst (cdr lst)))
             (cons cur
                   (pp-lists-to-term-pp-lst (cdr lst))))))))

(define pp-flatten ((term pp-term-p)
                    (sign booleanp))
  (case-match term
    (('binary-and ('bit-of & &) ('bit-of & &))
     (if (lexorder (cadr term) (caddr term))
         `(list ,(if sign `(-- ,term) term))
       `(list
         ,(if sign
              `(-- (binary-and ,(caddr term) ,(cadr term)))
            `(binary-and ,(caddr term) ,(cadr term))))))
    (&
     (b* ((pp-lists (pp-term-to-pp-lists term sign))
          (result (pp-lists-to-term-pp-lst pp-lists))
          (result (If pp-lists (cons 'list result) ''nil)))
       result))))

(progn
  (define sort-sum-meta-aux (term)
    :returns (mv valid pp-lists)
    (case-match term
      (('binary-sum x rest)
       (case-match x
         (('binary-and a b)
          (b* ((a-orig a)
               (b-orig b)
               (a (ex-from-rp a))
               (b (ex-from-rp b))
               ((unless (and (or (case-match a (('bit-of & &) t))
                                 (case-match a-orig (('rp ''bitp &) t)))
                             (or (case-match b (('bit-of & &) t) )
                                 (case-match b-orig (('rp ''bitp &) t)))))
                (mv nil nil))
               ((mv rest-valid rest)
                (sort-sum-meta-aux rest))
               ((unless rest-valid)
                (mv nil nil)))
            (mv t
                (cons (cons nil (sort-and$-list (cdr x) 2))
                      rest))))
         (''0
          (sort-sum-meta-aux rest))
         (& (mv nil nil))))
      (('binary-and a b)
       (b* ((a-orig a)
            (b-orig b)
            (a (ex-from-rp a))
            (b (ex-from-rp b))
            ((unless (and (or (case-match a (('bit-of & &) t))
                              (case-match a-orig (('rp ''bitp &) t)))
                          (or (case-match b (('bit-of & &) t) )
                              (case-match b-orig (('rp ''bitp &) t)))))
             (mv nil nil)))
         (mv t
             (cons (cons nil (sort-and$-list (cdr term) 2))
                   nil))))
      (''0
       (mv t nil))
      (&
       (mv nil nil)))
    ///
    (acl2::defret pp-lists-p-of-<fn>
                  (implies valid
                           (pp-lists-p pp-lists))))

  (define sort-sum-meta (term)
    :returns (mv result
                 (dont-rw dont-rw-syntaxp))
    (case-match term
      (('sort-sum x)
       (b* (((mv valid pp-lists)
             (sort-sum-meta-aux x))
            ((unless valid)
             (progn$ (cw "sort-sum-meta got an unexpected term ~p0 ~%"
                         term)
                     (hard-error 'sort-sum-meta "" nil)
                     (mv term t)))
            (pp-lists (sort-pp-lists pp-lists (len pp-lists)))
            (result (pp-lists-to-term-pp-lst pp-lists))
            (result (If pp-lists `(sum-list (list . ,result)) ''0)))
         (mv result t)))
      (&
       (progn$ (cw "sort-sum-meta got an unexpected term ~p0 ~%"
                   term)
               (hard-error 'sort-sum-meta "" nil)
               (mv term t))))))

(local
 (in-theory (disable floor len)))

(local
 (encapsulate
   nil

   (local
    (use-arith-5 t))

   (defthm floor-len-is-less-than-len
     (implies (and (natp len))
              (<= (floor len 2) len)))

   (defthm natp-len
     (natp (len x)))

   (defthmd dummy-arith-lemma-1
     (implies (NOT (CONSP LST))
              (equal (len lst) 0)))

   (defthmd dummy-arith-lemma-2
     (implies (and (<= SIZE (LEN LST))
                   (consp lst))
              (equal (< (LEN (CDR LST)) (+ -1 SIZE)) nil)))))

(local
 (defthm rp-term-listp-cut-list-by-half
   (implies (and (rp-term-listp lst)
                 (<= size (len lst)))
            (and (rp-term-listp (mv-nth 0 (cut-list-by-half lst size)))
                 (rp-term-listp (mv-nth 1 (cut-list-by-half lst size)))))
   :hints (("Goal"
            :do-not-induct t
            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half) ())))))

(local
 (defthm rp-term-list-listp-cut-list-by-half
   (implies (and (rp-term-list-listp lst)
                 (<= size (len lst)))
            (and (rp-term-list-listp (mv-nth 0 (cut-list-by-half lst size)))
                 (rp-term-list-listp (mv-nth 1 (cut-list-by-half lst size)))))
   :hints (("Goal"
            :do-not-induct t
            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half) ())))))

(local
 (defthm rp-term-list-listp-cut-list-by-half-2
   (implies (and (rp-term-list-listp (strip-cdrs lst))
                 (<= size (len lst)))
            (and (rp-term-list-listp (strip-cdrs (mv-nth 0 (cut-list-by-half lst size))))
                 (rp-term-list-listp (strip-cdrs (mv-nth 1 (cut-list-by-half lst size))))))
   :hints (("Goal"
            :do-not-induct t
            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half
                             dummy-arith-lemma-1) ())))))

(local
 (defthm rp-term-listp-merge-sorted-and$-lists
   (implies (and (rp-term-listp lst1)
                 (rp-term-listp lst2))
            (rp-term-listp (merge-sorted-and$-lists lst1 lst2)))
   :hints (("Goal"
            :induct (merge-sorted-and$-lists lst1 lst2)
            :in-theory (e/d (merge-sorted-and$-lists) ())))))

(local
 (defthm rp-term-listp-sort-and$-list
   (implies (rp-term-listp lst)
            (rp-term-listp (sort-and$-list lst len)))
   :hints (("Goal"
            :in-theory (e/d (sort-and$-list) ())))))

(local
 (defthm rp-term-list-listp-merge-sorted-pp-lists
   (implies (and (rp-term-list-listp (strip-cdrs lst1))
                 (rp-term-list-listp (strip-cdrs lst2)))
            (rp-term-list-listp
             (strip-cdrs
              (merge-sorted-pp-lists lst1 lst2))))
   :hints (("Goal"
            :induct (merge-sorted-pp-lists lst1 lst2)
            :in-theory (e/d (merge-sorted-pp-lists) ())))))

(local
 (defthm rp-term-list-listp-sort-pp-lists
   (implies (rp-term-list-listp (strip-cdrs lst1))
            (rp-term-list-listp (strip-cdrs
                                 (sort-pp-lists lst1 len))))
   :hints (("Goal"
;:induct (sort-pp-lists lst1 len)
;:do-not-induct t
            :in-theory (e/d (sort-pp-lists) ())))))

(local
 (defthm rp-term-list-listp-and$-pp-lists-aux
   (implies (and (rp-term-listp cur)
                 (rp-term-list-listp (strip-cdrs lst2))
                 (rp-term-list-listp (strip-cdrs acc)))
            (rp-term-list-listp (strip-cdrs (and$-pp-lists-aux cur lst2 acc
                                                               sign))))
   :hints (("Goal"
            :in-theory (e/d (and$-pp-lists-aux) ())))))

(local
 (defthm rp-term-list-listp-and$-pp-lists
   (implies (and (rp-term-list-listp (strip-cdrs lst1))
                 (rp-term-list-listp (strip-cdrs lst2))
                 (rp-term-list-listp (strip-cdrs acc)))
            (rp-term-list-listp (strip-cdrs (and$-pp-lists lst1 lst2 acc
                                                           sign))))
   :hints (("Goal"
            :in-theory (e/d (and$-pp-lists) ())))))

(Local
 (defthm rp-term-list-listp-pp-term-to-pp-lists
   (implies (rp-termp term)
            (rp-term-list-listp (strip-cdrs (pp-term-to-pp-lists term sign))))
   :hints (("Goal"
            :in-theory (e/d (pp-term-to-pp-lists) ())))))

(local
 (defthm rp-termp-of-pp-lists-to-term-pp-lst
   (implies (rp-term-list-listp (strip-cdrs lst))
            (rp-term-listp (pp-lists-to-term-pp-lst lst)))
   :hints (("Goal"
            :in-theory (e/d (pp-lists-to-term-pp-lst) ())))))

(defthm rp-termp-of-pp-flatten
  (implies (rp-termp term)
           (rp-termp (pp-flatten term sign)))
  :hints (("Goal"
           :in-theory (e/d (pp-flatten) ()))))

(defthm rp-term-list-listp-strip-cdrs-sort-sum-meta-aux
  (implies (rp-termp term)
           (rp-term-list-listp (strip-cdrs (mv-nth 1 (sort-sum-meta-aux
                                                      term)))))
  :hints (("goal"
           :in-theory (e/d (sort-sum-meta-aux)
                           ((:definition acl2::apply$-badgep)
                            (:linear acl2::apply$-badgep-properties . 1)
                            (:rewrite rp-termp-implies-cdr-listp)
                            (:definition member-equal)
                            (:rewrite rp-term-listp-is-true-listp)
                            (:linear acl2::apply$-badgep-properties . 2)
                            (:definition true-listp)
                            (:rewrite is-if-rp-termp)
                            (:rewrite acl2::o-p-o-infp-car)
                            (:rewrite is-rp-pseudo-termp)
                            (:rewrite atom-rp-termp-is-symbolp)
                            falist-consistent
                            (:definition subsetp-equal))))))

(defthm rp-termp-of-sort-sum-meta.result
  (implies (rp-termp term)
           (b* (((mv ?result ?dont-rw)
                 (sort-sum-meta term)))
             (rp-termp result)))
  :rule-classes :rewrite
  :hints (("Goal"
           :in-theory (e/d (sort-sum-meta)
                           ()))))

;; valid-sc:

(local
 (defun valid-sc-subterms-lst (lst a)
   (if (atom lst)
       (eq lst nil)
     (and (valid-sc-subterms (car lst) a)
          (valid-sc-subterms-lst (cdr lst) a)))))

(local
 (defthm valid-sc-subterms-cut-list-by-half
   (implies (and (valid-sc-subterms lst a)
                 (<= size (len lst)))
            (and (valid-sc-subterms (mv-nth 0 (cut-list-by-half lst size)) a)
                 (valid-sc-subterms (mv-nth 1 (cut-list-by-half lst size)) a)))
   :hints (("Goal"
            ;;          :do-not-induct t
            ;;            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half
                             dummy-arith-lemma-2) ())))))

(local
 (defthm valid-sc-subterms-lst-cut-list-by-half
   (implies (and (valid-sc-subterms-lst lst a)
                 (<= size (len lst)))
            (and (valid-sc-subterms-lst (mv-nth 0 (cut-list-by-half lst size)) a)
                 (valid-sc-subterms-lst (mv-nth 1 (cut-list-by-half lst size)) a)))
   :hints (("Goal"
            :do-not-induct t
            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half) ())))))

(local
 (defthm valid-sc-subterms-lst-cut-list-by-half-2
   (implies (and (valid-sc-subterms-lst (strip-cdrs lst) a)
                 (<= size (len lst)))
            (and (valid-sc-subterms-lst
                  (strip-cdrs (mv-nth 0 (cut-list-by-half lst size)))
                  a)
                 (valid-sc-subterms-lst
                  (strip-cdrs (mv-nth 1 (cut-list-by-half lst size)))
                  a)))
   :hints (("Goal"
            :do-not-induct t
            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half
                             dummy-arith-lemma-1) ())))))

(local
 (defthm valid-sc-subterms-merge-sorted-and$-lists
   (implies (and (valid-sc-subterms lst1 a)
                 (valid-sc-subterms lst2 a))
            (valid-sc-subterms (merge-sorted-and$-lists lst1 lst2) a))
   :hints (("Goal"
            :induct (merge-sorted-and$-lists lst1 lst2)
            :in-theory (e/d (merge-sorted-and$-lists) ())))))

(local
 (defthm valid-sc-subterms-sort-and$-list
   (implies (valid-sc-subterms lst a)
            (valid-sc-subterms (sort-and$-list lst len) a))
   :hints (("Goal"
            :in-theory (e/d (sort-and$-list) ())))))

(local
 (defthm valid-sc-subterms-lst-merge-sorted-pp-lists
   (implies (and (valid-sc-subterms-lst (strip-cdrs lst1) a)
                 (valid-sc-subterms-lst (strip-cdrs lst2) a))
            (valid-sc-subterms-lst
             (strip-cdrs
              (merge-sorted-pp-lists lst1 lst2))
             a))
   :hints (("Goal"
            :induct (merge-sorted-pp-lists lst1 lst2)
            :in-theory (e/d (merge-sorted-pp-lists) ())))))

(local
 (defthm valid-sc-subterms-lst-sort-pp-lists
   (implies (valid-sc-subterms-lst (strip-cdrs lst1) a)
            (valid-sc-subterms-lst (strip-cdrs
                                    (sort-pp-lists lst1 len))
                                   a))
   :hints (("Goal"
            ;;:induct (sort-pp-lists lst1 len)
            ;;:do-not-induct t
            :in-theory (e/d (sort-pp-lists) ())))))

(local
 (defthm valid-sc-subterms-lst-and$-pp-lists-aux
   (implies (and (valid-sc-subterms cur a)
                 (valid-sc-subterms-lst (strip-cdrs lst2) a)
                 (valid-sc-subterms-lst (strip-cdrs acc) a))
            (valid-sc-subterms-lst (strip-cdrs (and$-pp-lists-aux cur lst2 acc
                                                                  sign))
                                   a))
   :hints (("Goal"
            :in-theory (e/d (and$-pp-lists-aux) ())))))

(local
 (defthm valid-sc-subterms-lst-and$-pp-lists
   (implies (and (valid-sc-subterms-lst (strip-cdrs lst1) a)
                 (valid-sc-subterms-lst (strip-cdrs lst2) a)
                 (valid-sc-subterms-lst (strip-cdrs acc) a))
            (valid-sc-subterms-lst (strip-cdrs (and$-pp-lists lst1 lst2 acc
                                                              sign))
                                   a))
   :hints (("Goal"
            :in-theory (e/d (and$-pp-lists) ())))))

(Local
 (defthm valid-sc-subterms-lst-pp-term-to-pp-lists
   (implies (valid-sc term a)
            (valid-sc-subterms-lst (strip-cdrs (pp-term-to-pp-lists term sign))
                                   a))
   :hints (("Goal"
            :in-theory (e/d (pp-term-to-pp-lists) ())))))

(local
 (defthm valid-sc-pp-lists-to-term-p+
   (implies (valid-sc-subterms-lst (strip-cdrs lst) a)
            (valid-sc-subterms (pp-lists-to-term-pp-lst lst) a))
   :hints (("Goal"
            :in-theory (e/d (pp-lists-to-term-pp-lst
                             is-if
                             is-rp) ())))))

(defthm pp-flatten-returns-valid-sc
  (implies (valid-sc term a)
           (valid-sc (pp-flatten term sign) a))
  :hints (("Goal"
           :in-theory (e/d (pp-flatten
                            is-if is-rp) ()))))

(local
 (defthm sort-sum-meta-aux-returns-valid-sc
   (implies (valid-sc term a)
            (valid-sc-subterms-lst
             (strip-cdrs (mv-nth 1 (sort-sum-meta-aux term)))
             a))
   :hints (("goal"
            :in-theory (e/d (sort-sum-meta-aux
                             )
                            ((:definition valid-sc)
                             (:definition rp-termp)
                             (:rewrite car-of-ex-from-rp-is-not-rp)
                             (:definition rp-term-listp)
                             (:rewrite not-include-rp-means-valid-sc)
                             (:definition include-fnc)
                             (:rewrite rp-termp-implies-subterms)
                             (:definition quotep)))))))

(defthm sort-sum-meta-returns-valid-sc
  (implies (valid-sc term a)
           (valid-sc (mv-nth 0 (sort-sum-meta term)) a))
  :hints (("Goal"
           :in-theory (e/d (sort-sum-meta
                            is-rp
                            is-if) ()))))
