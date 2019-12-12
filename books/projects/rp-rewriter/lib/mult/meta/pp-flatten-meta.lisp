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

(include-book "../binary-fn-defs")

(include-book "../mult-defs")

;(include-book "../macros")

(include-book "pp-order-fncs")

;;(include-book "pp-order-meta")

(include-book "centaur/svl/portcullis" :dir :system)

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
      #|(''0 t)||#
      (''1 t)
      (& (pp-has-bitp-rp orig)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SORT PP-LISTS

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
 (in-theory (disable floor
                     len)))

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
                 (cons (car first)
                       (merge-sorted-and$-lists (cdr first)
                                                second)))
                (t
                 (cons (car second)
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
             ((pp-list-order term1 term2)
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

             ((pp-list-order term1 term2)
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

(define pp-lists-to-term-and$ ((cur true-listp))
  (cond ((atom cur)
         ''1)
        ((atom (cdr cur))
         (car cur))
        (t
         `(binary-and ,(car cur)
                      ,(pp-lists-to-term-and$ (cdr cur))))))

(define pp-lists-to-term-p+ ((lst pp-lists-p))
  (cond ((atom lst)
         ''0)
        ((atom (cdr lst))
         (b* ((cur (pp-lists-to-term-and$ (cdar lst))))
           (if (caar lst)
               `(-- ,cur)
             cur)))
        (t
         (b* ((cur (pp-lists-to-term-and$ (cdar lst))))
           (if (caar lst)
               `(p+ (-- ,cur) ,(pp-lists-to-term-p+ (cdr lst)))
             `(p+ ,cur ,(pp-lists-to-term-p+ (cdr lst))))))))

;; (pp-lists-to-term '((t b x y a)
;;                           (nil b x a)
;;                           (nil b y a)
;;                           (t b y)
;;                           (t b x)
;;                           (nil b x y)
;;                           (t a)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|(define pp-lists-has-anded-1 ((pp-lists pp-lists-p))
  (if (atom pp-lists)
      nil
    (or (member-equal ''1 (cdar pp-lists))
        (member-equal '1 (cdar pp-lists))
        (pp-lists-has-anded-1 (cdr pp-lists)))))||#

(define flatten-pp-main (term)
  (case-match term
    (('binary-and ('bit-of & &) ('bit-of & &))
     (if (lexorder (cadr term)
                   (caddr term))
         term
       `(binary-and ,(caddr term) ,(cadr term))))
    (('binary-and ('[] & &) ('[] & &))
     (if (lexorder (cadr term)
                   (caddr term))
         term
       `(binary-and ,(caddr term) ,(cadr term))))
    (('-- x)
     (if (pp-term-p x)
         (b* ((pp-lists (pp-term-to-pp-lists x t))
              #|(pp-lists (sort-pp-lists pp-lists
              (len pp-lists)))||#
              #|(- (if (pp-lists-has-anded-1 pp-lists)
              (cw "Bad pp-lists! orig: ~p0 sorted: ~p1 ~%"
              orig pp-lists)
              nil))||#
              (result (pp-lists-to-term-p+ pp-lists)))
           result)
       (progn$ (cw "Error! The term ~p0 does not satisfy pp-term-p ~%"
                   term)
               (hard-error 'flatten-pp-main
                           ""
                           nil)
               term)))
    (&
     (if (pp-term-p term)
         (b* ((pp-lists (pp-term-to-pp-lists term nil))
              #|(pp-lists (sort-pp-lists pp-lists
              (len pp-lists)))||#
              (result (pp-lists-to-term-p+ pp-lists)))
           result)
       (progn$ (cw "Error! The term ~p0 does not satisfy pp-term-p ~%"
                   term)
               (hard-error 'flatten-pp-main
                           ""
                           nil)
               term)))))

(encapsulate
  nil

  (local
   (in-theory (disable lexorder
                       pp-or$-order
                       ex-from-rp
                       ex-from-rp-loose
                       pp-list-order)))

  (def-formula-checks
    pp-flatten-formula-checks
    (merge-pp-and
     flatten-pp-main
     merge-pp-or
     binary-not
     binary-and
     bitp
     binary-or
     binary-?
     bit-of
     binary-xor
     pp-term-to-pp-lists
     p+
     --
     pp-lists-to-term-p+
     sort-pp-lists)))

(local
 (defthmd rp-evl-of-ex-from-rp-reverse
   (implies (syntaxp (atom x))
            (equal (rp-evlt x a)
                   (rp-evlt (ex-from-rp x) a)))
   :hints (("goal"
            :in-theory (e/d (ex-from-rp
                             is-rp) ())))))

(local
 (defthm when-ex-from-rp-is-1
   (implies (equal (ex-from-rp term) ''1)
            (equal (rp-evlt term a)
                   1))
   :hints (("goal"
            :in-theory (e/d (ex-from-rp is-rp)
                            (ex-from-rp-lemma1))))))

(local
 (defthm when-ex-from-rp-is-0
   (implies (equal (ex-from-rp term) ''0)
            (equal (rp-evlt term a)
                   0))
   :hints (("goal"
            :in-theory (e/d (ex-from-rp is-rp)
                            (ex-from-rp-lemma1))))))

;;;;;;;;;;;;;;;;
;; EVAL LEMMAS

(progn
  (local
   (defthmd eval-of-binary-not-1
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          'binary-not)
                   (consp term)
                   (consp (cdr term))
                   (not (cddr term)))
              (equal (rp-evlt term a)
                     (binary-not (rp-evlt (cadr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of-binary-not
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          'binary-not)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (not (cddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (binary-not (rp-evlt (cadr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of-binary-not-1)
                              (evl-of-extract-from-rp)))))))

(progn
  (local
   (defthmd eval-of---1
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          '--)
                   (consp term)
                   (consp (cdr term))
                   (not (cddr term)))
              (equal (rp-evlt term a)
                     (-- (rp-evlt (cadr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of----
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          '--)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (not (cddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (-- (rp-evlt (cadr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of---1)
                              (evl-of-extract-from-rp)))))))

(progn
  (local
   (defthmd eval-of-bit-of-1
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          'bit-of)
                   (consp term)
                   (consp (cdr term))
                   (consp (cddr term))
                   (not (cdddr term)))
              (equal (rp-evlt term a)
                     (bit-of (rp-evlt (cadr term) a)
                             (rp-evlt (caddr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of-bit-of
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          'bit-of)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (consp (cddr (ex-from-rp term)))
                   (not (cdddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (bit-of (rp-evlt (cadr (ex-from-rp term)) a)
                             (rp-evlt (caddr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of-bit-of-1)
                              (evl-of-extract-from-rp)))))))

(progn
  (local
   (defthmd eval-of-binary-?-1
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          'binary-?)
                   (consp term)
                   (consp (cdr term))
                   (consp (cddr term))
                   (consp (cdddr term))
                   (not (cddddr term)))
              (equal (rp-evlt term a)
                     (binary-? (rp-evlt (cadr term) a)
                               (rp-evlt (caddr term) a)
                               (rp-evlt (cadddr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of-binary-?
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          'binary-?)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (consp (cddr (ex-from-rp term)))
                   (consp (cdddr (ex-from-rp term)))
                   (not (cddddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (binary-? (rp-evlt (cadr (ex-from-rp term)) a)
                               (rp-evlt (caddr (ex-from-rp term)) a)
                               (rp-evlt (cadddr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of-binary-?-1)
                              (evl-of-extract-from-rp)))))))

(progn
  (local
   (defthmd eval-of-binary-or-1
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          'binary-or)
                   (consp term)
                   (consp (cdr term))
                   (consp (cddr term))
                   (not (cdddr term)))
              (equal (rp-evlt term a)
                     (binary-or (rp-evlt (cadr term) a)
                                (rp-evlt (caddr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of-binary-or
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          'binary-or)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (consp (cddr (ex-from-rp term)))
                   (not (cdddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (binary-or (rp-evlt (cadr (ex-from-rp term)) a)
                                (rp-evlt (caddr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of-binary-or-1)
                              (evl-of-extract-from-rp)))))))

(progn
  (local
   (defthmd eval-of-binary-xor-1
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          'binary-xor)
                   (consp term)
                   (consp (cdr term))
                   (consp (cddr term))
                   (not (cdddr term)))
              (equal (rp-evlt term a)
                     (binary-xor (rp-evlt (cadr term) a)
                                 (rp-evlt (caddr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of-binary-xor
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          'binary-xor)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (consp (cddr (ex-from-rp term)))
                   (not (cdddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (binary-xor (rp-evlt (cadr (ex-from-rp term)) a)
                                 (rp-evlt (caddr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of-binary-xor-1)
                              (evl-of-extract-from-rp)))))))

(progn
  (local
   (defthmd eval-of-binary-and-1
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          'binary-and)
                   (consp term)
                   (consp (cdr term))
                   (consp (cddr term))
                   (not (cdddr term)))
              (equal (rp-evlt term a)
                     (binary-and (rp-evlt (cadr term) a)
                                 (rp-evlt (caddr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of-binary-and
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          'binary-and)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (consp (cddr (ex-from-rp term)))
                   (not (cdddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (binary-and (rp-evlt (cadr (ex-from-rp term)) a)
                                 (rp-evlt (caddr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of-binary-and-1)
                              (evl-of-extract-from-rp)))))))

(local
 (defthmd not$-to-pp-sum
   (implies (bitp a)
            (equal (not$ a)
                   (pp-sum 1 (-- a))))))

(progn
  (local
   (defthmd pp-has-bitp-rp-implies-lemma
     (implies (and (pp-has-bitp-rp term)
                   (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (eval-and-all (context-from-rp term nil) a))
              (bitp (rp-evlt term a)))
     :hints (("goal"
              :induct (pp-has-bitp-rp term)
              :do-not-induct t
              :in-theory (e/d (pp-has-bitp-rp
                               is-rp
                               is-if
                               eval-and-all
                               context-from-rp)
                              (bitp
                               ex-from-rp-lemma1
                               valid-sc))))))

  (local
   (defthm pp-has-bitp-rp-implies
     (implies (and (pp-has-bitp-rp term)
                   (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (valid-sc term a))
              (bitp (rp-evlt term a)))
     :hints (("goal"
              :induct (pp-has-bitp-rp term)
              :expand ((valid-sc term a))
              :do-not-induct t
              :in-theory (e/d (pp-has-bitp-rp
                               pp-has-bitp-rp-implies-lemma
                               is-rp
                               is-if)
                              (bitp
                               rp-trans
                               ex-from-rp-lemma1
                               context-from-rp
                               valid-sc-ex-from-rp-2
                               not-include-rp
                               rp-evl-of-rp-call
                               valid-sc
                               eval-and-all)))))))

(local
 (defthm pp-term-p-is-bitp
   (implies (and (pp-term-p term)
                 (pp-flatten-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (valid-sc term a))
            (bitp (rp-evlt term a)))
   :hints (("goal"
            :in-theory (e/d ()
                            (valid-sc
                             bitp
                             rp-trans
                             p+
                             not$-to-pp-sum))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ARITH LEMMAS

(local
 (in-theory (disable rp-evlt-of-ex-from-rp)))

(local
 (encapsulate
   nil
   (local
    (use-arith-5 t))
   (defthm floor-of-two-is-less
     (implies (and (> x 2)
                   (integerp x))
              (< (floor x 2)
                 x)))

   (defthm floor-of-len-is-less-than-lst
     (implies (and (consp lst)
                   (consp (cdr lst)))
              (< (FLOOR (LEN LST) 2) (LEN LST)))
     :hints (("Goal"
              :in-theory (e/d (len) ()))))

   (defthm fix-less-than-with-smm
     (implies (consp lst)
              (< 2 (+ 2 (LEN lst)))))))

(progn
  (local
   (defun bit-list-listp (lst)
     (if (atom lst)
         (equal lst nil)
       (and (bit-listp (car lst))
            (bit-list-listp (cdr lst))))))

  (local
   (defun rp-evlt-lst-lst (lst a)
     (if (atom lst)
         nil
       (cons (rp-evlt-lst (car lst) a)
             (rp-evlt-lst-lst (cdr lst) a)))))

  (local
   (define times$ (x y)
     :verify-guards nil
     (b* ((x (type-fix x))
          (y (type-fix y)))
       (* x y)))))

(local
 (defthm times$-of-1-and-0
   (and (equal (times$ 1 x)
               (type-fix x))
        (equal (times$ x 1)
               (type-fix x))
        (equal (times$ x 0)
               0)
        (equal (times$ 0 x)
               0))
   :hints (("goal"
            :in-theory (e/d (times$ and$) ())))))

(local
 (defthm len-equals-2
   (implies (and (integerp x)
                 (integerp y))
            (equal (EQUAL (+ x (len lst)) y)
                   (equal (len lst) (- y x))))))

(progn (local
        (defthm bit-listp-lemma
          (implies (bit-listp (rp-evlt-lst lst a))
                   (bit-listp (rp-evlt-lst (cdr lst) a)))))

       (local
        (defthm bit-listp-lemma-2
          (implies (and (bit-listp (rp-evlt-lst lst a))
                        (consp lst))
                   (bitp (rp-evlt (car lst) a))))))

(progn
  (local
   (defthmd or$-to-pp-sum
     (implies (and (bitp x)
                   (bitp y))
              (equal (or$ x y)
                     (pp-sum x y (-- (and$ x y)))))
     :hints (("goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthmd binary-xor-to-pp-sum
     (implies (and (bitp x)
                   (bitp y))
              (equal (binary-xor  x y)
                     (pp-sum x y
                             (-- (and$ x y))
                             (-- (and$ x y)))))))

  (local
   (defthmd binary-?-to-pp-sum
     (implies (and (bitp x)
                   (bitp test)
                   (bitp y))
              (equal (binary-? test  x y)
                     (pp-sum y (and$ test x)
                             (-- (and$ test y)))))))

  (local
   (defthm ---of-pp-sum
     (implies t
              (equal (-- (pp-sum x y))
                     (pp-sum (-- x) (-- y))))
     :hints (("goal"
              :in-theory (e/d (bitp pp-sum --) ())))))

  (local
   (defthm --of--
     (equal (-- (-- x))
            (type-fix x))))

  (local
   (defthm pp-sum-reorder
     (equal (pp-sum (pp-sum a b) c)
            (pp-sum a b c))
     :hints (("goal"
              :in-theory (e/d (pp-sum) ())))))

  (local
   (defthm pp-sum-comm
     (and (equal (pp-sum b a c)
                 (pp-sum a b c))
          (equal (pp-sum b a)
                 (pp-sum a b)))
     :hints (("goal"
              :in-theory (e/d (pp-sum) ())))))

  (local
   (defthm pp-sum-of-0
     (and (equal (pp-sum 0 c)
                 (type-fix c))
          (equal (pp-sum  c 0)
                 (type-fix c)))
     :hints (("goal"
              :in-theory (e/d (pp-sum) ())))))

  (local
   (defthm type-fix-of-fncs
     (and (equal (type-fix (and$ a b))
                 (and$ a b))
          (equal (type-fix (pp-sum a b))
                 (pp-sum a b)))
     :hints (("goal"
              :in-theory (e/d (and$ type-fix
                                    pp-sum) ())))))

  (local
   (defthm type-fix-of--
     (equal (type-fix (-- x))
            (-- x))))

  (local
   (defthm type-fix-when-integerp
     (implies (integerp x)
              (equal (type-fix x)
                     x))))

  (local
   (defthm type-fix-when-bitp
     (implies (bitp x)
              (equal (type-fix x)
                     x))))

  (local
   (defthm integerp-of-fncs
     (and (integerp (pp-sum x y))
          (integerp (-- x))
          (integerp (and$ x y))
          (integerp (or$ x y))
          (integerp (not$ x)))))

  (local
   (defthm bitp-implies-integerp
     (implies (bitp x)
              (integerp x))))

  (local
   (defthm when-minus-of-x-is-zero
     (implies (and (integerp x)
                   (equal (- x) 0))
              (equal x 0))
     :rule-classes :forward-chaining))

  (local
   (defthm when-minus-of-x-is-1
     (implies (and (integerp x)
                   (equal (- x) 1))
              (equal x -1))
     :rule-classes :forward-chaining))

  (local
   (defthm binar-and-abs-is-and$-2
     (and (implies (and (bitp x)
                        (bitp y))
                   (equal (times$ x y)
                          (and$ x y)))
          (implies (and (bitp x)
                        (bitp (-- y)))
                   (equal (times$ x y)
                          (-- (and$ x (-- y)))))
          (implies (and (bitp (-- x))
                        (bitp y))
                   (equal (times$ x y)
                          (-- (and$ (-- x) y))))
          (implies (and (bitp (-- x))
                        (bitp (-- y)))
                   (equal (times$ x y)
                          (and$ (-- x) (-- y)))))
     :hints (("goal"
              :in-theory (e/d (times$
                               bit-fix --
                               and$) ())))))
  (local
   (defthm pp-sum-equals
     (equal (equal (pp-sum a x)
                   (pp-sum a y))
            (equal (type-fix x)
                   (type-fix y)))))

  (local
   (defthm --of--equals
     (equal (equal (-- x)
                   (-- y))
            (equal (type-fix x)
                   (type-fix y)))))

  (local
   (defthm and$-of-1-0
     (implies t
              (and (equal (and$ x 1)
                          (bit-fix x))
                   (equal (and$ 1 x)
                          (bit-fix x))
                   (equal (and$ 0 x)
                          0)
                   (equal (and$ x 0)
                          0)))
     :hints (("goal"
              :in-theory (e/d (and$) ())))))

  (local
   (defthm pp-sum-of-negated-sum
     (and (equal (pp-sum a (-- a) b)
                 (type-fix b))
          (equal (pp-sum a (-- a))
                 0)
          (equal (pp-sum (-- a) a b)
                 (type-fix b))
          (equal (pp-sum (-- a) a)
                 0))
     :hints (("goal"
              :in-theory (e/d (pp-sum
                               type-fix) ())))))

  (local
   (defthm and$-assoc
     (equal (and$ (and$ a b) c)
            (and$ a b c))
     :hints (("goal"
              :in-theory (e/d (and$) ())))))

  (local
   (defthm and$-comm-loop=stopper
     (and (equal (and$ b a c)
                 (and$ a b c))
          (equal (and$ b a)
                 (and$ a b)))
     :hints (("goal"
              :in-theory (e/d (and$) ()))))))

(local
 (encapsulate
   nil

   (local
    (use-arith-5 t))

   (defthmd and$-is-times
     (implies (and (bitp x)
                   (bitp y))
              (equal (and$ x y)
                     (times$ x y))))

   (defthm type-fix-of-times
     (equal (type-fix (times$ a b))
            (times$ a b))
     :hints (("goal"
              :in-theory (e/d (times$ type-fix) ()))))

   (defthm times$-of---
     (and (equal (times$ a (-- b))
                 (-- (times$ a b)))
          (equal (times$ (-- a) b)
                 (-- (times$ a b))))
     :hints (("goal"
              :in-theory (e/d (-- times$ type-fix) ()))))

   (defthm times$-distribute-over-pp-sum
     (and (equal (times$ x (pp-sum a b))
                 (pp-sum (times$ x a)
                         (times$ x b)))
          (equal (times$ (pp-sum a b) x)
                 (pp-sum (times$ x a)
                         (times$ x b))))
     :hints (("goal"
              :in-theory (e/d (times$ pp-sum
                                      type-fix) ()))))

   (defthm times$-comm
     (and (equal (times$ b (times$ a c))
                 (times$ a (times$ b c)))
          (equal (times$ b a)
                 (times$ a b)))
     :hints (("goal"
              :in-theory (e/d (times$) ()))))

   (defthm times$-reoder
     (equal (times$ (times$ a b) c)
            (times$ a (times$ b c)))
     :hints (("goal"
              :in-theory (e/d (times$) ()))))))

(local
 (defthm and$-of-repeated-vars
   (and (equal (and$ a a b)
               (and$ a b))
        (equal (and$ a a)
               (bit-fix a)))
   :hints (("Goal"
            :in-theory (e/d (and$) ())))))

(local
 (progn
   (defthm len-to-consp
     (implies (not (zp size))
              (equal (equal (len x) size)
                     (and (consp x)
                          (equal (len (cdr x)) (1- size)))))
     :hints (("Goal"
              :in-theory (e/d (len) ()))))

   (defthm len-to-consp-when-o
     (equal (equal (len x) 0)
            (atom x)))

   (defthm len-to-consp-when-less-than-2
     (equal (< (LEN X) 2)
            (not (and (consp x)
                      (consp (cdr x)))))
     :hints (("Goal"
              :in-theory (e/d (len) ()))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; pp-lists-to-term lemmas

(local
 (progn
   (defthm append-returns-bit-list-listp
     (implies (and (pp-flatten-formula-checks state)
                   (booleanp sign)
                   (bit-list-listp (rp-evlt-lst-lst lst1 a))
                   (bit-list-listp (rp-evlt-lst-lst lst2 a))
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (append lst1 lst2)
                               a)))
     :hints (("goal"
              :in-theory (e/d (rp-evlt-lst-lst
                               and$-pp-lists
                               and$-pp-lists-aux
                               pp-term-to-pp-lists
                               bit-list-listp) ()))))

   (defthm append-returns-bit-list-listp-with-strip-cdrs
     (implies (and (pp-flatten-formula-checks state)
                   (booleanp sign)
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a))
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (strip-cdrs (append lst1 lst2))
                               a)))
     :hints (("goal"
              :in-theory (e/d (rp-evlt-lst-lst
                               and$-pp-lists
                               and$-pp-lists-aux
                               pp-term-to-pp-lists
                               bit-list-listp) ()))))

   (defthm append-returns-bit-listp
     (implies (and (pp-flatten-formula-checks state)
                   (booleanp sign)
                   (bit-listp (rp-evlt-lst lst1 a))
                   (bit-listp (rp-evlt-lst lst2 a))
                   (rp-evl-meta-extract-global-facts))
              (bit-listp
               (rp-evlt-lst (append lst1 lst2)
                           a)))
     :hints (("goal"
              :in-theory (e/d (rp-evlt-lst-lst
                               and$-pp-lists
                               and$-pp-lists-aux
                               pp-term-to-pp-lists
                               bit-list-listp) ()))))))

(local
 (defthm append-equal
   (and (equal (equal (append a x) (append a y))
               (equal x y))
        (implies (and (true-listp x)
                      (true-listp y))
                 (equal (equal (append x a) (append y a))
                        (equal x y))))))

(local
 (defthm append-equal2
   (implies (and (force (equal x k))
                 (force (equal y l)))
            (equal (equal (append x y a) (append k l a))
                   t))))

(progn
  (local
   (defthm bitp-of-eval-of-pp-lists-to-term-aux
     (implies (and (bit-listp (rp-evlt-lst lst a))
                   (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts))
              (bitp (rp-evlt (pp-lists-to-term-and$ lst) a)))
     :hints (("goal"
              :in-theory (e/d (pp-lists-to-term-and$) ())))))

  (local
   (defthm eval-of-append-of-pp-lists-to-term-aux
     (implies  (and (pp-flatten-formula-checks state)
                    (rp-evl-meta-extract-global-facts)
                    (bit-listp (rp-evlt-lst cur a))
                    (bit-listp (rp-evlt-lst cur2 a)))
               (equal (rp-evlt (pp-lists-to-term-and$ (append cur cur2)) a)
                      (and$ (rp-evlt (pp-lists-to-term-and$ cur) a)
                            (rp-evlt (pp-lists-to-term-and$ cur2) a))))
     :hints (("goal"
              :do-not-induct t
              :induct (pp-lists-to-term-and$ cur)
              :in-theory (e/d (pp-lists-to-term-and$)
                              (bitp
                               rp-evl-lst-of-cons
                               (:rewrite acl2::consp-of-append)
                               bit-listp))))))

  (local
   (defthm integerp-of-eval-of-pp-lists-to-term-aux
     (implies (and (integer-listp (rp-evlt-lst lst a))
                   (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts))
              (integerp (rp-evlt (pp-lists-to-term-and$ lst) a)))
     :hints (("goal"
              :in-theory (e/d (pp-lists-to-term-and$) ())))))

  (local
   (defthm integerp-of-eval-of-pp-lists-to-term
     (implies (and (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a))
                   (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts))
              (integerp (rp-evlt (pp-lists-to-term-p+ lst) a)))
     :hints (("goal"
              :do-not-induct t
              :induct (pp-lists-to-term-p+ lst)
              :in-theory (e/d (pp-lists-to-term-p+)
                              (pp-sum --
                                      and$
                                      bitp
                                      type-fix))))))

  (local
   (defthm integerp-of-eval-of-pp-lists-to-term-forward-chaining
     (implies (and (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a)))
              (integerp (rp-evlt (pp-lists-to-term-p+ lst) a)))
     :rule-classes :forward-chaining
     :hints (("goal"
              :in-theory (e/d (pp-lists-to-term-p+) ()))))))

(local
 (defthm pp-lists-to-term-of-apply-sign-to-pp-lists
   (implies (and (pp-flatten-formula-checks state)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a))
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt (pp-lists-to-term-p+ (apply-sign-to-pp-lists lst t)) a)
                   (-- (rp-evlt (pp-lists-to-term-p+ lst) a))))
   :hints (("goal"
            :do-not-induct t
            :induct (pp-lists-to-term-p+ lst)
            :in-theory (e/d (pp-lists-to-term-p+
                             APPLY-SIGN-TO-PP-LISTS)
                            (--
                             pp-sum
                             type-fix
                             type-p))))))

(local
 (defthm pp-lists-to-term-of-append
   (implies (and (pp-flatten-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a))
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a)))
            (equal (rp-evlt (pp-lists-to-term-p+ (append lst1 lst2)) a)
                   (pp-sum (rp-evlt (pp-lists-to-term-p+ lst1) a)
                           (rp-evlt (pp-lists-to-term-p+ lst2) a))))
   :hints (("goal"
            :induct (pp-lists-to-term-p+ lst1)
            :do-not-induct t
            :in-theory (e/d (pp-lists-to-term-p+)
                            (pp-sum
                             --
                             type-fix))))))

(local
 (defthm apply-sign-to-pp-lists-of-sign=nil
   (implies (pp-lists-p lst)
            (equal (apply-sign-to-pp-lists lst nil)
                   lst))
   :hints (("Goal"
            :in-theory (e/d (apply-sign-to-pp-lists) ())))))

(local
 (defthm apply-sign-to-pp-lists-of-append
   (implies t
            (equal (apply-sign-to-pp-lists (append x1 x2) sign)
                   (append (apply-sign-to-pp-lists x1 sign)
                           (apply-sign-to-pp-lists x2 sign))))
   :hints (("Goal"
            :in-theory (e/d (apply-sign-to-pp-lists) ())))))

(local
 (defthm apply-sign-to-pp-lists-of-apply-sign-to-pp-lists
   (equal (apply-sign-to-pp-lists (apply-sign-to-pp-lists lst s1) s2)
          (apply-sign-to-pp-lists lst (xor s1 s2)))
   :hints (("Goal"
            :in-theory (e/d (apply-sign-to-pp-lists) ())))))

(local
 (defthm bit-list-listp-of-apply-sign-to-pp-lists
   (implies (and (pp-flatten-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a)))
            (bit-list-listp
             (rp-evlt-lst-lst
              (strip-cdrs (apply-sign-to-pp-lists lst1
                                                  sign))
              a)))
   :hints (("Goal"
            :in-theory (e/d (apply-sign-to-pp-lists) ())))))

(local
 (defthmd sign-convert-apply-sign-to-pp-lists
   (implies (and (pp-flatten-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a)))
            (equal (rp-evlt (pp-lists-to-term-p+
                            (apply-sign-to-pp-lists lst t))
                           a)
                   (-- (rp-evlt (pp-lists-to-term-p+
                                (apply-sign-to-pp-lists lst nil))
                               a))))
   :hints (("goal"
            :do-not-induct t
            :induct (apply-sign-to-pp-lists lst sign)
            :in-theory (e/d (pp-term-to-pp-lists
                             and$-pp-lists
                             apply-sign-to-pp-lists
                             and$-pp-lists-aux
                             pp-lists-to-term-p+)
                            (--
                             pp-sum
                             and$))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sorting lemmas

(local
 (defthm bit-list-p-with-constants-1
   (equal (bit-listp (cons 1 rest))
          (bit-listp rest))))

(local
 (defthm bit-list-p-def
   (equal (bit-listp (cons x rest))
          (and (bitp x)
               (bit-listp rest)))))

(progn
  (local
   (defthm PP-LISTS-TO-TERM-AND$-def-1
     (implies (consp rest)
              (equal (PP-LISTS-TO-TERM-AND$ (cons x rest))
                     `(binary-and ,x ,(PP-LISTS-TO-TERM-AND$ rest))))
     :hints (("Goal"
              :in-theory (e/d (pp-lists-to-term-and$) ())))))

  (local
   (defthm PP-LISTS-TO-TERM-AND$-def-2
     (implies (atom rest)
              (equal (PP-LISTS-TO-TERM-AND$ (cons x rest))
                     x))
     :hints (("Goal"
              :in-theory (e/d (pp-lists-to-term-and$) ())))))

  (local
   (defthm PP-LISTS-TO-TERM-AND$-def
     (implies t
              (equal (PP-LISTS-TO-TERM-AND$ (cons x rest))
                     (if (consp rest)
                         `(binary-and ,x ,(PP-LISTS-TO-TERM-AND$ rest))
                       x)))
     :hints (("Goal"
              :in-theory (e/d (pp-lists-to-term-and$) ()))))))

(progn
  (local
   (defthm PP-LISTS-TO-TERM-p+-def
     (implies t
              (equal (pp-lists-to-term-p+ (cons x rest))
                     (COND
                      ((ATOM rest)
                       (B* ((CUR (PP-LISTS-TO-TERM-AND$ (cdr x))))
                         (IF (car x)
                             (CONS '-- (CONS CUR 'NIL))
                             CUR)))
                      (T
                       (B*
                           ((CUR (PP-LISTS-TO-TERM-AND$ (CDR x))))
                         (IF (car x)
                             (CONS 'P+
                                   (CONS (CONS '-- (CONS CUR 'NIL))
                                         (CONS (PP-LISTS-TO-TERM-P+ rest)
                                               'NIL)))
                             (CONS 'P+
                                   (CONS CUR
                                         (CONS (PP-LISTS-TO-TERM-P+ rest)
                                               'NIL)))))))))
     :hints (("Goal"
              :in-theory (e/d (pp-lists-to-term-p+) ()))))))

(local
 (encapsulate
   nil

   (defthm atom-merge-sorted-and$-lists
     (equal (CONSP (MERGE-SORTED-AND$-LISTS LST1 lst2))
            (not (and (atom lst1)
                      (atom lst2))))
     :hints (("Goal"
              :in-theory (e/d (merge-sorted-and$-lists) ()))))

   (local
    (defthm dummy-lemma1
      (implies (equal x (and$ a b))
               (equal (equal x
                             (and$ a x))
                      t))))

   (defthm eval-of-list-to-term-of-merge-sorted-and$-list
     (implies (and (pp-flatten-formula-checks state)
                   (force (bit-listp (rp-evlt-lst lst1 a)))
                   (force (bit-listp (rp-evlt-lst lst2 a)))
                   (force (true-listp lst1))
                   (force (true-listp lst2))
                   (rp-evl-meta-extract-global-facts))
              (equal (rp-evlt
                      (pp-lists-to-term-and$
                       (merge-sorted-and$-lists lst1 lst2))
                      a)
                     (and$ (rp-evlt (pp-lists-to-term-and$ lst1) a)
                           (rp-evlt (pp-lists-to-term-and$ lst2) a))))
     :hints (("Goal"
              :induct (MERGE-SORTED-AND$-LISTS lst1 lst2)
              :do-not-induct t
              :in-theory (e/d (;;pp-lists-to-term-and$
                               ;; for soem reason when this is enabled, the proof
                               ;; does too many case-splits.
                               MERGE-SORTED-AND$-LISTS)
                              (len
                               pp-sum valid-sc
                               --
                               and$ or$
                               bitp
                               bit-listp
                               true-listp)))
             ("Subgoal *1/6"
              :expand ((PP-LISTS-TO-TERM-AND$ LST2)))
             ("Subgoal *1/5"
              :expand ((PP-LISTS-TO-TERM-AND$ LST1)))
             ("Subgoal *1/4"
              :do-not-induct t
              :expand ((PP-LISTS-TO-TERM-AND$ LST2)
                       (PP-LISTS-TO-TERM-AND$ LST1)))))

   (defthm bit-listp-of-merge-sorted-and$-lists
     (implies (and (bit-listp (rp-evlt-lst lst1 a))
                   (bit-listp (rp-evlt-lst lst2 a)))
              (bit-listp (rp-evlt-lst (MERGE-SORTED-AND$-LISTS LST1 lst2)
                                     a)))
     :hints (("Goal"
              :do-not-induct t
              :induct (MERGE-SORTED-AND$-LISTS LST1 lst2)
              :in-theory (e/d (bit-listp
                               merge-sorted-and$-lists)
                              (bitp
                               floor)))))))

(local
 (encapsulate
   nil

   (local
    (defthm bitp-bitlistp-lemma
      (IMPLIES (AND (consp lst)
                    (BIT-LISTP (RP-EVLT-LST LST A)))
               (BITP (RP-EVLT (CAR LST) A)))
      :hints (("Goal"
               :in-theory (e/d (bitp bit-listp) ())))))

   (local
    (defthm consp-bit-listp-lemma
      (IMPLIES (AND (NOT (ZP SIZE))
                    (< SIZE (LEN LST)))
               (consp lst))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (len bitp bit-listp) ())))))

   (defthm bit-listp-of-CUT-LIST-BY-HALF
     (implies (and (bit-listp (rp-evlt-lst lst a))
                   (< size (len lst)))
              (and (bit-listp (rp-evlt-lst (MV-NTH 0
                                                  (CUT-LIST-BY-HALF LST size))
                                          a))
                   (bit-listp (rp-evlt-lst (MV-NTH 1
                                                  (CUT-LIST-BY-HALF LST size))
                                          a))))
     :hints (("Goal"
              :do-not-induct t
              :induct (CUT-LIST-BY-HALF LST size)
              :in-theory (e/d (bit-listp
                               cut-list-by-half)
                              (bitp)))))

   (defthm bit-list-listp-of-CUT-LIST-BY-HALF
     (implies (and (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a))
                   (< size (len lst)))
              (and (bit-list-listp (rp-evlt-lst-lst (strip-cdrs
                                                    (MV-NTH 0
                                                            (CUT-LIST-BY-HALF LST size)))
                                                   a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs (MV-NTH 1
                                                                       (CUT-LIST-BY-HALF LST size)))
                                                   a))))
     :hints (("Goal"
              :do-not-induct t
              :induct (CUT-LIST-BY-HALF LST size)
              :in-theory (e/d (
                               bit-list-listp
                               cut-list-by-half)
                              (bitp
                               bit-listp)))))

   (local
    (defthm lemma1
      (implies (NOT (CONSP (MV-NTH 0 (CUT-LIST-BY-HALF lst size))))
               (equal (MV-NTH 1 (CUT-LIST-BY-HALF lst size))
                      lst))
      :hints (("Goal"
               :in-theory (e/d (cut-list-by-half) ())))))

   (defthm eval-of-CUT-LIST-BY-HALF
     (implies (and (pp-flatten-formula-checks state)
                   (force (bit-listp (rp-evlt-lst lst a)))
                   (force (true-listp lst))
                   (force (< size (len lst)))
                   (rp-evl-meta-extract-global-facts))
              (equal (AND$ (RP-EVLT (PP-LISTS-TO-TERM-AND$
                                    (MV-NTH 0
                                            (CUT-LIST-BY-HALF LST size)))
                                   A)
                           (RP-EVLT (PP-LISTS-TO-TERM-AND$
                                    (MV-NTH 1
                                            (CUT-LIST-BY-HALF LST size)))
                                   A))
                     (RP-EVLT (PP-LISTS-TO-TERM-AND$
                              lst)
                             A)))
     :hints (("Goal"
              :do-not-induct t
              :induct (CUT-LIST-BY-HALF LST size)
              :expand ((PP-LISTS-TO-TERM-AND$ LST))
              :in-theory (e/d (cut-list-by-half)
                              (bitp len
                                    true-listp)))))

   (local
    (defthm PP-LISTS-TO-TERM-P+-when-not-consp
      (implies (atom x)
               (equal (PP-LISTS-TO-TERM-P+ x)
                      ''0))
      :hints (("Goal"
               :in-theory (e/d (PP-LISTS-TO-TERM-P+) ())))))

   (defthm eval-of-CUT-LIST-BY-HALF-with-pp-sum
     (implies (and (pp-flatten-formula-checks state)
                   (force (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a)))
                   (force (pp-lists-p lst))
                   (force (< size (len lst)))
                   (rp-evl-meta-extract-global-facts))
              (equal (pp-sum (RP-EVLT (PP-LISTS-TO-TERM-p+
                                      (MV-NTH 0
                                              (CUT-LIST-BY-HALF LST size)))
                                     A)
                             (RP-EVLT (PP-LISTS-TO-TERM-p+
                                      (MV-NTH 1
                                              (CUT-LIST-BY-HALF LST size)))
                                     A))
                     (RP-EVLT (PP-LISTS-TO-TERM-p+
                              lst)
                             A)))
     :hints (("Goal"
              :do-not-induct t
              :induct (CUT-LIST-BY-HALF LST size)
              :expand ((PP-LISTS-TO-TERM-p+ LST))
              :in-theory (e/d (cut-list-by-half)
                              (bitp
                               pp-sum
                               --
                               len
                               true-listp)))))))

(local
 (defthm pos-len-implies-fc
   (implies (< 0 (LEN LST))
            (consp lst))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (len) ())))))

(local
 (defthm bit-listp-of-sort-and$-list
   (implies (bit-listp (rp-evlt-lst lst a))
            (and (bit-listp (rp-evlt-lst (sort-and$-list LST size)
                                        a))))
   :hints (("Goal"
            :do-not-induct t
            :induct (sort-and$-list LST size)
            :in-theory (e/d (bit-listp
                             sort-and$-list
                             pp-lists-p-implies-true-listp)
                            (bitp
                             floor))))))

;; MAIN LEMMA 2: sort-and$-list-is-correct
(local
 (defthm eval-of-list-to-term-of-sort-and$-list
   (implies (and (pp-flatten-formula-checks state)
                 (bit-listp (rp-evlt-lst lst a))
                 (true-listp lst)
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt
                    (pp-lists-to-term-and$
                     (sort-and$-list lst len))
                    a)
                   (rp-evlt (pp-lists-to-term-and$ lst) a)))
   :hints (("Goal"
            :do-not-induct t
            :induct (sort-and$-list lst len)
            :in-theory (e/d (sort-and$-list
                             )
                            (floor
                             (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                             (:DEFINITION TRUE-LISTP)
                             (:DEFINITION RP-TERMP)
                             (:DEFINITION RP-TERM-LISTP)
                             (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                             (:REWRITE PP-LISTS-P-IMPLIES-TRUE-LISTP)
                             (:DEFINITION PP-LISTS-P)
                             (:DEFINITION ACL2::APPLY$-BADGEP)
                             (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                             (:REWRITE IS-IF-RP-TERMP)
                             (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                             (:DEFINITION SUBSETP-EQUAL)
                             (:DEFINITION MEMBER-EQUAL)
                             (:REWRITE DEFAULT-CDR)
                             (:REWRITE RP-TERMP-CADR)
                             (:REWRITE IS-RP-PSEUDO-TERMP)
                             (:REWRITE RP-TERMP-CADDR)
                             (:REWRITE ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                             (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE ACL2::O-P-O-INFP-CAR)
                             (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                             (:DEFINITION NATP)
                             (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 3)
                             (:TYPE-PRESCRIPTION MEMBER-EQUAL)
                             (:TYPE-PRESCRIPTION PP-LISTS-P)
                             len))))))

;; proofs with merge-sorted-pp-lists-simple are easier to work with
#|(local
 (define merge-sorted-pp-lists-simple
   ((first pp-lists-p)
    (second pp-lists-p))
   :measure
   (+ (acl2-count first)
      (acl2-count second))
   :returns
   (res pp-lists-p
        :hyp (and (pp-lists-p first)
                  (pp-lists-p second)))
   :verify-guards nil
   (cond
    ((atom first) second)
    ((atom second) first)
    (t
     (b*
         ((sign1 (caar first))
          (term1 (cdar first))
;(term1 (sort-and$-list term1 (len term1)))
          (sign2 (caar second))
          (term2 (cdar second))
          #|(term2 (sort-and$-list term2 (len term2)))||#)
       (cond
        ((and (not (equal sign1 sign2))
              (equal term1 term2))
         (merge-sorted-pp-lists-simple (cdr first) (cdr second)))
        ((pp-list-order term1 term2)
         (acons sign1 term1
                (merge-sorted-pp-lists-simple (cdr first) second)))
        (t (acons sign2 term2
                  (merge-sorted-pp-lists-simple first (cdr second))))))))
   ///

   (local
    (defthm lemma1
      (implies (consp first)
               (equal (merge-sorted-pp-lists
                       first
                       (cdr (car first)) #|(sort-and$-list (cdr (car first)) (len (cdr (car first))))||#
                       second sim2)
                      (merge-sorted-pp-lists first nil second sim2)))
      :hints (("goal"
               :do-not-induct t
               :expand ((merge-sorted-pp-lists
                         first
                         (cdr (car first)) #|(sort-and$-list (cdr (car first)) (len (cdr (car first))))||#
                         second sim2)
                        (merge-sorted-pp-lists first nil second sim2))
               :in-theory (e/d () ())))))

   (local
    (defthm lemma2
      (implies (consp second)
               (equal (merge-sorted-pp-lists
                       first
                       sim1
                       second
                       (cdr (car second)) #|(sort-and$-list (cdr (car second)) (len (cdr (car second))))||#)
                      (merge-sorted-pp-lists first sim1 second nil)))
      :hints (("goal"
               :do-not-induct t
               :expand ((merge-sorted-pp-lists
                         first
                         sim1
                         second
                         (cdr (car second)) #|(sort-and$-list (cdr (car second)) (len (cdr (car second))))||#)
                        (merge-sorted-pp-lists first sim1 second nil))
               :in-theory (e/d () ())))))

   (defthm merge-sorted-pp-lists_to_merge-sorted-pp-lists-simple
     (implies t
              (equal (merge-sorted-pp-lists first nil second nil)
                     (merge-sorted-pp-lists-simple first second)))
     :hints (("goal"
              :induct (merge-sorted-pp-lists-simple first second)
              :in-theory (e/d (merge-sorted-pp-lists
                               merge-sorted-pp-lists-simple
                               ) ()))))))||#

(local
 (encapsulate
   nil

   (defun two-pp-list-cancel-each-other (lst1 lst2)
     (if (or (atom lst1)
             (atom lst2))
         (and (atom lst1)
              (atom lst2))
       (and (not (equal (caar lst1)
                        (caar lst2)))
            (equal (cdar lst1) ;(SORT-AND$-LIST (cdar lst1) (len (cdar lst1)))
                   (cdar lst2) ;(SORT-AND$-LIST (cdar lst2) (len (cdar lst2)))
                   )
            (two-pp-list-cancel-each-other (cdr lst1)
                                           (cdr lst2)))))

   (defthm when-SORT-AND$-LIST-is-equal-with-opposite-signs
     (implies (and #|(EQUAL (SORT-AND$-LIST lst1 size1)
               (SORT-AND$-LIST lst2 size2))||#
               (equal lst1 lst2)
               (pp-flatten-formula-checks state)
               (rp-evl-meta-extract-global-facts)
               (bit-listp (rp-evlt-lst lst1 a))
               (bit-listp (rp-evlt-lst lst2 a))
               (true-listp lst1)
               (true-listp lst2))
              (and (equal (PP-SUM (RP-EVLT (pp-lists-to-term-and$ LST1)
                                          A)
                                  (-- (RP-EVLT (pp-lists-to-term-and$ LST2)
                                              A)))
                          0)
                   (equal (PP-SUM (-- (RP-EVLT (pp-lists-to-term-and$ LST1)
                                              A))
                                  (RP-EVLT (pp-lists-to-term-and$ LST2)
                                          A))
                          0)))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance eval-of-list-to-term-of-sort-and$-list
                               (lst lst1)
                               (len size1))
                    (:instance eval-of-list-to-term-of-sort-and$-list
                               (lst lst2)
                               (len size2)))
              :in-theory (e/d ()
                              (pp-sum
                               eval-of-list-to-term-of-sort-and$-list
                               --)))))

   (defthm two-pp-list-cancel-each-other-implies
     (implies (and (two-pp-list-cancel-each-other lst1 lst2)
                   (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a))
                   (pp-lists-p lst1)
                   (pp-lists-p lst2))
              (equal (PP-SUM (RP-EVLT (PP-LISTS-TO-TERM-P+ LST1)
                                     A)
                             (RP-EVLT (PP-LISTS-TO-TERM-P+ LST2)
                                     A))
                     0))
     :hints (("Goal"
              :induct (two-pp-list-cancel-each-other lst1 lst2)
              :in-theory (e/d (PP-LISTS-TO-TERM-P+)
                              (pp-sum
                               --)))))

   (defthm two-pp-list-cancel-each-other-implies-2
     (implies (and (two-pp-list-cancel-each-other lst1 lst2)
                   (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a))
                   (pp-lists-p lst1)
                   (pp-lists-p lst2))
              (equal (RP-EVLT (PP-LISTS-TO-TERM-P+
                              (merge-sorted-pp-lists
                               lst1 LST2))
                             A)
                     0))
     :hints (("Goal"
              :do-not-induct t
              :induct (two-pp-list-cancel-each-other lst1 lst2)
              :in-theory (e/d (PP-LISTS-TO-TERM-P+
                               merge-sorted-pp-lists)
                              (pp-sum
                               --)))))

   (defthm atom-merge-sorted-pp-lists
     (equal (CONSP (merge-sorted-pp-lists LST1 lst2))
            (not (two-pp-list-cancel-each-other lst1 lst2)))
     :hints (("Goal"
              :do-not-induct t
              :induct (merge-sorted-pp-lists LST1 lst2)
              :in-theory (e/d (merge-sorted-pp-lists)
                              ()))))

   (defthm pp-sum-equals-2
     (implies (integerp a)
              (equal (equal a (pp-sum x y a))
                     (equal (pp-sum x y) 0)))
     :hints (("Goal"
              :in-theory (e/d (pp-sum type-fix) ()))))

   (defthm eval-of-list-to-term-of-merge-sorted-pp-lists
     (implies (and (pp-flatten-formula-checks state)
                   (force (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a)))
                   (force (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a)))
                   (force (pp-lists-p lst1))
                   (force (pp-lists-p lst2))
                   (rp-evl-meta-extract-global-facts))
              (equal (rp-evlt
                      (pp-lists-to-term-p+
                       (merge-sorted-pp-lists lst1 lst2))
                      a)
                     (pp-sum (rp-evlt (pp-lists-to-term-p+ lst1) a)
                             (rp-evlt (pp-lists-to-term-p+ lst2) a))))
     :hints (("Goal"
              :induct (merge-sorted-pp-lists lst1 lst2)
              :do-not-induct t
              :in-theory (e/d (;;pp-lists-to-term-and$
                               ;; for soem reason when this is enabled, the proof
                               ;; does too many case-splits.
                               merge-sorted-pp-lists)
                              (len
                               pp-sum valid-sc
                               --
                               and$ or$
                               TWO-PP-LIST-CANCEL-EACH-OTHER
                               bitp
                               bit-listp
                               ;;PP-LISTS-P
;BIT-LIST-LISTP
                               true-listp)))
             ("Subgoal *1/5"
              :expand ((PP-LISTS-TO-TERM-P+ LST2)))
             ("Subgoal *1/4"
              :expand ((PP-LISTS-TO-TERM-P+ LST1)
                       (TWO-PP-LIST-CANCEL-EACH-OTHER NIL LST2)))
             ("Subgoal *1/3"
              :expand ((PP-LISTS-TO-TERM-P+ LST1)
                       (PP-LISTS-TO-TERM-P+ LST2)))))

   (defthm bit-list-list-of-merge-sorted-pp-lists
     (implies (and (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a)))
              (bit-list-listp (rp-evlt-lst-lst (strip-cdrs (merge-sorted-pp-lists LST1 lst2))
                                              a)))
     :hints (("Goal"
              :do-not-induct t
              :induct (merge-sorted-pp-lists LST1 lst2)
              :in-theory (e/d (bit-listp
                               bit-list-listp
                               merge-sorted-pp-lists)
                              (bitp
                               floor)))))))

(local
 (defthm bit-list-listp-of-sort-pp-lists
   (implies (and (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a))
                 (pp-lists-p lst))
            (bit-list-listp (rp-evlt-lst-lst (strip-cdrs (sort-pp-lists lst
                                                                       size))
                                            a)))
   :hints (("Goal"
            :do-not-induct t
            :induct (sort-pp-lists lst size)
            :in-theory (e/d (sort-pp-lists)
                            (floor))))))

(local
 (defthm eval-of-sort-pp-lists-is-correct
   (implies (and (pp-flatten-formula-checks state)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a))
                 (pp-lists-p lst)
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt (pp-lists-to-term-p+ (sort-pp-lists lst size)) a)
                   (rp-evlt (pp-lists-to-term-p+ lst) a)))
   :hints (("Goal"
            :do-not-induct t
            :induct (sort-pp-lists lst size)
            :in-theory (e/d (sort-pp-lists
                             len
                             PP-LISTS-TO-TERM-P+)
                            (floor
                             bitp
                             --
                             pp-sum))))))

(local
 (defthm consp-of-apply-sign
   (equal (consp (apply-sign-to-pp-lists lst sign))
          (consp lst))
   :hints (("Goal"
            :in-theory (e/d (apply-sign-to-pp-lists) ())))))

(local
 (defthm len-of-apply-sign
   (equal (len (apply-sign-to-pp-lists lst sign))
          (len lst))
   :hints (("Goal"
            :in-theory (e/d (apply-sign-to-pp-lists len) ())))))

(local
 (defthm merge-sorted-pp-lists-simple-of-apply-sign
   (implies (and (pp-lists-p lst1)
                 (pp-lists-p lst2))
            (equal (merge-sorted-pp-lists (apply-sign-to-pp-lists lst1 sign)
                                                 (apply-sign-to-pp-lists lst2 sign))
                   (apply-sign-to-pp-lists (merge-sorted-pp-lists lst1 lst2)
                                           sign)))
   :hints (("Goal"
            :induct (merge-sorted-pp-lists lst1 lst2)
            :do-not-induct t
            :in-theory (e/d (apply-sign-to-pp-lists
                             merge-sorted-pp-lists) ())))))

(local
 (defthmd merge-sorted-pp-lists-simple-of-apply-sign-reverse
   (implies (and (pp-lists-p lst1)
                 (pp-lists-p lst2))
            (equal (apply-sign-to-pp-lists (merge-sorted-pp-lists lst1 lst2)
                                           sign)
                   (merge-sorted-pp-lists (apply-sign-to-pp-lists lst1 sign)
                                                 (apply-sign-to-pp-lists lst2 sign))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d () ())))))


(local
 (defthm merge-sorted-pp-lists-simple-of-apply-sign-2
   (implies (and (pp-lists-p lst1)
                 (pp-lists-p lst2)
                 (syntaxp (or (atom lst2)
                              (not (equal (car lst2) 'apply-sign-to-pp-lists)))))
            (equal (merge-sorted-pp-lists (apply-sign-to-pp-lists lst1 sign)
                                                 lst2)
                   (apply-sign-to-pp-lists (merge-sorted-pp-lists
                                            lst1
                                            (apply-sign-to-pp-lists lst2 sign))
                                           sign)))
   :hints (("Goal"
            ;:induct (merge-sorted-pp-lists-simple lst1 lst2)
            :do-not-induct t
            :in-theory (e/d (merge-sorted-pp-lists-simple-of-apply-sign-reverse)
                            (merge-sorted-pp-lists-simple-of-apply-sign))))))

(local
 (defthm cut-list-by-half-of-signed-pp-lists-0
   (implies (and (pp-lists-p lst)
                 (< size (len lst)))
            (equal (mv-nth
                    0
                    (cut-list-by-half (apply-sign-to-pp-lists lst sign) size))
                   (apply-sign-to-pp-lists
                    (mv-nth 0
                            (cut-list-by-half lst size))
                    sign)))
   :hints (("Goal"
            :in-theory (e/d (cut-list-by-half
                             apply-sign-to-pp-lists) ())))))

(local
 (defthm cut-list-by-half-of-signed-pp-lists-1
   (implies (and (pp-lists-p lst)
                 (< size (len lst)))
            (equal (mv-nth
                    1
                    (cut-list-by-half (apply-sign-to-pp-lists lst sign) size))
                   (apply-sign-to-pp-lists
                    (mv-nth 1
                            (cut-list-by-half lst size))
                    sign)))
   :hints (("Goal"
            :in-theory (e/d (cut-list-by-half
                             apply-sign-to-pp-lists) ())))))


(local
 (defthm PP-LISTS-P-implies-fc
   (implies (PP-LISTS-P x)
            (IF (ATOM X)
                (EQ X NIL)
                (AND (CONSP (CAR X))
                     (BOOLEANP (CAAR X))
                     (TRUE-LISTP (CDAR X))
                     (PP-LISTS-P (CDR X)))))
   :rule-classes :forward-chaining))

(local
 (defthmd pos-len-is
   (equal (< 0 (LEN LST))
          (consp lst))
   :hints (("Goal"
            :in-theory (e/d (len) ())))))

(local
 (encapsulate
   nil
   (local
    (defthm sort-pp-lists-of-apply-sign-dummy-lemma1
      (IMPLIES (AND (CONSP LST)
                    (CONSP (CDR LST))
                    (NOT (CONSP (CDDR LST)))
                    (PP-LISTS-P LST)
                    (CONSP (CADR LST))
                    (CAR (CADR LST)))
               (equal (EQUAL (CADR LST)
                             (CONS T (CDR (CADR LST))))
                      t))))

   (local
    (defthm sort-pp-lists-of-apply-sign-dummy-lemma2
      (IMPLIES (AND (CONSP (CDR LST))
                    (PP-LISTS-P LST)
                    (CAR (CADR LST)))
               (equal (EQUAL T (CAR (CADR LST)))
                      t))))

   (local
    (defthm sort-pp-lists-of-apply-sign-dummy-lemma3
      (IMPLIES (AND (CONSP LST)
                    (CONSP (CDR LST))
                    (PP-LISTS-P LST)
                    (NOT (CAR (CADR LST))))
               (equal (EQUAL (CADR LST)
                             (CONS NIL (CDR (CADR LST))))
                      t))))

   (local
    (defthm sort-pp-lists-of-apply-sign-dummy-lemma4
      (IMPLIES (AND (CONSP LST)
                    (CONSP (CDR LST))
                    (PP-LISTS-P LST)
                    (CAR (CADR LST)))
               (equal (EQUAL (CADR LST)
                             (CONS t (CDR (CADR LST))))
                      t))))

   (local
    (defthm  sort-pp-lists-of-apply-sign-dummy-lemma5
      (implies (and (consp lst)
                    (consp (cdr lst))
                    (not (consp (cddr lst)))
                    (equal (car (car lst)) (car (cadr lst)))
                    (pp-lists-p lst))
               (equal
                (equal (cadr lst)
                       (cons (car (car lst))
                             (cdr (cadr lst))))
                t))))


   (defthm sort-pp-lists-of-apply-sign
     (implies (and (pp-lists-p lst))
              (equal (sort-pp-lists (apply-sign-to-pp-lists lst sign) size)
                     (apply-sign-to-pp-lists (sort-pp-lists lst size)
                                             sign)))
     :otf-flg t
     :hints (("Goal"
              :induct (sort-pp-lists lst size)
              :do-not-induct t
              :in-theory (e/d (apply-sign-to-pp-lists
                               sort-pp-lists
                               pos-len-is)
                              (pp-lists-p
                               merge-sorted-pp-lists-simple-of-apply-sign-2)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FLATTEN LEMMAS

(local
 (progn
   (defthm and$-pp-lists-aux-returns-bit-list-listp
     (implies (and (pp-flatten-formula-checks state)
                   (booleanp sign)
                   (bit-listp (rp-evlt-lst cur a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs acc) a))
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (strip-cdrs (and$-pp-lists-aux cur lst2 acc sign))
                               a)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists-aux cur lst2 acc sign)
              :in-theory (e/d (rp-evlt-lst-lst
                               and$-pp-lists
                               and$-pp-lists-aux
                               pp-term-to-pp-lists
                               bit-list-listp) ()))))

   (defthm and$-pp-lists-returns-bit-list-listp
     (implies (and (pp-flatten-formula-checks state)
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs acc) a))
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (strip-cdrs (and$-pp-lists lst1 lst2 acc sign))
                               a)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists lst1 lst2 acc sign)
              :in-theory (e/d (rp-evlt-lst-lst
                               and$-pp-lists
                               and$-pp-lists-aux
                               pp-term-to-pp-lists
                               bit-list-listp) ()))))

   (defthm pp-term-to-pp-lists-returns-bit-list-listp
     (implies (and (pp-flatten-formula-checks state)
                   (pp-term-p term)
                   (booleanp sign)
                   (valid-sc term a)
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (strip-cdrs (pp-term-to-pp-lists term sign))
                               a)))
     :hints (("goal"
              :do-not-induct t
              :induct (pp-term-to-pp-lists term sign)
              :in-theory (e/d (rp-evlt-lst-lst
                               pp-term-to-pp-lists
                               bit-list-listp) ()))))))

(progn
  (local
   (defthm and$-pp-lists-aux-extract-acc
     (implies (and (syntaxp (not (equal acc ''nil))))
              (equal (and$-pp-lists-aux cur lst2 acc sign)
                     (append (and$-pp-lists-aux cur lst2 nil sign)
                             acc)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists-aux cur lst2 acc sign)
              :in-theory (e/d (and$-pp-lists-aux
                               and$-pp-lists)
                              (pp-sum
                               --
                               type-fix))))))

  (local
   (defthm and$-pp-lists-extract-acc
     (implies (and (syntaxp (not (equal acc ''nil)))
                   (pp-flatten-formula-checks state)
                   (rp-evl-meta-extract-global-facts))
              (equal (and$-pp-lists lst1 lst2 acc sign)
                     (append (and$-pp-lists lst1 lst2 nil sign)
                             acc)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists lst1 lst2 acc sign)
              :in-theory (e/d (pp-lists-to-term-p+
                               and$-pp-lists)
                              (pp-sum
                               --
                               type-fix))))))

  (local
   (defthm and$-pp-lists-aux-extract-sign-and-acc
     (implies (and (syntaxp (not (and (equal acc ''nil)
                                      (equal sign ''nil)))))
              (equal (and$-pp-lists-aux cur lst2 acc sign)
                     (append (apply-sign-to-pp-lists
                              (and$-pp-lists-aux cur lst2 nil nil)
                              sign)
                             acc)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists-aux cur lst2 acc sign)
              :in-theory (e/d (and$-pp-lists-aux
                               and$-pp-lists
                               APPLY-SIGN-TO-PP-LISTS)
                              (pp-sum
                               --
                               type-fix))))))

  (local
   (defthm and$-pp-lists-extract-sign-and-acc
     (implies (syntaxp (not (and (equal acc ''nil)
                                 (equal sign ''nil))))
              (equal (and$-pp-lists lst1 lst2 acc sign)
                     (append (apply-sign-to-pp-lists
                              (and$-pp-lists lst1 lst2 nil nil)
                              sign)
                             acc)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists lst1 lst2 acc sign)
              :in-theory (e/d (pp-lists-to-term-p+
                               APPLY-SIGN-TO-PP-LISTS
                               and$-pp-lists)
                              (pp-sum
                               --
                               type-fix))))))

  (local
   (defthm true-list-fix-of-apply-sign-to-pp-lists
     (equal (true-list-fix (apply-sign-to-pp-lists lst sign))
            (apply-sign-to-pp-lists lst sign))
     :hints (("Goal"
              :in-theory (e/d (apply-sign-to-pp-lists) ())))))

  (local
   (defthm and$-pp-lists-aux-of-applied-sign
     (implies (booleanp sign)
              (equal (and$-pp-lists-aux cur
                                        (apply-sign-to-pp-lists lst2 sign)
                                        acc cur-sign)
                     (append (apply-sign-to-pp-lists
                              (and$-pp-lists-aux cur lst2 nil cur-sign)
                              sign)
                             acc)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists-aux cur lst2 acc cur-sign)
              :in-theory (e/d (and$-pp-lists-aux
                               APPLY-SIGN-TO-PP-LISTS) ())))))

  (local
   (defthm and$-pp-lists-of-applied-with-same-sign
     (implies (booleanp sign)
              (equal (and$-pp-lists (apply-sign-to-pp-lists lst1 sign)
                                    (apply-sign-to-pp-lists lst2 sign)
                                    acc main-sign)
                     (and$-pp-lists lst1
                                    lst2
                                    acc main-sign)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists lst1
                                     lst2
                                     acc main-sign)
              :in-theory (e/d (and$-pp-lists
                               APPLY-SIGN-TO-PP-LISTS)
                              ())))))

  (local
   (defthm pp-term-to-pp-lists-extract-sign-lemma-dummy-lemma
     (implies (and (EQUAL (APPLY-SIGN-TO-PP-LISTS x T) z)
                   (EQUAL (APPLY-SIGN-TO-PP-LISTS k T) m))
              (equal (and$-pp-lists z m acc main-sign)
                     (and$-pp-lists x
                                    k
                                    acc main-sign)))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (APPLY-SIGN-TO-PP-LISTS)
                              (and$-pp-lists
                               apply-sign-to-pp-lists
                               AND$-PP-LISTS-EXTRACT-SIGN-AND-ACC))))))

  (local
   (defthm pp-term-to-pp-lists-extract-sign-lemma-dummy-lemma-2
     (implies (and (EQUAL (PP-TERM-TO-PP-LISTS (cadr x) T)
                          (APPLY-SIGN-TO-PP-LISTS a T))
                   (EQUAL (PP-TERM-TO-PP-LISTS (caddr z) T)
                          (APPLY-SIGN-TO-PP-LISTS b T))
                   (pp-lists-p a)
                   (pp-lists-p b)
                   (pp-lists-p lst-x))
               (EQUAL
                (merge-sorted-pp-lists
                 (merge-sorted-pp-lists (PP-TERM-TO-PP-LISTS (cadr x) T)
                                               (PP-TERM-TO-PP-LISTS (caddr z) T))
                 lst-x)
                (APPLY-SIGN-TO-PP-LISTS
                 (merge-sorted-pp-lists
                  (merge-sorted-pp-lists
                   a b)
                  (APPLY-SIGN-TO-PP-LISTS lst-x T))
                 T)))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d ()
                              (and$-pp-lists
                               apply-sign-to-pp-lists
                               AND$-PP-LISTS-EXTRACT-SIGN-AND-ACC))))))

  (local
   (defthm pp-term-to-pp-lists-extract-sign-lemma-dummy-lemma-3
     (implies (and (EQUAL (PP-TERM-TO-PP-LISTS (cadr x) T)
                          (APPLY-SIGN-TO-PP-LISTS a T))
                   (pp-lists-p a)
                   (booleanp sign))
               (EQUAL
                (merge-sorted-pp-lists `((,sign '1))
                                              (PP-TERM-TO-PP-LISTS (CADR x) T))
                (APPLY-SIGN-TO-PP-LISTS (merge-sorted-pp-lists
                                         `((,(not sign) '1))
                                         a)
                                        T)))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (merge-sorted-pp-lists-simple-of-apply-sign-reverse)
                              (and$-pp-lists
                               merge-sorted-pp-lists-simple-of-apply-sign
                               apply-sign-to-pp-lists
                               AND$-PP-LISTS-EXTRACT-SIGN-AND-ACC))))))

  (local
   (defthm pp-term-to-pp-lists-extract-sign-lemma-dummy-lemma-4
     (implies (and (EQUAL (PP-TERM-TO-PP-LISTS (cadr x) nil)
                          (APPLY-SIGN-TO-PP-LISTS a T))
                   (pp-lists-p a))
               (EQUAL
                (merge-sorted-pp-lists `((t '1))
                                              (PP-TERM-TO-PP-LISTS (CADR x) nil))
                (APPLY-SIGN-TO-PP-LISTS (merge-sorted-pp-lists
                                         `((nil '1))
                                         a)
                                        T)))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (merge-sorted-pp-lists-simple-of-apply-sign-reverse)
                              (and$-pp-lists
                               merge-sorted-pp-lists-simple-of-apply-sign
                               apply-sign-to-pp-lists
                               AND$-PP-LISTS-EXTRACT-SIGN-AND-ACC))))))

  (local
   (defthmd pp-term-to-pp-lists-extract-sign-lemma
     (implies (and (booleanp sign)
                   (booleanp s2))
              (equal (pp-term-to-pp-lists term sign)
                     (apply-sign-to-pp-lists
                      (pp-term-to-pp-lists term (xor s2 sign))
                      s2)))
     :otf-flg t
     :hints (("goal"
              :do-not-induct t
              :induct (pp-term-to-pp-lists term sign)
              :in-theory (e/d (pp-term-to-pp-lists
                               APPLY-SIGN-TO-PP-LISTS)
                              (pp-sum
                               --
                               type-fix)))
             ("subgoal *1/2"
              :in-theory (e/d (pp-term-to-pp-lists)
                              (pp-sum
                               and$-pp-lists-of-applied-with-same-sign
                               --
                               type-fix))
              :use ((:instance and$-pp-lists-of-applied-with-same-sign
                               (lst1 (pp-term-to-pp-lists (cadr (ex-from-rp term))
                                                          t))
                               (lst2 (pp-term-to-pp-lists (caddr (ex-from-rp term))
                                                          t))
                               (sign t)
                               (acc nil)
                               (main-sign nil)))))))

  (local
   (defthm pp-term-to-pp-lists-extract-sign
     (implies (and (syntaxp (not (and (equal sign ''nil))))
                   (booleanp sign))
              (equal (pp-term-to-pp-lists term sign)
                     (apply-sign-to-pp-lists
                      (pp-term-to-pp-lists term nil)
                      sign)))
     :otf-flg t
     :hints (("goal"
              :do-not-induct t
              :use ((:instance pp-term-to-pp-lists-extract-sign-lemma
                               (s2 t)))
              :in-theory (e/d (APPLY-SIGN-TO-PP-LISTS)
                              (pp-sum
                               --
                               type-fix)))))))

(local
 (defthm and$-pp-lists-aux-is-correct-lemma-2
   (implies (and (bitp x)
                 (bitp (pp-sum (-- x) y))
                 (not (bitp y))
                 (integerp y))
            (and (equal x 1)
                 (equal y 2)))
   :rule-classes :forward-chaining))

(local
 (defthm and$-pp-lists-aux-is-correct
   (implies (and (pp-flatten-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (pp-lists-p lst2)
                 (bit-listp (rp-evlt-lst cur a))
                 (true-listp cur)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a)))
            (equal (rp-evlt (pp-lists-to-term-p+ (and$-pp-lists-aux cur lst2 nil nil)) a)
                   (times$ (rp-evlt (pp-lists-to-term-and$ cur) a)
                           (rp-evlt (pp-lists-to-term-p+ lst2) a))))
   :hints (("goal"
            :induct (and$-pp-lists-aux cur lst2 nil nil)
            :do-not-induct t
            :expand (#|(pp-lists-to-term (cons (cons (car (car lst2))
                     (append cur (cdr (car lst2))))
                     (and$-pp-lists-aux cur (cdr lst2)
                     nil nil)))||#)
            :in-theory (e/d (and$-pp-lists-aux
                             pp-lists-to-term-p+
                             and$-is-times
                             pp-lists-to-term-and$)
                            (pp-sum
                             binar-and-abs-is-and$-2
                             and$
                             times$
                             --
                             pp-sum
                             type-fix
                             bitp
                             true-listp))))))

(local
 (defthm and$-pp-lists-is-correct
   (implies (and (pp-flatten-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (pp-lists-p lst1)
                 (pp-lists-p lst2)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a))
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a)))
            (equal (rp-evlt (pp-lists-to-term-p+ (and$-pp-lists lst1 lst2 nil nil)) a)
                   (times$ (rp-evlt (pp-lists-to-term-p+ lst1) a)
                           (rp-evlt (pp-lists-to-term-p+ lst2) a))))
   :hints (("goal"
            :induct (and$-pp-lists lst1 lst2 nil nol)
            :do-not-induct t
            :in-theory (e/d (pp-lists-to-term-p+
                             and$-is-times
                             pp-lists-to-term-and$
                             and$-pp-lists)
                            (pp-sum
                             times$
                             binar-and-abs-is-and$-2
                             and$
                             --
                             bitp
                             true-listp))))))

;; MAIN LEMMA1.
(defthm rp-evlt_of_pp-lists-to-term_of_pp-term-to-pp-lists
  (implies (and (pp-flatten-formula-checks state)
                (pp-term-p term)
                (booleanp sign)
                (valid-sc term a)
                (rp-evl-meta-extract-global-facts))
           (equal (rp-evlt (pp-lists-to-term-p+
                           (pp-term-to-pp-lists term sign))
                          a)
                  (if sign
                      (-- (rp-evlt term a))
                    (rp-evlt term a))))
  :hints (("goal"
           :do-not-induct t
           :induct (pp-term-to-pp-lists term sign)
           :in-theory (e/d (pp-term-to-pp-lists
                            not$-to-pp-sum
                            or$-to-pp-sum
                            binary-xor-to-pp-sum
                            binary-?-to-pp-sum
                            ---of-pp-sum
                            pp-lists-to-term-and$
                            pp-lists-to-term-p+
                            APPLY-SIGN-TO-PP-LISTS
                            len)
                           (--
                            p+
                            valid-sc
                            and$
                            bitp
                            or$
                            type-fix
                            (:REWRITE VALID-SC-EX-FROM-RP-2)
                            (:DEFINITION EVAL-AND-ALL)
                            valid-sc
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION RP-TERMP)
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:META ACL2::MV-NTH-CONS-META)
                            (:REWRITE PP-LISTS-P-IMPLIES-TRUE-LISTP)
                            (:REWRITE DEFAULT-CAR)
                            type-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm eval-of-sort-pp-flatten-main-is-correct
  (implies (and (pp-flatten-formula-checks state)
                (valid-sc term a)
                (rp-evl-meta-extract-global-facts))
           (equal (rp-evlt (flatten-pp-main term) a)
                  (rp-evlt term a)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (flatten-pp-main
                            eval-of---1)
                           (floor
                            pp-term-p
                            bitp
                            EVAL-OF----
                            --
                            pp-sum)))))

