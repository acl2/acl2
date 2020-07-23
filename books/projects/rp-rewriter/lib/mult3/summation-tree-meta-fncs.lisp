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

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(include-book "pp-flatten-meta-fncs")

(include-book "std/util/defines" :dir :system)

(include-book "sum-merge-fncs")

(local
 (in-theory (disable +-IS-SUM)))

#|(define create-list-instance-single (e)
  :returns (res rp-termp :hyp (rp-termp e))
  (cond ((equal e ''0)
         ''nil)
        (t
         `(list ,e))))||#

;; (define list-instance-to-lst (term)
;;   :inline t
;;   (case-match term
;;     (('list . lst)
;;      lst)
;;     (''nil

#|(defconst *a*
  '((in1 . 1231231) (in2 . 131321)))||#

(define clean-pp-args-cond (s c-lst)
  (or nil
      (and (equal s ''nil)
           (or (atom c-lst)
               (atom (cdr c-lst))))))

(local
 (defthm ex-from-rp-loose-is-rp-termp
   (implies (rp-termp term)
            (equal (ex-from-rp-loose term)
                   (ex-from-rp term)))
   :hints (("Goal"
            :induct (ex-from-rp-loose term)
            :do-not-induct t
            :in-theory (e/d (is-rp
                             EX-FROM-RP-LOOSE
                             EX-FROM-RP
                             is-rp-loose) ())))))

(define get-c-args ((c))
  :inline t
  :returns (mv (hash-code integerp)
               (s-args rp-termp
                       :hyp (rp-termp c))
               (pp-args rp-termp
                        :hyp (rp-termp c))
               (c-arg-lst rp-term-listp
                          :hyp (rp-termp c))
               (valid symbolp))
  (b* ((c (ex-from-rp-loose c)))
    (case-match c
      (('c ('quote hash-code) s pp ('list . c-lst))
       (mv (ifix hash-code) s pp c-lst 'c))
      (('c ('quote hash-code) s pp ''nil)
       (mv (ifix hash-code) s pp nil 'c))
      (''0
       (mv 0 ''nil ''nil nil 'c))
      (& (mv 0 ''nil ''nil nil nil)))))

(progn
  (define pp-instance-hash (e)
    :returns (hash integerp)
    :inline t
    (case-match e
      (('and-list ('quote hash) &)
       (ifix hash))
      (('-- ('and-list ('quote hash) &))
       (- (ifix hash)))
      (''1
       1)
      (''-1
       -1)
      (& 0)))

  (defwarrant pp-instance-hash$inline)

  (define pp-lst-hash (pp-lst)
    ;;:inline t
    :returns (hash-code integerp)
    ;;(loop$ for x in pp-lst sum (pp-instance-hash x))
    (if (atom pp-lst)
        0
      (+ (pp-instance-hash (car pp-lst))
         (pp-lst-hash (cdr pp-lst)))))

  (defwarrant pp-lst-hash)

  (define calculate-pp-hash (pp)
    :returns (hash-code integerp)
    :inline t
    (case-match pp
      (('list . pp-lst)
       ;;(let ((len (len pp-lst))) (* len len))
       (pp-lst-hash pp-lst)
       )
      (& 0)))

  (defwarrant calculate-pp-hash$inline)

  (define get-hash-code-of-single-s (s)
    :returns (hash-code integerp)
    :inline t
    (b* ((s (ex-from-rp/--loose s)))
      (case-match s
        (('s ('quote hash-code) & &)
         (ifix hash-code))
        (''0
         0)
        (&
         (progn$ (hard-error
                  'get-hash-code-of-single-s
                  "unrecognized s instance in get-hash-code-of-s:~p0 ~%"
                  (list (cons #\0 s)))
                 0)))))

  (defwarrant get-hash-code-of-single-s$inline)

  (define get-hash-code-of-s-lst (s-lst)
    :returns (hash-code integerp)
    :inline t
    ;;(loop$ for x in s-lst sum (get-hash-code-of-single-s x))
    (if (atom s-lst)
        0
      (+ (get-hash-code-of-single-s (car s-lst))
         (get-hash-code-of-s-lst (cdr s-lst)))))

  (defwarrant get-hash-code-of-s-lst$inline)

  (define get-hash-code-of-s (s)
    :returns (hash-code integerp)
    :inline t
    (case-match s
      (('list . s-lst)
       (get-hash-code-of-s-lst s-lst))
      (& 0)))

  (defwarrant get-hash-code-of-s$inline)

  (define get-hash-code-of-single-c (c)
    :returns (hash-code integerp)
    :inline t
    (b* ((c (ex-from-rp/--loose c)))
      (case-match c
        (('c ('quote hash-code) & & &)
         (ifix hash-code))
        (''0
         0)
        (& (progn$ (hard-error
                    'get-hash-code-of-single-c
                    "unrecognized c instance:~p0 ~%"
                    (list (cons #\0 c)))
                   0)))))

  (defwarrant get-hash-code-of-single-c$inline)

  (define get-hash-code-of-c-lst (c-lst)
    :returns (hash-code integerp)
    :inline t
    ;;(loop$ for x in s-lst sum (get-hash-code-of-single-c x))
    (if (atom c-lst)
        0
      (+ (get-hash-code-of-single-c (car c-lst))
         (get-hash-code-of-c-lst (cdr c-lst)))))

  (define get-hash-code-of-c (c)
    :returns (hash-code integerp)
    :inline t
    (case-match c
      (('list . c-lst)
       (get-hash-code-of-c-lst c-lst))
      (& 0)))

  (define calculate-s-hash (pp c)
    :returns (hash-code integerp)
;:inline t
    (+ (calculate-pp-hash pp)
       (* 2 (get-hash-code-of-c c)))
    #|(* 4 (+ (* 2 (calculate-pp-hash pp))
    (get-hash-code-of-c c)))||#
    )

  (define calculate-c-hash (s pp c)
    :returns (hash-code integerp)
    (+ (get-hash-code-of-s s)
       (calculate-pp-hash pp)
       (* 2 (get-hash-code-of-c c)))))

(define is-rp-bitp (term)
  (case-match term
    (('rp ''bitp &)
     t)))

(local
 (in-theory (disable rp-termp)))

(local
 (defthm measure-lemma-loose1
   (IMPLIES (AND
             (CONSP (EX-FROM-RP-LOOSE MAX-TERM))
             (CONSP (CDR (EX-FROM-RP-LOOSE MAX-TERM)))
             (NOT (CDDR (EX-FROM-RP-LOOSE MAX-TERM))))
            (O< (CONS-COUNT (CADR (EX-FROM-RP-LOOSE MAX-TERM)))
                (CONS-COUNT MAX-TERM)))
   :hints (("Goal"
            :induct (EX-FROM-RP-LOOSE MAX-TERM)
            :do-not-induct t
            :in-theory (e/d (EX-FROM-RP-LOOSE
                             measure-lemmas)
                            ((:REWRITE MEASURE-LEMMA1)
                             (:REWRITE CONS-COUNT-ATOM)

                             (:REWRITE DEFAULT-CDR)
                             (:REWRITE MEASURE-LEMMA6-5)
                             (:DEFINITION EX-FROM-RP)
                             (:REWRITE MEASURE-LEMMA1-2)))))))
(local
 (defthm measure-lemma-loose2
   (IMPLIES (AND  (CONSP (EX-FROM-RP-LOOSE MAX-TERM))
                  (CONSP (CDR (EX-FROM-RP-LOOSE MAX-TERM)))
                  (CONSP (CDDR (EX-FROM-RP-LOOSE MAX-TERM)))
                  (CONSP (CDDDR (EX-FROM-RP-LOOSE MAX-TERM)))
                  (CONSP (CDDDDR (EX-FROM-RP-LOOSE MAX-TERM)))
                  (NOT (CDR (CDDDDR (EX-FROM-RP-LOOSE MAX-TERM)))))
            (O< (CONS-COUNT (CDR (CAR (CDDDDR (EX-FROM-RP-LOOSE MAX-TERM)))))
                (CONS-COUNT MAX-TERM)))
   :hints (("Goal"
            :induct (EX-FROM-RP-LOOSE MAX-TERM)
            :do-not-induct t
            :in-theory (e/d (EX-FROM-RP-LOOSE
                             measure-lemmas)
                            ((:REWRITE DEFAULT-CDR)
                             (:REWRITE EX-FROM-RP-LOOSE-IS-RP-TERMP)
                             (:DEFINITION RP-TERMP)
                             (:REWRITE MEASURE-LEMMA1-2)
                             (:DEFINITION EX-FROM-RP)
                             (:REWRITE MEASURE-LEMMA1)))))))

(local
 (defthm measure-lemma-loose3
   (IMPLIES (AND  (CONSP (EX-FROM-RP-LOOSE MAX-TERM))
                  (CONSP (CDR (EX-FROM-RP-LOOSE MAX-TERM)))
                  (CONSP (CDDR (EX-FROM-RP-LOOSE MAX-TERM)))
                  (CONSP (CDDDR (EX-FROM-RP-LOOSE MAX-TERM)))
                  (CONSP (CDDDDR (EX-FROM-RP-LOOSE MAX-TERM)))
                  (NOT (CDR (CDDDDR (EX-FROM-RP-LOOSE MAX-TERM)))))
            (O< (CONS-COUNT (CDR (CADDDR (EX-FROM-RP-LOOSE MAX-TERM))))
                (CONS-COUNT MAX-TERM)))
   :hints (("Goal"
            :induct (EX-FROM-RP-LOOSE MAX-TERM)
            :do-not-induct t
            :in-theory (e/d (EX-FROM-RP-LOOSE
                             measure-lemmas)
                            ((:REWRITE DEFAULT-CDR)
                             (:REWRITE MEASURE-LEMMA1)
                             (:REWRITE MEASURE-LEMMA1-2)
                             (:DEFINITION EX-FROM-RP)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE ACL2::O<=-O-FINP-DEF)
                             ))))))

(local
 (defthm measure-lemma-loose4
   (IMPLIES (AND  (CONSP (EX-FROM-RP-LOOSE MAX-TERM))
                  (CONSP (CDR (EX-FROM-RP-LOOSE MAX-TERM)))
                  (CONSP (CDDR (EX-FROM-RP-LOOSE MAX-TERM)))
                  (CONSP (CDDDR (EX-FROM-RP-LOOSE MAX-TERM)))
                  (CONSP (CDDDDR (EX-FROM-RP-LOOSE MAX-TERM)))
                  (NOT (CDR (CDDDDR (EX-FROM-RP-LOOSE MAX-TERM)))))
            (O< (CONS-COUNT (CDR (CADDR (EX-FROM-RP-LOOSE MAX-TERM))))
                (CONS-COUNT MAX-TERM)))
   :hints (("Goal"
            :induct (EX-FROM-RP-LOOSE MAX-TERM)
            :do-not-induct t
            :in-theory (e/d (EX-FROM-RP-LOOSE
                             measure-lemmas)
                            ((:REWRITE DEFAULT-CDR)
                             (:REWRITE MEASURE-LEMMA1)
                             (:REWRITE MEASURE-LEMMA1-2)
                             (:DEFINITION EX-FROM-RP)

                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE ACL2::O<=-O-FINP-DEF)

                             ))))))

(local
 (in-theory (disable EX-FROM-RP
                     (:DEFINITION ACL2::APPLY$-BADGEP)
                     (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                     (:DEFINITION SUBSETP-EQUAL)
                     (:DEFINITION MEMBER-EQUAL)
                     (:REWRITE
                      ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                     (:DEFINITION RP-TERM-LISTP)
                     INCLUDE-FNC)))

(acl2::defines
 get-max-min-val
 :flag-defthm-macro defthm-get-min-max-val
 :flag-local nil
 :prepwork ((local
             (in-theory (e/d (measure-lemmas)
                             (MEASURE-LEMMA1
                              MEASURE-LEMMA1-2
                              EX-FROM-RP-LOOSE-IS-RP-TERMP
                              (:REWRITE ACL2::O-P-O-INFP-CAR)
                              (:REWRITE DEFAULT-CAR)
                              NOT-INCLUDE-RP)))))

 :verify-guards nil
 (define get-max-min-val (term)
   :measure (cons-count term)
   :returns (mv  (max-val integerp)
                 (min-val integerp)
                 (valid booleanp))
   (b* (((when (is-rp-bitp term)) (mv 1 0 t))
        (term (ex-from-rp-loose term)))
     (case-match term
       (('c & s pp c)
        (b* (((mv s-max-val s-min-val s-valid)
              (case-match s
                (('list . lst) (get-max-min-val-lst lst))
                (''nil (mv 0 0 t))
                (& (mv 0 0 nil))))
             ((mv pp-max-val pp-min-val pp-valid)
              (case-match pp
                (('list . lst) (get-max-min-val-lst lst))
                (''nil (mv 0 0 t))
                (& (mv 0 0 nil))))
             ((mv c-max-val c-min-val c-valid)
              (case-match c
                (('list . lst) (get-max-min-val-lst lst))
                (''nil (mv 0 0 t))
                (& (mv 0 0 nil))))
             ((unless (and s-valid
                           pp-valid
                           c-valid))
              (mv 0 0 nil)))
          (mv (floor (+ s-max-val pp-max-val c-max-val) 2)
              (floor (+ s-min-val pp-min-val c-min-val) 2)t)))
       (('s & & &) (mv 1 0 t))
       (''1 (mv 1 1 t))
       (('and-list & &) (mv 1 0 t))
       (('-- n)
        (b* (((mv max-val min-val valid)
              (get-max-min-val n)))
          (mv (- min-val) (- max-val) valid)))
       (& (mv 0 0 nil)))))
 (define get-max-min-val-lst (lst)
   :measure (cons-count lst)
   :returns (mv (max-val integerp)
                (min-val integerp)
                (valid booleanp))
   (if (atom lst)
       (mv 0 0 t)
     (b* (((mv max-val1 min-val1 valid1)
           (get-max-min-val (car lst)))
          ((unless valid1)
           (mv max-val1 min-val1 valid1))
          ((mv max-val2 min-val2 valid2)
           (get-max-min-val-lst (cdr lst))))
       (mv (+ max-val1 max-val2) (+ min-val1 min-val2) valid2))))

 ///
 (verify-guards get-max-min-val-lst)
 )

#|(acl2::defines
 get-max-val
 :flag-defthm-macro defthm-get-max-val
 :flag-local nil
 :prepwork ((local
             (in-theory (enable measure-lemmas))))

 :verify-guards nil
 (define get-max-val (max-term)
   :measure (cons-count max-term)
   :returns (mv  (max-val integerp)
                 (valid booleanp))
   (b* (((when (is-rp-bitp max-term)) (mv 1 t))
        (term (ex-from-rp-loose max-term)))
     (case-match term
       (('c & s pp c)
        (b* (((mv s-max-val s-valid)
              (case-match s
                (('list . lst) (get-max-val-lst lst))
                (''nil (mv 0 t))
                (& (mv 0 nil))))
             ((mv pp-max-val pp-valid)
              (case-match pp
                (('list . lst) (get-max-val-lst lst))
                (''nil (mv 0 t))
                (& (mv 0 nil))))
             ((mv c-max-val c-valid)
              (case-match c
                (('list . lst) (get-max-val-lst lst))
                (''nil (mv 0 t))
                (& (mv 0 nil))))
             ((unless (and s-valid
                           pp-valid
                           c-valid))
              (mv 0 nil)))
          (mv (floor (+ s-max-val pp-max-val c-max-val) 2) t)))
       (('s & & &) (mv 1 t))
       (''1 (mv 1 t))
       (('and-list & &) (mv 1 t))
       (('-- n)
        (b* (((mv min-val valid)
              (get-min-val n)))
          (mv (- min-val) valid)))
       (& (mv 0 nil)))))
 (define get-max-val-lst (max-lst)
   :measure (cons-count max-lst)
   :returns (mv (max-val integerp)
                (valid booleanp))
   (if (atom max-lst)
       (mv 0 t)
     (b* (((mv max-val1 valid1)
           (get-max-val (car max-lst)))
          ((unless valid1)
           (mv max-val1 valid1))
          ((mv max-val2 valid2)
           (get-max-val-lst (cdr max-lst))))
       (mv (+ max-val1 max-val2) valid2))))
 (define get-min-val (min-term)
   :measure (cons-count min-term)
   :returns (mv (min-val integerp)
                (valid booleanp))
   (b* (((when (is-rp-bitp min-term)) (mv 0 t))
        (term (ex-from-rp-loose min-term)))
     (case-match term
       (('c & s pp c)
        (b* (((mv s-min-val s-valid)
              (case-match s
                (('list . lst) (get-min-val-lst lst))
                (''nil (mv 0 t))
                (& (mv 0 nil))))
             ((mv pp-min-val pp-valid)
              (case-match pp
                (('list . lst) (get-min-val-lst lst))
                (''nil (mv 0 t))
                (& (mv 0 nil))))
             ((mv c-min-val c-valid)
              (case-match c
                (('list . lst) (get-min-val-lst lst))
                (''nil (mv 0 t))
                (& (mv 0 nil))))
             ((unless (and s-valid
                           pp-valid
                           c-valid))
              (mv 0 nil)))
          (mv (floor (+ s-min-val pp-min-val c-min-val) 2) t)))
       (('s & & &) (mv 0 t))
       (''1 (mv 1 t))
       (('and-list & &) (mv 0 t))
       (('-- n)
        (b* (((mv max-val valid)
              (get-max-val n)))
          (mv (- max-val) valid)))
       (& (mv 0 nil)))))
 (define get-min-val-lst (min-lst)
   :returns (mv (min-val integerp)
                (valid booleanp))
   :measure (cons-count min-lst)
   (if (atom min-lst)
       (mv 0 t)
     (b* (((mv min-val1 valid1)
           (get-min-val (car min-lst)))
          ((unless valid1)
           (mv min-val1 valid1))
          ((mv min-val2 valid2)
           (get-min-val-lst (cdr min-lst))))
       (mv (+ min-val1 min-val2) valid2))))
 ///
 (verify-guards get-min-val-lst))||#

#|(skip-proofs
 (acl2::defines
  is-c-bitp-traverse-aux
  (define is-c-bitp-traverse-aux (single-c remainder)
    (case-match single-c
      (('c & s pp c)
       (b* ((pp-len (case-match pp (('list . lst) (len lst)) (& 0)))
            (s-len (case-match s (('list . lst) (len lst)) (& 0)))
            #|((when (> s-len 0))
            -1)||#
            (remainder (- remainder (+ pp-len s-len))))
         (if (< remainder 0)
             remainder
           (case-match c
             (('list . lst)
              (is-c-bitp-traverse-aux-lst lst (1+ (* 2 remainder))))
             (& remainder)))))
      (('rp ''bitp &)
       (- remainder 1))
      (& (progn$
          (hard-error 'is-c-bitp-traverse-aux
                      "Unexpected c form ~p0 ~%"
                      (list (cons #\0 single-c)))
          -1))))

  (define is-c-bitp-traverse-aux-lst (lst remainder)
    (if (atom lst)
        remainder
      (is-c-bitp-traverse-aux-lst (cdr lst)
                                  (is-c-bitp-traverse-aux (car lst) remainder))))))||#

#|(define is-c-bitp-traverse (single-c)
  (declare (ignorable single-c))
  (and t (>= (is-c-bitp-traverse-aux single-c 3) 0)))||#

(define is-c-bitp-traverse (single-c)
  :returns (res booleanp)
  (b* (((mv max-val min-val valid)
        (get-max-min-val single-c)))
    (and
     valid
     (equal min-val 0)
     (equal max-val 1))))

;; a b c e
;; a b c d e

(progn
  (define pp-lst-subsetp (pp-lst1 pp-lst2)
    :measure (+ (cons-count pp-lst1)
                (cons-count pp-lst2))
    :prepwork ((local
                (in-theory (enable measure-lemmas))))
    (b* (((when (atom pp-lst1)) t)
         ((when (atom pp-lst2)) (atom pp-lst1))
         (cur1 (car pp-lst1))
         (cur2 (car pp-lst2))
         ((mv order equals) (pp-order cur1 cur2)))
      (cond (equals
             (pp-lst-subsetp (cdr pp-lst1) (cdr pp-lst2)))
            (order nil)
            (t (pp-lst-subsetp pp-lst1 (cdr pp-lst2))))))

  (define pp-subsetp (pp1 pp2)
    (b* ((pp1-lst (list-to-lst pp1))
         (pp2-lst (list-to-lst pp2)))
      (pp-lst-subsetp pp1-lst pp2-lst))))

(local
 (defthm rp-term-listp-of-cons
   (equal (rp-term-listp (cons a b))
          (and (rp-termp a)
               (rp-term-listp b)))
   :hints (("Goal"
            :in-theory (e/d (rp-term-listp) ())))))

(local
 (defthm rp-termp-of--
   (iff (rp-termp (list '-- a))
        (rp-termp a))
   :hints (("Goal"
            :expand (rp-termp (list '-- a))
            :in-theory (e/d () ())))))

(local
 (defthm rp-termp-of-list
   (iff (rp-termp (cons 'list rest))
        (rp-term-listp rest))
   :hints (("Goal"
            :expand (rp-termp (cons 'list rest))
            :in-theory (e/d () ())))))

(local
 (defthm rp-termp-of-s-and-c
   (and (iff (rp-termp (cons 's rest))
             (rp-term-listp rest))
        (iff (rp-termp (cons 'c rest))
             (rp-term-listp rest)))
   :hints (("Goal"
            :expand ((rp-termp (cons 's rest))
                     (rp-termp (cons 'c rest)))
            :in-theory (e/d () ())))))

(local
 (defthm rp-termp-car-cddddr
   (IMPLIES (AND (RP-TERMP TERM)
                 (CONSP TERM)
                 (NOT (QUOTEP TERM))
                 (CONSP (CDR TERM))
                 (CONSP (CDDR TERM))
                 (CONSP (CDDDR TERM))
                 (CONSP (CDDdDR TERM)))
            (RP-TERMP (CAr (cDdDDR TERM))))
   :hints (("Goal"
            :do-not-induct t
            :expand (RP-TERMP TERM)
            :in-theory (e/d (rp-termp
                             is-rp
                             rp-term-listp)
                            ())))))

(local
 (defthm rp-termp-of-consed
   (equal (rp-termp (cons sym rest))
          (let ((term  (cons sym rest)))
            (COND ((ATOM TERM) (AND (SYMBOLP TERM) TERM))
                  ((EQ (CAR TERM) 'QUOTE)
                   (AND (CONSP (CDR TERM))
                        (NULL (CDR (CDR TERM)))))
                  ((EQ (CAR TERM) 'RP)
                   (AND (IS-RP TERM)
                        (RP-TERMP (CADDR TERM))))
                  ((EQ (CAR TERM) 'FALIST)
                   (AND (FALIST-CONSISTENT TERM)
                        (RP-TERMP (CADDR TERM))))
                  (T (AND (SYMBOLP (CAR TERM))
                          (CAR TERM)
                          (RP-TERM-LISTP (CDR TERM)))))))
   :hints (("Goal"
            :expand (rp-termp (cons sym rest))
            :in-theory (e/d () ())))))

(progn
  (define compress-s-c-pass-pp-lst (pp1-lst pp2-lst under-s)
    :measure (+ (cons-count pp1-lst)
                (cons-count pp2-lst))
    :prepwork ((local
                (in-theory (e/d (measure-lemmas)
                                ((:REWRITE MEASURE-LEMMA1)
                                 (:REWRITE DEFAULT-CAR)
                                 (:REWRITE ACL2::O-P-O-INFP-CAR)
                                 (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)

                                 (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                                 (:TYPE-PRESCRIPTION RP-TERMP)
                                 (:TYPE-PRESCRIPTION RP-EQUAL)
                                 (:REWRITE EX-FROM-RP-LOOSE-IS-RP-TERMP)
                                 (:REWRITE MEASURE-LEMMA1-2)
                                 (:DEFINITION RP-EQUAL))))))
    :returns (mv (res-pp1-lst rp-term-listp
                              :hyp (rp-term-listp pp1-lst))
                 (res-pp2-lst rp-term-listp
                              :hyp (and (rp-term-listp pp1-lst)
                                        (rp-term-listp pp2-lst)))
                 (changed booleanp))
    (b* (((when (or (atom pp1-lst)
                    (atom pp2-lst)))
          (mv pp1-lst pp2-lst nil))
         (c1 (car pp1-lst))
         (c2 (car pp2-lst))
         ((mv c1-abs c1-signed)
          (case-match c1 (('-- c1) (mv c1 t)) (& (mv c1 nil))))
         ((mv c2-abs c2-signed)
          (case-match c2 (('-- c2) (mv c2 t)) (& (mv c2 nil))))
         ((mv to-pass passable)
          (cond ((and under-s (rp-equal c1 c2)
                      (not c1-signed) (not c2-signed))
                 (mv `(-- ,c1) t))
                ((and (not under-s)
                      (rp-equal c1-abs c2-abs)
                      c1-signed (not c2-signed))
                 (mv c1 t))
                (t (mv nil nil))))
         ((when passable)
          (b* (((mv pp1-lst-rest pp2-lst-rest &)
                (compress-s-c-pass-pp-lst (cdr pp1-lst) (cdr pp2-lst) under-s)))
            (mv pp1-lst-rest (cons to-pass pp2-lst-rest) t)))
         ((mv pp-order &)
          (pp-order (ex-from-rp/--loose c1) (ex-from-rp/--loose c2))))
      (if pp-order
          (b* (((mv pp1-lst-rest pp2-lst-rest rest-changed)
                (compress-s-c-pass-pp-lst (cdr pp1-lst) pp2-lst under-s)))
            (mv (cons-with-hint c1 pp1-lst-rest pp1-lst)
                pp2-lst-rest rest-changed))
        (b* (((mv pp1-lst-rest pp2-lst-rest rest-changed)
              (compress-s-c-pass-pp-lst pp1-lst (cdr pp2-lst) under-s)))
          (mv pp1-lst-rest (cons-with-hint c2 pp2-lst-rest pp2-lst) rest-changed)))))

  (define compress-s-c-pass-pp (pp1 pp2 under-s)
    :returns (mv (res-pp1 rp-termp :hyp (rp-termp pp1))
                 (res-pp2 rp-termp :hyp (and (rp-termp pp1)
                                             (rp-termp pp2)))
                 (changed booleanp))
    (b* ((pp1-lst (list-to-lst pp1))
         (pp2-lst (list-to-lst pp2))
         ((mv pp1-lst pp2-lst changed)
          (compress-s-c-pass-pp-lst pp1-lst pp2-lst under-s)))
      (if changed
          (mv (create-list-instance pp1-lst) (create-list-instance pp2-lst) t)
        (mv pp1 pp2 nil))))

  (define compress-s-c (term &key (limit '(expt 2 30)))
    :measure (nfix limit)
    :guard (natp limit)
    :prepwork ((local
                (in-theory (enable measure-lemmas))))
    :returns (res-term rp-termp :hyp (rp-termp term))
    (b* (((when (zp limit)) term)
         (term-orig term)
         (term (ex-from-rp-loose term)))
      (case-match term
        (('s hash-code pp ('list single-c))
         (b* ((single-c (ex-from-rp-loose single-c)))
           (case-match single-c
             (('c c-hash ''nil c-pp c-arg)
              (b* (((mv pp c-pp changed)
                    (compress-s-c-pass-pp pp c-pp t))
                   ((unless changed) term-orig)
                   (new-single-c `(c ,c-hash 'nil ,c-pp ,c-arg))
                   (new-single-c (compress-s-c new-single-c :limit (1- limit) )))
                `(s ,hash-code  ,pp (list ,new-single-c))))
             (& term-orig))))
        (('c hash-code ''nil pp1 ('list single-c))
         (b* ((single-c (ex-from-rp-loose single-c)))
           (case-match single-c
             (('c c-hash ''nil c-pp c2)
              (b* (((mv pp1 c-pp changed)
                    (compress-s-c-pass-pp pp1 c-pp nil))
                   ((unless changed) term-orig)
                   (new-single-c `(c ,c-hash 'nil ,c-pp ,c2))
                   (new-single-c (compress-s-c new-single-c :limit (1- limit))))
                `(c ,hash-code 'nil ,pp1 (list ,new-single-c))))
             (& term-orig))))
        (& term-orig))))

  (define decompress-s-c (term &key (limit '(expt 2 30)))
    :measure (nfix limit)
    :guard (natp limit)
    :returns (mv (res-term)
                 (coughed-term))
    (b* (((when (zp limit)) (mv term ''nil))
         (term-orig term)
         (term (ex-from-rp-loose term)))
      (case-match term
        (('s & pp ('list single-c))
         (b* (((mv single-c coughed-pp)
               (decompress-s-c single-c :limit (1- limit)))
              (pp (pp-sum-merge pp coughed-pp))
              (pp (s-fix-args pp))
              (c (create-list-instance (list single-c))))
           (mv `(s ',(calculate-s-hash pp c) ,pp ,c)
               ''nil)))
        (('c & ''nil pp ('list single-c))
         (b* (((mv single-c coughed-pp)
               (decompress-s-c single-c :limit (1- limit)))
              (pp (pp-sum-merge pp coughed-pp))
              ((mv pp-coughed pp) (c-fix-pp-args pp (expt 2 30)))
              (c (create-list-instance (list single-c))))
           (mv `(c ',(calculate-c-hash ''nil pp c) 'nil ,pp ,c)
               pp-coughed)))
        (('c & ''nil pp ''nil)
         (b* (((mv pp-coughed pp) (c-fix-pp-args pp (expt 2 30)))
              (c ''nil))
           (mv `(c ',(calculate-c-hash ''nil pp c) 'nil ,pp ,c)
               pp-coughed)))
        (& (mv term-orig ''nil))))
    ///

    (acl2::defret
     rp-termp-of-<fn>
     :hyp (rp-termp term)
     (and (rp-termp res-term)
          (rp-termp coughed-term)))))

#|(define s-pattern1-success ()
  t)||#

#|(profile 's-pattern1-success)||#

#|(define s-pattern1-reduce (pp c)
  ;; sometimes (s pp (c pp (c rest))) can be reduced to
  ;; (s pp (c rest)). For example when a multiplier's output bit is repeated
  ;; more than necessary such as the 7th output bit of a 3x3 signed
  ;; multiplication.
  (case-match c
    (('list single-c)
     (b* ((single-c (ex-from-rp-loose single-c)))
       (case-match single-c
         (('c & ''nil c-pp &)
          (b* (((unless (equal pp c-pp))
                ;; A cheap condition check for pattern1
                (mv pp c nil))
               (compressed (compress-s-c `(s '0 ,pp ,c))))
            (case-match compressed
              (('s & ''nil ('list ('c & ''nil ''nil ('list inner-single-c))))
               (b* (((mv max-val min-val valid)
                     (get-max-min-val inner-single-c))
                    ((unless (and valid
                                  (equal max-val 0)
                                  (equal min-val -1)))
                     (mv pp c nil))
                    ((mv decompressed &)
                     (decompress-s-c `(s '0 'nil (list ,inner-single-c)))))
                 (case-match decompressed
                   (('s & arg-pp arg-c)
                    (mv arg-pp arg-c (s-pattern1-success)))
                   (& (mv pp c nil)))))
              (& (mv pp c nil)))))
         (& (mv pp c nil)))))
    (& (mv pp c nil))))||#

#|(progn
  (define s-pattern2-reduce-lst (pp c-lst)
    (b* (((when (atom c-lst))
          (mv pp c-lst nil))
         ((mv pp c-lst-rest rest-changed)
          (s-pattern2-reduce-lst pp (cdr c-lst)))
         (cur (car c-lst))
         (cur (ex-from-rp-loose cur))
         ((mv should-try c-pp-arg)
          (case-match cur
            (('c & ''nil pp1 ('list single-c-arg1))
             (b* ((single-c-arg1 (ex-from-rp-loose single-c-arg1)))
               (case-match single-c-arg1
                 (('c & ''nil pp2 &)
                  (if (equal pp1 pp2)
                      (mv t pp1)
                    (mv nil nil)))
                 (& (mv nil nil)))))
            (& (mv nil nil))))
         ((unless should-try)
          (if rest-changed
              (mv pp (cons cur c-lst-rest) t)
            (mv pp c-lst nil)))
         ((mv pp-extra c-extra changed)
          (s-pattern1-reduce c-pp-arg `(list ,cur)))
         ((unless changed)
          (if rest-changed
              (mv pp (cons cur c-lst-rest) t)
            (mv pp c-lst nil)))
         (pp (pp-sum-merge pp-extra pp))
         (pp (pp-sum-merge c-pp-arg pp)))
      (case-match c-extra
        (('list single-c)
         (mv pp (cons single-c c-lst-rest) t))
        (&
         (mv pp c-lst nil)))))

  (define s-pattern2-success ()
    t)

  (profile 's-pattern2-success)

  (define s-pattern2-reduce (pp c)
    (case-match c
      (('list . c-lst)
       (b* (((mv pp c-lst changed)
             (s-pattern2-reduce-lst pp c-lst))
            ((unless changed)
             (mv pp c nil))
            (pp (s-fix-args pp))
            (c-lst (s-fix-pp-args-aux c-lst)))
         (mv pp `(list . ,c-lst) (s-pattern2-success))))
      (& (mv pp c nil)))))||#

(progn
  (define negate-pp-lst (pp-lst)
    :returns (negated-pp-lst rp-term-listp :hyp (rp-term-listp pp-lst))
    (b* (((when (atom pp-lst)) pp-lst)
         (rest (negate-pp-lst (cdr pp-lst)))
         (cur-orig (car pp-lst))
         (cur (ex-from-rp-loose cur-orig)))
      (case-match cur
        (('-- term)
         (cons term rest))
        (& (cons `(-- ,cur-orig)
                 rest)))))

  (define negate-pp (pp)
    :returns (pp-res rp-termp :hyp (rp-termp pp))
    (create-list-instance (negate-pp-lst (list-to-lst pp)))))
    ;; (case-match pp
    ;;   (('list . lst)
    ;;    (create-list-instance (negate-pp-lst lst)))
    ;;   (''nil
    ;;    pp)
    ;;   (&
    ;;    (progn$ (hard-error
    ;;             'negate-pp
    ;;             "Unexpected pp instance ~p0 ~%"
    ;;             (list (cons #\0 pp)))
    ;;            `(list (-- (sum-list ,pp))))))))

(define c-pattern2-reduce (s pp c)
  ;; This function is called before forming a single-c instance as (c s pp c).
  ;; It might be possible to compress the c instance.
  :returns (mv (s-res rp-termp
                      :hyp (and (rp-termp s)
                                (rp-termp pp)
                                (rp-termp c)))
               (pp-res rp-termp
                       :hyp (and (rp-termp s)
                                 (rp-termp pp)
                                 (rp-termp c)))
               (c-res rp-termp
                      :hyp (and (rp-termp s)
                                (rp-termp pp)
                                (rp-termp c))))
  (cond
   ((not (equal s ''nil)) (mv s pp c))
   (t
    (case-match c
      (('list ('c & ''nil c-pp &))
       (b* (((unless (pp-subsetp pp c-pp)) (mv s pp c))
            (--pp (negate-pp pp))
            (single-c `(c '0 ,s ,--pp ,c))
            (compressed (compress-s-c single-c)))
         (case-match compressed
           (('c & ''nil ''nil ('list single-c))
            (b* (((mv max min valid) (get-max-min-val single-c))
                 ((unless (and valid
                               (equal max 0)
                               (equal min -1)))
                  (mv s pp c))
                 ((mv decompressed coughed-pp)
                  (decompress-s-c single-c))
                 (coughed-pp (pp-sum-merge pp coughed-pp))
                 ((unless (equal coughed-pp ''nil))
                  (mv s pp c)))
              (case-match decompressed
                (('c & s pp c)
                 (mv s pp c))
                (& (mv s pp c)))))
           (& (mv s pp c)))))
      (& (mv s pp c))))))


(define create-c-instance (s pp c)
;:inline t
  :returns (c/d-res rp-termp :hyp (and (rp-termp pp)
                                       (rp-termp s)
                                       (rp-termp c)))
  (b* (((mv s pp c)
        (c-pattern2-reduce s pp c)))
    (cond ((or (and (equal c ''nil)
                    (equal s ''nil)
                    (case-match pp (('list ('and-list & &)) t)))
               (and (equal c ''nil)
                    (equal pp ''nil)
                    (case-match s (('list ('s & & &)) t)
                      (('list ('rp ''bitp &)) t)))
               (and (equal s ''nil)
                    (equal pp ''nil)
                    (case-match c
                      (('list single-c)
                       (or (is-rp-bitp single-c)
                           (is-c-bitp-traverse single-c))))))
           ''0)
          ((and (quotep pp)
                (consp (cdr pp))
                (quotep s)
                (consp (cdr s))
                (quotep c)
                (consp (cdr c)))
           `',(c 0 (unquote s) (unquote pp) (unquote c)))
          (t
           (b* ((hash-code (calculate-c-hash s pp c))
                #|(- (if (equal hash-code 2215122)
                (progn$ (cw "found hash-code: ~p0 ~%" hash-code) ; ;
                (sleep 10)) ; ;
                nil))||#)
;;;;; hash-code calc..
             `(c ',hash-code ,s ,pp ,c))))))

#|(define s-pattern3-success ()
  t)||#

#|(profile 's-pattern3-success)||#

(local
 (defthm is-rp-of-bitp
   (is-rp `(rp 'bitp ,x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(define s-pattern3-reduce (pp c)
  ;; :returns (mv pp c reduced reducedp)
  ;; Search for (s pp1 (c pp1 rest))
  ;; which is equivalant to (s (c -pp1 rest))
  ;; which is created with compress-s-c
  ;; if the max/min val of (c -pp1 rest) is 0/-1,
  ;; then reducedp=1 and reduced=(-- (c -pp1 rest))
  ;; but it is decompressed so reduced=(sum pp1 (-- (c rest)))
  ;; reduced will be the value returned from create-s-instance right away.

  :returns (mv (pp-res rp-termp :hyp (and (rp-termp pp)
                                          (rp-termp c)))
               (c-res rp-termp :hyp (and (rp-termp pp)
                                         (rp-termp c)))
               (reduced rp-termp :hyp (and (rp-termp pp)
                                           (rp-termp c)))
               (reducedp booleanp))
  (case-match c
    (('list ('c & ''nil c-pp &))
     (b* (((unless (pp-subsetp pp c-pp))
           (mv pp c ''0 nil))
          (compressed (compress-s-c `(s '0 ,pp ,c))))
       (case-match compressed
         (('s & ''nil ('list single-c))
          (b* (((mv max min valid) (get-max-min-val single-c))
               ((unless (and valid
                             (= max 0)
                             (= min -1)))
                (mv pp c ''0 nil)))
            (mv ''nil ''nil
                `(rp 'bitp (c-res 'nil ,pp (list (-- ,(cadr c)))))
                t)))
         (& (mv pp c ''0 nil)))))
    (& (mv pp c ''0 nil))))


;; (compress-s-c '(s '0 (list c b a) (list (c '0 'nil (list d c a) 'nil))))
;; (decompress-s-c '(S '0 (LIST B) (LIST (C '0 'NIL (LIST D (-- C) (-- A)) 'NIL))))

(define create-s-instance (pp c)
  :inline t
  :returns (res rp-termp
                :hyp (and (rp-termp pp)
                          (rp-termp c)))
  (b* (#|((mv pp c changed1) (s-pattern1-reduce pp c))||#
       #|((mv pp c changed2) (s-pattern2-reduce pp c))||#
       #|((when (or changed1 changed2))
       (create-s-instance pp c))||#
       ((mv pp c reduced reducedp)
        (s-pattern3-reduce pp c))
       ((when reducedp)
        reduced))
    (cond ((and (quotep pp)
                (quotep c)
                (consp (cdr pp))
                (consp (cdr c)))
           `',(s 0 (unquote pp) (unquote c)))
          ((and (equal c ''nil)
                (case-match pp (('list ('and-list & &)) t)))
           (cadr pp))
          ((and (equal pp ''nil)
                (case-match c
                  (('list single-c)
                   (or (is-rp-bitp single-c)))))
           (cadr c))
          ((and (equal pp ''nil)
                (case-match c
                  (('list single-c)
                   (is-c-bitp-traverse single-c))))
           `(rp 'bitp ,(cadr c)))
          #|((can-s-be-compressed pp c)
          (compress-s pp c))||#
          ((and
            (case-match pp
              (('list & &) t))
            (case-match c
              (('list ('rp ''bitp ('c & & c-pp &)))
               (and (equal c-pp pp)))))
           (cadr c))

          (t
           `(rp 'bitp (s ',(calculate-s-hash pp c) ,pp ,c))))))

(define swap-terms (single-c1 single-c2 swap)
  :inline t
  :returns (mv (res1 rp-termp
                     :hyp (and (rp-termp single-c1)
                               (rp-termp single-c2)))
               (res2 rp-termp
                     :hyp (and (rp-termp single-c1)
                               (rp-termp single-c2))))
  (if swap
      (mv single-c2 single-c1)
    (mv single-c1 single-c2)))

(local
 (defthm is-rp-of-evenpi
   (IS-RP `(RP 'EVENPI ,x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

;;;;;;;;;;;;;;

;;c-merge

;; (progn
;;   (define can-c-merge-fast-aux (s-lst pp c)
;;     ;;:inline t
;;     (if (atom s-lst)
;;         nil
;;       (or (b* ((cur-s (ex-from-rp-loose (car s-lst))))
;;             (case-match cur-s
;;               (('s & pp-arg c-arg)
;;                (progn$
;;                 (and
;;                  ;;(equal pp-arg pp) (equal c/d-arg c)
;;                  (rp-equal-cnt c-arg c 0) (rp-equal-cnt pp-arg pp 0) ;; TEST
;;                  ;; ADDING CALCULATE-PP-HASH COMPARISON HERE.
;;                  )))))
;;           (can-c-merge-fast-aux (cdr s-lst) pp c)
;;           )))

;;   (define can-c-merge-fast (single-c1 single-c2)
;;     ;; returns nil, 0 or 1. 0 and 1 mean terms can merge fast, and 1 means flip c/d1
;;     ;; and c/d2
;;     (b* (((mv & s-arg1 pp-arg1 c-arg1 type1) (get-c-args single-c1))
;;          ((mv & s-arg2 pp-arg2 c-arg2 type2) (get-c-args single-c2))
;;          (c-arg1 (create-list-instance c-arg1))
;;          (c-arg2 (create-list-instance c-arg2))
;;          ((when (or (not (equal type1 'c))
;;                     (not (equal type2 'c))))
;;           nil)
;;          (match1 ;; possible match to (sum (f2 x) (f2 (sum (m2 x) y)))
;;           ;; c/d1 = (c 'nil arg-pp1 arg-c/d1)
;;           ;; c/d2 = (c (list (s arg-pp1 arg-c/d1) other-s) arg-pp2 arg-c/d2)
;;           (and (equal s-arg1 ''nil)
;;                (case-match s-arg2 (('list . &) t))))

;;          (match2 ;; possible match to (sum (f2 x) (f2 (sum (m2 x) y)))
;;           ;; c/d1 = (c (list (s arg-pp1 arg-c/d1) other-s) arg-pp2 arg-c/d2)
;;           ;; c/d2 = (c 'nil arg-pp1 arg-c/d1)
;;           (and (case-match s-arg1 (('list . &) t))
;;                (equal s-arg2 ''nil))))
;;       (cond (match1
;;              (if (can-c-merge-fast-aux (cdr s-arg2) pp-arg1 c-arg1)
;;                  0
;;                nil))
;;             (match2
;;              (if (can-c-merge-fast-aux (cdr s-arg1) pp-arg2 c-arg2)
;;                  1
;;                nil))
;;             (t
;;              nil))))

;;   (define well-merged-c-lst-p-aux (single-c c-lst)
;;     (if (atom c-lst)
;;         t
;;       (and (not (can-c-merge-fast single-c (car c-lst)))
;;            (well-merged-c-lst-p-aux single-c (cdr c-lst)))))

;;   (define well-merged-c-lst-p (c-lst)
;;     (if (atom c-lst)
;;         t
;;       (and (well-merged-c-lst-p-aux (car c-lst) (cdr c-lst))
;;            (well-merged-c-lst-p (cdr c-lst)))))

;;   (define well-merged-c-p (c &key (message '""))
;;     (and nil
;;          (case-match c
;;            (('list . c-lst)
;;             (b* ((res (well-merged-c-lst-p c-lst)))
;;               (if res
;;                   res
;;                 (hard-error 'well-merged-c-p
;;                             "The given c is not merged well.~%~p0~%~p1~%"
;;                             (list (cons #\0 message)
;;                                   (cons #\1 c))))))
;;            (& t))))

;;   (acl2::defines
;;    all-well-merged-c-p
;;    (define all-well-merged-c-p (term)
;;      :measure (cons-count term)
;;      :prepwork ((local
;;                  (in-theory (enable measure-lemmas))))
;;      (b* ((term (ex-from-rp-loose term)))
;;        (case-match term
;;          (('c & s & c)
;;           (and (well-merged-c-p c)
;;                (all-well-merged-c-p c)
;;                (all-well-merged-c-p s)))
;;          (('s & & c)
;;           (and (well-merged-c-p c)
;;                (all-well-merged-c-p c)))
;;          (('list . lst)
;;           (all-well-merged-c-lst-p lst))
;;          (& t))))

;;    (define all-well-merged-c-lst-p (lst)
;;      (if (atom lst)
;;          t
;;        (and (all-well-merged-c-p (car lst))
;;             (all-well-merged-c-lst-p (cdr lst)))))))

;; ;; TEST:try passign hash of c (and make the calculation  same as s)

;; #|(define cough-negated-single-c (single-c)
;;   (b* ((orig single-c)
;;        (single-c (ex-from-rp-loose single-c)))
;;     (case-match single-c
;;       (('-- c-in)
;;        (mv (list orig) c-in))
;;       (&
;;        (mv nil orig)))))||#


;; (progn
;;   (defwarrant EX-FROM-RP-LOOSE)
;;   (define c-pattern1-search-aux ((s-arg-lst rp-term-listp)
;;                                  (c-arg-lst rp-term-listp))
;;     (loop$
;;      for i from 0 to (len s-arg-lst) as cur-s in s-arg-lst when
;;      (b* ((cur-s (ex-from-rp-loose cur-s))
;;           (& (cw "cur-s:~p0 ~%" cur-s))
;;           (res
;;            (case-match cur-s
;;              (('s & & ('list . s-c-lst))
;;               (loop$ for cur-c in c-arg-lst sum :guard (and (integerp i)
;;                                                             (true-listp c-arg-lst)
;;                                                             (true-listp s-c-lst))
;;                      (b* ((cur-c (ex-from-rp-loose cur-c))
;;                           (& (cw "cur-c:~p0 ~%" cur-c)))
;;                        (case-match cur-c
;;                          (('c & ('list . c-s-lst) & &)
;;                           (loop$ for cur-c-s in c-s-lst sum :guard (and
;;                                                                     (integerp
;;                                                                      i)
;;                                                                     (true-listp s-c-lst)
;;                                                                     (true-listp
;;                                                                      c-s-lst))
;;                                  (b* ((cur-c-s (ex-from-rp-loose cur-c-s))
;;                                       (& (cw "cur-c-s ~p0 ~%" cur-c-s)))
;;                                    (case-match cur-c-s
;;                                      (('s hash1 & &)
;;                                       (loop$ for cur-s-c in s-c-lst sum :guard
;;                                              (and (integerp i)
;;                                                   (true-listp s-c-lst))
;;                                              (b* ((cur-s-c
;;                                                    (ex-from-rp-loose
;;                                                     cur-s-c))
;;                                                   (& (cw "cur-s-c:~p0 ~%"
;;                                                          cur-s-c))
;;                                                   (& (cw "hash1 : ~p0 ~%" hash1)))
;;                                                (case-match cur-s-c
;;                                                  (('c hash2 & & &)
;;                                                   (progn$
;;                                                    (if (equal hash1 hash2)
;;                                                        1
;;                                                      0)))
;;                                                  (& 0)))))
;;                                      (& 0)))))
;;                          (& 0)))))
;;              (& 0))))
;;        (not (equal 0 res)))
;;      collect i))

;;   (define c-pattern1-success ()
;;     t)

;;   (profile 'c-pattern1-success)

;;   (define c-pattern1-search ((s-arg rp-termp)
;;                              (c-arg-lst rp-term-listp))
;;     :prepwork ((local
;;                 (defthm lemma1
;;                   (implies  (rp-term-listp lst)
;;                             (true-listp lst))))
;;                (local
;;                 (defthm lemma2
;;                   (implies (and (rp-termp s-arg)
;;                                 (case-match s-arg (('list . &) t)))
;;                            (and (rp-term-listp (cdr s-arg))
;;                                 (true-listp (cdr s-arg))))
;;                   :hints (("Goal"
;;                            :in-theory (e/d (rp-term-listp
;;                                             rp-termp)
;;                                            ())))))
;;                (local
;;                 (in-theory (disable posp
;;                                     nth
;;                                     rp-term-listp
;;                                     rp-termp))))
;;     (b* (((when t) nil)
;;          ((unless (case-match s-arg (('list . &) t))) nil)
;;          (s-arg-lst (cdr s-arg))
;;          (s-index-lst (c-pattern1-search-aux s-arg-lst c-arg-lst))
;;          ((unless (consp s-index-lst)) nil)
;;          (selected-s (nth (nfix (car s-index-lst)) s-arg-lst))
;;          (selected-s (ex-from-rp-loose selected-s)))
;;       (case-match selected-s
;;         (('s & pp c)
;;          (and (c-pattern1-success) nil
;;               (create-c-instance ''nil pp c)))
;;         (& nil)))))

#|(define loop-test ((lst1 true-listp)
                   (lst2 true-listp))
  :verify-guards nil
  (loop$ for i from 1 to (len lst1) as cur1 in lst1 sum
         (loop$ for cur2 in lst2 sum :guard (integerp i)
                (if (equal cur1 cur2) i 0))))||#



(progn
  (define light-s-of-s-fix-lst (s-lst c-lst)
    :returns (mv (pp-res-lst rp-term-listp
                             :hyp (and (rp-term-listp s-lst)
                                       (rp-term-listp c-lst)))
                 (c-res-lst rp-term-listp
                            :hyp (and (rp-term-listp s-lst)
                                      (rp-term-listp c-lst))))
    ;; similar to s-of-s-fix-lst but it doesn't try to merge c-lsts
    :measure (acl2-count  s-lst)
    (b* (((when (atom s-lst)) (mv nil c-lst))
         ((mv pp-lst c-lst) (light-s-of-s-fix-lst (cdr s-lst) c-lst))
         (cur-s (ex-from-rp/-- (car s-lst))))
      (case-match cur-s
        (('s & cur-pp cur-c)
         (b* ((cur-c-lst (list-to-lst cur-c))
              (c-lst (s-sum-merge-aux c-lst cur-c-lst)) ;; put c's together
              ;; without trying to merge them..
              (pp-lst (pp-sum-merge-aux (list-to-lst cur-pp) pp-lst)))
           (mv pp-lst c-lst)))
        (''nil
         (mv pp-lst c-lst))
        (&
         (progn$ (cw "Unexpected s term ~p0 ~%" cur-s)
                 (hard-error 's-of-s-fix-aux "Read above.." nil)
                 (mv (list-to-lst `(binary-append ,cur-s (list . ,pp-lst)))
                     c-lst))))))

  (define light-s-of-s-fix (s pp c-lst)
    :returns (mv (pp-res rp-termp :hyp (and (rp-termp s)
                                            (rp-termp pp)
                                            (rp-term-listp c-lst)))
                 (c-res-lst rp-term-listp :hyp (and (rp-termp s)
                                                    (rp-termp pp)
                                                    (rp-term-listp c-lst))))
    (b* ((s-lst (list-to-lst s))
         ((when (equal s-lst nil))  (mv pp c-lst))
         ((mv pp-lst c-lst)
          (light-s-of-s-fix-lst s-lst c-lst))
         (pp-lst (pp-sum-merge-aux (list-to-lst pp) pp-lst))
         (pp (create-list-instance pp-lst)))
      (mv pp c-lst)))


  (define single-c-try-merge-params (s-lst c-hash-code s-arg pp-arg c-arg-lst)
    :returns (mv (updated-s-lst rp-term-listp :hyp (and (rp-term-listp s-lst)))
                 (success booleanp))
    :measure (acl2-count s-lst)
    (if (atom s-lst)
        (mv s-lst nil)
      (b* ((cur-s (ex-from-rp-loose (car s-lst))))
        (case-match cur-s
          (('s ('quote s-hash-code) cur-pp-arg cur-c-arg)
           (if (and (equal c-hash-code s-hash-code)
                    (b* (((mv pp-arg c-arg-lst)
                          (light-s-of-s-fix s-arg pp-arg c-arg-lst)))
                      (and (equal (create-list-instance c-arg-lst) cur-c-arg)
                           (equal pp-arg cur-pp-arg))))
               (mv (cdr s-lst) t)

             (b* (((mv rest-s-lst success)
                   (single-c-try-merge-params (cdr s-lst) c-hash-code s-arg pp-arg c-arg-lst)))
               (if success
                   (mv (cons (car s-lst) rest-s-lst) t)
                 (mv s-lst nil)))))
          (&
           (progn$
            (hard-error 'single-c-try-merge-params
                        "Bad form for current s-lst:~p0~%"
                        (list (cons #\0 s-lst)))
            (mv s-lst nil))))))))


#|(mutual-recursion
 (defun c-sum-measure (term)
   (cond ((atom term) 1)
         ((quotep term) 1)
         ((equal (car term) 'c)
          (/ (c-sum-measure-lst (cdr term))
             4))
         ((equal (car term) '--)
          (- (c-sum-measure-lst (cdr term))))
         (t (1+ (c-sum-measure-lst (cdr term))))))
 (defun c-sum-measure-lst (term)
   (if (atom term)
       0
     (+ (c-sum-measure (car term))
        (c-sum-measure-lst (cdr term))))))||#

(skip-proofs
 (acl2::defines
  c-sum-merge

  (define single-c-try-merge  (single-c1 single-c2 &key (level 'level))
    ;; returns (mv coughed-s coughed-pp-lst produced-c-lst merge-success)
    ;; if merge-success is t
    ;; otherwise (mv nil nil 0 merge-success)
    (declare (ignorable level))
    :measure (+ (cons-count single-c1)
                (cons-count single-c2))
    (b* (;; don't try to merge negated elements. They will be coughed off and
         ;; will be tried later.
         ((when (or (case-match single-c1 (('-- &) t))
                    (case-match single-c2 (('-- &) t))))
          (mv ''nil nil nil nil))
         ((mv c1-hash-code s-arg1 pp-arg1 c-arg1-lst type1) (get-c-args single-c1))
         ((mv &            s-arg2 pp-arg2 c-arg2-lst type2) (get-c-args single-c2))
         ((when (or (not type1) (not type2)))
          (progn$ (hard-error
                   'single-c-try-merge
                   "Unexpected single-c instances.~%single-c1:~p0~%single-c2:~p1~%"
                   (list (cons #\0 (list type1 single-c1))
                         (cons #\1 (list type2 single-c2))))
                  (mv ''nil nil nil nil)))
         ((unless (case-match s-arg2 (('list . &) t)))
          (mv ''nil nil nil nil))
         ;; search for a merge potential by going through s-lst of the single-c2
         ;; when a match is found, that s will be removed from the list.
         ((mv updated-s-arg2-lst success)
          (single-c-try-merge-params (cdr s-arg2)
                                     c1-hash-code
                                     s-arg1
                                     pp-arg1
                                     c-arg1-lst))
         ;; no match? move on..
         ((unless success)
          (mv ''nil nil ''0 nil))
         ;; if it reached here, then it  means it can merge. Eviscerate single-c1
         ;; and merge its arguments:
         ;; first merge c-arguments. It might cough out s and pp lists, and a
         ;; c-lst to be coughed
         ((mv arg-coughed-s arg-coughed-pp-lst arg-merged-c-lst arg-to-be-coughed-c-lst)
          (c-sum-merge c-arg1-lst c-arg2-lst))

         ;; create the new pp arg by merging the coughed-pp from c-merger, and
         ;; pp-args from the original single-c1 and single-c2
         (pp-lst (pp-sum-merge-aux (list-to-lst pp-arg1) (list-to-lst pp-arg2)))
         (pp-lst (pp-sum-merge-aux arg-coughed-pp-lst pp-lst))

         ;; also merge the updated s-lst of single-c2 and coughed s-lst.
         ;; and s-arg1 if any (it will be ''nil most of the time)
         ;; before creating the c instance, try coughing out with the new s argument
         (new-s-arg (s-sum-merge s-arg1
                                 (s-sum-merge arg-coughed-s
                                              (create-list-instance updated-s-arg2-lst))))
         ((mv coughed-s new-s-arg)
          (c-fix-s-args new-s-arg))

         ((mv coughed-pp-lst new-pp-lst)
          (if (clean-pp-args-cond new-s-arg arg-merged-c-lst)
              (c-fix-arg-aux pp-lst t (expt 2 30))
            (mv nil pp-lst)))
         (new-pp-arg (pp-lst-to-pp new-pp-lst))

         ;; To-be-coughed c-lst from the args is the coughed-c-lst of the
         ;; new c instance.
         (merged-single-c (create-c-instance new-s-arg
                                             new-pp-arg
                                             (create-list-instance
                                              arg-merged-c-lst)))

         (produced-c-lst (cons merged-single-c arg-to-be-coughed-c-lst)))
      (mv coughed-s coughed-pp-lst produced-c-lst t)))

  (define c-sum-merge-lst-aux (single-c1 c2-lst &key (level 'level))
    (declare (ignorable level))
    ;;:returns (mv coughed-s coughed-pp-lst produced-c-lst rest-c2-lst merge-success)

    ;; try and merge single-c1 with something in c2-lst
    ;; after the merge, coughed-s and coughed-pp-lst might have results from the
    ;; new c.
    ;; the result "produced-c-lst" may be mergable with something(s) in
    ;; rest-c2-lst
    ;; when merge is succesful c2-lst will have one less element.
    :measure (+ (cons-count single-c1) (cons-count c2-lst))

    (if (atom c2-lst)
        (mv ''nil nil nil nil nil)
      (b* (((mv coughed-s coughed-pp-lst  produced-c-lst merge-success)
            (single-c-try-merge single-c1 (car c2-lst)))
           ((when merge-success)
            (mv coughed-s coughed-pp-lst produced-c-lst (cdr c2-lst)
                merge-success))

           ((mv coughed-s coughed-pp-lst produced-c-lst merge-success)
            (single-c-try-merge (car c2-lst) single-c1))
           ((when merge-success)
            (mv coughed-s coughed-pp-lst  produced-c-lst (cdr c2-lst)
                merge-success))

           ((mv coughed-s coughed-pp-lst produced-c-lst rest-c2-lst merge-success)
            (c-sum-merge-lst-aux single-c1 (cdr c2-lst)))

           ;;(- (well-merged-c-p merged-c :message "pos. a"))
           )
        (if merge-success
            (mv coughed-s coughed-pp-lst produced-c-lst (cons (car c2-lst) rest-c2-lst)
                merge-success)
          (mv ''nil nil nil c2-lst nil)))))

  (define c-sum-merge-lst (single-c1 c2-lst &key (level 'level))
    (declare (ignorable level))
    :measure (acl2-count c2-lst)
    ;;:returns (mv coughed-s2 coughed-pp-lst new-c2-lst)

    ;; Same as c-sum-merge-lst-aux but produced-c-lst is not mergable with anything
    ;; in rest-c2-lst because it was tried to be merged as long as it goes.

    (b* (((when (equal single-c1 ''0)) ;; if it is 0 then convert it to a pp
          (mv ''nil nil c2-lst))
         ((when (quotep single-c1)) ;; if it is quoted then convert it to a pp
          (mv ''nil (list single-c1) c2-lst))
         ((mv coughed-s coughed-pp-lst produced-c-lst rest-c2-lst merge-success)
          (c-sum-merge-lst-aux single-c1 c2-lst)))
      (if merge-success
          (b* (((mv coughed-s2 coughed-pp-lst2 new-c2-lst)
                (c-sum-merge-lst-lst produced-c-lst rest-c2-lst))  ;;;;;;; measure-mbe-here
               (coughed-s (s-sum-merge coughed-s coughed-s2))
               (coughed-pp-lst (pp-sum-merge-aux  coughed-pp-lst coughed-pp-lst2)))
            (mv coughed-s coughed-pp-lst  new-c2-lst))
        (mv ''nil nil (s-sum-merge-aux (list single-c1) c2-lst)))))

  (define c-sum-merge-lst-lst (c1-lst c2-lst &key (level 'level))
    ;;:returns (mv coughed-s coughed-pp-lst-lst c2-lst)
    (declare (ignorable level))
    (b* (((when (atom c1-lst))  (mv ''nil nil c2-lst))   
         ((mv coughed-s coughed-pp-lst1 c2-lst)
          (c-sum-merge-lst (car c1-lst) c2-lst))

         ((mv coughed-s2 coughed-pp-lst2  c2-lst) ;;;;;;; measure-mbe-here
          (c-sum-merge-lst-lst (cdr c1-lst) c2-lst))

         (coughed-s-merged (s-sum-merge coughed-s coughed-s2))
         (coughed-pp-lst (pp-sum-merge-aux coughed-pp-lst1
                                           coughed-pp-lst2)))
      (mv coughed-s-merged
          coughed-pp-lst
          c2-lst)))

  (define c-sum-merge (c1-lst c2-lst &key
                              (auto-swap 't)
                              (clean-c1-lst 'nil)
                              (level 'level))
    (declare (ignorable level))
    :returns (mv (coughed-s rp-termp
                            :hyp (and (rp-term-listp c1-lst)
                                      (rp-term-listp c2-lst)))
                 (coughed-pp-lst rp-term-listp
                                 :hyp (and (rp-term-listp c1-lst)
                                           (rp-term-listp c2-lst)))
                 (c-merged-lst rp-term-listp
                               :hyp (and (rp-termp c1-lst)
                                         (rp-termp c2-lst)))
                 (to-be-coughed-c-lst rp-term-list-listp
                                      :hyp (and (rp-termp c1-lst)
                                                (rp-termp c2-lst))))
    :measure (+ (cons-count c1-lst)
                1
                (cons-count c2-lst))
    (b* (((mv c1-lst c2-lst)
          (swap-terms c1-lst c2-lst
                      (and auto-swap
                           (let ((first-id  (case-match c1-lst
                                              ((('c ('quote hash) . &) . &) hash)
                                              (& 0)))
                                 (second-id (case-match c2-lst
                                              ((('c ('quote hash) . &) . &) hash)
                                              (& 0)))
                                 (len1 (len c1-lst))
                                 (len2 (len c2-lst)))
                             (if (= len1 len2)
                                 (> (nfix first-id)
                                    (nfix second-id))
                               (> len1 len2))))))
         ((mv coughed-s coughed-pp-lst merged-c-lst to-be-coughed-c-lst)
          (c-sum-merge-aux c1-lst c2-lst :clean-c1-lst clean-c1-lst))

         #|(- (m-eval-compare `(sum (sum . ,c1-lst)
         (sum . ,c2-lst))
         `(sum (sum-list ,coughed-s)
         (sum-list-list ',(m-eval-lst-lst
         coughed-pp-lst-lst *a*))
         (sum . ,merged-c-lst)
         (sum . ,to-be-coughed-c-lst)
         (sum . ,to-be-coughed-c-lst))
         :id 'c-sum-merge1
         :print-exps t))||#
         )
      (mv coughed-s coughed-pp-lst merged-c-lst to-be-coughed-c-lst)))

  (define c-sum-merge-aux (c1-lst c2-lst &key
                                  (clean-c1-lst 'nil)
                                  (level 'level))
    (declare (ignorable level))
    ;; returns (mv coughed-s coughed-pp-lst res-c)
    :returns (mv (coughed-s rp-termp
                            :hyp (and (rp-termp c1-lst)
                                      (rp-termp c2-lst)))
                 (coughed-pp-lst rp-term-listp
                                 :hyp (and (rp-termp c1-lst)
                                           (rp-termp c2-lst)))
                 (c-merged-lst rp-term-listp
                               :hyp (and (rp-termp c1-lst)
                                         (rp-termp c2-lst)))
                 (to-be-coughed-c-lst rp-term-listp
                                      :hyp (and (rp-termp c1-lst)
                                                (rp-termp c2-lst))))
    :measure (+ (cons-count c1-lst)
                1
                (cons-count c2-lst))
    (cond ((equal c1-lst nil)
           (mv ''nil nil c2-lst nil))
          ((and (equal c2-lst nil)
                (not clean-c1-lst))
           (mv ''nil nil c1-lst nil))
          (t (b* (((mv coughed-s1 coughed-pp-lst1 merged-c-lst)
                   (c-sum-merge-lst-lst c1-lst c2-lst))
                  ((mv selected-c-lst reduced-c-lst to-be-coughed-c-lst1)
                   (c-fix-c-arg-lst merged-c-lst))
                  ((mv coughed-s2 coughed-pp-lst2 merged-c-lst to-be-coughed-c-lst2)
                   (c-sum-merge selected-c-lst reduced-c-lst)) ;;;;;;  measure-mbe-here
                  (to-be-coughed-c-lst (s-sum-merge-aux to-be-coughed-c-lst1
                                                        to-be-coughed-c-lst2))
                  (coughed-s (s-sum-merge coughed-s1 coughed-s2))
                  (coughed-pp-lst (pp-sum-merge-aux coughed-pp-lst1
                                                    coughed-pp-lst2)))
               (mv coughed-s coughed-pp-lst merged-c-lst to-be-coughed-c-lst)))))))


(memoize 'c-sum-merge-aux
         :memo-table-init-size 100000
;:condition 'mem
         ;;:recursive nil
         ;;:condition '(and (not (equal c1-lst nil)) (not (equal c2-lst nil)))
         :aokp t)




(define s-of-s-fix-lst (s-lst c-lst &key (level 'level))
  :returns (mv (pp-res-lst rp-term-listp
                           :hyp (and (rp-term-listp s-lst)
                                     (rp-term-listp c-lst)))
               (c-res rp-termp
                      :hyp (and (rp-term-listp s-lst)
                                (rp-term-listp c-lst))))
  (declare (ignorable level))
  (if (atom s-lst)
      (mv nil c-lst)
    (b* (((mv pp-lst c-lst) (s-of-s-fix-lst (cdr s-lst) c-lst))
         (cur-s (ex-from-rp/-- (car s-lst))))
      (case-match cur-s
        (('s & cur-pp cur-c)
         (b* ((cur-c-lst (list-to-lst cur-c))
              ((mv coughed-s coughed-pp-lst c-lst &)
               (c-sum-merge cur-c-lst c-lst))
              (pp-lst (pp-sum-merge-aux coughed-pp-lst pp-lst))
              (pp-lst (pp-sum-merge-aux (list-to-lst cur-pp) pp-lst)))
           (case-match coughed-s
             (('list . s-lst)
              (b* (((mv rest-pp-lst c-lst)
                    (s-of-s-fix-lst s-lst c-lst)))
                (mv (pp-sum-merge-aux rest-pp-lst pp-lst) c-lst)))
             (''nil
              (mv pp-lst c-lst))
             (& (progn$ (cw "Unexpected s format ~p0 ~%" coughed-s)
                        (hard-error 's-of-s-fix-aux "" nil)
                        (mv `(binary-append (list . ,pp-lst) ,coughed-s) c-lst))))))
        (''nil
         (mv pp-lst c-lst))
        (&
         (progn$ (cw "Unexpected s term ~p0 ~%" cur-s)
                 (hard-error 's-of-s-fix-aux "Read above.." nil)
                 (mv (list-to-lst `(binary-append ,cur-s (list . ,pp-lst)))
                     c-lst)))))))

(define s-of-s-fix (s pp c-lst &key (level 'level))
  (declare (ignorable level))
  :returns (mv (pp-res rp-termp :hyp (and (rp-termp s)
                                          (rp-termp pp)
                                          (rp-term-listp c-lst)))
               (c-res rp-termp :hyp (and (rp-termp s)
                                         (rp-termp pp)
                                         (rp-term-listp c-lst))))
  (b* ((s-lst (list-to-lst s))
       ((when (equal s-lst nil))  (mv pp c-lst))
       ((mv pp-lst c-lst)
        (s-of-s-fix-lst s-lst c-lst))
       (pp-lst (pp-sum-merge-aux (list-to-lst pp) pp-lst))
       (pp (create-list-instance pp-lst)))
    (mv pp c-lst)))



;;;;;;;



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

(define extract-new-sum-element (term acc)
  :measure (cons-count term)
  :prepwork
  ((local
    (in-theory (enable measure-lemmas))))
  (b* ((term-orig term)
       (term (ex-from-rp-loose term)))
    (case-match term
      (('c & & & &)
       (cons term-orig acc))
      (('s & & &)
       (cons term-orig acc))
      (('c-res & & &)
       (cons term-orig acc))
      (('sum-list &)
       (cons term-orig acc))
      (('and-list & &)
       (cons term-orig acc))
      (('binary-sum a b)
       (b* ((acc (extract-new-sum-element a acc))
            (acc (extract-new-sum-element b acc)))
         acc))
      (('quote x)
       (b* ((x (ifix x)))
         (cond ((natp x) (append (repeat x ''1) acc))
               (t (append (repeat (- x) ''-1) acc)))))
      (&
       (cond ((good-4vec-term-p term)
              (cons term-orig acc))
             (t
              (progn$
               (hard-error 'extract-new-sum-element
                           "Unexpexted term: ~p0 ~%"
                           (list (cons #\0 term-orig)))
               (cons term-orig acc))))))))

(define extract-new-sum-consed (term)
  :measure (cons-count term)
  :prepwork
  ((local
    (in-theory (enable measure-lemmas
                       ex-from-rp-loose))))
  (b* ((term-orig term)
       (term (ex-from-rp-loose term)))
    (case-match term
      (('cons x rest)
       (b* ((acc (extract-new-sum-consed rest)))
         (extract-new-sum-element x acc)))
      (('quote x)
       (if (consp x)
           (b* ((acc (extract-new-sum-consed (list 'quote (cdr x)))))
             (extract-new-sum-element (list 'quote (car x)) acc))
         (extract-new-sum-element term-orig nil)))
      (&
       (extract-new-sum-element term-orig nil)))))

(define new-sum-merge-aux (sum-lst)
  ;;:returns (mv s pp-lst c-lst to-be-coughed-c-lst)
  (b* (((when (atom sum-lst))
        (mv ''nil nil nil nil))
       ((mv s pp-lst c-lst to-be-coughed-c-lst)
        (new-sum-merge-aux (cdr sum-lst)))
       (term-orig (car sum-lst))
       (term (ex-from-rp-loose term-orig)))
    (case-match term
      (('c & & & &)
       (b* (#|(exp1 `(sum ,term-orig
            (sum-list ,s)
            (sum-list-list ',(m-eval-lst-lst pp-lst-lst
            *a*))
            (sum . ,c-lst)
            (sum . ,to-be-coughed-c-lst)
            (sum . ,to-be-coughed-c-lst)))||#
            ((mv coughed-s coughed-pp-lst c-lst to-be-coughed-c-lst2)
             (c-sum-merge (list term-orig) c-lst :auto-swap nil :level (expt 2 30)))
            (s (s-sum-merge s coughed-s))
            (to-be-coughed-c-lst (s-sum-merge-aux to-be-coughed-c-lst to-be-coughed-c-lst2))
            (pp-lst (pp-sum-merge-aux coughed-pp-lst pp-lst))

            #|(- (m-eval-compare exp1
            `(sum (sum-list ,s)
            (sum-list-list ',(m-eval-lst-lst pp-lst-lst
            *a*))
            (sum . ,c-lst)
            (sum . ,to-be-coughed-c-lst)
            (sum . ,to-be-coughed-c-lst))
            :id 'new-sum-merge-aux-c))||#

            )
         (mv s pp-lst c-lst to-be-coughed-c-lst)))
      (('s & & &)
       (b* ((s (s-sum-merge s (create-list-instance
                               (list term-orig)))))
         (mv s pp-lst c-lst to-be-coughed-c-lst)))
      (('c-res s-arg pp-arg ('list . c-arg-lst))
       (b* (#|(exp1 `(sum ,term-orig
            (rp 's (sum-list ,s))
            (rp 'pp-lst-lst (sum-list-list ',(m-eval-lst-lst pp-lst-lst
            *a*)))
            (rp 'c-lst (sum . ,c-lst))
            (rp 'to-be-coughed-c-lst (sum . ,to-be-coughed-c-lst))
            (rp 'to-be-coughed-c-lst (sum . ,to-be-coughed-c-lst))))||#

            ((mv coughed-s coughed-pp-lst c-lst to-be-coughed-c-lst2)
             (c-sum-merge c-arg-lst c-lst :auto-swap nil :clean-c1-lst t :level (expt 2 30)))

            (s (s-sum-merge s s-arg))
            (s (s-sum-merge s coughed-s))
            (pp-lst (pp-sum-merge-aux (list-to-lst pp-arg) pp-lst))
            (pp-lst (pp-sum-merge-aux coughed-pp-lst pp-lst))
            (to-be-coughed-c-lst (s-sum-merge-aux to-be-coughed-c-lst
                                                  to-be-coughed-c-lst2))
            #|(- (m-eval-compare exp1
            `(sum (rp 's (sum-list ,s))
            (rp 'pp-lst-lst (sum-list-list ',(m-eval-lst-lst pp-lst-lst
            *a*)))
            (rp 'c-lst (sum . ,c-lst))
            (rp 'to-be-coughed-c-lst (sum . ,to-be-coughed-c-lst))
            (rp 'to-be-coughed-c-lst (sum . ,to-be-coughed-c-lst)))
            :id 'new-sum-merge-aux-c-res
            :print-exps t))||#)
         (mv s pp-lst c-lst to-be-coughed-c-lst)))
      (('c-res s-arg pp-arg ''nil)
       (b* ((s (s-sum-merge s s-arg))
            (pp-lst (pp-sum-merge-aux (list-to-lst pp-arg) pp-lst)))
         (mv s pp-lst c-lst to-be-coughed-c-lst)))
      (('sum-list arg-pp)
       (b* ((pp-lst (pp-sum-merge-aux (list-to-lst arg-pp)  pp-lst)))
         (mv s pp-lst c-lst to-be-coughed-c-lst)))
      (('and-list & &)
       (b* ((pp-lst (pp-sum-merge-aux (list term)  pp-lst)))
         (mv s pp-lst c-lst to-be-coughed-c-lst)))
      (('quote &)
       (b* ((pp-lst (pp-sum-merge-aux (list term)  pp-lst)))
         (mv s pp-lst c-lst to-be-coughed-c-lst)))
      (& (cond ((good-4vec-term-p term)
                (b* ((term (4vec->pp-term term-orig))
                     (pp-lst2 (pp-flatten term nil))
                     (pp-lst (pp-sum-merge-aux pp-lst pp-lst2)))
                  (mv s pp-lst c-lst to-be-coughed-c-lst)))
               (t
                (progn$ (hard-error 'new-sum-merge-aux
                                    "Unexpected term ~p0 ~%"
                                    (list (cons #\0 term-orig)))
                        (mv `(cons ,term-orig ,s)
                            pp-lst
                            c-lst
                            to-be-coughed-c-lst))))))))

(define new-sum-merge (term)
  (b* ((sum-lst (extract-new-sum-consed term))
       ((mv s pp-lst c-lst to-be-coughed-c-lst)
        (new-sum-merge-aux sum-lst)))
    (mv s pp-lst c-lst to-be-coughed-c-lst)))

;; (progn
(define well-formed-new-sum (term)
  :returns (res booleanp)
  (or nil
      (case-match term
        (('cons x rest)
         (b* ((x (ex-from-rp-loose x))
              (rest-res (well-formed-new-sum rest)))
           (cond ((good-4vec-term-p x)
                  rest-res)
                 ((case-match x (('and-list & &) t))
                  rest-res)
                 ((case-match x (('s & & &) t))
                  rest-res)
                 ((case-match x (('c & & & &) t))
                  rest-res)
                 #|((case-match x (('d ('rp ''evenpi ('d-sum & & &))) t))
                 rest-res)||#
                 ((case-match x (('c-res & & &) t))
                  rest-res)
                 ((case-match x (('sum-list &) t))
                  rest-res)
                 ((equal x ''0)
                  rest-res)
                 (t
                  nil))))
        (('quote x)
         (integer-listp x))
        (& nil))))

(defmacro mv-nth-0-of-2 (term)
  `(b* (((mv x &) ,term))
     x))

(progn
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
          t)
         (''1
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
               ((case-match x (('s & & &) t))
                (mv (1+ rest-sum) t))
               ((case-match x-orig (('rp ''bitp ('c & & & &)) t))
                (mv (1+ rest-sum) t))
               ((case-match x-orig (('and-list & &) t))
                (mv (1+ rest-sum) t))
               ((case-match x-orig (('rp ''bitp ('c-res & & &)) t))
                (mv (1+ rest-sum) t))
               ((equal x ''0)
                (mv rest-sum t))
               ((equal x ''1)
                (mv (1+ rest-sum) t))
               #|((case-match x (('quote &) t))
               (cond ((natp (cadr x)) ;
               (mv (+ (cadr x) rest-sum) t)) ;
               (t ;
               (mv 0 nil))))||#
               ((case-match x (('sum-list ''nil) t))
                (mv rest-sum t))
               ((case-match x (('sum-list ('list . &)) t))
                (if (light-pp-term-list-p (cdr (cadr x)))
                    (mv (+ rest-sum (len (cdr (cadr x)))) t)
                  (mv 0 nil)))
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

  (define quarternaryp-sum ((sum well-formed-new-sum))
    :returns (res booleanp)
    (b* (((mv res valid)
          (quarternaryp-sum-aux sum)))
      (and valid
           (quarternaryp res)))))

(define c-spec-meta-aux (arg-s arg-pp-lst arg-c-lst to-be-coughed-c-lst quarternaryp)
  :returns (res rp-termp
                :hyp (and (rp-termp arg-s)
                          (rp-term-listp arg-pp-lst)
                          (rp-term-listp arg-c-lst)))
  :prepwork ((local
              (in-theory (disable natp))))
  (b* (((mv s-coughed arg-s) (c-fix-s-args arg-s))

       #|(single-c-from-c-pattern1 (c-pattern1-search arg-s arg-c-lst))||#

       ((mv pp-coughed arg-pp)
        (if (clean-pp-args-cond arg-s arg-c-lst)
            (c-fix-pp-args (create-list-instance arg-pp-lst) (expt 2 30))
          (mv ''nil (create-list-instance arg-pp-lst))))
       (- (and (equal arg-pp '(LIST ('0)))
               (cw "arg-pp: ~p0, pp-coughed:~p1 ~%"
                   arg-pp pp-coughed)
               (hard-error 'nil "" 'nil)))
       (single-c-term (create-c-instance arg-s
                                         arg-pp
                                         (create-list-instance arg-c-lst)))

       ((when (not to-be-coughed-c-lst))
        (cond ((and (equal s-coughed ''nil)
                    #|(not single-c-from-c-pattern1)||#
                    (equal pp-coughed ''nil))
               (if (quotep single-c-term)
                   single-c-term
                 (if quarternaryp
                     `(rp 'bitp ,single-c-term)
                   single-c-term)))
              (t
               (b* ((c-merged-lst  (list single-c-term))
                    #|(c-merged-lst (if single-c-from-c-pattern1
                    (list single-c-term
                    single-c-from-c-pattern1
                    `(-- ,single-c-from-c-pattern1))
                    (list single-c-term)))||#
                    (res `(c-res ,s-coughed ,pp-coughed ,(create-list-instance c-merged-lst))))
                 (if quarternaryp
                     `(rp 'bitp ,res)
                   res)))))

       ((mv s-coughed2 coughed-pp-lst c-merged-lst)
        (c-sum-merge-lst single-c-term to-be-coughed-c-lst :level (expt 2 30)))

       #|(c-merged-lst (if single-c-from-c-pattern1
       (append c-merged-lst
       (list single-c-from-c-pattern1
       `(-- ,single-c-from-c-pattern1)))
       c-merged-lst))||#

       (s-coughed (s-sum-merge s-coughed s-coughed2))

       (coughed-pp-lst (pp-sum-merge-aux (list-to-lst pp-coughed) coughed-pp-lst))
       (pp-coughed (pp-lst-to-pp coughed-pp-lst))

       (res `(c-res ,s-coughed ,pp-coughed (list . ,c-merged-lst)))
       (res (if quarternaryp `(rp 'bitp ,res) res)))
    res))

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
               (b* ((;;(mv s pp c)
                     (mv s pp-lst  c-lst to-be-coughed-c-lst)
                     (new-sum-merge sum))
                    (quarternaryp (quarternaryp-sum sum))

                    #|(- (and (not quarternarp)
                    (cw "s-c-spec This term is not quarternarp ~p0 ~&" sum)))||#)
                 (c-spec-meta-aux s pp-lst c-lst to-be-coughed-c-lst quarternaryp))
             (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                     term)))
          (& term))))
    (mv result t)))

;; (c-spec-meta `(c-spec (cons (binary-and (bit-of a 0) (bit-of b 0))
;;                             (cons (binary-or (binary-and (bit-of a 0) (bit-of b 0))
;;                                              (binary-and (bit-of a 0) (bit-of b 0)))
;;                                   'nil))))

(define s-spec-meta-aux (s pp-lst c-lst)
  :returns (res rp-termp
                :hyp (and (rp-termp s)
                          (rp-term-listp pp-lst)
                          (rp-term-listp c-lst)))
  (b* (#|(exp1 `(sum (sum-list ,s)
       (sum . ,pp-lst)
       (sum . ,c-lst)))||#

       (?limit (expt 2 40))
       (pp (pp-lst-to-pp pp-lst))
       ((mv pp c-lst) (s-of-s-fix s pp c-lst :level (expt 2 30)))

       (pp (if (clean-pp-args-cond ''nil c-lst)
               (s-fix-args pp)
             pp)) ;; clean-with-cond-here

       (c (create-list-instance c-lst))
       (res (create-s-instance pp c))
       #|(- (m-eval-compare `(s '0 ,pp ,c) res :id 's-spec-meta-aux1 :print-exps t))||#
       #|(- (m-eval-compare res `(s '0 (list ,exp1) 'nil) :id 's-spec-meta-aux2))||#)
    res))

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
                         (b* (((mv s pp-lst c-lst &);;(mv s pp c)
                               (new-sum-merge sum)))
                           (s-spec-meta-aux s pp-lst c-lst)))
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
               (b* (((mv s pp-lst c-lst to-be-coughed-c-lst);;(mv s pp c)
                     (new-sum-merge sum))

                    #|(a *a*)||#

                    #|(eval1-sum (m-eval `(sum-list ,sum) a))||#
                    #|(eval2-sum (m-eval `(sum (sum-list s)
                    (sum . ,pp-lst)
                    (sum . ,to-be-coughed-pp-lst)
                    (sum . ,to-be-coughed-pp-lst)
                    (sum . ,c-lst)

                    (sum . ,to-be-coughed-c-lst)
                    (sum . ,to-be-coughed-c-lst))
                    a))||#

                    #|(eval3 (m-eval `(s-c-spec (list ',eval2-sum)) a))||#

                    (quarternaryp (quarternaryp-sum sum))

                    #|(- (and (not quarternarp)
                    (cw "s-c-spec This term is not quarternarp ~p0 ~&" sum)))||#
                    (s-res (s-spec-meta-aux s pp-lst c-lst))
                    (c-res (c-spec-meta-aux s pp-lst c-lst
                                            to-be-coughed-c-lst quarternaryp))
                    (res `(cons ,s-res (cons ,c-res 'nil)))
                    #|(- (if (search-pattern res)
                    (cw "pattern found s-c-spec-meta ~%")
                    nil))||#

                    #|(eval1 (m-eval term a))||#
                    #|(eval2 (m-eval res a))||#
                    #|(- (and (not (equal eval1 eval2))
                    (not (cw "s-c-spec-meta: eval1:~p0, eval2:~p1, eval3:~p2, eval1-sum:~p3 eval2-sum:~p4"
                    eval1 eval2 eval3 eval1-sum eval2-sum))
                    (hard-error 'bad-eval
                    "Mismatching results. ~%"
                    nil)))||#
                    )
                 res)
             (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                     term)))
          (('c-s-spec sum)
           (if (well-formed-new-sum sum)
               (b* (((mv s pp-lst c-lst to-be-coughed-c-lst);;(mv s pp c)
                     (new-sum-merge sum))
                    (quarternaryp (quarternaryp-sum sum))
                    (s-res (s-spec-meta-aux s pp-lst c-lst))
                    (c-res (c-spec-meta-aux s pp-lst c-lst to-be-coughed-c-lst quarternaryp)))
                 `(cons ,c-res (cons ,s-res 'nil)))
             (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                     term)))
          (('s-spec sum)
           (cond ((well-formed-new-sum sum)
                  (b* (((mv s pp-lst c-lst &);;(mv s pp c)
                        (new-sum-merge sum)))
                    (s-spec-meta-aux s pp-lst c-lst)))
                 (t
                  (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                          term))))
          (('c-spec sum)
           (if (well-formed-new-sum sum)
               (b* (((mv s pp-lst c-lst to-be-coughed-c-lst)
                     (new-sum-merge sum))
                    (quarternaryp (quarternaryp-sum sum)))
                 (c-spec-meta-aux s pp-lst c-lst to-be-coughed-c-lst quarternaryp))
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

  ;; (local
  ;;  (defthm lemma1
  ;;    (EQUAL (NOT (ATOM Y)) (CONSP Y))))

  ;; (local
  ;;  (in-theory (disable
  ;;              (:DEFINITION PP-TERM-P)
  ;;              (:DEFINITION rp-termp)
  ;;              (:DEFINITION ASSOC-EQUAL)
  ;;              (:DEFINITION NOT)
  ;;              (:definition assoc-equal)
  ;;              (:definition pairlis2)
  ;;              (:definition pairlis$)
  ;;              (:DEFINITION GLOBAL-TABLE)
  ;;              (:DEFINITION GET-GLOBAL)
  ;;              (:DEFINITION c-merge)
  ;;              (:DEFINITION W)
  ;;              (:REWRITE ACL2::MV-NTH-OF-CONS)

  ;;              +-is-SUM
  ;;              mod2-is-m2
  ;;              floor2-if-f2
  ;;              c-is-f2
  ;;              D-IS-D2
  ;;              s-is-m2
  ;;              s-spec-is-m2
  ;;              SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
  ;;              c-spec-is-f2
  ;;              s-c-spec-is-list-m2-f2
  ;;              c-s-spec-is-list-m2-f2
  ;;              S-OF-C-TRIG-def
  ;;              )))

  ;; (local
  ;;  (defthm pairlis$-opener
  ;;    (equal (pairlis$ (cons x rest) y)
  ;;           (CONS (CONS x (car y))
  ;;                 (PAIRLIS$ rest
  ;;                           (cdr y))))
  ;;    :hints (("Goal"
  ;;             :in-theory (e/d (pairlis$) ())))))

  ;; (local
  ;;  (defthm pairlis$-nil
  ;;    (equal (pairlis$ nil y)
  ;;           nil)
  ;;    :hints (("Goal"
  ;;             :in-theory (e/d (pairlis$) ())))))

  ;; (local
  ;;  (defthm assoc-equal-opener
  ;;    (equal (assoc-equal x (cons (cons key val) b))
  ;;           (if (equal x key)
  ;;               (cons key val)
  ;;             (assoc-equal x b)))
  ;;    :hints (("Goal"
  ;;             :in-theory (e/d (assoc-equal) ())))))

  ;; (local
  ;;  (defthm assoc-equal-nil
  ;;    (equal (assoc-equal key nil)
  ;;           nil)
  ;;    :hints (("Goal"
  ;;             :in-theory (e/d (assoc-equal) ())))))

  ;; (local
  ;;  (defthm rp-evl-of-variable-redef
  ;;    (implies (and (SYMBOLP ACL2::X)
  ;;                  ACL2::X)
  ;;             (EQUAL (RP-EVL ACL2::X ACL2::A)
  ;;                    (CDR (ASSOC-EQUAL ACL2::X ACL2::A))))))

  ;; (local
  ;;  (define if$ (x y z)
  ;;    (if x y z)
  ;;    ///
  ;;    (defthm if$-implies
  ;;      (implies (if$ x y z)
  ;;               (if x y z))
  ;;      :rule-classes :forward-chaining)
  ;;    (defthm rp-evl-of-if-call-redef
  ;;      (implies (and (consp acl2::x)
  ;;                    (equal (car acl2::x) 'if))
  ;;               (equal (rp-evl acl2::x acl2::a)
  ;;                      (if$ (rp-evl (cadr acl2::x) acl2::a)
  ;;                           (rp-evl (caddr acl2::x) acl2::a)
  ;;                           (rp-evl (cadddr acl2::x) acl2::a)))))

  ;;    (defthm if$-test-correct
  ;;      (implies x
  ;;               (equal (if$ x y z)
  ;;                      y)))

  ;;    (defthm if$-test-false
  ;;      (implies (not x)
  ;;               (equal (if$ x y z)
  ;;                      z)))

  ;;    (defthm if$-case-1
  ;;      (iff (if$ x x t)
  ;;           t))

  ;;    (defthm if$-case-2
  ;;      (equal (if$ x y y)
  ;;             y))

  ;;    (defthm eq-is-equal
  ;;      (equal (eq x y)
  ;;             (equal x y)))

  ;;    (defthm if$-of-repeated-boolean
  ;;      (implies (booleanp x)
  ;;               (equal (if$ x x nil)
  ;;                      x)))

  ;;    (defthm if$-test-of-constants
  ;;      (and (iff (if$ test t nil)
  ;;                test)
  ;;           (implies (booleanp test)
  ;;                    (equal (if$ test t nil)
  ;;                           test))
  ;;           (equal (if$ test nil t)
  ;;                  (not test))
  ;;           (equal (if$ test t t)
  ;;                  t)
  ;;           (equal (if$ test nil nil)
  ;;                  nil)))))

  ;; (local
  ;;  (in-theory (disable rp-evl-of-variable)))

  ;; (local
  ;;  (defthm dummy-lemma2
  ;;    (implies (or (EQUAL (CAR (RP-EVL Y CMR::ENV))
  ;;                        'BINARY-AND)
  ;;                 (EQUAL (CAR (RP-EVL Y CMR::ENV))
  ;;                        'AND-LIST))
  ;;             (equal (EQUAL (RP-EVL Y CMR::ENV) ''1)
  ;;                    nil))))

  ;; (local
  ;;  (in-theory (enable extra-s-can-be-pp)))

  ;; (local
  ;;  (defthm EXTRA-S-CAN-BE-PP-def
  ;;    (equal (EXTRA-S-CAN-BE-PP pp c)
  ;;           (AND (EQUAL c ''0)
  ;;                (CASE-MATCH PP (('LIST ('BINARY-AND & &)) T))))))

  (local
   (in-theory (disable
               +-is-SUM
               mod2-is-m2
               floor2-if-f2
               c-is-f2
               ;;  D-IS-D2
               s-is-m2
               s-spec-is-m2
               SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
               c-spec-is-f2
               s-c-spec-is-list-m2-f2
               c-s-spec-is-list-m2-f2
               S-OF-C-TRIG-def)))

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
; d
       c
       m2
;d2
       f2
       times2
       s
       binary-sum
;sort-sum-meta
;evenpi
;d-sum
       sv::3vec-fix
       sv::4vec-fix
;c-s-spec-meta
       ))))

(defmacro ss (&rest args)
  `(s-spec (list . ,args)))

(defmacro dd (&rest args)
  `(d-spec (list . ,args)))

(defmacro cc (&rest args)
  `(c-spec (list . ,args)))

(defmacro sc (&rest args)
  `(s-c-spec (list . ,args)))

(defmacro cs (&rest args)
  `(c-s-spec (list . ,args)))

(define str-cat-lst ((lst string-listp))
  (if (atom lst)
      ""
    (str::cat (car lst)
              (if (atom (cdr lst)) "" "-")
              (str-cat-lst (cdr lst)))))

(acl2::defines
 make-readable
 :verify-guards nil
 (define make-readable (term)
   (declare (xargs :mode :program))
   (b* ((term (ex-from-rp-loose term)))
     (case-match term
       (('equal a b)
        `(equal ,(make-readable a)
                ,(make-readable b)))
       (('s hash pp c)
        (b* ((pp-lst (make-readable-lst (list-to-lst pp)))
             (c-lst (make-readable-lst (list-to-lst c))))
          `(s (,hash). ,(append pp-lst c-lst))))
       (('c hash s pp c)
        (b* ((s-lst (make-readable-lst (list-to-lst s)))
             (pp-lst (make-readable-lst (list-to-lst pp)))
             (c-lst (make-readable-lst (list-to-lst c))))
          `(c (,hash) . ,(append s-lst pp-lst c-lst))))
       (('-- n)
        `(-- ,(make-readable n)))
       (''1
        1)
       (('and-list & bits)
        (b* ((lst (make-readable-lst (list-to-lst bits)))
             (str (str-cat-lst lst))
             (sym (intern$ str "RP")))
          sym))
       (('bit-of name ('quote index))
        (b* ((sym (sa  (ex-from-rp-loose name) index)))
          (symbol-name sym)))
       (('bit-of name index)
        (b* ((sym (sa  (ex-from-rp-loose name) index)))
          (symbol-name sym)))
       (& (progn$
           (hard-error 'make-readable
                       "Unexpected term instance~p0~%"
                       (list (cons #\0 term)))
           nil)))))
 (define make-readable-lst (lst)
   (if (atom lst)
       nil
     (cons (make-readable (car lst))
           (make-readable-lst (cdr lst))))))
