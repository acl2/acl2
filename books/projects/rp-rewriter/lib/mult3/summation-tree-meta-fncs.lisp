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

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(include-book "pp-flatten-meta-fncs")

(include-book "std/util/defines" :dir :system)

(include-book "sum-merge-fncs")

(local
 (in-theory (disable +-IS-SUM)))

(progn
  (encapsulate
    (((stingy-pp-clean) => *))
    (local
     (defun stingy-pp-clean ()
       nil)))

  (define return-t ()
    t)
  (define return-nil ()
    nil)

  (defmacro enable-stingy-pp-clean (enabled)
    (if enabled
        `(defattach  stingy-pp-clean return-t)
      `(defattach  stingy-pp-clean return-nil)))

  (enable-stingy-pp-clean t)

  (define clean-pp-args-cond (s c-lst)
    (or (not (stingy-pp-clean))
        (and (equal s ''nil)
             (or (atom c-lst)
                 (atom (cdr c-lst)))))))

(define get-c-args ((c rp-termp))
  :inline t
  :returns (mv (hash-code integerp)
               (s-args rp-termp
                       :hyp (rp-termp c))
               (pp-args rp-termp
                        :hyp (rp-termp c))
               (c-arg-lst rp-term-listp
                          :hyp (rp-termp c))
               (valid symbolp))
  (b* ((c (ex-from-rp$ c)))
    (case-match c
      (('c ('quote hash-code) s pp ('list . c-lst))
       (mv (ifix hash-code) s pp c-lst 'c))
      (('c ('quote hash-code) s pp ''nil)
       (mv (ifix hash-code) s pp nil 'c))
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
    (+ (calculate-pp-hash pp)
       (* 2 (get-hash-code-of-c c))))

  (define calculate-c-hash (s pp c)
    :returns (hash-code integerp)
    (+ (get-hash-code-of-s s)
       (calculate-pp-hash pp)
       (* 2 (get-hash-code-of-c c)))))


(local
 (in-theory (disable rp-termp)))

(local
 (defthm measure-lemma-loose1
   (IMPLIES (AND
             (CONSP (ex-from-rp MAX-TERM))
             (CONSP (CDR (ex-from-rp MAX-TERM)))
             (NOT (CDDR (ex-from-rp MAX-TERM))))
            (O< (CONS-COUNT (CADR (ex-from-rp MAX-TERM)))
                (CONS-COUNT MAX-TERM)))
   :hints (("Goal"
            :induct (ex-from-rp MAX-TERM)
            :do-not-induct t
            :in-theory (e/d (ex-from-rp
                             measure-lemmas)
                            ((:REWRITE MEASURE-LEMMA1)
                             (:REWRITE CONS-COUNT-ATOM)

                             (:REWRITE DEFAULT-CDR)
                             (:REWRITE MEASURE-LEMMA6-5)
                             (:DEFINITION EX-FROM-RP)
                             (:REWRITE MEASURE-LEMMA1-2)))))))
(local
 (defthm measure-lemma-loose2
   (IMPLIES (AND  (CONSP (ex-from-rp MAX-TERM))
                  (CONSP (CDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDDDR (ex-from-rp MAX-TERM)))
                  (NOT (CDR (CDDDDR (ex-from-rp MAX-TERM)))))
            (O< (CONS-COUNT (CDR (CAR (CDDDDR (ex-from-rp MAX-TERM)))))
                (CONS-COUNT MAX-TERM)))
   :hints (("Goal"
            :induct (ex-from-rp MAX-TERM)
            :do-not-induct t
            :in-theory (e/d (ex-from-rp
                             measure-lemmas)
                            ((:REWRITE DEFAULT-CDR)
;(:REWRITE EX-FROM-RP-LOOSE-IS-RP-TERMP)
                             (:DEFINITION RP-TERMP)
                             (:REWRITE MEASURE-LEMMA1-2)
                             (:REWRITE MEASURE-LEMMA1)))))))

(local
 (defthm measure-lemma-loose3
   (IMPLIES (AND  (CONSP (ex-from-rp MAX-TERM))
                  (CONSP (CDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDDDR (ex-from-rp MAX-TERM)))
                  (NOT (CDR (CDDDDR (ex-from-rp MAX-TERM)))))
            (O< (CONS-COUNT (CDR (CADDDR (ex-from-rp MAX-TERM))))
                (CONS-COUNT MAX-TERM)))
   :hints (("Goal"
            :induct (ex-from-rp MAX-TERM)
            :do-not-induct t
            :in-theory (e/d (ex-from-rp
                             measure-lemmas)
                            ((:REWRITE DEFAULT-CDR)
                             (:REWRITE MEASURE-LEMMA1)
                             (:REWRITE MEASURE-LEMMA1-2)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE ACL2::O<=-O-FINP-DEF)
                             ))))))

(local
 (defthm measure-lemma-loose4
   (IMPLIES (AND  (CONSP (ex-from-rp MAX-TERM))
                  (CONSP (CDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDDDR (ex-from-rp MAX-TERM)))
                  (NOT (CDR (CDDDDR (ex-from-rp MAX-TERM)))))
            (O< (CONS-COUNT (CDR (CADDR (ex-from-rp MAX-TERM))))
                (CONS-COUNT MAX-TERM)))
   :hints (("Goal"
            :induct (ex-from-rp MAX-TERM)
            :do-not-induct t
            :in-theory (e/d (ex-from-rp
                             measure-lemmas)
                            ((:REWRITE DEFAULT-CDR)
                             (:REWRITE MEASURE-LEMMA1)
                             (:REWRITE MEASURE-LEMMA1-2)

                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE ACL2::O<=-O-FINP-DEF)

                             ))))))
(local
 (defthm local-measure-lemma4
   (implies (and
             (integerp term1)
             (integerp term2)
             (integerp term3)
             (o<= term2 term3)
             (o< term1 term2))
            (o< term1 term3))
   :hints (("Goal"
            :in-theory (e/d (o<) ())))))

(local
 (defthm local-measure-lemma5
   (implies (and (consp term)
                 (consp (cdr term))
                 (consp (cddr term))
                 (consp (cdddr term))
                 (consp (cddddr term))
                 (consp (car (cddddr term)))
                 (not (cdr (cddddr term))))
            (o< (cons-count (cdr (car (cddddr term))))
                (cons-count term)))
   :hints (("Goal"
            :in-theory (e/d (cons-count) ())))))

(local
 (defthm local-measure-lemma6
   (implies (and (consp term)
                 (consp (cdr term))
                 (consp (cddr term))
                 (consp (cdddr term))
                 (consp (car (cdddr term)))
                 (not (cdr (cdddr term))))
            (o< (cons-count (cdr (car (cdddr term))))
                (cons-count term)))
   :hints (("Goal"
            :in-theory (e/d (cons-count) ())))))

(local
 (defthm local-measure-lemma7
   (implies (and (consp (ex-from-rp term))
                 (consp (cdr (ex-from-rp term)))
                 (consp (cddr (ex-from-rp term)))
                 (consp (cdddr (ex-from-rp term)))
                 (consp (cddddr (ex-from-rp term)))
                 (consp (car (cddddr (ex-from-rp term))))
                 (not (cdr (cddddr (ex-from-rp term)))))
            (o< (cons-count (cdr (car (cddddr (ex-from-rp term)))))
                (cons-count term)))
   :hints (("goal"
            :use ((:instance local-measure-lemma5 (term (ex-from-rp term)))
                  (:instance local-measure-lemma4
                             (term1 (CONS-COUNT (CDR (CAR (CDDDDR (ex-from-rp TERM))))))
                             (term2 (CONS-COUNT (ex-from-rp TERM)))
                             (term3 (CONS-COUNT TERM))))
            :in-theory (e/d (measure-lemmas)
                            (local-measure-lemma5 local-measure-lemma4))))))

(local
 (defthm local-measure-lemma8
   (implies (and (consp (ex-from-rp term))
                 (consp (cdr (ex-from-rp term)))
                 (consp (cddr (ex-from-rp term)))
                 (consp (cdddr (ex-from-rp term)))
                 (consp (car (cdddr (ex-from-rp term))))
                 (not (cdr (cdddr (ex-from-rp term)))))
            (o< (cons-count (cdr (car (cdddr (ex-from-rp term)))))
                (cons-count term)))
   :hints (("goal"
            :use ((:instance local-measure-lemma6 (term (ex-from-rp term)))
                  (:instance local-measure-lemma4
                             (term1 (CONS-COUNT (CDR (CAR (CDDDR (ex-from-rp TERM))))))
                             (term2 (CONS-COUNT (ex-from-rp TERM)))
                             (term3 (CONS-COUNT TERM))))
            :in-theory (e/d (measure-lemmas) (local-measure-lemma4 local-measure-lemma6))))))


(local
 (defthm local-measure-lemma10
   (IMPLIES (AND (consp (ex-from-rp TERM)))
            (O< (CONS-COUNT (CDR (ex-from-rp TERM)))
                (CONS-COUNT TERM)))
   :hints (("Goal"
            :in-theory (e/d (measure-lemmas) ())))))

(local
 (defthm local-measure-lemma11
   (implies (and
             (consp (ex-from-rp term)))
            (o< 1 (cons-count term)))
   :hints (("goal"
            :in-theory (e/d (ex-from-rp cons-count) ())))))

(local
 (in-theory (disable ex-from-rp
                     (:definition acl2::apply$-badgep)
                     (:linear acl2::apply$-badgep-properties . 1)
                     (:definition subsetp-equal)
                     (:definition member-equal)
                     (:rewrite
                      acl2::member-equal-newvar-components-1)
                     (:definition rp-term-listp)
                     include-fnc)))

(local
 (defthm single-c-p-rp-term-listp-lemma
   (implies (and (single-c-p term)
                 (rp-termp term)
                 (equal (car (car (cddddr term)))
                        'list))
            (rp-term-listp (cdr (car (cddddr term)))))
   :hints (("goal"
            :expand ((rp-termp term)
                     (rp-term-listp (cddddr term))
                     (rp-termp (car (cddddr term)))
                     (rp-term-listp (cddr term))
                     (rp-term-listp (cdddr term))
                     (rp-term-listp (cdr term)))
            :in-theory (e/d (rp-term-listp
                             single-c-p)
                            ())))))

(local
 (defthm dummy-rp-term-listp-lemma
   (implies (and (rp-term-listp lst) (consp lst))
            (rp-termp (car lst)))
   :hints (("goal"
            :in-theory (e/d (rp-termp rp-term-listp) ())))))

(acl2::defines
 get-max-min-val
 :flag-defthm-macro defthm-get-min-max-val
 :flag-local nil
 :prepwork ((local
             (in-theory (e/d (measure-lemmas
                              list-to-lst)
                             (measure-lemma1
                              measure-lemma1-2
                              (:rewrite acl2::o-p-o-infp-car)
                              (:rewrite default-car)
                              not-include-rp)))))

 :verify-guards nil
 (define get-max-min-val ((term rp-termp))
   :measure (cons-count term)
   :returns (mv  (max-val integerp)
                 (min-val integerp)
                 (valid booleanp))
   (b* (((when (is-rp-bitp term)) (mv 1 0 t))
        (term (ex-from-rp$ term)))
     (cond
      ((single-c-p term)
       (b* (((mv s pp c)
             (case-match term (('c & s pp c) (mv s pp c)) (& (mv nil nil nil))))
            ((mv s-max-val s-min-val s-valid)
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
            ((unless (and s-valid pp-valid c-valid))
             (mv 0 0 nil)))
         (mv (floor (+ s-max-val pp-max-val c-max-val) 2)
             (floor (+ s-min-val pp-min-val c-min-val) 2)t)))
      ((single-s-p term) (mv 1 0 t))
      ((equal term ''1) (mv 1 1 t))
      ((and-list-p term) (mv 1 0 t))
      ((--.p term)
       (b* ((n (cadr term))
            ((mv max-val min-val valid)
             (get-max-min-val n)))
         (mv (- min-val) (- max-val) valid)))
      (t (mv 0 0 nil)))))
 (define get-max-min-val-lst ((lst rp-term-listp))
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
 (verify-guards get-max-min-val-lst
   :hints (("Goal"
            :in-theory (e/d (RP-TERM-LISTP) ())))))

(define is-c-bitp-traverse ((single-c rp-termp))
  :returns (res booleanp)
  (b* (((mv max-val min-val valid)
        (get-max-min-val single-c)))
    (and
     valid
     (equal min-val 0)
     (equal max-val 1))))

;; a b c e
;; a b c d e

(local
 (defthm dummmy-rp-term-listp-lemma
   (implies (and (rp-term-listp x)
                 (consp x))
            (rp-term-listp (cdr x)))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (rp-term-listp) ())))))

(progn
  (define pp-lst-subsetp ((pp-lst1 rp-term-listp)
                          (pp-lst2 rp-term-listp))
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

  (define pp-subsetp ((pp1 rp-termp)
                      (pp2 rp-termp))
    (b* ((pp1-lst (list-to-lst pp1))
         (pp2-lst (list-to-lst pp2)))
      (pp-lst-subsetp pp1-lst pp2-lst))))


(progn
  (define and-lst-subsetp ((pp-lst1 rp-term-listp)
                           (pp-lst2 rp-term-listp))
    :measure (+ (cons-count pp-lst1)
                (cons-count pp-lst2))
    :prepwork ((local
                (in-theory (enable measure-lemmas))))
    (b* (((when (atom pp-lst1)) t)
         ((when (atom pp-lst2)) (atom pp-lst1))
         (cur1 (car pp-lst1))
         (cur2 (car pp-lst2)))
      (cond ((equal cur1 cur2)
             (and-lst-subsetp (cdr pp-lst1) (cdr pp-lst2)))
            ((lexorder2- cur1 cur2) nil)
            (t (and-lst-subsetp pp-lst1 (cdr pp-lst2))))))

  (define and-subsetp ((pp1 rp-termp)
                       (pp2 rp-termp))
    (b* ((pp1 (ex-from-rp$ pp1))
         (pp2 (ex-from-rp$ pp2))
         ((unless (and (case-match pp1 (('and-list & ('list . &)) t))
                       (case-match pp2 (('and-list & ('list . &)) t))))
          nil)
         
         (pp1-lst (cdr (caddr pp1)))
         (pp2-lst (cdr (caddr pp2))))
      (and-lst-subsetp pp1-lst pp2-lst))))




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
  (define abs-term (term)
    :inline t
    :returns (mv (abs rp-termp :hyp (rp-termp term))
                 (signed booleanp))
    (case-match term (('-- c1) (mv c1 t)) (& (mv term nil))))

  (define ligth-compress-s-c$fix-pp-lst$for-s ((pp1-lst rp-term-listp)
                                               (pp2-lst rp-term-listp))
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
                                 (:REWRITE MEASURE-LEMMA1-2)
                                 (:DEFINITION RP-EQUAL))))))
    :returns (mv (res-pp1-lst rp-term-listp
                              :hyp (rp-term-listp pp1-lst))
                 (changed booleanp))
    (b* (((when (or (atom pp1-lst)
                    (atom pp2-lst)))
          (mv pp1-lst nil))
         (c1 (car pp1-lst))
         (c2 (car pp2-lst))
         ((mv new-c1 changed)
          (cond ((rp-equal c1 c2)
                 (case-match c1
                   (('-- n)
                    (mv n t))
                   (&
                    (mv `(-- ,c1) t))))
                (t (mv nil nil))))
         ((when changed)
          (b* (((mv pp1-lst-rest &)
                (ligth-compress-s-c$fix-pp-lst$for-s (cdr pp1-lst) (cdr pp2-lst) )))
            (mv (cons new-c1 pp1-lst-rest) t)))
         ((mv pp-order &)
          (pp-order (ex-from-rp/--loose c1) (ex-from-rp/--loose c2))))
      (if pp-order
          (b* (((mv pp1-lst-rest rest-changed)
                (ligth-compress-s-c$fix-pp-lst$for-s (cdr pp1-lst) pp2-lst )))
            (mv (cons-with-hint c1 pp1-lst-rest pp1-lst) rest-changed))
        (b* (((mv pp1-lst-rest rest-changed)
              (ligth-compress-s-c$fix-pp-lst$for-s pp1-lst (cdr pp2-lst) )))
          (mv pp1-lst-rest rest-changed)))))

  (define light-compress-s-c$fix-pp$for-s ((pp1 rp-termp)
                                           (pp2 rp-termp))
    :returns (res-pp1 rp-termp :hyp (rp-termp pp1))
    (b* ((pp1-lst (list-to-lst pp1))
         (pp2-lst (list-to-lst pp2))
         ((mv pp1-lst changed)
          (ligth-compress-s-c$fix-pp-lst$for-s pp1-lst pp2-lst)))
      (if changed
          (create-list-instance pp1-lst)
        pp1)))

  (define light-compress-s-c$pass-pp-lst ((pp1-lst rp-term-listp)
                                          (pp2-lst rp-term-listp))
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
          (abs-term c1))
         ;;(case-match c1 (('-- c1) (mv c1 t)) (& (mv c1 nil))))
         ((mv c2-abs c2-signed)
          (abs-term c2))
;(case-match c2 (('-- c2) (mv c2 t)) (& (mv c2 nil))))
         ((mv to-pass passable)
          (cond ((and (rp-equal c1-abs c2-abs)
                      (not (equal c1-signed c2-signed)))
                 (mv c1 t))
                (t (mv nil nil))))
         ((when passable)
          (b* (((mv pp1-lst-rest pp2-lst-rest &)
                (light-compress-s-c$pass-pp-lst (cdr pp1-lst) (cdr pp2-lst))))
            (mv pp1-lst-rest (cons to-pass pp2-lst-rest) t)))
         ((mv pp-order &)
          (pp-order (ex-from-rp/--loose c1-abs) (ex-from-rp/--loose c2-abs))))
      (if pp-order
          (b* (((mv pp1-lst-rest pp2-lst-rest rest-changed)
                (light-compress-s-c$pass-pp-lst (cdr pp1-lst) pp2-lst)))
            (mv (cons-with-hint c1 pp1-lst-rest pp1-lst)
                pp2-lst-rest rest-changed))
        (b* (((mv pp1-lst-rest pp2-lst-rest rest-changed)
              (light-compress-s-c$pass-pp-lst pp1-lst (cdr pp2-lst))))
          (mv pp1-lst-rest (cons-with-hint c2 pp2-lst-rest pp2-lst) rest-changed)))))

  (define light-compress-s-c$pass-pp ((pp1 rp-termp)
                                      (pp2 rp-termp))
    :returns (mv (res-pp1 rp-termp :hyp (rp-termp pp1))
                 (res-pp2 rp-termp :hyp (and (rp-termp pp1)
                                             (rp-termp pp2)))
                 (changed booleanp))
    (b* ((pp1-lst (list-to-lst pp1))
         (pp2-lst (list-to-lst pp2))
         ((mv pp1-lst pp2-lst changed)
          (light-compress-s-c$pass-pp-lst pp1-lst pp2-lst)))
      (if changed
          (mv (create-list-instance pp1-lst) (create-list-instance pp2-lst) t)
        (mv pp1 pp2 nil))))

  (local
   (defthmd o<-chain
     (and (implies (and
                    (syntaxp (equal (all-vars x)
                                    (all-vars y)))
                    (force (O< (cons-count x) (cons-count y))))
                   (O< (cons-count (car x))
                       (cons-count y)))
          (implies (and
                    (syntaxp (equal (all-vars x)
                                    (all-vars y)))
                    (force (O< (cons-count x) (cons-count y))))
                   (O< (cons-count (cdr x))
                       (cons-count y))))
     :hints (("Goal"
              :in-theory (e/d (cons-count) ())))))

  (local
   (defthmd o<-chain-2
     (and (implies (and
                    (syntaxp (equal (all-vars x)
                                    (all-vars y)))
                    (force (O< (cons-count x) (cons-count y))))
                   (O< (cons-count (ex-from-rp x))
                       (cons-count y))))
     :hints (("Goal"
              :in-theory (e/d (ex-from-rp
                               measure-lemmas
;cons-count
                               )
                              ())))))

  (define light-compress-s-c-aux ((pp rp-termp)
                                  (c-arg rp-termp))
    :returns (mv (pp-res rp-termp :hyp (rp-termp pp))
                 (c-arg-res rp-termp :hyp (and (rp-termp pp)
                                               (rp-termp c-arg)))
                 (changed booleanp))
    :measure (cons-count c-arg)
    :hints (("Goal"
             :in-theory (e/d (measure-lemmas
                              o<-chain-2
                              o<-chain)
                             ())))
    (case-match c-arg
      (('list single-c)
       (b* ((single-c (ex-from-rp$ single-c))
            ((unless (and (single-c-p single-c)))
             (mv pp c-arg nil))
            (pp-arg1 (cadddr single-c))
            (c-arg1 (car (cddddr single-c)))
            ((mv pp-new pp-arg1 changed)
             (light-compress-s-c$pass-pp pp pp-arg1))
            ((unless changed)
             (mv pp c-arg nil))
            ((mv pp-arg1 c-arg1 &)
             (light-compress-s-c-aux pp-arg1 c-arg1)))
         (mv pp-new `(list (c ',(calculate-c-hash (caddr single-c) pp-arg1 c-arg1)
                              ,(caddr single-c) ,pp-arg1 ,c-arg1))
             t)))
      (& (mv pp c-arg nil))))

  (define light-compress-s-c ((term rp-termp))
    :prepwork ((local
                (in-theory (enable measure-lemmas))))
    :returns (res-term rp-termp :hyp (rp-termp term))
    (b* ((term-orig term)
         (term (ex-from-rp$ term)))
      (case-match term
        (('s & pp ('list single-c))
         (b* ((single-c (ex-from-rp$ single-c)))
           (case-match single-c
             (('c & & c-pp &)
              (b* ((pp (light-compress-s-c$fix-pp$for-s pp c-pp))
                   ((mv pp c-arg changed)
                    (light-compress-s-c-aux pp (cadddr term)))
                   ((Unless changed)
                    term-orig))
                `(s ',(calculate-s-hash pp c-arg) ,pp ,c-arg)))
             (& term-orig))))
        (('c & s-arg pp c-arg)
         (b* (((mv pp c-arg changed)
               (light-compress-s-c-aux pp c-arg)))
           (if changed
               `(c ',(calculate-c-hash s-arg pp c-arg) ,s-arg ,pp ,c-arg)
             term-orig)))
        (& term-orig))))

  (define case-match-|('s & pp ('list single-c))|
    (term)
    :inline t
    "Used by decompress-s-c"
    (case-match term
      (('s & pp ('list single-c))
       (mv pp single-c t))
      (& (mv ''nil ''nil nil))))

  (define case-match-|('c & ''nil pp ('list single-c))| (term)
    :inline t
    "Used by decompress-s-c"
    (case-match term
      (('c & ''nil pp ('list single-c))
       (mv pp single-c t))
      (& (mv ''nil ''nil nil))))

  (define case-match-|('c & ''nil pp ''nil)| (term)
    :inline t
    "Used by decompress-s-c"
    (case-match term
      (('c & ''nil pp ''nil)
       (mv pp t))
      (& (mv ''nil nil))))

  (define decompress-s-c ((term rp-termp) &key (limit '(expt 2 30)))
    :measure (nfix limit)
    :guard (natp limit)
    :returns (mv (res-term)
                 (coughed-term))
    :verify-guards nil
    :prepwork ((local
                (in-theory (enable case-match-|('s & pp ('list single-c))|
                                   case-match-|('c & ''nil pp ('list single-c))|
                                   case-match-|('c & ''nil pp ''nil)|))))

    (b* (((when (zp limit)) (mv term ''nil))
         (term-orig term)
         (term (ex-from-rp$ term))
         ((mv pp single-c match)
          (case-match-|('s & pp ('list single-c))| term))
         ((when match)
          (b* (((mv single-c coughed-pp)
                (decompress-s-c single-c :limit (1- limit)))
               (pp (pp-sum-merge pp coughed-pp))
               (pp (s-fix-args pp))
               (c (create-list-instance (list single-c))))
            (mv `(s ',(calculate-s-hash pp c) ,pp ,c)
                ''nil)))
         ((mv pp single-c match)
          (case-match-|('c & ''nil pp ('list single-c))| term))
         ((when match)
          (b* (((mv single-c coughed-pp)
                (decompress-s-c single-c :limit (1- limit)))
               (pp (pp-sum-merge pp coughed-pp))
               ((mv pp-coughed pp) (c-fix-pp-args pp ))
               (c (create-list-instance (list single-c))))
            (mv `(c ',(calculate-c-hash ''nil pp c) 'nil ,pp ,c)
                pp-coughed)))
         ((mv pp match)
          (case-match-|('c & ''nil pp ''nil)| term))
         ((when match)
          (b* (((mv pp-coughed pp) (c-fix-pp-args pp))
               (c ''nil))
            (mv `(c ',(calculate-c-hash ''nil pp c) 'nil ,pp ,c)
                pp-coughed))))
      (mv term-orig ''nil))
    ///

    (acl2::defret
     rp-termp-of-<fn>
     :hyp (rp-termp term)
     (and (rp-termp res-term)
          (rp-termp coughed-term)))

    (verify-guards decompress-s-c-fn)))

(progn
  (define negate-lst-aux ((lst rp-term-listp))
    :returns (negated-lst rp-term-listp :hyp (rp-term-listp lst))
    (b* (((when (atom lst)) lst)
         (rest (negate-lst-aux (cdr lst)))
         (cur-orig (car lst))
         (cur (ex-from-rp$ cur-orig)))
      (case-match cur
        (('-- term)
         (cons term rest))
        (& (cons `(-- ,cur-orig)
                 rest)))))

  (define negate-lst ((lst rp-term-listp)
                      &optional (enabled 't))
    :inline t
    :returns (negated-lst rp-term-listp :hyp (rp-term-listp lst))
    (if enabled
        (negate-lst-aux lst)
      lst))

  (define negate-list-instance ((term rp-termp)
                                &optional (enabled 't))
    :returns (res rp-termp :hyp (rp-termp term))
    :inline t
    (create-list-instance (negate-lst (list-to-lst term) enabled))))



(progn
  (encapsulate
    (((c-pattern1-reduce-enabled) => *))
    (local
     (defun c-pattern1-reduce-enabled ()
       nil)))

  (defmacro enable-c-pattern1-reduce (enable)
    (if enable
        `(defattach c-pattern1-reduce-enabled return-t)
      `(defattach c-pattern1-reduce-enabled return-nil)))

  (enable-c-pattern1-reduce t))


(define c-pattern1-reduce ((s rp-termp)
                           (pp rp-termp)
                           (c rp-termp))
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
   ((not (c-pattern1-reduce-enabled)) (mv s pp c))
   (t
    (case-match c
      (('list ('c & ''nil c-pp &))
       (b* (((unless (pp-subsetp pp c-pp)) (mv s pp c))
            (--pp (negate-list-instance pp))
            (single-c `(c '0 ,s ,--pp ,c))
            (compressed (light-compress-s-c single-c)))
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
                (('c & s pp ('list . c-lst)) ;; changed it to this way to prove
                 ;; measure of c-sum-merge with count-c.
                 (mv s pp `(list . ,c-lst)))
                (('c & s pp ''nil)
                 (mv s pp ''nil))
                (& (mv s pp c)))))
           (& (mv s pp c)))))
      (& (mv s pp c))))))


(local
 (defthmd and-subsetp-IMPLIES-and-list-intance
   (implies (and-subsetp pp1 pp2)
            (B* ((PP1 (EX-FROM-RP$ PP1))
                 (PP2 (EX-FROM-RP$ PP2)))
              (AND (CASE-MATCH PP1 (('AND-LIST & ('LIST . &)) T))
                   (CASE-MATCH PP2 (('AND-LIST & ('LIST . &)) T)))))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (and-subsetp) ())))))
               
(define c-pattern2-reduce ((pp-lst-coughed rp-term-listp)
                           (single-c rp-termp))
  :returns (mv (res-pp-lst-coughed
                rp-term-listp
                :hyp (and (rp-term-listp pp-lst-coughed)
                          (rp-termp single-c))
                :hints (("Goal"
                         :use ((:instance and-subsetp-IMPLIES-and-list-intance
                                          (pp1 (CADDR (CADDDR (EX-FROM-RP
                                                               SINGLE-C))))
                                          (pp2 (CADR (CADDDR (EX-FROM-RP
                                                              SINGLE-C)))))
                               (:instance and-subsetp-IMPLIES-and-list-intance
                                          (pp1 (CADDDR (CADDDR (EX-FROM-RP SINGLE-C))))
                                          (pp2 (CADR (CADDDR (EX-FROM-RP SINGLE-C))))))
                         :in-theory (e/d () ()))))
               (res-single-c rp-termp
                             :hyp
                             (and (rp-termp single-c))))
  :verify-guards nil
  (b* ((single-c-orig single-c)
       (single-c (ex-from-rp$ single-c)))
    (case-match single-c
      (('c & ''nil ('list pp1 pp2 pp3) ''nil)
       (b* (((unless (and (and-subsetp pp2 pp1)
                          (and-subsetp pp3 pp1)))
             (mv pp-lst-coughed single-c-orig))
            (pp2 (ex-from-rp$ pp2))
            (pp3 (ex-from-rp$ pp3))
            (and-list2 (cdr (caddr pp2)))
            (and-list3 (cdr (caddr pp3)))
            (res-and-list (merge-sorted-and$-lists and-list2 and-list3))
            (res-and (create-and-list-instance res-and-list)))
         (mv (pp-sum-merge-aux (list res-and)
                               pp-lst-coughed)
             ''0)))
      (('c & ''nil ('list pp1 pp2) ''nil)
       (b* (((unless (and (and-subsetp pp2 pp1)))
             (mv pp-lst-coughed single-c-orig)))
         (mv (pp-sum-merge-aux (list pp1)
                               pp-lst-coughed)
             ''0)))
      (& (mv pp-lst-coughed single-c-orig))))
  ///
  (verify-guards c-pattern2-reduce
    :hints (("Goal"
             :use ((:instance and-subsetp-IMPLIES-and-list-intance
                                          (pp1 (CADDR (CADDDR (EX-FROM-RP
                                                               SINGLE-C))))
                                          (pp2 (CADR (CADDDR (EX-FROM-RP
                                                              SINGLE-C)))))
                               (:instance and-subsetp-IMPLIES-and-list-intance
                                          (pp1 (CADDDR (CADDDR (EX-FROM-RP SINGLE-C))))
                                          (pp2 (CADR (CADDDR (EX-FROM-RP SINGLE-C))))))
             :in-theory (e/d () ())))))
           

(define create-c-instance ((s rp-termp)
                           (pp rp-termp)
                           (c rp-termp))
;:inline t
  :returns (c-res rp-termp :hyp (and (rp-termp pp)
                                     (rp-termp s)
                                     (rp-termp c)))
  (b* (((mv s pp c)
        (c-pattern1-reduce s pp c)))
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

(progn
  (encapsulate
    (((s-pattern1-reduce-enabled) => *))
    (local
     (defun s-pattern1-reduce-enabled ()
       nil)))

  (defmacro enable-s-pattern1-reduce (enable)
    (if enable
        `(defattach  s-pattern1-reduce-enabled return-t)
      `(defattach  s-pattern1-reduce-enabled return-nil)))

  (enable-s-pattern1-reduce t))


(define s-pattern1-reduce ((pp rp-termp)
                           (c rp-termp))
  ;; :returns (mv pp c reduced reducedp)
  ;; Search for (s pp1 (c pp1 rest))
  ;; which is equivalant to (s (c -pp1 rest))
  ;; which is created with compress-s-c
  ;; if the max/min val of (c -pp1 rest) is 0/-1,
  ;; then reducedp=1 and reduced=(-- (c -pp1 rest))
  ;; but it is decompressed so reduced=(sum pp1 (-- (c rest)))
  ;; reduced will be the value returned from create-s-instance right away.

  :returns (mv #|(pp-res rp-termp :hyp (and (rp-termp pp)
            (rp-termp c)))||#
            #|(c-res rp-termp :hyp (and (rp-termp pp)
            (rp-termp c)))||#
            (reduced rp-termp :hyp (and (rp-termp pp)
                                        (rp-termp c)))
            (reducedp booleanp))
  (b* (((unless (s-pattern1-reduce-enabled))
        (mv ''0 nil)))
    (case-match c
      (('list ('c & ''nil c-pp &))
       (b* (((unless (pp-subsetp pp c-pp))
             (mv ''0 nil))
            (compressed (light-compress-s-c `(s '0 ,pp ,c))))
         (case-match compressed
           (('s & ''nil ('list single-c))
            (b* (((mv max min valid) (get-max-min-val single-c))
                 ((unless (and valid
                               (= max 0)
                               (= min -1)))
                  (mv ''0 nil))
                 ((mv res coughed-pp) (decompress-s-c single-c))
                 (coughed-pp (negate-list-instance coughed-pp)))
              (mv `(rp 'bitp (c-res 'nil ,coughed-pp (list (-- ,res))))
                  t)))
           (& (mv ''0 nil)))))
      (& (mv ''0 nil)))))

;; (compress-s-c '(s '0 (list c b a) (list (c '0 'nil (list d c a) 'nil))))
;; (decompress-s-c '(S '0 (LIST B) (LIST (C '0 'NIL (LIST D (-- C) (-- A)) 'NIL))))



(progn
  (define and-list-instance-to-binary-and-aux ((lst rp-term-listp))
    :returns (res rp-termp
                  :hyp (rp-term-listp lst))
    (if (atom lst)
        ''1
      `(binary-and ,(car lst)
                   ,(and-list-instance-to-binary-and-aux (cdr lst)))))

  (define and-list-instance-to-binary-and ((term rp-termp))
    :Returns (res rp-termp
                  :hyp (rp-termp term))
    (case-match term
      (('and-list & ('list . lst))
       (and-list-instance-to-binary-and-aux lst))
      (& term))))

(define s-pattern2-reduce ((pp rp-termp)
                           (c rp-termp))
  :returns (mv (reduced rp-termp :hyp (and (rp-termp pp)
                                           (rp-termp c)))
               (reducedp booleanp))
  (b* (((unless (equal c ''nil))
        (mv ''0 nil)))
    (case-match pp
      (('list pp1 pp2 pp3)
       (b* (((unless (and (and-subsetp pp2 pp1)
                          (and-subsetp pp3 pp1)))
             (mv ''0 nil))
            (pp
             `(binary-xor ,(and-list-instance-to-binary-and pp1)
                          (binary-xor ,(and-list-instance-to-binary-and pp2)
                                      ,(and-list-instance-to-binary-and pp3))))
            ((unless (pp-term-p pp))
             (mv ''0 nil)))
         (mv `(rp 'bitp (sum-list ,(create-list-instance (pp-flatten pp nil)))) t)))
      (('list pp1 pp2)
       (b* (((unless (and (and-subsetp pp2 pp1)))
             (mv ''0 nil))
            (pp
             `(binary-xor ,(and-list-instance-to-binary-and pp1)
                          ,(and-list-instance-to-binary-and pp2)))
            ((unless (pp-term-p pp))
             (mv ''0 nil)))
         (mv `(rp 'bitp (sum-list ,(create-list-instance (pp-flatten pp nil)))) t)))
      (& (mv ''0 nil)))))



(define create-s-instance ((pp rp-termp)
                           (c rp-termp))
  :inline t
  :returns (res rp-termp
                :hyp (and (rp-termp pp)
                          (rp-termp c)))
  (b* (((mv reduced reducedp)
        (s-pattern1-reduce pp c))
       ((when reducedp)
        reduced)
       ;; ((mv reduced reducedp)
       ;;  (s-pattern2-reduce pp c))
       ;; ((when reducedp)
       ;;  reduced)
       )
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
          (t
           `(rp 'bitp (s ',(calculate-s-hash pp c) ,pp ,c))))))

(define swap-c-lsts (c1-lst c2-lst enabled)
  :inline t
  :returns (mv (res1 rp-term-listp
                     :hyp (and (rp-term-listp c1-lst)
                               (rp-term-listp c2-lst)))
               (res2 rp-term-listp
                     :hyp (and (rp-term-listp c1-lst)
                               (rp-term-listp c2-lst))))
  (b* (((unless enabled)
        (mv c1-lst c2-lst))
       (first-id  (case-match c1-lst
                    ((('c ('quote hash) . &) . &) hash)
                    (& 0)))
       (second-id (case-match c2-lst
                    ((('c ('quote hash) . &) . &) hash)
                    (& 0)))
       (len2 (len c2-lst))
       (len1 (len c1-lst))
       (swap (if (= len1 len2)
                 (> (nfix first-id)
                    (nfix second-id))
               (> len1 len2))))
    (if swap
        (mv c2-lst c1-lst)
      (mv c1-lst c2-lst))))

(progn
  (define light-s-of-s-fix-lst ((s-lst rp-term-listp)
                                (c-lst rp-term-listp))
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
                 (mv (cons cur-s pp-lst)
                     c-lst))))))

  (define light-s-of-s-fix ((s rp-termp)
                            (pp rp-termp)
                            (c-lst rp-term-listp))
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

  (define single-c-try-merge-params-aux ((cur-s rp-termp)
                                         c-hash-code
                                         (s-arg rp-termp)
                                         (pp-arg rp-termp)
                                         (c-arg-lst rp-term-listp))
    :inline t
    :returns (success booleanp)
    (b* ((cur-s (ex-from-rp$ cur-s)))
      (case-match cur-s
        (('s ('quote s-hash-code) cur-pp-arg cur-c-arg)
         (and (equal c-hash-code s-hash-code)
              (b* (((mv pp-arg c-arg-lst)
                    (light-s-of-s-fix s-arg pp-arg c-arg-lst)))
                (and (equal c-arg-lst (list-to-lst cur-c-arg))
                     (equal pp-arg cur-pp-arg)))))
        (&
         (hard-error 'single-c-try-merge-params-aux
                     "Bad form for current s:~p0~%"
                     (list (cons #\0 cur-s)))))))

  (define single-c-try-merge-params ((s-lst rp-term-listp)
                                     c-hash-code
                                     (s-arg rp-termp)
                                     (pp-arg rp-termp)
                                     (c-arg-lst rp-term-listp))
    :returns (mv (updated-s-lst rp-term-listp :hyp (and (rp-term-listp s-lst)))
                 (success booleanp))
    :measure (acl2-count s-lst)

    (b* (((when (atom s-lst))
          (mv s-lst nil))
         ((when (single-c-try-merge-params-aux (car s-lst) c-hash-code
                                               s-arg pp-arg c-arg-lst))
          (mv (cdr s-lst) t))
         ((mv rest-s-lst success)
          (single-c-try-merge-params (cdr s-lst) c-hash-code s-arg pp-arg
                                     c-arg-lst))
         ((when success)
          (mv (cons (car s-lst) rest-s-lst) t)))
      (mv s-lst nil))))

(acl2::defines
 count-c
 :flag-defthm-macro defthm-count-c
 :flag-local nil
 :hints (("Goal"
          :in-theory (e/d (measure-lemmas
                           single-c-p
                           single-s-p)
                          ())))
 (define count-c (term)
   :measure (cons-count term)

   (b* ((term (ex-from-rp term)))
     (cond
      ((single-c-p term)
       (let ((arg-c (car (cddddr term))))
         (case-match arg-c
           (('list . c-lst) (1+ (count-c-lst c-lst)))
           (& 1))))
      ((single-s-p term)
       (let ((arg-c (car (cdddr term))))
         (case-match arg-c
           (('list . c-lst) (count-c-lst c-lst))
           (& 0))))
      ((or (atom term) (quotep term)) 0)
      (t (count-c-lst (cdr term))))))
 (define count-c-lst (lst)
   :measure (cons-count lst)
   (if (atom lst)
       0
     (+ (count-c-lst (cdr lst))
        (count-c (car lst))))))

(local
 (encapsulate
   nil
   (defthm c-sum-merge-m-lemma1
     (EQUAL (+ (COUNT-C-LST (MV-NTH 0 (swap-c-lsts C1-LST C2-LST cond)))
               (COUNT-C-LST (MV-NTH 1 (swap-c-lsts C1-LST C2-LST cond))))
            (+ (COUNT-C-LST C1-LST)
               (COUNT-C-LST C2-LST)))
     :hints (("Goal"
              :in-theory (e/d (swap-c-lsts) ()))))

   (defthm c-sum-merge-m-lemma2
     (implies (and (MV-NTH 4 (GET-C-ARGS SINGLE-C1))
                   (MV-NTH 4 (GET-C-ARGS SINGLE-C2))
                   (EQUAL (CAR (MV-NTH 1 (GET-C-ARGS SINGLE-C2)))
                          'LIST))
              (< (+ (COUNT-C-LST (MV-NTH 3 (GET-C-ARGS SINGLE-C1)))
                    (COUNT-C-LST (MV-NTH 3 (GET-C-ARGS SINGLE-C2))))
                 (+ (COUNT-C SINGLE-C1)
                    (COUNT-C SINGLE-C2))))
     :hints (("Goal"
              :do-not-induct t
              :expand ((COUNT-C SINGLE-C1)
                       (COUNT-C SINGLE-C2))
              :in-theory (e/d (GET-C-ARGS
                               SINGLE-C-P
                               SINGLE-s-P)
                              ()))))

   (defthm c-sum-merge-m-lemma3
     (IMPLIES (AND (CONSP C2-LST))
              (and (<= (COUNT-C-LST (CDR C2-LST))
                       (COUNT-C-LST C2-LST))
                   (>= (COUNT-C-LST C2-LST)
                       (COUNT-C-LST (CDR C2-LST)))))
     :hints (("Goal"
              :expand (COUNT-C-LST C2-LST)
              :in-theory (e/d () ()))))

   (defthm c-sum-merge-m-lemma4
     (IMPLIES (AND (CONSP C1-LST))
              (<= (+ a (COUNT-C (CAR C1-LST)))
                  (+ (COUNT-C-LST C1-LST) a)))
     :hints (("Goal"
              :expand (COUNT-C-LST C1-LST)
              :in-theory (e/d () ()))))

   (defthm c-sum-merge-m-lemma5
     (IMPLIES (AND (CONSP C1-LST)
                   (<= (+ (COUNT-C-LST C1-LST)
                          (COUNT-C-LST C2-LST))
                       (+ (COUNT-C-LST C2-LST)
                          (COUNT-C (CAR C1-LST)))))
              (EQUAL (+ (COUNT-C-LST C2-LST)
                        (COUNT-C (CAR C1-LST)))
                     (+ (COUNT-C-LST C1-LST)
                        (COUNT-C-LST C2-LST))))
     :hints (("Goal"
              :use ((:instance c-sum-merge-m-lemma4
                               (a (COUNT-C-LST C2-LST))))
              :in-theory (e/d () (c-sum-merge-m-lemma4)))))

   (defthm c-sum-merge-m-lemma6
     (implies (consp c2-lst)
              (>= (COUNT-C-LST C2-LST)
                  (COUNT-C (CAR C2-LST))))
     :hints (("Goal"
              :expand (COUNT-C-LST C2-LST)
              :in-theory (e/d () ()))))

   (defthm c-sum-merge-m-lemma7
     (implies (and (consp c2-lst)
                   (<= (count-c-lst c2-lst)
                       (count-c (car c2-lst))))
              (equal (+ (count-c single-c1)
                        (count-c (car c2-lst)))
                     (+ (count-c single-c1)
                        (count-c-lst c2-lst))))
     :hints (("Goal"
              :use ((:instance c-sum-merge-m-lemma6))
              :in-theory (e/d () (c-sum-merge-m-lemma6)))))

   (defthm c-sum-merge-m-lemma8
     (IMPLIES (AND (CONSP C2-LST)
                   (<= (COUNT-C-LST C2-LST)
                       (COUNT-C-LST (CDR C2-LST))))
              (equal (COUNT-C-LST C2-LST)
                     (COUNT-C-LST (CDR C2-LST))))
     :hints (("Goal"
              :expand (COUNT-C-LST C2-LST)
              :in-theory (e/d () ()))))

   ))

(define negated-termp (term)
  :inline t
  (case-match term (('-- &) t)))

(in-theory (enable PP-LST-TO-PP))

(acl2::defines
 c-sum-merge
 :flag-defthm-macro defthm-c-sum-merge
 :flag-local nil
 :verify-guards nil
 :hints (("Goal"
          :in-theory (e/d (measure-lemmas) ())))

 (define single-c-try-merge  ((single-c1 rp-termp)
                              (single-c2 rp-termp))
   ;; returns (mv coughed-s coughed-pp-lst produced-c-lst merge-success)
   ;; if merge-success is t
   ;; otherwise (mv nil nil 0 merge-success)
   :measure (acl2::nat-list-measure
             (list
              (+ (count-c single-c1) (count-c single-c2))
              0 0))
   :returns (mv (coughed-s rp-termp :hyp (and (rp-termp single-c1)
                                              (rp-termp single-c2)))
                (coughed-pp-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                        (rp-termp single-c2)) )
                (produced-c-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                        (rp-termp single-c2)))
                (merge-success booleanp))
   (b* (;; don't try to merge negated elements. They will be coughed off and
        ;; will be tried later.
        ((when (or (negated-termp single-c1)
                   (negated-termp single-c2)))
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
         (mv ''nil nil nil nil))
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
        (new-s-arg-lst (s-sum-merge-aux (list-to-lst s-arg1)
                                        (s-sum-merge-aux (list-to-lst arg-coughed-s)
                                                         updated-s-arg2-lst)))
        (new-s-arg (create-list-instance new-s-arg-lst))
        ((mv coughed-s new-s-arg)
         (c-fix-s-args new-s-arg))

        ((mv coughed-pp-lst new-pp-lst)
         (if (clean-pp-args-cond new-s-arg arg-merged-c-lst)
             (c-fix-arg-aux pp-lst t)
           (mv nil pp-lst)))

        ;; To-be-coughed c-lst from the args is the coughed-c-lst of the
        ;; new c instance.
        (merged-single-c (create-c-instance new-s-arg
                                            (pp-lst-to-pp new-pp-lst)
                                            (create-list-instance
                                             arg-merged-c-lst)))

        #|((mv coughed-pp-lst merged-single-c)
         (c-pattern2-reduce coughed-pp-lst merged-single-c))||#
        
        (produced-c-lst (cons merged-single-c arg-to-be-coughed-c-lst)))
     (mv coughed-s coughed-pp-lst produced-c-lst t)))

 (define c-sum-merge-lst-aux ((single-c1 rp-termp)
                              (c2-lst rp-term-listp))
   ;;:returns (mv coughed-s coughed-pp-lst produced-c-lst rest-c2-lst merge-success)

   ;; try and merge single-c1 with something in c2-lst
   ;; after the merge, coughed-s and coughed-pp-lst might have results from the
   ;; new c.
   ;; the result "produced-c-lst" may be mergable with something(s) in
   ;; rest-c2-lst
   ;; when merge is succesful c2-lst will have one less element.
   :measure (acl2::nat-list-measure
             (list
              (+ (count-c single-c1) (count-c-lst c2-lst))
              1
              (acl2-count c2-lst)))
   :returns (mv (coughed-s rp-termp :hyp (and (rp-termp single-c1)
                                              (rp-term-listp c2-lst)))
                (coughed-pp-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                        (rp-term-listp c2-lst)))
                (produced-c-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                        (rp-term-listp c2-lst)))
                (updated-c2-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                        (rp-term-listp c2-lst)))
                (merge-success booleanp))
   (if (atom c2-lst)
       (mv ''nil nil nil c2-lst nil)
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

 (define c-sum-merge-lst ((single-c1 rp-termp)
                          (c2-lst rp-term-listp))

   :measure (acl2::nat-list-measure
             (list
              (+ (count-c single-c1) (count-c-lst c2-lst))
              2 0))
   :returns (mv (coughed-s rp-termp :hyp (and (rp-termp single-c1)
                                              (rp-term-listp c2-lst)))
                (coughed-pp-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                        (rp-term-listp c2-lst)))
                (new-c2-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                    (rp-term-listp c2-lst))))

   ;; Same as c-sum-merge-lst-aux but produced-c-lst is not mergable with anything
   ;; in rest-c2-lst because it was tried to be merged as long as it goes.

   (b* (((when (equal single-c1 ''0)) ;; if it is 0 then convert it to a pp
         (mv ''nil nil c2-lst))
        ((when (quotep single-c1)) ;; if it is quoted then convert it to a pp
         (mv ''nil (list single-c1) c2-lst))

        ((mv coughed-s coughed-pp-lst produced-c-lst rest-c2-lst merge-success)
         (c-sum-merge-lst-aux single-c1 c2-lst)))
     (if merge-success
         (b* (((unless (mbt (< (+ (count-c-lst produced-c-lst) (count-c-lst rest-c2-lst))
                               (+ (count-c single-c1) (count-c-lst c2-lst)))))
               (mv coughed-s coughed-pp-lst  (s-sum-merge-aux produced-c-lst rest-c2-lst)))
              ((mv coughed-s2 coughed-pp-lst2 new-c2-lst)
               (c-sum-merge-lst-lst produced-c-lst rest-c2-lst))
              (coughed-s (s-sum-merge coughed-s coughed-s2))
              (coughed-pp-lst (pp-sum-merge-aux  coughed-pp-lst coughed-pp-lst2)))
           (mv coughed-s coughed-pp-lst  new-c2-lst))
       (mv ''nil nil (s-sum-merge-aux (list single-c1) c2-lst)))))

 (define c-sum-merge-lst-lst ((c1-lst rp-term-listp)
                              (c2-lst rp-term-listp))
   ;;:returns (mv coughed-s coughed-pp-lst-lst c2-lst)

   :measure (acl2::nat-list-measure
             (list
              (+ (count-c-lst c1-lst) (count-c-lst c2-lst))
              3
              (acl2-count c1-lst)))
   :returns (mv (coughed-s rp-termp :hyp (and (rp-term-listp c1-lst)
                                              (rp-term-listp c2-lst)))
                (coughed-pp-lst rp-term-listp :hyp (and (rp-term-listp c1-lst)
                                                        (rp-term-listp
                                                         c2-lst)))
                (updated-c2-lst rp-term-listp :hyp (and (rp-term-listp c1-lst)
                                                        (rp-term-listp c2-lst))))
   (b* (((when (atom c1-lst))
         (mv ''nil nil c2-lst))

        ((mv coughed-s coughed-pp-lst1 updated-c2-lst)
         (c-sum-merge-lst (car c1-lst) c2-lst))

        ((unless (mbt (<= (+ (count-c-lst (cdr c1-lst)) (count-c-lst updated-c2-lst))
                          (+ (count-c-lst c1-lst) (count-c-lst c2-lst)))))
         (mv coughed-s coughed-pp-lst1 (s-sum-merge-aux (cdr c1-lst) updated-c2-lst)))

        ((mv coughed-s2 coughed-pp-lst2  updated2-c2-lst)
         (c-sum-merge-lst-lst (cdr c1-lst) updated-c2-lst))

        (coughed-s-merged (s-sum-merge coughed-s coughed-s2))
        (coughed-pp-lst (pp-sum-merge-aux coughed-pp-lst1
                                          coughed-pp-lst2)))
     (mv coughed-s-merged
         coughed-pp-lst
         updated2-c2-lst)))

 (define c-sum-merge ((c1-lst rp-term-listp)
                      (c2-lst rp-term-listp)
                      &key
                      (auto-swap 't)
                      (clean-c1-lst 'nil))
   :returns (mv (coughed-s rp-termp
                           :hyp (and (rp-term-listp c1-lst)
                                     (rp-term-listp c2-lst)))
                (coughed-pp-lst rp-term-listp
                                :hyp (and (rp-term-listp c1-lst)
                                          (rp-term-listp c2-lst)))
                (c-merged-lst rp-term-listp
                              :hyp (and (rp-term-listp c1-lst)
                                        (rp-term-listp c2-lst)))
                (to-be-coughed-c-lst rp-term-listp
                                     :hyp (and (rp-term-listp c1-lst)
                                               (rp-term-listp c2-lst))))
   :measure (acl2::nat-list-measure
             (list
              (+ (count-c-lst c1-lst) (count-c-lst c2-lst))
              5 0))
   (b* (((mv c1-lst c2-lst)
         (swap-c-lsts c1-lst c2-lst auto-swap)))
     (c-sum-merge-aux c1-lst c2-lst :clean-c1-lst clean-c1-lst)))

 (define c-sum-merge-aux ((c1-lst rp-term-listp)
                          (c2-lst rp-term-listp)
                          &key
                          (clean-c1-lst 'nil))
   ;; returns (mv coughed-s coughed-pp-lst res-c)
   :measure (acl2::nat-list-measure
             (list
              (+ (count-c-lst c1-lst) (count-c-lst c2-lst))
              4 0))
   :returns (mv (coughed-s rp-termp
                           :hyp (and (rp-term-listp c1-lst)
                                     (rp-term-listp c2-lst)))
                (coughed-pp-lst rp-term-listp
                                :hyp (and (rp-term-listp c1-lst)
                                          (rp-term-listp c2-lst)))
                (c-merged-lst rp-term-listp
                              :hyp (and (rp-term-listp c1-lst)
                                        (rp-term-listp c2-lst)))
                (to-be-coughed-c-lst rp-term-listp
                                     :hyp (and (rp-term-listp c1-lst)
                                               (rp-term-listp c2-lst))))
   (cond ((equal c1-lst nil)
          (mv ''nil nil c2-lst nil))
         ((and (equal c2-lst nil)
               (not clean-c1-lst))
          (mv ''nil nil c1-lst nil))
         (t (b* (((mv coughed-s coughed-pp-lst merged-c-lst)
                  (c-sum-merge-lst-lst c1-lst c2-lst))

                 ((mv to-be-coughed-c-lst merged-c-lst)
                  (cough-duplicates merged-c-lst)))
              (mv coughed-s coughed-pp-lst merged-c-lst to-be-coughed-c-lst))))))

(local
 (defthm rp-termp-lemma1
   (implies (and (consp x)
                 (rp-term-listp x))
            (rp-termp (car x)))))

(define s-of-s-fix-lst ((s-lst rp-term-listp)
                        (c-lst rp-term-listp)
                        &key
                        (limit '(expt 2 30)))
  :returns (mv (pp-res-lst)
               (c-res-lst))
  :guard (natp limit)
  :measure (nfix limit)
  :verify-guards nil
  (b* (((when (zp limit))
        (progn$ (hard-error 's-of-s-fix-aux "Limit reached!.." nil)
                (mv s-lst c-lst)))
       ((when (atom s-lst)) (mv nil c-lst))
       ((mv pp-lst new-c-lst) (s-of-s-fix-lst (cdr s-lst) c-lst :limit (1- limit)))
       (cur-s (ex-from-rp/-- (car s-lst))))
    (case-match cur-s
      (('s & cur-pp cur-c)
       (b* ((cur-c-lst (list-to-lst cur-c))
            ((mv coughed-s coughed-pp-lst c-lst &)
             (c-sum-merge cur-c-lst new-c-lst))
            (pp-lst (pp-sum-merge-aux coughed-pp-lst pp-lst))
            (pp-lst (pp-sum-merge-aux (list-to-lst cur-pp) pp-lst))
            (coughed-s-lst (list-to-lst coughed-s))
            ((unless coughed-s-lst)
             (mv pp-lst c-lst))
            ((mv rest-pp-lst c-lst)
             (s-of-s-fix-lst coughed-s-lst c-lst :limit (1- limit))))
         (mv (pp-sum-merge-aux rest-pp-lst pp-lst) c-lst)))
      (''nil
       (mv pp-lst new-c-lst))
      (&
       (progn$ (cw "Unexpected s term ~p0 ~%" cur-s)
               (hard-error 's-of-s-fix-aux "Read above.." nil)
               (mv s-lst
                   ;;(list-to-lst `(binary-append ,cur-s (list . ,pp-lst)))

                   c-lst)))))
  ///
  (acl2::defret
   rp-term-listp-of-<fn>
   :hyp (and (rp-term-listp s-lst)
             (rp-term-listp c-lst))
   (and (rp-term-listp c-res-lst)
        (rp-term-listp pp-res-lst))))

(define s-of-s-fix ((s rp-termp)
                    (pp rp-termp)
                    (c-lst rp-term-listp))
  :verify-guards nil
  :returns (mv (pp-res rp-termp :hyp (and (rp-termp s)
                                          (rp-termp pp)
                                          (rp-term-listp c-lst)))
               (c-res-lst rp-term-listp :hyp (and (rp-termp s)
                                                  (rp-termp pp)
                                                  (rp-term-listp c-lst))))
  (b* ((s-lst (list-to-lst s))
       ((when (equal s-lst nil))  (mv pp c-lst))
       ((mv pp-lst c-lst)
        (s-of-s-fix-lst s-lst c-lst))
       ;; MAYBE clear c-lst here!
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

(define good-4vec-term-p ((term rp-termp))
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

(define 4vec->pp-term (term)
  :returns (pp-term)
  :measure (cons-count term)
  :guard (and (rp-termp term)
              (good-4vec-term-p term))
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :guard-hints (("Goal"
                 :in-theory (e/d (good-4vec-term-p) ())))
  (b* ((orig term)
       (term (ex-from-rp$ term)))
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
                                falist-consistent)))))

  (acl2::defret
   pp-term-p-of--<fn>
   :hyp (good-4vec-term-p term)
   (pp-term-p pp-term)
   :hints (("Goal"
            :induct (4vec->pp-term term)
            :do-not-induct t
            :expand ((:free (x y) (pp-term-p (cons x y)))
                     (:free (x y) (is-rp (cons x y))))
            :in-theory (e/d (good-4vec-term-p
                             ex-from-rp)
                            (rp-termp pp-term-p))))))

(local
 (defthm rp-term-listp-of-append
   (implies (and (rp-term-listp x)
                 (rp-term-listp y))
            (rp-term-listp (append x y)))
   :hints (("Goal"
            :in-theory (e/d (rp-term-listp) ())))))

(local
 (defthm rp-term-listp-of-repeat
   (implies (rp-termp x)
            (rp-term-listp (repeat num x)))
   :hints (("Goal"
            :induct (REPEAT NUM X)
            :in-theory (e/d (rp-term-listp repeat) ())))))

;;;;;;;;;;;;;;;;;;;

(define extract-new-sum-element ((term rp-termp) acc)
  :returns (acc-res rp-term-listp
                    :hyp (and (rp-termp term)
                              (rp-term-listp acc)))
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((term-orig term)
       (term (ex-from-rp$ term)))
    (cond
     ((single-c-p term)
      (cons term-orig acc))
     ((single-s-p term)
      (cons term-orig acc))
     ((single-c-res-p term)
      (cons term-orig acc))
     ((sum-list-p term)
      (cons term-orig acc))
     ((and-list-p term)
      (cons term-orig acc))
     ((binary-sum-p term)
      (b* ((acc (extract-new-sum-element (cadr term) acc))
           (acc (extract-new-sum-element (caddr term) acc)))
        acc))
     ((quote-p term)
      (b* ((x (ifix (cadr term)))) ;; ifix here is ok because sum-list calls sum which
        ;; calls ifix for its arguments..
        (cond ((natp x) (append (repeat x ''1) acc))
              (t (append (repeat (- x) ''-1) acc)))))
     ((good-4vec-term-p term)
      (cons term-orig acc))
     (t
      (progn$
       (hard-error 'extract-new-sum-element
                   "Unexpexted term: ~p0 ~%"
                   (list (cons #\0 term-orig)))
       (cons term-orig acc))))))



(define extract-new-sum-consed ((term rp-termp))
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :prepwork
  ((local
    (in-theory (enable ex-from-rp))))
  :returns (acc-res rp-term-listp
                    :hyp (and (rp-termp term)))
  (b* ((term-orig term)
       (term (ex-from-rp$ term)))
    (case-match term
      (('cons x rest)
       (b* ((acc (extract-new-sum-consed rest)))
         (extract-new-sum-element x acc)))
      (''nil
       nil)
      (('quote x)
       (if (consp x)
           (extract-new-sum-element (list 'quote (sum-list x)) nil)
         (progn$
          (hard-error 'extract-new-sum-consed
                      "Unexpected term. Should be a true-listp formm: ~p0~%"
                      (list (cons #\0 term-orig)))
          (list-to-lst term-orig)
          )))
      (&
       (progn$
        (hard-error 'extract-new-sum-consed
                    "Unexpected term. Should be a true-listp formm: ~p0~%"
                    (list (cons #\0 term-orig)))
        (list-to-lst term-orig)
;(list `(sum-list ,term-orig))
        ))
      )))

(define new-sum-merge-aux-dissect-term ((term rp-termp))
  :inline t
  :returns (mv (term-orig rp-termp :hyp (rp-termp term))
               (abs-term-w/-sc rp-termp :hyp (rp-termp term))
               (abs-term rp-termp :hyp (rp-termp term))
               (negated booleanp))
  (b* ((term-orig term)
       ((mv abs-term-w/-sc negated)
        (case-match term-orig (('-- e) (mv e t)) (& (mv term-orig nil))))
       (abs-term (ex-from-rp$ abs-term-w/-sc)))
    (mv term-orig abs-term-w/-sc abs-term negated)))

(define new-sum-merge-aux-add-negated-coughed ((to-be-coughed-c-lst rp-term-listp)
                                               (abs-term-w/-sc rp-termp)
                                               negated)
  :inline t
  :returns (res-lst rp-term-listp :hyp (and (rp-term-listp to-be-coughed-c-lst)
                                            (rp-termp abs-term-w/-sc)))
  (if negated
      (s-sum-merge-aux to-be-coughed-c-lst
                       (list `(-- ,abs-term-w/-sc)))
    to-be-coughed-c-lst))

;;(include-book "pp-flatten-wrapper")

(define new-sum-merge-aux ((sum-lst rp-term-listp))
  :verify-guards nil
  ;;:returns (mv s pp-lst c-lst to-be-coughed-c-lst)

  :returns (mv (s) (pp-lst) (c-lst) (to-be-coughed-c-lst))
  (b* (((when (atom sum-lst))
        (mv ''nil nil nil nil))
       ((mv s pp-lst c-lst to-be-coughed-c-lst)
        (new-sum-merge-aux (cdr sum-lst)))
       ((mv term-orig abs-term-w/-sc abs-term negated)
        (new-sum-merge-aux-dissect-term (car sum-lst))))
    (cond
     ((single-c-p abs-term)
      (b* (((mv coughed-s coughed-pp-lst c-lst to-be-coughed-c-lst2)
            (c-sum-merge (list abs-term-w/-sc) c-lst :auto-swap nil ))
           (s (s-sum-merge s coughed-s))
           (to-be-coughed-c-lst (s-sum-merge-aux to-be-coughed-c-lst
                                                 to-be-coughed-c-lst2))
           (to-be-coughed-c-lst
            (new-sum-merge-aux-add-negated-coughed to-be-coughed-c-lst
                                                   abs-term-w/-sc
                                                   negated))
           (pp-lst (pp-sum-merge-aux coughed-pp-lst pp-lst)))
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     ((single-s-p abs-term)
      (b* ((s (s-sum-merge s (create-list-instance
                              (list term-orig)))))
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     ((single-c-res-p abs-term)
      (b* (((mv s-arg pp-arg c-arg)
            (case-match abs-term
              (('c-res s-arg pp-arg c-arg) (mv s-arg pp-arg c-arg))
              (& (mv ''nil ''nil ''nil))))
           ((mv s-arg pp-arg c-arg-lst)
            (mv (negate-list-instance s-arg negated)
                (negate-list-instance pp-arg negated)
                (negate-lst (list-to-lst c-arg) negated)))
           ((mv to-be-coughed-c-lst2 c-arg-lst)
            (cough-lst c-arg-lst))

           ((mv coughed-s coughed-pp-lst c-lst to-be-coughed-c-lst3)
            (c-sum-merge c-arg-lst c-lst :auto-swap nil :clean-c1-lst t ))

           (s (s-sum-merge s s-arg))
           (s (s-sum-merge s coughed-s))
           (pp-lst (pp-sum-merge-aux (list-to-lst pp-arg) pp-lst))
           (pp-lst (pp-sum-merge-aux coughed-pp-lst pp-lst))
           (to-be-coughed-c-lst (s-sum-merge-aux to-be-coughed-c-lst
                                                 to-be-coughed-c-lst2))
           (to-be-coughed-c-lst (s-sum-merge-aux to-be-coughed-c-lst
                                                 to-be-coughed-c-lst3))
           )
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     ((sum-list-p abs-term)
      (b* ((arg-pp (cadr abs-term))
           (arg-pp (negate-list-instance arg-pp negated))
           (pp-lst (pp-sum-merge-aux (list-to-lst arg-pp)  pp-lst)))
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     ((and-list-p abs-term)
      (b* ((pp-lst (pp-sum-merge-aux (list term-orig)  pp-lst)))
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     ((quote-p abs-term)
      (b* ((pp-lst (pp-sum-merge-aux (list term-orig)  pp-lst)))
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     ((good-4vec-term-p abs-term)
      (b* ((abs-term (4vec->pp-term abs-term))
           (pp-lst2 (pp-flatten abs-term negated))
           (pp-lst (pp-sum-merge-aux pp-lst pp-lst2)))
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     (t
      (progn$ (hard-error 'new-sum-merge-aux
                          "Unexpected term ~p0 ~%"
                          (list (cons #\0 abs-term-w/-sc)))
              (mv `(cons ,term-orig ,s)
                  pp-lst
                  c-lst
                  to-be-coughed-c-lst)))))
  ///
  (acl2::defret
   return-vals--of--<fn>
   :hyp (rp-term-listp sum-lst)
   (and (rp-termp s)
        (rp-term-listp pp-lst)
        (rp-term-listp c-lst)
        (rp-term-listp to-be-coughed-c-lst))
   :hints (("Goal"
            :do-not-induct t
            :expand ((NEW-SUM-MERGE-AUX SUM-LST))
            :induct (new-sum-merge-aux sum-lst)
            :in-theory (e/d ((:REWRITE ACL2::O-P-O-INFP-CAR)
                             (:induction new-sum-merge-aux))
                            ((:definition new-sum-merge-aux)
                             (:e tau-system)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE DEFAULT-CDR)
                             (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)))))))

(define new-sum-merge ((term rp-termp))
  :verify-guards nil
  :returns (mv (s) (pp-lst) (c-lst) (to-be-coughed-c-lst))
  (b* ((sum-lst (extract-new-sum-consed term))
       ((mv s pp-lst c-lst to-be-coughed-c-lst)
        (new-sum-merge-aux sum-lst)))
    (mv s pp-lst c-lst to-be-coughed-c-lst))
  ///
  (acl2::defret
   return-vals--of--<fn>
   :hyp (rp-termp term)
   (and (rp-termp s)
        (rp-term-listp pp-lst)
        (rp-term-listp c-lst)
        (rp-term-listp to-be-coughed-c-lst))))

;; (progn
(define well-formed-new-sum ((term rp-termp))
  :returns (res booleanp)
  (or nil
      (case-match term
        (('cons x rest)
         (b* ((x (ex-from-rp$ x))
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

(progn
  (define light-pp-term-p ((term rp-termp))
    :inline t
    (or
     (pp-has-bitp-rp term)
     (b* ((term (ex-from-rp$ term)))
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

  (define light-pp-term-list-p ((lst rp-term-listp))
    (if (atom lst)
        (equal lst nil)
      (and (light-pp-term-p (car lst))
           (light-pp-term-list-p (cdr lst)))))

  (define quarternaryp-sum-aux ((term rp-termp))
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
            (x (ex-from-rp$ x)))
         (cond ((light-pp-term-p x)
                (mv (1+ rest-sum) t))
               ((single-s-p x)
                (mv (1+ rest-sum) t))
               ((is-rp-bitp x-orig)
                (mv (1+ rest-sum) t))
               ((and-list-p x)
                (mv (1+ rest-sum) t))
               ((equal x ''0)
                (mv rest-sum t))
               ((equal x ''1)
                (mv (1+ rest-sum) t))
               #|((case-match x (('sum-list ''nil) t))
               (mv rest-sum t))||#
               ((sum-list-p x)
                (if (light-pp-term-list-p (list-to-lst (cadr x)))
                    (mv (+ rest-sum (len (list-to-lst (cadr x)))) t)
                  (mv 0 nil)))
               (t
                (mv 0 nil)))))
      (''nil
       (mv 0 t))
      (('quote x)
       (b* ((res (sum-list x)))
         (if (natp res)
             (mv res t)
           (mv 0 nil))))
      (& (mv 0 nil)))
    ///
    (verify-guards quarternaryp-sum-aux
      :hints (("Goal"
               :in-theory (e/d () ())))))

  (define quarternaryp-sum ((sum rp-termp))
    :returns (res booleanp)
    (b* (((mv res valid)
          (quarternaryp-sum-aux sum)))
      (and valid
           (quarternaryp res)))))

(define c-spec-meta-aux ((arg-s rp-termp)
                         (arg-pp-lst rp-term-listp)
                         (arg-c-lst rp-term-listp)
                         (to-be-coughed-c-lst rp-term-listp)
                         (quarternaryp booleanp))
  :returns (res rp-termp
                :hyp (and (rp-termp arg-s)
                          (rp-term-listp arg-pp-lst)
                          (rp-term-listp to-be-coughed-c-lst)
                          (rp-term-listp arg-c-lst)))
  :verify-guards nil
  :prepwork ((local
              (in-theory (disable natp))))
  (b* (((mv s-coughed arg-s) (c-fix-s-args arg-s))
       ((mv pp-coughed arg-pp)
        (if (clean-pp-args-cond arg-s arg-c-lst)
            (c-fix-pp-args (create-list-instance arg-pp-lst))
          (mv ''nil (create-list-instance arg-pp-lst))))

       (single-c-term (create-c-instance arg-s
                                         arg-pp
                                         (create-list-instance arg-c-lst)))

       ;; ((mv c-pattern2-pp-lst single-c-term)
       ;;  (c-pattern2-reduce nil single-c-term))
       ;; (pp-coughed (pp-sum-merge pp-coughed (create-list-instance c-pattern2-pp-lst)))
       
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
                    (res `(c-res ,s-coughed ,pp-coughed ,(create-list-instance c-merged-lst))))
                 (if quarternaryp
                     `(rp 'bitp ,res)
                   res)))))

       ((mv s-coughed2 coughed-pp-lst c-merged-lst)
        (c-sum-merge-lst single-c-term to-be-coughed-c-lst ))

       (s-coughed (s-sum-merge s-coughed s-coughed2))

       (coughed-pp-lst (pp-sum-merge-aux (list-to-lst pp-coughed) coughed-pp-lst))
       (pp-coughed (pp-lst-to-pp coughed-pp-lst))

       (res `(c-res ,s-coughed ,pp-coughed (list . ,c-merged-lst)))
       (res (if quarternaryp `(rp 'bitp ,res) res)))
    res))

(define s-spec-meta-aux ((s rp-termp)
                         (pp-lst rp-term-listp)
                         (c-lst rp-term-listp))
  :verify-guards nil
  :returns (res rp-termp
                :hyp (and (rp-termp s)
                          (rp-term-listp pp-lst)
                          (rp-term-listp c-lst)))
  (b* ((pp (pp-lst-to-pp pp-lst))
       ((mv pp c-lst) (s-of-s-fix s pp c-lst))

       (pp-orig pp)
       
       (pp (if (clean-pp-args-cond ''nil c-lst) (s-fix-args pp) pp))

       (- (and (clean-pp-args-cond ''nil c-lst)
               (not (equal (s-fix-args pp) pp))
               (cw "pp-orig : ~p0 ~% " pp-orig)))

       (c (create-list-instance c-lst))
       (res (create-s-instance pp c)))
    res))

(define s-c-spec-meta ((term rp-termp))
  :returns (mv (res rp-termp
                    :hyp (rp-termp term))
               (dont-rw dont-rw-syntaxp))
  :prepwork ((local
              (defthm lemma1
                (IS-RP (LIST 'RP ''BITP x))
                :hints (("Goal"
                         :in-theory (e/d (is-rp) ()))))))
  :verify-guards nil
  (b* ((result
        (case-match term
          (('s-c-spec sum)
           (b* (((mv s pp-lst c-lst to-be-coughed-c-lst);;(mv s pp c)
                 (new-sum-merge sum))

                (quarternaryp (quarternaryp-sum sum))

                (s-res (s-spec-meta-aux s pp-lst c-lst))
                (c-res (c-spec-meta-aux s pp-lst c-lst
                                        to-be-coughed-c-lst quarternaryp))
                (res `(cons ,s-res (cons ,c-res 'nil)))
                )
             res))
          (('c-s-spec sum)
           (b* (((mv s pp-lst c-lst to-be-coughed-c-lst);;(mv s pp c)
                 (new-sum-merge sum))
                (quarternaryp (quarternaryp-sum sum))
                (s-res (s-spec-meta-aux s pp-lst c-lst))
                (c-res (c-spec-meta-aux s pp-lst c-lst to-be-coughed-c-lst quarternaryp)))
             `(cons ,c-res (cons ,s-res 'nil))))
          (('s-spec sum)
           (b* (((mv s pp-lst c-lst &);;(mv s pp c)
                 (new-sum-merge sum)))
             (s-spec-meta-aux s pp-lst c-lst)))
          (('c-spec sum)
           (b* (((mv s pp-lst c-lst to-be-coughed-c-lst)
                 (new-sum-merge sum))
                (quarternaryp (quarternaryp-sum sum)))
             (c-spec-meta-aux s pp-lst c-lst to-be-coughed-c-lst quarternaryp)))
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
   (in-theory (disable
               +-is-SUM
               mod2-is-m2
               floor2-if-f2
               c-is-f2
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
      (binary-append
       --
       sum-list
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
       c
       m2
       f2
       times2
       s
       binary-sum
       sv::3vec-fix
       sv::4vec-fix))))
