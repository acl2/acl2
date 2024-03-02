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

(include-book "pp-flatten-meta-fncs")

(include-book "pp-flatten-with-binds-meta")

(include-book "std/util/defines" :dir :system)

(include-book "sum-merge-fncs")

(local
 (fetch-new-theory
  (include-book "ihs/logops-lemmas" :dir :system)
  use-ihs-logops-lemmas
  :disabled t))

(local
 (fetch-new-theory
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))
(local
 (include-book "lemmas"))
(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (in-theory (disable +-is-sum
                     rp-termp
                     ex-from-rp
                     (:definition acl2::apply$-badgep)
                     (:linear acl2::apply$-badgep-properties . 1)
                     (:definition subsetp-equal)
                     (:definition member-equal)
                     (:rewrite
                      acl2::member-equal-newvar-components-1)
                     include-fnc)))
(local
 (set-induction-depth-limit 1))

(defsection hash-codes

  (local
   (use-ihs-logops-lemmas t))

  (define hash-coef ()
    :inline t
    13)

  (local
   (defthm cons-count-of-ex-from-rp/times
     (and (<= (cons-count (ex-from-rp/times x))
              (cons-count x))
          (implies (consp (ex-from-rp/times x))
                   (and (O< (CONS-COUNT (CADR (ex-from-rp/times x)))
                            (CONS-COUNT x)))))
     :hints (("Goal"
              :induct (ex-from-rp/times x)
              :do-not-induct t
              :in-theory (e/d (ex-from-rp/times
                               o<
                               cons-count)
                              ())))))

  (define binary-fnc-hash (term)
    :returns (hash integerp)
    :measure (cons-count term)

    :hints (("Goal"
             :in-theory (e/d (measure-lemmas) ())))
    (b* ((term (ex-from-rp/times term)))
      (cond ((atom term)
             0)
            ((quotep term)
             (if (and (consp (cdr term))
                      (integerp (cadr term)))
                 (cadr term)
               0))
            ((binary-not-p term)
             (+ 5
                (binary-fnc-hash (cadr term))))
            ((or (binary-and-p term)
                 (binary-or-p term)
                 (binary-xor-p term))
             (+ 5
                (binary-fnc-hash (caddr term))
                (binary-fnc-hash (cadr term))))
            ((binary-?-p term)
             (+ 5
                (binary-fnc-hash (cadddr term))
                (binary-fnc-hash (caddr term))
                (binary-fnc-hash (cadr term))))
            ((single-c-p term)
             (ifix (and (quotep (cadr term))
                        (consp (cdr (cadr term)))
                        (consp (unquote (cadr term)))
                        (car (unquote (cadr term))))))
            ((single-s-p term)
             (ifix (and (quotep (cadr term))
                        (consp (cdr (cadr term)))
                        (unquote (cadr term)))))
            ((logbit-p term)
             (ifix (and (quotep (caddr term))
                        (consp (cdr (caddr term)))
                        (unquote (caddr term)))))
            (t 0))))

  (define pp-instance-hash (e)
    :returns (hash integerp)
    :inline t
    (b* ((e (ex-from-rp/times e)))
      (case-match e
        (('and-list ('quote hash) &)
         (ifix hash))
        (('and-times-list ('quote hash) &)
         (ifix hash))
        (('-- ('and-list ('quote hash) &))
         (ifix hash))
        (('-- ('and-times-list ('quote hash) &))
         (ifix hash))
        (''1
         1)
        (&
         (if (binary-fnc-p (ex-from-rp e))
             (binary-fnc-hash e)
           0)
         ))))

  (defwarrant pp-instance-hash$inline)

  (define pp-lst-hash ((pp-lst rp-term-listp)
                       &key
                       ((acc integerp) '0))
    :inline t ;; tail-recursive..
    :returns (hash-code integerp :hyp (integerp acc))
    (if (atom pp-lst)
        acc
      (pp-lst-hash (cdr pp-lst)
                   :acc (+ acc (pp-instance-hash (car pp-lst))))))

  (define calculate-pp-hash ((pp rp-termp))
    :returns (hash-code integerp)
    :inline t
    (case-match pp
      (('list . pp-lst)
       ;;(let ((len (len pp-lst))) (* len len))
       (pp-lst-hash pp-lst)
       )
      (& 0)))

  (defwarrant calculate-pp-hash$inline)

  (local
   (defthm ingerep-of-+/*
     (implies (and (integerp x)
                   (integerp y))
              (and (integerp (+ x y))
                   (integerp (* x y))))))

  (define get-hash-code-of-single-s (s)
    :returns (hash-code integerp)
    :inline t
    (b* ((s (ex-from-rp/times s)))
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

  ;;(defwarrant get-hash-code-of-single-s$inline)
  ;;(defwarrant acl2::logcar$inline)

  (define get-hash-code-of-s-lst ((lst true-listp))
    :returns (mv (hash-code1 integerp)
                 (hash-code2 integerp))
    ;;:inline t ;; or should it be inline?
    (b* (((when (atom lst)) (mv 0 0))
         ((mv r1 r2)
          (get-hash-code-of-s-lst (cdr lst)))
         (h (get-hash-code-of-single-s (car lst))))
      (mv (+ r1 h) (ifix (+ r2 (logcar h))))))

  ;; (defwarrant get-hash-code-of-s-lst$inline)

  (define get-hash-code-of-s ((s rp-termp))
    :returns (mv (hash-code1 integerp)
                 (hash-code2 integerp))
    :inline t
    (case-match s
      (('list . s-lst)
       (get-hash-code-of-s-lst s-lst))
      (& (mv 0 0))))

  ;;(defwarrant get-hash-code-of-s$inline)

  (define get-hash-code-of-single-c (c)
    :returns (hash-code integerp)
    :inline t
    (b* ((c (ex-from-rp/times c)))
      (case-match c
        (('c ('quote hash-code) & & &)
         (if (consp hash-code)
             (ifix (cdr hash-code))
           (ifix hash-code)))
        (''0
         0)
        (& (progn$ (hard-error
                    'get-hash-code-of-single-c
                    "unrecognized c instance:~p0 ~%"
                    (list (cons #\0 c)))
                   0)))))

  ;;(defwarrant get-hash-code-of-single-c$inline)

  (define get-hash-code-of-c-lst ((c-lst true-listp)
                                  ;;&optional
                                  ;;((cnt natp) '0)
                                  )
    :returns (hash-code integerp)
    ;;:inline t
    (if (atom c-lst)
        0 ;
      (+ (ifix (ash (get-hash-code-of-single-c (car c-lst)) -1))
         (get-hash-code-of-c-lst (cdr c-lst)))))

  (define get-hash-code-of-c ((c rp-termp))
    :returns (hash-code integerp)
    :inline t
    (case-match c
      (('list . c-lst)
       (get-hash-code-of-c-lst c-lst))
      (& 0)))

  (define calculate-s-hash ((pp rp-termp)
                            (c rp-termp))
    :guard-hints (("Goal"
                   :in-theory (e/d () (loghead unsigned-byte-p))))
    :returns (hash-code integerp)
    (the (unsigned-byte 59)
         (loghead 59
                  (* (hash-coef)
                     (+ (* 3 (calculate-pp-hash pp))
                        (* 7 (get-hash-code-of-c c)))))))

  (local
   (defthm integerp-of-+and*
     (implies (and (integerp x)
                   (integerp y))
              (and (integerp (+ x y))
                   (integerp (* x y))))))

  (define calculate-c-hash ((s rp-termp)
                            (pp rp-termp)
                            (c rp-termp))
    :returns (hash-code)
    :guard-hints (("Goal"
                   :in-theory (e/d () (ash logapp loghead unsigned-byte-p))))
    (b* ((?hash-code-base (calculate-s-hash pp c))
         ((mv ?s-hash-codes1 ?s-hash-codes2)
          (get-hash-code-of-s s))

         (hash-coef (the (unsigned-byte 8) (hash-coef)))

         (mult0 (the (unsigned-byte 90)
                     (loghead 90
                              (* hash-coef
                                 (logxor (loghead 90 hash-code-base)
                                         (loghead 90 (ash hash-code-base -90)))))))

         ;; expecting below to be zero in cases where c-of-s simplification is
         ;; enabled (which is the default)
         (mult1 (the (unsigned-byte 59)
                     (loghead 59 (* s-hash-codes1 hash-coef))))
         (mult2 (the (unsigned-byte 59)
                     (loghead 59 (* s-hash-codes2 hash-coef)))))
      (cons
       (the (unsigned-byte 59)
            (logapp 8 (len (list-to-lst pp))
                    (logapp 8 (len (list-to-lst c))
                            (loghead 43 (ash (the (unsigned-Byte 90)
                                                  (loghead 90 (+ mult0 mult1))) ;
                                             -47)))))
       (the (unsigned-byte 59) (loghead 59 (+ mult0 mult2)))
       ))))

(local
 (defsection local-measure-lemmas
   (defthm measure-lemma-loose1
     (implies (and
               (consp (ex-from-rp max-term))
               (consp (cdr (ex-from-rp max-term)))
               (not (cddr (ex-from-rp max-term))))
              (o< (cons-count (cadr (ex-from-rp max-term)))
                  (cons-count max-term)))
     :hints (("goal"
              :induct (ex-from-rp max-term)
              :do-not-induct t
              :in-theory (e/d (ex-from-rp
                               measure-lemmas)
                              ((:rewrite measure-lemma1)
                               (:rewrite cons-count-atom)
                               (:rewrite default-cdr)
                               (:rewrite measure-lemma6-5)
                               (:definition ex-from-rp)
                               (:rewrite measure-lemma1-2))))))

   (defthm measure-lemma-loose2
     (implies (and  (consp (ex-from-rp max-term))
                    (consp (cdr (ex-from-rp max-term)))
                    (consp (cddr (ex-from-rp max-term)))
                    (consp (cdddr (ex-from-rp max-term)))
                    (consp (cddddr (ex-from-rp max-term)))
                    (not (cdr (cddddr (ex-from-rp max-term)))))
              (o< (cons-count (cdr (car (cddddr (ex-from-rp max-term)))))
                  (cons-count max-term)))
     :hints (("goal"
              :induct (ex-from-rp max-term)
              :do-not-induct t
              :in-theory (e/d (ex-from-rp
                               measure-lemmas)
                              ((:rewrite default-cdr)
;(:rewrite ex-from-rp-loose-is-rp-termp)
                               (:definition rp-termp)
                               (:rewrite measure-lemma1-2)
                               (:rewrite measure-lemma1))))))

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
                               ;;                             (:REWRITE ACL2::O<=-O-FINP-DEF)
                               )))))

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
                               ;;                             (:REWRITE ACL2::O<=-O-FINP-DEF)

                               )))))

   (defthm local-measure-lemma4
     (implies (and
               (integerp term1)
               (integerp term2)
               (integerp term3)
               (o<= term2 term3)
               (o< term1 term2))
              (o< term1 term3))
     :hints (("Goal"
              :in-theory (e/d (o<) ()))))

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
              :in-theory (e/d (cons-count) ()))))

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
              :in-theory (e/d (cons-count) ()))))

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
                              (local-measure-lemma5 local-measure-lemma4)))))

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
              :in-theory (e/d (measure-lemmas) (local-measure-lemma4 local-measure-lemma6)))))

   (defthm local-measure-lemma10
     (IMPLIES (AND (consp (ex-from-rp TERM)))
              (O< (CONS-COUNT (CDR (ex-from-rp TERM)))
                  (CONS-COUNT TERM)))
     :hints (("Goal"
              :in-theory (e/d (measure-lemmas) ()))))

   (defthm local-measure-lemma11
     (implies (and
               (consp (ex-from-rp term)))
              (o< 1 (cons-count term)))
     :hints (("goal"
              :in-theory (e/d (ex-from-rp cons-count) ()))))))

;; (local
;;  (defthm single-c-p-rp-term-listp-lemma
;;    (implies (and (single-c-p term)
;;                  (rp-termp term)
;;                  (equal (car (car (cddddr term)))
;;                         'list))
;;             (rp-term-listp (cdr (car (cddddr term)))))
;;    :hints (("goal"
;;             :expand ((rp-termp term)
;;                      (rp-term-listp (cddddr term))
;;                      (rp-termp (car (cddddr term)))
;;                      (rp-term-listp (cddr term))
;;                      (rp-term-listp (cdddr term))
;;                      (rp-term-listp (cdr term)))
;;             :in-theory (e/d (rp-term-listp
;;                              single-c-p)
;;                             ())))))

;; (local
;;  (defthm dummy-rp-term-listp-lemma
;;    (implies (and (rp-term-listp lst) (consp lst))
;;             (rp-termp (car lst)))
;;    :hints (("goal"
;;             :in-theory (e/d (rp-termp rp-term-listp) ())))))

(acl2::defines
 get-max-min-val
 :flag-defthm-macro defthm-get-min-max-val
 :flag-local nil
 :prepwork ((local
             (in-theory (e/d (measure-lemmas
                              list-to-lst)
                             (measure-lemma1
                              measure-lemma1-2
                              ;;                              (:rewrite acl2::o-p-o-infp-car)
                              (:rewrite default-car)
                              not-include-rp)))))

 :verify-guards nil
 (define get-max-min-val ((term rp-termp))
   :measure (cons-count term)
   :returns (mv  (max-val integerp)
                 (min-val integerp)
                 (valid booleanp))
   (b* (((when (has-bitp-rp term)) (mv 1 0 t))
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
             (floor (+ s-min-val pp-min-val c-min-val) 2)
             t)))
      ((and-times-list-p term)
       (b* (((mv max-val min-val valid) (get-max-min-val (fourth term)))
            ((when (and*-exec valid
                              (natp min-val)
                              (natp max-val)))
             (mv max-val 0 t)))
         (mv 0 0 nil)))

      ((or* (single-s-p term)
            (binary-fnc-p term)
            (logbit-p term)
            (and-list-p term))
       (mv 1 0 t))
      ((equal term ''1) (mv 1 1 t))
      ((times-p term)
       (b* ((coef (ifix (unquote (cadr term))))
            (n (second (cdr term)))
            ((mv max-val min-val valid)
             (get-max-min-val n)))
         (if (< coef 0)
             (mv (* coef min-val) (* coef max-val) valid)
           (mv (* coef max-val) (* coef min-val) valid))))
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
            :in-theory (e/d (RP-TERM-LISTP) ()))))

 (profile 'get-max-min-val))

(define len-lte (lst size)
  ;; checks if length of lst is less than or equal to size.
  :guard (natp size)
  :returns (res-size)
  (if (atom lst)
      size
    (if (zp size)
        nil
      (len-lte (cdr lst) (1- size))))
  ///
  (defret natp-of-<fn>
    (implies (and (natp size)
                  res-size)
             (natp res-size))))

(acl2::defines maybe-bitp-precheck
               ;; A light-weight check to  see if a given term can satisfy  bitp. It is used
               ;; to cost of calling get-max-min-val inside create-c-instance function.

               :hints (("Goal"
                        :in-theory (e/d (measure-lemmas
                                         )
                                        ())))
               :prepwork
               ((local
                 (defthmd dummy-lemma0
                   (implies (and (natp x)
                                 (O< x (CONS-COUNT (ex-from-rp TERM))))
                            (O< x (CONS-COUNT TERM)))
                   :hints (("Goal"
                            :in-theory (e/d (ex-from-rp cons-count) ())))))

                (local
                 (In-Theory (enable measure-lemmas)))

                (local
                 (defthmd dummy-lemma1
                   (implies (or #|(and (<= x y)
                             (< y z))|#
                             (and (< x y)
                                  (<= y z)))
                            (< x z))))

                (local
                 (defthm 0<-to-<
                   (implies (and (natp x) (natp y))
                            (equal (O< x y)
                                   (< x y)))
                   :hints (("Goal"
                            :expand (O< x y)
                            :in-theory (e/d () ())))))

                (local
                 (defthm dummy-lemma2
                   (IMPLIES (AND (CONSP term)
                                 (EQUAL (CAR term) 'C)
                                 (CONSP (CDR term))
                                 (CONSP (CDDR term))
                                 (CONSP (CDDDR term))
                                 (CONSP (CDDDDR term))
                                 (NOT (CDR (CDDDDR term))))
                            (O< (CONS-COUNT (LIST-TO-LST (CAR (CDDDDR term))))
                                (CONS-COUNT TERM)))
                   :otf-flg t
                   :hints (("Goal"

                            :do-not-induct t
                            :in-theory (e/d (LIST-TO-LST
                                             cons-count)
                                            ())))))

                (local
                 (defthm dummy-lemma3
                   (IMPLIES (AND (CONSP (EX-FROM-RP TERM))
                                 (EQUAL (CAR (EX-FROM-RP TERM)) 'C)
                                 (CONSP (CDR (EX-FROM-RP TERM)))
                                 (CONSP (CDDR (EX-FROM-RP TERM)))
                                 (CONSP (CDDDR (EX-FROM-RP TERM)))
                                 (CONSP (CDDDDR (EX-FROM-RP TERM)))
                                 (NOT (CDR (CDDDDR (EX-FROM-RP TERM)))))
                            (O< (CONS-COUNT (LIST-TO-LST (CAR (CDDDDR (EX-FROM-RP TERM)))))
                                (CONS-COUNT TERM)))
                   :otf-flg t
                   :hints (("Goal"
                            :use ((:instance dummy-lemma2
                                             (term (ex-from-rp term)))
                                  (:instance dummy-lemma1
                                             (x (CONS-COUNT
                                                 (LIST-TO-LST (CAR (CDDDDR
                                                                    (EX-FROM-RP TERM))))))
                                             (z (CONS-COUNT TERM))
                                             (y (cons-count (EX-FROM-RP TERM)))))
                            :do-not-induct t
                            :in-theory (e/d () (dummy-lemma1 dummy-lemma2)))))))

               (define maybe-bitp-precheck ((term rp-termp)
                                            &optional
                                            ((upper-bound natp) '1))
                 :verify-guards nil
                 :returns (res)
                 :measure (cons-count term)
                 (b* (((when (has-bitp-rp term))
                       (1- upper-bound))
                      (term (ex-from-rp$ term)))
                   (case-match term
                     (('c & s pp c)
                      (b* ((upper-bound (1+ (* 2 upper-bound)))
                           (s-lst (list-to-lst s))
                           (upper-bound (len-lte s-lst upper-bound))
                           ((unless upper-bound) -1)
                           (pp-lst (list-to-lst pp))
                           (upper-bound (len-lte pp-lst upper-bound))
                           ((unless upper-bound) -1)
                           (c-lst (list-to-lst c)))
                        (f2 (maybe-bitp-precheck-lst c-lst upper-bound))))
                     (& -1))))
               (define maybe-bitp-precheck-lst ((lst rp-term-listp)
                                                (upper-bound natp))
                 :measure (cons-count lst)
                 :returns (res)
                 (if (atom lst)
                     upper-bound
                   (b* ((upper-bound (maybe-bitp-precheck (car lst) upper-bound))
                        ((when (equal upper-bound -1)) upper-bound)
                        (upper-bound (maybe-bitp-precheck-lst (cdr lst) upper-bound)))
                     upper-bound)))
               ///

               (defret-mutual result-of-maybe-bitp-precheck
                 (defret natp-of-<fn>
                   (implies (and (natp upper-bound)
                                 (not (equal res -1)))
                            (natp res))
                   :fn maybe-bitp-precheck)
                 (defret natp-of-<fn>
                   (implies (and (natp upper-bound)
                                 (not (equal res -1)))
                            (natp res))
                   :fn maybe-bitp-precheck-lst)
                 :hints (("Goal"
                          :in-theory (e/d (f2)
                                          (FLOOR2-IF-F2)))))

               (verify-guards maybe-bitp-precheck-fn
                 :hints (("Goal"
                          :in-theory (e/d (rp-term-listp)
                                          ())))))

(define is-c-bitp-traverse ((single-c rp-termp))
  ;; Check every piece of a c instance to see if it satisfies bitp.
  :returns (res booleanp)
  (b* (((unless (natp (maybe-bitp-precheck single-c)))
        nil)
       ((mv max-val min-val valid)
        (get-max-min-val single-c)))
    (and
     valid
     (equal min-val 0)
     (equal max-val 1))))

;; a b c e
;; a b c d e

#|(local
(defthm dummmy-rp-term-listp-lemma
(implies (and (rp-term-listp x)
(consp x))
(rp-term-listp (cdr x)))
:rule-classes :forward-chaining
:hints (("Goal"
:in-theory (e/d (rp-term-listp) ())))))|#

(progn
  (define pp-lst-subsetp ((pp-lst1 rp-term-listp)
                          (pp-lst2 rp-term-listp)
                          &key
                          (pp-flg 't))
    :measure (+ (cons-count pp-lst1)
                (cons-count pp-lst2))
    :prepwork ((local
                (in-theory (enable measure-lemmas))))
    (b* (((when (atom pp-lst1)) t)
         ((when (atom pp-lst2)) (atom pp-lst1))
         ((mv & cur1) (get-pp-and-coef (car pp-lst1)))
         ((mv & cur2) (get-pp-and-coef (car pp-lst2)))
         ((mv order equals) (if pp-flg (pp-order cur1 cur2) (s-order cur1 cur2)))
         (equals (or equals
                     (rp-equal-cnt cur1 cur2 2))))
      (cond (equals
             (pp-lst-subsetp (cdr pp-lst1) (cdr pp-lst2) :pp-flg pp-flg))
            (order nil)
            (t (pp-lst-subsetp pp-lst1 (cdr pp-lst2) :pp-flg pp-flg)))))

  (define pp-subsetp ((pp1 rp-termp)
                      (pp2 rp-termp)
                      &key
                      (pp-flg 't))
    (b* ((pp1-lst (list-to-lst pp1))
         (pp2-lst (list-to-lst pp2)))
      (pp-lst-subsetp pp1-lst pp2-lst :pp-flg pp-flg))))

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
      (cond ((rp-equal-cnt cur1 cur2 0)
             (and-lst-subsetp (cdr pp-lst1) (cdr pp-lst2)))
            ((lexorder2- cur1 cur2) nil)
            (t (and-lst-subsetp pp-lst1 (cdr pp-lst2))))))

  (define and-subsetp ((pp1 rp-termp)
                       (pp2 rp-termp))
    :guard-hints (("Goal"
                   :in-theory (e/d (RP-TERM-LISTP) ())))
    (b* ((pp1 (ex-from-rp$ pp1))
         (pp2 (ex-from-rp$ pp2))
         ;; Restricting to these cases may be too much. But nothing else should
         ;; appear here..
         ((unless (and (or (case-match pp1 (('and-list & ('list . &)) t))
                           (logbit-p (ex-from-rp$ pp1)))
                       (or (case-match pp2 (('and-list & ('list . &)) t))
                           (logbit-p (ex-from-rp$ pp2)))))
          nil)

         (pp1-lst (if (logbit-p (ex-from-rp$ pp1))
                      (list (ex-from-rp$ pp1))
                    (cdr (caddr pp1))))
         (pp2-lst (if (logbit-p (ex-from-rp$ pp2))
                      (list (ex-from-rp$ pp2))
                    (cdr (caddr pp2)))))
      (and-lst-subsetp pp1-lst pp2-lst))))

(local
 (defsection local-rp-termp-lemmas

   (defthm rp-term-listp-of-repeat
     (implies (rp-termp x)
              (rp-term-listp (repeat num x)))
     :hints (("Goal"
              :induct (REPEAT NUM X)
              :in-theory (e/d (rp-term-listp repeat) ()))))

   (defthm rp-term-listp-of-cons
     (equal (rp-term-listp (cons a b))
            (and (rp-termp a)
                 (rp-term-listp b)))
     :hints (("Goal"
              :in-theory (e/d (rp-term-listp) ()))))

   (defthm rp-termp-of-times
     (iff (rp-termp (list 'times a b))
          (and (rp-termp a)
               (rp-termp b)))
     :hints (("Goal"
              :expand (rp-termp (list 'times a b))
              :in-theory (e/d () ()))))

   (defthm rp-termp-of-list
     (iff (rp-termp (cons 'list rest))
          (rp-term-listp rest))
     :hints (("Goal"
              :expand (rp-termp (cons 'list rest))
              :in-theory (e/d () ()))))

   (defthm rp-termp-of-s-and-c
     (and (iff (rp-termp (cons 's rest))
               (rp-term-listp rest))
          (iff (rp-termp (cons 'c rest))
               (rp-term-listp rest)))
     :hints (("Goal"
              :expand ((rp-termp (cons 's rest))
                       (rp-termp (cons 'c rest)))
              :in-theory (e/d () ()))))

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
                              ()))))

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
              :in-theory (e/d () ()))))

   (defthm rp-termp-of-car-when-rp-term-listp
     (implies (and (rp-term-listp lst)
                   (consp lst))
              (rp-termp (car lst))))
   ))

(defsection decompress-s-c
  (define ligth-compress-s-c$fix-pp-lst$for-s ((pp1-lst rp-term-listp)
                                               (pp2-lst rp-term-listp)
                                               &key
                                               (pp-flg 't))
    ;; used to prep (s pp1 (c pp2)) so that the same elements in pp1 has the opposite sign as pp2.
    :measure (+ (cons-count pp1-lst)
                (cons-count pp2-lst))
    :prepwork ((local
                (in-theory (e/d (measure-lemmas)
                                ((:REWRITE MEASURE-LEMMA1)
                                 (:REWRITE DEFAULT-CAR)
                                 ;;                                 (:REWRITE ACL2::O-P-O-INFP-CAR)
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
         ((mv coef1 c1) (get-pp-and-coef (car pp1-lst)))
         ((mv ?coef2 c2) (get-pp-and-coef (car pp2-lst)))
         (c1-is-c2 (rp-equal-cnt c1 c2 0))
         ((when c1-is-c2)
          (b* (((mv pp1-lst-rest &)
                (ligth-compress-s-c$fix-pp-lst$for-s (cdr pp1-lst) (cdr pp2-lst) :pp-flg pp-flg )))
            (mv (cons-with-hint (if (equal (< coef1 0) (< coef2 0))
                                    (create-times-instance (- coef1) c1)
                                  (car pp1-lst))
                                pp1-lst-rest
                                pp1-lst)
                t)))
         ((mv order &)
          (if pp-flg
              (pp-order c1 c2)
            (s-order c1 c2))))
      (if order
          (b* (((mv pp1-lst-rest rest-changed)
                (ligth-compress-s-c$fix-pp-lst$for-s (cdr pp1-lst) pp2-lst :pp-flg pp-flg )))
            (mv (cons-with-hint (car pp1-lst) pp1-lst-rest pp1-lst) rest-changed))
        (b* (((mv pp1-lst-rest rest-changed)
              (ligth-compress-s-c$fix-pp-lst$for-s pp1-lst (cdr pp2-lst)
                                                   :pp-flg pp-flg)))
          (mv pp1-lst-rest rest-changed)))))

  (define light-compress-s-c$fix-pp$for-s ((pp1 rp-termp)
                                           (pp2 rp-termp)
                                           &key
                                           (pp-flg 't))
    :returns (res-pp1 rp-termp :hyp (rp-termp pp1))
    (b* ((pp1-lst (list-to-lst pp1))
         (pp2-lst (list-to-lst pp2))
         ((mv pp1-lst changed)
          (ligth-compress-s-c$fix-pp-lst$for-s pp1-lst pp2-lst :pp-flg pp-flg)))
      (if changed
          (create-list-instance pp1-lst)
        pp1)))

  (define light-compress-s-c$pass-pp-lst ((pp1-lst rp-term-listp)
                                          (pp2-lst rp-term-listp)
                                          &key
                                          (pp-flg 't))
    :measure (+ (cons-count pp1-lst)
                (cons-count pp2-lst))
    :prepwork ((local
                (in-theory (e/d (measure-lemmas)
                                ((:REWRITE MEASURE-LEMMA1)
                                 (:REWRITE DEFAULT-CAR)
                                 ;;                                 (:REWRITE ACL2::O-P-O-INFP-CAR)
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
         ((mv coef1 c1) (get-pp-and-coef c1))
         ((mv coef2 c2) (get-pp-and-coef c2))
         ((mv to-pass passable)
          (cond ((and* (rp-equal-cnt c1 c2 1)
                       (or* (and* (equal coef1 1)
                                  (equal coef2 -1))
                            (and* (equal coef1 -1)
                                  (equal coef2 1))))
                 (mv (car pp1-lst) t))
                (t (mv nil nil))))
         ((when passable)
          (b* (((mv pp1-lst-rest pp2-lst-rest &)
                (light-compress-s-c$pass-pp-lst (cdr pp1-lst) (cdr pp2-lst)
                                                :pp-flg pp-flg)))
            (mv pp1-lst-rest (cons to-pass pp2-lst-rest) t)))
         ((mv order &)
          (if pp-flg
              (pp-order c1 c2)
            (s-order c1 c2))))
      (if order
          (b* (((mv pp1-lst-rest pp2-lst-rest rest-changed)
                (light-compress-s-c$pass-pp-lst (cdr pp1-lst) pp2-lst :pp-flg pp-flg)))
            (mv (cons-with-hint (car pp1-lst) pp1-lst-rest pp1-lst)
                pp2-lst-rest rest-changed))
        (b* (((mv pp1-lst-rest pp2-lst-rest rest-changed)
              (light-compress-s-c$pass-pp-lst pp1-lst (cdr pp2-lst) :pp-flg pp-flg)))
          (mv pp1-lst-rest (cons-with-hint (car pp2-lst) pp2-lst-rest pp2-lst) rest-changed)))))

  (define light-compress-s-c$pass-pp ((pp1 rp-termp)
                                      (pp2 rp-termp)
                                      &key
                                      (pp-flg 't))
    :returns (mv (res-pp1 rp-termp :hyp (rp-termp pp1))
                 (res-pp2 rp-termp :hyp (and (rp-termp pp1)
                                             (rp-termp pp2)))
                 (changed booleanp))
    (b* ((pp1-lst (list-to-lst pp1))
         (pp2-lst (list-to-lst pp2))
         ((mv pp1-lst pp2-lst changed)
          (light-compress-s-c$pass-pp-lst pp1-lst pp2-lst :pp-flg pp-flg)))
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
                                  (s rp-termp)
                                  (c-arg rp-termp))
    :returns (mv (pp-res rp-termp :hyp (rp-termp pp))
                 (s-res rp-termp :hyp (rp-termp s))
                 (c-arg-res rp-termp :hyp (and (rp-termp pp)
                                               (rp-termp s)
                                               (rp-termp c-arg)))
                 (changed booleanp))
    :measure (cons-count c-arg)
    :hints (("Goal"
             :in-theory (e/d (measure-lemmas
                              o<-chain-2
                              o<-chain)
                             ())))
    :verify-guards :after-returns
    (case-match c-arg
      (('list single-c)
       (b* ((single-c (ex-from-rp$ single-c))
            ((unless (and (single-c-p single-c)))
             (mv pp s c-arg nil))
            (pp-arg1 (cadddr single-c))
            (s-arg1 (caddr single-c))
            (c-arg1 (car (cddddr single-c)))
            ((mv pp-new pp-arg1 changed1)
             (light-compress-s-c$pass-pp pp pp-arg1 :pp-flg t))
            ((mv s-new s-arg1 changed2)
             (light-compress-s-c$pass-pp s s-arg1 :pp-flg nil))
            ((unless (or changed1 changed2))
             (mv pp s c-arg nil))
            ((mv pp-arg1 s-arg1 c-arg1 &)
             (light-compress-s-c-aux pp-arg1 s-arg1 c-arg1)))
         (mv pp-new s-new
             `(list (c ',(calculate-c-hash s-arg1 pp-arg1 c-arg1)
                       ,s-arg1 ,pp-arg1 ,c-arg1))
             t)))
      (& (mv pp s c-arg nil))))

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
                   ((mv pp s-res c-arg changed)
                    (light-compress-s-c-aux pp ''nil (cadddr term)))
                   ((unless (and changed
                                 (equal s-res ''nil))) ;; this has to be nil
                    ;; all the time but to make the proofs easier...
                    term-orig))
                `(s ',(calculate-s-hash pp c-arg) ,pp ,c-arg)))
             (& term-orig))))
        (('c & s pp c-arg)
         (b* (((mv pp s c-arg changed)
               (light-compress-s-c-aux pp s c-arg)))
           (if changed
               `(c ',(calculate-c-hash s pp c-arg) ,s ,pp ,c-arg)
             term-orig)))
        (& term-orig))))

  (defines decompress-s-c
    :flag-local nil
    (define decompress-s-c ((term rp-termp) &key (limit '*large-number*))
      :measure (nfix limit)
      :guard (natp limit)
      :returns (mv (res-term)
                   (coughed-s)
                   (coughed-pp))
      :verify-guards nil
      (b* (((when (zp limit)) (mv term ''nil ''nil))
           (term-orig term)
           (term (ex-from-rp$ term)))
        (case-match term
          (('s & pp ('list single-c))
           (b* (((mv single-c coughed-s coughed-pp)
                 (decompress-s-c single-c :limit (1- limit)))
                (- (and (not (equal coughed-s ''nil))
                        (hard-error 'decompress-s-c
                                    "We do not expect decompress-s-c to cough s
    terms to s instances yet... ~%" nil)))
                (pp (pp-sum-merge pp coughed-s)) ;; for proofs...

                (pp (pp-sum-merge pp coughed-pp))
                (pp (s-fix-args pp))
                (c (create-list-instance (list single-c))))
             (mv `(s ',(calculate-s-hash pp c) ,pp ,c)
                 ''nil
                 ''nil)))
          (('c & s pp ('list . c-lst))
           (b* (((mv c-lst coughed-s coughed-pp)
                 (decompress-s-c-lst c-lst :limit (1- limit)))
                (pp (pp-sum-merge pp coughed-pp))
                ((mv coughed-pp pp) (c-fix-pp-args pp))
                (s (s-sum-merge s coughed-s))
                ((mv coughed-s s) (c-fix-s-args s))
                (c (create-list-instance c-lst)))
             (mv `(c ',(calculate-c-hash s pp c) ,s ,pp ,c)
                 coughed-s
                 coughed-pp)))
          (('c & s pp ''nil)
           (b* (((mv coughed-pp pp) (c-fix-pp-args pp))
                ((mv coughed-s s) (c-fix-s-args s))
                (c ''nil))
             (mv `(c ',(calculate-c-hash s pp c) ,s ,pp ,c)
                 coughed-s
                 coughed-pp)))
          (& (mv term-orig ''nil ''nil)))))
    (define decompress-s-c-lst ((lst rp-term-listp) &key (limit '*large-number*))
      :measure (nfix limit)
      :guard (natp limit)
      :returns (mv (res-term-lst)
                   (coughed-s)
                   (coughed-pp))
      (b* (((when (zp limit)) (mv lst ''nil ''nil))
           ((when (atom lst)) (mv nil ''nil ''nil))
           (limit (1- limit))
           ((mv cur coughed-s1 coughed-pp1)
            (decompress-s-c (car lst) :limit limit))
           ((mv rest coughed-s2 coughed-pp2)
            (decompress-s-c-lst (cdr lst) :limit limit))
           (coughed-s (s-sum-merge coughed-s1 coughed-s2))
           (coughed-pp (pp-sum-merge coughed-pp1 coughed-pp2)))
        (mv (cons cur rest)
            coughed-s coughed-pp)))

    ///

    (defret-mutual
      rp-termp-of-<fn>
      (defret rp-termp-of-<fn>
        :hyp (rp-termp term)
        (and (rp-termp res-term)
             (rp-termp coughed-pp)
             (rp-termp coughed-s))
        :fn decompress-s-c)
      (defret rp-termp-of-<fn>
        :hyp (rp-term-listp lst)
        (and (rp-term-listp res-term-lst)
             (rp-termp coughed-pp)
             (rp-termp coughed-s))
        :fn decompress-s-c-lst))
    (verify-guards decompress-s-c-fn)))

#|(progn
(encapsulate
(((c-pattern1-reduce-enabled) => *))
(local
(defun c-pattern1-reduce-enabled ()
nil)))

(defmacro enable-c-pattern1-reduce (enable)
(if enable
`(defattach c-pattern1-reduce-enabled return-t)
`(defattach c-pattern1-reduce-enabled return-nil)))

(enable-c-pattern1-reduce t))||#

(define c-pattern1-reduce ((s-lst rp-term-listp)
                           (pp-lst rp-term-listp)
                           (c-lst rp-term-listp))
  ;; This function is called before forming a single-c instance as (c s pp c).
  ;; It might be possible to compress the c instance.
  :returns (mv (s-res-lst rp-term-listp
                          :hyp (and (rp-term-listp s-lst)
                                    (rp-term-listp pp-lst)
                                    (rp-term-listp c-lst)))
               (pp-res-lst rp-term-listp
                           :hyp (and (rp-term-listp s-lst)
                                     (rp-term-listp pp-lst)
                                     (rp-term-listp c-lst)))
               (c-res-lst rp-term-listp
                          :hyp (and (rp-term-listp s-lst)
                                    (rp-term-listp pp-lst)
                                    (rp-term-listp c-lst))))
  (cond
   ;;(s-lst (mv s-lst pp-lst c-lst))
   ;;((not (c-pattern1-reduce-enabled)) (mv s-lst pp-lst c-lst))
   (t
    (case-match c-lst
      ((('c & c-s c-pp &))
       (b* (((unless (and (pp-lst-subsetp pp-lst (list-to-lst c-pp))
                          (pp-lst-subsetp s-lst (list-to-lst c-s))))
             (mv s-lst pp-lst c-lst))
            (--pp-lst (negate-lst pp-lst t))
            (--s-lst (negate-lst s-lst t))
            (single-c `(c '0
                          ,(create-list-instance --s-lst)
                          ,(create-list-instance --pp-lst)
                          ,(create-list-instance c-lst)))
            (compressed (light-compress-s-c single-c)))
         (case-match compressed
           (('c & ''nil ''nil ('list single-c))
            (b* (((mv max min valid) (get-max-min-val single-c))
                 ((unless (and valid
                               (equal max 0)
                               (equal min -1)))
                  (mv s-lst pp-lst c-lst))
                 ((mv decompressed coughed-s coughed-pp)
                  (decompress-s-c single-c))
                 (coughed-pp-lst (pp-sum-merge-aux pp-lst (list-to-lst
                                                           coughed-pp)))
                 (coughed-s-lst (s-sum-merge-aux s-lst (list-to-lst
                                                        coughed-s)))
                 ((unless (and (equal coughed-pp-lst nil)
                               (equal coughed-s-lst nil)))
                  (mv s-lst pp-lst c-lst)))
              (case-match decompressed
                (('c & s pp ('list . c-lst)) ;; changed it to this way to prove
                 ;; measure of c-sum-merge with count-c.
                 (mv (list-to-lst s) (list-to-lst pp) c-lst))
                (('c & s pp ''nil)
                 (mv (list-to-lst s) (list-to-lst pp) nil))
                (& (mv s-lst pp-lst c-lst)))))
           (& (mv s-lst pp-lst c-lst)))))
      (& (mv s-lst pp-lst c-lst))))))

(progn
  (define and-list-instance-to-binary-and-aux ((lst))
    :returns (res rp-termp
                  :hyp (rp-term-listp lst))
    (if (atom lst)
        ''1
      `(binary-and ,(car lst)
                   ,(and-list-instance-to-binary-and-aux (cdr lst)))))

  (define and-list-instance-to-binary-and ((term))
    :Returns (res rp-termp
                  :hyp (rp-termp term))
    (case-match term
      (('and-list & ('list . lst))
       (and-list-instance-to-binary-and-aux lst))
      (& term))))

(define single-s-to-pp-lst ((pp1 rp-termp)
                            (pp2 rp-termp)
                            (pp3 rp-termp))
  :returns (mv (res-pp-lst rp-term-listp
                           :hyp (and (rp-termp pp1)
                                     (rp-termp pp2)
                                     (rp-termp pp3)))
               (success booleanp))
  :verify-guards nil
  (b* ((pp1 (and-list-instance-to-binary-and pp1))
       (pp2 (and-list-instance-to-binary-and pp2))
       (pp3 (and-list-instance-to-binary-and pp3))
       ((Unless (and (pp-term-p pp1)
                     (pp-term-p pp2)
                     (pp-term-p pp3)
                     ))
        (mv nil nil)))
    (mv (pp-flatten `(binary-xor ,pp1
                                 (binary-xor ,pp2
                                             ,pp3)))
        t))
  ///
  (verify-guards single-s-to-pp-lst
    :hints (("Goal"
             :expand ((:free (x y)
                             (pp-term-p `(binary-xor ,x ,y))))
             :in-theory (e/d (is-rp ex-from-rp) ())))))

(define single-c-to-pp-lst ((pp1 rp-termp)
                            (pp2 rp-termp)
                            (pp3 rp-termp))
  :returns (mv (res-pp-lst rp-term-listp
                           :hyp (and (rp-termp pp1)
                                     (rp-termp pp2)
                                     (rp-termp pp3)))
               (success booleanp))
  :verify-guards nil
  (b* ((pp1 (and-list-instance-to-binary-and pp1))
       (pp2 (and-list-instance-to-binary-and pp2))
       (pp3 (and-list-instance-to-binary-and pp3))
       ((Unless (and (pp-term-p pp1)
                     (pp-term-p pp2)
                     (pp-term-p pp3)))
        (mv nil nil)))
    (mv (pp-flatten `(binary-or (binary-and ,pp1 ,pp2)
                                (binary-or (binary-and ,pp2 ,pp3)
                                           (binary-and ,pp1 ,pp3))))
        t))
  ///
  (verify-guards single-c-to-pp-lst
    :hints (("Goal"
             :expand ((:free (x y)
                             (pp-term-p `(binary-or ,x ,y))))
             :in-theory (e/d (is-rp ex-from-rp) ())))))

(progn
  (encapsulate
    (((pattern2-reduce-enabled) => *))
    (local
     (defun pattern2-reduce-enabled ()
       nil)))

  (defmacro enable-pattern2-reduce (enable)
    (if enable
        `(defattach  pattern2-reduce-enabled return-t)
      `(defattach  pattern2-reduce-enabled return-nil)))

  (enable-pattern2-reduce t))

#|(progn
(encapsulate
(((pattern2-aggressive-reduce-enabled) => *))
(local
(defun pattern2-aggressive-reduce-enabled ()
nil)))

(defmacro enable-pattern2-aggressive-reduce  (enable)
(if enable
`(defattach pattern2-aggressive-reduce-enabled return-t)
`(defattach pattern2-aggressive-reduce-enabled return-nil)))

(enable-pattern2-aggressive-reduce nil))||#

(define has-unflatenned-pp ((pp-lst rp-term-listp))
  (if (atom pp-lst)
      nil
    (or (binary-fnc-p (ex-from-rp$ (car pp-lst)))
        (has-unflatenned-pp (cdr pp-lst)))))

(define c-pattern2-reduce-aux-cond (new-pp-lst)
  (and (consp new-pp-lst)
       (not (cdr new-pp-lst))
       (let ((e (car new-pp-lst)))
         (case-match e
           (('and-list & ('list . lst))
            (<= (len lst) 4)
            )))))

(define c-pattern2-reduce ((s-lst rp-term-listp)
                           (pp-lst rp-term-listp)
                           (c-lst rp-term-listp))
  :returns (mv
            (res-pp-lst rp-term-listp
                        :hyp (rp-term-listp pp-lst))
            (reducedp booleanp))

  :verify-guards :after-returns
  (b* (((unless (and (not s-lst)
                     (not c-lst)
                     (not (has-unflatenned-pp pp-lst))
                     (pattern2-reduce-enabled)))
        (mv nil nil))

       ;;(aggressive (pattern2-aggressive-reduce-enabled))
       )
    (case-match pp-lst
      ((''1 pp1 pp2 pp3)
       (b* (((unless (or
                      (equal pp1 ''1)
                      (and (and-subsetp pp2 pp1)
                           (and-subsetp pp3 pp1))))
             (mv nil nil))
            ((mv new-pp-lst1 success1) (single-c-to-pp-lst pp1 pp2 pp3))
            ((mv new-pp-lst2 success2) (single-s-to-pp-lst pp1 pp2 pp3))
            ((unless (and success1 success2))
             (mv nil nil)))
         (mv (pp-sum-merge-aux new-pp-lst1 new-pp-lst2)  t)))
      ((pp1 pp2 pp3)
       (b* (((unless (or
                      (equal pp1 ''1)
                      (and (and-subsetp pp2 pp1)
                           (and-subsetp pp3 pp1))))
             (mv nil nil))
            ((mv new-pp-lst success) (single-c-to-pp-lst pp1 pp2 pp3))
            ((unless success)
             (mv nil nil)))
         (mv new-pp-lst t)))
      ((pp1 pp2)
       (b* (((mv new-pp-lst success) (single-c-to-pp-lst pp1 pp2 ''0))
            ((when (and success
                        ;; (or t
                        ;;     (equal pp1 ''1)
                        ;;     (and (and-subsetp pp2 pp1))
                        ;;     (c-pattern2-reduce-aux-cond new-pp-lst))
                        ))
             (mv new-pp-lst t))
            ;; ((when t) (mv nil nil))
            ;; ((mv e-lst1 success) (cond ((and-list-p pp1)
            ;;                             (mv (list-to-lst (third pp1)) t))
            ;;                            ((logbit-p pp1)
            ;;                             (mv (list pp1) t))
            ;;                            (t (mv nil nil))))
            ;; ((unless success) (mv nil nil))
            ;; ((mv e-lst2 s/c success) (cond ((and-times-list-p pp2)
            ;;                                 (mv (list-to-lst (third pp2))
            ;;                                     (fourth pp2)
            ;;                                     (has-bitp-rp (fourth pp2))))
            ;;                                (t (mv nil nil nil))))
            ;; ((unless success) (mv nil nil))
            ;; (e-lst (merge-sorted-and$-lists e-lst1 e-lst2))
            ;; (res (create-and-times-list-instance e-lst s/c))
            )
         (mv nil nil)))
      (& (mv nil nil)))))

(define pattern0-syntax-check ((s-lst rp-term-listp)
                               (pp-lst rp-term-listp)
                               (c-lst rp-term-listp)
                               (limit natp))
  :returns (valid-syntax booleanp)
  :measure (nfix limit)
  (b* (((when (zp limit)) nil)
       ((mv pp-cnt pp-valid) (case-match pp-lst
                               ((& &) (mv 2 t))
                               ((&) (mv 1 t))
                               (() (mv 0 t))
                               (& (mv 0 nil))))
       ((unless pp-valid) nil)
       (total-cnt pp-cnt)
       ((mv s-cnt s-valid)
        (case-match s-lst
          (()
           (mv 0 t))
          ((x)
           (mv 1 (b* (((when (> (1+ total-cnt) 2)) nil)
                      (x (ex-from-rp x)))
                   (case-match x
                     (('s & pp-arg c-arg)
                      (pattern0-syntax-check nil
                                             (list-to-lst pp-arg)
                                             (list-to-lst c-arg)
                                             (1- limit)))))))
          ((x y)
           (mv 2 (b* (((when (> (+ 2 total-cnt) 2)) nil)
                      (x (ex-from-rp x))
                      (y (ex-from-rp y)))
                   (and
                    (case-match x
                      (('s & pp-arg c-arg)
                       (pattern0-syntax-check nil
                                              (list-to-lst pp-arg)
                                              (list-to-lst c-arg)
                                              (1- limit))))
                    (case-match y
                      (('s & pp-arg c-arg)
                       (pattern0-syntax-check nil
                                              (list-to-lst pp-arg)
                                              (list-to-lst c-arg)
                                              (1- limit))))))))
          (& (mv 0 nil))))
       ((Unless s-valid) nil)
       (total-cnt (+ pp-cnt s-cnt))
       ((mv c-cnt c-valid)
        (case-match c-lst
          (()
           (mv 0 t))
          ((x)
           (mv 1 (b* (((when (> (1+ total-cnt) 2)) nil)
                      (x (ex-from-rp x)))
                   (case-match x
                     (('c & s-arg pp-arg c-arg)
                      (pattern0-syntax-check (list-to-lst s-arg)
                                             (list-to-lst pp-arg)
                                             (list-to-lst c-arg)
                                             (1- limit)))))))
          ((x y)
           (mv 2 (b* (((when (> (+ 2 total-cnt) 2)) nil)
                      (x (ex-from-rp x))
                      (y (ex-from-rp y)))
                   (and
                    (case-match x
                      (('c & s-arg pp-arg c-arg)
                       (pattern0-syntax-check (list-to-lst s-arg)
                                              (list-to-lst pp-arg)
                                              (list-to-lst c-arg)
                                              (1- limit))))
                    (case-match y
                      (('c & s-arg pp-arg c-arg)
                       (pattern0-syntax-check (list-to-lst s-arg)
                                              (list-to-lst pp-arg)
                                              (list-to-lst c-arg)
                                              (1- limit))))))))
          (& (mv 0 nil))))
       ((unless c-valid) nil))
    (= (+ s-cnt c-cnt pp-cnt) 2)))

(define pattern0-reduce-aux-pp-lst ((pp-lst rp-term-listp))
  :returns (mv (pp1 rp-termp :hyp (rp-term-listp pp-lst))
               (pp2 rp-termp :hyp (rp-term-listp pp-lst))
               (pp-cnt natp)
               (pp-valid booleanp))
  (case-match pp-lst
    ((pp1 pp2)
     (if (and (pp-term-p pp1)
              (pp-term-p pp2))
         (mv pp1 pp2 2 t)
       (mv ''nil ''nil 0 nil)))
    ((pp1)
     (if (pp-term-p pp1)
         (mv pp1 ''0 1 t)
       (mv ''nil ''nil 0 nil)))
    (()
     (mv ''0 ''0 0 t))
    (&
     (mv ''nil ''nil 0 nil)))
  ///

  (defret pp-term-p-<fn>
    (implies pp-valid
             (and (pp-term-p pp1)
                  (pp-term-p pp2)))))

(acl2::defines
 pattern0-reduce-aux
 :flag-defthm-macro defthm-pattern0-reduce-aux
 :flag-local nil
 :returns-hints (("Goal"
                  :expand ((pattern0-reduce-aux nil pp-lst nil limit))
                  :do-not-induct t
                  :in-theory (e/d () ())))
 :prepwork ((local
             (in-theory (disable (:definition not)
                                 (:definition natp)
                                 (:rewrite acl2::zp-open)
                                 (:type-prescription single-c-p$inline)
                                 (:type-prescription rp-termp)
                                 (:type-prescription acl2::element-list-p)
                                 (:type-prescription str::dec-digit-char-listp)
                                 (:rewrite quotep-term-with-ex-from-rp)
                                 (:rewrite rp-termp-implies-subterms)
                                 (:type-prescription ex-from-synp)
                                 (:rewrite default-+-1)
                                 (:type-prescription pp-term-p-fn)
                                 (:rewrite acl2::fold-consts-in-+)
                                 (:type-prescription o-finp)
                                 (:type-prescription rp-term-listp)
                                 (:definition pp-term-p-fn)
                                 (:rewrite default-cdr)
                                 (:rewrite default-car)
                                 (:rewrite default-+-2)
                                 (:rewrite is-if-rp-termp)
                                 (:rewrite is-rp-pseudo-termp)))))
 :verify-guards nil

 (define pattern0-reduce-aux-s-lst ((s-lst rp-term-listp)
                                    (limit natp)
                                    (search-limit integerp))
   :returns (mv (s1 rp-termp :hyp (rp-term-listp s-lst))
                (s2 rp-termp :hyp (rp-term-listp s-lst))
                (s-cnt natp)
                (s-valid booleanp))
   :measure (nfix limit)
   (if (zp limit)
       (mv ''nil ''nil 0 nil)
     (case-match s-lst
       ((s1 s2)
        (b* (((when (< (- search-limit 2) 0))
              (mv ''nil ''nil 0 nil))
             (s1 (ex-from-rp$ s1))
             (s2 (ex-from-rp$ s2))
             ((unless (and (single-s-p s1)
                           (single-s-p s2)))
              (mv ''nil ''nil 0 nil))
             ((mv term1 term2 s1-valid)
              (pattern0-reduce-aux nil
                                   (list-to-lst (caddr s1))
                                   (list-to-lst (cadddr s1))
                                   (1- limit)))
             ((unless s1-valid)
              (mv ''nil ''nil 0 nil))
             (s1 `(binary-xor ,term1 ,term2))
             ((mv term1 term2 s2-valid)
              (pattern0-reduce-aux nil
                                   (list-to-lst (caddr s2))
                                   (list-to-lst (cadddr s2))
                                   (1- limit)))
             ((unless s2-valid)
              (mv ''nil ''nil 0 nil))
             (s2 `(binary-xor ,term1 ,term2)))
          (mv s1 s2 2 t)))
       ((s1)
        (b* (((when (< (- search-limit 1) 0))
              (mv ''nil ''nil 0 nil))
             (s1 (ex-from-rp s1))
             ((unless (single-s-p s1))
              (mv ''nil ''nil 0 nil))
             ((mv term1 term2 s1-valid)
              (pattern0-reduce-aux nil
                                   (list-to-lst (caddr s1))
                                   (list-to-lst (cadddr s1))
                                   (1- limit)))
             ((unless s1-valid)
              (mv ''nil ''nil 0 nil))
             (s1 `(binary-xor ,term1 ,term2)))
          (mv s1 ''0 1 t)))
       (()
        (mv ''0 ''0 0 t))
       (&
        (mv ''nil ''nil 0 nil)))))

 (define pattern0-reduce-aux-c-lst ((c-lst rp-term-listp)
                                    (limit natp)
                                    (search-limit integerp))
   :returns (mv (c1 rp-termp :hyp (rp-term-listp c-lst))
                (c2 rp-termp :hyp (rp-term-listp c-lst))
                (c-cnt natp)
                (c-valid booleanp))
   :measure (nfix limit)
   (if (zp limit)
       (mv ''nil ''nil 0 nil)
     (case-match c-lst
       ((c1 c2)
        (b* (((when (< (- search-limit 2) 0))
              (mv ''nil ''nil 0 nil))
             (c1 (ex-from-rp$ c1))
             (c2 (ex-from-rp$ c2))
             ((unless (and (single-c-p c1)
                           (single-c-p c2)))
              (mv ''nil ''nil 0 nil))
             ((mv term1 term2 c1-valid)
              (pattern0-reduce-aux (list-to-lst (caddr c1))
                                   (list-to-lst (cadddr c1))
                                   (list-to-lst (caddr(cddr c1)))
                                   (1- limit)))
             ((unless c1-valid)
              (mv ''nil ''nil 0 nil))
             (c1 `(binary-and ,term1 ,term2))
             ((mv term1 term2 c2-valid)
              (pattern0-reduce-aux (list-to-lst (caddr c2))
                                   (list-to-lst (cadddr c2))
                                   (list-to-lst (caddr(cddr c2)))
                                   (1- limit)))
             ((unless c2-valid)
              (mv ''nil ''nil 0 nil))
             (c2 `(binary-and ,term1 ,term2)))
          (mv c1 c2 2 t)))
       ((c1)
        (b* (((when (< (- search-limit 1) 0))
              (mv ''nil ''nil 0 nil))
             (c1 (ex-from-rp c1))
             ((unless (single-c-p c1))
              (mv ''nil ''nil 0 nil))
             ((mv term1 term2 c1-valid)
              (pattern0-reduce-aux (list-to-lst (caddr c1))
                                   (list-to-lst (cadddr c1))
                                   (list-to-lst (caddr(cddr c1)))
                                   (1- limit)))
             ((unless c1-valid)
              (mv ''nil ''nil 0 nil))
             (c1 `(binary-and ,term1 ,term2)))
          (mv c1 ''0 1 t)))
       (()
        (mv ''0 ''0 0 t))
       (&
        (mv ''nil ''nil 0 nil)))))

 (define pattern0-reduce-aux ((s-lst rp-term-listp)
                              (pp-lst rp-term-listp)
                              (c-lst rp-term-listp)
                              (limit natp))
   :returns (mv (pp-term1 rp-termp :hyp (and (rp-term-listp s-lst)
                                             (rp-term-listp pp-lst)
                                             (rp-term-listp c-lst)))
                (pp-term2 rp-termp :hyp (and (rp-term-listp s-lst)
                                             (rp-term-listp pp-lst)
                                             (rp-term-listp c-lst)))
                (valid booleanp))
   :measure (nfix limit)

   ;;:verify-guards nil

   (b* (((when (zp limit)) (mv ''nil ''nil nil))
        ((mv pp1 pp2 pp-cnt pp-valid)
         (pattern0-reduce-aux-pp-lst pp-lst))
        ((unless pp-valid)
         (mv ''nil ''nil nil))
        ((mv s1 s2 s-cnt s-valid)
         (pattern0-reduce-aux-s-lst s-lst (1- limit) (- 2 pp-cnt)))
        ((unless s-valid)
         (mv ''nil ''nil nil))
        ((mv c1 c2 c-cnt c-valid)
         (pattern0-reduce-aux-c-lst c-lst (1- limit) (+ 2 (- pp-cnt) (- s-cnt))))
        ((unless c-valid)
         (mv ''nil ''nil nil)))
     (cond ((and* (= s-cnt 0) (= pp-cnt 0) (= c-cnt 2))
            (mv c1 c2 t))
           ((and* (= s-cnt 0) (= pp-cnt 1) (= c-cnt 1))
            (mv pp1 c1 t))
           ((and* (= s-cnt 0) (= pp-cnt 2) (= c-cnt 0))
            (mv pp1 pp2 t))
           ((and* (= s-cnt 1) (= pp-cnt 0) (= c-cnt 1))
            (mv s1 c1 t))
           ((and* (= s-cnt 1) (= pp-cnt 1) (= c-cnt 0))
            (mv s1 pp1 t))
           ((and* (= s-cnt 2) (= pp-cnt 0) (= c-cnt 0))
            (mv s1 s2 t))
           (t
            (mv ''nil ''nil nil)))))
 ///

 (local
  (defthm dummy-lemma
    (and (implies (and (natp x)
                       (natp y))
                  (and (integerp (+ 2 (- x) (- y)))))
         (implies (natp x)
                  (integerp (+ 2 (- x)))))))

 (verify-guards  pattern0-reduce-aux
   :hints (("Goal"
            :in-theory (e/d ()
                            ((:type-prescription single-s-p$inline)
                             (:type-prescription single-c-p$inline)
                             (:type-prescription o<)
                             (:type-prescription zp)
                             (:type-prescription quotep)
                             (:rewrite rp-termp-should-term-be-in-cons-lhs)
                             (:rewrite extract-from-rp-pseudo-term-listp)
                             (:rewrite local-measure-lemma4)
                             (:rewrite rp-termp-caddddr)
                             (:rewrite rp-termp-cadr)
                             (:rewrite rp-termp-extract-from-rp))))))

 (defret-mutual pp-term-p-of-<fn>
   (defret pp-term-p-of-<fn>
     (implies s-valid
              (and (pp-term-p s1)
                   (pp-term-p s2)))
     :fn pattern0-reduce-aux-s-lst)
   (defret pp-term-p-of-<fn>
     (implies c-valid
              (and (pp-term-p c1)
                   (pp-term-p c2)))
     :fn pattern0-reduce-aux-c-lst)
   (defret pp-term-p-of-<fn>
     (implies valid
              (and (pp-term-p pp-term1)
                   (pp-term-p pp-term2)))
     :fn pattern0-reduce-aux)
   :hints (("Goal"
            :expand ((pattern0-reduce-aux nil pp-lst nil limit)
                     (:free (x) (pp-term-p (cons 'binary-and x)))
                     (:free (x) (pp-term-p (cons 'binary-xor x)))
                     (:free (x) (ex-from-rp (cons 'binary-and x)))
                     (:free (x) (ex-from-rp (cons 'binary-xor x))))
            :do-not-induct t
            :in-theory (e/d (is-rp) ())))))

(define c-pattern0-reduce ((s-lst rp-term-listp)
                           (pp-lst rp-term-listp)
                           (c-lst rp-term-listp))
  :returns (reduced booleanp)
  :verify-guards t
  :guard-hints (("Goal"
                 :expand ((:free (x) (pp-term-p (cons 'binary-and x)))
                          (:free (x) (ex-from-rp (cons 'binary-and x))))
                 :in-theory (e/d (is-rp) (pp-term-p))))

  (and (pattern0-syntax-check s-lst pp-lst c-lst 10)
       (b* (((when (or (cons-count-compare pp-lst 50)
                       (cons-count-compare s-lst 100)
                       (cons-count-compare c-lst 150)))
             nil)
            ((mv pp-term1 pp-term2 valid)
             (pattern0-reduce-aux s-lst pp-lst c-lst 10))
            ((unless valid) nil)
            (flatten-res (pp-flatten `(binary-and ,pp-term1 ,pp-term2)))
            ((when (not flatten-res))
             (progn$ (cw "c-pattern0-reduce match (3)! ~%")
                     t)))
         nil))

  ///
  (verify-guards c-pattern0-reduce
    :hints (("Goal"
             :expand ((:free (x)
                             (pp-term-p (cons 'binary-and x)))
                      (:free (x)
                             (ex-from-rp (cons 'binary-and x))))
             :in-theory (e/d (is-rp) ())))))

(define s-pattern0-reduce ((pp rp-termp)
                           (c rp-termp))
  :returns (reduced booleanp)
  :verify-guards nil

  (b* ((pp-lst (list-to-lst pp))
       (c-lst (list-to-lst c)))
    (if (pattern0-syntax-check nil pp-lst c-lst 10)
        (b* (((when (or (cons-count-compare pp-lst 50)
                        (cons-count-compare c-lst 150)))
              nil)
             ((mv pp-term1 pp-term2 valid)
              (pattern0-reduce-aux nil pp-lst c-lst 10))
             ((unless valid) nil)
             (flatten-res (pp-flatten `(binary-xor ,pp-term1 ,pp-term2)))
             ((when (not flatten-res))
              (progn$ (cw "s-pattern0-reduce match (1,2,3)! ~%")
                      t)))
          nil)
      nil))
  ///
  (verify-guards s-pattern0-reduce
    :hints (("Goal"
             :expand ((:free (x)
                             (pp-term-p (cons 'binary-xor x)))
                      (:free (x)
                             (ex-from-rp (cons 'binary-xor x))))
             :in-theory (e/d (is-rp) ())))))

(defun quoted-listp (lst)
  (declare (xargs :mode :logic :guard t))
  (if (atom lst)
      (EQUAL LST NIL)
    (and (quotep (car lst))
         (consp (cdar lst))
         (quoteD-listp (cdr lst)))))

(define all-quoted-list (term)
  (case-match term
    (('list . lst)
     (quoted-listp lst))
    (''nil
     t)))

(define s-of-s-fix-lst ((s-lst rp-term-listp)
                        (pp-lst rp-term-listp)
                        (c-lst rp-term-listp))
  :returns (mv (pp-res-lst rp-term-listp
                           :hyp (and (rp-term-listp s-lst)
                                     (rp-term-listp pp-lst)
                                     (rp-term-listp c-lst)))
               (c-res-lst rp-term-listp
                          :hyp (and (rp-term-listp s-lst)
                                    (rp-term-listp pp-lst)
                                    (rp-term-listp c-lst))))
  ;; similar to s-of-s-fix-lst but it doesn't try to merge c-lsts
  :measure (acl2-count  s-lst)
  (b* (((when (atom s-lst)) (mv pp-lst c-lst))
       ((mv pp-lst c-lst) (s-of-s-fix-lst (cdr s-lst) pp-lst c-lst))
       ((mv coef cur-s) (get-pp-and-coef (car s-lst)))
       ((when (evenp coef))
        (mv pp-lst c-lst))
       (cur-s-extracted (ex-from-rp$ cur-s)))
    (case-match cur-s-extracted
      (('s & cur-pp cur-c)
       (b* ((cur-c-lst (list-to-lst cur-c))
            (c-lst (sum-merge-lst-for-s c-lst cur-c-lst)) ;; put c's together
            ;; without trying to merge them..
            (pp-lst (pp-sum-merge-lst-for-s (list-to-lst cur-pp) pp-lst)))
         (mv pp-lst c-lst)))
      (''nil
       (mv pp-lst c-lst))
      (&
       (progn$ (cw "Unexpected s term ~p0 ~%" cur-s)
               (hard-error 'S-OF-S-FIX-LST "Read above.." nil)
               (mv (cons cur-s pp-lst)
                   c-lst))))))

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

  :returns (mv (reduced-pp-lst rp-term-listp
                               :hyp (and (rp-termp pp)
                                         (rp-termp c)))
               (reduced-c-lst rp-term-listp
                              :hyp (and (rp-termp pp)
                                        (rp-termp c)))
               (reducedp booleanp))
  (b* (((unless (s-pattern1-reduce-enabled))
        (mv nil nil nil)))
    (case-match c
      (('list ('c & ''nil c-pp &))
       (b* (((unless (pp-subsetp pp c-pp))
             (mv nil nil nil))
            (compressed (light-compress-s-c `(s '0 ,pp ,c))))
         (case-match compressed
           (('s & ''nil ('list single-c))
            (b* (((mv max min valid) (get-max-min-val single-c)))
              (cond  ((and valid
                           (= max 0)
                           (= min -1))
                      (b* (((mv res coughed-s coughed-pp) (decompress-s-c single-c))
                           ((unless (equal coughed-s ''nil))
                            (mv nil nil nil))
                           (coughed-pp (negate-list-instance coughed-pp)))
                        (mv (list-to-lst coughed-pp)
                            (list (create-times-instance -1 res))
                            t)))
                     (t (mv nil nil nil)))))
           (& (mv nil nil nil)))))
      (& (mv nil nil nil)))))

;; (compress-s-c '(s '0 (list c b a) (list (c '0 'nil (list d c a) 'nil))))
;; (decompress-s-c '(S '0 (LIST B) (LIST (C '0 'NIL (LIST D (times '-1 C) (times '-1 A)) 'NIL))))

(define s-pattern2-reduce ((pp rp-termp)
                           (c rp-termp))
  :returns (mv (reduced-pp-lst rp-term-listp
                               :hyp (and (rp-termp pp)
                                         (rp-termp c)))
               (reducedp booleanp))
  (b* (((unless (and (equal c ''nil)
                     (pattern2-reduce-enabled)
                     (not (has-unflatenned-pp (list-to-lst pp)))))
        (mv nil nil))

       ;;(aggressive (pattern2-aggressive-reduce-enabled))
       )
    (case-match pp
      (('list ''1 pp1 pp2 pp3)
       (b* (((unless (or
                      (equal pp1 ''1)
                      (and (and-subsetp pp2 pp1)
                           (and-subsetp pp3 pp1))))
             (mv nil nil))
            ((mv new-pp-lst success)
             (single-s-to-pp-lst pp1 pp2 pp3))
            ((Unless success)
             (mv nil nil)))
         (mv (pp-sum-merge-aux (list ''1) (negate-lst new-pp-lst)) t)))
      (('list pp1 pp2 pp3)
       (b* (((unless (or
                      (equal pp1 ''1)
                      (and (and-subsetp pp2 pp1)
                           (and-subsetp pp3 pp1))))
             (mv nil nil))
            ((mv new-pp-lst success)
             (single-s-to-pp-lst pp1 pp2 pp3))
            ((Unless success)
             (mv nil nil)))
         (mv new-pp-lst t)))
      ;;(mv `(rp 'bitp (sum-list ,(create-list-instance new-pp-lst))) t)
      (('list pp1 pp2)
       (b* (((unless (or (equal pp1 ''1)
                         (and (and-subsetp pp2 pp1))))
             (mv nil nil))
            ((mv new-pp-lst success)
             (single-s-to-pp-lst pp1 pp2 ''0))
            ((Unless success)
             (mv nil nil)))
         (mv new-pp-lst t)))
      ;;(mv `(rp 'bitp (sum-list ,(create-list-instance new-pp-lst))) t)))
      (& (mv nil nil)))))

(progn
  (encapsulate
    (((pattern3-reduce-enabled) => *))
    (local
     (defun pattern3-reduce-enabled ()
       nil)))

  (defmacro enable-pattern3-reduce (enable)
    (if enable
        `(defattach  pattern3-reduce-enabled return-t)
      `(defattach  pattern3-reduce-enabled return-nil)))

  (enable-pattern3-reduce nil))

(define odd-many-ones (pp-lst)
  (cond ((atom pp-lst)
         nil)
        ((equal (car pp-lst) ''1)
         (not (odd-many-ones (cdr pp-lst))))
        (t nil))
  ///
  (defthm odd-many-ones-implies-consp
    (implies (odd-many-ones pp-lst)
             (and (consp pp-lst)
                  (equal (car pp-lst) ''1)))
    :rule-classes :forward-chaining))

(define s-pattern3-reduce ((pp rp-termp)
                           (c rp-termp))
  :returns (mv (s-res-lst rp-term-listp
                          :hyp (and (rp-termp pp)
                                    (rp-termp c)))
               (pp-res-lst rp-term-listp
                           :hyp (and (rp-termp pp)
                                     (rp-termp c)))
               (reducedp booleanp))
  :prepwork
  ((local
    (defthm lemma1
      (implies (rp-term-listp lst)
               (rp-term-listp (cdr lst))))))

  (b* (((unless (and
                 (pattern3-reduce-enabled)
                 (odd-many-ones (list-to-lst pp))))
        (mv nil nil nil))
       (pp-lst (list-to-lst pp))
       ((unless (odd-many-ones pp-lst))
        (mv nil nil nil))
       (rest-pp-lst (cdr pp-lst))
       (new-pp (create-list-instance rest-pp-lst))
       (single-s `(rp 'bitp (s ',(calculate-s-hash new-pp c)
                               ,new-pp
                               ,c))))
    (mv (list (create-times-instance -1 single-s))
        (list ''1)
        t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c-pattern4-compress


(progn
  (defthm rp-term-listp-intersection-equal
    (implies (and (rp-term-listp x)
                  (rp-term-listp y))
             (rp-term-listp (intersection-equal x y))))

  (defthm rp-term-listp-union-equal
    (implies (and (rp-term-listp x)
                  (rp-term-listp y))
             (rp-term-listp (union-equal x y))))

  (defthm rp-term-listp-set-difference-equal
    (implies (and (rp-term-listp x)
                  ;; (rp-term-listp y)
                  )
             (rp-term-listp (set-difference-equal x y)))))


(define create-and-times-list-instance ((lst rp-term-listp)
                                        (s/c rp-termp))
  :returns (ins rp-termp
                :hyp (and (rp-term-listp lst)
                          (rp-termp s/c)))
  :prepwork
  ((define e-lsts-have-common? ((e-lst1 rp-term-listp)
                                (e-lst2 rp-term-listp))
     :measure (+ (len e-lst1) (len e-lst2))
     (if (or (atom e-lst1)
             (atom e-lst2))
         nil
       (b* ((e1 (car e-lst1))
            (e2 (car e-lst2))
            ((when (equal e1 e2)) t))
         (if (lexorder2- e1 e2)
             (e-lsts-have-common? (cdr e-lst1) e-lst2)
           (e-lsts-have-common? e-lst1 (cdr e-lst2))))))

   (define lists-have-common? ((lst1 true-listp)
                               (lst2 true-listp))
     (if (atom lst1)
         nil
       (or (member-equal (car lst1) lst2)
           (lists-have-common? (cdr lst1) lst2))))

   (define simplify-pp-lst-from-e-lst ((pp-lst rp-term-listp)
                                       (e-lst rp-term-listp))
     :returns (mv (new-pp-lst rp-term-listp
                              :hyp (rp-term-listp pp-lst))
                  changed)
     (if (atom pp-lst)
         (mv nil nil)
       (b* ((cur (car pp-lst))
            ((mv e-lst2 s/c has-s/c valid)
             (case-match* cur
                          (('and-list & ('list . x))
                           (mv x nil nil t))
                          (('and-times-list & ('list . x) s/c)
                           (mv x s/c t t))
                          (('logbit$inline & &)
                           (mv (list cur) nil nil t))
                          (& (mv nil nil nil nil))))
            ((unless valid) (mv pp-lst nil))
            ((mv rest-pp-lst rest-changed)
             (simplify-pp-lst-from-e-lst (cdr pp-lst) e-lst))
            (has-common (e-lsts-have-common? e-lst e-lst2))
            ((unless has-common)
             (if rest-changed
                 (mv (cons cur rest-pp-lst) t)
               (mv pp-lst nil)))
            (e-lst2 (set-difference-equal e-lst2 e-lst))
            (new-cur (cond ((not has-s/c)
                            (create-and-list-instance e-lst2))
                           (t `(and-times-list ',(and-list-hash (cons s/c e-lst2))
                                               (list . ,e-lst2)
                                               ,s/c)))))
         (mv (cons new-cur rest-pp-lst) t))))

   (define collect-e-lst-from-pp-lst ((pp-lst rp-term-listp))
     :returns (collected rp-term-listp :hyp (rp-term-listp pp-lst))
     :verify-guards :after-returns
     (if (atom pp-lst)
         nil
       (b* ((rest (collect-e-lst-from-pp-lst (cdr pp-lst)))
            (cur (car pp-lst))
            (e-lst
             (case-match* cur
                          (('and-list & ('list . x))
                           x)
                          (('and-times-list & ('list . x) &)
                           x)
                          (('logbit$inline & &)
                           (list cur))
                          (& nil))))
         (union-equal e-lst rest)))
     ///
     (memoize 'collect-e-lst-from-pp-lst :recursive nil))

   (defines collect-e-lst-from-s/c
     (define collect-e-lst-from-s/c ((s/c rp-termp)
                                     &key
                                     ((limit natp) 'limit))
       :verify-guards nil
       :returns (e-lst)
       :measure (nfix limit)
       :no-function t
       (if (zp limit)
           nil
         (let ((limit (1- limit)))
           (b* ((x (ex-from-rp/times s/c)))
             (case-match*
              x
              (('c & ''nil pp c)
               (b* ((pp-lst (list-to-lst pp))
                    (c-lst (list-to-lst c))
                    (rest (collect-e-lst-from-s/c-lst c-lst)))
                 (union-equal rest
                              (collect-e-lst-from-pp-lst pp-lst))))
              (& nil))))))
     (define collect-e-lst-from-s/c-lst ((s/c-lst rp-term-listp)
                                         &key
                                         ((limit natp) 'limit))
       :measure (nfix limit)
       :no-function t
       :returns (e-lst)
       (if (zp limit)
           nil
         (let ((limit (1- limit)))
           (if (atom s/c-lst)
               nil
             (union-equal (collect-e-lst-from-s/c (car s/c-lst))
                          (collect-e-lst-from-s/c-lst (cdr s/c-lst)))))))
     ///
     (defret-mutual return-type-of-<fn>
       (defret return-type-of-<fn>
         (rp-term-listp e-lst)
         :hyp (rp-termp s/c)
         :fn collect-e-lst-from-s/c)
       (defret return-type-of-<fn>
         (rp-term-listp e-lst)
         :hyp (rp-term-listp s/c-lst)
         :fn collect-e-lst-from-s/c-lst))

     (verify-guards collect-e-lst-from-s/c-fn
       :guard-debug t)

     (memoize-partial ((collect-e-lst-from-s/c* collect-e-lst-from-s/c-fn)
                       (collect-e-lst-from-s/c-lst*
                        collect-e-lst-from-s/c-lst-fn :condition 'nil))))

   (defines simplify-s/c-from-e-lst
     :flag-local nil
     (define simplify-s/c-from-e-lst-main ((s/c rp-termp)
                                           (e-lst rp-term-listp)
                                           &key
                                           ((limit natp) '*big-number*))
       :measure (nfix limit)
       :returns (mv (res rp-termp :hyp (rp-termp s/c))
                    changed)
       (b* (((when (zp limit)) (mv s/c nil))
            (collected-e-lst (collect-e-lst-from-s/c* s/c))
            ((unless (lists-have-common? e-lst collected-e-lst))
             (mv s/c nil)))
         (simplify-s/c-from-e-lst s/c e-lst :limit (1- limit))))

     (define simplify-s/c-from-e-lst ((s/c rp-termp)
                                      (e-lst rp-term-listp)
                                      &key
                                      ((limit natp) '*big-number*))
       :measure (nfix limit)
       :returns (mv (res rp-termp :hyp (rp-termp s/c))
                    changed)
       :verify-guards nil
       (b* (((when (zp limit)) (mv s/c nil))
            (s/c-orig s/c)
            (s/c (ex-from-rp$ s/c)))
         (case-match s/c
           (('c & ''nil pp c)
            (b* ((pp-lst (list-to-lst pp))
                 ((mv pp-lst changed1)
                  (simplify-pp-lst-from-e-lst pp-lst e-lst))
                 (c-lst (list-to-lst c))
                 ((mv c-lst changed2)
                  (simplify-s/c-list-from-e-lst c-lst e-lst :limit (1- limit)))
                 ((unless (or changed1 changed2))
                  (mv s/c-orig nil))
                 (pp-lst (if (or (not changed1)
                                 (pp-lst-orderedp pp-lst))
                             pp-lst
                           (pp-sum-sort-lst pp-lst)))
                 (pp (create-list-instance pp-lst))
                 (c (create-list-instance c-lst))
                 (hash-code (calculate-c-hash ''nil pp c))
                 ;; todo be careful when it clears to 0.
                 (res-c `(c ',hash-code 'nil ,pp ,c)))
              (mv res-c t)))
           (& (mv s/c-orig nil)))))
     (define simplify-s/c-list-from-e-lst ((s/c-lst rp-term-listp)
                                           (e-lst rp-term-listp)
                                           &key
                                           ((limit natp) '*big-number*))
       :measure (nfix limit)
       :returns (mv (res-lst rp-term-listp
                             :hyp (rp-term-listp s/c-lst))
                    changed)
       (if (atom s/c-lst)
           (mv nil nil)
         (b* (((when (zp limit)) (mv s/c-lst nil))
              ((mv cur changed1)
               (simplify-s/c-from-e-lst-main (car s/c-lst) e-lst :limit (1- limit)))
              ((mv rest changed2)
               (simplify-s/c-list-from-e-lst (cdr s/c-lst) e-lst :limit (1- limit))))
           (if (or changed1 changed2)
               (mv (cons cur rest) t)
             (mv s/c-lst nil)))))
     ///
     (verify-guards simplify-s/c-from-e-lst-fn)))

  (cond
   ((and*-exec (atom lst)
               (or*-exec (has-bitp-rp s/c)
                         (single-s-p (ex-from-rp s/c))
                         (single-c-p (ex-from-rp s/c))))
    s/c)
   ((equal s/c ''1)
    (create-and-list-instance lst))
   (t
    (b* ((lst (sort-and$-list lst (len lst)))
         ((mv new-s/c &)
          (simplify-s/c-from-e-lst-main s/c lst))
         ((when (equal new-s/c ''1))
          (create-and-list-instance lst))
         (hash-code (and-list-hash (cons new-s/c lst)))
         ;; (- (and (equal hash-code '23254)
         ;;         (raise "here ((e-lst ~p0)
         ;;                     (s/c ~p1)
         ;;                     (new-s/c ~p2))~%"
         ;;                lst s/c new-s/c)))
         )
      `(and-times-list ',hash-code
                       (list . ,lst)
                       ,new-s/c)))))

;; collect common elements in pp-lst and pull it out from a c term's arguments
;; into a (times pp-common new-c) way.
(define c-pattern4-compress ((s-lst rp-term-listp)
                             (pp-lst rp-term-listp)
                             (c-lst rp-term-listp))
  :returns (mv (res-pp-lst rp-term-listp
                           :hyp (rp-term-listp pp-lst)
                           :hints (("Goal"
                                    :in-theory (e/d (rp-term-listp) ()))))
               valid)
  :prepwork
  ((progn
     (encapsulate
       (((c-pattern4-compress-enabled) => *))
       (local
        (defun c-pattern4-compress-enabled ()
          nil)))

     (defmacro enable-c-pattern4-compress (enable)
       (if enable
           `(defattach  c-pattern4-compress-enabled return-t)
         `(defattach  c-pattern4-compress-enabled return-nil)))

     (enable-c-pattern4-compress nil))

   (define collect-common-e-lst ((pp-lst rp-term-listp))
     :returns (commons rp-term-listp
                       :hyp (rp-term-listp pp-lst))
     :verify-guards :after-returns
     (b* (((when (atom pp-lst))
           nil)
          (cur (car pp-lst))
          #|((when (equal cur ''1))
          (collect-common-e-lst (cdr pp-lst)))|#
          ((mv cur valid) (case-match cur
                            (('and-list & ('list . x))
                             (mv x t))
                            (('and-times-list & ('list . x) &)
                             (mv x t))
                            (('logbit$inline & &)
                             (mv (list cur) t))
                            (& (mv nil nil))))
          ((Unless valid) nil)
          ((when (atom (cdr pp-lst))) cur))
       (intersection-equal (collect-common-e-lst (cdr pp-lst))
                           cur)))

   (define remove-e-lst-from-e-lst ((e-lst rp-term-listp)
                                    (to-remove-e-lst rp-term-listp))
     :returns (mv (res-e-lst rp-term-listp :hyp (rp-term-listp e-lst))
                  (valid))

     (b* (((when (atom e-lst)) (mv nil (atom to-remove-e-lst)))
          ((when (atom to-remove-e-lst)) (mv e-lst t))
          (f1 (car e-lst))
          (f2 (car to-remove-e-lst))
          ((when (equal f1 f2)) (remove-e-lst-from-e-lst (cdr e-lst)
                                                         (cdr to-remove-e-lst)))
          ((mv rest valid)
           (remove-e-lst-from-e-lst (cdr e-lst)
                                    to-remove-e-lst))
          ((unless valid) (mv nil nil)))
       (mv (cons f1 rest) t)))

   (define remove-e-lst-from-pp-lst ((pp-lst rp-term-listp)
                                     (to-remove-e-lst rp-term-listp))
     :returns (mv (s-lst rp-term-listp :hyp (and (rp-term-listp pp-lst)
                                                 (rp-term-listp to-remove-e-lst)))
                  (res-pp-lst rp-term-listp :hyp (and (rp-term-listp pp-lst)
                                                      (rp-term-listp to-remove-e-lst)))
                  (c-lst rp-term-listp :hyp (and (rp-term-listp pp-lst)
                                                 (rp-term-listp to-remove-e-lst)))
                  (valid))
     (if (atom pp-lst)
         (mv nil nil nil t)
       (b* ((cur (car pp-lst))
            ((mv cur s/c has-s/c valid)
             (case-match cur
               (('and-list & ('list . x))
                (mv x nil nil t))
               (('and-times-list & ('list . x) s/c)
                (mv x s/c t t))
               (('logbit$inline & &)
                (mv (list cur) nil nil t))
               (& (mv nil nil nil nil))))
            ((unless valid) (mv nil nil nil nil))
            ((mv rest-s-lst rest-pp-lst rest-c-lst valid)
             (remove-e-lst-from-pp-lst (cdr pp-lst) to-remove-e-lst))
            ((unless valid) (mv nil nil nil nil))
            ((mv cur valid) (remove-e-lst-from-e-lst cur to-remove-e-lst)))
         (cond ((not valid) (mv nil nil nil nil))
               ((atom cur)
                (if has-s/c
                    (cond ((single-c-p (ex-from-rp/times s/c))
                           (mv rest-s-lst rest-pp-lst
                               (cons s/c rest-c-lst) t))
                          ((single-s-p (ex-from-rp/times s/c))
                           (mv (cons s/c rest-s-lst) rest-pp-lst
                               rest-c-lst t))
                          (t (mv rest-s-lst (cons s/c rest-pp-lst)
                                 rest-c-lst t)))
                  (mv rest-s-lst (cons ''1 rest-pp-lst) rest-c-lst t)))
               (t (if has-s/c
                      (mv rest-s-lst (cons (create-and-times-list-instance cur s/c)
                                           rest-pp-lst)
                          rest-c-lst
                          t)
                    (mv rest-s-lst (cons (create-and-list-instance cur)
                                         rest-pp-lst)
                        rest-c-lst
                        t)))))))

   (define break-down-two-arg-c ((c-in rp-termp))
     :returns (mv (e-lst)
                  (res-c))
     :measure (cons-count c-in)
     :hints (("Goal"
              :in-theory (e/d (measure-lemmas) ())))
     :prepwork ((local
                 (in-theory (disable
                             (:e tau-system)
                             (:type-prescription acl2::binary-and*)
                             ;;(:forward-chaining acl2::and*-forward)
                             (:type-prescription rp-termp)
                             (:rewrite default-cdr)
                             (:rewrite acl2::and*-rem-second)
                             (:rewrite is-if-rp-termp)
                             (:rewrite acl2::and*-nil-second)
                             (:rewrite default-car)))))
     (b* ((x (ex-from-rp c-in))
          ((unless (single-c-p x))
           (mv nil c-in)))
       (case-match* x
                    (('c & ''nil ('list a b) ''nil)
                     (b* (((mv a-e-lst a-has-s/c a-valid)
                           (case-match* a
                                        (('and-list & ('list . lst))
                                         (mv lst nil t))
                                        (('logbit$inline & &)
                                         (mv (list a) nil t))
                                        (''1
                                         (mv (list ''1) nil t))
                                        ;; extra cases adds up!!!
                                        (('and-times-list & ('list . lst) s/c)
                                         (mv lst s/c (is-c-bitp-traverse s/c)))
                                        (& (mv nil nil nil)
                                           #|(if (has-bitp-rp a)
                                           (mv (list a) nil t)
                                           (mv nil nil nil))|#)))
                          ((unless a-valid)
                           (mv nil c-in))
                          ((mv b-e-lst b-has-s/c b-valid)
                           (case-match* b
                                        (('and-list & ('list . lst))
                                         (mv lst nil t))
                                        (('logbit$inline & &)
                                         (mv (list b) nil t))
                                        (('and-times-list & ('list . lst) s/c)
                                         (mv lst s/c (or*-exec
                                                      (has-bitp-rp s/c)
                                                      (is-c-bitp-traverse s/c))))
                                        (''1
                                         (mv (list ''1) nil t))
                                        (& (mv nil nil nil)
                                           #|(if (has-bitp-rp b)
                                           (mv (list b) nil t)
                                           (mv nil nil nil))|#)))
                          ((unless b-valid)
                           (mv nil c-in))
                          ((when (and*-exec b-has-s/c a-has-s/c))
                           (mv nil c-in))
                          (e-lst (merge-sorted-and$-lists a-e-lst b-e-lst))
                          (s/c (or*-exec a-has-s/c b-has-s/c ''1)))
                       (mv e-lst s/c)))
                    (('c & ''nil ('list a) ('list b))
                     (b* (((unless (and*-exec (or*-exec (has-bitp-rp a)
                                                        (and-list-p a)
                                                        (logbit-p a)
                                                        (equal a ''1))
                                              (or*-exec (has-bitp-rp b)
                                                        (is-c-bitp-traverse b))))
                           (mv nil c-in))
                          ((mv rest-e-lst rest-c)
                           (break-down-two-arg-c b)))
                       (mv (cons a rest-e-lst) rest-c)))
                    (& (mv nil c-in))))
     ///
     (defret rp-termp-o-<fn>
       (and (rp-termp res-c)
            (rp-term-listp e-lst))
       :hyp (rp-termp c-in)))
   )

  (b* (((unless (and (not s-lst) (not c-lst))) (mv nil nil))
       ((unless (c-pattern4-compress-enabled)) (mv nil nil))
       ((unless (> (len pp-lst) 1)) (mv nil nil))
       (pp-commons (collect-common-e-lst pp-lst))
       ((unless pp-commons) (mv nil nil))
       (pp-commons (sort-and$-list pp-commons (len pp-commons)))
       ((mv s-lst pp-lst c-lst valid) (remove-e-lst-from-pp-lst pp-lst pp-commons))
       ((unless valid) (mv nil nil))
       ((when s-lst) (mv nil nil))
       ((when (and*-exec (not* pp-lst) (not* c-lst)))
        (mv (list ''0) t))

       #|((when (equal (+ (len pp-lst) (len c-lst)) 2))
       (mv (list (create-and-list-instance ;
       (merge-sorted-and$-lists ;
       (merge-sorted-and$-lists pp-lst c-lst) ;
       pp-commons))) ;
       t))|#

       (pp-lst (if (pp-lst-orderedp pp-lst)
                   pp-lst
                 (pp-sum-sort-lst pp-lst)))

       (pp (create-list-instance pp-lst))
       (c (create-list-instance c-lst))
       (hash-code (calculate-c-hash ''nil pp c))

       (res-c `(c ',hash-code 'nil ,pp ,c))

       #|(- (and (equal hash-code '(2 . 5315388))
       (raise "here ((s-lst ~p0)
       (pp-lst ~p1)
       (c-lst ~p2))~%"
       s-lst pp-lst c-lst)))|#


       ((mv more-pp-commons res-c)
        (break-down-two-arg-c res-c))
       (more-pp-commons (sort-and$-list more-pp-commons (len more-pp-commons)))
       (pp-commons (merge-sorted-and$-lists pp-commons more-pp-commons)))
    (mv (list (create-and-times-list-instance pp-commons res-c)) t)))



    ;;    ((mv pp-commons pp-lst c-lst)
    ;;     (b* (((unless (and (atom c-lst)
    ;;                        (equal (len pp-lst) 2)))
    ;;           (mv pp-commons pp-lst c-lst)))
    ;;       (mv (merge-sorted-and$-lists (sort-and$-list pp-lst 2)
    ;;                                    pp-commons)
    ;;           nil nil)))

    ;;    (pp (create-list-instance pp-lst))
    ;;    (c (create-list-instance c-lst))
    ;;    (hash-code (calculate-c-hash ''nil pp c))


    ;;    #|(- (and (equal (len c-lst) 1)
    ;;            (equal (second (car c-lst)) ''(257 . 360468381))
    ;;            (raise "here")))|#

    ;;    (res-c `(rp 'bitp (rp 'natp (c ',hash-code 'nil ,pp ,c))))
    ;;    (res (merge-sorted-and$-lists (list res-c) pp-commons))
    ;;    (res (create-and-list-instance res))

    ;;    ;;(- (cw "res: ~p0 ~%" res))
    ;;    )
    ;; (mv (list res) t))))

#|(skip-proofs
 (define c-instance-to-e-lst (x)
  :returns (mv e-lst res-c)
  (b* ((x-orig x)
       (x (ex-from-rp x)))
    (case-match x
      (('c & ''nil ('list a) ('list b))
       (b* (((mv rest-e-lst c)
             (c-instance-to-e-lst b)))
         (mv (merge-sorted-and$-lists (list a)
                                      rest-e-lst)
             c)))
      (('c & ''nil ('list a b) ''nil)
       (b* ()
         (mv (sort-and$-list (list a b) 2)
             ''1)))
      (& (mv nil x-orig))))))|#


(define create-c-instance ((s-lst rp-term-listp)
                           (pp-lst rp-term-listp)
                           (c-lst rp-term-listp)
                           ;;(s-coughed-lst rp-term-listp)
                           ;;(pp-coughed-lst rp-term-listp)
                           )
;:inline t
  :returns (mv (res-s-lst rp-term-listp
                          :hyp (and (rp-term-listp s-lst)
                                    (rp-term-listp pp-lst)
                                    (rp-term-listp c-lst)
                                    ))
               (res-pp-lst rp-term-listp
                           :hyp (and (rp-term-listp s-lst)
                                     (rp-term-listp pp-lst)
                                     (rp-term-listp c-lst)))
               (res-c-lst rp-term-listp
                          :hyp (and (rp-term-listp s-lst)
                                    (rp-term-listp pp-lst)
                                    (rp-term-listp c-lst))))
  (b* ((reducedp (c-pattern0-reduce s-lst pp-lst c-lst))
       ((when reducedp)
        (mv nil nil nil))
       ((mv s-lst pp-lst c-lst)
        (c-pattern1-reduce s-lst pp-lst c-lst))
       ((mv reduced-pp-lst reducedp)
        (c-pattern2-reduce s-lst pp-lst c-lst))
       ((when reducedp)
        (mv nil reduced-pp-lst nil))
       ;; pattern4 comes after because pattern2 can do a better reduction
       ;; first.
       ((mv reduced-pp-lst reducedp)
        (c-pattern4-compress s-lst pp-lst c-lst))
       ((when reducedp)
        (mv nil reduced-pp-lst nil)))
    (cond ((or (and (equal c-lst nil)
                    (equal s-lst nil)
                    (case-match pp-lst
                      ((('and-list & &)) t)))
               (and (equal c-lst nil)
                    (equal pp-lst nil)
                    (case-match s-lst
                      ((('s & & &)) t)
                      ((('rp ''bitp &)) t)))
               (and (equal s-lst nil)
                    (equal pp-lst nil)
                    (case-match c-lst
                      ((single-c)
                       (or (has-bitp-rp single-c)
                           (is-c-bitp-traverse single-c))))))
           (mv nil nil nil))
          ((and (quoted-listp s-lst)
                (quoted-listp pp-lst)
                (quoted-listp c-lst))
           (b* ((res
                 `',(c 0
                       (unquote-all s-lst)
                       (unquote-all pp-lst)
                       (unquote-all c-lst))))
             (if (equal res ''0)
                 (mv nil nil nil)
               (mv nil (list res) nil))))
          (t
           (b* ((s (create-list-instance s-lst))
                (pp (create-list-instance pp-lst))
                (c (create-list-instance c-lst))
                (hash-code (calculate-c-hash s pp c))

                (res `(c ',hash-code ,s ,pp ,c))

                ;; (- (and (equal hash-code '(2 . 6288828))
                ;;         (raise "s-lst: ~p0. pp-lst ~p1, c-lst ~p2 ~%" s-lst
                ;;         pp-lst c-lst)))

                ((mv max-val min-val valid)
                 (if (natp (maybe-bitp-precheck res)) ;; minimize the calls made to get-max-min-val
                     (get-max-min-val res)
                   (mv 0 0 nil)))
                ((when (and valid
                            (equal max-val 1)
                            (equal min-val 0)))
                 (mv nil nil (list `(rp 'bitp ,res))))

                ((when (and valid
                            (equal max-val 0)
                            (equal min-val 0)))
                 (mv nil nil nil))

                )
             (mv nil nil (list res)))))))

;;(memoize 'get-max-min-val :condition '(single-c-p (ex-from-rp-loose term)))

(define create-s-instance ((pp rp-termp)
                           (c rp-termp))
  ;;:inline t
  :returns (mv (s-res-lst rp-term-listp
                          :hyp (and (rp-termp pp)
                                    (rp-termp c)))
               (pp-res-lst rp-term-listp
                           :hyp (and (rp-termp pp)
                                     (rp-termp c)))
               (c-res-lst rp-term-listp
                          :hyp (and (rp-termp pp)
                                    (rp-termp c))))
  (b* ((reducedp (s-pattern0-reduce pp c))
       ((when reducedp)
        (mv nil nil nil))
       ((mv reduced-pp-lst reduced-c-lst reducedp)
        (s-pattern1-reduce pp c))
       ((when reducedp)
        (mv nil reduced-pp-lst reduced-c-lst))
       ((mv reduced-pp-lst reducedp)
        (s-pattern2-reduce pp c))
       ((when reducedp)
        (mv nil reduced-pp-lst nil))
       ((mv reduced-s-lst reduced-pp-lst reducedp)
        (s-pattern3-reduce pp c))
       ((when reducedp)
        (mv reduced-s-lst reduced-pp-lst nil))
       )
    (cond ((and (quotep pp)
                (quotep c)
                (consp (cdr pp))
                (consp (cdr c)))
           (b* ((res `',(s 0 (unquote pp) (unquote c))))
             (if (equal res ''0)
                 (mv nil nil nil)
               (mv nil (list res) nil))))
          ((and (all-quoted-list pp)
                (all-quoted-list c))
           (mv nil
               (list `',(s 0
                           (unquote-all (list-to-lst pp))
                           (unquote-all (list-to-lst c))))
               nil))
          ((and (equal c ''nil)
                (case-match pp (('list e)
                                (b* ((e-ex (ex-from-rp$ e)))
                                  (or* (and-list-p e-ex)
                                       (logbit-p e-ex)
                                       (binary-fnc-p e-ex)
                                       (has-bitp-rp e))))))
           (mv nil (list (cadr pp)) nil))
          ((and (equal pp ''nil)
                (case-match c
                  (('list single-c)
                   (or (has-bitp-rp single-c)))))
           (mv nil nil (list (cadr c))))
          ((and (equal pp ''nil)
                (case-match c
                  (('list single-c)
                   (is-c-bitp-traverse single-c))))
           (mv nil nil (list `(rp 'bitp ,(cadr c)))))
          (t
           (mv (list `(rp 'bitp (s ',(calculate-s-hash pp c) ,pp ,c)))
               nil
               nil)))))

#|(define c-sum-merge-main ((c1-lst rp-term-listp)
(c2-lst rp-term-listp)
&key
(auto-swap 't)
(clean-c1-lst 'nil)
(cough-c-lst 't)
(clean-args-for-s 'nil))
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
(rp-term-listp c2-lst)))
)
(b* ((merged-c-lst (if clean-args-for-s
(sum-merge-lst-for-s c1-lst c2-lst)
(s-sum-merge-aux c1-lst c2-lst)))
#|(- (or (s-sum-ordered-listp c1-lst)
(hard-error 'c-sum-merge-main
"c1-lst is not ordered. ~p0 ~%"
(list (cons #\0 c1-lst)))))
(- (or (s-sum-ordered-listp c2-lst)
(hard-error 'c-sum-merge-main
"c2-lst is not ordered. ~p0 ~%"
(list (cons #\0 c2-lst)))))
(- (or (s-sum-ordered-listp merged-c-lst)
(hard-error 'c-sum-merge-main
"merged-c-lst is not ordered. ~p0. c1-lst: ~p1
c2-lst: ~p2 ~%"
(list (cons #\0 merged-c-lst)
(cons #\1 c1-lst)
(cons #\2 c2-lst)))))||#)
(mv ''nil nil merged-c-lst nil)))|#

(define c-of-s-fix-lst ((arg-s-lst rp-term-listp)
                        (arg-pp-lst rp-term-listp)
                        (arg-c-lst rp-term-listp)
                        (to-be-coughed-c-lst rp-term-listp))
  :returns (mv (res-pp-lst rp-term-listp
                           :hyp (and (rp-term-listp arg-s-lst)
                                     (rp-term-listp arg-pp-lst)
                                     (rp-term-listp arg-c-lst)))
               (res-c-lst rp-term-listp
                          :hyp (and (rp-term-listp arg-s-lst)
                                    (rp-term-listp arg-pp-lst)
                                    (rp-term-listp arg-c-lst)))
               (to-be-coughed-s-lst rp-term-listp
                                    :hyp (and (rp-term-listp arg-s-lst)
                                              (rp-term-listp arg-pp-lst)
                                              (rp-term-listp arg-c-lst)))
               (to-be-coughed-pp-lst rp-term-listp
                                     :hyp (and (rp-term-listp arg-s-lst)
                                               (rp-term-listp arg-pp-lst)
                                               (rp-term-listp arg-c-lst)))
               (res-coughed-c-lst rp-term-listp
                                  :hyp (and (rp-term-listp arg-s-lst)
                                            (rp-term-listp arg-pp-lst)
                                            (rp-term-listp arg-c-lst)
                                            (rp-term-listp to-be-coughed-c-lst))))
  :verify-guards :after-returns
  (b* (((when (atom arg-s-lst))
        (mv arg-pp-lst arg-c-lst nil nil to-be-coughed-c-lst))
       ((mv arg-pp-lst arg-c-lst to-be-coughed-s-lst to-be-coughed-pp-lst to-be-coughed-c-lst)
        (c-of-s-fix-lst (cdr arg-s-lst)
                        arg-pp-lst
                        arg-c-lst
                        to-be-coughed-c-lst))
       (cur-s (car arg-s-lst))
       ((mv coef cur-s) (get-pp-and-coef cur-s))
       ((when (evenp coef))
        (b* ((to-be-coughed-s-lst (s-sum-merge-aux to-be-coughed-s-lst
                                                   (list (create-times-instance (/ coef 2) cur-s)))))
          (mv arg-pp-lst arg-c-lst to-be-coughed-s-lst to-be-coughed-pp-lst to-be-coughed-c-lst)))
       (cur-s-w/sc cur-s)
       (cur-s (ex-from-rp$ cur-s))

       )
    (case-match cur-s
      (('s & s-arg-pp s-arg-c)
       (b* (((mv & to-be-coughed-pp-lst2 to-be-coughed-c-lst2)
             (create-c-instance nil
                                (list-to-lst s-arg-pp)
                                (list-to-lst s-arg-c)))

            ;;(to-be-coughed-c-lst2 (add-c-rp-bitp to-be-coughed-c-lst2))

            (sign (if (< coef 0) -1 1))
            ;;(sign 1)

            (to-be-coughed-c-lst2 (append-with-times (- sign) to-be-coughed-c-lst2 nil))
            (to-be-coughed-pp-lst2 (append-with-times (- sign) to-be-coughed-pp-lst2 nil))
            (to-be-coughed-s-lst2 (cons-with-times (/ (+ coef (- sign)) 2) cur-s-w/sc nil))

            (to-be-coughed-pp-lst (pp-sum-merge-aux to-be-coughed-pp-lst
                                                    to-be-coughed-pp-lst2))
            (to-be-coughed-c-lst (s-sum-merge-aux to-be-coughed-c-lst
                                                  to-be-coughed-c-lst2))
            (to-be-coughed-s-lst (s-sum-merge-aux to-be-coughed-s-lst
                                                  to-be-coughed-s-lst2))

            (arg-pp-lst (pp-sum-merge-aux arg-pp-lst
                                          (append-with-times sign (list-to-lst s-arg-pp) nil)))
            (arg-c-lst (s-sum-merge-aux arg-c-lst
                                        (append-with-times sign (list-to-lst s-arg-c) nil))))
         (mv arg-pp-lst arg-c-lst to-be-coughed-s-lst to-be-coughed-pp-lst to-be-coughed-c-lst)))
      (''0
       (mv arg-pp-lst arg-c-lst to-be-coughed-s-lst to-be-coughed-pp-lst to-be-coughed-c-lst))
      (& (progn$
          (hard-error 'c-of-s-fix-lst
                      "Unexpected single-s instance: ~p0 ~%"
                      (list (cons #\0 cur-s)))
          (mv (cons (car arg-s-lst) arg-pp-lst) arg-c-lst to-be-coughed-s-lst to-be-coughed-pp-lst to-be-coughed-c-lst))))))

;;;;;;;

(define c-pattern3-reduce ((s-lst rp-term-listp)
                           (pp-lst rp-term-listp)
                           (c-lst rp-term-listp)
                           (s-coughed-lst rp-term-listp)
                           (pp-coughed-lst rp-term-listp)
                           (c-coughed-lst rp-term-listp))
  :verify-guards t
  :returns (mv (res-s-lst rp-term-listp
                          :hyp (and (rp-term-listp s-lst)
                                    (rp-term-listp pp-lst)
                                    (rp-term-listp c-lst)
                                    (rp-term-listp s-coughed-lst)
                                    (rp-term-listp pp-coughed-lst)
                                    (rp-term-listp c-coughed-lst)
                                    ))
               (res-pp-lst rp-term-listp
                           :hyp (and (rp-term-listp s-lst)
                                     (rp-term-listp pp-lst)
                                     (rp-term-listp c-lst)
                                     (rp-term-listp s-coughed-lst)
                                     (rp-term-listp pp-coughed-lst)
                                     (rp-term-listp c-coughed-lst)
                                     ))
               (res-c-lst rp-term-listp
                          :hyp (and (rp-term-listp s-lst)
                                    (rp-term-listp pp-lst)
                                    (rp-term-listp c-lst)
                                    (rp-term-listp s-coughed-lst)
                                    (rp-term-listp pp-coughed-lst)
                                    (rp-term-listp c-coughed-lst)
                                    ))
               (res-s-coughed-lst rp-term-listp
                                  :hyp (and (rp-term-listp s-lst)
                                            (rp-term-listp pp-lst)
                                            (rp-term-listp c-lst)
                                            (rp-term-listp s-coughed-lst)
                                            (rp-term-listp pp-coughed-lst)
                                            (rp-term-listp c-coughed-lst)
                                            ))
               (res-pp-coughed-lst rp-term-listp
                                   :hyp (and (rp-term-listp s-lst)
                                             (rp-term-listp pp-lst)
                                             (rp-term-listp c-lst)
                                             (rp-term-listp s-coughed-lst)
                                             (rp-term-listp pp-coughed-lst)
                                             (rp-term-listp c-coughed-lst)
                                             ))
               (res-c-coughed-lst rp-term-listp
                                  :hyp (and (rp-term-listp s-lst)
                                            (rp-term-listp pp-lst)
                                            (rp-term-listp c-lst)
                                            (rp-term-listp s-coughed-lst)
                                            (rp-term-listp pp-coughed-lst)
                                            (rp-term-listp c-coughed-lst)
                                            )))

  (b* (((when (or (not (pattern3-reduce-enabled))
                  (not (odd-many-ones pp-lst))))
        (mv s-lst pp-lst c-lst s-coughed-lst pp-coughed-lst c-coughed-lst))

       (res-s-lst s-lst)
       (res-pp-lst (cdr pp-lst))
       (res-c-lst c-lst)

       ((mv new-pp-lst new-c-lst)
        (s-of-s-fix-lst s-lst
                        (cdr pp-lst)
                        c-lst))

       #| (- (and (not-well-merged-c-lst new-c-lst)
       (hard-error 'c-pattern3-reduce
       "Mergable c-lst ~p0 ~%"
       (list (cons #\0 new-c-lst)))))||#

       ((mv res-s-lst2 res-pp-lst2 res-c-lst2)
        (create-s-instance (create-list-instance new-pp-lst)
                           (create-list-instance new-c-lst)))

       (res-s-coughed-lst (s-sum-merge-aux s-coughed-lst res-s-lst2))
       (res-pp-coughed-lst (pp-sum-merge-aux pp-coughed-lst res-pp-lst2))
       (res-c-coughed-lst (s-sum-merge-aux c-coughed-lst res-c-lst2)))
    (mv res-s-lst res-pp-lst res-c-lst
        res-s-coughed-lst res-pp-coughed-lst res-c-coughed-lst)))

;;;;;;;;;

(define quote-all (lst)
  :returns (res rp-term-listp)
  (if (atom lst)
      nil
    (cons (list 'quote (car lst))
          (quote-all (cdr lst)))))

;;;;;;;;;;;;;;;;;;;
(defsection recollect-pp-lst-to-sc-main

  (define recollectable-pp-p ((pp))
    (b* ((pp (ex-from-rp/times pp)))
      (case-match pp
        (('and-list & ('list a1 a2 a3 a4))
         (b* ((a1 (ex-from-rp a1))
              (a2 (ex-from-rp a2))
              (a3 (ex-from-rp a3))
              (a4 (ex-from-rp a4))
              (a1 (ex-from-rp (case-match a1 (('logbit$inline & x) x) (& a1))))
              (a2 (ex-from-rp (case-match a2 (('logbit$inline & x) x) (& a2))))
              (a3 (ex-from-rp (case-match a3 (('logbit$inline & x) x) (& a3))))
              (a4 (ex-from-rp (case-match a4 (('logbit$inline & x) x) (& a4)))))
           (or (and (equal a1 a2)
                    (equal a1 a3)
                    (not (equal a1 a4))
                    1)
               (and (equal a4 a2)
                    (equal a4 a3)
                    (not (equal a1 a4))
                    2)))))))

  (define recollect-pp ((pp rp-termp))
    :guard (recollectable-pp-p pp)
    :prepwork ((local
                (defthm is-rp-of-rp-bitp
                  (is-rp `(rp 'bitp ,x))
                  :hints (("Goal"
                           :in-theory (e/d (is-rp) ()))))))
    :returns (mv  (res-pp-lst rp-term-listp :hyp (rp-termp pp))
                  (c rp-termp :hyp (rp-termp pp)))
    (b* ((p (recollectable-pp-p pp))
         (pp-orig pp)
         ((mv coef pp) (get-pp-and-coef pp))
         (pp (ex-from-rp pp))
         ((mv pp1 pp2 pp3 pp4 pp5 pp6 valid)
          (case-match pp
            (('and-list & ('list a1 a2 a3 a4))
             (cond ((equal p 1)
                    (mv (create-and-list-instance (list a1 a4))
                        (create-and-list-instance (list a2 a4))
                        (create-and-list-instance (list a3 a4))
                        (create-and-list-instance (list a1 a2 a4))
                        (create-and-list-instance (list a1 a3 a4))
                        (create-and-list-instance (list a2 a3 a4))
                        t))
                   ((equal p 2)
                    (mv (create-and-list-instance (list a1 a2))
                        (create-and-list-instance (list a1 a3))
                        (create-and-list-instance (list a1 a4))
                        (create-and-list-instance (list a1 a2 a3))
                        (create-and-list-instance (list a1 a2 a4))
                        (create-and-list-instance (list a1 a3 a4))
                        t))
                   (t (mv ''0 ''0 ''0 ''0 ''0 ''0 nil))))
            (& (mv ''0 ''0 ''0 ''0 ''0 ''0 nil))))
         ((unless valid) (mv (list pp-orig pp-orig) ''0))
         (c (b* ((pp-lst (pp-sum-merge-aux (list pp1)
                                           (pp-sum-merge-aux (list pp2)
                                                             (list pp3))))
                 (pp (create-list-instance pp-lst))
                 (hash-code (calculate-c-hash ''nil pp ''nil))
                 (c `(rp 'bitp (c ',hash-code 'nil ,pp 'nil )))
                 (c (create-times-instance (- coef) c)))
              c))
         ((mv pp4 pp5 pp6)
          (mv (create-times-instance coef pp4)
              (create-times-instance coef pp5)
              (create-times-instance coef pp6)))
         (res-pp-lst (pp-sum-merge-aux (list pp4)
                                       (pp-sum-merge-aux (list pp5) (list
                                                                     pp6)))))
      (mv res-pp-lst c)))

  (define recollect-pp-lst-to-sc ((pp-lst rp-term-listp))

    :measure (cons-count pp-lst)
    :prepwork ((local
                (defthm cons-count-cddr
                  (implies (and (consp pp-lst)
                                (consp (cdr pp-lst)))
                           (o< (cons-count (cddr pp-lst))
                               (cons-count pp-lst)))
                  :hints (("Goal"
                           :induct (cons-count pp-lst)
                           :do-not-induct t
                           :in-theory (e/d (cons-count)
                                           (+-IS-SUM))))))
               (local
                (in-theory (enable measure-lemmas))))
    :verify-guards :after-returns
    :returns (mv (res-pp-lst rp-term-listp :hyp (rp-term-listp pp-lst))
                 (res-c-lst rp-term-listp :hyp (rp-term-listp pp-lst)))
    (cond ((atom pp-lst) (mv pp-lst nil))
          ((atom (cdr pp-lst)) (mv pp-lst nil))
          ((and (equal (car pp-lst)
                       (cadr pp-lst))
                (recollectable-pp-p (car pp-lst)))
           (b* (((mv new-pp-lst c)
                 (recollect-pp (car pp-lst)))
                ((mv rest-pp-lst rest-c-lst)
                 (recollect-pp-lst-to-sc (cddr pp-lst))))
             (mv (pp-sum-merge-aux rest-pp-lst new-pp-lst)
                 (s-sum-merge-aux (list c) rest-c-lst))))
          (t (b* (((mv rest-pp-lst rest-c-lst)
                   (recollect-pp-lst-to-sc (cdr pp-lst)))
                  (can-be-consed (or (atom rest-pp-lst)
                                     (b* (((mv order &) (pp-order (car pp-lst)
                                                                  (car rest-pp-lst))))
                                       order))))
               (mv (if can-be-consed
                       (cons-with-hint (car pp-lst) rest-pp-lst pp-lst)
                     (pp-sum-merge-aux (list (car pp-lst)) rest-pp-lst))
                   rest-c-lst)))))

  (progn
    (encapsulate
      (((recollect-pp-enabled) => *))
      (local
       (defun recollect-pp-enabled ()
         nil)))

    (defmacro enable-recollect-pp (enable)
      (if enable
          `(defattach recollect-pp-enabled return-t)
        `(defattach recollect-pp-enabled return-nil)))

    (enable-recollect-pp nil))

  (define recollect-pp-lst-to-sc-main ((pp-lst rp-term-listp))
    :returns (mv (res-pp-lst rp-term-listp :hyp (rp-term-listp pp-lst))
                 (res-c-lst rp-term-listp :hyp (rp-term-listp pp-lst)))
    :enabled t
    (if (recollect-pp-enabled)
        (recollect-pp-lst-to-sc pp-lst)
      (mv pp-lst nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;
;; cross product applicable pp

(define extract-first-arg-of-equals (term)
  :returns (res rp-termp :hyp (rp-termp term))
  (case-match term
    (('equals x &) x)
    (& term)))

(progn
  (encapsulate
    (((cross-product-two-larges-enabled) => *))
    (local
     (defun cross-product-two-larges-enabled ()
       nil)))

  (defmacro enable-cross-product-two-larges (enable)
    (if enable
        `(defattach cross-product-two-larges-enabled return-t)
      `(defattach cross-product-two-larges-enabled return-nil)))

  (enable-cross-product-two-larges nil))

;; checks if  single-pp in and-list  form contains  only one s/c/s-c-res  and a
;; bunch of logbits
(define cross-product-pp-pattern-check ((single-pp rp-termp))
  :prepwork
  ((define cross-product-pp-pattern-check-aux ((ppe-lst rp-term-listp))
     :returns (mv (pass booleanp)
                  (s/c-cnt natp))
     (if (atom ppe-lst)
         (mv t 0)
       (b* ((cur-orig (car ppe-lst))
            (has-bitp (has-bitp-rp cur-orig))
            (cur (ex-from-rp cur-orig))
            (cur (extract-first-arg-of-equals cur))
            (cur (ex-from-rp cur)))
         (case-match cur
           (('logbit$inline & &)
            (cross-product-pp-pattern-check-aux (cdr ppe-lst)))
           (('s & & &)
            (b* (((mv rest-valid rest-s/c-cnt)
                  (cross-product-pp-pattern-check-aux (cdr ppe-lst))))
              (mv rest-valid
                  (1+ rest-s/c-cnt))))
           (('c & & & &)
            (b* (((mv rest-valid rest-s/c-cnt)
                  (cross-product-pp-pattern-check-aux (cdr ppe-lst))))
              (mv (and rest-valid
                       has-bitp)
                  (1+ rest-s/c-cnt))))
           (('s-c-res & & &)
            (b* (((mv rest-valid rest-s/c-cnt)
                  (cross-product-pp-pattern-check-aux (cdr ppe-lst))))
              (mv (and rest-valid
                       has-bitp)
                  (1+ rest-s/c-cnt))))
           (& (mv nil 0)))))))
  :returns (pass booleanp)
  (case-match single-pp
    (('and-list & ('list . lst))
     (b* (((mv pass s/c-cnt)
           (cross-product-pp-pattern-check-aux lst)))
       (and pass (or (= s/c-cnt 1)
                     (= s/c-cnt 2)))))
    (& nil)))

;; Traverse a single-pp that is still in its binary-fnc form to see if it
;; contains only one s/c/s-c-res term.
(define cross-product-pp-pattern-check2 ((single-pp rp-termp))
  :returns (pass booleanp)
  :prepwork
  ((define cross-product-pp-pattern-check2-aux ((term rp-termp))
     :returns (mv (pass booleanp)
                  (s/c-count natp))
     :measure (cons-count term)
     :hints (("Goal"
              :in-theory (e/d (extract-first-arg-of-equals
                               measure-lemmas)
                              ())))
     :verify-guards :after-returns
     (b* ((has-bitp (has-bitp-rp term))
          (term (ex-from-rp term))
          (term (extract-first-arg-of-equals term)))
       (cond ((binary-?-p term)
              (b* (((mv pass1 s/c-count1)
                    (cross-product-pp-pattern-check2-aux (cadr term)))
                   ((mv pass2 s/c-count2)
                    (cross-product-pp-pattern-check2-aux (caddr term)))
                   ((mv pass3 s/c-count3)
                    (cross-product-pp-pattern-check2-aux (cadddr term)))
                   (sum13 (+ s/c-count1 s/c-count3)))
                (mv (and pass1 pass2 pass3
                         (equal sum13 0))
                    (+ sum13 s/c-count2))))
             ((binary-and-p term)
              (b* (((mv pass1 s/c-count1)
                    (cross-product-pp-pattern-check2-aux (cadr term)))
                   ((mv pass2 s/c-count2)
                    (cross-product-pp-pattern-check2-aux (caddr term))))
                (mv (and pass1 pass2 )
                    (+ s/c-count1 s/c-count2))))
             ((or (binary-or-p term)
                  (binary-xor-p term))
              (b* (((mv pass1 s/c-count1)
                    (cross-product-pp-pattern-check2-aux (cadr term)))
                   ((mv pass2 s/c-count2)
                    (cross-product-pp-pattern-check2-aux (caddr term)))
                   (total (+ s/c-count1 s/c-count2)))
                (mv (and pass1 pass2 (equal total 0))
                    total)))
             ((binary-not-p term)
              (b* (((mv pass s/c-count)
                    (cross-product-pp-pattern-check2-aux (cadr term))))
                (mv (and pass (equal s/c-count 0)) s/c-count)))
             ((logbit-p term)
              (mv t 0))
             ((single-s-p term)
              (mv t 1))
             ((single-c-p term)
              (mv has-bitp 1))
             ((single-s-c-res-p term)
              (mv has-bitp 1))
             (t (mv has-bitp 0))))))
  (b* (((mv pass s/c-count)
        (cross-product-pp-pattern-check2-aux single-pp)))
    (and pass
         (equal s/c-count 1))))

;; check if single-pp is a product of only two s/c/s-c-res
(define cross-product-pp-pattern-check3 ((single-pp rp-termp))
  (case-match single-pp
    (('and-list & ('list x y))
     (or (and (single-s-p (ex-from-rp$ x))
              (single-s-p (ex-from-rp$ y)))
         (and (single-c-p (ex-from-rp$ x))
              (has-bitp-rp x)
              (single-s-p (ex-from-rp$ y)))
         (and (single-s-p (ex-from-rp$ x))
              (single-c-p (ex-from-rp$ y))
              (has-bitp-rp y))
         (and (single-s-p (ex-from-rp$ x))
              (single-s-c-res-p (ex-from-rp$ y))
              (has-bitp-rp y)))))
  ///
  (defthm cross-product-pp-pattern-check3-implies-fc
    (implies (cross-product-pp-pattern-check3 single-pp)
             (case-match single-pp
               (('and-list & ('list & &)) t)))
    :rule-classes :forward-chaining))

;; Given an e-lst, separate its logbit elements with s/c..
(define cross-product-pp-aux-precollect ((e-lst rp-term-listp))
  :returns (mv (single-s/c-lst rp-term-listp :hyp (rp-term-listp e-lst))
               (res-e-lst rp-term-listp :hyp (rp-term-listp e-lst))
               (valid booleanp))
  (if (atom e-lst)
      (mv nil nil t)
    (b* ((cur-orig (car e-lst))
         (has-bitp (has-bitp-rp cur-orig))
         (cur (ex-from-rp cur-orig))
         (cur (extract-first-arg-of-equals cur))
         (cur (ex-from-rp cur))
         ((mv rest-single-s/c-lst rest-lst valid)
          (cross-product-pp-aux-precollect (cdr e-lst)))
         ((unless valid)
          (mv rest-single-s/c-lst
              (cons cur rest-lst)
              nil)))
      (cond
       ((logbit-p cur)
        (mv rest-single-s/c-lst
            (cons-with-hint cur rest-lst e-lst)
            t))
       ((single-s-p cur)
        (mv (cons cur rest-single-s/c-lst) rest-lst t))
       ((single-c-p cur)
        (mv (cons cur rest-single-s/c-lst) rest-lst has-bitp))
       ((s-c-res-p cur)
        (mv (cons cur rest-single-s/c-lst) rest-lst has-bitp))
       (t  ;; should never come here because of pattern-check
        (mv rest-single-s/c-lst
            (cons cur rest-lst)
            nil))))))

;; separate single-s/c from within binary-fncs
(define cross-product-pp-aux-precollect2 ((single-pp rp-termp))
  :returns (mv (single-s/c rp-termp :hyp (rp-termp single-pp))
               (res-pp rp-termp :hyp (rp-termp single-pp))
               (side-pp-lst rp-term-listp :hyp (rp-termp single-pp))
               (valid booleanp))
  :measure (cons-count single-pp)
  :hints (("Goal"
           :in-theory (e/d (extract-first-arg-of-equals
                            measure-lemmas) ())))
  :verify-guards :after-returns
  :prepwork
  ((define cross-product-pp-aux-precollect2-aux ((single-pp rp-termp)
                                                 (side-pp-lst rp-term-listp))
     :returns (res-side-pp-lst rp-term-listp :hyp (and (rp-termp single-pp)
                                                       (rp-term-listp side-pp-lst)))
     (if (atom side-pp-lst)
         nil
       (cons `(binary-and ,single-pp
                          ,(car side-pp-lst))
             (cross-product-pp-aux-precollect2-aux single-pp (cdr side-pp-lst))))))

  (b* ((has-bitp (has-bitp-rp single-pp))
       (term (ex-from-rp single-pp))
       #|(term (extract-first-arg-of-equals term))|#)
    (cond ((binary-?-p term)
           (b* ((test (cadr term))
                (then (caddr term))
                (else (cadddr term))
                ((mv s/c1 pp1 side-pp1 valid)
                 (cross-product-pp-aux-precollect2 then))
                ((when (equal s/c1 ''1))
                 (mv ''1 single-pp nil t))
                ((unless valid)
                 (mv ''nil ''nil nil nil)))
             (mv s/c1
                 `(binary-and ,test ,pp1)
                 (cons `(binary-and (binary-not ,test) ,else)
                       (cross-product-pp-aux-precollect2-aux test side-pp1))
                 t)))
          ((or*-exec (binary-not-p term)
                     (binary-or-p term)
                     (binary-xor-p term)
                     (logbit-p term)
                     (equal term ''1)
                     (equal term ''0))
           (mv ''1 single-pp nil t))
          ((binary-and-p term)
           (b* (((mv s/c1 pp1 side1 valid1)
                 (cross-product-pp-aux-precollect2 (cadr term)))
                ((mv s/c2 pp2 side2 valid2)
                 (cross-product-pp-aux-precollect2 (caddr term)))
                ((unless (and valid1 valid2))
                 (mv ''nil ''nil nil nil))
                (s/c1-e (not (equal s/c1 ''1)))
                (s/c2-e (not (equal s/c2 ''1)))
                ((when (and s/c1-e (not s/c2-e) (not side2)))
                 (mv s/c1 `(binary-and ,pp1 ,pp2)
                     (cross-product-pp-aux-precollect2-aux pp2 side1)
                     t))
                ((when (and s/c2-e (not s/c1-e) (not side1)))
                 (mv s/c2 `(binary-and ,pp1 ,pp2)
                     (cross-product-pp-aux-precollect2-aux pp1 side2)
                     t))
                ((when (and (not s/c1-e) (not s/c2-e) (not side1) (not side2)))
                 (mv ''1 `(binary-and ,pp1 ,pp2) nil t)))
             (mv ''nil ''nil nil nil)))
          ((single-s-p term)
           (mv single-pp ''1 nil t))
          ((or (single-c-p term)
               (single-s-c-res-p term))
           (mv single-pp ''1 nil has-bitp))
          (t
           (mv ''1 single-pp nil has-bitp)))))

(define and-list-to-binary-and ((term rp-termp))
  :returns (mv (res rp-termp :hyp (rp-termp term))
               (valid booleanp))
  :prepwork
  ((define and-list-to-binary-and-aux (lst)
     :returns (res rp-termp :hyp (rp-term-listp lst))
     (if (atom lst)
         ''1
       (if (atom (cdr lst))
           `(binary-and ,(car lst) '1)
         (if (atom (cddr lst))
             `(binary-and ,(car lst) ,(cadr lst))
           `(binary-and ,(car lst)
                        ,(and-list-to-binary-and-aux (cdr lst))))))))

  (case-match term
    (('and-list & ''nil)
     (mv ''1 t))
    (('and-list & ('list . lst))
     (mv (and-list-to-binary-and-aux lst) t))
    (('logbit$inline & &)
     (mv term t))
    (& (mv term (or (binary-fnc-p term)
                    (equal term ''1)
                    (equal term ''0)
                    (has-bitp-rp term))))))

;; Cross product e-lst into pp-lst.

(define cross-product-pp-aux-for-pp-lst  ((pp-lst rp-term-listp)
                                          (e-lst rp-term-listp))
  :returns (mv (res-pp-lst rp-term-listp :hyp (and (rp-term-listp pp-lst)
                                                   (rp-term-listp e-lst)))
               (valid booleanp))
  :prepwork
  ((define cross-product-pp-aux-for-pp-lst-aux ((pp-lst rp-term-listp)
                                                (e-lst rp-term-listp))
     :returns (mv (res-pp-lst rp-term-listp :hyp (and (rp-term-listp pp-lst)
                                                      (rp-term-listp e-lst)))
                  (valid booleanp))
     (if (atom pp-lst)
         (mv nil t)
       (b* ((cur (car pp-lst))
            ((mv coef cur) (get-pp-and-coef cur)))
         (cond
          ((and (consp e-lst)
                (not (cdr e-lst))
                (binary-fnc-p (car e-lst)))
           (b* (((mv cur-in-binary-fnc cur-is-bitp) (and-list-to-binary-and cur))
                ((Unless cur-is-bitp) (mv nil nil))
                ((mv rest-pp-lst valid)
                 (cross-product-pp-aux-for-pp-lst-aux (cdr pp-lst) e-lst))
                (res `(binary-and ,cur-in-binary-fnc ,(car e-lst))))
             (mv (cons (create-times-instance coef res)
                       rest-pp-lst)
                 valid)))
          ((and-list-p cur)
           (case-match cur
             (('and-list & ('list . lst))
              (b* ((res-e-lst (merge-sorted-and$-lists lst e-lst))
                   (cur-pp (create-and-list-instance res-e-lst))
                   (cur-pp (create-times-instance coef cur-pp))
                   ((mv rest-pp-lst valid)
                    (cross-product-pp-aux-for-pp-lst-aux (cdr pp-lst) e-lst)))
                (mv (cons cur-pp rest-pp-lst)
                    valid)))
             (&
              (mv nil (hard-error 'cross-product-pp-aux-for-pp-lst-aux
                                  "Unexpected pp-lst element: ~p0 ~%"
                                  (list (cons #\0 cur)))))))
          ((or (logbit-p cur)
               (equal cur ''1)
               (has-bitp-rp cur))
           (b* ((res-e-lst (merge-sorted-and$-lists (list cur) e-lst))
                (cur-pp (create-and-list-instance res-e-lst))
                (cur-pp (create-times-instance coef cur-pp))
                ((mv rest-pp-lst valid)
                 (cross-product-pp-aux-for-pp-lst-aux (cdr pp-lst) e-lst)))
             (mv (cons cur-pp rest-pp-lst)
                 valid)))
          ((binary-fnc-p cur)
           (b* ((e-lst-in-binary-fnc (and-list-to-binary-and-aux e-lst))
                ((mv rest-pp-lst valid)
                 (cross-product-pp-aux-for-pp-lst-aux (cdr pp-lst) e-lst))
                (res `(binary-and ,e-lst-in-binary-fnc ,cur)))
             (mv (cons (create-times-instance coef res)
                       rest-pp-lst)
                 valid)))
          (t (mv nil (hard-error 'cross-product-pp-aux-for-pp-lst-aux
                                 "Unexpected pp-lst element: ~p0 ~%"
                                 (list (cons #\0 cur))))))))))

  (b* (((mv res-pp-lst valid)
        (cross-product-pp-aux-for-pp-lst-aux pp-lst e-lst))
       ((unless valid)
        (mv res-pp-lst valid))
       ((when (pp-lst-orderedp res-pp-lst))
        (mv res-pp-lst valid))
       (res-pp-lst (pp-sum-sort-lst res-pp-lst)))
    (mv res-pp-lst valid)))



;; Cros product e-lst into single-s/c
(defines cross-product-pp-aux-for-s/c

  :flag-local nil
  :hints (("Goal"
           :in-theory (e/d (get-pp-and-coef
                            measure-lemmas)
                           (floor))))
  :prepwork ((local
              (use-arithmetic-5 t))

             ;; (local
             ;;  (defthmd *-<-with-posp
             ;;    (implies (and (posp size)
             ;;                  (acl2-numberp x)
             ;;                  (acl2-numberp y))
             ;;             (equal (< x y)
             ;;                    (< (* size x)
             ;;                       (* size y))))))

             ;; (local
             ;;  (defthm dumb-equality
             ;;    (implies (and (natp x)
             ;;                  (natp y)
             ;;                  (posp z)
             ;;                  (< x y))
             ;;             (< x (* y z)))
             ;;    :hints (("Goal"
             ;;             :cases ((= z 1))
             ;;             :in-theory (e/d ((:e tau-system)) ())))))

             ;; (local
             ;;  (defthm floor-lemma
             ;;    (implies (and (natp x)
             ;;                  (natp y)
             ;;                  (posp size)
             ;;                  (< x y))
             ;;             (< (floor x size)
             ;;                y))
             ;;    :hints (("Goal"
             ;;             :in-theory (e/d () (*-<-with-posp)))
             ;;            (and stable-under-simplificationp
             ;;                 '(:use ((:instance *-<-with-posp
             ;;                                    (x (* x (/ size))))))))))

             (local
              (defthm m-lemma1
                (implies (and (consp y)
                              (<= (cons-count x) (cons-count y)))
                         (and (o< (cons-count (cadr (cadddr x)))
                                  (cons-count y))
                              (< (cons-count (cadr (cadddr x)))
                                 (cons-count y))))
                :hints (("goal"
                         :in-theory (e/d (cons-count) ())))))
             (local
              (defthm m-lemma2
                (implies (and (consp y)
                              (<= (cons-count x) (cons-count y)))
                         (and (o< (cons-count (cadr (car (cddddr x))))
                                  (cons-count y))
                              (< (cons-count (cadr (car (cddddr x))))
                                 (cons-count y))))
                :hints (("goal"
                         :in-theory (e/d (cons-count) ())))))

             )

  (define cross-product-pp-aux-for-s/c ((single-s/c rp-termp)
                                        (e-lst rp-term-listp)
                                        &optional
                                        ((limit natp) 'limit))
    :verify-guards nil
    :returns (mv (res-s-lst)
                 (res-pp-lst)
                 (res-c-lst)
                 (valid booleanp))
    :measure (acl2::nat-list-measure (list (nfix limit) 0))

    (b* (((when (zp limit)) (mv nil nil nil nil))
         ;;(limit (1- limit))
         (single-s/c-orig single-s/c)
         ((mv coef single-s/c) (get-pp-and-coef single-s/c))
         (single-s/c (ex-from-rp$ single-s/c)))
      (cond ((single-s-p single-s/c)
             (case-match single-s/c
               (('s & pp c-list)
                (b* ((pp-lst (list-to-lst pp))
                     ((mv new-pp-lst valid)
                      (cross-product-pp-aux-for-pp-lst pp-lst e-lst))
                     ((unless valid) (mv nil nil nil nil))
                     (c-lst (list-to-lst c-list))
                     (len-c-lst (len c-lst))
                     (limit (if (> len-c-lst 1) (floor limit len-c-lst) (1- limit))) ;; shrink limit even
                     ;; further if more than one c-lst exists, which should
                     ;; almost never happen.
                     ((mv rest-s-lst rest-pp-lst rest-c-lst valid)
                      (cross-product-pp-aux-for-s/c-lst c-lst e-lst))
                     ((unless (and valid
                                   (equal rest-s-lst nil)))
                      (mv nil nil nil nil))
                     (new-pp-lst (pp-sum-merge-aux rest-pp-lst new-pp-lst))
                     (new-pp-lst (s-fix-pp-args-aux new-pp-lst))
                     (rest-c-lst (s-fix-pp-args-aux rest-c-lst))
                     ((mv res-s-lst res-pp-lst res-c-lst)
                      (create-s-instance (create-list-instance new-pp-lst)
                                         (create-list-instance rest-c-lst))))
                  (mv (append-with-times coef res-s-lst nil)
                      (append-with-times coef  res-pp-lst nil)
                      (append-with-times coef  res-c-lst nil)
                      t)))
               ;; (('s & ('list . pp-lst) ''nil)
               ;;  (b* (((mv new-pp-lst valid)
               ;;        (cross-product-pp-aux-for-pp-lst pp-lst e-lst))
               ;;       ((unless valid) (mv nil nil nil nil))
               ;;       (new-pp-lst (s-fix-pp-args-aux new-pp-lst))
               ;;       ((mv res-s-lst res-pp-lst res-c-lst)
               ;;        (create-s-instance (create-list-instance new-pp-lst)
               ;;                           ''nil)))
               ;;    (mv (append-with-times coef  res-s-lst nil)
               ;;        (append-with-times coef  res-pp-lst nil)
               ;;        (append-with-times coef  res-c-lst nil)
               ;;        t)))
               (& (mv nil nil nil nil))))


            ((and*-exec (single-c-p single-s/c)
                        (c-pattern4-compress-enabled))
             (b* (((when (not e-lst)) (mv nil nil nil nil))

                  ((mv more-pp-common res-c)
                   (break-down-two-arg-c single-s/c-orig))

                  (pp-commons (merge-sorted-and$-lists more-pp-common e-lst))
                  (res (create-and-times-list-instance pp-commons res-c))

                  #|(- (cw "res: ~p0, single-s/c-orig:~p1, e-lst:~p2 ~%" res
                  single-s/c-orig e-lst))|#
                  )
               (mv nil (list res) nil t)))


            ((single-c-p single-s/c)
             (case-match single-s/c
               (('c & ''nil pp c-list)
                (b* ((pp-lst (list-to-lst pp))
                     ((mv new-pp-lst valid)
                      (cross-product-pp-aux-for-pp-lst pp-lst e-lst))
                     ((unless valid) (mv nil nil nil nil))
                     (c-lst (list-to-lst c-list))
                     (len-c-lst (len c-lst))
                     (limit (if (> len-c-lst 1) (floor limit len-c-lst) (1- limit)))  ;; shrink  limit even
                     ;; further  if more  than one  c-lst exists,  which should
                     ;; almost never happen.
                     ((mv rest-s-lst rest-pp-lst rest-c-lst valid)
                      (cross-product-pp-aux-for-s/c-lst c-lst e-lst))
                     ((unless (and valid
                                   (equal rest-s-lst nil)))
                      (mv nil nil nil nil))
                     (new-pp-lst (pp-sum-merge-aux rest-pp-lst new-pp-lst))
                     ((mv coughed-pp-lst new-pp-lst) (c-fix-arg-aux new-pp-lst))
                     ((mv coughed-c-lst rest-c-lst) (c-fix-arg-aux rest-c-lst))
                     ((mv res-s-lst res-pp-lst res-c-lst)
                      (create-c-instance nil
                                         new-pp-lst
                                         rest-c-lst))
                     (res-pp-lst (pp-sum-merge-aux coughed-pp-lst res-pp-lst))
                     (res-c-lst (s-sum-merge-aux res-c-lst coughed-c-lst)))
                  (mv (append-with-times coef res-s-lst nil)
                      (append-with-times coef res-pp-lst nil)
                      (append-with-times coef res-c-lst nil)
                      t)))
               #|(('c & ''nil ('list . pp-lst) ''nil)
               (b* (((mv new-pp-lst valid)
               (cross-product-pp-aux-for-pp-lst pp-lst e-lst))
               ((unless valid) (mv nil nil nil nil))
               ((mv coughed-pp-lst new-pp-lst) (c-fix-arg-aux new-pp-lst))
               ((mv res-s-lst res-pp-lst res-c-lst)
               (create-c-instance nil
               new-pp-lst
               nil))
               (res-pp-lst (pp-sum-merge-aux coughed-pp-lst res-pp-lst)))
               (mv (append-with-times coef res-s-lst nil)
               (append-with-times coef res-pp-lst nil)
               (append-with-times coef res-c-lst nil)
               t)))|#
               (& (mv nil nil nil nil))))
            (t (mv nil nil nil nil)))))

  (define cross-product-pp-aux-for-s/c-lst ((s/c-lst rp-term-listp)
                                            (e-lst rp-term-listp)
                                            &optional
                                            ((limit natp) 'limit))
    :returns (mv (res-s-lst)
                 (res-pp-lst)
                 (res-c-lst)
                 (valid booleanp))
    :verify-guards nil
    :measure (acl2::nat-list-measure (list (nfix limit) (len s/c-lst)))
    (b* (((when (zp limit)) (mv nil nil nil nil))
         ;;(limit (1- limit))
         ((when (atom s/c-lst)) (mv nil nil nil t))
         ((mv res-s-lst res-pp-lst res-c-lst valid)
          (cross-product-pp-aux-for-s/c (car s/c-lst) e-lst))
         ((unless valid) (mv nil nil nil nil))
         ((mv res-s-lst2 res-pp-lst2 res-c-lst2 valid)
          (cross-product-pp-aux-for-s/c-lst (cdr s/c-lst) e-lst))
         ((unless valid) (mv nil nil nil nil)))
      (mv (s-sum-merge-aux res-s-lst res-s-lst2)
          (pp-sum-merge-aux res-pp-lst res-pp-lst2)
          (s-sum-merge-aux res-c-lst res-c-lst2)
          t)))

  ///

  (defret-mutual rp-term-listp-of-<fn>
    (defret rp-term-listp-of-<fn>
      (implies (and (rp-termp single-s/c)
                    (rp-term-listp e-lst))
               (and (rp-term-listp res-s-lst)
                    (rp-term-listp res-pp-lst)
                    (rp-term-listp res-c-lst)))
      :fn cross-product-pp-aux-for-s/c)
    (defret rp-term-listp-of-<fn>
      (implies (and (rp-term-listp s/c-lst)
                    (rp-term-listp e-lst))
               (and (rp-term-listp res-s-lst)
                    (rp-term-listp res-pp-lst)
                    (rp-term-listp res-c-lst)))
      :fn cross-product-pp-aux-for-s/c-lst))

  (verify-guards cross-product-pp-aux-for-s/c-fn))

#|(memoize 'cons-count :forget t)|#

;; Cross product list of s/c with e-lst

;; Calls cross-product-pp-aux-for-s/c to cross product  single-s/c with e-lst
;; Difference from cross-product-pp-aux-for-s/c: this can handle s-c-res terms.
(define cross-product-pp-aux-for-s/c-main ((single-s/c rp-termp)
                                           (e-lst rp-term-listp))
  :returns (mv (res-s-lst)
               (res-pp-lst)
               (res-c-lst)
               (valid booleanp))
  (b* (;; (count (+ (cons-count single-s/c) (cons-count e-lst)))
       ;; ((when (> count (expt 2 17))) (mv nil nil nil nil))
       (limit (expt 2 14)) ;;cross-product-pp-aux-for-s/c recursion limit
       (single-s/c-orig single-s/c)
       (single-s/c (ex-from-rp$ single-s/c)))
    (cond ((single-s-c-res-p single-s/c)
           (b* ((s-lst (list-to-lst (cadr single-s/c)))
                (pp-lst (list-to-lst (caddr single-s/c)))
                (c-lst (list-to-lst (cadddr single-s/c)))
                ((mv res-s-lst1 res-pp-lst1 res-c-lst1 valid)
                 (cross-product-pp-aux-for-s/c-lst s-lst e-lst))
                ((unless valid) (mv nil nil nil nil))
                ((mv res-pp-lst2 valid)
                 (cross-product-pp-aux-for-pp-lst pp-lst e-lst))
                ((unless valid) (mv nil nil nil nil))
                ((mv res-s-lst3 res-pp-lst3 res-c-lst3 valid)
                 (cross-product-pp-aux-for-s/c-lst c-lst e-lst))
                ((unless valid) (mv nil nil nil nil)))
             (mv (s-sum-merge-aux res-s-lst1 res-s-lst3)
                 (pp-sum-merge-aux res-pp-lst1
                                   (pp-sum-merge-aux res-pp-lst2 res-pp-lst3))
                 (s-sum-merge-aux res-c-lst1 res-c-lst3)
                 t)))
          (t (cross-product-pp-aux-for-s/c single-s/c-orig e-lst))))
  ///
  (defret rp-term-listp-of-<fn>
    (implies (and (rp-termp single-s/c)
                  (rp-term-listp e-lst))
             (and (rp-term-listp res-s-lst)
                  (rp-term-listp res-pp-lst)
                  (rp-term-listp res-c-lst)))))

;; Cross product two s/c helper
(define cross-product-two-larges-aux-pp-lst ((pp-lst rp-term-listp)
                                             (single-s/c2 rp-termp))
  :returns (mv (res-s-lst)
               (res-pp-lst)
               (res-c-lst)
               (valid booleanp))
  (if (atom pp-lst)
      (mv nil nil nil t)
    (b* (((mv rest-s-lst rest-pp-lst rest-c-lst valid)
          (cross-product-two-larges-aux-pp-lst (cdr pp-lst) single-s/c2))
         ((unless valid)
          (mv nil nil nil nil))
         (cur-pp (car pp-lst))
         ((mv cur-s-lst cur-pp-lst cur-c-lst valid)
          (case-match cur-pp
            (('and-list & ('list . e-lst))
             (cross-product-pp-aux-for-s/c-main single-s/c2 e-lst))
            (('binary-and x y)
             (cross-product-pp-aux-for-s/c-main single-s/c2 (list x y)))
            (('logbit$inline & &)
             (cross-product-pp-aux-for-s/c-main single-s/c2 (list cur-pp)))
            (''1
             (cond ((single-s-p (ex-from-rp$ single-s/c2))
                    (mv (list single-s/c2) nil nil t))
                   ((single-c-p (ex-from-rp$ single-s/c2))
                    (mv nil nil (list single-s/c2) t))
                   (t
                    (cross-product-pp-aux-for-s/c-main single-s/c2 (list ''1)))))
            (& (mv nil nil nil nil))))
         ((unless valid)
          (mv nil nil nil nil)))
      (mv (s-sum-merge-aux rest-s-lst cur-s-lst)
          (pp-sum-merge-aux rest-pp-lst cur-pp-lst)
          (s-sum-merge-aux rest-c-lst cur-c-lst)
          t)))
  ///
  (defret rp-term-listp-of-<fn>
    (implies (and (rp-termp single-s/c2)
                  (rp-term-listp pp-lst))
             (and (rp-term-listp res-s-lst)
                  (rp-term-listp res-pp-lst)
                  (rp-term-listp res-c-lst)))))

(define cross-product-two-larges-aux ((single-s/c1 rp-termp)
                                      (single-s/c2 rp-termp))
  :returns (mv (res-s-lst)
               (res-pp-lst)
               (res-c-lst)
               (valid booleanp))
  ;;:mode :program
  :measure (cons-count single-s/c1)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :prepwork ((local
              (defthm m-lemma1
                (IMPLIES (and (consp y)
                              (<= (cons-count x) (cons-count y)))
                         (and (O< (CONS-COUNT (CADR (CADDDR x)))
                                  (CONS-COUNT y))
                              (< (CONS-COUNT (CADR (CADDDR x)))
                                 (CONS-COUNT y))))
                :hints (("Goal"
                         :in-theory (e/d (CONS-COUNT) ())))))
             (local
              (defthm m-lemma2
                (IMPLIES (and (consp y)
                              (<= (cons-count x) (cons-count y)))
                         (and (O< (CONS-COUNT (CADR (CAR (CDDDDR x))))
                                  (CONS-COUNT y))
                              (< (CONS-COUNT (CADR (CAR (CDDDDR x))))
                                 (CONS-COUNT y))))
                :hints (("Goal"
                         :in-theory (e/d (CONS-COUNT) ())))))

             )
  :verify-guards nil

  (b* ((?orig single-s/c1)
       (single-s/c1 (ex-from-rp$ single-s/c1)))
    (cond ((single-s-p single-s/c1)
           (case-match single-s/c1
             (('s & pp ('list single-c))
              (b* ((pp-lst (list-to-lst pp))
                   ((mv s-lst1 pp-lst1 c-lst1 valid)
                    (cross-product-two-larges-aux-pp-lst pp-lst single-s/c2))
                   ((unless valid)
                    (mv nil nil nil nil))
                   ((mv s-lst2 pp-lst2 c-lst2 valid)
                    (cross-product-two-larges-aux single-c single-s/c2))
                   ((unless valid)
                    (mv nil nil nil nil))
                   (s-lst (s-sum-merge-aux s-lst1 s-lst2))
                   (s-lst (s-fix-pp-args-aux s-lst))
                   (pp-lst (pp-sum-merge-lst-for-s pp-lst1 pp-lst2))
                   (pp-lst (s-fix-pp-args-aux pp-lst))
                   (c-lst (s-sum-merge-aux c-lst1 c-lst2))
                   (c-lst (s-fix-pp-args-aux c-lst))

                   ((mv pp-lst c-lst)
                    (s-of-s-fix-lst s-lst pp-lst c-lst))
                   ((mv s-res-lst pp-res-lst c-res-lst)
                    (create-s-instance (create-list-instance pp-lst)
                                       (create-list-instance c-lst))))
                (mv s-res-lst pp-res-lst c-res-lst t)))
             (('s & pp ''nil)
              (b* ((pp-lst (list-to-lst pp))
                   ((mv s-lst pp-lst c-lst valid)
                    (cross-product-two-larges-aux-pp-lst pp-lst single-s/c2))
                   ((unless valid)
                    (mv nil nil nil nil))
                   (s-lst (s-fix-pp-args-aux s-lst))
                   (c-lst (s-fix-pp-args-aux c-lst))
                   (pp-lst (s-fix-pp-args-aux pp-lst))

                   ((mv pp-lst c-lst)
                    (s-of-s-fix-lst s-lst pp-lst c-lst))
                   ((mv s-res-lst pp-res-lst c-res-lst)
                    (create-s-instance (create-list-instance pp-lst)
                                       (create-list-instance c-lst))))
                (mv s-res-lst pp-res-lst c-res-lst t)))
             (& (mv nil nil nil nil))))
          ((single-c-p single-s/c1)
           (case-match single-s/c1
             (('c & ''nil pp ('list single-c))
              (b* ((pp-lst (list-to-lst pp))
                   ((mv s-lst1 pp-lst1 c-lst1 valid)
                    (cross-product-two-larges-aux-pp-lst pp-lst single-s/c2))
                   ((unless valid)
                    (mv nil nil nil nil))
                   ((mv s-lst2 pp-lst2 c-lst2 valid)
                    (cross-product-two-larges-aux single-c single-s/c2))
                   ((unless valid)
                    (mv nil nil nil nil))
                   (s-lst (s-sum-merge-aux s-lst1 s-lst2))
                   (pp-lst (pp-sum-merge-aux pp-lst1 pp-lst2))
                   (c-lst (s-sum-merge-aux c-lst1 c-lst2))

                   ((mv pp-res-lst c-res-lst
                        coughed-s-lst coughed-pp-lst coughed-c-lst)
                    (c-of-s-fix-lst s-lst pp-lst c-lst nil))

                   ((mv coughed-pp-lst2 pp-res-lst)
                    (c-fix-arg-aux pp-res-lst))
                   ((mv coughed-c-lst2 c-res-lst)
                    (c-fix-arg-aux c-res-lst))

                   ((mv s-res-lst pp-res-lst c-res-lst)
                    (create-c-instance nil pp-res-lst c-res-lst))

                   (s-res-lst (s-sum-merge-aux coughed-s-lst
                                               s-res-lst))
                   (pp-res-lst (pp-sum-merge-aux coughed-pp-lst
                                                 (pp-sum-merge-aux coughed-pp-lst2
                                                                   pp-res-lst)))
                   (c-res-lst (s-sum-merge-aux coughed-c-lst
                                               (s-sum-merge-aux coughed-c-lst2
                                                                c-res-lst))))
                (mv s-res-lst pp-res-lst c-res-lst t)))
             (('c & ''nil pp ''nil)
              (b* ((pp-lst (list-to-lst pp))
                   ((mv s-lst pp-lst c-lst valid)
                    (cross-product-two-larges-aux-pp-lst pp-lst single-s/c2))
                   ((unless valid)
                    (mv nil nil nil nil))

                   ((mv pp-res-lst c-res-lst
                        coughed-s-lst coughed-pp-lst coughed-c-lst)
                    (c-of-s-fix-lst s-lst pp-lst c-lst nil))

                   ((mv coughed-pp-lst2 pp-res-lst)
                    (c-fix-arg-aux pp-res-lst))
                   ((mv coughed-s-lst2 c-res-lst)
                    (c-fix-arg-aux c-res-lst))

                   ((mv s-res-lst pp-res-lst c-res-lst)
                    (create-c-instance nil pp-res-lst c-res-lst))

                   (s-res-lst (s-sum-merge-aux coughed-s-lst
                                               (s-sum-merge-aux coughed-s-lst2
                                                                s-res-lst)))
                   (pp-res-lst (pp-sum-merge-aux coughed-pp-lst
                                                 (pp-sum-merge-aux coughed-pp-lst2
                                                                   pp-res-lst)))
                   (c-res-lst (s-sum-merge-aux coughed-c-lst
                                               c-res-lst)))
                (mv s-res-lst pp-res-lst c-res-lst t)))

             (& (mv nil nil nil nil))))
          (t (mv nil nil nil nil))))
  ///

  (defret rp-term-listp-of-<fn>
    (implies (and (rp-termp single-s/c1)
                  (rp-termp single-s/c2))
             (and (rp-term-listp res-s-lst)
                  (rp-term-listp res-pp-lst)
                  (rp-term-listp res-c-lst))))

  (verify-guards cross-product-two-larges-aux))

(define create-s-c-res-instance ((s-lst rp-term-listp)
                                 (pp-lst rp-term-listp)
                                 (c-lst rp-term-listp)
                                 (bitp booleanp))
  :inline t
  :returns (res rp-termp :hyp (and (rp-term-listp s-lst)
                                   (rp-term-listp pp-lst)
                                   (rp-term-listp c-lst)))
  :guard-hints (("Goal"
                 :in-theory (e/d (rp-term-listp) ())))
  (cond ((and (not pp-lst) (not c-lst)
              (consp s-lst) (not (cdr s-lst))
              (single-s-p (ex-from-rp$ (car s-lst))))
         (cond ((and bitp
                     (not (hide (is-rp (car s-lst)))))
                `(rp 'bitp ,(car s-lst)))
               (t (car s-lst))))
        ((and (not pp-lst) (not s-lst)
              (consp c-lst) (not (cdr c-lst))
              (single-c-p (ex-from-rp$ (car c-lst))))
         (cond ((and bitp
                     (not (hide (is-rp (car c-lst)))))
                `(rp 'bitp ,(car c-lst)))
               (t (car c-lst))))
        ((and (quoted-listp s-lst)
              (quoted-listp pp-lst)
              (quoted-listp c-lst))
         `',(s-c-res (unquote-all s-lst)
                     (unquote-all pp-lst)
                     (unquote-all c-lst)))
        (t
         (b* (((mv term valid) ;; if there is only one and-list, return its
               ;; binary-and equivalent instead.
               (if (and (not c-lst)
                        (not s-lst)
                        (consp pp-lst)
                        (not (cdr pp-lst)))
                   (and-list-to-binary-and (car pp-lst))
                 (mv nil nil)))
              ((when valid) term)

              (term `(s-c-res ,(create-list-instance s-lst)
                              ,(create-list-instance pp-lst)
                              ,(create-list-instance c-lst))))
           (if bitp
               `(rp 'bitp ,term)
             term)))))

(define cross-product-pp-aux--mid-large-merge ((single-s-lst rp-term-listp))
  :returns (mv (res rp-termp :hyp (rp-term-listp single-s-lst))
               valid)
  (b* (((when (equal (len single-s-lst) 1))
        (mv (car single-s-lst) t))
       ((unless (equal (len single-s-lst) 2))
        (mv ''0 nil))
       (?a (first single-s-lst))
       (?b (second single-s-lst))
       ((unless (or (cross-product-two-larges-enabled)
                    ;; (not (cons-count-compare a 50))
                    ;; (not (cons-count-compare b 50))
                    ))
        (mv ''0 nil))
       ((mv s-lst pp-lst c-lst valid)
        (cross-product-two-larges-aux a b))
       ((unless valid)
        (mv ''0 nil)))
    (mv (create-s-c-res-instance s-lst pp-lst c-lst t)
        t)))

;; Try to cross product single-pp
(define cross-product-pp-aux ((single-pp rp-termp))
  :returns (mv (res-s-lst  rp-term-listp :hyp (rp-termp single-pp))
               (res-pp-lst rp-term-listp :hyp (rp-termp single-pp))
               (res-c-lst  rp-term-listp :hyp (rp-termp single-pp))
               (valid booleanp))

  (b* (((mv coef single-pp) (get-pp-and-coef single-pp)))
    (cond
     ((and*-exec
       (and-list-p single-pp)
       ;; when there's only one s, c, or s-c-res in single-pp:
       (cross-product-pp-pattern-check single-pp))
      (b* ((e-lst (list-to-lst (caddr single-pp)))
           ((mv single-s-lst e-lst valid)
            (cross-product-pp-aux-precollect e-lst))
           ((unless (and*-exec valid))
            (mv nil nil nil nil))
           ((mv single-s/c valid)
            (cross-product-pp-aux--mid-large-merge single-s-lst))
           ((unless (and*-exec valid))
            (mv nil nil nil nil))
           ((mv res-s-lst res-pp-lst res-c-lst valid)
            (cross-product-pp-aux-for-s/c-main single-s/c e-lst)))
        (mv (append-with-times coef res-s-lst nil)
            (append-with-times coef res-pp-lst nil)
            (append-with-times coef res-c-lst nil)
            valid)))
     ((and*-exec
       (binary-fnc-p single-pp)
       (cross-product-pp-pattern-check2 single-pp))
      (b* (((mv single-s/c res-pp side-pp-lst valid)
            (cross-product-pp-aux-precollect2 single-pp))
           ((unless valid)
            (mv nil nil nil nil))
           ((mv res-s-lst res-pp-lst res-c-lst valid)
            (cross-product-pp-aux-for-s/c-main single-s/c (list res-pp)))
           (res-pp-lst (pp-sum-merge-aux res-pp-lst side-pp-lst)))
        (mv (append-with-times coef res-s-lst nil)
            (append-with-times coef res-pp-lst nil)
            (append-with-times coef res-c-lst nil)
            valid)))
     ((and*-exec
       (cross-product-two-larges-enabled)
       (and-list-p single-pp)
       ;; when there's only one s, c, or s-c-res in single-pp:
       (cross-product-pp-pattern-check3 single-pp))
      (b* ((single-s/c1 (cadr (caddr single-pp)))
           (single-s/c2 (caddr (caddr single-pp)))
           ((mv s-lst pp-lst c-lst valid)
            (cross-product-two-larges-aux single-s/c1 single-s/c2))
           ((unless valid)
            (mv nil nil nil nil)))
        (mv (append-with-times coef s-lst nil)
            (append-with-times coef pp-lst nil)
            (append-with-times coef c-lst nil)
            t)))
     (t (mv nil nil nil nil)))))

(local
 (defthm rp-term-listp-of-nthcdr
   (implies (and (rp-term-listp lst)
                 (<= num (len lst)))
            (rp-term-listp (nthcdr num lst)))
   :hints (("Goal"
            :in-theory (e/d (nthcdr len)
                            ())))))

;; Traverse pp-lst to see if each is eligible for cross-product. If so, do it.
(define cross-product-pp-aux2 ((pp-lst rp-term-listp))
  :returns (mv (res-s-lst rp-term-listp :hyp (rp-term-listp pp-lst))
               (res-pp-lst rp-term-listp :hyp (rp-term-listp pp-lst))
               (res-c-lst rp-term-listp :hyp (rp-term-listp pp-lst)))
  :measure (len pp-lst)
  :prepwork ((local
              (defthm len-of-nthcdr
                (implies (and (consp pp-lst)
                              (posp num)
                              (<= num (len pp-lst)))
                         (< (len (nthcdr num pp-lst))
                            (len pp-lst)))
                :hints (("goal"
                         :in-theory (e/d (len nthcdr) ()))))))
  :verify-guards :after-returns
  (if (atom pp-lst)
      (mv nil nil nil)
    (b* (((mv res-s-lst res-pp-lst res-c-lst valid)
          (cross-product-pp-aux (car pp-lst)))
         ((mv rest-s-lst rest-pp-lst rest-c-lst)
          (cross-product-pp-aux2 (cdr pp-lst)))) ;;
      (if valid
          (mv (s-sum-merge-aux res-s-lst rest-s-lst)
              (pp-sum-merge-aux res-pp-lst rest-pp-lst)
              (s-sum-merge-aux res-c-lst rest-c-lst))
        (mv rest-s-lst
            (cons-with-hint (car pp-lst)
                            rest-pp-lst
                            pp-lst)
            rest-c-lst)))))

(define cross-product-pp ((pp-lst rp-term-listp))
  :returns (mv (res-s-lst rp-term-listp :hyp (rp-term-listp pp-lst))
               (res-pp-lst rp-term-listp :hyp (rp-term-listp pp-lst))
               (res-c-lst rp-term-listp :hyp (rp-term-listp pp-lst)))
  "Applicable elements in pp-lst will be tried for cross product. For example,
  (and$ x (s a b c)) may become (s (and$ a x) (and$ b x) (and$ c x))"
  (b* (((mv res-s-lst res-pp-lst res-c-lst)
        (cross-product-pp-aux2 pp-lst))
       (res-pp-lst (if (pp-lst-orderedp res-pp-lst)
                       res-pp-lst
                     (pp-sum-sort-lst res-pp-lst))))
    (mv res-s-lst res-pp-lst res-c-lst)))

;; Not used ?
(define pp-lst-is-a-part-of-radix8+-summation ((pp-lst))
  :returns (res booleanp)
  (if (atom pp-lst)
      (equal pp-lst nil)
    (b* ((cur (ex-from-rp-loose (car pp-lst))))
      (and (or (equal cur ''1)
               (logbit-p cur)
               (and (binary-not-p cur)
                    (logbit-p (cadr cur))))
           (pp-lst-is-a-part-of-radix8+-summation (cdr pp-lst))))))

;; If pp is from mcand calculation in radix8+, return t.
(define pp-is-a-part-of-radix8+-summation ((cur))
  :returns (res booleanp)
  (and (or (equal cur ''1)
           (logbit-p cur)
           (and (binary-and-p cur)
                (or (logbit-p (ex-from-rp-loose (cadr cur)))
                    (quotep (cadr cur)))
                (or (logbit-p (ex-from-rp-loose (caddr cur)))
                    (quotep (caddr cur))))
           (and (binary-not-p cur)
                (logbit-p (ex-from-rp-loose (cadr cur)))))))

;;;;;;;;

;;;;;;;;;;;;;;;;;;;

(define is-bitp-svl-bits ((term-orig rp-termp))
  (and (has-integerp-rp term-orig)
       (b* ((term (ex-from-rp$ term-orig)))
         (case-match term
           (('svl::bits & & ''1)
            t)))))

(defthm true-listp-of-APPEND-WITH-TIMES-AUX
  (implies (true-listp rest)
           (true-listp (append-with-times-aux coef term rest)))
  :hints (("Goal"
           :in-theory (e/d (append-with-times-aux) ()))))

(local
 (defthmd cons-count-when-times
   (implies (case-match term (('times & &) t))
            (equal (cons-count term)
                   (+ 2 (cons-count (cadr term))
                      (cons-count (caddr term)))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d (cons-count) ())))))

(local
 (defthmd cons-count-when-quoted
   (implies (case-match term (('quote &) t))
            (equal (cons-count term)
                   (+ 2 (cons-count (cadr term)))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d (cons-count) ())))))

(define extract-new-sum-element ((term rp-termp)
                                 (acc true-listp)
                                 &key
                                 ((limit natp) '*large-number*) ;; too lazy to prove measure....
                                 )
  :returns (acc-res rp-term-listp
                    :hyp (and (rp-termp term)
                              (rp-term-listp acc)))
  ;;:measure (cons-count term)
  :measure (nfix limit)
  :verify-guards nil
  ;; :hints (("Goal"
  ;;          :in-theory (e/d (get-pp-and-coef
  ;;                           cons-count-when-quoted
  ;;                           cons-count-when-times
  ;;                           create-times-instance
  ;;                           measure-lemmas) ())))
  (b* ((term-orig term)
       ((mv coef term) (get-pp-and-coef term))
       (term-with-sc term)
       (term (ex-from-rp$ term)))
    (cond
     ((single-c-p term)
      (cons term-orig acc))
     ((single-s-p term)
      (cons term-orig acc))
     ((single-s-c-res-p term)
      (cons term-orig acc))
     ((sum-list-p term)
      (cons term-orig acc))
     ((and-list-p term)
      (cons term-orig acc))
     ((binary-sum-p term)
      (b* (((when (zp limit)) (cons term-orig acc))
           (acc (extract-new-sum-element (create-times-instance coef (cadr term)) acc :limit (1- limit)))
           (acc (extract-new-sum-element (create-times-instance coef (caddr term)) acc :limit (1- limit))))
        acc))
     ((quote-p term)
      (b* ((x (ifix (cadr term)))) ;; ifix here is ok because sum-list calls sum which
        ;; calls ifix for its arguments..
        (cons-with-times (* coef x) ''1 acc)))
     ((or (pp-term-p term)
          (binary-fnc-p term)
          (has-bitp-rp term-with-sc))
      (cons term-orig acc))
     ((is-bitp-svl-bits term-with-sc)
      (cons-with-times coef `(rp 'bitp ,term-with-sc) acc))
     ((--.p term)
      (cons-with-times (- coef) (cadr term)  acc))
     (t
      (progn$
       (hard-error 'extract-new-sum-element
                   "Unexpected term: ~p0 ~%"
                   (list (cons #\0 term-orig)))
       (cons term-orig acc)))))
  ///
  (defret true-listp-of-<fn>
    (implies (true-listp acc)
             (true-listp acc-res))
    :hints (("Goal"
             :in-theory (e/d (append-with-times-aux
                              append-with-times
                              cons-with-times) ()))))
  (verify-guards extract-new-sum-element-fn))

(define extract-new-sum-consed ((term rp-termp))
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :prepwork
  ((local
    (in-theory (enable ex-from-rp))))
  :returns (acc-res rp-term-listp
                    :hyp (and (rp-termp term)))
  :verify-guards :after-returns
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

(defsection extract-equals-from-pp-lst

  (define extract-equals-from-pp-lst-precheck (e-lst)
    (if (atom e-lst)
        nil
      (or (is-equals (ex-from-rp-loose (car e-lst)))
          (extract-equals-from-pp-lst-precheck (cdr e-lst)))))

  (define extract-equals-from-pp-lst-aux ((e-lst rp-term-listp))
    :returns (mv (res-e-lst rp-term-listp :hyp (rp-term-listp e-lst))
                 (res-pp-lst rp-term-listp :hyp (rp-term-listp e-lst)))
    (if (atom e-lst)
        (mv nil nil)
      (b* ((cur (ex-from-rp$ (car e-lst)))
           ((when (and (is-equals cur)
                       (pp-term-p (caddr cur))))
            (mv (cdr e-lst)
                (pp-flatten-memoized (caddr cur))))
           ((mv rest1 rest2)
            (extract-equals-from-pp-lst-aux (cdr e-lst))))
        (mv (cons-with-hint (car e-lst) rest1 e-lst)
            rest2))))

  (define extract-equals-from-pp-lst ((pp-lst rp-term-listp)
                                      (limit natp))
    :measure (acl2::nat-list-measure (list limit (len pp-lst)))
    :returns (res-lst rp-term-listp :hyp (rp-term-listp pp-lst))
    :verify-guards :after-returns
    (b* (((when (zp limit)) pp-lst)
         ((when (atom pp-lst)) nil)
         ;; skip repeateds because they'll either be coughed or removed.
         #|((when (and (consp (cdr pp-lst))
         (rp-equal-cnt (first pp-lst)
         (second pp-lst)
         1)))
         (cons-with-hint (first pp-lst)
         (cons-with-hint (second pp-lst)
         (extract-equals-from-pp-lst (cddr pp-lst) limit)
         (cdr pp-lst))
         pp-lst))|#

         (rest (extract-equals-from-pp-lst (cdr pp-lst) limit))
         ((mv coef cur) (get-pp-and-coef (car pp-lst)))
         ((when (evenp coef))
          (cons-with-hint (first pp-lst)
                          rest
                          pp-lst))

         (cur (ex-from-rp$ cur))
         ((when (is-equals cur))
          (cons (create-times-instance coef (cadr cur)) rest))

         ((mv e-lst valid)
          (case-match cur (('and-list & ('list . lst)) (mv lst t))
            (& (mv nil nil))))
         ((unless (and valid
                       (extract-equals-from-pp-lst-precheck e-lst)))
          (cons-with-hint (car pp-lst) rest pp-lst))

         ((mv res-e-lst res-pp-lst)
          (extract-equals-from-pp-lst-aux e-lst))

         ((unless res-pp-lst)
          (cons-with-hint (car pp-lst) rest pp-lst))

         ((mv res-pp-lst2 valid)
          (cross-product-pp-aux-for-pp-lst res-pp-lst res-e-lst))
         ((unless valid)
          (cons-with-hint (car pp-lst) rest pp-lst))
         (res-pp-lst3 (extract-equals-from-pp-lst (append-with-times coef res-pp-lst2 nil)
                                                  (1- limit))))
      (pp-sum-merge-aux res-pp-lst3
                        rest)))

  ;; check if a matching pattern exists.
  (define check-if-clearable-equals-in-pp-lst (pp-lst)
    (b* (((when (atom pp-lst)) nil)
         ((mv coef cur) (get-pp-and-coef (car pp-lst)))
         (cur (ex-from-rp-loose cur))
         ((when (evenp coef)) (check-if-clearable-equals-in-pp-lst (cdr pp-lst)))
         ((when (is-equals cur)) t)
         ((mv e-lst valid)
          (case-match cur (('and-list & ('list . lst)) (mv lst t))
            (& (mv nil nil)))))
      (or (and valid
               (extract-equals-from-pp-lst-precheck e-lst))
          (check-if-clearable-equals-in-pp-lst (cdr pp-lst))))))

#|(define new-sum-merge-aux-dissect-term ((term rp-termp))
:inline t
:returns (mv (term-orig rp-termp :hyp (rp-termp term))
(abs-term-w/-sc rp-termp :hyp (rp-termp term))
(abs-term rp-termp :hyp (rp-termp term))
(negated booleanp))
(b* ((term-orig term)
((mv abs-term-w/-sc negated)
(case-match term-orig (('-- e) (mv e t)) (& (mv term-orig nil))))
(abs-term (ex-from-rp$ abs-term-w/-sc)))
(mv term-orig abs-term-w/-sc abs-term negated)))|#

#|(define new-sum-merge-aux-add-negated-coughed ((to-be-coughed-c-lst rp-term-listp)
(abs-term-w/-sc rp-termp)
negated)
:inline t
:returns (res-lst rp-term-listp :hyp (and (rp-term-listp to-be-coughed-c-lst)
(rp-termp abs-term-w/-sc)))
(if negated
(s-sum-merge-aux to-be-coughed-c-lst
(list `(-- ,abs-term-w/-sc)))
to-be-coughed-c-lst))|#

;;(include-book "pp-flatten-wrapper")



(defines has-more-than-one-var?
  (define has-more-than-one-var? (term)
    ;; second return value should be ignored. 
    :returns (mv result found-var) 
    (cond ((atom term)
           (mv nil term))
          ((quotep term)
           (mv nil nil))
          (t (has-more-than-one-var?-lst (cdr term)))))
  (define has-more-than-one-var?-lst (lst)
    :returns (mv result found-var)
    (if (atom lst)
        (mv nil nil)
      (b* (((mv result1 found-var1)
            (has-more-than-one-var? (car lst)))
           ((when result1)
            (mv result1 nil))
           ((mv result2 found-var2)
            (has-more-than-one-var?-lst (cdr lst))))
        (mv (or result2
                (and found-var1 found-var2
                     (not (equal found-var1 found-var2))))
            (or found-var1 found-var2))))))

(define has-s-c-buried-under-binary-fnc? (term
                                          &key
                                          (exclude-radix8+-cases 'exclude-radix8+-cases))
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((term (ex-from-rp term)))
    (cond ((binary-not-p term)
           (has-s-c-buried-under-binary-fnc? (cadr term)))
          ((or (binary-and-p term)
               (binary-or-p term)
               (binary-xor-p term))
           (or (has-s-c-buried-under-binary-fnc? (cadr term))
               (has-s-c-buried-under-binary-fnc? (caddr term))))
          ((binary-?-p term)
           (or (has-s-c-buried-under-binary-fnc? (cadr term))
               (has-s-c-buried-under-binary-fnc? (caddr term))
               (has-s-c-buried-under-binary-fnc? (cadddr term))))
          ((or (single-s-p term)
               (single-c-p term)
               (s-c-res-p term))
           (if exclude-radix8+-cases
               (b* (((mv has-more-than-one-var &)
                     (has-more-than-one-var? term)))
                 has-more-than-one-var)
             t)))))
        
           

(define new-sum-merge-aux ((sum-lst rp-term-listp)
                           (limit natp))
  :verify-guards nil
  :measure (acl2::nat-list-measure (list limit (len sum-lst)))
  :returns (mv (s) (pp-lst) (c-lst))
  (b* (((when (zp limit)) (mv ''nil sum-lst (raise "Limit ~
  reached. This is highly unexpected. Something must have gone wrong.")))
       ((when (atom sum-lst))
        (mv ''nil nil nil))
       ((mv s pp-lst c-lst)
        (new-sum-merge-aux (cdr sum-lst) limit))

       (term-orig (car sum-lst))
       ((mv coef term-w/-sc) (get-pp-and-coef term-orig))
       (term (ex-from-rp$ term-w/-sc))

       #|((mv term-orig term-w/-sc term negated)
       (new-sum-merge-aux-dissect-term (car sum-lst)))|#)
    (cond
     ((single-c-p term)
      (b* (;; Extra c's  may be  coughed here..  But probably  not complicating
           ;; things here is the best.
           (c-lst (s-sum-merge-aux c-lst (list term-orig)))
           )
        (mv s pp-lst c-lst)))
     ((single-s-p term)
      (b* ((s (s-sum-merge s (create-list-instance
                              (list term-orig)))))
        (mv s pp-lst c-lst)))
     ((single-s-c-res-p term)
      (b* (((mv s-arg pp-arg c-arg)
            (case-match term
              (('s-c-res s-arg pp-arg c-arg) (mv s-arg pp-arg c-arg))
              (& (mv ''nil ''nil ''nil)) ;; can never get here.
              ))
           ((mv s-arg-lst pp-arg-lst c-arg-lst)
            (mv (append-with-times coef (list-to-lst s-arg) nil)
                (append-with-times coef (list-to-lst pp-arg) nil)
                (append-with-times coef (list-to-lst c-arg) nil)))
           (s (s-sum-merge s (create-list-instance s-arg-lst)))
           (pp-lst (pp-sum-merge-aux pp-arg-lst pp-lst))
           (c-lst (s-sum-merge-aux c-lst c-arg-lst)))
        (mv s pp-lst c-lst)))
     ((sum-list-p term)
      (b* ((arg-pp (cadr term))
           (arg-pp-lst (append-with-times coef  (list-to-lst arg-pp) nil))
           ;;(arg-pp-lst (if (pp-lst-orderedp arg-pp-lst) arg-pp-lst (pp-sum-sort-lst arg-pp-lst)))

           ;; Below is likely unecessary. But doing it just in case.
           ((mv s-lst2 pp-lst2 c-lst2) (ex-from-pp-lst arg-pp-lst))
           (pp-lst (pp-sum-merge-aux pp-lst2 pp-lst))
           (s (s-sum-merge s (create-list-instance s-lst2)))
           (c-lst (s-sum-merge-aux c-lst c-lst2)))
        (mv s pp-lst c-lst)))
     ((and-list-p term)
      (b* ((pp-lst (pp-sum-merge-aux (list term-orig)  pp-lst)))
        (mv s pp-lst c-lst )))
     ((quote-p term)
      (b* ((pp-lst (pp-sum-merge-aux (list term-orig)  pp-lst)))
        (mv s pp-lst c-lst)))
     ((is-equals term)
      (b* (((mv s2 pp-lst2 c-lst2)
            (new-sum-merge-aux (list (cadr term)) (1- limit)))

           ((mv s2 pp-lst2 c-lst2)
            (mv (create-list-instance
                 (append-with-times coef (list-to-lst s2) nil))
                (append-with-times coef pp-lst2 nil)
                (append-with-times coef c-lst2 nil))))
        (mv (s-sum-merge s s2)
            (pp-sum-merge-aux pp-lst pp-lst2)
            (s-sum-merge-aux c-lst c-lst2))))
     ((pp-term-p term-w/-sc)
      (b* (;;(term (4vec->pp-term term))
           (pp-lst2 (pp-flatten-with-binds
                     term-w/-sc
                     :coef 1
                     :disabled (and*-exec (unpack-booth-later-enabled)
                                          (not (has-s-c-buried-under-binary-fnc?
                                                term-w/-sc
                                                :exclude-radix8+-cases t))
                                          (not
                                           (pp-is-a-part-of-radix8+-summation term-w/-sc)))))

           (pp-lst2 (append-with-times coef pp-lst2 nil))

           (?orig-pp-lst2 pp-lst2)
           ;;(pp-lst2 (extract-equals-from-pp-lst pp-lst2 *large-number*))

           #|(- (or (check-if-clearable-equals-in-pp-lst pp-lst2)
           (raise "?orig-pp-lst2: ~p0, pp-lst2: ~p1 ~%" orig-pp-lst2 pp-lst2)))|#

           ((mv s-lst2 pp-lst2 c-lst2) (ex-from-pp-lst pp-lst2))
           (s (s-sum-merge s (create-list-instance s-lst2)))
           (c-lst (s-sum-merge-aux c-lst c-lst2))

           ((mv s-lst2 pp-lst2 c-lst2) (cross-product-pp pp-lst2))
           (s (s-sum-merge s (create-list-instance s-lst2)))
           (c-lst (s-sum-merge-aux c-lst c-lst2))

           ((mv pp-lst2 recollected-c-lst) (recollect-pp-lst-to-sc-main pp-lst2))
           (c-lst (s-sum-merge-aux recollected-c-lst c-lst))
           (pp-lst (pp-sum-merge-aux pp-lst pp-lst2)))
        (mv s pp-lst c-lst)))
     ((binary-fnc-p term) ;; this can still be reached if some inner term
      ;; is not pp-term-p.
      (b* ((pp-lst (pp-sum-merge-aux (list term-orig)  pp-lst)))
        (mv s pp-lst c-lst)))
     ((--.p term)
      (b* (((mv s2 pp-lst2 c-lst2)
            (new-sum-merge-aux (list (cadr term)) (1- limit)))
           ((mv s2 pp-lst2 c-lst2)
            (mv (create-list-instance
                 (append-with-times (- coef) (list-to-lst s2) nil))
                (append-with-times (- coef) pp-lst2 nil)
                (append-with-times (- coef) c-lst2 nil))))
        (mv (s-sum-merge s s2)
            (pp-sum-merge-aux pp-lst pp-lst2)
            (s-sum-merge-aux c-lst c-lst2))))
     (t
      (progn$ (hard-error 'new-sum-merge-aux
                          "Unexpected term ~p0 ~%"
                          (list (cons #\0 term-w/-sc)))
              (mv `(cons ,term-orig ,s)
                  pp-lst
                  c-lst)))))
  ///
  (acl2::defret
   return-vals--of--<fn>
   :hyp (rp-term-listp sum-lst)
   (and (rp-termp s)
        (rp-term-listp pp-lst)
        (rp-term-listp c-lst))
   :hints (("Goal"
            :do-not-induct t
            :expand ((new-sum-merge-aux sum-lst limit)
                     (new-sum-merge-aux nil limit))
            :induct (new-sum-merge-aux sum-lst limit)
            :in-theory (e/d ((:induction new-sum-merge-aux))
                            ((:definition new-sum-merge-aux)
                             (:e tau-system)
                             (:rewrite default-car)
                             (:rewrite default-cdr)
                             (:rewrite rp-termp-implies-subterms))))))
  (verify-guards new-sum-merge-aux))

(define extract-from-equals-lst ((pp-lst rp-term-listp))
  :returns (mv (s) (res-pp-lst) (c-lst) changed)
  :verify-guards nil
  (if (atom pp-lst)
      (mv ''nil nil nil nil)
    (b* ((cur-orig (car pp-lst))
         (rest (cdr pp-lst))
         ((mv s1 pp-lst1 c-lst1 changed1)
          (extract-from-equals-lst rest))

         ((mv coef cur) (get-pp-and-coef cur-orig))
         (cur (ex-from-rp$ cur))

         ((mv s2 pp-lst2 c-lst2 changed2)
          (case-match cur
            (('equals & &)
             (b* (((mv s pp-lst c-lst)
                   (new-sum-merge-aux (list (cadr cur)) *large-number*)))
               (mv s pp-lst c-lst t)))
            (&
             (if (and (consp cur)
                      (or (equal (first cur) 's)
                          (equal (first cur) 'c)
                          (equal (first cur) 's-c-res)
                          (binary-fnc-p cur)))
                 (b* (((mv s pp-lst c-lst)
                       (new-sum-merge-aux (list cur) *large-number*)))
                   (mv s pp-lst c-lst t))
               (mv cur nil nil nil)))))
         ((mv s2 pp-lst2 c-lst2)
          (if changed2
              (mv (create-list-instance (append-with-times coef (list-to-lst s2) nil))
                  (append-with-times coef pp-lst2 nil)
                  (append-with-times coef c-lst2 nil)
                  )
            (mv s2 pp-lst2 c-lst2))))
      (cond ((and changed1 changed2)
             (mv (s-sum-merge s1 s2)
                 (pp-sum-merge-aux pp-lst1 pp-lst2)
                 (s-sum-merge-aux c-lst1 c-lst2)
                 t))
            (changed1
             (mv s1
                 (cons cur-orig pp-lst1)
                 c-lst1
                 t))
            (changed2
             (mv s2
                 (pp-sum-merge-aux rest pp-lst2)
                 c-lst2
                 t))
            (t (mv ''nil nil nil nil)))))
  ///
  (acl2::defret
   return-vals--of--<fn>
   :hyp (rp-term-listp pp-lst)
   (and (rp-termp s)
        (rp-term-listp res-pp-lst)
        (rp-term-listp c-lst)
        ))

  (verify-guards extract-from-equals-lst
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d () ())))))

(progn
  (encapsulate
    (((undo-rw-and-open-up-adders-enabled) => *))
    (local
     (defun undo-rw-and-open-up-adders-enabled ()
       nil)))

  (defmacro enable-undo-rw-and-open-up-adders (enable)
    (if enable
        `(defattach undo-rw-and-open-up-adders-enabled return-t)
      `(defattach undo-rw-and-open-up-adders-enabled return-nil)))

  (enable-undo-rw-and-open-up-adders nil))

(define new-sum-merge ((term rp-termp))
  :verify-guards t
  :returns (mv (s) (pp-lst) (c-lst))
  (b* ((sum-lst (extract-new-sum-consed term))
       ((mv s pp-lst c-lst)
        (new-sum-merge-aux sum-lst *large-number*))

       (pp-lst (if (check-if-clearable-equals-in-pp-lst pp-lst)
                   (b* ((- (cw "Undo-able adder is found. "))
                        ((unless (undo-rw-and-open-up-adders-enabled))
                         (progn$ (cw " However, undoing adder rw feature is disabled. See :doc rp::multiplier-verification-heuristics.~%")
                                 pp-lst))
                        (- (cw "Now, undoing rw and opening up some adders. If too slow, either disable this feature or reduce pp-lists-limit (see :doc rp::multiplier-verification-heuristics). ~%"))
                        (pp-lst (extract-equals-from-pp-lst pp-lst *large-number*))
                        (- (cw "Undoing rw (extract-equals-from-pp-lst) finished. ~%"))
                        #|(- (and (check-if-clearable-equals-in-pp-lst pp-lst)
                        (raise "pp-lst : ~p0 ~%" pp-lst)))|#
                        )
                     pp-lst)
                 pp-lst))

       ((mv s2 pp-lst2 c-lst2 changed2)
        (extract-from-equals-lst pp-lst))

       ((unless changed2)
        (mv s
            (if (pp-lst-orderedp pp-lst) pp-lst (pp-sum-sort-lst pp-lst))
            c-lst))
       )
    (mv (s-sum-merge s s2)
        (if (pp-lst-orderedp pp-lst2) pp-lst2 (pp-sum-sort-lst pp-lst2))
        (s-sum-merge-aux c-lst c-lst2)
        ))
  ///
  (acl2::defret
   return-vals--of--<fn>
   :hyp (rp-termp term)
   (and (rp-termp s)
        (rp-term-listp pp-lst)
        (rp-term-listp c-lst)
        )))

;; (progn
#|(define well-formed-new-sum ((term rp-termp))
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
((case-match x (('s-c-res & & &) t))
rest-res)
((case-match x (('sum-list &) t))
rest-res)
((equal x ''0)
rest-res)
(t
nil))))
(('quote x)
(integer-listp x))
(& nil))))||#

(progn
  (define light-pp-term-p ((term rp-termp))
    :inline t
    (or
     (has-bitp-rp term)
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
         (('logbit$inline & &)
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
               ((has-bitp-rp x-orig)
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

  (define quarternaryp-sum ((term rp-termp))
    :returns (mv (quarternaryp? booleanp)
                 (bitp? booleanp))
    (b* (((mv res valid)
          (quarternaryp-sum-aux term)))
      (mv (or (and valid
                   (quarternaryp res))
              #|(hard-error 'quarternarp-sum "term ~p0 ~%"
              (list (cons #\0 term)))||#)
          (and valid
               (bitp res))))))

#|(acl2::Defines
search-for-1
:hints (("Goal"
:in-theory (e/d (measure-lemmas) ())))
(define search-for-1 (term)
:measure (cons-count term)
(b* ((term (ex-from-rp term)))
(case-match term
(('s & pp c)
(or (and (consp (list-to-lst pp))
(equal (car (list-to-lst pp)) ''1))
(search-for-1-lst (list-to-lst c))))
(('s-c-res s & c)
(or (search-for-1-lst (list-to-lst s))
(search-for-1-lst (list-to-lst c))))
(('c & s pp c)
(or (and (consp (list-to-lst pp))
(equal (car (list-to-lst pp)) ''1))
(search-for-1-lst (list-to-lst s))
(search-for-1-lst (list-to-lst c))))
(& nil))))
(define search-for-1-lst (lst)
:measure (cons-count lst)
(if (atom lst)
nil
(or (search-for-1 (car lst))
(search-for-1-lst (cdr lst))))))||#

#|(rp::and-list-to-binary-and '(RP::AND-LIST '327716
(LIST (RP::LOGBIT OP1_LO '15)
(RP::LOGBIT OP2_LO '31))))||#

(define s-spec-meta-aux ((s rp-termp)
                         (pp-lst rp-term-listp)
                         (c-lst rp-term-listp))
  :verify-guards t
  :returns (res rp-termp
                :hyp (and (rp-termp s)
                          (rp-term-listp pp-lst)
                          (rp-term-listp c-lst)))
  (b* (((mv pp-lst c-lst) (s-of-s-fix-lst (list-to-lst s)
                                          pp-lst
                                          c-lst))
       #| (pp-lst-before-clean pp-lst)||#
       (c-lst (s-fix-pp-args-aux c-lst))

       (pp-lst (s-fix-pp-args-aux pp-lst))
       (pp (create-list-instance pp-lst))
       (c (create-list-instance c-lst))

       ((mv res-s-lst res-pp-lst res-c-lst) (create-s-instance pp c)))
    (create-s-c-res-instance res-s-lst res-pp-lst res-c-lst t)))

(define c-spec-meta-aux ((arg-s rp-termp)
                         (arg-pp-lst rp-term-listp)
                         (arg-c-lst rp-term-listp)
                         (quarternaryp booleanp))
  :returns (res rp-termp
                :hyp (and (rp-termp arg-s)
                          (rp-term-listp arg-pp-lst)
                          (rp-term-listp arg-c-lst)))
  :verify-guards t
  :prepwork ((local
              (in-theory (disable natp))))
  (b* ((arg-s-lst (list-to-lst arg-s))

       ((mv arg-pp-lst arg-c-lst coughed-s-lst2 coughed-pp-lst2 to-be-coughed-c-lst)
        (c-of-s-fix-lst arg-s-lst arg-pp-lst arg-c-lst nil))

       ((mv coughed-c-lst-from-args arg-c-lst)
        (c-fix-arg-aux arg-c-lst))
       (to-be-coughed-c-lst (s-sum-merge-aux to-be-coughed-c-lst coughed-c-lst-from-args))

       ((mv coughed-pp-lst arg-pp-lst)
        (c-fix-arg-aux arg-pp-lst))

       ((mv arg-s-lst arg-pp-lst arg-c-lst
            coughed-s-lst coughed-pp-lst to-be-coughed-c-lst)
        (c-pattern3-reduce nil arg-pp-lst arg-c-lst
                           nil coughed-pp-lst to-be-coughed-c-lst))

       ((mv merged-s-lst merged-pp-lst merged-c-lst)
        (create-c-instance arg-s-lst arg-pp-lst arg-c-lst))

       (coughed-s-lst (s-sum-merge-aux coughed-s-lst merged-s-lst))
       (coughed-s-lst (s-sum-merge-aux coughed-s-lst coughed-s-lst2))
       (coughed-pp-lst (pp-sum-merge-aux coughed-pp-lst merged-pp-lst))
       (coughed-pp-lst (pp-sum-merge-aux coughed-pp-lst2
                                         coughed-pp-lst))

       ((when (not to-be-coughed-c-lst))
        (create-s-c-res-instance coughed-s-lst coughed-pp-lst
                                 merged-c-lst quarternaryp))

       (merged-c-lst (s-sum-merge-aux to-be-coughed-c-lst merged-c-lst))

       (res (create-s-c-res-instance coughed-s-lst coughed-pp-lst merged-c-lst
                                     quarternaryp)))
    res))

(progn
  (define extract-binary-xor-for-s-spec-aux ((term rp-termp))
    :returns (res rp-termp
                  :hyp (rp-termp term))
    (case-match term
      (('binary-xor x y)
       `(binary-sum ,(extract-binary-xor-for-s-spec-aux x)
                    ,(extract-binary-xor-for-s-spec-aux y)))
      (('binary-not x)
       `(binary-sum '1
                    ,(extract-binary-xor-for-s-spec-aux x)))
      (& term)))

  (define extract-binary-xor-for-s-spec-aux-lst ((lst rp-term-listp))
    :returns (res-lst rp-term-listp
                      :hyp (rp-term-listp lst))
    (if (atom lst)
        lst
      (cons-with-hint (if (pp-term-p (car lst))
                          (extract-binary-xor-for-s-spec-aux (car lst))
                        (car lst))
                      (extract-binary-xor-for-s-spec-aux-lst (cdr lst))
                      lst)))

  (define extract-binary-xor-for-s-spec ((term rp-termp))
    :returns (res rp-termp
                  :hyp (rp-termp term))
    (case-match term
      (('cons x rest)
       (b* ((x-orig x)
            (x (ex-from-rp$ x)))
         (if (and (consp x)
                  (or (equal (car x) 'binary-xor)
                      (equal (car x) 'binary-not))
                  (pp-term-p x))
             `(cons ,(extract-binary-xor-for-s-spec-aux x)
                    ,(extract-binary-xor-for-s-spec rest))
           `(cons ,x-orig ,(extract-binary-xor-for-s-spec rest)))))
      (& term))))

(define s-c-spec-meta ((term rp-termp))
  :returns (mv (res rp-termp
                    :hyp (rp-termp term))
               (dont-rw dont-rw-syntaxp))
  :prepwork ((local
              (defthm lemma1
                (IS-RP (LIST 'RP ''BITP x))
                :hints (("Goal"
                         :in-theory (e/d (is-rp) ()))))))
  :verify-guards t
  (b* ((result
        (case-match term
          (('s-c-spec sum)
           (b* (((mv s pp-lst c-lst);;(mv s pp c)
                 (new-sum-merge sum))

                ((mv quarternaryp ?bitp) (quarternaryp-sum sum))

                (s-res (if bitp
                           (create-s-c-res-instance (list-to-lst s)
                                                    pp-lst
                                                    c-lst
                                                    t)
                         (s-spec-meta-aux s pp-lst c-lst)))
                (c-res (if bitp ''0
                         (c-spec-meta-aux s pp-lst c-lst quarternaryp)))
                ;;(- (if (< (cons-count s-res) 40) (cw "s-res is ~p0 and c-res is  ~p1 and input ~p2 ~%~%~%" s-res c-res term) nil))
                (res `(cons ,s-res (cons ,c-res 'nil))))
             res))
          (('c-s-spec sum)
           (b* (((mv s pp-lst c-lst);;(mv s pp c)
                 (new-sum-merge sum))
                ((mv quarternaryp ?bitp) (quarternaryp-sum sum))
                (s-res (if bitp (create-s-c-res-instance (list-to-lst s)
                                                         pp-lst
                                                         c-lst
                                                         t)
                         (s-spec-meta-aux s pp-lst c-lst)))
                (c-res (if bitp
                           ''0
                         (c-spec-meta-aux s pp-lst c-lst quarternaryp))))
             `(cons ,c-res (cons ,s-res 'nil))))
          (('s-spec sum)
           (b* (((mv ?quarternaryp ?bitp) (quarternaryp-sum sum))
                (sum (if bitp ;; when bitp, we'll want things to be coughed out
                         ;; as is so don't try to prematurely flatten
                         ;; binary-xors in such cases.
                         sum
                       (extract-binary-xor-for-s-spec sum)))
                ((mv s pp-lst c-lst)
                 (new-sum-merge sum)))
             (if bitp
                 (create-s-c-res-instance (list-to-lst s)
                                          pp-lst
                                          c-lst
                                          t)
               (s-spec-meta-aux s pp-lst c-lst))))
          (('c-spec sum)
           (b* (((mv s pp-lst c-lst)
                 (new-sum-merge sum))
                ((mv quarternaryp ?bitp) (quarternaryp-sum sum)))
             (if bitp
                 ''0
               (c-spec-meta-aux s pp-lst c-lst quarternaryp))))
          (& term))))
    (mv result t))
  ///
  (profile 's-c-spec-meta))

#|

(s-spec-meta `(s-spec (cons (binary-and (logbit a 0) (logbit b 0))
(cons (binary-or (binary-and (logbit a 0) (logbit b 0))
(binary-and (logbit a 0) (logbit b 0)))
(cons (binary-and (logbit a 0) (logbit b 0))
(cons (binary-and (logbit a 1) (logbit
b 0))
'nil
))))))
||#
;;;;;;;;;;;;;;;;;;;;
