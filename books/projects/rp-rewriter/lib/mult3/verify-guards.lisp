

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

(include-book "summation-tree-meta-fncs")

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arith-5
  :disabled t))

(progn
  (define lte (a b)
    :verify-guards nil
    (<= a b)
    ///
    (defthm rw-<=-to-lte
      (equal (<= a b)
             (lte a b))))

  (define lt (a b)
    :verify-guards nil
    (< a b)
    ///
    (defthm rw-<-to-lte
      (equal (< a b)
             (lt a b))))

  (define gt (a b)
    :verify-guards nil
    (> a b)
    ///
    (defthm rw->-to-gt
      (equal (> a b)
             (gt a b))))

  (define gte (a b)
    :verify-guards nil
    (>= a b)
    ///
    (defthm rw->=-to-gte
      (equal (>= a b)
             (gte a b))))

  (deftheory rw-dir1
    '(rw-<-to-lte
      rw->=-to-gte
      rw->-to-gt
      rw-<=-to-lte))

  (deftheory rw-dir2
    '(lt lte gte gt)))

(local
 (defthm ex-from-rp-loose-of-ex-from-rp
   (equal (ex-from-rp (ex-from-rp term))
          (ex-from-rp term))
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp ex-from-rp
                                        is-rp
                                        is-rp)
                            ())))))

(local
 (defthmd ex-from-rp-and-count-c-1
   (and (equal (count-c (ex-from-rp c1))
               (count-c c1)))
   :hints (("Goal"
            :expand (count-c (ex-from-rp c1))
            :do-not-induct t
            :in-theory (e/d (count-c
                             count-c-lst)
                            ())))))

(local
 (defthmd ex-from-rp-and-count-c-1-reverse
   (implies (syntaxp (atom c1))
            (and (equal (count-c c1)
                        (count-c (ex-from-rp c1)))))
   :hints (("Goal"
            :expand (count-c (ex-from-rp c1))
            :do-not-induct t
            :in-theory (e/d (count-c
                             count-c-lst)
                            ())))))

(local
 (defthm ex-from-rp-and-count-c-2
   (implies (and (equal (ex-from-rp c1)
                        (ex-from-rp c2))
                 (syntaxp (Not (lexorder c1 c2))))
            (equal (count-c c1)
                   (count-c c2)))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d (ex-from-rp-and-count-c-1-reverse) ())))))

(local
 (defthmd  count-c-when-rp-equal-lemma
   (implies (equal (car term) 'list)
            (equal (ex-from-rp term)
                   term))
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp is-rp) ())))))

;; (Local
;;  (defthm count-c-when-rp-equal-2
;;    (and (implies (and (RP-EQUAL TERM1 TERM2)
;;                       (SINGLE-C-P (EX-FROM-RP TERM1)))
;;                  (SINGLE-C-P (EX-FROM-RP TERM2))))
;;    :rule-classes :forward-chaining
;;    :hints (("Goal"
;;             :expand ((RP-EQUAL TERM1 TERM2))
;;             :in-theory (e/d (SINGLE-C-P)
;;                             (RP-EQUAL))))))

;; (Local
;;  (defthm count-c-when-rp-equal-2.5
;;    (and (implies (and (RP-EQUAL TERM1 TERM2)
;;                       (not (SINGLE-C-P (EX-FROM-RP TERM1))))
;;                  (not (SINGLE-C-P (EX-FROM-RP TERM2)))))
;;    :rule-classes :forward-chaining
;;    :hints (("Goal"
;;             :expand ((RP-EQUAL TERM1 TERM2))
;;             :in-theory (e/d (SINGLE-C-P)
;;                             (RP-EQUAL))))))

;; (Local
;;  (defthm count-c-when-rp-equal-3
;;    (implies (and (RP-EQUAL TERM1 TERM2)
;;                  (SINGLE-s-P (EX-FROM-RP TERM1)))
;;             (SINGLE-s-P (EX-FROM-RP TERM2)))
;;    :rule-classes :forward-chaining
;;    :hints (("Goal"
;;             :expand ((RP-EQUAL TERM1 TERM2))
;;             :in-theory (e/d (SINGLE-s-P)
;;                             (RP-EQUAL))))))

;; (Local
;;  (defthm count-c-when-rp-equal-3.5
;;    (and (implies (and (RP-EQUAL TERM1 TERM2)
;;                       (not (SINGLE-s-P (EX-FROM-RP TERM1))))
;;                  (not (SINGLE-s-P (EX-FROM-RP TERM2)))))
;;    :rule-classes (:forward-chaining :rewrite)
;;    :hints (("Goal"
;;             :expand ((RP-EQUAL TERM1 TERM2))
;;             :in-theory (e/d (SINGLE-s-P)
;;                             (RP-EQUAL))))))

;; (Local
;;  (defthm count-c-when-rp-equal-4
;;    (implies (and (RP-EQUAL TERM1 TERM2)
;;                  (syntaxp (not (lexorder term1 term2))))
;;             (and (iff (CONSP (EX-FROM-RP TERM1))
;;                       (CONSP (EX-FROM-RP TERM2)))))
;;    :rule-classes :forward-chaining
;;    :hints (("Goal"
;;             :expand ((RP-EQUAL TERM1 TERM2))
;;             :in-theory (e/d ()
;;                             (RP-EQUAL))))))

;; (Local
;;  (defthm count-c-when-rp-equal-5
;;    (implies (and (RP-EQUAL TERM1 TERM2))
;;             (EQUAL (CAR (EX-FROM-RP TERM1))
;;                    (CAR (EX-FROM-RP TERM2))))
;;    :rule-classes :forward-chaining
;;    :hints (("Goal"
;;             :expand ((RP-EQUAL TERM1 TERM2))
;;             :in-theory (e/d ()
;;                             (RP-EQUAL))))))

;; (Local
;;  (defthm count-c-when-rp-equal-6
;;    (implies (and (RP-EQUAL TERM1 TERM2))
;;             (RP-EQUAL-SUBTERMS (CDR (EX-FROM-RP TERM1))
;;                                (CDR (EX-FROM-RP TERM2))))
;;    :rule-classes :forward-chaining
;;    :hints (("Goal"
;;             :expand ((RP-EQUAL TERM1 TERM2))
;;             :in-theory (e/d ()
;;                             (RP-EQUAL))))))

;; (Local
;;  (defthm count-c-when-rp-equal-7
;;    (implies (and (RP-EQUAL TERM1 TERM2)
;;                  (single-s-p (EX-FROM-RP TERM1)))
;;             (and (rp-equal (car (cdddr (EX-FROM-RP TERM1)))
;;                            (car (cdddr (EX-FROM-RP TERM2))))))

;;    :rule-classes :forward-chaining
;;    :hints (("Goal"
;;             :expand ((RP-EQUAL TERM1 TERM2))
;;             :in-theory (e/d ()
;;                             (RP-EQUAL))))))

;; (Local
;;  (defthm count-c-when-rp-equal-8
;;    (implies (and (RP-EQUAL TERM1 TERM2)
;;                  (single-c-p (EX-FROM-RP TERM1)))
;;             (and (rp-equal (car (cddddr (EX-FROM-RP TERM1)))
;;                            (car (cddddr (EX-FROM-RP TERM2))))))

;;    :rule-classes :forward-chaining
;;    :hints (("Goal"
;;             :expand ((RP-EQUAL TERM1 TERM2))
;;             :in-theory (e/d ()
;;                             (RP-EQUAL))))))

;; (local
;;  (defthm-rp-equal-cnt
;;    (defthm count-c-when-rp-equal
;;      (implies (rp-equal-cnt term1 term2 cnt)
;;               (equal (count-c term1)
;;                      (count-c term2)))
;;      :flag rp-equal-cnt)
;;    (defthm count-c-lst-when-rp-equal-subterms
;;      (implies (rp-equal-cnt-subterms subterm1 subterm2 cnt)
;;               (equal (count-c-lst subterm1)
;;                      (count-c-lst subterm2)))
;;      :flag rp-equal-cnt-subterms)
;;    :hints (("Goal"
;;             :expand ((RP-EQUAL-SUBTERMS SUBTERM1 SUBTERM2)
;;                      (COUNT-C (EX-FROM-RP TERM1))
;;                      (COUNT-C (EX-FROM-RP TERM2)))
;;             :do-not-induct t
;;             :in-theory (e/d (ex-from-rp-and-count-c-1-reverse
;;                              count-c-when-rp-equal-lemma
;;                              count-c-lst
;;                              count-c)
;;                             (RP-EQUAL-IS-SYMMETRIC
;;                              count-c-when-rp-equal-7
;;                              count-c-when-rp-equal-8
;;                              rp-equal-subterms
;;                              rp-equal
;;                              RP-EQUAL-SUBTERMS-IS-SYMMETRIC)))
;;            ("Subgoal *1/10"
;;             :use ((:instance count-c-when-rp-equal-7)
;;                   (:instance count-c-when-rp-equal-8))))))

(local
 (std::defret
  measure-lemma-of-cough-duplicates
  ;; (equal (+ (count-c-lst coughed-lst)
  ;;           (count-c-lst coughed-lst)
  ;;           (count-c-lst res-lst))
  ;;        (count-c-lst lst))
  (and #|(implies (consp lst)
   (and (lt (count-c-lst COUGHED-LST)
   (count-c-lst lst))
   (not (gte (count-c-lst COUGHED-LST)
   (count-c-lst lst)))))||#
   (lte (count-c-lst COUGHED-LST)
        (count-c-lst lst))
   (not (gt (count-c-lst COUGHED-LST)
            (count-c-lst lst)))
   (lte (count-c-lst RES-LST)
        (count-c-lst lst))
   (not (gt (count-c-lst RES-LST)
            (count-c-lst lst)))
   (lte (+ (count-c-lst COUGHED-LST)
           (count-c-lst RES-LST))
        (count-c-lst lst))
   (not (gt (+ (count-c-lst COUGHED-LST)
               (count-c-lst RES-LST))
            (count-c-lst lst))))
  :fn COUGH-DUPLICATES
  :hints (("Goal"
           :do-not-induct t
           :induct (COUGH-DUPLICATES lst)
           :in-theory (e/d (COUNT-C-LST
                            rw-dir2
                            COUGH-DUPLICATES)
                           (rw-dir1))))))

(local
 (defthm ex-from-rp-loose-of-cons
   (implies (not (equal fnc 'rp))
            (equal (ex-from-rp (cons fnc rest))
                   (cons fnc rest)))
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp
                             is-rp)
                            ())))))

(set-ignore-ok t)
(local
 (make-event
  (b* ((count-c-formula (meta-extract-formula 'count-c state))
       (count-c-formula (caddr count-c-formula)))
    `(defthm count-c-when-c-instance
       (equal (count-c (cons 'c args))
              (let ((term (cons 'c args)))
                ,count-c-formula))
       :hints (("Goal"
                :in-theory (e/d (count-c) ())))))))

(local
 (defthm count-c-when-quoted
   (equal (count-c (cons 'quote rest))
          0)
   :hints (("Goal"
            :expand ((count-c (cons 'quote rest))
                     (ex-from-rp (CONS 'QUOTE REST)))
            :in-theory (e/d (count-c
                             single-c-p
                             single-s-p)
                            ())))))


(local
 (defthm local-measure-lemma-1
   (implies (and (acl2-numberp a)
                 (acl2-numberp b))
            (and (equal (< (1+ a) (1+ b))
                        (< a b))
                 (equal (lt (1+ a) (1+ b))
                        (lt a b))
                 (equal (> (1+ a) (1+ b))
                        (> a b))
                 (equal (gt (1+ a) (1+ b))
                        (gt a b))
                 (equal (> (+ a 1) (+ b 1))
                        (> a b))
                 (equal (gt (+ a 1) (+ b 1))
                        (gt a b))
                 (equal (< (+ a 1) (+ b 1))
                        (< a b))
                 (equal (lt (+ a 1) (+ b 1))
                        (lt a b))
                 (equal (<= (1+ a) (1+ b))
                        (<= a b))
                 (equal (lte (1+ a) (1+ b))
                        (lte a b))
                 (equal (>= (1+ a) (1+ b))
                        (>= a b))
                 (equal (gte (1+ a) (1+ b))
                        (gte a b))))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2
                             (:REWRITE ACL2::|(+ y x)|)
                             (:REWRITE ACL2::|(equal (if a b c) x)|)
                             (:REWRITE ACL2::EQUAL-OF-PREDICATES-REWRITE))
                            (rw-dir1))))))



(local
 (defthm local-measure-lemma-2
   (and (implies (and (<= a b)
                      (<= b c))
                 (<= a c))
        (implies (and (lte a b)
                      (lte b c))
                 (and (lte a c)
                      (not (gt a c))))
        (implies (and (gte a b)
                      (gte b c))
                 (and (gte a c)
                      (not (lt a c))))
        (implies (and (lt a b)
                      (lte b c))
                 (and (lt a c)
                      (not (gte a c))))
        (implies (and (lte a b)
                      (lt b c))
                 (and (not (gte a c))
                      (lt a c))))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2)
                            (rw-dir1))))
   ))

(local
 (defthm local-measure-lemma-4
   (and (lte a a)
        (gte a a)
        (not (gt a a))
        (not (lt a a)))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2)
                            (rw-dir1))))))

(local
 (defthm count-c-lst-when-not-conp
   (implies (atom x)
            (equal (count-c-lst x)
                   0))
   :hints (("Goal"
            :in-theory (e/d (count-c-lst) ())))))

(local
 (std::defret
  measure-lemma-of-SWAP-C-LSTS
  (and (equal (+ (count-c-lst res1)
                 (count-c-lst res2))
              (+ (count-c-lst c1-lst)
                 (count-c-lst c2-lst)))
       (equal (+ (count-c-lst res2)
                 (count-c-lst res1))
              (+ (count-c-lst c1-lst)
                 (count-c-lst c2-lst)))
       (implies (not res1)
                (equal (count-c-lst res2)
                       (+ (count-c-lst c1-lst)
                          (count-c-lst c2-lst))))
       (implies (not res2)
                (equal (count-c-lst res1)
                       (+ (count-c-lst c1-lst)
                          (count-c-lst c2-lst)))))
  :fn SWAP-C-LSTS
  :hints (("Goal"
           :in-theory (e/d (SWAP-C-LSTS) ())))))

(local
 (std::defret measure-lemma-of-s-sum-merge-aux
              (and (lte (count-c-lst merged-s-lst)
                        (+ (count-c-lst s1-lst)
                           (count-c-lst s2-lst)))
                   (not (gt (count-c-lst merged-s-lst)
                            (+ (count-c-lst s1-lst)
                               (count-c-lst s2-lst))))
                   (<= (count-c-lst merged-s-lst)
                       (+ (count-c-lst s1-lst)
                          (count-c-lst s2-lst))))
              :fn S-SUM-MERGE-AUX
              :hints (("Goal"
                       :in-theory (e/d (rw-dir2
                                        COUNT-C-LST
                                        S-SUM-MERGE-AUX)
                                       (rw-dir1))))))

(local
 (defthm local-measure-lemma-5
   (and (implies (and (lte a b)
                      (lte b c)
                      (lte c d))
                 (and (lte a d)
                      (not (gt a d)))))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2) (rw-dir1))))))

(local
 (defthm local-measure-lemma-6
   (implies (consp c1-lst)
            (LTE (+ (COUNT-C-LST C2-LST)
                    (COUNT-C (CAR C1-LST)))
                 (+ (COUNT-C-LST C1-LST)
                    (COUNT-C-LST C2-LST))))
   :hints (("Goal"
            :expand (COUNT-C-LST C1-LST)
            :in-theory (e/d (rw-dir2 count-c-lst) (rw-dir1))))))
(local
 (defthm dummy-lemma1
   (implies (and (natp a)
                 (natp b))
            (and
             (lte a
                  (+ a b))
             (lte b
                  (+ a b))))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2) (rw-dir1))))))

#|(local
 (defthm gt-to-not-lte
   (and (equal (gt a b)
               (not (lte a b)))
        (equal (gte a b)
               (not (lt a b))))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2) (rw-dir1))))))||#

;; (local
;;  (defthm bind-free-test
;;    (implies (and (

(local
 (defthm dummy-lemma2
   (implies (and (consp C1-LST)
                 (acl2-numberp c))
            (equal (gt (+ (COUNT-C-LST C1-LST) b)
                       (+ (COUNT-C-LST (cdr C1-LST)) c))
                   (gt (+ (COUNT-C (car C1-LST)) b)
                       c)))
   :hints (("Goal"
            :use ((:instance ACL2::SIMPLIFY-SUMS-<
                             (ACL2::X (COUNT-C-lst (cdr C1-LST)))
                             (ACL2::RHS (+ (COUNT-C (car C1-LST)) b))
                             (ACL2::LHS c)))
            :Expand (COUNT-C-LST C1-LST)
            :in-theory (e/d (rw-dir2)
                            (rw-dir1))))))

(local
 (defthm dummy-lemma3
   (implies (and (lte a b)
                 (ACL2-NUMBERP a)
                 (ACL2-NUMBERP b)
                 (lte b a))
            (equal a b))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (rw-dir2) (rw-dir1))))))

(local
 (defthm dummy-lemma4
   (implies (and (lte a b)
                 (NOT (lte b a)))
            (LT a b))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (rw-dir2) (rw-dir1))))))

#|(local
 (defthm local-measure-lemma-3
   (and (equal (not (gte a b))
               (lt a b))
        (equal (equal (gte a b) nil)
               (lt a b))
        (equal (iff (gte a b) nil)
               (lt a b))
        (equal (if (gte a b) nil t)
               (lt a b))
        (iff (not (gte a b))
             (lt a b))

        (equal (not (lte a b))
               (gt a b))
        (equal (if (lte a b) nil t)
               (gt a b))
        (iff (not (lte a b))
             (gt a b))

        (equal (not (lt a b))
               (gte a b))
        (equal (if (lt a b) nil t)
               (gte a b))
        (iff (not (lt a b))
             (gte a b))

        ;; (equal (gt a b)
        ;;        (not (lte a b)))

        ;; (equal (gte a b)
        ;;        (not (lt a b)))

        (equal (not (gt a b))
               (lte a b))
        (equal (equal (gt a b) nil)
               (lte a b))
        (equal (iff (gt a b) nil)
               (lte a b))
        (equal (if (gt a b) nil t)
               (lte a b))
        (iff (not (gt a b))
             (lte a b))
        (equal (or (gt a b) c)
               (or (not (lte a b)) c))
        )
   :hints (("Goal"
            :in-theory (e/d (rw-dir2)
                            (rw-dir1))))))||#

(local
 (defthm local-measure-lemma-3-2
   (AND (IMPLIES (ACL2::rewriting-positive-literal `(lt ,a ,b))
                 (equal (lt a b)
                        (NOT (gte a b))))
        (IMPLIES (ACL2::rewriting-positive-literal `(Gt ,a ,b))
                 (equal (gt a b)
                        (NOT (lte a b))))
        (IMPLIES (ACL2::rewriting-positive-literal `(gte ,a ,b))
                 (equal (gte a b)
                        (NOT (gt b a))))
        (IMPLIES (ACL2::rewriting-positive-literal `(lte ,a ,b))
                 (equal (lte a b)
                        (NOT (gt a b)))))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2)
                            (rw-dir1))))))

(local
 (defthm dummy-lemma-5
   (implies (ACL2-NUMBERP B)
            (and (equal (lte (+ b a)
                             (+ c d a))
                        (lte b
                             (+ c d)))
                 (equal (lte (+ a b)
                             (+ c d a))
                        (lte b
                             (+ c d)))))
   :hints (("Goal"
            :use ((:instance ACL2::SIMPLIFY-SUMS-<
                             (ACL2::X a)
                             (ACL2::RHS (+ c d))
                             (ACL2::LHS b)))
            :in-theory (e/d (rw-dir2) (rw-dir1))))))

(defthm lte-and-gte-implies
  (and (implies (lt x y)
                (and (lte x y)
                     (not (gt x y))))
       (implies (gt x y)
                (and (gte x y)
                     (not (gt y x)))))
  :hints (("Goal"
           :in-theory (e/d (rw-dir2) (rw-dir1)))))

(local
 (defthm expand-count-c-lst-when-consp
   (implies (consp x)
            (equal (count-c-lst x)
                   (+ (count-c (car x))
                      (count-c-lst (cdr x)))))
   :hints (("Goal"
            :expand (count-c-lst x)
            :in-theory (e/d () ())))))

(local
 (defthm count-c-of-quoted
   (implies (EQUAL (CAR SINGLE-C1) 'QUOTE)
            (equal (COUNT-C SINGLE-C1)
                   0))
   :hints (("Goal"
            :in-theory (e/d (count-c) ())))))

(local
 (defthm dummy-lemma-6
   (NOT (GT (COUNT-C-LST C2-LST)
            (+ 1 (COUNT-C-LST C2-LST))))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2) (rw-dir1))))))

(local
 (defthm dummy-lemma-7
   (implies (acl2-numberp m)
            (and (equal (lte (+ x a y)
                             (+ a m))
                        (lte (+ x y)
                             m))
                 (equal (lte (+ x y a)
                             (+ a m))
                        (lte (+ x y)
                             m))
                 (equal (gt (+ a m)
                            (+ x y a))
                        (gt m
                            (+ x y)))))
   :hints (("Goal"
            :use ((:instance ACL2::SIMPLIFY-SUMS-<
                             (ACL2::X a)
                             (ACL2::rHS (+ x y))
                             (ACL2::lHS m))
                  (:instance ACL2::SIMPLIFY-SUMS-<
                             (ACL2::X a)
                             (ACL2::lHS (+ x y))
                             (ACL2::rHS m)))
            :in-theory (e/d (rw-dir2) (rw-dir1))))))



(progn
  (local
   (defthm count-c-GET-C-ARGS-1
     (and
      (implies (and (MV-NTH 4 (GET-C-ARGS SINGLE-C1))
                    ;;(case-split (not (equal (ex-from-rp SINGLE-C1) ''0)))
                    )
               (equal (COUNT-C-LST (MV-NTH 3 (GET-C-ARGS SINGLE-C1)))
                      (1- (count-c SINGLE-C1)))))
     :hints (("Goal"
              :do-not-induct t
              :expand (COUNT-C SINGLE-C1)
              :in-theory (e/d (GET-C-ARGS
                               SINGLE-C-P
                               SINGLE-s-P)
                              ())))))

  #|(local
  (defthm count-c-GET-C-ARGS-2
  (and
  (implies (and (MV-NTH 4 (GET-C-ARGS SINGLE-C1))
  (CONSP (MV-NTH 1 (GET-C-ARGS SINGLE-C1)))
  (EQUAL (CAR (MV-NTH 1 (GET-C-ARGS SINGLE-C1)))
  'LIST))
  (equal (COUNT-C-LST (MV-NTH 3 (GET-C-ARGS SINGLE-C1)))
  (1- (count-c SINGLE-C1)))))
  :hints (("Goal"
  :do-not-induct t
  :expand (COUNT-C SINGLE-C1)
  :in-theory (e/d (GET-C-ARGS
  SINGLE-C-P
  SINGLE-s-P)
  ())))))||#

  #| (local
  (defthm GET-C-ARGS-lemma1
  (implies (EQUAL (EX-FROM-RP SINGLE-C1) ''0)
  (equal (GET-C-ARGS SINGLE-C1)
  (MV 0 ''NIL ''NIL NIL 'C)))
  :hints (("Goal"
  :in-theory (e/d (GET-C-ARGS) ())))))||#)

(local
 (defthm c-sum-merge-nil-lemma
   (equal (C-SUM-MERGE NIL arg2
                       :AUTO-SWAP T
                       :CLEAN-C1-LST NIL)
          (LIST* ''NIL NIL ARG2 '(NIL)))
   :hints (("Goal"
            :expand ((SWAP-C-LSTS NIL ARG2 T)
                     (C-SUM-MERGE NIL arg2
                                  :AUTO-SWAP T
                                  :CLEAN-C1-LST NIL)
                     (C-SUM-MERGE-AUX NIL ARG2
                                      :CLEAN-C1-LST NIL)
                     (C-SUM-MERGE-AUX ARG2 NIL
                                      :CLEAN-C1-LST NIL))
            :in-theory (e/d () ())))))

;; (local
;;  (defthm SINGLE-C-TRY-MERGE-PARAMS-lemma
;;    (equal (SINGLE-C-TRY-MERGE-PARAMS s-lst
;;                                      0 ''NIL
;;                                      ''NIL
;;                                      NIL)

(local
 (defthm dummy-lemma-8
   (equal (lte a (+ -2 b))
          (lte (+ a 2) b))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2) (rw-dir1))))))

(local
 (defthm dummy-lemma-9
   (implies (and (MV-NTH 4 (GET-C-ARGS SINGLE-C2)))
            (consp single-c2))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (GET-C-ARGS) ())))))

(local
 (defthm dummy-lemma-10
   (implies (acl2-numberp b)
            (and (equal (lte (+ 2 a x)
                             (+ x b))
                        (lte (+ 2 a)
                             b))
                 (equal (gt (+ 2 a x)
                            (+ x b))
                        (gt (+ 2 a)
                            b))
                 (equal (gte (+ 2 a x)
                             (+ x b))
                        (gte (+ 2 a)
                             b))
                 (equal (lt (+ 2 a x)
                            (+ x b))
                        (lt (+ 2 a)
                            b))))
   :hints (("Goal"
            :use ((:instance ACL2::SIMPLIFY-SUMS-<
                             (ACL2::X x)
                             (ACL2::RHS (+ 2 a))
                             (ACL2::LHS b))
                  (:instance ACL2::SIMPLIFY-SUMS-<
                             (ACL2::X x)
                             (ACL2::LHS (+ 2 a))
                             (ACL2::RHS b)))
            :in-theory (e/d (rw-dir2) (rw-dir1))))))

(local
 (defthm dummy-lemma-11
   (implies (lte a (1+ b))
            (lte a (+ 2 b)))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2) (rw-dir1))))))

;; (local
;;  (defthm dummy-lemma-12
;;    (implies (lte a b)
;;             (not (lte b a)))

(progn

  (local
   (define lte-chain-smart-fn-aux (cl a d)
     (if (or (atom cl)
             )
         (mv nil nil)
       (b* ((cur (car cl))
            ((mv rest-b rest-c)
             (lte-chain-smart-fn-aux (cdr cl) a d))
            ((unless (case-match cur (('not &) t)))
             (mv rest-b rest-c))
            (cur (cadr cur)))
         (case-match cur
           (('lte x y)
            (mv (if (and (equal x a) (not (equal y d))) y rest-b)
                (if (and (equal y d) (not (equal x a))) x rest-c)))
           (('gt y x)
            (mv (if (and (or (not rest-b) (equal rest-c d)) (equal x a) )
                    (progn$   y)
                  rest-b)
                (if (and (or (not rest-c) (equal rest-c a)) (equal y d) )
                    (progn$   x)
                  rest-c)))
           (&
            (mv rest-b rest-c)))))))

  (local
   (define lte-chain-smart-fn (a d mfc state)
     :verify-guards nil
     (b* ( ;(ancestors  (mfc-ancestors mfc))
          (rcnst (access acl2::metafunction-context mfc :rcnst))
          (cl (access acl2::rewrite-constant rcnst :current-clause))
          (?top-cl (access acl2::rewrite-constant rcnst :top-clause))
          (cl (beta-search-reduce-subterms cl (expt 2 30)))
          ((mv b c)
           (lte-chain-smart-fn-aux cl a d))
          ;;(- (cw "rcnst : ~p0 ~%" (cddr rcnst)))
          (b (if (not b) c b))
          (c (if (not c) b c))

          #|(- (and (or (and b c)
          (equal a '(binary-+
          (COUNT-C-LST
          (MV-NTH '0
          (COUGH-DUPLICATES (MV-NTH '2 (C-SUM-MERGE-LST-LST C1-LST 'NIL)))))
          (COUNT-C-LST
          (MV-NTH
          '1
          (COUGH-DUPLICATES (MV-NTH '2 (C-SUM-MERGE-LST-LST C1-LST 'NIL))))))))
          (cw "a: ~p0
          b:~p1
          c:~p2
          d:~p3
          cl:~p4
          "
          a b c d cl
          )))||#)
       (if (and b c)
           (progn$
;(cw "a:~p0 b:~p1 c:~p2, d:~p3 ~%" a b c d)
            `((b . ,b)
              (c . ,c)))
         nil))))

  (local
   (defthm ge-chain-smart
     (implies (and (bind-free (lte-chain-smart-fn a d mfc state)
                              (b c))
                   (or (and (gt b a)
                            (gt c b)
                            (gt d c))

                       (and (gt b a)
                            (gte c b)
                            (gte d c))
                       (and (gte b a)
                            (gte c b)
                            (gt d c))
                       (and (gte b a)
                            (gt c b)
                            (gte d c))

                       (and (gte b a)
                            (gt c b)
                            (gt d c))
                       (and (gt b a)
                            (gte c b)
                            (gt d c))
                       (and (gt b a)
                            (gt c b)
                            (gte d c)))
                   )
              (and ;(gt d a)
               (not (lte d a))))
     :hints (("Goal"
              :in-theory (e/d (rw-dir2) (rw-dir1))))))

  (local
   (defthm lte-chain-smart
     (implies (and (bind-free (lte-chain-smart-fn a d mfc state)
                              (b c))
                   (or (and (lte a b)
                            (lte b c)
                            (lte c d))

                       (and (lte a b)
                            (lte b c)
                            (lt c d))
                       (and (lte a b)
                            (lt b c)
                            (lte c d))
                       (and (lt a b)
                            (lte b c)
                            (lte c d))

                       (and (lt a b)
                            (lte b c)
                            (lt c d))
                       (and (lte a b)
                            (lt b c)
                            (lt c d))
                       (and (lt a b)
                            (lt b c)
                            (lte c d)))
                   )
              (and ;(lte a d)
               (not (gt a d))))
     :hints (("Goal"
              :in-theory (e/d (rw-dir2) (rw-dir1))))))

  )

(local
 (defthm gte-to-lte
   (equal (gte a b)
          (lte b a))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2) (rw-dir1))))))


(local
 (defthm dummy-lemma-13
   (implies (EQUAL (CAR C) 'LIST)
            (NOT (GT (COUNT-C-LST (CDR C)) (COUNT-C C))))
   :hints (("Goal"
            :expand (COUNT-C C)
            :in-theory (e/d (SINGLE-C-P
                             EX-FROM-RP
                             is-rp
                             ) ())))))

(local
 (std::defret
  measure-lemma-compress-s-c
  (equal (count-c res-term)
         (count-c term))
  :fn compress-s-c
  :hints (("Goal"
           :induct (compress-s-c term :limit limit)
           :do-not-induct t
           :in-theory (e/d (compress-s-c
                            count-c
                            single-c-p
                            single-s-p
                            )
                           ())))))
(local
 (defthm dummy-lemma-14
   (implies (and (acl2-numberp a)
                 (acl2-numberp b))
            (equal (equal (+ 1 a) (+ 1 b))
                   (equal a b)))))

(local
 (std::defret
  measure-lemma-decompress-s-c
  (equal (count-c res-term)
         (count-c term))
  :fn decompress-s-c
  :hints (("Goal"
           :induct (decompress-s-c term :limit limit)
           :do-not-induct t
           :in-theory (e/d (decompress-s-c
                            CREATE-LIST-INSTANCE
                            count-c
                            single-c-p
                            single-s-p
                            )
                           ())))))
(local
 (defthm dummy-lemma-15
   (and (implies (and (equal (car c) 'list)
                      (consp c))
                 (equal (count-c c) (count-c-lst (cdr c)))))
   :hints (("Goal"
            :expand (count-c c)
            :in-theory (e/d (EX-FROM-RP
                             is-rp)
                            ())))))

(local
 (defthm dummy-lemma-16
   (and (implies (case-match term
                   (('c & & & ('list . &)) t)
                   (('c & & & ''nil) t))
                 (and (equal (count-c (car (cddddr term)))
                             (1- (count-c term)))
                      (equal (count-c-lst (cdr (car (cddddr term))))
                             (1- (count-c term)))))
        (implies (case-match term
                   (('c & & & ('list  &)) t))
                 (and (equal (count-c (cadr (car (cddddr term))))
                             (1- (count-c term))))))
   :hints (("Goal"
            :expand (count-c term)
            :in-theory (e/d (EX-FROM-RP
                             single-c-p
                             is-rp)
                            ())))))

(local
 (defthm dummy-lemma-17
   (and (implies (acl2-numberp a)
                 (not (gt (1- a) a)))
        (implies (and (CONSP C)
                      (EQUAL (CAR C) 'LIST)
                      (CONSP (CDR C))
                      (CONSP (CADR C))
                      (EQUAL (CAR (CADR C)) 'C)
                      (CONSP (CDR (CADR C)))
                      (CONSP (CDDR (CADR C)))
                      (EQUAL (CADDR (CADR C)) ''NIL)
                      (CONSP (CDDDR (CADR C)))
                      (CONSP (CDDDDR (CADR C)))
                      (NOT (CDDR C))
                      (NOT (CDR (CDDDDR (CADR C)))))
                 (not (gt 0 (count-c (cadr c))))))
  
   :hints (("Goal"
            :in-theory (e/d (rw-dir2) (rw-dir1))))))

(local
 (std::defret
  measure-lemma-c-pattern2-reduce
  (and (lte (count-c c-res)
            (count-c c))
       (<= (count-c c-res)
           (count-c c))
       (implies (case-match c-res (('list . &) t))
                (lte (count-c-lst (cdr c-res))
                     (count-c c)))
       (implies (case-match c-res (('list . &) t))
                (<= (count-c-lst (cdr c-res))
                    (count-c c))))
  :fn c-pattern2-reduce
  ;:otf-flg t
  :hints (("goal"
           :do-not-induct t
           :expand ((:free (x) (SINGLE-C-P `(c . ,x))))
           :in-theory (e/d (c-pattern2-reduce
                            count-c
                            count-c-lst)
                           (ex-from-rp))))))

(local
 (std::defret
  measure-lemma-create-c-instance
  (and (not (gt (count-c c-res)
                (1+ (count-c c))))
       (lte (count-c c-res)
            (1+ (count-c c))))
  :fn CREATE-C-INSTANCE
  :hints (("Goal"
           :in-theory (e/d (CREATE-C-INSTANCE
                            SINGLE-C-P
                            rw-dir2)
                           (rw-dir1))))))

(local
 (std::defret measure-lemma-create-c-instance-2
              (and (not (gte (count-c c-res)
                             (+ 2 (count-c c))))
                   (lt (count-c c-res)
                       (+ 2 (count-c c)))
                   (gt (+ 2 (count-c c))
                       (count-c c-res)))
              :fn CREATE-C-INSTANCE
              :hints (("Goal"
                       :use ((:instance measure-lemma-create-c-instance))
                       :in-theory (e/d (rw-dir2) (rw-dir1
                                                  measure-lemma-create-c-instance))))))

(local
 (defthm CREATE-list-INSTANCE-measure-lemma
   (equal (count-c (create-list-instance lst))
          (count-c-lst lst))
   :hints (("Goal"
            :expand (COUNT-C (CONS 'LIST LST))
            :in-theory (e/d (create-list-instance
                             SINGLE-S-P
                             SINGLE-C-P)
                            ())))))

(local
 (defthm
   measure-lemma-create-c-instance-3
   (b* ((c (create-list-instance c-lst))
        (?c-res (create-c-instance s pp c)))
     (and (not (gte (count-c c-res) (+ 2 (count-c-lst c-lst))))
          (lt (count-c c-res) (+ 2 (count-c-lst c-lst)))
          (gt (+ 2 (count-c-lst c-lst)) (count-c c-res))
          (not (gt (count-c c-res)
                   (1+ (count-c-lst c-lst))))
          (lte (count-c c-res)
               (1+ (count-c-lst c-lst)))))
   :hints
   (("goal" :use ((:instance measure-lemma-create-c-instance
                             (c (create-list-instance c-lst))))
     :in-theory
     (e/d (rw-dir2)
          (rw-dir1
           measure-lemma-create-c-instance))))))



(std::defret-mutual
 measure-lemma-of-c-sum-merge
 (std::defret
  measure-lemma-of-single-c-try-merge
  (implies merge-success
           (and (< (count-c-lst produced-c-lst)
                   (+ (count-c single-c1)
                      (count-c single-c2)))
                (consp single-c1)
                (consp single-c2)))
  :fn single-c-try-merge)
 (std::defret
  measure-lemma-of-c-sum-merge-lst-aux
  (and (implies merge-success
                (and (< (+ (count-c-lst produced-c-lst)
                           (count-c-lst updated-c2-lst))
                        (+ (count-c single-c1)
                           (count-c-lst c2-lst)))
                     (consp single-c1)))
       (implies (not merge-success)
                (and (equal produced-c-lst nil)
                     (equal updated-c2-lst c2-lst))))
  :fn c-sum-merge-lst-aux)
 (std::defret
  measure-lemma-of-c-sum-merge-lst
  (<= (count-c-lst new-c2-lst)
      (+ (count-c single-c1)
         (count-c-lst c2-lst)))
  :fn c-sum-merge-lst)
 (std::defret
  measure-lemma-of-c-sum-merge-lst-lst
  (<= (count-c-lst updated-c2-lst)
      (+ (count-c-lst c1-lst)
         (count-c-lst c2-lst)))
  :fn c-sum-merge-lst-lst)
 (std::defret
  measure-lemma-of-c-sum-merge
  (<= (+ (count-c-lst c-merged-lst)
         (count-c-lst to-be-coughed-c-lst))
      (+ (count-c-lst c1-lst)
         (count-c-lst c2-lst)))
  :fn c-sum-merge)
 (std::defret
  measure-lemma-of-c-sum-merge-aux
  (<= (+ (count-c-lst c-merged-lst)
         (count-c-lst to-be-coughed-c-lst))
      (+ (count-c-lst c1-lst)
         (count-c-lst c2-lst)))
  :fn c-sum-merge-aux)
 :otf-flg t
 :hints (("Goal"
          :do-not-induct t
          :do-not '(preprocess fertilize generalize)
          :expand ((C-SUM-MERGE C1-LST C2-LST
                                :AUTO-SWAP AUTO-SWAP
                                :CLEAN-C1-LST NIL)
                   (SINGLE-C-TRY-MERGE SINGLE-C1 SINGLE-C2)
                   (C-SUM-MERGE-AUX NIL C2-LST :CLEAN-C1-LST CLEAN-C1-LST)
                   (C-SUM-MERGE C1-LST C2-LST
                                :AUTO-SWAP AUTO-SWAP
                                :CLEAN-C1-LST CLEAN-C1-LST)
                   (C-SUM-MERGE-AUX (MV-NTH 0 (SWAP-C-LSTS C1-LST C2-LST AUTO-SWAP))
                                    (MV-NTH 1 (SWAP-C-LSTS C1-LST C2-LST AUTO-SWAP))
                                    :CLEAN-C1-LST CLEAN-C1-LST)
                   (C-SUM-MERGE-AUX NIL
                                    (MV-NTH 1 (SWAP-C-LSTS C1-LST C2-LST AUTO-SWAP))
                                    :CLEAN-C1-LST CLEAN-C1-LST)
                   (C-SUM-MERGE-AUX (MV-NTH 0 (SWAP-C-LSTS C1-LST C2-LST AUTO-SWAP))
                                    NIL
                                    :CLEAN-C1-LST NIL)
                   (C-SUM-MERGE-AUX (MV-NTH 0 (SWAP-C-LSTS C1-LST C2-LST AUTO-SWAP))
                                    NIL
                                    :CLEAN-C1-LST CLEAN-C1-LST)
                   (C-SUM-MERGE-LST-LST C1-LST C2-LST)
                   (C-SUM-MERGE-AUX C1-LST C2-LST
                                    :CLEAN-C1-LST CLEAN-C1-LST)
                   (C-SUM-MERGE-LST SINGLE-C1 C2-LST)
                   (C-SUM-MERGE-LST SINGLE-C1 C2-LST)
                   (C-SUM-MERGE-LST ''0 C2-LST)
                   (C-SUM-MERGE-LST-AUX SINGLE-C1 C2-LST)
                   (C-SUM-MERGE-AUX C1-LST NIL :CLEAN-C1-LST NIL)
                   (C-SUM-MERGE-AUX C1-LST NIL :CLEAN-C1-LST CLEAN-C1-LST))
          :in-theory (e/d () ()))

         #|("Subgoal *1/20.1"
          ;:expand (COUNT-C-LST C1-LST) ; ; ;
         :use ((:instance measure-lemma-of-s-sum-merge-aux ;
         (s1-lst (CDR C1-LST)) ;
         (s2-lst (MV-NTH 2 ;
         (C-SUM-MERGE-LST (CAR C1-LST) ;
         C2-LST))))) ;
         :in-theory (disable  measure-lemma-of-s-sum-merge-aux))||#

         #|("Subgoal *1/26"
         :use ((:instance measure-lemma-of-s-sum-merge-aux
         (s1-lst (CDR C1-LST))
         (s2-lst (MV-NTH 2
         (C-SUM-MERGE-LST (CAR C1-LST)
         C2-LST)))))
         :in-theory (disable measure-lemma-of-s-sum-merge-aux))||#
         ("Subgoal *1/18"
          :expand ((COUNT-C-LST (LIST SINGLE-C1))
                   (C-SUM-MERGE-LST SINGLE-C1 C2-LST)
                   (C-SUM-MERGE-LST-AUX SINGLE-C1 C2-LST))
          :use ((:instance measure-lemma-of-s-sum-merge-aux
                           (s1-lst (LIST SINGLE-C1))
                           (s2-lst C2-LST)))
          :in-theory (disable measure-lemma-of-s-sum-merge-aux))

         ))




(local
 (use-arith-5 t))

(verify-guards c-sum-merge-fn
  :hints (("Goal"
           :in-theory (e/d (rw-dir2) (rw-dir1)))))

(memoize 'c-sum-merge-aux
         :memo-table-init-size 100000
         ;;:condition 'mem
         ;;:recursive nil
         ;;:condition '(and (not (equal c1-lst nil)) (not (equal c2-lst nil)))
         :aokp t)

(verify-guards s-of-s-fix-lst-fn)

(verify-guards s-of-s-fix)

(verify-guards new-sum-merge-aux)

(verify-guards new-sum-merge)

(verify-guards c-spec-meta-aux)

(verify-guards c-spec-meta)

(verify-guards s-spec-meta-aux)

(verify-guards s-spec-meta)

(verify-guards s-c-spec-meta)
