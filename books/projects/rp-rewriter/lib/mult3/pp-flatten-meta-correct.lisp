; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
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

(local
 (include-book "lemmas"))

(local
 (include-book "sum-merge-fncs-correct"))

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

(local
 (in-theory (enable pp)))

(local
 (set-induction-depth-limit 1))

(local
 (in-theory (e/d (sum-comm-1-loop-stopper
                  sum-comm-2-loop-stopper)
                 (sum-comm-1
                  sum-comm-2))))

(local
 (in-theory (disable floor len)))

(local
 (in-theory (disable +-IS-SUM
                     FLOOR2-IF-F2
                     mod2-is-m2)))

(local
 (defthm is-equals-of-others
   (implies (not (equal (car term) 'equals))
            (not (is-equals term )))
   :hints (("Goal"
            :in-theory (e/d (is-equals) ())))))

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
                   (case-split (consp lst)))
              (equal (< (LEN (CDR LST)) (+ -1 SIZE)) nil)))))

#|(local
(defthm rp-term-listp-cut-list-by-half
(implies (and (rp-term-listp lst)
(<= size (len lst)))
(and (rp-term-listp (mv-nth 0 (cut-list-by-half lst size)))
(rp-term-listp (mv-nth 1 (cut-list-by-half lst size)))))
:hints (("Goal"
:do-not-induct t
:induct (cut-list-by-half lst size)
:in-theory (e/d (rp-term-listp
cut-list-by-half)
())))))|#

#|(defthm rp-term-listp-merge-sorted-and$-lists
(implies (and (rp-term-listp lst1)
(rp-term-listp lst2))
(rp-term-listp (merge-sorted-and$-lists lst1 lst2)))
:hints (("Goal"
:induct (merge-sorted-and$-lists lst1 lst2)
:in-theory (e/d (merge-sorted-and$-lists) ()))))|#

#|(local
(defthm rp-term-listp-sort-and$-list
(implies (rp-term-listp lst)
(rp-term-listp (sort-and$-list lst len)))
:hints (("Goal"
:in-theory (e/d (sort-and$-list) ())))))|#

#|(local
(defthm rp-term-list-listp-merge-sorted-pp-e-lists
(implies (and (rp-term-list-listp (strip-cdrs lst1))
(rp-term-list-listp (strip-cdrs lst2)))
(rp-term-list-listp
(strip-cdrs
(merge-sorted-pp-e-lists lst1 lst2))))
:hints (("Goal"
:induct (merge-sorted-pp-e-lists lst1 lst2)
:in-theory (e/d (merge-sorted-pp-e-lists) ())))))|#

(local
 (defthm RP-TERM-LIST-LISTP-of-STRIP-CDRS-lemma
   (implies (RP-TERM-LIST-LISTP (STRIP-CDRS x))
            (RP-TERM-LISTP (CDR (CADR x))))))

#|(local
(defthm rp-term-list-listp-sort-pp-e-lists
(implies (rp-term-list-listp (strip-cdrs lst1))
(rp-term-list-listp (strip-cdrs
(sort-pp-e-lists lst1 len))))
:hints (("Goal"
;;:induct (sort-pp-e-lists lst1 len)
;;:do-not-induct t
:in-theory (e/d (RP-TERM-LIST-LISTP
sort-pp-e-lists
RP-TERM-LISTP)
())))))|#

#|(local
(defthm rp-term-list-listp-and$-pp-e-lists-aux
(implies (and (rp-term-listp cur)
(rp-term-list-listp (strip-cdrs lst2))
(rp-term-list-listp (strip-cdrs acc)))
(rp-term-list-listp (strip-cdrs (and$-pp-e-lists-aux cur lst2 acc
sign))))
:hints (("Goal"
:in-theory (e/d (and$-pp-e-lists-aux) ())))))|#

#|(local
(defthm rp-term-list-listp-and$-pp-e-lists
(implies (and (rp-term-list-listp (strip-cdrs lst1))
(rp-term-list-listp (strip-cdrs lst2))
(rp-term-list-listp (strip-cdrs acc)))
(rp-term-list-listp (strip-cdrs (and$-pp-e-lists lst1 lst2 acc
sign))))
:hints (("Goal"
:in-theory (e/d (and$-pp-e-lists) ())))))|#

#|(Local
(defret rp-term-list-listp-pp-term-to-pp-e-list
(implies (and (rp-termp term)
(not too-large-p))
(rp-term-list-listp (strip-cdrs result)))
:fn pp-term-to-pp-e-list
:hints (("Goal"
:in-theory (e/d (pp-term-to-pp-e-list) ())))))|#

#|(defthm rp-term-list-listp-strip-cdrs-sort-sum-meta-aux2
(implies (rp-termp term)
(rp-term-list-listp (strip-cdrs (mv-nth 1 (sort-sum-meta-aux2
term)))))
:hints (("goal"
:in-theory (e/d (sort-sum-meta-aux2)
((:definition acl2::apply$-badgep)
(:linear acl2::apply$-badgep-properties . 1)
(:rewrite rp-termp-implies-cdr-listp)
(:definition member-equal)
(:rewrite rp-term-listp-is-true-listp)
(:linear acl2::apply$-badgep-properties . 2)
(:definition true-listp)
(:rewrite is-if-rp-termp)
;;(:rewrite acl2::o-p-o-infp-car)
(:rewrite is-rp-pseudo-termp)
(:rewrite atom-rp-termp-is-symbolp)
falist-consistent
(:definition subsetp-equal))))))|#

#|(defthm rp-termp-of-sort-sum-meta.result
(implies (rp-termp term)
(b* (((mv ?result ?dont-rw)
(sort-sum-meta term)))
(rp-termp result)))
:rule-classes :rewrite
:hints (("Goal"
:in-theory (e/d (sort-sum-meta)
()))))|#

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

;; valid-sc
;; to be used instead of strip-cdrs below
(defun collect-pp-e-elements (lst)
  (if (atom lst)
      nil
    (cons (pp-e->elements (car lst))
          (collect-pp-e-elements (cdr lst)))))

(defun valid-sc-subterms-lst (lst a)
  (if (atom lst)
      (eq lst nil)
    (and (valid-sc-subterms (car lst) a)
         (valid-sc-subterms-lst (cdr lst) a))))

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
                             dummy-arith-lemma-2)
                            (+-IS-SUM))))))

(local
 (defthm valid-sc-subterms-lst-cut-list-by-half
   (implies (and (valid-sc-subterms-lst lst a)
                 (<= size (len lst)))
            (and (valid-sc-subterms-lst (mv-nth 0 (cut-list-by-half lst size)) a)
                 (valid-sc-subterms-lst (mv-nth 1 (cut-list-by-half lst size)) a)))
   :hints (("Goal"
            :do-not-induct t
            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half)
                            (+-IS-SUM))))))

(local
 (defthm valid-sc-subterms-lst-cut-list-by-half-2
   (implies (and (valid-sc-subterms-lst (collect-pp-e-elements lst) a)
                 (<= size (len lst)))
            (and (valid-sc-subterms-lst
                  (collect-pp-e-elements (mv-nth 0 (cut-list-by-half lst size)))
                  a)
                 (valid-sc-subterms-lst
                  (collect-pp-e-elements (mv-nth 1 (cut-list-by-half lst size)))
                  a)))
   :hints (("Goal"
            :do-not-induct t
            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half
                             dummy-arith-lemma-1)
                            (+-IS-SUM))))))

(defthm valid-sc-subterms-merge-sorted-and$-lists
  (implies (and (valid-sc-subterms lst1 a)
                (valid-sc-subterms lst2 a))
           (valid-sc-subterms (merge-sorted-and$-lists lst1 lst2) a))
  :hints (("Goal"
           :induct (merge-sorted-and$-lists lst1 lst2)
           :in-theory (e/d (merge-sorted-and$-lists) ()))))

(encapsulate nil
  (local
   (use-arith-5 t))

  (defthm valid-sc-subterms-sort-and$-list
    (implies (valid-sc-subterms lst a)
             (valid-sc-subterms (sort-and$-list lst len) a))
    :hints (("Goal"
             :induct (sort-and$-list lst len)
             :do-not-induct t
             :in-theory (e/d (sort-and$-list)
                             (+-IS-SUM)))))

  (defthm valid-sc-subterms-lst-merge-sorted-pp-e-lists
    (implies (and (valid-sc-subterms-lst (collect-pp-e-elements lst1) a)
                  (valid-sc-subterms-lst (collect-pp-e-elements lst2) a))
             (valid-sc-subterms-lst
              (collect-pp-e-elements
               (merge-sorted-pp-e-lists lst1 lst2))
              a))
    :hints (("Goal"
             :induct (merge-sorted-pp-e-lists lst1 lst2)
             :in-theory (e/d (merge-sorted-pp-e-lists) ()))))

  (defthm valid-sc-subterms-lst-sort-pp-e-lists
    (implies (valid-sc-subterms-lst (collect-pp-e-elements lst1) a)
             (valid-sc-subterms-lst (collect-pp-e-elements
                                     (sort-pp-e-lists lst1 len))
                                    a))
    :hints (("Goal"
             ;;:induct (sort-pp-e-lists lst1 len)
             ;;:do-not-induct t
             :in-theory (e/d (sort-pp-e-lists)
                             (+-IS-SUM))))))

(local
 (defthm VALID-SC-SUBTERMS-of-RP-TERM-LIST-FIX
   (implies (valid-sc-subterms x a)
            (valid-sc-subterms (RP-TERM-LIST-FIX x) a))
   :hints (("Goal"
            :in-theory (e/d (RP-TERM-LIST-FIX) ())))))

(local
 (defthm valid-sc-subterms-lst-and$-pp-e-lists-aux
   (implies (and (valid-sc-subterms (pp-e->elements cur) a)
                 (valid-sc-subterms-lst (collect-pp-e-elements lst2) a)
                 (valid-sc-subterms-lst (collect-pp-e-elements acc) a))
            (valid-sc-subterms-lst (collect-pp-e-elements (and$-pp-e-lists-aux cur lst2 acc))
                                   a))
   :hints (("Goal"
            :in-theory (e/d (and$-pp-e-lists-aux) ())))))

(defthm valid-sc-subterms-lst-and$-pp-e-lists
  (implies (and (valid-sc-subterms-lst (collect-pp-e-elements lst1) a)
                (valid-sc-subterms-lst (collect-pp-e-elements lst2) a)
                (valid-sc-subterms-lst (collect-pp-e-elements acc) a))
           (valid-sc-subterms-lst (collect-pp-e-elements (and$-pp-e-lists lst1 lst2 acc
                                                                          sign))
                                  a))
  :hints (("Goal"
           :in-theory (e/d (and$-pp-e-lists) ()))))

(defret valid-sc-subterms-lst-pp-term-to-pp-e-list
  (implies (valid-sc term a)
           (valid-sc-subterms-lst (collect-pp-e-elements result)
                                  a))
  :fn pp-term-to-pp-e-list
  :hints (("Goal"
           :in-theory (e/d (pp-term-to-pp-e-list) ()))))

(defthm valid-sc-pp-e-list-to-term-p+
  (implies (valid-sc-subterms-lst (collect-pp-e-elements lst) a)
           (valid-sc-subterms (pp-e-list-to-term-pp-lst lst) a))
  :hints (("Goal"
           :in-theory (e/d (pp-e-list-to-term-pp-lst
                            CREATE-AND-LIST-INSTANCE
                            is-if is-equals
                            is-rp) ()))))

(defret valid-sc-of-pp-remove-extraneous-sc
  (implies (force (valid-sc term a))
           (valid-sc res-term a))
  :fn pp-remove-extraneous-sc
  :hints (("Goal"
           :do-not-induct t
           :induct (pp-remove-extraneous-sc term)
           :expand ((:free (x y) (is-rp (cons x y))))
           :in-theory (e/d (pp-remove-extraneous-sc)
                           ((:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            (:DEFINITION INCLUDE-FNC-fn)
                            (:DEFINITION RP-TERMP)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE RP-TERMP-OF-PP-REMOVE-EXTRANEOUS-SC)
                            (:DEFINITION FALIST-CONSISTENT)
                            (:DEFINITION FALIST-CONSISTENT-AUX)
                            rp-termp)))))

(defret valid-sc-subterms-of-pp-remove-extraneous-sc
  (implies (force (valid-sc-subterms lst a))
           (valid-sc-subterms res-lst a))
  :fn pp-remove-extraneous-sc-lst
  :hints (("Goal"
           :expand ((:free (x y) (is-rp (cons x y))))
           :in-theory (e/d (pp-remove-extraneous-sc-lst)
                           ((:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            (:DEFINITION INCLUDE-FNC-fn)
                            (:DEFINITION RP-TERMP)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE RP-TERMP-OF-PP-REMOVE-EXTRANEOUS-SC)
                            (:DEFINITION FALIST-CONSISTENT)
                            (:DEFINITION FALIST-CONSISTENT-AUX)
                            rp-termp)))))

(defthm valid-sc-subterms-append-wog
  (implies (and (force (valid-sc-subterms lst1 a))
                (force (valid-sc-subterms lst2 a)))
           (valid-sc-subterms (append-wog lst1 lst2) a))
  :hints (("Goal"
           :induct (append-wog lst1 lst2)
           :do-not-induct t
           :in-theory (e/d (append-wog) ()))))

(defthm valid-sc-subterms-list-to-lst
  (implies (valid-sc term a)
           (valid-sc-subterms (list-to-lst term) a))
  :hints (("Goal"
           :in-theory (e/d (list-to-lst
                            valid-sc
                            is-rp is-equals
                            is-if)
                           ()))))

(defret valid-sc-of-create-times-instance
  (implies (valid-sc term a)
           (valid-sc res a))
  :fn CREATE-TIMES-INSTANCE
  :hints (("Goal"
           :in-theory (e/d (CREATE-TIMES-INSTANCE) ()))))

(defret pp-flatten-returns-valid-sc
  (implies (force (valid-sc term a))
           (VALID-SC-SUBTERMS pp-lst a))
  :fn pp-flatten
  :hints (("Goal"
           :in-theory (e/d (pp-flatten
                            create-and-list-instance
                            is-if is-equals is-rp) ()))))

(defthm valid-sc-subterms-of-cdr
  (implies (or (valid-sc-subterms lst a)
               (and (valid-sc lst a)
                    (not (equal (car lst) 'rp))
                    (not (equal (car lst) 'quote))
                    (not (equal (car lst) 'if))))
           (valid-sc-subterms (cdr lst) a))
  :hints (("Goal"
           :in-theory (e/d (is-rp
                            is-if is-equals)
                           ()))))

(local
 (defret valid-sc-of-<fn>
   (implies (and (valid-sc cur a)
                 valid)
            (VALID-SC-SUBTERMS (pp-e->elements e) a))
   :fn SORT-SUM-META-AUX-AUX
   :hints (("Goal"
            :in-theory (e/d (SORT-SUM-META-AUX-AUX
                             is-rp is-if is-equals)
                            ((:DEFINITION EVAL-AND-ALL)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:DEFINITION INCLUDE-FNC-fn)
                             (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)

                             (:DEFINITION RP-TERMP)
                             (:DEFINITION FALIST-CONSISTENT)
                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION FALIST-CONSISTENT-AUX)
                             rp-trans
                             (:TYPE-PRESCRIPTION O<)
                             (:TYPE-PRESCRIPTION INCLUDE-FNC-fn)
                             (:TYPE-PRESCRIPTION VALID-SC-SUBTERMS)
                             (:REWRITE DEFAULT-CAR)
                             (:DEFINITION INCLUDE-FNC-SUBTERMS-fn)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                             (:TYPE-PRESCRIPTION VALID-SC)
                             (:TYPE-PRESCRIPTION O-P)
                             (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS-fn)
                             (:REWRITE VALID-SC-OF-EX-FROM-RP)
                             (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                             (:definition rp-termp)))))))

(local
 (defthm sort-sum-meta-aux-returns-valid-sc
   (implies (valid-sc term a)
            (valid-sc-subterms-lst
             (collect-pp-e-elements (mv-nth 1 (sort-sum-meta-aux term)))
             a))
   :hints (("goal"
            :in-theory (e/d (sort-sum-meta-aux
                             )
                            ((:definition valid-sc)
                             (:DEFINITION EVAL-AND-ALL)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:DEFINITION INCLUDE-FNC-fn)
                             (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)

                             (:DEFINITION RP-TERMP)
                             (:DEFINITION FALIST-CONSISTENT)
                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION FALIST-CONSISTENT-AUX)
                             rp-trans
                             (:definition rp-termp)
                             (:rewrite car-of-ex-from-rp-is-not-rp)
                             (:definition rp-term-listp)
                             (:rewrite not-include-rp-means-valid-sc)
                             (:definition include-fnc-fn)
                             (:rewrite rp-termp-implies-subterms)
                             (:definition quotep)))))))

(local
 (defthm VALID-SC-SUBTERMS-LST-strip-cdrs-append
   (equal (VALID-SC-SUBTERMS-LST (collect-pp-e-elements (APPEND x y)) a)
          (and (VALID-SC-SUBTERMS-LST (collect-pp-e-elements x) a)
               (VALID-SC-SUBTERMS-LST (collect-pp-e-elements y) a)))))

(local
 (defthm VALID-SC-SUBTERMS-LST-of-append
   (equal (VALID-SC-SUBTERMS-LST (append x y) a)
          (and (valid-sc-subterms-lst (true-list-fix x) a)
               (valid-sc-subterms-lst y a)))))

(local
 (defthm sort-sum-meta-aux2-returns-valid-sc
   (implies (valid-sc term a)
            (valid-sc-subterms-lst
             (collect-pp-e-elements (mv-nth 1 (sort-sum-meta-aux2 term)))
             a))
   :hints (("goal"
            :in-theory (e/d (sort-sum-meta-aux2
                             )
                            ((:definition valid-sc)
                             (:DEFINITION EVAL-AND-ALL)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:DEFINITION INCLUDE-FNC-fn)
                             (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)

                             (:DEFINITION RP-TERMP)
                             (:DEFINITION FALIST-CONSISTENT)
                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION FALIST-CONSISTENT-AUX)
                             rp-trans
                             (:definition rp-termp)
                             (:rewrite car-of-ex-from-rp-is-not-rp)
                             (:definition rp-term-listp)
                             (:rewrite not-include-rp-means-valid-sc)
                             (:definition include-fnc-fn)
                             (:rewrite rp-termp-implies-subterms)
                             (:definition quotep)))))))

(defthm sort-sum-meta-returns-valid-sc
  (implies (valid-sc term a)
           (valid-sc (mv-nth 0 (sort-sum-meta term)) a))
  :hints (("Goal"
           :in-theory (e/d (sort-sum-meta
                            CREATE-LIST-INSTANCE
                            is-rp
                            is-if is-equals) ()))))

;;;;;;;;;;;;;;;;
;; EVAL LEMMAS

(progn
  (local
   (defthmd eval-of-binary-not-1
     (implies (and (mult-formula-checks state)
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
     (implies (and (mult-formula-checks state)
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
     (implies (and (mult-formula-checks state)
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
     (implies (and (mult-formula-checks state)
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
   (defthmd eval-of-logbit-1
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          'logbit$inline)
                   (consp term)
                   (consp (cdr term))
                   (consp (cddr term))
                   (not (cdddr term)))
              (equal (rp-evlt term a)
                     (logbit (rp-evlt (cadr term) a)
                             (rp-evlt (caddr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of-logbit
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          'logbit$inline)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (consp (cddr (ex-from-rp term)))
                   (not (cdddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (logbit (rp-evlt (cadr (ex-from-rp term)) a)
                             (rp-evlt (caddr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of-logbit-1)
                              (evl-of-extract-from-rp)))))))

(progn
  (local
   (defthmd eval-of-binary-?-1
     (implies (and (mult-formula-checks state)
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
     (implies (and (mult-formula-checks state)
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
     (implies (and (mult-formula-checks state)
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
     (implies (and (mult-formula-checks state)
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
     (implies (and (mult-formula-checks state)
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
     (implies (and (mult-formula-checks state)
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
     (implies (and (mult-formula-checks state)
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
     (implies (and (mult-formula-checks state)
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
                   (sum 1 (-- a))))))

(progn
  (local
   (defthmd has-bitp-rp-implies-lemma
     (implies (and (has-bitp-rp term)
                   (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (eval-and-all (context-from-rp term nil) a))
              (bitp (rp-evlt term a)))
     :hints (("goal"
              :induct (has-bitp-rp term)
              :do-not-induct t
              :in-theory (e/d (has-bitp-rp
                               is-rp
                               is-if is-equals
                               eval-and-all
                               context-from-rp)
                              (bitp
                               ex-from-rp-lemma1
                               valid-sc))))))

  (defthm pp-has-bitp-rp-implies
    (implies (and (has-bitp-rp term)
                  (mult-formula-checks state)
                  (rp-evl-meta-extract-global-facts)
                  (valid-sc term a))
             (and (bitp (rp-evlt term a))
                  (bitp (rp-evlt (ex-from-rp term) a))))
    :hints (("goal"
             :induct (has-bitp-rp term)
             :expand ((valid-sc term a))
             :do-not-induct t
             :in-theory (e/d (has-bitp-rp
                              has-bitp-rp-implies-lemma
                              is-rp
                              is-if is-equals)
                             (bitp
                              rp-trans
                              ex-from-rp-lemma1
                              context-from-rp
                              valid-sc-ex-from-rp-2
                              not-include-rp
                              rp-evl-of-rp-call
                              valid-sc
                              eval-and-all))))))

(defthmd rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
  (AND (IMPLIES (SYNTAXP (or (ATOM TERM)
                             (and (equal (car term) 'car)
                                  (not (include-fnc term 'ex-from-rp )))))
                (EQUAL (RP-EVL (RP-TRANS TERM) A)
                       (RP-EVL (RP-TRANS (EX-FROM-RP TERM))
                               A)))
       (IMPLIES (SYNTAXP (not (or (ATOM TERM)
                                  (and (equal (car term) 'car)
                                       (not (include-fnc term 'ex-from-rp ))))))
                (EQUAL (RP-EVL (RP-TRANS (EX-FROM-RP TERM)) A)
                       (RP-EVL (RP-TRANS TERM) A)))))

(create-regular-eval-lemma pp 1 mult-formula-checks)

(create-regular-eval-lemma bit-fix 1 mult-formula-checks)

(encapsulate
  nil

  (local
   (defthmd bitp-implies-integerp
     (implies (bitp x)
              (integerp x))))

  (defthm pp-term-p-is-bitp
    (implies (and (pp-term-p term :strict strict)
                  (mult-formula-checks state)
                  (rp-evl-meta-extract-global-facts)
                  (valid-sc term a))
             (and (bitp (rp-evlt term a))
                  (integerp (rp-evlt term a))
                  (bitp (rp-evlt (ex-from-rp term) a))
                  (integerp (rp-evlt (ex-from-rp term) a))))
    :hints (("goal"
             :do-not-induct t
             :induct (pp-term-p term :strict strict)
             :in-theory (e/d* (;;rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
                               bitp-implies-integerp
                               (:REWRITE
                                REGULAR-RP-EVL-OF_PP_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                               (:REWRITE
                                REGULAR-RP-EVL-OF_bit-fix_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP))
                              (valid-sc
                               bitp
                               RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                               rp-trans
                               ;;rp-evlt-of-ex-from-rp
                               sum
                               not$-to-pp-sum)))))

  (defthm pp-term-p-is-bitp-strict=nil
    (implies (and (pp-term-p term :strict nil)
                  (mult-formula-checks state)
                  (rp-evl-meta-extract-global-facts)
                  (valid-sc term a))
             (and (bitp (rp-evlt term a))
                  (integerp (rp-evlt term a))))
    :hints (("goal"
             :use ((:instance pp-term-p-is-bitp
                              (strict nil)))
             ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ARITH LEMMAS

(local
 (in-theory (disable rp-evlt-of-ex-from-rp)))

(local
 (encapsulate
   nil
   (local
    (in-theory (disable +-IS-SUM)))
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
   (in-theory (enable bit-listp)))

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
     (b* ((x (ifix x))
          (y (ifix y)))
       (* x y)))))

(local
 (defthm times$-of-1-and-0
   (and (equal (times$ 1 x)
               (ifix x))
        (equal (times$ x 1)
               (ifix x))
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
                   (equal (len lst) (- y x))))
   :hints (("Goal"
            :in-theory (e/d () (+-IS-SUM))))))

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
                     (sum x y (-- (and$ x y)))))
     :hints (("goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthmd binary-xor-to-pp-sum
     (implies (and (bitp x)
                   (bitp y))
              (equal (binary-xor  x y)
                     (sum x y
                          (-- (and$ x y))
                          (-- (and$ x y)))))))

  (local
   (defthmd binary-?-to-pp-sum
     (implies (and (bitp x)
                   (bitp test)
                   (bitp y))
              (equal (binary-? test  x y)
                     (sum y (and$ test x)
                          (-- (and$ test y)))))))

  (local
   (defthm ---of-pp-sum
     (implies t
              (equal (-- (sum x y))
                     (sum (-- x) (-- y))))
     :hints (("goal"
              :in-theory (e/d (bitp sum --)
                              (+-IS-SUM))))))

  (local
   (defthm --of--
     (equal (-- (-- x))
            (ifix x))
     :hints (("Goal"
              :in-theory (e/d (--) ())))))

  (local
   (defthm type-fix-of-fncs
     (and (equal (ifix (and$ a b))
                 (and$ a b))
          (equal (ifix (sum a b))
                 (sum a b)))
     :hints (("goal"
              :in-theory (e/d (and$ ifix) ())))))

  (local
   (defthm type-fix-of--
     (equal (ifix (-- x))
            (-- x))))

  (local
   (defthm type-fix-when-integerp
     (implies (integerp x)
              (equal (ifix x)
                     x))))

  (local
   (defthm type-fix-when-bitp
     (implies (bitp x)
              (equal (ifix x)
                     x))))

  (local
   (defthm integerp-of-fncs
     (and (integerp (sum x y))
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
   (defthm binar-and-abs-is-and$-2-lemma
     (equal (EQUAL (- (IFIX X)) 0)
            (equal (ifix x) 0))))

  (local
   (defthm binar-and-abs-is-and$-2-lemma-2
     (equal (EQUAL (- (IFIX X)) 1)
            (equal (ifix x) -1))))

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
     (equal (equal (sum a x)
                   (sum a y))
            (equal (ifix x)
                   (ifix y)))))

  (local
   (defthm --of--equals
     (equal (equal (-- x)
                   (-- y))
            (equal (ifix x)
                   (ifix y)))
     :hints (("Goal"
              :in-theory (e/d (--) ())))))

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
     (and (equal (sum a (-- a) b)
                 (ifix b))
          (equal (sum a (-- a))
                 0)
          (equal (sum (-- a) a b)
                 (ifix b))
          (equal (sum (-- a) a)
                 0))
     :hints (("goal"
              :in-theory (e/d (sum
                               --
                               ifix)
                              (+-IS-SUM))))))

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
                     (times x y))))

   (defthm times-distribute-over-pp-sum
     (and (equal (times x (sum a b))
                 (sum (times x a)
                      (times x b)))
          (equal (times (sum a b) x)
                 (sum (times x a)
                      (times x b))))
     :hints (("goal"
              :in-theory (e/d (times sum
                                     ifix)
                              (+-IS-SUM)))))

   ))

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
              :in-theory (e/d (len) (+-IS-SUM)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; pp-e-list-to-term lemmas

(local
 (progn
   (defthm append-returns-bit-list-listp
     (implies (and (mult-formula-checks state)
                   (booleanp sign)
                   (bit-list-listp (rp-evlt-lst-lst lst1 a))
                   (bit-list-listp (rp-evlt-lst-lst lst2 a))
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (append lst1 lst2)
                                a)))
     :hints (("goal"
              :in-theory (e/d (rp-evlt-lst-lst
                               and$-pp-e-lists
                               and$-pp-e-lists-aux
                               pp-term-to-pp-e-list
                               bit-list-listp) ()))))

   (defthm append-returns-bit-list-listp-with-strip-cdrs
     (implies (and (mult-formula-checks state)
                   (booleanp sign)
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a))
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (strip-cdrs (append lst1 lst2))
                                a)))
     :hints (("goal"
              :in-theory (e/d (rp-evlt-lst-lst
                               and$-pp-e-lists
                               and$-pp-e-lists-aux
                               pp-term-to-pp-e-list
                               bit-list-listp) ()))))

   (defthm append-returns-bit-listp
     (implies (and (mult-formula-checks state)
                   (booleanp sign)
                   (bit-listp (rp-evlt-lst lst1 a))
                   (bit-listp (rp-evlt-lst lst2 a))
                   (rp-evl-meta-extract-global-facts))
              (bit-listp
               (rp-evlt-lst (append lst1 lst2)
                            a)))
     :hints (("goal"
              :in-theory (e/d (rp-evlt-lst-lst
                               and$-pp-e-lists
                               and$-pp-e-lists-aux
                               pp-term-to-pp-e-list
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
  (define pp-e-list-to-term-and$ ((cur true-listp))
    (cond ((atom cur)
           ''1)
          #|((atom (cdr cur))
          `(binary-and ,(car cur) '1))||#
          (t
           `(binary-and ,(car cur)
                        ,(pp-e-list-to-term-and$ (cdr cur))))))

  (define pp-e-list-to-term-p+ ((lst pp-e-list-p))
    (cond ((atom lst)
           ''0)
          #|((atom (cdr lst))
          (b* (((pp-e e) (car lst))
          (cur (pp-e-list-to-term-and$ e.elements)))
          `(times ',e.coef ,cur)))|#
          (t
           (b* (((pp-e e) (car lst))
                (cur (pp-e-list-to-term-and$ e.elements)))
             `(binary-sum (times ',e.coef ,cur) ,(pp-e-list-to-term-p+ (cdr lst)))))))

  ;; auxilary function used only in the local lemmas for correctness proofs.
  (local
   (define apply-coef-to-pp-e-list (lst coef)
     :returns (res pp-e-list-p
                   :hyp (pp-e-list-p lst))
     :verify-guards nil
     (if (atom lst)
         nil
       (cons (b* (((pp-e e) (car lst)))
               (change-pp-e e
                            :coef (* (ifix coef) e.coef)))
             (apply-coef-to-pp-e-list (cdr lst) coef))))))

(progn
  (local
   (defthm bitp-of-eval-of-pp-e-list-to-term-aux
     (implies (and (bit-listp (rp-evlt-lst lst a))
                   (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts))
              (bitp (rp-evlt (pp-e-list-to-term-and$ lst) a)))
     :hints (("goal"
              :in-theory (e/d (pp-e-list-to-term-and$) ())))))

  (local
   (defthm eval-of-append-of-pp-e-list-to-term-aux
     (implies  (and (mult-formula-checks state)
                    (rp-evl-meta-extract-global-facts)
                    (bit-listp (rp-evlt-lst cur a))
                    (bit-listp (rp-evlt-lst cur2 a)))
               (equal (rp-evlt (pp-e-list-to-term-and$ (append cur cur2)) a)
                      (and$ (rp-evlt (pp-e-list-to-term-and$ cur) a)
                            (rp-evlt (pp-e-list-to-term-and$ cur2) a))))
     :hints (("goal"
              :do-not-induct t
              :induct (pp-e-list-to-term-and$ cur)
              :in-theory (e/d (pp-e-list-to-term-and$)
                              (bitp
                               rp-evl-lst-of-cons
                               (:rewrite acl2::consp-of-append)
                               bit-listp))))))

  (local
   (defthm integerp-of-eval-of-pp-e-list-to-term-aux
     (implies (and (integer-listp (rp-evlt-lst lst a))
                   (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts))
              (integerp (rp-evlt (pp-e-list-to-term-and$ lst) a)))
     :hints (("goal"
              :in-theory (e/d (pp-e-list-to-term-and$) ())))))

  (local
   (defthm bit-listp-implies-integer-listp
     (implies (bit-listp x)
              (integer-listp x))))

  (local
   (defthm integerp-of-eval-of-pp-e-list-to-term
     (implies (and (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst) a))
                   (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts))
              (integerp (rp-evlt (pp-e-list-to-term-p+ lst) a)))
     :hints (("goal"
              :do-not-induct t
              :induct (pp-e-list-to-term-p+ lst)
              :in-theory (e/d (pp-e-list-to-term-p+)
                              (sum --
                                   and$
                                   bitp
                                   ifix))))))

  (local
   (defthm integerp-of-eval-of-pp-e-list-to-term-forward-chaining
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst) a)))
              (integerp (rp-evlt (pp-e-list-to-term-p+ lst) a)))
     :rule-classes :forward-chaining
     :hints (("goal"
              :in-theory (e/d (pp-e-list-to-term-p+) ()))))))

(local
 (defthm rp-term-list-fix-of-pp-e->elements
   (equal (rp-term-list-fix (pp-e->elements x))
          (pp-e->elements x))
   :hints (("goal"
            :in-theory (e/d (rp-term-list-fix) ())))))

(local
 (defthmd times-of-sum
   (equal (times coef (sum x y))
          (sum (times coef x)
               (times coef y)))
   :hints (("Goal"
            :in-theory (e/d (sum times)
                            (+-IS-SUM))))))

(defthm times-of-times
  (equal (times c1 (times c2 term))
         (times (* (ifix c1) (ifix c2)) term))
  :hints (("Goal"
           :in-theory (e/d (ACL2::|arith (* y x)|
                                  ACL2::|arith (* c (* d x))|
                                  ACL2::|arith (* y (* x z))|
                                  times ifix
                                  commutativity-of-*)
                           ()))))

(defthm times-of-0
  (and (equal (times 0 term)
              0)
       (equal (times coef 0)
              0))
  :hints (("Goal"
           :in-theory (e/d (times) ()))))

(local
 (defthm pp-e-list-to-term-of-apply-coef-to-pp-e-list
   (implies (and (mult-formula-checks state)
                 (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst) a))
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt (pp-e-list-to-term-p+ (apply-coef-to-pp-e-list lst coef)) a)
                   (times coef (rp-evlt (pp-e-list-to-term-p+ lst) a))))
   :hints (("goal"
            :do-not-induct t
            :induct (pp-e-list-to-term-p+ lst)
            :in-theory (e/d (times-of-sum
                             pp-e-list-to-term-p+
                             apply-coef-to-pp-e-list)
                            (--
                             sum
                             ifix
                             integerp))))))

(local
 (defthm pp-e-list-to-term-of-append
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst1) a))
                 (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst2) a)))
            (equal (rp-evlt (pp-e-list-to-term-p+ (append lst1 lst2)) a)
                   (sum (rp-evlt (pp-e-list-to-term-p+ lst1) a)
                        (rp-evlt (pp-e-list-to-term-p+ lst2) a))))
   :hints (("goal"
            :induct (pp-e-list-to-term-p+ lst1)
            :do-not-induct t
            :in-theory (e/d (pp-e-list-to-term-p+)
                            (sum
                             --
                             ifix))))))

(local
 (defthm apply-coef-to-pp-e-list-of-sign=nil
   (implies (pp-e-list-p lst)
            (equal (apply-coef-to-pp-e-list lst 1)
                   lst))
   :hints (("Goal"
            :in-theory (e/d (apply-coef-to-pp-e-list) ())))))

(local
 (defthm apply-coef-to-pp-e-list-of-append
   (implies t
            (equal (apply-coef-to-pp-e-list (append x1 x2) coef)
                   (append (apply-coef-to-pp-e-list x1 coef)
                           (apply-coef-to-pp-e-list x2 coef))))
   :hints (("Goal"
            :in-theory (e/d (apply-coef-to-pp-e-list) ())))))

(local
 (defthm apply-coef-to-pp-e-list-of-apply-coef-to-pp-e-list
   (equal (apply-coef-to-pp-e-list (apply-coef-to-pp-e-list lst coef1) coef2)
          (apply-coef-to-pp-e-list lst (* (ifix coef1) (ifix coef2))))
   :hints (("Goal"
            :in-theory (e/d (apply-coef-to-pp-e-list
                             ACL2::|arith (* y x)|
                             ACL2::|arith (* c (* d x))|
                             ACL2::|arith (* y (* x z))|
                             )
                            ())))))

(local
 (defthm bit-list-listp-of-apply-coef-to-pp-e-list
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst1) a)))
            (bit-list-listp
             (rp-evlt-lst-lst
              (collect-pp-e-elements (apply-coef-to-pp-e-list lst1 coef))
              a)))
   :hints (("Goal"
            :in-theory (e/d (apply-coef-to-pp-e-list) ())))))

(local
 (defthmd sign-convert-apply-coef-to-pp-e-list
   (implies (and (syntaxp (not (equal coef ''1)))
                 (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst) a)))
            (equal (rp-evlt (pp-e-list-to-term-p+
                             (apply-coef-to-pp-e-list lst coef))
                            a)
                   (times coef
                          (rp-evlt (pp-e-list-to-term-p+
                                    (apply-coef-to-pp-e-list lst 1))
                                   a))))
   :hints (("goal"
            :do-not-induct t
            :induct (apply-coef-to-pp-e-list lst sign)
            :in-theory (e/d (times-of-sum
                             pp-term-to-pp-e-list
                             and$-pp-e-lists
                             apply-coef-to-pp-e-list
                             and$-pp-e-lists-aux
                             pp-e-list-to-term-p+)
                            (--
                             sum
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
   (defthm pp-e-list-to-term-and$-def-1
     (implies (consp rest)
              (equal (pp-e-list-to-term-and$ (cons x rest))
                     `(binary-and ,x ,(pp-e-list-to-term-and$ rest))))
     :hints (("goal"
              :in-theory (e/d (pp-e-list-to-term-and$) ())))))

  (local
   (defthm pp-e-list-to-term-and$-def-2
     (implies (atom rest)
              (equal (pp-e-list-to-term-and$ (cons x rest))
                     `(binary-and ,x '1)))
     :hints (("goal"
              :in-theory (e/d (pp-e-list-to-term-and$) ())))))

  (local
   (defthm pp-e-list-to-term-and$-def
     (implies t
              (equal (pp-e-list-to-term-and$ (cons x rest))
                     `(binary-and ,x ,(pp-e-list-to-term-and$ rest))))
     :hints (("goal"
              :in-theory (e/d (pp-e-list-to-term-and$) ()))))))

(local
 (encapsulate
   nil

   (defthm atom-merge-sorted-and$-lists
     (equal (consp (merge-sorted-and$-lists lst1 lst2))
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
     (implies (and (mult-formula-checks state)
                   (force (bit-listp (rp-evlt-lst lst1 a)))
                   (force (bit-listp (rp-evlt-lst lst2 a)))
                   (force (true-listp lst1))
                   (force (true-listp lst2))
                   (rp-evl-meta-extract-global-facts))
              (equal (rp-evlt
                      (pp-e-list-to-term-and$
                       (merge-sorted-and$-lists lst1 lst2))
                      a)
                     (and$ (rp-evlt (pp-e-list-to-term-and$ lst1) a)
                           (rp-evlt (pp-e-list-to-term-and$ lst2) a))))
     :hints (("Goal"
              :induct (MERGE-SORTED-AND$-LISTS lst1 lst2)
              :do-not-induct t
              :in-theory (e/d (;;pp-e-list-to-term-and$
                               ;; for soem reason when this is enabled, the proof
                               ;; does too many case-splits.
                               MERGE-SORTED-AND$-LISTS)
                              (len
                               sum valid-sc
                               --
                               and$ or$
                               bitp
                               bit-listp
                               true-listp)))
             ("Subgoal *1/6"
              :expand ((PP-E-LIST-TO-TERM-AND$ LST2)))
             ("Subgoal *1/5"
              :expand ((PP-E-LIST-TO-TERM-AND$ LST1)))
             ("Subgoal *1/4"
              :do-not-induct t
              :expand ((PP-E-LIST-TO-TERM-AND$ LST2)
                       (PP-E-LIST-TO-TERM-AND$ LST1)))))

   (defthm bit-listp-of-merge-sorted-and$-lists
     (implies (and (bit-listp (rp-evlt-lst lst1 a))
                   (bit-listp (rp-evlt-lst lst2 a)))
              (bit-listp (rp-evlt-lst (merge-sorted-and$-lists lst1 lst2)
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
      (implies (and (consp lst)
                    (bit-listp (rp-evlt-lst lst a)))
               (bitp (rp-evlt (car lst) a)))
      :hints (("goal"
               :in-theory (e/d (bitp bit-listp) ())))))

   (local
    (defthm consp-bit-listp-lemma
      (implies (and (not (zp size))
                    (< size (len lst)))
               (consp lst))
      :rule-classes :forward-chaining
      :hints (("goal"
               :in-theory (e/d (len bitp bit-listp) ())))))

   (defthm bit-listp-of-cut-list-by-half
     (implies (and (bit-listp (rp-evlt-lst lst a))
                   (< size (len lst)))
              (and (bit-listp (rp-evlt-lst (mv-nth 0
                                                   (cut-list-by-half lst size))
                                           a))
                   (bit-listp (rp-evlt-lst (mv-nth 1
                                                   (cut-list-by-half lst size))
                                           a))))
     :hints (("goal"
              :do-not-induct t
              :induct (cut-list-by-half lst size)
              :in-theory (e/d (bit-listp
                               cut-list-by-half)
                              (bitp
                               +-is-sum)))))

   (defthm bit-list-listp-of-cut-list-by-half
     (implies (and (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst) a))
                   (< size (len lst)))
              (and (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements
                                                     (mv-nth 0
                                                             (cut-list-by-half lst size)))
                                                    a))
                   (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements (mv-nth 1
                                                                                   (cut-list-by-half lst size)))
                                                    a))))
     :hints (("goal"
              :do-not-induct t
              :induct (cut-list-by-half lst size)
              :in-theory (e/d (
                               bit-list-listp
                               cut-list-by-half)
                              (bitp
                               +-is-sum
                               bit-listp)))))

   (local
    (defthm lemma1
      (implies (not (consp (mv-nth 0 (cut-list-by-half lst size))))
               (equal (mv-nth 1 (cut-list-by-half lst size))
                      lst))
      :hints (("goal"
               :in-theory (e/d (cut-list-by-half) ())))))

   (defthm eval-of-cut-list-by-half
     (implies (and (mult-formula-checks state)
                   (force (bit-listp (rp-evlt-lst lst a)))
                   (force (true-listp lst))
                   (force (< size (len lst)))
                   (rp-evl-meta-extract-global-facts))
              (equal (and$ (rp-evlt (pp-e-list-to-term-and$
                                     (mv-nth 0
                                             (cut-list-by-half lst size)))
                                    a)
                           (rp-evlt (pp-e-list-to-term-and$
                                     (mv-nth 1
                                             (cut-list-by-half lst size)))
                                    a))
                     (rp-evlt (pp-e-list-to-term-and$
                               lst)
                              a)))
     :hints (("goal"
              :do-not-induct t
              :induct (cut-list-by-half lst size)
              :expand ((pp-e-list-to-term-and$ lst))
              :in-theory (e/d (cut-list-by-half)
                              (bitp len
                                    true-listp
                                    +-is-sum)))))

   (local
    (defthm pp-e-list-to-term-p+-when-not-consp
      (implies (atom x)
               (equal (pp-e-list-to-term-p+ x)
                      ''0))
      :hints (("goal"
               :in-theory (e/d (pp-e-list-to-term-p+) ())))))

   (defthm eval-of-cut-list-by-half-with-pp-sum
     (implies (and (mult-formula-checks state)
                   (force (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst) a)))
                   (force (pp-e-list-p lst))
                   (force (< size (len lst)))
                   (rp-evl-meta-extract-global-facts))
              (equal (sum (rp-evlt (pp-e-list-to-term-p+
                                    (mv-nth 0
                                            (cut-list-by-half lst size)))
                                   a)
                          (rp-evlt (pp-e-list-to-term-p+
                                    (mv-nth 1
                                            (cut-list-by-half lst size)))
                                   a))
                     (rp-evlt (pp-e-list-to-term-p+
                               lst)
                              a)))
     :hints (("goal"
              :do-not-induct t
              :induct (cut-list-by-half lst size)
              :expand ((pp-e-list-to-term-p+ lst)
                       (:free (x y)
                              (pp-e-list-to-term-p+ (cons x y))))
              :in-theory (e/d (cut-list-by-half)
                              (bitp
                               sum
                               --
                               +-is-sum
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
 (defthmd pp-e-list-p-implies-true-listp
   (implies (pp-e-list-p x)
            (true-listp x))))

(local
 (defthm bit-listp-of-sort-and$-list
   (implies (force (bit-listp (rp-evlt-lst lst a)))
            (and (bit-listp (rp-evlt-lst (sort-and$-list LST size)
                                         a))))
   :hints (("Goal"
            :do-not-induct t
            :induct (sort-and$-list LST size)
            :in-theory (e/d (bit-listp
                             sort-and$-list
                             pp-e-list-p-implies-true-listp
                             )
                            (bitp
                             +-IS-SUM
                             FLOOR2-IF-F2
                             floor))))))

;; MAIN LEMMA 2: sort-and$-list-is-correct
(defthm eval-of-list-to-term-of-sort-and$-list
  (implies (and (mult-formula-checks state)
                (bit-listp (rp-evlt-lst lst a))
                (true-listp lst)
                (rp-evl-meta-extract-global-facts))
           (equal (rp-evlt
                   (pp-e-list-to-term-and$
                    (sort-and$-list lst len))
                   a)
                  (rp-evlt (pp-e-list-to-term-and$ lst) a)))
  :hints (("Goal"
           :do-not-induct t
           :induct (sort-and$-list lst len)
           :in-theory (e/d (sort-and$-list
                            )
                           (floor
                            +-IS-SUM
                            FLOOR2-IF-F2
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION TRUE-LISTP)
                            (:DEFINITION RP-TERMP)
                            (:DEFINITION RP-TERM-LISTP)
                            (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                            (:REWRITE PP-E-LIST-P-IMPLIES-TRUE-LISTP)
                            (:DEFINITION PP-E-LIST-P)
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
                            ;;                             (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                            (:DEFINITION NATP)
                            (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 3)
                            (:TYPE-PRESCRIPTION MEMBER-EQUAL)
                            (:TYPE-PRESCRIPTION PP-E-LIST-P)
                            len)))))

(local
 (defthm and-list-of-cons-1
   (equal (and-list hash (cons 1 x))
          (and-list 0 x))
   :hints (("Goal"
            :in-theory (e/d (and-list) ())))))

(local
 (defthm and-list-rid-of-hash
   (implies (syntaxp (not (equal hash ''0)))
            (equal (and-list hash x)
                   (and-list 0 x)))
   :hints (("Goal"
            :in-theory (e/d (and-list) ())))))

(encapsulate
  nil

  (local
   (defthm merge-sorted-and$-lists-correct-under-and-list-dummy-lemma
     (equal (AND-LIST 0
                      (RP-EVLT-LST (CONS x lst)
                                   A))
            (and$ (rp-evlt x a)
                  (and-list 0 (rp-evlt-lst lst a))))
     :hints (("Goal"
              :do-not-induct t
              :expand (AND-LIST 0
                                (CONS (RP-EVLT X A)
                                      (RP-EVLT-LST LST A)))
              :in-theory (e/d () ())))))

  (local
   (defthm merge-sorted-and$-lists-correct-under-and-list-dummy-lemma2
     (implies (EQUAL (CAR LST2) ''1)
              (equal (AND-LIST 0 (RP-EVLT-LST LST2 A))
                     (AND-LIST 0 (RP-EVLT-LST (cdr LST2) A))))
     :hints (("Goal"
              :do-not-induct t
              :expand (AND-LIST 0
                                (CONS (RP-EVLT X A)
                                      (RP-EVLT-LST LST A)))
              :in-theory (e/d () ())))))

  (defthm and$-of-bit-fix
    (and (equal (and$ (bit-fix x) y) (and$ x y))
         (equal (and$ y (bit-fix x)) (and$ x y)))
    :hints (("Goal"
             :in-theory (e/d (and$) ()))))

  (local
   (defthm merge-sorted-and$-lists-correct-under-and-list-dummy-lemma3
     (implies (and (consp lst1)
                   (consp lst2)
                   (RP-EQUAL (CAR LST1) (CAR LST2)))
              (equal (AND$ (AND-LIST 0 (RP-EVLT-LST LST1 A))
                           (AND-LIST 0 (RP-EVLT-LST LST2 A)))
                     (AND$ (AND-LIST 0 (RP-EVLT-LST LST1 A))
                           (AND-LIST 0 (RP-EVLT-LST (cdr LST2) A)))))
     :hints (("Goal"
              :do-not-induct t
              :expand ((AND-LIST 0 (RP-EVLT-LST LST1 A))
                       (AND-LIST 0
                                 (CONS (RP-EVLT (CAR LST1) A)
                                       (RP-EVLT-LST (CDR LST2) A)))
                       (AND-LIST 0
                                 (CONS (RP-EVLT (CAR LST1) A)
                                       (RP-EVLT-LST (CDR LST1) A))))
              :in-theory (e/d () ())))))

  (defthm bit-fix-of-and-list
    (equal (bit-fix (and-list hash lst))
           (and-list hash lst)))

  (defthm merge-sorted-and$-lists-correct-under-and-list
    (equal
     (and-list hash (rp-evlt-lst (merge-sorted-and$-lists lst1 lst2) a))
     (and$ (and-list 0 (rp-evlt-lst lst1 a))
           (and-list 0 (rp-evlt-lst lst2 a))))
    :hints (("goal"
             :expand (
                      (MERGE-SORTED-AND$-LISTS LST1 LST2)
                      (AND-LIST 0
                                (CONS (RP-EVLT (CAR LST1) A)
                                      (RP-EVLT-LST (CDR LST1) A)))
                      (AND-LIST 0
                                (CONS (RP-EVLT (CAR LST2) A)
                                      (RP-EVLT-LST (CDR LST2) A)))
                      #|(:free (hash x y)
                      (and-list hash (cons x y)))|#)
             :in-theory (e/d (
                              (:induction merge-sorted-and$-lists))
                             (RP-EVLT-LST-OF-CONS
                              RP-EVL-LST-OF-CONS
                              RP-TRANS-LST
                              (:DEFINITION EX-FROM-RP)
                              (:DEFINITION LEXORDER2-)
                              (:REWRITE BIT-FIX-OPENER)
                              (:REWRITE BIT-LISTP-LEMMA-2)
                              (:REWRITE NOT-INCLUDE-RP)
                              (:DEFINITION INCLUDE-FNC-fn)
                              (:REWRITE DEFAULT-CAR)
                              (:REWRITE DEFAULT-CDR)
                              (:DEFINITION RP-EQUAL)
                              (:META BINARY-OR**/AND**-GUARD-META-CORRECT)
                              (:DEFINITION QUOTEP)
                              (:DEFINITION RP-TRANS)
                              (:TYPE-PRESCRIPTION INCLUDE-FNC-fn)
                              (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS-fn)
                              is-rp
                              and$)))))

  (defthm and-list-of-cons-nil
    (equal (and-list 0 (cons nil other))
           0)
    :hints (("Goal"
             :in-theory (e/d (and-list and$) ()))))

  (defretd cut-list-by-half-to-take-and-nthcdr
    (and (equal first (take size lst))
         (equal second (nthcdr size lst)))
    :fn cut-list-by-half
    :hints (("Goal"
             :in-theory (e/d (cut-list-by-half) ()))))

  (defthm RP-EVL-LST-OF-CONS-without-hyp
    (EQUAL (RP-EVL-LST (cons fn args) ACL2::A)
           (CONS (RP-EVL fn ACL2::A)
                 (RP-EVL-LST args ACL2::A))))

  (defret CUT-LIST-BY-HALF-correct-under-and-list
    (implies (< size (len lst))
             (equal (and$ (and-list hash (rp-evlt-lst first a))
                          (and-list hash (rp-evlt-lst second a)))
                    (and-list 0 (rp-evlt-lst lst a))))
    :fn cut-list-by-half
    :otf-flg t
    :hints (("Goal"
             :do-not-induct t
             :induct (cut-list-by-half lst size)
             :expand ((rp-trans-lst lst)
                      (AND-LIST 0
                                (CONS (RP-EVLT (CAR LST) A)
                                      (RP-EVLT-LST (CDR LST) A))))
             :in-theory (e/d ((:induction cut-list-by-half)
                              cut-list-by-half-to-take-and-nthcdr)
                             (len
                              ;;RP-EVLT-LST-OF-CONS
                              RP-EVL-LST-OF-CONS
                              RP-EVLT-LST-OF-CONS
                              rp-trans-lst)))))

  (local
   (defthm sort-and$-list-correct-under-and-list-dummy-lemma
     (EQUAL (AND-LIST 0
                      (LIST x y))
            (AND-LIST 0
                      (LIST y x)))
     :hints (("Goal"
              :in-theory (e/d (and-list) ())))))

  (local
   (defthm sort-and$-list-correct-under-and-list-dummy-lemma-2
     (EQUAL (AND-LIST 0
                      (LIST x x))
            (AND-LIST 0
                      (LIST x)))
     :hints (("Goal"
              :in-theory (e/d (and-list) ())))))

  (defthm sort-and$-list-correct-under-and-list
    (equal (and-list hash (rp-evlt-lst
                           (sort-and$-list lst len)
                           a))
           (and-list 0 (rp-evlt-lst lst a)))
    :otf-flg t
    :hints (("Goal"
             :do-not-induct t
             :induct (sort-and$-list lst len)

             :in-theory (e/d (sort-and$-list)
                             ())))))

(value-triple (hons-clear t))

(local
 (encapsulate
   nil
   (defthm pp-sum-equals-2
     (implies (integerp a)
              (equal (equal a (sum x y a))
                     (equal (sum x y) 0)))
     :hints (("Goal"
              :in-theory (e/d (sum ifix)
                              (+-is-sum)))))

   #|(defthm times-of-coef-sum
   (implies (and (integerp c1)
   (integerp c2))
   (equal (times (+ c1 c2) term)
   (sum (times c1 term)
   (times c2 term))))
   :hints (("Goal"
   :in-theory (e/d (times sum) (+-IS-SUM)))))|#

   (defthmd merge-times-of-coefs
     (equal (sum (times c1 term)
                 (times c2 term))
            (times (+ (ifix c1) (ifix c2))
                   term))
     :hints (("Goal"
              :in-theory (e/d (times sum) (+-is-sum)))))

   (defthm eval-of-list-to-term-of-merge-sorted-pp-e-lists
     (implies (and (mult-formula-checks state)
                   (force (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst1) a)))
                   (force (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst2) a)))
                   (force (pp-e-list-p lst1))
                   (force (pp-e-list-p lst2))
                   (rp-evl-meta-extract-global-facts))
              (equal (rp-evlt
                      (pp-e-list-to-term-p+
                       (merge-sorted-pp-e-lists lst1 lst2))
                      a)
                     (sum (rp-evlt (pp-e-list-to-term-p+ lst1) a)
                          (rp-evlt (pp-e-list-to-term-p+ lst2) a))))
     :hints (("Goal"
              :induct (merge-sorted-pp-e-lists lst1 lst2)
              :do-not-induct t
              :expand ((:free (x y) (pp-e-list-to-term-p+ (cons x y)))
                       (pp-e-list-to-term-p+ lst1)
                       (pp-e-list-to-term-p+ lst2))
              :in-theory (e/d (;;pp-e-list-to-term-and$
                               ;; for soem reason when this is enabled, the proof
                               ;; does too many case-splits.
                               merge-sorted-pp-e-lists
                               merge-times-of-coefs)
                              (len
                               sum valid-sc
                               --
                               and$ or$
                               bitp
                               bit-listp
                               ;;PP-E-LIST-P
;BIT-LIST-LISTP
                               true-listp)))))

   (defthm bit-list-list-of-merge-sorted-pp-e-lists
     (implies (and (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst1) a))
                   (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst2) a)))
              (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements (merge-sorted-pp-e-lists LST1 lst2))
                                               a)))
     :hints (("Goal"
              :do-not-induct t
              :induct (merge-sorted-pp-e-lists LST1 lst2)
              :in-theory (e/d (bit-listp
                               bit-list-listp
                               merge-sorted-pp-e-lists)
                              (bitp
                               floor)))))))

(local
 (defthm cut-list-by-half-returns-pp-e-list
   (implies (and (pp-e-list-p lst)
                 (< size (len lst)))
            (and (pp-e-list-p (mv-nth 0 (cut-list-by-half lst size)))
                 (pp-e-list-p (mv-nth 1 (cut-list-by-half lst size)))))
   :hints (("goal"
            :in-theory (e/d (cut-list-by-half) (+-is-sum))))))

(local
 (defthm bit-list-listp-of-sort-pp-e-lists
   (implies (and (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst) a))
                 (pp-e-list-p lst))
            (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements (sort-pp-e-lists lst
                                                                                     size))
                                             a)))
   :hints (("Goal"
            :do-not-induct t
            :induct (sort-pp-e-lists lst size)
            :in-theory (e/d (merge-times-of-coefs
                             sort-pp-e-lists)
                            (floor
                             +-is-sum
                             floor2-if-f2))))))

(local
 (defthm eval-of-sort-pp-e-lists-is-correct
   (implies (and (mult-formula-checks state)
                 (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst) a))
                 (pp-e-list-p lst)
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt (pp-e-list-to-term-p+ (sort-pp-e-lists lst size)) a)
                   (rp-evlt (pp-e-list-to-term-p+ lst) a)))
   :hints (("Goal"
            :do-not-induct t
            :induct (sort-pp-e-lists lst size)
            :in-theory (e/d (merge-times-of-coefs
                             sort-pp-e-lists
                             len
                             PP-E-LIST-TO-TERM-P+)
                            (floor
                             bitp
                             --
                             +-IS-SUM
                             FLOOR2-IF-F2
                             sum))))))

(local
 (defthm consp-of-apply-sign
   (equal (consp (apply-coef-to-pp-e-list lst coef))
          (consp lst))
   :hints (("Goal"
            :in-theory (e/d (apply-coef-to-pp-e-list) ())))))

(local
 (defthm len-of-apply-sign
   (equal (len (apply-coef-to-pp-e-list lst coef))
          (len lst))
   :hints (("Goal"
            :in-theory (e/d (apply-coef-to-pp-e-list len) ())))))

(local
 (defthmd pull-out-common-multiplier
   (implies (and (integerp m)
                 (integerp x)
                 (integerp y))
            (and (equal (sum (* m x)
                             (* m y))
                        (* m (sum x y)))
                 (equal (+ (* m x)
                           (* m y))
                        (* m (+ x y)))))
   :hints (("Goal"
            :in-theory (e/d ((:REWRITE ACL2::|(* x (+ y z))|)
                             sum
                             ifix)
                            (+-IS-SUM))))))

(local
 (defthm merge-sorted-pp-e-lists-simple-of-apply-sign
   (implies (and (pp-e-list-p lst1)
                 (pp-e-list-p lst2)
                 (not (equal (ifix coef) 0)))
            (equal (merge-sorted-pp-e-lists (apply-coef-to-pp-e-list lst1 coef)
                                            (apply-coef-to-pp-e-list lst2 coef))
                   (apply-coef-to-pp-e-list (merge-sorted-pp-e-lists lst1 lst2)
                                            coef)))
   :otf-flg t
   :hints (("Goal"
            :induct (merge-sorted-pp-e-lists lst1 lst2)
            :do-not-induct t
            :in-theory (e/d (pull-out-common-multiplier
                             +-IS-SUM
                             apply-coef-to-pp-e-list
                             merge-sorted-pp-e-lists) ())))))

(local
 (defthmd merge-sorted-pp-e-lists-simple-of-apply-sign-reverse
   (implies (and (pp-e-list-p lst1)
                 (pp-e-list-p lst2)
                 (not (equal (ifix coef) 0)))
            (equal (apply-coef-to-pp-e-list (merge-sorted-pp-e-lists lst1 lst2)
                                            coef)
                   (merge-sorted-pp-e-lists (apply-coef-to-pp-e-list lst1 coef)
                                            (apply-coef-to-pp-e-list lst2 coef))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d (merge-sorted-pp-e-lists-simple-of-apply-sign) ())))))

#|(local
(defthm merge-sorted-pp-e-lists-simple-of-apply-sign-2
(implies (and (pp-e-list-p lst1)
(pp-e-list-p lst2)
(not (equal (ifix coef) 0))
(syntaxp (or (atom lst2)
(not (equal (car lst2) 'apply-coef-to-pp-e-list)))))
(equal (merge-sorted-pp-e-lists (apply-coef-to-pp-e-list lst1 coef)
lst2)
(apply-coef-to-pp-e-list (merge-sorted-pp-e-lists
lst1
(apply-coef-to-pp-e-list lst2 coef))
coef)))
:hints (("Goal"
;:induct (merge-sorted-pp-e-lists-simple lst1 lst2) ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
:do-not-induct t
:in-theory (e/d (merge-sorted-pp-e-lists-simple-of-apply-sign-reverse)
(merge-sorted-pp-e-lists-simple-of-apply-sign))))))|#

(local
 (defthm cut-list-by-half-of-signed-pp-e-list-0
   (implies (and (pp-e-list-p lst)
                 (< size (len lst)))
            (equal (mv-nth
                    0
                    (cut-list-by-half (apply-coef-to-pp-e-list lst coef) size))
                   (apply-coef-to-pp-e-list
                    (mv-nth 0
                            (cut-list-by-half lst size))
                    coef)))
   :hints (("Goal"
            :in-theory (e/d (cut-list-by-half
                             apply-coef-to-pp-e-list)
                            (+-IS-SUM))))))

(local
 (defthm cut-list-by-half-of-signed-pp-e-list-1
   (implies (and (pp-e-list-p lst)
                 (< size (len lst)))
            (equal (mv-nth
                    1
                    (cut-list-by-half (apply-coef-to-pp-e-list lst coef) size))
                   (apply-coef-to-pp-e-list
                    (mv-nth 1
                            (cut-list-by-half lst size))
                    coef)))
   :hints (("Goal"
            :in-theory (e/d (cut-list-by-half
                             apply-coef-to-pp-e-list)
                            (+-IS-SUM))))))

#|(local
(defthm PP-E-LIST-P-implies-fc
(implies (PP-E-LIST-P x)
(IF (ATOM X)
(EQ X NIL)
(AND (CONSP (CAR X))
(BOOLEANP (CAAR X))
(TRUE-LISTP (CDAR X))
(PP-E-LIST-P (CDR X)))))
:rule-classes :forward-chaining))|#

(local
 (defthmd pos-len-is
   (equal (< 0 (LEN LST))
          (consp lst))
   :hints (("Goal"
            :in-theory (e/d (len)
                            (+-IS-SUM))))))

(local
 (encapsulate
   nil

   (defthm sort-pp-e-lists-of-apply-sign
     (implies (and (pp-e-list-p lst)
                   (not (equal (ifix coef) 0)))
              (equal (sort-pp-e-lists (apply-coef-to-pp-e-list lst coef) size)
                     (apply-coef-to-pp-e-list (sort-pp-e-lists lst size)
                                              coef)))
     :otf-flg t
     :hints (("Goal"
              :induct (sort-pp-e-lists lst size)
              :do-not-induct t
              :in-theory (e/d (apply-coef-to-pp-e-list
                               pull-out-common-multiplier
                               sort-pp-e-lists
                               pos-len-is
                               +-IS-SUM
                               MERGE-SORTED-PP-E-LISTS-SIMPLE-OF-APPLY-SIGN-REVERSE)
                              (pp-e-list-p

                               floor
                               MERGE-SORTED-PP-E-LISTS-SIMPLE-OF-APPLY-SIGN
                               floor2-if-f2
                               ;;merge-sorted-pp-e-lists-simple-of-apply-sign-2
                               )))))

   (defthmd sort-pp-e-lists-of-apply-sign-reverse
     (implies (and (pp-e-list-p lst)
                   (not (equal (ifix coef) 0)))
              (equal (apply-coef-to-pp-e-list (sort-pp-e-lists lst size)
                                              coef)
                     (sort-pp-e-lists (apply-coef-to-pp-e-list lst coef) size)))
     :otf-flg t
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (sort-pp-e-lists-of-apply-sign)
                              ()))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FLATTEN LEMMAS

(local
 (defthm pp-e-list-p-and$-pp-e-lists
   (implies (and (pp-e-list-p lst1)
                 (pp-e-list-p lst2)
                 (pp-e-list-p acc)
                 (integerp coef)
                 )
            (pp-e-list-p (and$-pp-e-lists lst1 lst2 acc coef)))))

(local
 (progn
   (defthm and$-pp-e-lists-aux-returns-bit-list-listp
     (implies (and (mult-formula-checks state)
                   (bit-listp (rp-evlt-lst (pp-e->elements cur) a))
                   (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst2) a))
                   (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements acc) a))
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (collect-pp-e-elements (and$-pp-e-lists-aux cur lst2 acc))
                                a)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-e-lists-aux cur lst2 acc)
              :in-theory (e/d (RP-TERM-LIST-FIX
                               rp-evlt-lst-lst
                               and$-pp-e-lists
                               and$-pp-e-lists-aux
                               pp-term-to-pp-e-list
                               bit-list-listp)
                              ()))))

   (defthm and$-pp-e-lists-returns-bit-list-listp
     (implies (and (mult-formula-checks state)
                   (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst1) a))
                   (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst2) a))
                   (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements acc) a))
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (collect-pp-e-elements (and$-pp-e-lists lst1 lst2 acc coef))
                                a)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-e-lists lst1 lst2 acc coef)
              :in-theory (e/d (RP-TERM-LIST-FIX
                               rp-evlt-lst-lst
                               and$-pp-e-lists
                               and$-pp-e-lists-aux
                               pp-term-to-pp-e-list
                               bit-list-listp) ()))))

   (defret pp-term-to-pp-e-list-returns-bit-list-listp
     (implies (and (mult-formula-checks state)
                   (pp-term-p term)
                   (rp-termp term)
                   (integerp coef)
                   (valid-sc term a)
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (collect-pp-e-elements result)
                                a)))
     :fn pp-term-to-pp-e-list
     :hints (("goal"
              :do-not-induct t
              :induct (pp-term-to-pp-e-list term coef)
              :expand ((:free (x) (RP-TERM-LIST-FIX (LIST x))))
              :in-theory (e/d (;;RP-TERM-LIST-FIX
                               rp-evlt-lst-lst
                               pp-term-p
                               pp-term-to-pp-e-list
                               bit-list-listp)
                              ((:TYPE-PRESCRIPTION LEN)
                               (:REWRITE ACL2::OR*-TRUE-SECOND)
                               (:TYPE-PRESCRIPTION ACL2::BINARY-OR*)
                               (:DEFINITION EX-FROM-RP)
                               (:REWRITE ACL2::LEN-MEMBER-EQUAL-LOOP$-AS)
                               falist-consistent-aux
                               (:REWRITE NOT-INCLUDE-RP)
                               (:REWRITE VALID-SC-EX-FROM-RP-2)
                               (:DEFINITION EVAL-AND-ALL)
                               (:DEFINITION INCLUDE-FNC-FN)
                               (:DEFINITION VALID-SC)
                               (:DEFINITION RP-TERMP)
                               (:REWRITE RP-EVL-OF-RP-EQUAL2)
                               (:REWRITE RP-TERMP-OF-RP-TRANS)
                               (:REWRITE IS-IF-RP-TERMP)
                               (:DEFINITION RP-TERM-LISTP))))))))

(progn
  (local
   (defthmd and$-pp-e-lists-aux-extract-acc
     (implies (and (syntaxp (not (equal acc ''nil))))
              (equal (and$-pp-e-lists-aux cur lst2 acc)
                     (append (and$-pp-e-lists-aux cur lst2 nil)
                             acc)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-e-lists-aux cur lst2 acc)
              :in-theory (e/d (and$-pp-e-lists-aux
                               and$-pp-e-lists)
                              (sum
                               --
                               ifix))))))

  (local
   (defthmd and$-pp-e-lists-aux-extract-acc-reverse
     (implies t
              (equal (append (and$-pp-e-lists-aux cur lst2 nil)
                             acc)
                     (and$-pp-e-lists-aux cur lst2 acc)))
     :hints (("goal"

              :in-theory (e/d (and$-pp-e-lists-aux-extract-acc)
                              ())))))

  (local
   (defthm and$-pp-e-lists-extract-acc
     (implies (and (syntaxp (not (equal acc ''nil)))
                   (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts))
              (equal (and$-pp-e-lists lst1 lst2 acc coef)
                     (append (and$-pp-e-lists lst1 lst2 nil coef)
                             acc)))
     :hints (("goal"
              :do-not-induct t
              ;;:induct (and$-pp-e-lists-extract-acc-induct lst1 lst2 acc acc sign)
              :induct (and$-pp-e-lists lst1 lst2 acc coef)
              :in-theory (e/d (and$-pp-e-lists-aux-extract-acc
                               pp-e-list-to-term-p+
                               and$-pp-e-lists)
                              (sum
                               xor
                               --
                               ifix))))))

  (local
   (defthm and$-pp-e-lists-aux-extract-sign-and-acc-1
     (implies (syntaxp (not (equal acc ''nil)))
              (equal (and$-pp-e-lists-aux cur lst2 acc)
                     (append (apply-coef-to-pp-e-list
                              (and$-pp-e-lists-aux
                               (change-pp-e cur :coef 1) lst2 nil)
                              (pp-e->coef cur))
                             acc)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-e-lists-aux cur lst2 acc)
              :in-theory (e/d (and$-pp-e-lists-aux
                               and$-pp-e-lists
                               APPLY-COEF-TO-PP-E-LIST)
                              (sum
                               --
                               ifix))))))

  (local
   (defthm and$-pp-e-lists-aux-extract-sign-and-acc-2
     (implies (and (syntaxp (equal acc ''nil))
                   (case-split (not (equal (PP-E->coef cur) 1))))
              (equal (and$-pp-e-lists-aux cur lst2 acc)
                     (append (apply-coef-to-pp-e-list
                              (and$-pp-e-lists-aux
                               (change-pp-e cur :coef 1) lst2 nil)
                              (pp-e->coef cur))
                             acc)))
     :hints (("goal"
              :use and$-pp-e-lists-aux-extract-sign-and-acc-1))))

  (local
   (defret true-listp-of-AND$-PP-E-LISTS-AUX
     (implies (true-listp acc)
              (true-listp res-acc))
     :fn AND$-PP-E-LISTS-AUX
     :hints (("Goal"
              :in-theory (e/d (AND$-PP-E-LISTS-AUX) ())))))

  (local
   (defthm and$-pp-e-lists-extract-sign-and-acc
     (implies (and (syntaxp (not (and (equal acc ''nil)
                                      (equal coef ''1))))
                   (integerp coef))
              (equal (and$-pp-e-lists lst1 lst2 acc coef)
                     (append (apply-coef-to-pp-e-list
                              (and$-pp-e-lists lst1 lst2 nil 1)
                              coef)
                             acc)))
     :otf-flg t
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-e-lists lst1 lst2 acc coef)
              :in-theory (e/d (;;and$-pp-e-lists-aux-extract-acc
                               pp-e-list-to-term-p+
                               APPLY-COEF-TO-PP-E-LIST
                               and$-pp-e-lists)
                              (sum
                               --
                               ifix))))))

  (local
   (defthm true-list-fix-of-apply-coef-to-pp-e-list
     (equal (true-list-fix (apply-coef-to-pp-e-list lst coef))
            (apply-coef-to-pp-e-list lst coef))
     :hints (("Goal"
              :in-theory (e/d (apply-coef-to-pp-e-list) ())))))

  (local
   (defthm and$-pp-e-lists-aux-of-applied-sign
     (implies (integerp coef)
              (equal (and$-pp-e-lists-aux cur
                                          (apply-coef-to-pp-e-list lst2 coef)
                                          acc)
                     (append (apply-coef-to-pp-e-list
                              (and$-pp-e-lists-aux cur lst2 nil)
                              coef)
                             acc)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-e-lists-aux cur lst2 acc)
              :in-theory (e/d ((:REWRITE ACL2::|(* 0 x)|)
                               (:REWRITE ACL2::|(* x (if a b c))|)
                               (:REWRITE ACL2::|(* y (* x z))|)
                               (:REWRITE ACL2::|(* y x)|)
                               and$-pp-e-lists-aux
                               APPLY-COEF-TO-PP-E-LIST)
                              ())))))

  (local
   (defthm and$-pp-e-lists-of-applied-with-same-sign
     (implies (and (integerp coef)
                   (integerp main-coef))
              (equal (and$-pp-e-lists (apply-coef-to-pp-e-list lst1 coef)
                                      (apply-coef-to-pp-e-list lst2 coef)
                                      acc main-coef)
                     (and$-pp-e-lists lst1
                                      lst2
                                      acc (* (expt coef 2) main-coef))))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-e-lists lst1
                                       lst2
                                       acc main-sign)
              :in-theory (e/d ((:REWRITE ACL2::|(* 0 x)|)
                               (:REWRITE ACL2::|(* x (if a b c))|)
                               (:REWRITE ACL2::|(* y (* x z))|)
                               (:REWRITE ACL2::|(* y x)|)
                               ACL2::|arith (* -1 x)|
                               and$-pp-e-lists
                               apply-coef-to-pp-e-list)
                              (append-equal2
                               )))
             (and stable-under-simplificationp
                  '(:use ((:instance when-mult-of-two-integers-is-1
                                     (x coef)
                                     (y (PP-E->COEF (CAR LST1)))))))))))

#|(defret PP-E-LIST-P-of-PP-TERM-TO-PP-E-LIST
(implies (booleanp sign)
(pp-e-list-p result))
:fn PP-TERM-TO-PP-E-LIST
:hints (("Goal"
:in-theory (e/d (PP-TERM-TO-PP-E-LIST) ()))))|#

(local
 (defthmd equiv-of-merged-sorted-pp-e-list-with-apply-coef-to-pp-e-list
   (implies (and (PP-E-LIST-P LST1)
                 (PP-E-LIST-P LST2)
                 (PP-E-LIST-P LST1-2)
                 (PP-E-LIST-P LST2-2)
                 (NOT (EQUAL (IFIX COEF) 0))
                 (equal lst1 (apply-coef-to-pp-e-list lst1-2 coef))
                 (equal lst2 (apply-coef-to-pp-e-list lst2-2 coef)))
            (and  #|(equal (len (merge-soted-pp-e-list lst1 lst2))
             (len (merge-sorted-pp-e-lists lst1-2 lst2-2)))
             (equal (collect-pp-e-elements (merge-sorted-pp-e-lists lst1 lst2))
             (collect-pp-e-elements (merge-sorted-pp-e-lists lst1-2 lst2-2)))|#
             (equal (apply-coef-to-pp-e-list (merge-sorted-pp-e-lists lst1-2 lst2-2) coef)
                    (merge-sorted-pp-e-lists lst1 lst2))))
   :otf-flg t
   :hints (("Goal"
            :do-not-induct t
            ;;:induct (MERGE-SORTED-PP-E-LISTS LST1-2 LST2-2)
            :in-theory (e/d
                        (;;APPLY-COEF-TO-PP-E-LIST
                         MERGE-SORTED-PP-E-LISTS
                         MERGE-SORTED-PP-E-LISTS-SIMPLE-OF-APPLY-SIGN-REVERSE)
                        (+-IS-SUM
                         ;;ATOM-MERGE-SORTED-PP-E-LISTS
                         ;;merge-sorted-pp-e-lists-simple-of-apply-sign-2
                         MERGE-SORTED-PP-E-LISTS-SIMPLE-OF-APPLY-SIGN))))))

(local
 (defthm strip-cdrs-of-apply-coef-to-pp-e-list
   (equal (collect-pp-e-elements (apply-coef-to-pp-e-list lst sign))
          (collect-pp-e-elements lst))
   :hints (("Goal"
            :in-theory (e/d (apply-coef-to-pp-e-list) ())))))

(local
 (defthmd len-equiv-of-merged-sorted-pp-e-list-with-apply-coef-to-pp-e-list
   (implies (and (PP-E-LIST-P LST1)
                 (PP-E-LIST-P LST2)
                 (PP-E-LIST-P LST1-2)
                 (PP-E-LIST-P LST2-2)
                 (NOT (EQUAL (IFIX COEF) 0))
                 (equal lst1 (apply-coef-to-pp-e-list lst1-2 coef))
                 (equal lst2 (apply-coef-to-pp-e-list lst2-2 coef)))
            (and  (equal (len (merge-sorted-pp-e-lists lst1 lst2))
                         (len (merge-sorted-pp-e-lists lst1-2 lst2-2)))
                  (equal (equal (len (merge-sorted-pp-e-lists lst1 lst2))
                                (len (merge-sorted-pp-e-lists lst1-2 lst2-2)))
                         t)
                  (equal (collect-pp-e-elements (merge-sorted-pp-e-lists lst1 lst2))
                         (collect-pp-e-elements (merge-sorted-pp-e-lists lst1-2 lst2-2)))
                  #|(equal (apply-coef-to-pp-e-list (merge-sorted-pp-e-lists lst1 lst2) sign)
                  (merge-sorted-pp-e-lists lst1-2 lst2-2))|#))
   :otf-flg t
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance
                   equiv-of-merged-sorted-pp-e-list-with-apply-coef-to-pp-e-list
                   ))
            ;;:induct (MERGE-SORTED-PP-E-LISTS LST1-2 LST2-2)
            :in-theory (e/d
                        (;;APPLY-COEF-TO-PP-E-LIST
                         ;;MERGE-SORTED-PP-E-LISTS
                         ;;MERGE-SORTED-PP-E-LISTS-SIMPLE-OF-APPLY-SIGN-REVERSE
                         )
                        (+-IS-SUM
                         ;;ATOM-MERGE-SORTED-PP-E-LISTS
                         ;;merge-sorted-pp-e-lists-simple-of-apply-sign-2
                         MERGE-SORTED-PP-E-LISTS-SIMPLE-OF-APPLY-SIGN))))))

(local
 (defthmd len-of-AND$-PP-E-LISTS-with-apply-coef-to-pp-e-list
   (implies (and (PP-E-LIST-P LST1)
                 (PP-E-LIST-P LST2)
                 (PP-E-LIST-P LST1-2)
                 (PP-E-LIST-P LST2-2)
                 (integerp coef1)
                 (integerp coef2)
                 (equal lst1 (apply-coef-to-pp-e-list lst1-2 coef2))
                 (equal lst2 (apply-coef-to-pp-e-list lst2-2 coef2)))
            (and
             (equal (len (AND$-PP-E-LISTS lst1 lst2 acc coef1))
                    (len (AND$-PP-E-LISTS lst1-2 lst2-2 acc coef1)))))
   :otf-flg t
   :hints (("Goal"
            :do-not-induct t

            ;;:induct (AND$-PP-E-LISTS LST1-2 LST2-2 acc sign)
            :in-theory (e/d
                        (;;APPLY-COEF-TO-PP-E-LIST
                         )
                        (LEN-EQUALS-2
                         and$-pp-e-lists-aux-extract-sign-and-acc-1
                         and$-pp-e-lists-aux-extract-sign-and-acc-2
                         ;;AND$-PP-E-LISTS-OF-APPLIED-WITH-SAME-SIGN
                         ;;APPLY-COEF-TO-PP-E-LIST-OF-APPEND
                         ))))))

#|(local
(defthm apply-coef-to-pp-e-list-move-to-other-side
(implies (and (equal lst1 (apply-coef-to-pp-e-list lst2 coef))
#|(syntaxp (case-match lst1
(('mv-nth & ('PP-TERM-TO-PP-E-LIST & ''nil)) ;
t)))|#
(pp-e-list-p lst1)
(pp-e-list-p lst2))
(and (equal (apply-coef-to-pp-e-list lst1 coef) lst2)
(equal lst1 (apply-coef-to-pp-e-list lst2 coef))))
:rule-classes :forward-chaining
:hints (("Goal"
:in-theory (e/d () ())))))|#

;; :i-am-here ;; skip from here....
;; (local
;;  (defthmd and$-pp-e-lists-insert-sign
;;    (implies (syntaxp (and (case-match lst1
;;                             (('MV-NTH & ('PP-TERM-TO-PP-E-LIST & ''T)) t))
;;                           (case-match lst2
;;                             (('MV-NTH & ('PP-TERM-TO-PP-E-LIST & ''T)) t))))
;;             (equal (and$-pp-e-lists lst1
;;                                     lst2
;;                                     acc
;;                                     main-coef)
;;                    (and$-pp-e-lists (apply-coef-to-pp-e-list lst1 coef)
;;                                     (apply-coef-to-pp-e-list lst2 coef)
;;                                     acc
;;                                     main-coef)))))

;; (local
;;  (defthm
;;    merge-sorted-pp-e-lists-simple-of-apply-sign-3
;;    (implies
;;     (and (pp-e-list-p lst1)
;;          (pp-e-list-p lst2)
;;          (syntaxp (quotep lst1)))
;;     (equal
;;      (merge-sorted-pp-e-lists lst1
;;                               (apply-coef-to-pp-e-list lst2 sign))
;;      (apply-coef-to-pp-e-list
;;       (merge-sorted-pp-e-lists
;;        (apply-coef-to-pp-e-list lst1 sign) lst2)
;;       sign)))
;;    :hints
;;    (("goal"
;;      :do-not-induct t
;;      :in-theory
;;      (e/d (merge-sorted-pp-e-lists-simple-of-apply-sign-reverse)
;;           (merge-sorted-pp-e-lists-simple-of-apply-sign
;;            merge-sorted-pp-e-lists-simple-of-apply-sign-2
;;            ))))))
;; :i-am-here ;; skip before here

(local
 (defret len-of-AND$-PP-E-LISTS-AUX
   (equal (len res-acc)
          (+ (len acc)
             (len lst2)))
   :fn AND$-PP-E-LISTS-AUX
   :hints (("Goal"
            :do-not-induct t
            :induct (<fn> cur lst2 acc)
            :in-theory (e/d (len
                             and$-pp-e-lists-aux )
                            (LEN-EQUALS-2))))))

(local
 (defret len-of-AND$-PP-E-LISTS
   (implies t; (consp lst1)
            (equal (len res-acc)
                   (+ (len acc)
                      (* (len lst1)
                         (len lst2)))))
   :fn AND$-PP-E-LISTS
   :hints (("Goal"
            :induct (len lst1)
            :do-not-induct t
            :in-theory (e/d (AND$-PP-E-LISTS len)
                            ())))))

(local
 (defret len-of-<fn>
   (implies (and (force (<= size (len lst)))
                 )
            (and (equal (len first)
                        (nfix size))
                 (equal (len second)
                        (- (len lst) (nfix size)))))
   :fn CUT-LIST-BY-HALF
   :hints (("Goal"
            :in-theory (e/d (CUT-LIST-BY-HALF
                             len)
                            (LEN-EQUALS-2))))))

(local
 (defret len-of-<fn>
   (<= (len res)
       (+ (len first)
          (len second)))
   :fn MERGE-SORTED-PP-E-LISTS
   :rule-classes (:rewrite :linear)
   :hints (("Goal"
            :in-theory (e/d (MERGE-SORTED-PP-E-LISTS) ())))))

(local
 (defret len-of-SORT-PP-E-LISTS
   (<= (len res)
       (len lst))
   :fn sort-pp-e-lists
   :rule-classes (:rewrite :linear)
   :hints (("Goal"
            :in-theory (e/d (sort-pp-e-lists)
                            (MERGE-SORTED-PP-E-LISTS)))
           (and stable-under-simplificationp
                '(:use ((:instance
                         MERGE-SORTED-PP-E-LISTS
                         (first (SORT-PP-E-LISTS (MV-NTH 0
                                                         (CUT-LIST-BY-HALF LST (FLOOR (LEN LST) 2)))
                                                 (FLOOR (LEN LST) 2)))
                         (second (SORT-PP-E-LISTS (MV-NTH 1
                                                          (CUT-LIST-BY-HALF LST (FLOOR (LEN LST) 2)))
                                                  (+ (LEN LST) (- (FLOOR (LEN LST) 2))))))))))))

;; :i-am-here ;;skipping below
;; (Local
;;  (encapsulate nil

;;    (local
;;     (define pp-term-to-pp-e-list-two-sign-induct (term sign1 sign2)
;;       :measure (cons-count term)
;;       :hints
;;       (("goal" :in-theory (e/d (measure-lemmas) nil)))
;;       (declare (ignorable term sign1 sign2))

;;       :verify-guards nil
;;       (b* ((term (ex-from-rp term)))
;;         (cond
;;          ((or (binary-and-p term)
;;               (binary-or-p term)
;;               (binary-xor-p term))
;;           (b* ((x (cadr term))
;;                (y (caddr term)))
;;             (list*
;;              (pp-term-to-pp-e-list-two-sign-induct x nil nil)
;;              (pp-term-to-pp-e-list-two-sign-induct x sign1 sign2)
;;              (pp-term-to-pp-e-list-two-sign-induct y nil nil)
;;              (pp-term-to-pp-e-list-two-sign-induct y sign1 sign2))))
;;          ((binary-?-p term)
;;           (b* ((test (cadr term))
;;                (x (caddr term))
;;                (y (cadddr term)))
;;             (list*
;;              (pp-term-to-pp-e-list-two-sign-induct test sign1 sign2)
;;              (pp-term-to-pp-e-list-two-sign-induct x sign1 sign2)
;;              (pp-term-to-pp-e-list-two-sign-induct y sign1 sign2))))
;;          ((binary-not-p term)
;;           (list* (pp-term-to-pp-e-list-two-sign-induct
;;                   (cadr term) (not sign1) (not sign2))
;;                  (pp-term-to-pp-e-list-two-sign-induct
;;                   (cadr term) (not sign1) sign2)
;;                  (pp-term-to-pp-e-list-two-sign-induct
;;                   (cadr term) sign1 (not sign2))
;;                  (pp-term-to-pp-e-list-two-sign-induct
;;                   (cadr term) sign1 sign2)))
;;          ((pp-p term)
;;           (pp-term-to-pp-e-list-two-sign-induct (cadr term) sign1 sign2))
;;          (t nil)))))

;;    (local
;;     (define hidden-pp-term-to-pp-e-list (term coef &key (term-size-limit 'term-size-limit))
;;       :verify-guards nil
;;       :returns (mv res too-large-p)
;;       (pp-term-to-pp-e-list term coef)
;;       ///
;;       (defret pp-e-list-p-of<fn>
;;         (implies (and (integerp coef) (rp-termp term))
;;                  (pp-e-list-p res)))))

;;    (local
;;     (defthmd pp-term-to-pp-e-list-extract-sign-lemma
;;       (and (implies (and (syntaxp (not (atom lst1)))
;;                          (rp-termp lst1)
;;                          (integerp coef)
;;                          (integerp c1)
;;                          (integerp c2)
;;                          (not (equal (ifix coef) 0))
;;                          (equal (* c1 c2) coef))
;;                     (and (equal (mv-nth 0 (pp-term-to-pp-e-list lst1 coef))
;;                                 (apply-coef-to-pp-e-list
;;                                  (mv-nth 0 (hidden-pp-term-to-pp-e-list lst1 c1))
;;                                  c2))
;;                          (equal (pp-term-to-pp-e-list lst1 1)
;;                                 (hidden-pp-term-to-pp-e-list lst1 1))))
;;            #|(implies (syntaxp (not (atom lst1)))
;;            (equal (pp-term-to-pp-e-list lst1 nil) ; ; ; ; ; ;
;;            (hidden-pp-term-to-pp-e-list lst1 nil)))|#)
;;       :hints (("Goal"
;;                :expand ((:free (x y) (APPLY-COEF-TO-PP-E-LIST (cons x y) COEF))
;;                         (:free (x y) (APPLY-COEF-TO-PP-E-LIST (cons x y) (- COEF)))
;;                         (APPLY-COEF-TO-PP-E-LIST NIL COEF)
;;                         (APPLY-COEF-TO-PP-E-LIST NIL (- COEF)))
;;                :induct (pp-term-to-pp-e-list lst1 coef)
;;                :in-theory (e/d
;;                            ( ACL2::|(* -1 x)|
;;                              MERGE-SORTED-PP-E-LISTS-SIMPLE-OF-APPLY-SIGN-REVERSE
;;                              pp-term-to-pp-e-list
;;                              APPLY-COEF-TO-PP-E-LIST
;;                              hidden-pp-term-to-pp-e-list)
;;                            (MERGE-SORTED-PP-E-LISTS-SIMPLE-OF-APPLY-SIGN))))))

;;    (local
;;     (defthmd pp-term-to-pp-e-list-extract-sign-lemma-2
;;       (and (implies (and (syntaxp (not (atom lst1)))
;;                          )
;;                     (equal (pp-term-to-pp-e-list lst1 nil)
;;                            (hidden-pp-term-to-pp-e-list lst1 nil)))
;;            #|(implies (syntaxp (not (atom lst1)))
;;            (equal (pp-term-to-pp-e-list lst1 nil) ; ; ;
;;            (hidden-pp-term-to-pp-e-list lst1 nil)))|#)
;;       :hints (("Goal"

;;                :in-theory (e/d (hidden-pp-term-to-pp-e-list)
;;                                ())))))

;;    (local
;;     (defthmd APPLY-COEF-TO-PP-E-LIST-of-MERGE-SORTED-PP-E-LISTS-equiv
;;       (implies (AND (PP-E-LIST-P LST3)
;;                     (PP-E-LIST-P LST4))
;;                (equal (equal (merge-sorted-pp-e-lists lst1 lst2)
;;                              (apply-coef-to-pp-e-list
;;                               (merge-sorted-pp-e-lists lst3 lst4)
;;                               t))
;;                       (equal (merge-sorted-pp-e-lists lst1 lst2)
;;                              (merge-sorted-pp-e-lists (apply-coef-to-pp-e-list lst3 t)
;;                                                       (apply-coef-to-pp-e-list lst4 t)))))
;;       :hints (("Goal"
;;                :in-theory (e/d (merge-sorted-pp-e-lists-simple-of-apply-sign-reverse)
;;                                (MERGE-SORTED-PP-E-LISTS-SIMPLE-OF-APPLY-SIGN))))))

;;    (local
;;     (defthmd dummy-and$-pp-e-lists-lemma
;;       (implies (and (equal y
;;                            (apply-coef-to-pp-e-list x t))
;;                     (equal y2
;;                            (apply-coef-to-pp-e-list x2 t)))
;;                (equal (AND$-PP-E-LISTS y y2 nil nil)
;;                       (and$-pp-e-lists x x2 nil nil)))))

;;    (local
;;     (defthmd dummy-MERGE-SORTED-PP-E-LISTS-lemma
;;       (implies (and (equal y
;;                            (apply-coef-to-pp-e-list x t))
;;                     (equal y2
;;                            (apply-coef-to-pp-e-list x2 t))
;;                     (AND (PP-E-LIST-P x)
;;                          (PP-E-LIST-P y)
;;                          (PP-E-LIST-P y2)
;;                          (PP-E-LIST-P x2)))
;;                (equal (MERGE-SORTED-PP-E-LISTS y y2)
;;                       (apply-coef-to-pp-e-list
;;                        (MERGE-SORTED-PP-E-LISTS x x2)
;;                        t)))
;;       :hints (("Goal"
;;                :in-theory (e/d () ())))))

;;    (defret pp-term-to-pp-e-list-extract-sign-1
;;      (implies (and (syntaxp (not (and (equal sign ''nil))))
;;                    (rp-termp term)
;;                    (booleanp sign)
;;                    (booleanp sign2))
;;               ;;(test term sign sign2)

;;               (and (equal (mv-nth 1 (pp-term-to-pp-e-list term (xor sign sign2)))
;;                           (mv-nth 1 (pp-term-to-pp-e-list term sign2)))
;;                    (equal (len (mv-nth 0 (pp-term-to-pp-e-list term (xor sign sign2))))
;;                           (len (mv-nth 0 (pp-term-to-pp-e-list term sign2))))
;;                    (equal (mv-nth 0 (pp-term-to-pp-e-list term (xor sign sign2)))
;;                           (apply-coef-to-pp-e-list
;;                            (mv-nth 0 (pp-term-to-pp-e-list term sign2))
;;                            sign))))
;;      :otf-flg t
;;      :fn pp-term-to-pp-e-list
;;      :hints (
;;              #|("Subgoal *1/2"
;;              :use ((:instance ; ;
;;              APPLY-COEF-TO-PP-E-LIST-move-to-other-side ; ;
;;              (lst1 (MV-NTH 0 ; ;
;;              (PP-TERM-TO-PP-E-LIST (CADDDR (EX-FROM-RP TERM)) ; ;
;;              NIL))) ; ;
;;              (lst2 (MV-NTH 0 ; ;
;;              (PP-TERM-TO-PP-E-LIST (CADDDR (EX-FROM-RP TERM)) ; ;
;;              T))) ; ;
;;              (sign t)) ; ;
;;              (:instance ; ;
;;              len-of-AND$-PP-E-LISTS-with-apply-coef-to-pp-e-list ; ;
;;              (sign nil) ; ;
;;              (sign2 sign2) ; ;
;;              (lst1 (MV-NTH 0 ; ;
;;              (PP-TERM-TO-PP-E-LIST (CADR (EX-FROM-RP TERM)) ; ;
;;              nil))) ; ;
;;              (lst2 (MV-NTH 0 ; ;
;;              (PP-TERM-TO-PP-E-LIST (CADDR (EX-FROM-RP TERM)) ; ;
;;              nil))) ; ;
;;              (lst1-2 (MV-NTH 0 ; ;
;;              (PP-TERM-TO-PP-E-LIST (CADR (EX-FROM-RP TERM)) ; ;
;;              sign2))) ; ;
;;              (lst2-2 (MV-NTH 0 ; ;
;;              (PP-TERM-TO-PP-E-LIST (CADdR (EX-FROM-RP TERM)) ; ;
;;              sign2))))) ; ;
;;              )|#

;;              ("goal"
;;               :do-not '(generalize fertilize)
;;               :expand ((booleanp sign)
;;                        (HIDDEN-PP-TERM-TO-PP-E-LIST TERM NIL)
;;                        (pp-term-to-pp-e-list term sign)
;;                        (pp-term-to-pp-e-list term nil)
;;                        (pp-term-to-pp-e-list term t)
;;                        (pp-term-to-pp-e-list term sign2))
;;               :do-not-induct t
;;               :induct (pp-term-to-pp-e-list-two-sign-induct term sign sign2)
;;               :in-theory (e/d
;;                           (dummy-and$-pp-e-lists-lemma
;;                            dummy-MERGE-SORTED-PP-E-LISTS-lemma
;;                            pp-term-to-pp-e-list-extract-sign-lemma-2
;;                            pp-term-to-pp-e-list-extract-sign-lemma
;;                            APPLY-COEF-TO-PP-E-LIST-of-MERGE-SORTED-PP-E-LISTS-equiv
;;                            merge-sorted-pp-e-lists-simple-of-apply-sign-3

;;                            ;;and$-pp-e-lists-insert-sign
;;                            len-of-AND$-PP-E-LISTS-with-apply-coef-to-pp-e-list
;;                            equiv-of-merged-sorted-pp-e-list-with-apply-coef-to-pp-e-list
;;                            len-equiv-of-merged-sorted-pp-e-list-with-apply-coef-to-pp-e-list
;;                            pp-term-to-pp-e-list-two-sign-induct
;;                            ;;merge-sorted-pp-e-lists-simple-of-apply-sign-reverse
;;                            apply-coef-to-pp-e-list
;;                            )
;;                           (sum
;;                            (:E PP-E)
;;                            ;;APPLY-COEF-TO-PP-E-LIST-MOVE-TO-OTHER-SIDE

;;                            ;;AND$-PP-E-LISTS-OF-APPLIED-WITH-SAME-SIGN
;;                            ;;merge-sorted-pp-e-lists-simple-of-apply-sign-2
;;                            ;;MERGE-SORTED-PP-E-LISTS-SIMPLE-OF-APPLY-SIGN
;;                            ATOM-MERGE-SORTED-PP-E-LISTS
;;                            --
;;                            ifix))
;;               )))

;;    (defthm pp-term-to-pp-e-list-extract-sign
;;      (implies (and (syntaxp (not (and (equal sign ''nil))))
;;                    (rp-termp term)
;;                    (booleanp sign))
;;               (and (equal (mv-nth 0 (pp-term-to-pp-e-list term sign))
;;                           (apply-coef-to-pp-e-list
;;                            (mv-nth 0 (pp-term-to-pp-e-list term nil))
;;                            sign))
;;                    (equal (mv-nth 1 (pp-term-to-pp-e-list term sign))
;;                           (mv-nth 1 (pp-term-to-pp-e-list term nil)))))
;;      :otf-flg t
;;      :hints (("goal"
;;               :do-not-induct t
;;               :use ((:instance pp-term-to-pp-e-list-extract-sign-1
;;                                (sign2 t)))
;;               :in-theory (e/d
;;                           (booleanp
;;                            APPLY-COEF-TO-PP-E-LIST)
;;                           ()))))))

;; :i-am-here ;; skipped above

(local
 (defthm and$-pp-e-lists-aux-is-correct-lemma-2
   (implies (and (bitp x)
                 (bitp (sum (-- x) y))
                 (not (bitp y))
                 (integerp y))
            (and (equal x 1)
                 (equal y 2)))
   :hints (("Goal"
            :in-theory (e/d (sum)
                            (+-IS-SUM))))
   :rule-classes :forward-chaining))

(local
 (defthm bitp-of-times
   (implies (and (bitp x)
                 (bitp y))
            (bitp (times x y)))))

(local
 (defthmd *-is-times
   (implies (and (integerp x)
                 (integerp y))
            (equal (* x y)
                   (times x y)))
   :hints (("Goal"
            :in-theory (e/d (times) ())))))

(local
 (defthm and$-pp-e-lists-aux-is-correct
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (pp-e-list-p lst2)
                 (rp-term-listp (pp-e->elements cur))
                 (bit-listp (rp-evlt-lst (pp-e->elements cur) a))
                 (true-listp (pp-e->elements cur))
                 ;;(not (pp-e->sign cur))
                 (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst2) a)))
            (equal (rp-evlt (pp-e-list-to-term-p+ (and$-pp-e-lists-aux cur lst2 nil)) a)
                   (times (pp-e->coef cur)
                          (times (rp-evlt (pp-e-list-to-term-and$ (pp-e->elements cur)) a)
                                 (rp-evlt (pp-e-list-to-term-p+ lst2) a)))))
   :hints (("goal"
            :induct (and$-pp-e-lists-aux cur lst2 nil )
            :do-not-induct t
            :expand (#|(pp-e-list-to-term (cons (cons (car (car lst2))
                     (append cur (cdr (car lst2))))
                     (and$-pp-e-lists-aux cur (cdr lst2)
                     nil nil)))||#)
            :in-theory (e/d (*-is-times
                             and$-pp-e-lists-aux
                             pp-e-list-to-term-p+
                             and$-is-times
                             RP-TERM-LIST-FIX
                             pp-e-list-to-term-and$
                             ;;times
                             ;;ifix
                             )
                            (sum
                             binar-and-abs-is-and$-2
                             and$
                             --
                             sum
                             ;;ifix
                             times
                             times-of-times
                             bitp
                             true-listp))))))

(local
 (defthm PP-E-LIST-TO-TERM-P+-of-append
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt (PP-E-LIST-TO-TERM-P+ (append lst1 lst2)) a)
                   (sum (rp-evlt (PP-E-LIST-TO-TERM-P+ lst1) a)
                        (rp-evlt (PP-E-LIST-TO-TERM-P+ lst2) a))))
   :hints (("Goal"
            :expand (PP-E-LIST-TO-TERM-P+ lst2)
            :in-theory (e/d (PP-E-LIST-TO-TERM-P+) ())))))

(local
 (defthm PP-E-LIST-TO-TERM-P+-of-PP-E-LIST-TO-TERM-P+
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (integerp coef))
            (equal (rp-evlt (PP-E-LIST-TO-TERM-P+
                             (apply-coef-to-pp-e-list lst1 coef))
                            a)
                   (times coef (rp-evlt (pp-e-list-to-term-p+ lst1) a))))
   :hints (("Goal"
            :in-theory (e/d (PP-E-LIST-TO-TERM-P+
                             APPLY-COEF-TO-PP-E-LIST)
                            ())))))

(local
 (defthm and$-pp-e-lists-is-correct
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (pp-e-list-p lst1)
                 (pp-e-list-p lst2)
                 (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst2) a))
                 (bit-list-listp (rp-evlt-lst-lst (collect-pp-e-elements lst1) a))
                 (integerp coef))
            (equal (rp-evlt (pp-e-list-to-term-p+ (and$-pp-e-lists lst1 lst2 nil coef)) a)
                   (times coef
                          (times (rp-evlt (pp-e-list-to-term-p+ lst1) a)
                                 (rp-evlt (pp-e-list-to-term-p+ lst2) a)))))
   :hints (("goal"
            :induct (and$-pp-e-lists lst1 lst2 nil nol)
            :do-not-induct t
            :in-theory (e/d (*-is-times
                             pp-e-list-to-term-p+
                             and$-is-times
                             pp-e-list-to-term-and$
                             and$-pp-e-lists)
                            (sum
                             times-of-times
                             times
                             binar-and-abs-is-and$-2
                             and$
                             --
                             bitp
                             true-listp))))))

(value-triple (hons-clear t))

(defthm bitp-pattern-for-binary-?-in-summation
  (implies (and (bitp test) (bitp then) (bitp else))
           (bitp (sum else
                      (and$ test then)
                      (-- (and$ test else))))))

(defthm bitp-pattern-for-binary-xor-in-summation
  (implies (and (bitp x) (bitp y) )
           (bitp (sum x y (-- (and$ x y)) (-- (and$ x y))))))

(defthm bitp-pattern-for-binary-or-in-summation
  (implies (and (bitp x) (bitp y) )
           (bitp (sum x y (-- (and$ x y))))))

(progn
  (local
   (use-arith-5 t))

  (defthmd times-of--
    (and (equal (times (- x) y)
                (- (times x y)))
         (equal (times x (- y))
                (- (times x y))))
    :hints (("Goal"
             :in-theory (e/d (times ifix) ()))))
  (local
   (use-arith-5 nil)))

(defthmd -of-sum
  (equal (- (sum x y))
         (sum (- x) (- y)))
  :hints (("Goal"
           :in-theory (e/d (sum ifix) ()))))

(defthm bitp-of-binary-?-form
  (implies (and (bitp x) (bitp y) (bitp z))
           (bitp (SUM z
                      (TIMES x y)
                      (- (TIMES x z)))))
  :hints (("Goal"
           :in-theory (e/d () ()))))

(defthm bitp-of-binary-xor-form
  (implies (and (bitp x) (bitp y))
           (bitp (SUM x
                      y
                      (- (TIMES x y))
                      (- (TIMES x y)))))
  :hints (("Goal"
           :in-theory (e/d () ()))))

(defthm bitp-of-binary-or-form
  (implies (and (bitp x) (bitp y))
           (bitp (SUM x y
                      (- (TIMES x y)))))
  :hints (("Goal"
           :in-theory (e/d () ()))))

(defthmd times-with-coef=2
  (equal (times 2 x)
         (sum x x))
  :hints (("Goal"
           :in-theory (e/d (times sum) ()))))

;; MAIN LEMMA1.
(defret rp-evlt_of_pp-e-list-to-term_of_pp-term-to-pp-e-list
  (implies (and (mult-formula-checks state)
                (pp-term-p term)
                (rp-termp term)
                (valid-sc term a)
                (rp-evl-meta-extract-global-facts)
                (integerp coef)
                ;;(not too-large-p)
                (or (equal coef 1)
                    (equal coef -1))
                )
           (equal (rp-evlt (pp-e-list-to-term-p+ result) a)
                  (times coef (rp-evlt term a))
                  ))
  :fn pp-term-to-pp-e-list
  :hints (("goal"
           :do-not-induct t
           :expand ((:free (term) (RP-TERM-LISTP (LIST TERM)))
                    (PP-TERM-P TERM :STRICT NIL))
           :induct (pp-term-to-pp-e-list term coef)
           :in-theory (e/d* (times-with-coef=2
                             -of-sum
                             *-is-times
                             and$-is-times
                             RP-TERM-LIST-FIX
                             pp-term-to-pp-e-list
                             not$-to-pp-sum
                             or$-to-pp-sum
                             binary-xor-to-pp-sum
                             binary-?-to-pp-sum
                             ---of-pp-sum
                             pp-e-list-to-term-and$
                             pp-e-list-to-term-p+
                             APPLY-COEF-TO-PP-E-LIST
                             regular-eval-lemmas
                             len
                             --
                             times-of--)
                            (times-of-times

                             (:rewrite bit-listp-lemma-2)
                             (:rewrite rationalp-implies-acl2-numberp)

                             ;;pp-term-to-pp-e-list-extract-sign
                             (:type-prescription len)
                             (:rewrite len-of-and$-pp-e-lists)

                             (:definition pp-e-list-p)
                             (:rewrite rp-term-listp-is-true-listp)
                             (:definition true-listp)
                             (:definition rp-term-listp)
                             rp-termp
                             (:rewrite is-if-rp-termp)
                             (:rewrite extract-from-rp-pseudo-term-listp)
                             (:rewrite sort-pp-e-lists-of-apply-sign)
                             pp-term-p
                             (:rewrite rp-termp-implies-subterms)
                             (:linear acl2::apply$-badgep-properties . 1)
                             (:definition acl2::apply$-badgep)
                             (:definition subsetp-equal)
                             (:definition member-equal)
                             (:rewrite
                              acl2::member-equal-newvar-components-1)
                             (:definition len)
                             (:rewrite not-include-rp)
                             (:rewrite pp-e-list-p-and$-pp-e-lists)
                             (:rewrite +-is-sum)
                             (:rewrite sum-of-negated-elements)
                             (:definition include-fnc-fn)
                             (:definition ex-from-rp)
                             (:definition apply-coef-to-pp-e-list)
                             ;;(:rewrite atom-merge-sorted-pp-e-lists)
                             ;;(:definition two-pp-list-cancel-each-other)

                             sum
                             valid-sc
                             and$
                             bitp
                             or$
                             ifix
                             (:rewrite valid-sc-ex-from-rp-2)
                             (:definition eval-and-all)
                             valid-sc
                             ;;                             (:rewrite acl2::o-p-o-infp-car)
                             (:rewrite default-cdr)
                             (:definition rp-termp)
                             (:type-prescription valid-sc)
                             (:meta acl2::mv-nth-cons-meta)
                             (:rewrite pp-e-list-p-implies-true-listp)
                             (:rewrite default-car)
                             integerp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;

(local
 (in-theory (disable RP-EVL-LST-OF-CONS)))

(with-output
  :off :all
  (local
   (progn
     (create-regular-eval-lemma -- 1 mult-formula-checks)
     (create-regular-eval-lemma logbit$inline 2 mult-formula-checks)
     (create-regular-eval-lemma BINARY-? 3 mult-formula-checks)
     (create-regular-eval-lemma BINARY-and 2 mult-formula-checks)
     (create-regular-eval-lemma BINARY-or 2 mult-formula-checks)
     (create-regular-eval-lemma BINARY-xor 2 mult-formula-checks)
     (create-regular-eval-lemma BINARY-NOT 1 mult-formula-checks))))

(local
 (defthm RP-EVL-LST-OF-CONS-with-syntaxp
   (IMPLIES (and (CONSP ACL2::X-LST)
                 (syntaxp (and (consp ACL2::X-LST)
                               (or (equal (car ACL2::X-LST)
                                          'cons)
                                   (equal (car ACL2::X-LST)
                                          'quote)))))
            (EQUAL (RP-EVL-LST ACL2::X-LST ACL2::A)
                   (CONS (RP-EVL (CAR ACL2::X-LST) ACL2::A)
                         (RP-EVL-LST (CDR ACL2::X-LST)
                                     ACL2::A))))
   :hints (("Goal"
            :in-theory (e/d (RP-EVL-LST-OF-CONS) ())))))

(local
 (defthm PP-E-LIST-TO-TERM-AND$-redef
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt (PP-E-LIST-TO-TERM-AND$ lst) a)
                   (and-list 0 (rp-evlt `(list . ,lst) a))))
   :hints (("Goal"
            :induct (PP-E-LIST-TO-TERM-AND$ lst)
            :do-not-induct t
            :in-theory (e/d (PP-E-LIST-TO-TERM-AND$
                             and-list)
                            ())))))

(defthm and-list-remove-hash
  (implies (syntaxp (not (equal hash ''0)))
           (equal (and-list hash lst)
                  (and-list 0 lst)))
  :hints (("Goal"
           :in-theory (e/d (and-list) ()))))

(defthm rp-evlt-of-create-and-list-instance
  (implies (and (rp-evl-meta-extract-global-facts)
                (mult-formula-checks state)
                (valid-sc-subterms lst a))
           (equal (rp-evlt (create-and-list-instance lst) a)
                  (and-list 0 (rp-evlt-lst lst A))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((rp-trans (CONS 'LIST LST))
                    (:free (hash x y)
                           (and-list hash (cons x y))))
           :in-theory (e/d (create-and-list-instance
                            regular-rp-evl-of_logbit$inline_when_mult-formula-checks
                            regular-rp-evl-of_and-list_when_mult-formula-checks)
                           (and*
                            and-list
                            rp-trans)))))

(local
 (defthm pp-e-list-to-term-p+-to-pp-e-list-to-term-pp-lst
   (implies (and (mult-formula-checks state)
                 (pp-e-list-p lst)
                 (rp-evl-meta-extract-global-facts)
                 (valid-sc-subterms-lst (collect-pp-e-elements lst) a))
            (equal (rp-evlt (pp-e-list-to-term-p+ lst) a)
                   (sum-list (rp-evlt-lst (pp-e-list-to-term-pp-lst lst)  a))))
   :hints (("Goal"
            :do-not-induct t
            :expand ((:free (x y hash) (and-list hash (cons x y))))
            :induct (pp-e-list-to-term-p+ lst)
            :in-theory (e/d (pp-e-list-to-term-p+
                             regular-rp-evl-of_logbit$inline_when_mult-formula-checks
                             pp-e-list-to-term-pp-lst)
                            ())))))

(local
 (defthm valid-sc-and-apply-coef-to-pp-e-list
   (implies (and ;;(true-listp pp-e-list)
             (valid-sc-subterms-lst (collect-pp-e-elements pp-e-list) a))
            (valid-sc-subterms-lst (collect-pp-e-elements (apply-coef-to-pp-e-list pp-e-list coef)) a))
   :hints (("goal"
            :in-theory (e/d (valid-sc-subterms-lst
                             apply-coef-to-pp-e-list)
                            (valid-sc-subterms))))))

(local
 (defthm pp-e-list-to-term-pp-lst_of_pp-term-to-pp-e-list
   (implies (and (mult-formula-checks state)
                 (pp-term-p term)
                 (integerp coef)
                 (or (= coef 1)
                     (= coef -1))
                 (rp-termp term)
                 (valid-sc term a)
                 (rp-evl-meta-extract-global-facts))
            (equal (sum-list (rp-evlt-lst (pp-e-list-to-term-pp-lst
                                           (mv-nth 0 (pp-term-to-pp-e-list term coef)))
                                          a))
                   (times coef (rp-evlt term a))))
   :hints (("goal"
            :do-not-induct t
            :use ((:instance rp-evlt_of_pp-e-list-to-term_of_pp-term-to-pp-e-list))
            :in-theory (e/d ()
                            (--
                             rp-evlt_of_pp-e-list-to-term_of_pp-term-to-pp-e-list

                             sum
                             valid-sc
                             and$
                             bitp
                             or$
                             ifix
                             (:REWRITE VALID-SC-EX-FROM-RP-2)
                             (:DEFINITION EVAL-AND-ALL)
                             valid-sc
                             ;;                             (:REWRITE ACL2::O-P-O-INFP-CAR)
                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION RP-TERMP)
                             (:TYPE-PRESCRIPTION VALID-SC)
                             (:META ACL2::MV-NTH-CONS-META)
                             (:REWRITE PP-E-LIST-P-IMPLIES-TRUE-LISTP)
                             (:REWRITE DEFAULT-CAR)
                             integerp))))))

#|(RP-EVL-OF-TRANS-LIST (RP-TRANS-LST LST)
A)||#

;; (local
;;  (defthm ...
;;    (RP-EVL-OF-TRANS-LIST (LIST (LIST '-- term)) A)

(local
 (defthmd and-list-to-binary-and
   (equal (and-list 0 (list a b))
          (and$ a b))
   :hints (("Goal"
            :in-theory (e/d (and-list
                             and$) ())))))

(defret pp-remove-extraneous-sc-correct
  (implies (and (rp-evl-meta-extract-global-facts)
                (mult-formula-checks state))
           (equal (rp-evlt res-term a)
                  (rp-evlt term a)))
  :fn pp-remove-extraneous-sc
  :hints (("Goal"
           :do-not-induct t
           :induct (pp-remove-extraneous-sc term)
           :expand ((:free (term) (nth 3 term)))
           :in-theory (e/d* (pp-remove-extraneous-sc
                             rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
                             regular-eval-lemmas)
                            (rp-trans
                             rp-termp
                             rp-evlt-of-ex-from-rp
                             (:DEFINITION EX-FROM-RP)
                             (:DEFINITION INCLUDE-FNC-fn)
                             (:REWRITE NOT-INCLUDE-RP)
                             (:DEFINITION INCLUDE-FNC-SUBTERMS-fn)
                             (:DEFINITION RP-EQUAL)
                             (:REWRITE RP-EQUAL-IS-SYMMETRIC)
                             (:REWRITE RP-EVLT-OF-RP-EQUAL)
                             (:REWRITE WHEN-EX-FROM-RP-IS-1)
                             (:REWRITE WHEN-EX-FROM-RP-IS-0)
                             (:TYPE-PRESCRIPTION BINARY-?-P$INLINE)
                             )))))

(defret pp-remove-extraneous-sc-lst-correct
  (implies (and (rp-evl-meta-extract-global-facts)
                (mult-formula-checks state))
           (equal (rp-evlt-lst res-lst a)
                  (rp-evlt-lst lst a)))
  :fn pp-remove-extraneous-sc-lst
  :hints (("Goal"
           :expand ((:free (term) (nth 3 term)))
           :in-theory (e/d* (pp-remove-extraneous-sc-lst)
                            ()))))

(defret pp-remove-extraneous-sc-correct-2
  (implies (and (rp-evl-meta-extract-global-facts)
                (mult-formula-checks state))
           (and (equal (equal (ifix (rp-evlt res-term a))
                              (ifix (rp-evlt term a)))
                       t)
                (equal (equal (rp-evlt res-term a)
                              (rp-evlt term a))
                       t)))
  :fn pp-remove-extraneous-sc
  :hints (("Goal"
           :do-not-induct t
           )))

(defthm sum-list-of-append-wog
  (implies (and (mult-formula-checks state)
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list (rp-evlt-lst (append-wog x y) a))
                  (sum (sum-list (rp-evlt-lst x a))
                       (sum-list (rp-evlt-lst y a)))))
  :hints (("Goal"
           :induct (append-wog x y)
           :do-not-induct t
           :in-theory (e/d (append-wog) ()))))

(local
 (create-regular-eval-lemma AND-LIST 2 mult-formula-checks))

(local
 (create-regular-eval-lemma sum-list 1 mult-formula-checks))

(local
 (create-regular-eval-lemma s-c-res 3 mult-formula-checks))

(local
 (defthm rp-evlt-lst-of-list-to-lst
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts))
            (equal (sum-list (rp-evlt-lst (list-to-lst x) a))
                   (sum-list (rp-evlt x a))))
   :hints (("goal"
            :expand ((list-to-lst x))
            :in-theory (e/d* (regular-eval-lemmas)
                             ())))))

(defthm valid-sc-subterms-of-negate-lst
  (implies (valid-sc-subterms lst a)
           (valid-sc-subterms (negate-lst lst enabled) a))
  :hints (("Goal"
           :induct (NEGATE-LST-AUX LST)
           :in-theory (e/d (negate-lst
                            is-rp
                            is-if is-equals
                            NEGATE-LST-AUX)
                           ()))))

(defthm rp-evlt-lst-of-negate-lst
  (implies (and (mult-formula-checks state)
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list (rp-evlt-lst (negate-lst lst enabled) a))
                  (if enabled
                      (times -1 (sum-list (rp-evlt-lst lst a)))
                    (sum-list (rp-evlt-lst lst a)))))
  :hints (("Goal"
           :induct (negate-lst-aux lst)
           :do-not-induct t
           :in-theory (e/d (NEGATE-LST
                            negate-lst-aux)
                           ()))))

#|(defthm sum-list-eval-of-append-wog
(equal (sum-list-eval (append-wog x y) a)
(sum (sum-list-eval x a)
(sum-list-eval y a)))
:hints (("Goal"
:induct (append-wog x y)
:do-not-induct t
:in-theory (e/d (append-wog) ()))))|#

(defthm integerp-of-
  (implies (integerp x)
           (integerp (- x))))

;; A MAIN LEMMA
(defret pp-flatten-correct-lemma
  (implies (and (mult-formula-checks state)
                (pp-term-p term)
                (rp-termp term)
                (integerp coef)
                (or (= coef 1)
                    (= coef -1))
                (valid-sc term a)
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list (rp-evlt-lst pp-lst a))
                  (times coef (rp-evlt (pp-remove-extraneous-sc term) a))))
  :fn pp-flatten
  :hints (("goal"
           :do-not-induct t
           :in-theory (e/d* (pp-flatten
                             regular-eval-lemmas
                             and-list-to-binary-and
                             IFIX)
                            (TO-LIST*-SUM-EVAL
                             pp-term-p
                             rp-trans-is-term-when-list-is-absent
                             pp-remove-extraneous-sc-correct
                             ;;rp-evlt-of-ex-from-rp
                             ;;rp-trans
                             valid-sc
                             not-include-rp-means-valid-sc
                             rp-trans
                             (:rewrite ex-from-synp-lemma1)
                             ;;                             (:rewrite acl2::o-p-o-infp-car)
                             (:definition is-synp$inline)
                             (:rewrite not-include-rp)
                             ;;pp-term-to-pp-e-list-extract-sign
                             (:definition rp-termp)

                             ;;rp-trans-lst
                             )))))

(defret pp-flatten-correct
  (implies (and (mult-formula-checks state)
                (pp-term-p term)
                (valid-sc term a)
                (rp-termp term)
                (rp-evl-meta-extract-global-facts)
                (or (= coef 1)
                    (= coef -1)))
           (equal (sum-list (rp-evlt-lst pp-lst a))
                  (times coef (rp-evlt term a))))
  :fn pp-flatten
  :hints (("Goal"
           :do-not-induct t
; :use ((:instance pp-e-list-to-term-pp-lst_of_pp-term-to-pp-e-list))
           :in-theory (e/d* (;;rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
                             regular-eval-lemmas
                             and-list-to-binary-and)
                            (TO-LIST*-SUM-EVAL
                             ;;pp-e-list-to-term-pp-lst_of_pp-term-to-pp-e-list
                             PP-TERM-P
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                             ;;rp-evlt-of-ex-from-rp
                             ;;RP-TRANS
                             VALID-SC
                             NOT-INCLUDE-RP-MEANS-VALID-SC
                             rp-trans
                             (:REWRITE EX-FROM-SYNP-LEMMA1)
                             ;;                             (:REWRITE ACL2::O-P-O-INFP-CAR)
                             (:DEFINITION IS-SYNP$INLINE)
                             (:REWRITE NOT-INCLUDE-RP)
                             ;;PP-TERM-TO-PP-E-LIST-EXTRACT-SIGN
                             (:DEFINITION RP-TERMP)
                             ;;RP-TRANS-LST
                             )))))

(defthm rp-evl-to-of-create-list-instance
  (equal (sum-list (rp-evlt (create-list-instance lst) a))
         (sum-list (rp-evlt-lst lst a)))
  :hints (("Goal"
           :in-theory (e/d (create-list-instance
                            sum-list
;binary-sum
                            )
                           (SUM-OF-IFIX)))))

#|(defthmd RP-EVLt-LST-OF-CONS
(implies (consp lst)
(equal (rp-evlt-lst lst a)
(cons (rp-evlt (car lst) a)
(rp-evlt-lst (cdr lst) a))))
:hints (("Goal"
;:expand (rp-evlt-lst lst a) ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
:in-theory (e/d () ()))))||#

(defthm rp-evlt-of-list
  (equal (rp-evlt (cons 'list lst) a)
         (rp-evlt-lst lst a)))

(progn

  (local
   (in-theory (disable ;;RP-TRANS-OPENER
               TO-LIST*-SUM-EVAL)))

  (with-output :off :all
    (progn
      (create-regular-eval-lemma logbit$inline 2 mult-formula-checks)
      (create-regular-eval-lemma bitp 1 mult-formula-checks)
      (create-regular-eval-lemma ifix 1 mult-formula-checks)
      (create-regular-eval-lemma binary-and 2 mult-formula-checks)
      (create-regular-eval-lemma binary-sum 2 mult-formula-checks)))

  (defthm valid-rp-bitp-lemma
    (implies (and (mult-formula-checks state)
                  (valid-sc term a)
                  (rp-evl-meta-extract-global-facts)
                  (case-match term (('rp ''bitp &) t)))
             (and (bitp (rp-evlt (caddr term) a))
                  (bitp (rp-evlt term a))))
    :hints (("Goal"
             :in-theory (e/d (is-rp
                              valid-sc-single-step
                              is-if is-equals)
                             (valid-sc)))))

  (defthm bitp-of-bits-of-term-with-ex-from-rp
    (implies (and (mult-formula-checks state)
                  (rp-evl-meta-extract-global-facts)
                  (b* ((term (ex-from-rp term)))
                    (case-match term (('logbit$inline & &) t))))
             (and (bitp (rp-evlt term a))
                  (bitp (rp-evl term a))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance rp-evlt-of-ex-from-rp)
                   (:instance rp-evl-of-ex-from-rp))
             :in-theory (e/d* (is-rp
                               regular-eval-lemmas
                               is-if is-equals)
                              (valid-sc
                               rp-evl-of-ex-from-rp
                               EVL-OF-EXTRACT-FROM-RP
                               rp-evlt-of-ex-from-rp)))))

  (local
   (defthm bitp-valid-single-bitp
     (implies (and (mult-formula-checks state)
                   (valid-sc cur a)
                   (VALID-SINGLE-BITP cur)
                   (rp-evl-meta-extract-global-facts))
              (bitp (rp-evlt cur a)))
     :hints (("Goal"
              :in-theory (e/d (VALID-SINGLE-BITP
                               valid-sc-single-step
                               is-rp)
                              (bitp
                               valid-sc))))))

  (defthm rp-evlt-of-bitp
    (implies (and (mult-formula-checks state)
                  (rp-evl-meta-extract-global-facts))
             (equal (RP-EVLT (LIST 'BITP x) A)
                    (bitp (rp-evlt x a))))
    :hints (("Goal"
             :in-theory (e/d* (regular-eval-lemmas)
                              ()))))

  (local
   (defret sort-sum-meta-aux-aux-returns-bit-list-listp
     (implies (and valid
                   (mult-formula-checks state)
                   (valid-sc cur a)
                   (rp-evl-meta-extract-global-facts))
              (bit-listp (rp-evlt-lst (pp-e->elements e) a)))
     :fn SORT-SUM-META-AUX-AUX
     :hints (("Goal"
              :in-theory (e/d (RP-TERM-LIST-FIX
                               sort-sum-meta-aux-aux
                               is-rp
                               valid-sc-single-step
                               RP-EVLt-LST-OF-CONS
                               rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
                               )
                              (;;rp-trans-opener
                               rp-evlt-of-ex-from-rp
                               RP-TRANS-LST-IS-LST-WHEN-LIST-IS-ABSENT
                               (:EXECUTABLE-COUNTERPART RP-TRANS-LST)
                               (:REWRITE VALID-SC-EX-FROM-RP-2)
                               (:TYPE-PRESCRIPTION O<)
                               (:DEFINITION EVAL-AND-ALL)
                               (:REWRITE EVAL-OF-LOGBIT)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                               ex-from-rp
                               valid-sc
                               RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                               EX-FROM-RP-LEMMA1
                               (:REWRITE DEFAULT-CAR)
                               RP-TRANS-LST
                               rp-termp
                               bitp
                               (:REWRITE RP-EVL-LST-OF-CONS-WITH-SYNTAXP)
                               (:TYPE-PRESCRIPTION VALID-SC)
                               (:TYPE-PRESCRIPTION MULT-FORMULA-CHECKS)
                               (:TYPE-PRESCRIPTION BIT-LISTP)
                               ;;                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                               (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                               (:DEFINITION INCLUDE-FNC-fn)
                               (:TYPE-PRESCRIPTION O-P)
                               rp-trans))))))

  (local
   (defthm SORT-SUM-META-AUX-returns-bit-list-listp
     (implies (and (MV-NTH 0 (SORT-SUM-META-AUX term))
                   (mult-formula-checks state)
                   (valid-sc term a)
                   (rp-evl-meta-extract-global-facts))
              (BIT-LIST-LISTP
               (RP-EVLT-LST-LST (collect-pp-e-elements (MV-NTH 1 (SORT-SUM-META-AUX term)))
                                A)))
     :hints (("Goal"
              :induct (SORT-SUM-META-AUX term)
              :do-not-induct t
              :expand ((RP-TRANS-LST (CDR TERM))
                       (RP-TRANS-LST (CDdR TERM))
                       (RP-TRANS-LST (CDddR TERM)))
              :in-theory (e/d (SORT-SUM-META-AUX)
                              (bitp
                               valid-sc
                               rp-trans))))))

  (defthm COLLECT-PP-E-ELEMENTS-of-append
    (equal (COLLECT-PP-E-ELEMENTS (append lst1 lst2))
           (append (COLLECT-PP-E-ELEMENTS lst1)
                   (COLLECT-PP-E-ELEMENTS lst2))))

  (local
   (defthm SORT-SUM-META-AUX2-returns-bit-list-listp
     (implies (and (MV-NTH 0 (SORT-SUM-META-AUX2 term))
                   (mult-formula-checks state)
                   (valid-sc term a)
                   (rp-termp term)
                   (rp-evl-meta-extract-global-facts))
              (BIT-LIST-LISTP
               (RP-EVLT-LST-LST (collect-pp-e-elements (MV-NTH 1 (SORT-SUM-META-AUX2 term)))
                                A)))
     :hints (("Goal"
              :induct (SORT-SUM-META-AUX2 term)
              :do-not-induct t
              :expand ((RP-TRANS-LST (CDR TERM))
                       (RP-TRANS-LST (CDdR TERM))
                       (RP-TRANS-LST (CDddR TERM)))
              :in-theory (e/d (SORT-SUM-META-AUX2)
                              (bitp
                               valid-sc
                               rp-trans))))))

  (local
   (defthm valid-sort-sum-meta-aux-aux-is-integerp
     (implies (and (mult-formula-checks state)
                   (valid-sc term a)
                   (rp-evl-meta-extract-global-facts)
                   (MV-NTH 0 (SORT-SUM-META-AUX-aux term)))
              (and (integerp (rp-evlt term a))
                   (integerp (rp-evlt (ex-from-rp term) a))))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (SORT-SUM-META-AUX-aux
                               rp-evlt-of-ex-from-rp
                               valid-sc-single-step)
                              (valid-sc
                               EX-FROM-RP-LEMMA1
                               ))))))

  (local
   (defthm valid-sort-sum-meta-aux-is-integerp
     (implies (and (mult-formula-checks state)
                   (valid-sc term a)
                   (rp-evl-meta-extract-global-facts)
                   (MV-NTH 0 (SORT-SUM-META-AUX term)))
              (integerp (rp-evlt term a)))
     :hints (("Goal"
              :do-not-induct t
              :induct (SORT-SUM-META-AUX term)
              :in-theory (e/d* (SORT-SUM-META-AUX
                                regular-eval-lemmas
                                ;;rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
                                valid-sc-single-step)
                               (is-rp
                                rp-trans
                                rp-trans-lst
                                RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                                rp-evlt-of-ex-from-rp)))
             ("Subgoal *1/1"
              :use ((:instance rp-evlt-of-ex-from-rp)))
             ("Subgoal *1/2"
              :use ((:instance rp-evlt-of-ex-from-rp))))))

  (defthm consp-ex-from-rp-implies
    (implies (consp (ex-from-rp x))
             (consp x))
    :rule-classes :forward-chaining)

  (defthm rp-evlt-of-rp-2
    (implies (case-match term (('rp & &) t))
             (equal (rp-evlt term a)
                    (rp-evlt (caddr term) a))))

  (local
   (std::defretd
     not-consp-SORT-SUM-META-AUX-AUX-means
     (implies (and valid)
              (and #|(implies (and (not (consp e))
               (rp-termp cur))
               (equal (rp-evlt cur a) 0))|#
               (implies (not (quotep (ex-from-rp cur)))
                        (consp cur))
               (implies (not (consp cur))
                        (quotep (ex-from-rp cur)))
               ;;(not (pp-e->sign e))
               ))
     :fn SORT-SUM-META-AUX-AUX
     :hints (("Goal"
              :in-theory (e/d (PP-E
                               RP-TERM-LIST-FIX
                               ;;PP-E->SIGN
                               std::PROD-CONS
                               SORT-SUM-META-AUX-AUX)
                              (rp-termp ex-from-rp is-rp
                                        rp-trans-lst
                                        rp-trans
                                        (:TYPE-PRESCRIPTION O<)
                                        EX-FROM-RP
                                        (:REWRITE NOT-INCLUDE-RP)
                                        (:DEFINITION INCLUDE-FNC-fn)
                                        (:REWRITE DEFAULT-CDR)
                                        (:REWRITE DEFAULT-CAR)
                                        (:DEFINITION QUOTEP)
                                        (:TYPE-PRESCRIPTION INCLUDE-FNC-fn)
                                        (:TYPE-PRESCRIPTION O-P)
                                        (:TYPE-PRESCRIPTION IS-RP$INLINE)
                                        ;;                              (:REWRITE ACL2::O-P-O-INFP-CAR)
                                        ;;                              (:FORWARD-CHAINING
                                        ;;                               ACL2::|a <= b & b <= c  =>  a <= c|)
                                        ;;                              (:FORWARD-CHAINING
                                        ;;                               ACL2::|a <= b & b < c  =>  a < c|)
                                        ;;                              (:FORWARD-CHAINING
                                        ;;                               ACL2::|a <= b & ~(a = b)  =>  a < b|)
                                        (:REWRITE
                                         REGULAR-RP-EVL-OF_IFIX_WHEN_MULT-FORMULA-CHECKS)
                                        (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS-fn)
                                        ))))))

  (local
   (defthmd and-list-to-binary-and-2
     (equal (and-list 0 (cons a b))
            (binary-and a (and-list 0 b)))
     :hints (("Goal"
              :in-theory (e/d (and-list) ())))))

  (local
   (defthm SORT-SUM-META-AUX-AUX-correct-lemma
     (implies (equal (len lst) 2)
              (equal (AND-LIST 0
                               (RP-EVLT-LST (SORT-AND$-LIST lst 2)
                                            A))
                     (and-list 0 (rp-evlt-lst lst a))))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (SORT-AND$-LIST

                               and$
                               and-list-to-binary-and-2
                               and-list-to-binary-and)
                              ())))))

  (local
   (defthm not-consp-term-implis-not-consp-ex-from-rp
     (implies (not (consp x))
              (not (consp (ex-from-rp x))))
     :rule-classes :forward-chaining))

  (local
   (defret sort-sum-meta-aux-aux-correct
     (implies (and (mult-formula-checks state)
                   (valid-sc cur a)
                   (rp-evl-meta-extract-global-facts)
                   (consp (pp-e->elements e))
                   (rp-termp cur)
                   valid)
              (equal
               (rp-evlt
                (pp-e-list-to-term-and$ (pp-e->elements e))
                a)
               (rp-evlt cur a)))
     :fn sort-sum-meta-aux-aux
     :hints (("goal"
              :do-not-induct t
              :in-theory (e/d* (
                                sort-sum-meta-aux-aux
                                pp-e-list-to-term-and$
                                regular-eval-lemmas
                                ;;sort-and$-list
                                and-list-to-binary-and
                                rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
                                rp-evlt-lst-of-cons)
                               (;;rp-trans-opener
                                IS-RP-OF-QUOTED
                                IS-RP-OF-RP
                                ex-from-rp rp-termp
                                (:type-prescription valid-sc)
                                (:type-prescription mult-formula-checks)
                                (:type-prescription binary-and)
                                (:rewrite eval-of-logbit)

                                (:rewrite valid-sc-ex-from-rp-2)
                                (:definition eval-and-all)
                                (:rewrite
                                 regular-rp-evl-of_bitp_when_mult-formula-checks)
                                eval-of-list-to-term-of-sort-and$-list
                                rp-evlt-of-ex-from-rp
                                valid-sc
                                (:rewrite default-cdr)
                                (:type-prescription o<)
                                (:rewrite default-car)
                                ;;                                (:rewrite acl2::o-p-o-infp-car)
                                include-fnc-subterms
                                include-fnc
                                (:rewrite ex-from-synp-lemma1)
                                ex-from-rp-lemma1
                                bitp
                                RP-EVLT-OF-RP-2
                                rp-trans
                                rp-trans-lst))))))

  #|(local
  (defthm consp-of-pp-e-lemma
  (implies (and (rp-term-listp lst)
  (consp lst))
  (CONSP (PP-E NIL lst)))
  :hints (("Goal"
  :in-theory (e/d (STD::PROD-CONS
  RP-TERM-LIST-FIX
  pp-e)
  ())))))|#

  #|(defthm PP-E-LIST-TO-TERM-P+-SORT-SUM-META-AUX
  (implies (and (mult-formula-checks state)
  (valid-sc term a)
  (rp-termp term)
  (rp-evl-meta-extract-global-facts)
  (MV-NTH 0 (sort-sum-meta-aux term)))
  (EQUAL
  (rp-evlt (pp-e-list-to-term-p+ (mv-nth 1 (sort-sum-meta-aux term))) a)
  (rp-evlt term A)))
  :hints (("Goal"
  ;;:induct (SORT-SUM-META-AUX term)
  ;;:expand ((SORT-SUM-META-AUX-AUX TERM))
  ;;:do-not-induct t
  ;; :Expand ((true-listp (cdr term))
  ;;          (RP-TRANS-LST (CDR TERM))
  ;;          (RP-TRANS-LST (CDdR TERM)))
  :in-theory (e/d* (SORT-SUM-META-AUX
  regular-eval-lemmas
  rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
  not-consp-SORT-SUM-META-AUX-AUX-means
  is-if is-equals is-rp context-from-rp eval-and-all
  true-listp
  ifix-opener
  PP-E-LIST-TO-TERM-P+)
  (rp-termp
  PP-E-LIST-TO-TERM-AND$-REDEF
  rp-evlt-of-ex-from-rp
  rp-trans
  rp-trans-lst
  (:DEFINITION EX-FROM-RP)
;(:REWRITE VALID-SC-CADR) ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
;(:REWRITE VALID-SC-CADDR) ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  (:DEFINITION EVAL-AND-ALL)
  (:REWRITE DEFAULT-CDR)
  (:REWRITE DEFAULT-CAR)
  ;;                               (:REWRITE ACL2::O-P-O-INFP-CAR)
  (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
  (:DEFINITION RP-TRANS)
  (:REWRITE ATOM-RP-TERMP-IS-SYMBOLP)
  (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
  (:REWRITE EVAL-OF-LOGBIT)
  (:REWRITE EVAL-OF-BINARY-XOR)
  (:REWRITE EVAL-OF-BINARY-OR)
  (:DEFINITION INCLUDE-FNC-fn)
  (:DEFINITION RP-TERMP)
;VALID-SC-EX-FROM-RP-2 ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  rp-evl-of-ex-from-rp-reverse
  bitp
  TYPE-FIX-WHEN-BITP
  TYPE-FIX-WHEN-INTEGERP
  PP-E-LIST-TO-TERM-P+-TO-PP-E-LIST-TO-TERM-PP-LST)))))|#

  (defthm PP-E-LIST-TO-TERM-P+-SORT-SUM-META-AUX2
    (implies (and (mult-formula-checks state)
                  (valid-sc term a)
                  (rp-termp term)
                  (rp-evl-meta-extract-global-facts)
                  (MV-NTH 0 (SORT-SUM-META-AUX2 term)))
             (EQUAL
              (rp-evlt (pp-e-list-to-term-p+ (mv-nth 1 (sort-sum-meta-aux2 term))) a)
              (rp-evlt term A)))
    :hints (("Goal"
             :induct (MV-NTH 1 (SORT-SUM-META-AUX2 term))
             :do-not-induct t
             :Expand ((true-listp (cdr term))
                      (RP-TRANS-LST (CDR TERM))
                      (RP-TRANS-LST (CDdR TERM)))
             :in-theory (e/d* (SORT-SUM-META-AUX2
                               regular-eval-lemmas
                               rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
                               not-consp-SORT-SUM-META-AUX-AUX-means
                               is-if is-equals is-rp context-from-rp eval-and-all
                               true-listp
                               ifix-opener
                               PP-E-LIST-TO-TERM-P+)
                              (PP-E-LIST-TO-TERM-AND$-REDEF
                               rp-evlt-of-ex-from-rp
                               rp-trans
                               rp-trans-lst
                               (:DEFINITION EX-FROM-RP)
;(:REWRITE VALID-SC-CADR)
;(:REWRITE VALID-SC-CADDR)
                               (:DEFINITION EVAL-AND-ALL)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE DEFAULT-CAR)
                               ;;                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                               (:DEFINITION RP-TRANS)
                               (:REWRITE ATOM-RP-TERMP-IS-SYMBOLP)
                               (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                               (:REWRITE EVAL-OF-LOGBIT)
                               (:REWRITE EVAL-OF-BINARY-XOR)
                               (:REWRITE EVAL-OF-BINARY-OR)
                               (:DEFINITION INCLUDE-FNC-fn)
                               (:DEFINITION RP-TERMP)
;VALID-SC-EX-FROM-RP-2
                               rp-evl-of-ex-from-rp-reverse
                               bitp
                               TYPE-FIX-WHEN-BITP
                               TYPE-FIX-WHEN-INTEGERP
                               PP-E-LIST-TO-TERM-P+-TO-PP-E-LIST-TO-TERM-PP-LST)))))

  (local
   (defthm when-pp-lst-is-nil-evals-to-zero
     (implies (and (not pp-lst)
                   (equal (sum-list (rp-evlt-lst pp-lst a))
                          (rp-evlt term a)))
              (equal (equal 0 (rp-evlt term a))
                     t))))

  ;; A MAIN LEMMA
  (defthm sort-sum-meta-correct
    (implies (and (mult-formula-checks state)
                  (rp-evl-meta-extract-global-facts)
                  (rp-termp term)
                  (valid-sc term a))
             (equal (rp-evlt (mv-nth 0 (sort-sum-meta term)) a)
                    (rp-evlt term a)))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance PP-SUM-SORT-LST-CORRECT-ALT
                              (pp-lst
                               (PP-E-LIST-TO-TERM-PP-LST
                                (SORT-PP-E-LISTS (MV-NTH 1 (SORT-SUM-META-AUX2 (CADR TERM)))
                                                 (LEN (MV-NTH 1
                                                              (SORT-SUM-META-AUX2 (CADR TERM))))))))
                   (:instance pp-e-list-to-term-p+-to-pp-e-list-to-term-pp-lst
                              (lst (SORT-PP-E-LISTS (MV-NTH 1 (SORT-SUM-META-AUX2 (CADR TERM)))
                                                    (LEN (MV-NTH 1
                                                                 (SORT-SUM-META-AUX2 (CADR TERM)))))))
                   (:instance EVAL-OF-SORT-PP-E-LISTS-IS-CORRECT
                              (lst (MV-NTH 1 (SORT-SUM-META-AUX2 (CADR TERM))))
                              (size (LEN (MV-NTH 1 (SORT-SUM-META-AUX2 (CADR TERM)))))))
             :in-theory (e/d (sort-sum-meta
                              SORT-SUM
                              )
                             (PP-SUM-SORT-LST-CORRECT-ALT
                              to-list*-sum-eval
                              pp-e-list-to-term-p+-to-pp-e-list-to-term-pp-lst
                              PP-E-LIST-TO-TERM-AND$-REDEF
                              pp-sum-sort-lst-correct
                              EVAL-OF-SORT-PP-E-LISTS-IS-CORRECT)))))

  #|(defthm sort-sum-meta-valid-rp-meta-rulep-local
  (implies (and (rp-evl-meta-extract-global-facts :state state)
  (mult-formula-checks state))
  (let ((rule (make rp-meta-rule-rec
  :fnc 'sort-sum-meta
  :trig-fnc 'sort-sum
  :dont-rw t
  :valid-syntax t)))
  (and (valid-rp-meta-rulep rule state)
  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
  :in-theory (e/d (rp-meta-valid-syntaxp)
  (rp-termp
  rp-term-listp
  valid-sc)))))||#)
