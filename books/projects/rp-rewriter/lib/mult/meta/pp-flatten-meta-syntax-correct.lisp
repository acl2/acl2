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

(include-book "pp-flatten-meta")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rp-Termp

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
 (defthm rp-termp-pp-lists-to-term-and$
   (implies (rp-term-listp lst)
            (rp-termp (pp-lists-to-term-and$ lst)))
   :hints (("Goal"
            :in-theory (e/d (pp-lists-to-term-and$) ())))))

(local
 (defthm rp-termp-pp-lists-to-term-p+
   (implies (rp-term-list-listp (strip-cdrs lst))
            (rp-termp (pp-lists-to-term-p+ lst)))
   :hints (("Goal"
            :in-theory (e/d (pp-lists-to-term-p+) ())))))

(defthm flatten-pp-main-returns-pseudo-term2
  (implies (rp-termp term)
           (rp-termp (flatten-pp-main term)))
  :hints (("Goal"
           :in-theory (e/d (flatten-pp-main) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rp-syntaxp
#|
(local
 (defun rp-syntaxp-lst-lst (lst)
   (if (atom lst)
       (eq lst nil)
     (and (rp-syntaxp-lst (car lst))
          (rp-syntaxp-lst-lst (cdr lst))))))

(local
 (defthm rp-syntaxp-lst-cut-list-by-half
   (implies (and (rp-syntaxp-lst lst)
                 (<= size (len lst)))
            (and (rp-syntaxp-lst (mv-nth 0 (cut-list-by-half lst size)))
                 (rp-syntaxp-lst (mv-nth 1 (cut-list-by-half lst size)))))
   :hints (("Goal"
            ;;          :do-not-induct t
            ;;            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half
                             dummy-arith-lemma-2) ())))))

(local
 (defthm rp-syntaxp-lst-lst-cut-list-by-half
   (implies (and (rp-syntaxp-lst-lst lst)
                 (<= size (len lst)))
            (and (rp-syntaxp-lst-lst (mv-nth 0 (cut-list-by-half lst size)))
                 (rp-syntaxp-lst-lst (mv-nth 1 (cut-list-by-half lst size)))))
   :hints (("Goal"
            :do-not-induct t
            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half) ())))))

(local
 (defthm rp-syntaxp-lst-lst-cut-list-by-half-2
   (implies (and (rp-syntaxp-lst-lst (strip-cdrs lst))
                 (<= size (len lst)))
            (and (rp-syntaxp-lst-lst (strip-cdrs (mv-nth 0 (cut-list-by-half lst size))))
                 (rp-syntaxp-lst-lst (strip-cdrs (mv-nth 1 (cut-list-by-half lst size))))))
   :hints (("Goal"
            :do-not-induct t
            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half
                             dummy-arith-lemma-1) ())))))

(local
 (defthm rp-syntaxp-lst-merge-sorted-and$-lists
   (implies (and (rp-syntaxp-lst lst1)
                 (rp-syntaxp-lst lst2))
            (rp-syntaxp-lst (merge-sorted-and$-lists lst1 lst2)))
   :hints (("Goal"
            :induct (merge-sorted-and$-lists lst1 lst2)
            :in-theory (e/d (merge-sorted-and$-lists) ())))))

(local
 (defthm rp-syntaxp-lst-sort-and$-list
   (implies (rp-syntaxp-lst lst)
            (rp-syntaxp-lst (sort-and$-list lst len)))
   :hints (("Goal"
            :in-theory (e/d (sort-and$-list) ())))))

(local
 (defthm rp-syntaxp-lst-lst-merge-sorted-pp-lists
   (implies (and (rp-syntaxp-lst-lst (strip-cdrs lst1))
                 (rp-syntaxp-lst-lst (strip-cdrs lst2)))
            (rp-syntaxp-lst-lst
             (strip-cdrs
              (merge-sorted-pp-lists lst1 lst2))))
   :hints (("Goal"
            :induct (merge-sorted-pp-lists lst1 lst2)
            :in-theory (e/d (merge-sorted-pp-lists) ())))))

(local
 (defthm rp-syntaxp-lst-lst-sort-pp-lists
   (implies (rp-syntaxp-lst-lst (strip-cdrs lst1))
            (rp-syntaxp-lst-lst (strip-cdrs
                                 (sort-pp-lists lst1 len))))
   :hints (("Goal"
            ;;:induct (sort-pp-lists lst1 len)
            ;;:do-not-induct t
            :in-theory (e/d (sort-pp-lists) ())))))

(local
 (defthm rp-syntaxp-lst-lst-and$-pp-lists-aux
   (implies (and (rp-syntaxp-lst cur)
                 (rp-syntaxp-lst-lst (strip-cdrs lst2))
                 (rp-syntaxp-lst-lst (strip-cdrs acc)))
            (rp-syntaxp-lst-lst (strip-cdrs (and$-pp-lists-aux cur lst2 acc
                                                               sign))))
   :hints (("Goal"
            :in-theory (e/d (and$-pp-lists-aux) ())))))

(local
 (defthm rp-syntaxp-lst-lst-and$-pp-lists
   (implies (and (rp-syntaxp-lst-lst (strip-cdrs lst1))
                 (rp-syntaxp-lst-lst (strip-cdrs lst2))
                 (rp-syntaxp-lst-lst (strip-cdrs acc)))
            (rp-syntaxp-lst-lst (strip-cdrs (and$-pp-lists lst1 lst2 acc
                                                           sign))))
   :hints (("Goal"
            :in-theory (e/d (and$-pp-lists) ())))))

(Local
 (defthm rp-syntaxp-lst-lst-pp-term-to-pp-lists
   (implies (rp-syntaxp term)
            (rp-syntaxp-lst-lst (strip-cdrs (pp-term-to-pp-lists term sign))))
   :hints (("Goal"
            :in-theory (e/d (pp-term-to-pp-lists) ())))))

(local
 (defthm rp-syntaxp-pp-lists-to-term-and$
   (implies (rp-syntaxp-lst lst)
            (rp-syntaxp (pp-lists-to-term-and$ lst)))
   :hints (("Goal"
            :in-theory (e/d (pp-lists-to-term-and$) ())))))

(local
 (defthm rp-syntaxp-pp-lists-to-term-p+
   (implies (rp-syntaxp-lst-lst (strip-cdrs lst))
            (rp-syntaxp (pp-lists-to-term-p+ lst)))
   :hints (("Goal"
            :in-theory (e/d (pp-lists-to-term-p+) ())))))

(defthm flatten-pp-main-returns-rp-syntaxp
  (implies (rp-syntaxp term)
           (rp-syntaxp (flatten-pp-main term)))
  :hints (("Goal"
           :in-theory (e/d (flatten-pp-main) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; all-falist-consistent

(local
 (defun all-falist-consistent-lst-lst (lst)
   (if (atom lst)
       (eq lst nil)
     (and (all-falist-consistent-lst (car lst))
          (all-falist-consistent-lst-lst (cdr lst))))))

(local
 (defthm all-falist-consistent-lst-cut-list-by-half
   (implies (and (all-falist-consistent-lst lst)
                 (<= size (len lst)))
            (and (all-falist-consistent-lst (mv-nth 0 (cut-list-by-half lst size)))
                 (all-falist-consistent-lst (mv-nth 1 (cut-list-by-half lst size)))))
   :hints (("Goal"
            ;;          :do-not-induct t
            ;;            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half
                             dummy-arith-lemma-2) ())))))

(local
 (defthm all-falist-consistent-lst-lst-cut-list-by-half
   (implies (and (all-falist-consistent-lst-lst lst)
                 (<= size (len lst)))
            (and (all-falist-consistent-lst-lst (mv-nth 0 (cut-list-by-half lst size)))
                 (all-falist-consistent-lst-lst (mv-nth 1 (cut-list-by-half lst size)))))
   :hints (("Goal"
            :do-not-induct t
            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half) ())))))

(local
 (defthm all-falist-consistent-lst-lst-cut-list-by-half-2
   (implies (and (all-falist-consistent-lst-lst (strip-cdrs lst))
                 (<= size (len lst)))
            (and (all-falist-consistent-lst-lst (strip-cdrs (mv-nth 0 (cut-list-by-half lst size))))
                 (all-falist-consistent-lst-lst (strip-cdrs (mv-nth 1 (cut-list-by-half lst size))))))
   :hints (("Goal"
            :do-not-induct t
            :induct (cut-list-by-half lst size)
            :in-theory (e/d (cut-list-by-half
                             dummy-arith-lemma-1) ())))))

(local
 (defthm all-falist-consistent-lst-merge-sorted-and$-lists
   (implies (and (all-falist-consistent-lst lst1)
                 (all-falist-consistent-lst lst2))
            (all-falist-consistent-lst (merge-sorted-and$-lists lst1 lst2)))
   :hints (("Goal"
            :induct (merge-sorted-and$-lists lst1 lst2)
            :in-theory (e/d (merge-sorted-and$-lists) ())))))

(local
 (defthm all-falist-consistent-lst-sort-and$-list
   (implies (all-falist-consistent-lst lst)
            (all-falist-consistent-lst (sort-and$-list lst len)))
   :hints (("Goal"
            :in-theory (e/d (sort-and$-list) ())))))

(local
 (defthm all-falist-consistent-lst-lst-merge-sorted-pp-lists
   (implies (and (all-falist-consistent-lst-lst (strip-cdrs lst1))
                 (all-falist-consistent-lst-lst (strip-cdrs lst2)))
            (all-falist-consistent-lst-lst
             (strip-cdrs
              (merge-sorted-pp-lists lst1 lst2))))
   :hints (("Goal"
            :induct (merge-sorted-pp-lists lst1 lst2)
            :in-theory (e/d (merge-sorted-pp-lists) ())))))

(local
 (defthm all-falist-consistent-lst-lst-sort-pp-lists
   (implies (all-falist-consistent-lst-lst (strip-cdrs lst1))
            (all-falist-consistent-lst-lst (strip-cdrs
                                            (sort-pp-lists lst1 len))))
   :hints (("Goal"
            ;;:induct (sort-pp-lists lst1 len)
            ;;:do-not-induct t
            :in-theory (e/d (sort-pp-lists) ())))))

(local
 (defthm all-falist-consistent-lst-lst-and$-pp-lists-aux
   (implies (and (all-falist-consistent-lst cur)
                 (all-falist-consistent-lst-lst (strip-cdrs lst2))
                 (all-falist-consistent-lst-lst (strip-cdrs acc)))
            (all-falist-consistent-lst-lst (strip-cdrs (and$-pp-lists-aux cur lst2 acc
                                                                          sign))))
   :hints (("Goal"
            :in-theory (e/d (and$-pp-lists-aux) ())))))

(local
 (defthm all-falist-consistent-lst-lst-and$-pp-lists
   (implies (and (all-falist-consistent-lst-lst (strip-cdrs lst1))
                 (all-falist-consistent-lst-lst (strip-cdrs lst2))
                 (all-falist-consistent-lst-lst (strip-cdrs acc)))
            (all-falist-consistent-lst-lst (strip-cdrs (and$-pp-lists lst1 lst2 acc
                                                                      sign))))
   :hints (("Goal"
            :in-theory (e/d (and$-pp-lists) ())))))

(Local
 (defthm all-falist-consistent-lst-lst-pp-term-to-pp-lists
   (implies (all-falist-consistent term)
            (all-falist-consistent-lst-lst (strip-cdrs (pp-term-to-pp-lists term sign))))
   :hints (("Goal"
            :in-theory (e/d (pp-term-to-pp-lists) ())))))

(local
 (defthm all-falist-consistent-pp-lists-to-term-and$
   (implies (all-falist-consistent-lst lst)
            (all-falist-consistent (pp-lists-to-term-and$ lst)))
   :hints (("Goal"
            :in-theory (e/d (pp-lists-to-term-and$) ())))))

(local
 (defthm all-falist-consistent-pp-lists-to-term-p+
   (implies (all-falist-consistent-lst-lst (strip-cdrs lst))
            (all-falist-consistent (pp-lists-to-term-p+ lst)))
   :hints (("Goal"
            :in-theory (e/d (pp-lists-to-term-p+) ())))))

(defthm flatten-pp-main-returns-all-falist-consistent
  (implies (all-falist-consistent term)
           (all-falist-consistent (flatten-pp-main term)))
  :hints (("Goal"
           :in-theory (e/d (flatten-pp-main) ()))))||#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; valid-sc


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
 (defthm valid-sc-pp-lists-to-term-and$
   (implies (valid-sc-subterms lst a)
            (valid-sc (pp-lists-to-term-and$ lst)
                      a))
   :hints (("Goal"
            :in-theory (e/d (pp-lists-to-term-and$
                             is-rp) ())))))

(local
 (defthm valid-sc-pp-lists-to-term-p+
   (implies (valid-sc-subterms-lst (strip-cdrs lst) a)
            (valid-sc (pp-lists-to-term-p+ lst) a))
   :hints (("Goal"
            :in-theory (e/d (pp-lists-to-term-p+
                             is-if
                             is-rp) ())))))

(defthm flatten-pp-main-returns-valid-sc
  (implies (valid-sc term a)
           (valid-sc (flatten-pp-main term) a))
  :hints (("Goal"
           :in-theory (e/d (flatten-pp-main
                            is-if is-rp) ()))))



;; (flatten-pp-main `(binary-? (rp 'bitp y) (binary-and (rp 'bitp b) (binary-or (rp 'bitp x) (rp 'bitp y))) (rp 'bitp x)))
