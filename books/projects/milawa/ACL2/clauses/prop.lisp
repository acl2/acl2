; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "../build/prop")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defderiv build.lhs-commute-or-then-rassoc
  :derive (v B (v A C))
  :from   ((proof x (v (v A B) C)))
  :proof  (@derive
           ((v (v A B) C)   (@given x))
           ((v C (v A B))   (build.commute-or @-))
           ((v (v C A) B)   (build.associativity @-))
           ((v B (v C A))   (build.commute-or @-))
           ((v B (v A C))   (build.disjoined-commute-or @-))))

(defderiv clause.aux-limsplit-cutoff-step-bldr
  ;; BOZO i guess this is the same as above.
  :derive (v P (v A Q))
  :from ((proof x (v (v A P) Q)))
  :proof
  (@derive
   ((v (v A P) Q)     (@given x))
   ((v Q (v A P))     (build.commute-or @-))
   ((v (v Q A) P)     (build.associativity @-))
   ((v P (v Q A))     (build.commute-or @-))
   ((v P (v A Q))     (build.disjoined-commute-or @-))))

(defderiv clause.aux-split-default-3-bldr
  :derive (v (v A P) Q)
  :from   ((proof x (v P (v A Q))))
  :proof  (@derive
           ((v P (v A Q))   (@given x))
           ((v P (v Q A))   (build.disjoined-commute-or @-))
           ((v (v P Q) A)   (build.associativity @-))
           ((v A (v P Q))   (build.commute-or @-))
           ((v (v A P) Q)   (build.associativity @-))))

(defderiv clause.aux-split-twiddle-lemma-1
  :derive (v (v (v B C) (v A (v B C))) A)
  :from   ((proof x (v (v A C) (v B C))))
  :proof  (@derive
           ((v (v A C) (v B C))               (@given x))
           ((v (v B C) (v A C))               (build.commute-or @-))
           ((v A (v (v B C) (v A C)))         (build.expansion (@formula A) @-))
           ((v (v A (v B C)) (v A C))         (build.associativity @-))
           ((v (v (v A (v B C)) A) C)         (build.associativity @-))
           ((v C (v (v A (v B C)) A))         (build.commute-or @-))
           ((v B (v C (v (v A (v B C)) A)))   (build.expansion (@formula B) @-))
           ((v (v B C) (v (v A (v B C)) A))   (build.associativity @-))
           ((v (v (v B C) (v A (v B C))) A)   (build.associativity @-))))

(defderiv clause.aux-split-twiddle
  :derive (v A (v B C))
  :from   ((proof x (v (v A C) (v B C))))
  :proof  (@derive
           ((v (v A C) (v B C))               (@given x))
           ((v (v (v B C) (v A (v B C))) A)   (clause.aux-split-twiddle-lemma-1 @-))
           ((v A (v (v B C) (v A (v B C))))   (build.commute-or @-))
           ((v (v A (v B C)) (v A (v B C)))   (build.associativity @-))
           ((v A (v B C))                     (build.contraction @-))))

(defderiv clause.aux-split-twiddle2-lemma-1a
  :derive (v A (v B (v C (v P Q))))
  :from   ((proof x (v Q (v A C)))
           (formula p P)
           (formula b B))
  :proof  (@derive
           ((v Q (v A C))              (@given x))
           ((v P (v Q (v A C)))        (build.expansion (@formula P) @-))
           ((v (v P Q) (v A C))        (build.associativity @-))
           ((v (v A C) (v P Q))        (build.commute-or @-))
           ((v A (v C (v P Q)))        (build.right-associativity @-))
           ((v A (v B (v C (v P Q))))  (build.disjoined-left-expansion @- (@formula B)))))

(defderiv clause.aux-split-twiddle2-lemma-1
  :derive (v (v (v P Q) (v A B)) C)
  :from   ((proof x (v Q (v A C)))
           (formula p P)
           (formula b B))
  :proof (@derive
          ((v Q (v A C))              (@given x))
          ((v A (v B (v C (v P Q))))  (clause.aux-split-twiddle2-lemma-1a @- (@formula P) (@formula B)))
          ((v (v A B) (v C (v P Q)))  (build.associativity @-))
          ((v (v (v A B) C) (v P Q))  (build.associativity @-))
          ((v (v P Q) (v (v A B) C))  (build.commute-or @-))
          ((v (v (v P Q) (v A B)) C)  (build.associativity @-))))

(defderiv clause.aux-split-twiddle2-lemma-2a
  :derive (v A (v B (v (v P Q) C)))
  :from   ((proof x (v C (v B P)))
           (formula a A)
           (formula q Q))
  :proof  (@derive
           ((v C (v B P))               (@given x))
           ((v (v C B) P)               (build.associativity @-))
           ((v Q (v (v C B) P))         (build.expansion (@formula Q) @-))
           ((v (v Q (v C B)) P)         (build.associativity @-))
           ((v P (v Q (v C B)))         (build.commute-or @-))
           ((v (v P Q) (v C B))         (build.associativity @-))
           ((v (v (v P Q) C) B)         (build.associativity @-))
           ((v B (v (v P Q) C))         (build.commute-or @-))
           ((v A (v B (v (v P Q) C)))   (build.expansion (@formula A) @-))))

(defderiv clause.aux-split-twiddle2-lemma-2
  :derive (v C (v (v P Q) (v A B)))
  :from   ((proof x (v C (v B P)))
           (formula a A)
           (formula q Q))
  :proof  (@derive
           ((v C (v B P))               (@given x))
           ((v A (v B (v (v P Q) C)))   (clause.aux-split-twiddle2-lemma-2a @- (@formula A) (@formula Q)))
           ((v (v A B) (v (v P Q) C))   (build.associativity @-))
           ((v (v (v A B) (v P Q)) C)   (build.associativity @-))
           ((v C (v (v A B) (v P Q)))   (build.commute-or @-))
           ((v C (v (v P Q) (v A B)))   (build.disjoined-commute-or @-))))

(defderiv clause.aux-split-twiddle2
  :derive (v (v P Q) (v A B))
  :from   ((proof x (v (v A (v B P)) Q)))
  :proof  (@derive
           ((v (v A (v B P)) Q)                          (@given x))
           ((v Q (v A (v B P)))                          (build.commute-or @-))
           ((v (v (v P Q) (v A B)) (v B P))              (clause.aux-split-twiddle2-lemma-1 @- (@formula P) (@formula B)))
           ((v (v (v P Q) (v A B)) (v (v P Q) (v A B)))  (clause.aux-split-twiddle2-lemma-2 @- (@formula A) (@formula Q)))
           ((v (v P Q) (v A B))                          (build.contraction @-))))

