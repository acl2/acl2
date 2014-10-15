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
(include-book "prop")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(dd.open "conjunctions.tex")

(dd.subsection "Conjunction rules")

(dd.write "These builders act as $\\wedge$ introduction and elimination rules.
We typically avoid using conjunctions and instead build both proofs separately
to avoid the conversion overhead.")

(defderiv build.conjoin
 :derive (! (v (! A) (! B)))
 :from   ((proof x A)
          (proof y B))
 :proof  (@derive ((v (! (v (! A) (! B))) (v (! A) (! B)))   (build.propositional-schema (@formula (v (! A) (! B)))))
                  ((v (v (! (v (! A) (! B))) (! A)) (! B))   (build.associativity @-))
                  ((v (! B) (v (! (v (! A) (! B))) (! A)))   (build.commute-or @-))
                  (B                                         (@given y))
                  ((v (! (v (! A) (! B))) (! A))             (build.modus-ponens @- @--))
                  ((v (! A) (! (v (! A) (! B))))             (build.commute-or @-))
                  (A                                         (@given x))
                  ((! (v (! A) (! B)))                       (build.modus-ponens @- @--))))

(defderiv build.first-conjunct
 :derive A
 :from   ((proof x (! (v (! A) (! B)))))
 :proof  (@derive ((v (! A) A)             (build.propositional-schema (@formula A)))
                  ((v A (! A))             (build.commute-or @-))
                  ((v (! B) (v A (! A)))   (build.expansion (@formula (! B)) @-))
                  ((v (v (! B) A) (! A))   (build.associativity @-))
                  ((v (! A) (v (! B) A))   (build.commute-or @-))
                  ((v (v (! A) (! B)) A)   (build.associativity @-))
                  ((! (v (! A) (! B)))     (@given x))
                  (A                       (build.modus-ponens-2 @- @--))))

(defderiv build.second-conjunct
 :derive B
 :from   ((proof x (! (v (! A) (! B)))))
 :proof  (@derive ((v (! B) B)             (build.propositional-schema (@formula B)))
                  ((v (! A) (v (! B) B))   (build.expansion (@formula (! A)) @-))
                  ((v (v (! A) (! B)) B)   (build.associativity @-))
                  ((! (v (! A) (! B)))     (@given x))
                  (B                       (build.modus-ponens-2 @- @--))))

(defderiv build.disjoined-conjoin
 :derive (v P (! (v (! A) (! B))))
 :from   ((proof x (v P A))
          (proof y (v P B)))
 :proof  (@derive ((v (! (v (! A) (! B))) (v (! A) (! B)))   (build.propositional-schema (@formula (v (! A) (! B)))))
                  ((v (v (! (v (! A) (! B))) (! A)) (! B))   (build.associativity @-))
                  ((v (! B) (v (! (v (! A) (! B))) (! A)))   (build.commute-or @-)  *1)
                  ((v P B)                                   (@given y))
                  ((v B P)                                   (build.commute-or @-))
                  ((v P (v (! (v (! A) (! B))) (! A)))       (build.cut @- *1))
                  ((v P (v (! A) (! (v (! A) (! B)))))       (build.disjoined-commute-or @-))
                  ((v P A)                                   (@given x))
                  ((v P (! (v (! A) (! B))))                 (build.disjoined-modus-ponens @- @--))))

(defderiv build.disjoined-first-conjunct
 :derive (v P A)
 :from   ((proof x (v P (! (v (! A) (! B))))))
 :proof  (@derive ((v (! A) A)                 (build.propositional-schema (@formula A)))
                  ((v A (! A))                 (build.commute-or @-))
                  ((v (! B) (v A (! A)))       (build.expansion (@formula (! B)) @-))
                  ((v (v (! B) A) (! A))       (build.associativity @-))
                  ((v (! A) (v (! B) A))       (build.commute-or @-))
                  ((v (v (! A) (! B)) A)       (build.associativity @-)                   *1)
                  ((v P (! (v (! A) (! B))))   (@given x))
                  ((v (! (v (! A) (! B))) P)   (build.commute-or @-))
                  ((v A P)                     (build.cut *1 @-))
                  ((v P A)                     (build.commute-or @-))))

(defderiv build.disjoined-second-conjunct
 :derive (v P B)
 :from   ((proof x (v P (! (v (! A) (! B))))))
 :proof  (@derive ((v (! B) B)                 (build.propositional-schema (@formula B)))
                  ((v (! A) (v (! B) B))       (build.expansion (@formula (! A)) @-))
                  ((v (v (! A) (! B)) B)       (build.associativity @-)                    *1)
                  ((v P (! (v (! A) (! B))))   (@given x))
                  ((v (! (v (! A) (! B))) P)   (build.commute-or @-))
                  ((v B P)                     (build.cut *1 @-))
                  ((v P B)                     (build.commute-or @-))))

(dd.close)