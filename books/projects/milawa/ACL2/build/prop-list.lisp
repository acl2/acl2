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


;; List-based rules.

(defund@ build.modus-ponens-list (b as base)
  ;;    A1
  ;;    ...
  ;;    An
  ;;    ~A1 v ... v ~An v B
  ;;  -----------------------
  ;;    B
  (declare (xargs :guard (and (logic.formulap b)
                              (logic.appeal-listp as)
                              (logic.appealp base)
                              (equal (logic.conclusion base)
                                     (logic.disjoin-formulas (app (logic.negate-formulas (logic.strip-conclusions as))
                                                                  (list b)))))))
  (cond ((consp as)
         (@derive ((v (! A_1) (v dots (v (! A_n) B)))  (@given base))
                  (A_1                                 (@given (car as)))
                  ((v (! A_2) (v dots (v (! A_n) B)))  (build.modus-ponens @- @--))
                  (B                                   (build.modus-ponens-list b (cdr as) @-))))
        (t
         (@derive (B                                   (@given (logic.appeal-identity base)))))))

(encapsulate
 ()
 (local (in-theory (enable build.modus-ponens-list)))

 (defthm forcing-build.modus-ponens-list-under-iff
   (iff (build.modus-ponens-list b as base)
        t))

 (defthm forcing-logic.appealp-of-build.modus-ponens-list
   (implies (force (and (logic.formulap b)
                        (logic.appeal-listp as)
                        (logic.appealp base)
                        (equal (logic.conclusion base)
                               (logic.disjoin-formulas (app (logic.negate-formulas (logic.strip-conclusions as))
                                                            (list b))))))
            (equal (logic.appealp (build.modus-ponens-list b as base))
                   t)))

 (defthm forcing-logic.conclusion-of-build.modus-ponens-list
   (implies (force (and (logic.formulap b)
                        (logic.appeal-listp as)
                        (logic.appealp base)
                        (equal (logic.conclusion base)
                               (logic.disjoin-formulas (app (logic.negate-formulas (logic.strip-conclusions as))
                                                            (list b))))))
            (equal (logic.conclusion (build.modus-ponens-list b as base))
                   b))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm forcing-logic.proofp-of-build.modus-ponens-list
   (implies (force (and (logic.formulap b)
                        (logic.appeal-listp as)
                        (logic.appealp base)
                        (equal (logic.conclusion base)
                               (logic.disjoin-formulas (app (logic.negate-formulas (logic.strip-conclusions as))
                                                            (list b))))
                        (logic.proof-listp as axioms thms atbl)
                        (logic.proofp base axioms thms atbl)))
            (equal (logic.proofp (build.modus-ponens-list b as base) axioms thms atbl)
                   t))))




(defund@ build.modus-ponens-2-list (b as base)
  ;;    ~A1
  ;;    ...
  ;;    ~An
  ;;    A1 v ... v An v B
  ;;  ---------------------
  ;;    B
  (declare (xargs :guard (and (logic.formulap b)
                              (logic.appeal-listp as)
                              (logic.appealp base)
                              (logic.all-negationsp (logic.strip-conclusions as))
                              (equal (logic.conclusion base)
                                     (logic.disjoin-formulas (app (logic.~args (logic.strip-conclusions as))
                                                                  (list b)))))))
  (cond ((consp as)
         (@derive ((v A1 (v dots (v An B)))   (@given base))
                  ((! A1)                     (@given (car as)))
                  ((v A2 (v dots (v An B)))   (build.modus-ponens-2 @- @--))
                  (B                          (build.modus-ponens-2-list b (cdr as) @-))))
        (t
         (@derive (B                          (@given (logic.appeal-identity base)))))))

(encapsulate
 ()
 (local (in-theory (enable build.modus-ponens-2-list)))

 (defthm forcing-build.modus-ponens-2-list-under-iff
   (iff (build.modus-ponens-2-list b as base)
        t))

 (defthm forcing-logic.appealp-of-build.modus-ponens-2-list
   (implies (force (and (logic.formulap b)
                        (logic.appeal-listp as)
                        (logic.appealp base)
                        (logic.all-negationsp (logic.strip-conclusions as))
                        (equal (logic.conclusion base)
                               (logic.disjoin-formulas (app (logic.~args (logic.strip-conclusions as))
                                                            (list b))))))
            (equal (logic.appealp (build.modus-ponens-2-list b as base))
                   t)))

 (defthm forcing-logic.conclusion-of-build.modus-ponens-2-list
   (implies (force (and (logic.formulap b)
                        (logic.appeal-listp as)
                        (logic.appealp base)
                        (logic.all-negationsp (logic.strip-conclusions as))
                        (equal (logic.conclusion base)
                               (logic.disjoin-formulas (app (logic.~args (logic.strip-conclusions as))
                                                            (list b))))))
            (equal (logic.conclusion (build.modus-ponens-2-list b as base))
                   b))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm forcing-logic.proofp-of-build.modus-ponens-2-list
   (implies (force (and (logic.formulap b)
                        (logic.appeal-listp as)
                        (logic.appealp base)
                        (logic.all-negationsp (logic.strip-conclusions as))
                        (equal (logic.conclusion base)
                               (logic.disjoin-formulas (app (logic.~args (logic.strip-conclusions as))
                                                            (list b))))
                        ;; ---
                        (logic.proof-listp as axioms thms atbl)
                        (logic.proofp base axioms thms atbl)))
            (equal (logic.proofp (build.modus-ponens-2-list b as base) axioms thms atbl)
                   t))))




(defund@ build.disjoined-modus-ponens-list (b as base)
  ;; Derive P v B from P v A1, ..., P v An, and P v ~A1 v ~A2 v ... v ~An v B
  (declare (xargs :guard (and (logic.formulap b)
                              (logic.appeal-listp as)
                              (logic.appealp base)
                              (let ((aconcs   (logic.strip-conclusions as))
                                    (baseconc (logic.conclusion base)))
                                (and (logic.all-disjunctionsp aconcs)
                                     (equal (logic.fmtype baseconc) 'por*)
                                     (all-equalp (logic.vlhs baseconc) (logic.vlhses aconcs))
                                     (equal (logic.vrhs baseconc)
                                            (logic.disjoin-formulas (app (logic.negate-formulas (logic.vrhses aconcs))
                                                                         (list b)))))))))
  (cond ((consp as)
         (@derive ((v P (v A_1 (v dots (v A_n B))))    (@given base))
                  ((v P A_1)                           (@given (car as)))
                  ((v P (v A_2 (v dots (v A_n B))))    (build.disjoined-modus-ponens @- @--))
                  ((v P B)                             (build.disjoined-modus-ponens-list b (cdr as) @-))))
        (t
         (@derive ((v P B)                             (@given (logic.appeal-identity base)))))))

(encapsulate
 ()
 (local (in-theory (enable build.disjoined-modus-ponens-list)))

 (defthm forcing-build.disjoined-modus-ponens-list-under-iff
   (iff (build.disjoined-modus-ponens-list b as base)
        t))

 (defthm lemma-for-forcing-logic.appealp-of-build.disjoined-modus-ponens-list
   (implies (and (logic.formulap b)
                 (logic.appeal-listp as)
                 (logic.appealp base)
                 (logic.all-disjunctionsp (logic.strip-conclusions as))
                 (equal (logic.fmtype (logic.conclusion base)) 'por*)
                 (all-equalp (logic.vlhs (logic.conclusion base)) (logic.vlhses (logic.strip-conclusions as)))
                 (equal (logic.vrhs (logic.conclusion base))
                        (logic.disjoin-formulas (app (logic.negate-formulas (logic.vrhses (logic.strip-conclusions as)))
                                                     (list b)))))
            (and (logic.appealp (build.disjoined-modus-ponens-list b as base))
                 (equal (logic.conclusion (build.disjoined-modus-ponens-list b as base))
                        (logic.por (logic.vlhs (logic.conclusion base)) b))))
  :rule-classes nil)

 (defthm forcing-logic.appealp-of-build.disjoined-modus-ponens-list
   (implies (force (and (logic.formulap b)
                        (logic.appeal-listp as)
                        (logic.appealp base)
                        (logic.all-disjunctionsp (logic.strip-conclusions as))
                        (equal (logic.fmtype (logic.conclusion base)) 'por*)
                        (all-equalp (logic.vlhs (logic.conclusion base)) (logic.vlhses (logic.strip-conclusions as)))
                        (equal (logic.vrhs (logic.conclusion base))
                               (logic.disjoin-formulas (app (logic.negate-formulas (logic.vrhses (logic.strip-conclusions as)))
                                                            (list b))))))
            (equal (logic.appealp (build.disjoined-modus-ponens-list b as base))
                   t))
   :hints(("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-build.disjoined-modus-ponens-list)))))

 (defthm forcing-logic.conclusion-of-build.disjoined-modus-ponens-list
   (implies (force (and (logic.formulap b)
                        (logic.appeal-listp as)
                        (logic.appealp base)
                        (logic.all-disjunctionsp (logic.strip-conclusions as))
                        (equal (logic.fmtype (logic.conclusion base)) 'por*)
                        (all-equalp (logic.vlhs (logic.conclusion base)) (logic.vlhses (logic.strip-conclusions as)))
                        (equal (logic.vrhs (logic.conclusion base))
                               (logic.disjoin-formulas (app (logic.negate-formulas (logic.vrhses (logic.strip-conclusions as)))
                                                            (list b))))))
            (equal (logic.conclusion (build.disjoined-modus-ponens-list b as base))
                   (logic.por (logic.vlhs (logic.conclusion base)) b)))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-build.disjoined-modus-ponens-list)))))

 (defthm forcing-logic.proofp-of-build.disjoined-modus-ponens-list
   (implies (force (and (logic.formulap b)
                        (logic.appeal-listp as)
                        (logic.appealp base)
                        (logic.all-disjunctionsp (logic.strip-conclusions as))
                        (equal (logic.fmtype (logic.conclusion base)) 'por*)
                        (all-equalp (logic.vlhs (logic.conclusion base)) (logic.vlhses (logic.strip-conclusions as)))
                        (equal (logic.vrhs (logic.conclusion base))
                               (logic.disjoin-formulas (app (logic.negate-formulas (logic.vrhses (logic.strip-conclusions as)))
                                                            (list b))))
                        (logic.proof-listp as axioms thms atbl)
                        (logic.proofp base axioms thms atbl)))
            (equal (logic.proofp (build.disjoined-modus-ponens-list b as base) axioms thms atbl)
                   t))))



(defund@ build.multi-assoc-expansion (x as)
  ;; Derive (A_1 v ... v A_n) v P from A_i v P
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp as)
                              (@match (proof x (v A_i P)))
                              (memberp (@formula A_i) as))))
  (if (and (consp as)
           (consp (cdr as)))
      (cond ((equal (car as) (@formula A_i))
             (@derive ((v A_1 P)                             (@given x))
                      ((v A_1 (v (v A_2 (v dots A_n)) P))    (build.disjoined-left-expansion @- (logic.disjoin-formulas (cdr as))))
                      ((v (v A_1 (v dots A_n)) P)            (build.associativity @-))))
            (t
             (@derive ((v (v A_2 (v dots A_n)) P)            (build.multi-assoc-expansion x (cdr as)))
                      ((v A_1 (v (v A_2 (v dots A_n)) P))    (build.expansion (car as) @-))
                      ((v (v A_1 (v A_2 (v dots A_n))) P)    (build.associativity @-)))))
    (logic.appeal-identity x)))

(encapsulate
 ()
 (local (in-theory (enable build.multi-assoc-expansion)))

 (defthm build.multi-assoc-expansion-under-iff
   (iff (build.multi-assoc-expansion x as)
        t))

 (defthm lemma-for-forcing-logic.appealp-of-build.multi-assoc-expansion
   (implies (and (logic.appealp x)
                 (logic.formula-listp as)
                 (equal (logic.fmtype (logic.conclusion x)) 'por*)
                 (memberp (logic.vlhs (logic.conclusion x)) as))
            (and (logic.appealp (build.multi-assoc-expansion x as))
                 (equal (logic.conclusion (build.multi-assoc-expansion x as))
                        (logic.por (logic.disjoin-formulas as)
                                   (logic.vrhs (logic.conclusion x))))))
   :rule-classes nil)

 (defthm forcing-logic.appealp-of-build.multi-assoc-expansion
   (implies (force (and (logic.appealp x)
                        (logic.formula-listp as)
                        (equal (logic.fmtype (logic.conclusion x)) 'por*)
                        (memberp (logic.vlhs (logic.conclusion x)) as)))
            (equal (logic.appealp (build.multi-assoc-expansion x as))
                   t))
   :hints(("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-build.multi-assoc-expansion)))))

 (defthm forcing-logic.conclusion-of-build.multi-assoc-expansion
   (implies (force (and (logic.appealp x)
                        (logic.formula-listp as)
                        (equal (logic.fmtype (logic.conclusion x)) 'por*)
                        (memberp (logic.vlhs (logic.conclusion x)) as)))
            (equal (logic.conclusion (build.multi-assoc-expansion x as))
                   (logic.por (logic.disjoin-formulas as)
                              (logic.vrhs (logic.conclusion x)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-build.multi-assoc-expansion)))))

 (defthm forcing-logic.proofp-of-build.multi-assoc-expansion
   (implies (force (and (logic.appealp x)
                        (logic.formula-listp as)
                        (equal (logic.fmtype (logic.conclusion x)) 'por*)
                        (memberp (logic.vlhs (logic.conclusion x)) as)
                        (logic.proofp x axioms thms atbl)
                        (logic.formula-list-atblp as atbl)))
            (equal (logic.proofp (build.multi-assoc-expansion x as) axioms thms atbl)
                   t))))




(defund@ build.multi-expansion (x as)
  ;; Derive A_1 v ... v A_n from A_i
  ;; Note: this is like Shankar's M1-proof
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp as)
                              (@match (proof x A_i))
                              (memberp (@formula A_i) as))))
  (if (and (consp as)
           (consp (cdr as)))
      (cond ((equal (car as) (@formula A_i))
             (@derive (A_1                             (@given x))
                      ((v A_1 (v A_2 (v dots A_n)))    (build.right-expansion @- (logic.disjoin-formulas (cdr as))))))
            (t
             (@derive ((v A_2 (v dots A_n))            (build.multi-expansion x (cdr as)))
                      ((v A_1 (v A_2 (v dots A_n)))    (build.expansion (car as) @-)))))
    (logic.appeal-identity x)))

(encapsulate
 ()
 (local (in-theory (enable build.multi-expansion)))

 (defthm build.multi-expansion-under-iff
   (iff (build.multi-expansion ai as)
        t))

 (defthm forcing-logic.appealp-of-build.multi-expansion
   (implies (force (and (logic.formula-listp as)
                        (logic.appealp ai)
                        (memberp (logic.conclusion ai) as)))
            (equal (logic.appealp (build.multi-expansion ai as))
                   t)))

 (defthm forcing-logic.conclusion-of-build.multi-expansion
   (implies (force (and (logic.appealp ai)
                        (logic.formula-listp as)
                        (memberp (logic.conclusion ai) as)))
            (equal (logic.conclusion (build.multi-expansion ai as))
                   (logic.disjoin-formulas as)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm forcing-logic.proofp-of-build.multi-expansion
   (implies (force (and (logic.appealp ai)
                        (logic.formula-listp as)
                        (memberp (logic.conclusion ai) as)
                        (logic.proofp ai axioms thms atbl)
                        (logic.formula-list-atblp as atbl)))
            (equal (logic.proofp (build.multi-expansion ai as) axioms thms atbl)
                   t))))



(defund build.modus-ponens-list-okp (x)
  (declare (xargs :guard (logic.appealp x)))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'build.modus-ponens-list)
         (not extras)
         (consp subproofs)
         (let ((base (car subproofs))
               (as   (cdr subproofs)))
           (equal (logic.conclusion base)
                  (logic.disjoin-formulas
                   (app (logic.negate-formulas (logic.strip-conclusions as))
                        (list conclusion))))))))

(defund build.modus-ponens-list-high (b as base)
  (declare (xargs :guard (and (logic.formulap b)
                              (logic.appeal-listp as)
                              (logic.appealp base)
                              (equal (logic.conclusion base)
                                     (logic.disjoin-formulas
                                      (app (logic.negate-formulas (logic.strip-conclusions as))
                                           (list b)))))))
  (logic.appeal 'build.modus-ponens-list
                b
                (cons base (list-fix as))
                nil))

(encapsulate
 ()
 (local (in-theory (enable build.modus-ponens-list-okp)))

 (defthm booleanp-of-build.modus-ponens-list-okp
   (equal (booleanp (build.modus-ponens-list-okp x))
          t)
   :hints(("goal" :in-theory (disable forcing-true-listp-of-logic.subproofs))))

 (defthm build.modus-ponens-list-okp-of-logic.appeal-identity
   (equal (build.modus-ponens-list-okp (logic.appeal-identity x))
          (build.modus-ponens-list-okp x))
   :hints(("goal" :in-theory (disable forcing-true-listp-of-logic.subproofs))))

 (local (in-theory (enable backtracking-logic.formula-atblp-rules)))
 (local (in-theory (disable forcing-logic.formula-atblp-rules
                            forcing-lookup-of-logic.function-name-free
                            forcing-logic.term-list-atblp-of-logic.function-args)))

 (defthm lemma-1-for-soundness-of-build.modus-ponens-list-okp
   (implies (and (build.modus-ponens-list-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (build.modus-ponens-list (logic.conclusion x)
                                             (logic.provable-list-witness
                                              (logic.strip-conclusions (cdr (logic.subproofs x)))
                                              axioms thms atbl)
                                             (logic.provable-witness
                                              (logic.conclusion (car (logic.subproofs x)))
                                              axioms thms atbl)))
                   (logic.conclusion x))))

 (defthm lemma-2-for-soundness-of-build.modus-ponens-list-okp
   (implies (and (build.modus-ponens-list-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.proofp
                    (build.modus-ponens-list (logic.conclusion x)
                                             (logic.provable-list-witness
                                              (logic.strip-conclusions (cdr (logic.subproofs x)))
                                              axioms thms atbl)
                                             (logic.provable-witness
                                              (logic.conclusion (car (logic.subproofs x)))
                                              axioms thms atbl))
                    axioms thms atbl)
                   t)))

 (defthm forcing-soundness-of-build.modus-ponens-list-okp
   (implies (and (build.modus-ponens-list-okp x)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-build.modus-ponens-list-okp
                               lemma-2-for-soundness-of-build.modus-ponens-list-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (build.modus-ponens-list (logic.conclusion x)
                                                         (logic.provable-list-witness
                                                          (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                          axioms thms atbl)
                                                         (logic.provable-witness
                                                          (logic.conclusion (car (logic.subproofs x)))
                                                          axioms thms atbl)))))))))



(defund@ build.disjoined-modus-ponens-list (b as base)
  ;; Derive P v B from P v A1, ..., P v An, and P v ~A1 v ~A2 v ... v ~An v B
  (declare (xargs :guard (and (logic.formulap b)
                              (logic.appeal-listp as)
                              (logic.appealp base)
                              (let ((aconcs   (logic.strip-conclusions as))
                                    (baseconc (logic.conclusion base)))
                                (and (logic.all-disjunctionsp aconcs)
                                     (equal (logic.fmtype baseconc) 'por*)
                                     (all-equalp (logic.vlhs baseconc) (logic.vlhses aconcs))
                                     (equal (logic.vrhs baseconc)
                                            (logic.disjoin-formulas (app (logic.negate-formulas (logic.vrhses aconcs))
                                                                         (list b)))))))))
  (cond ((consp as)
         (@derive ((v P (v A_1 (v dots (v A_n B))))    (@given base))
                  ((v P A_1)                           (@given (car as)))
                  ((v P (v A_2 (v dots (v A_n B))))    (build.disjoined-modus-ponens @- @--))
                  ((v P B)                             (build.disjoined-modus-ponens-list b (cdr as) @-))))
        (t
         (@derive ((v P B)                             (@given (logic.appeal-identity base)))))))

(defund build.disjoined-modus-ponens-list-okp (x)
  (declare (xargs :guard (logic.appealp x)))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'build.disjoined-modus-ponens-list)
         (not extras)
         (consp subproofs)
         (equal (logic.fmtype conclusion) 'por*)
         (let* ((b        (logic.vrhs conclusion))
                (base     (car subproofs))
                (as       (cdr subproofs))
                (baseconc (logic.conclusion base))
                (aconcs   (logic.strip-conclusions as)))
           (and (logic.all-disjunctionsp aconcs)
                (equal (logic.fmtype baseconc) 'por*)
                (all-equalp (logic.vlhs baseconc) (logic.vlhses aconcs))
                (equal (logic.vlhs baseconc) (logic.vlhs conclusion))
                (equal (logic.vrhs baseconc)
                       (logic.disjoin-formulas (app (logic.negate-formulas (logic.vrhses aconcs))
                                                    (list b)))))))))

(defund build.disjoined-modus-ponens-list-high (b as base)
  (declare (xargs :guard (and (logic.formulap b)
                              (logic.appeal-listp as)
                              (logic.appealp base)
                              (let ((aconcs (logic.strip-conclusions as))
                                    (baseconc (logic.conclusion base)))
                                   (and (logic.all-disjunctionsp aconcs)
                                        (equal (logic.fmtype baseconc) 'por*)
                                        (all-equalp (logic.vlhs baseconc) (logic.vlhses aconcs))
                                        (equal (logic.vrhs baseconc)
                                               (logic.disjoin-formulas
                                                (app (logic.negate-formulas (logic.vrhses aconcs))
                                                     (list b)))))))))
  (logic.appeal 'build.disjoined-modus-ponens-list
                (logic.por (logic.vlhs (logic.conclusion base)) b)
                (cons base (list-fix as))
                nil))

(encapsulate
 ()
 (local (in-theory (enable build.disjoined-modus-ponens-list-okp)))

 (defthm booleanp-of-build.disjoined-modus-ponens-list-okp
   (equal (booleanp (build.disjoined-modus-ponens-list-okp x))
          t)
   :hints(("goal" :in-theory (disable forcing-true-listp-of-logic.subproofs))))

 (defthm build.disjoined-modus-ponens-list-okp-of-logic.appeal-identity
   (equal (build.disjoined-modus-ponens-list-okp (logic.appeal-identity x))
          (build.disjoined-modus-ponens-list-okp x))
   :hints(("goal" :in-theory (disable forcing-true-listp-of-logic.subproofs))))

 (local (in-theory (enable backtracking-logic.formula-atblp-rules)))
 (local (in-theory (disable forcing-logic.formula-atblp-rules
                            forcing-lookup-of-logic.function-name-free
                            forcing-logic.term-list-atblp-of-logic.function-args)))

 (defthm lemma-1-for-soundness-of-build.disjoined-modus-ponens-list-okp
   (implies (and (build.disjoined-modus-ponens-list-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (build.disjoined-modus-ponens-list (logic.vrhs (logic.conclusion x))
                                                       (logic.provable-list-witness
                                                        (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                        axioms thms atbl)
                                                       (logic.provable-witness
                                                        (logic.conclusion (car (logic.subproofs x)))
                                                        axioms thms atbl)))
                   (logic.conclusion x))))

 (defthm lemma-2-for-soundness-of-build.disjoined-modus-ponens-list-okp
   (implies (and (build.disjoined-modus-ponens-list-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.proofp
                    (build.disjoined-modus-ponens-list (logic.vrhs (logic.conclusion x))
                                                       (logic.provable-list-witness
                                                        (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                        axioms thms atbl)
                                                       (logic.provable-witness
                                                        (logic.conclusion (car (logic.subproofs x)))
                                                        axioms thms atbl))
                    axioms thms atbl)
                   t)))

 (defthm forcing-soundness-of-build.disjoined-modus-ponens-list-okp
   (implies (and (build.disjoined-modus-ponens-list-okp x)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-build.disjoined-modus-ponens-list-okp
                               lemma-2-for-soundness-of-build.disjoined-modus-ponens-list-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (build.disjoined-modus-ponens-list (logic.vrhs (logic.conclusion x))
                                                                   (logic.provable-list-witness
                                                                    (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                    axioms thms atbl)
                                                                   (logic.provable-witness
                                                                    (logic.conclusion (car (logic.subproofs x)))
                                                                    axioms thms atbl)))))))))


(defund build.multi-assoc-expansion-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'build.multi-assoc-expansion)
         (equal (len subproofs) 1)
         (let ((base (car subproofs))
               (as   extras))
           (and (logic.formula-listp as)
                (logic.formula-list-atblp as atbl)
                (equal (logic.fmtype (logic.conclusion base)) 'por*)
                (memberp (logic.vlhs (logic.conclusion base)) as)
                (equal conclusion
                       (logic.por (logic.disjoin-formulas as)
                                  (logic.vrhs (logic.conclusion base)))))))))

(defund@ build.multi-assoc-expansion-high (x as)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp as)
                              (@match (proof x (v A_i P)))
                              (memberp (@formula A_i) as))))
  (logic.appeal 'build.multi-assoc-expansion
                (logic.por (logic.disjoin-formulas as)
                           (@formula P))
                (list x)
                as))

(encapsulate
 ()
 (local (in-theory (enable build.multi-assoc-expansion-okp)))

 (defthm booleanp-of-build.multi-assoc-expansion-okp
   (equal (booleanp (build.multi-assoc-expansion-okp x atbl))
          t)
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm build.multi-assoc-expansion-okp-of-logic.appeal-identity
   (equal (build.multi-assoc-expansion-okp (logic.appeal-identity x) atbl)
          (build.multi-assoc-expansion-okp x atbl))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm lemma-1-for-soundness-of-build.multi-assoc-expansion-okp
   (implies (and (build.multi-assoc-expansion-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (build.multi-assoc-expansion (logic.provable-witness
                                                  (logic.conclusion (car (logic.subproofs x)))
                                                  axioms thms atbl)
                                                 (logic.extras x)))
                   (logic.conclusion x))))

 (defthm lemma-2-for-soundness-of-build.multi-assoc-expansion-okp
   (implies (and (build.multi-assoc-expansion-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.proofp
                    (build.multi-assoc-expansion (logic.provable-witness
                                                  (logic.conclusion (car (logic.subproofs x)))
                                                  axioms thms atbl)
                                                 (logic.extras x))
                    axioms thms atbl)
                   t)))

 (defthm forcing-soundness-of-build.multi-assoc-expansion-okp
   (implies (and (build.multi-assoc-expansion-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-build.multi-assoc-expansion-okp
                               lemma-2-for-soundness-of-build.multi-assoc-expansion-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (build.multi-assoc-expansion (logic.provable-witness
                                                              (logic.conclusion (car (logic.subproofs x)))
                                                              axioms thms atbl)
                                                             (logic.extras x)))))))))

