; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

; This book defines a set, (hpp-set) = {x \in V_{\omega*2}: (hpp-p x)}, which
; is intended to be the set of all HOL value pairs.  The final theorem,
; hpp-set-correctness, proves that (hpp-set) is indeed exactly that set.

; A key enabler is the set, V_{omega*2}, which we define to be the result of
; iterating powerset omega*2 times.  A key lemma is
; hol-valuep-implies-in-v-omega*2, proved in hol.lisp, which states that the
; evaluation of a type expression or of a list of type expressions is in
; V_{omega*2}.

; As of this writing, we don't need this book because the HOL props generated
; by translating theories implicitly create HOL values (including functions) as
; sets.  But down the road there could be a need to have a "bounding set" on
; which to use separation to show that a given HOL value or HOL value pair is a
; set, and this book provides that bounding set as (v-omega*2) and, more
; tightly, as (hpp-set) for the set of HOL value pairs.

(include-book "hol")

(defun-sk hpp-p (x)
  (exists (hta)
    (and (htap1 hta) ; types map to values in (v-omega*2)
         (hpp x hta))))

(zsub hpp-set () ; {x \in V_{\omega*2}: (hpp-p x)}
      x
      (v-omega*2)
      (hpp-p x))

(defthmz hol-valuep-implies-in-v-omega*2
  (implies (and (htap1 hta)
                (hol-valuep x type hta)
                (hol-typep-flg nil type hta))
           (in x (v-omega*2)))
  :props (hta-prop))

(defthmz hol-typep-flg-in-v-omega*2
  (implies (and (htap1 hta)
                (hol-typep-flg flg typ hta))
           (in typ (v-omega*2)))
  :props (hta-prop))

(defthmz hpp-set-correctness-lemma
  (implies (hpp-p x)
           (in x (hpp-set)))
  :props (hta-prop hpp-set$prop)
  :rule-classes nil)

(defthmz hpp-set-correctness
  (equal (in x (hpp-set))
         (hpp-p x))
  :hints (("Goal" :use hpp-set-correctness-lemma))
  :props (hta-prop hpp-set$prop))
