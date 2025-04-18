; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book defines set-theoretic operations not already defined in base.lisp,
; and proves properties of set-theoretic operations.

; There are probably many more good rules of this sort that can be proved
; easily.  One source of rules is
; https://en.wikipedia.org/wiki/List_of_set_identities_and_relations .

(in-package "ZF")

(include-book "base")

; (diff x y) = {a \in x : a \notin y}
(zsub diff (x y)     ; name, args
      a              ; x
      x              ; s
      (not (in a y)) ; u
      )

; Forced version of diff:
(defthm in-diff
  (implies (force (diff$prop))
           (equal (in a (diff x y))
                  (and (in a x) (not (in a y))))))

; Subsumed by in-diff:
(in-theory (disable diff$comprehension))

(defun int2 (x y)
  (diff x (diff x y)))

(defthmz in-int2
  (equal (in a (int2 x y))
         (and (in a x)
              (in a y)))
  :props (zfc diff$prop))

(in-theory (disable int2))

(defthmz diff-union2 ; a De Morgan law
  (equal (diff u (union2 x y))
         (int2 (diff u x)
               (diff u y)))
  :props (zfc diff$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

(defthmz diff-int2 ; a De Morgan law
  (equal (diff u (int2 x y))
         (union2 (diff u x)
                 (diff u y)))
  :props (zfc diff$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

(defthmz int2-distributes-over-union2
  (equal (int2 x (union2 y z))
         (union2 (int2 x y)
                 (int2 x z)))
  :props (zfc diff$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

(defthmz union2-distributes-over-int2
  (equal (union2 x (int2 y z))
         (int2 (union2 x y)
               (union2 x z)))
  :props (zfc diff$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

(defthmz diff-distributes-over-diff
  (equal (diff (diff x y) z)
         (diff (diff x z)
               (diff y z)))
  :props (zfc diff$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

(defthmdz subset-implies-diff-is-0
  (implies (subset x y)
           (equal (diff x y) 0))
  :props (zfc diff$prop)
  :hints (("Goal" :in-theory (e/d (extensionality-rewrite)
                                  (subset-x-0)))))

(defthmdz diff-is-0-implies-subset
  (implies (equal (diff x y) 0)
           (subset x y))
  :props (zfc diff$prop)
  :hints (("Goal"
           :expand (subset x y)
           :use ((:instance in-diff (a (subset-witness x y))))
           :in-theory (disable in-diff))))

(defthmdz equal-diff-0-is-subset
  (equal (equal (diff x y) 0)
         (subset x y))
  :props (zfc diff$prop)
  :hints (("Goal"
           :use (subset-implies-diff-is-0 diff-is-0-implies-subset))))

; Already in base.lisp, disabled:
(defthmz union2-commutative
  (equal (union2 x y)
         (union2 y x)))

(encapsulate
  ()

  (local (defthmz int2-commutative-lemma
           (implies (in a (int2 x y))
                    (in a (int2 y x)))
           :props (zfc diff$prop)))

  (defthmdz int2-commutative
    (equal (int2 x y)
           (int2 y x))
    :props (zfc diff$prop)
    :hints (("Goal" :in-theory (enable subset extensionality-rewrite)))))

(defthmz union2-x-x
  (equal (union2 x x)
         x)
  :hints (("Goal" :in-theory (enable subset extensionality-rewrite))))

(defthmz int2-x-x
  (equal (int2 x x) x)
  :props (zfc diff$prop)
  :hints (("Goal" :in-theory (enable subset extensionality-rewrite))))

; Already in base.lisp:
(defthmz union2-associative
  (equal (union2 (union2 x y) z)
         (union2 x (union2 y z))))

(defthmz int2-associative
  (equal (int2 (int2 x y) z)
         (int2 x (int2 y z)))
  :props (zfc diff$prop)
  :hints (("Goal" :in-theory (enable subset extensionality-rewrite))))

(defthmz prod2-distributes-over-union2
  (equal (prod2 x (union2 y z))
         (union2 (prod2 x y)
                 (prod2 x z)))
  :props (zfc prod2$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

(defthmz prod2-distributes-over-int2
  (equal (prod2 x (int2 y z))
         (int2 (prod2 x y)
               (prod2 x z)))
  :props (zfc prod2$prop diff$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

(defthmz prod2-distributes-over-diff
  (equal (prod2 x (diff y z))
         (diff (prod2 x y)
               (prod2 x z)))
  :props (zfc prod2$prop diff$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

(defthmdz union2-commutative2
  (equal (union2 x (union2 y z))
         (union2 y (union2 x z)))
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

(defthmdz int2-commutative2
  (equal (int2 x (int2 y z))
         (int2 y (int2 x z)))
  :props (zfc diff$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

; The next two examples come from "Isabelle’s Logics: FOL and ZF" by Lawrence
; C. Paulson (https://isabelle.in.tum.de/dist/Isabelle2024/doc/logics-ZF.pdf),
; Sections 3.13 and 3.14.  Paulson gives detailed proofs but points out that
; both theorems can be proved automatically using Isabelle's blast tactic.  We
; need to give hints here, but perhaps computed hints could be given that make
; such proofs fully automatic.

(defthmz int2-powerset
  (equal (int2 (powerset x) (powerset y))
         (powerset (int2 x y)))
  :props (zfc diff$prop)
  :hints (("Goal" :in-theory (enable subset extensionality-rewrite))))

(defthmz union-preserves-subset
  (implies (subset x y)
           (subset (union x) (union y)))
  :hints (("Goal"
           :in-theory (enable in-in)
           :expand ((subset (union x) (union y))))))

; The next example, apply-union2-first, is also taken from Paulson's work
; (above), Section 3.15, and was more of a challenge for me.  It would have
; been easy though if I'd already proved domain-union2 and
; funp-union2.  This example highlighted the possibility that there's a
; lot more basic work for me to do on basic library lemmas.

(encapsulate
  ()

  (local
   (defthmz domain-union2-1
     (subset (domain (union2 r s))
             (union2 (domain r) (domain s)))
     :props (zfc domain$prop)
     :hints (("Goal" :in-theory (enable subset in-domain-rewrite)))))

  (local (defthmz domain-union2-2-1
           (implies (subset r1 r2)
                    (subset (domain r1)
                            (domain r2)))
           :props (zfc domain$prop)
           :hints
           (("Goal"
             :use
             ((:instance in-domain-rewrite
                         (x (subset-witness (domain r1)
                                            (domain r2)))
                         (r r1)))
             :restrict
             ((in-car-domain-alt
               ((p (cons (subset-witness (domain r1)
                                         (domain r2))
                         (apply r1
                                (subset-witness (domain r1)
                                                (domain r2))))))))
             :expand
             ((subset (domain r1) (domain r2)))))))

  (local
   (defthmz domain-union2-2
     (subset (union2 (domain r) (domain s))
             (domain (union2 r s)))
     :props (zfc domain$prop)
     :hints (("Goal" :in-theory (enable subset in-domain-rewrite)))))

  (defthmz domain-union2
    (equal (domain (union2 r s))
           (union2 (domain r) (domain s)))
    :props (zfc domain$prop)
    :hints (("Goal" :in-theory (enable extensionality-rewrite subset)))))

(defthmz relation-p-union2
  (implies (and (relation-p f)
                (relation-p g))
           (relation-p (union2 f g)))
  :props (zfc domain$prop)
  :hints (("Goal" :expand ((relation-p (union2 f g))))))

(defthmz int2-non-empty
  (implies (and (in a x)
                (in a y))
           (not (equal (int2 x y) 0)))
  :props (zfc diff$prop)
  :hints (("Goal" :in-theory (disable in-int2) :use in-int2)))

(defthmz in-implies-car-in-domain
	 (implies (and (consp p)
                       (in p f))
		  (in (car p) (domain f)))
	 :props (zfc domain$prop)
	 :rule-classes :forward-chaining)

(defthmz funp-union2
  (implies (and (funp f)
                (funp g)
                (equal (int2 (domain f) (domain g))
                       0))
           (funp (union2 f g)))
  :props (zfc domain$prop diff$prop)
  :hints (("Goal" :expand ((funp (union2 f g))))))

(defthmz apply-union2-first
  (implies (and (funp f)
                (funp g)
                (equal (int2 (domain f) (domain g))
                       0)
                (in x (domain f)))
           (equal (apply (union2 f g) x)
                  (apply f x)))
  :props (zfc domain$prop diff$prop)
  :hints (("Goal" :in-theory (enable apply-intro))))

(defthmz apply-union2-second
  (implies (and (funp f)
                (funp g)
                (equal (int2 (domain f) (domain g))
                       0)
                (in x (domain f)))
           (equal (apply (union2 g f) x)
                  (apply f x)))
  :props (zfc domain$prop diff$prop)
  :hints (("Goal" :in-theory '(union2-commutative apply-union2-first))))

; Analogue of in-implies-car-in-domain
(defthmz in-implies-cdr-in-codomain
	 (implies (and (consp p) (in p f))
		  (in (cdr p) (codomain f)))
	 :props (zfc domain$prop prod2$prop inverse$prop)
	 :rule-classes :forward-chaining)

; A necessary lemma for tc-contains-union in tc.lisp:
(defthmz union-monotone
  (implies (subset s1 s2)
           (subset (union s1) (union s2)))
  :hints (("Goal"
           :in-theory (enable in-in)
           :expand ((subset (union s1) (union s2))))))
