; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This proof closely follows the proof of Cantor's theorem as presented in the
; Wikipedia article of that name (as of 4/5/2025), at the following URL.

; https://en.wikipedia.org/wiki/Cantor%27s_theorem

; That version states that a function f : A -> Powerset(A) cannot be
; surjective.  Since then A is the domain of f, I prove it in the form: the
; image of f can not equal the powerset of the domain of f.

; In the theorem statements below, the :props arguments generate hypotheses,
; all of which are justified by ACL2 formulations of the axioms of ZF plus
; global choice.  Thus, the :props arguments may be ignored when viewing those
; statements as theorems of ZFC.  (The development of set theory in ACL2 uses
; the well-known fact that the addition of global choice is conservative over
; ZFC.)

(in-package "ZF")

(include-book "base")

; Let b(f) = {x \in domain(f): not(x \in f(x)}.
; This is the set B from the Wikpedia article, expressed as a function of f.
(zsub b (f) ; name, args
      x     ; x
      (domain f)
      (not (in x (apply f x))))

; Let xi(f) = f^{-1}(b f).  This is Greek letter xi from the Wikipedia article,
; expressed as a function of f.
(defun xi (f)
  (apply (inverse f) (b f)))

; x \in B <=> not(x \in f(x))
(defthmz lemma-1
  (implies (in x (domain f))
           (iff (in x (b f))
                (not (in x (apply f x)))))
  :rule-classes nil ; not intended to be used as a rewrite rule
  :props (zfc b$prop))

(encapsulate
  ()

  (local
   (defthmz lemma-2a
     (implies (and (funp f)
                   (equal (image f)
                          (powerset (domain f))))
              (in (b f)
                  (image f)))
     :props (zfc b$prop)))

; f(xi) = B
  (defthmz lemma-2
    (implies (and (funp f)
                  (equal (image f)
                         (powerset (domain f))))
             (equal (apply f (xi f))
                    (b f)))
    :props (zfc prod2$prop domain$prop inverse$prop b$prop)))

; xi \in A
(defthmz lemma-3
  (implies (and (funp f)
                (equal (image f)
                       (powerset (domain f))))
           (in (xi f)
               (domain f)))
  :instructions (:bash
                 (:rewrite in-image-implies-in-apply-inverse-domain)
                 :prove)
  :props (zfc prod2$prop domain$prop inverse$prop b$prop))

; Function f does not map onto the powerset of A.
(defthmz cantor
  (implies (funp f)
           (not (equal (image f)
                       (powerset (domain f)))))
  :props (zfc prod2$prop domain$prop inverse$prop b$prop)
  :hints (("Goal"
           :in-theory (union-theories '(lemma-2 lemma-3)
                                      (theory 'minimal-theory))
           :use ((:instance lemma-1 (x (xi f)))))))
