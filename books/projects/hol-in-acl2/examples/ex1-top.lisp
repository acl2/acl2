; Copyright (C) 2026, Matt Kaufmann and Konrad Slind
; Written by Matt Kaufmann and Konrad Slind
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; For background, see file README.txt.

; This book provides a nice presentation of the result proved in
; ex1-proof.lisp.  Here we include non-locally only the translated HOL
; development from ex1-thy.lisp, exhibiting the desired theorem proved from
; that translated HOL development.

; See ex1-proof.lisp for comments about the proof, in particular about
; how to view the main result as a formalization of this prettier statement.

#|
(EQUAL (= (AND (= (FST P) (FST Q))
               (= (SND P) (SND Q)))
          (= P Q))
       HP-TRUE)
|#

(in-package "HOL")

(include-book "ex1-thy") ; translated HOL development

(local (include-book "ex1-proof"))

; Here is the HOL statement for the defgoal body below.  (This is an ASCII
; version without quantifiers; see ex1.defhol for the unmodified version.)
#|
  (FST p = FST q & SND p = SND q) <=> (p = q)
|#

(defgoal pair_fst_snd_eq
  (implies
   (and (alist-subsetp (ex1$hta) hta)
        (hpp p hta)
        (equal (hp-type p) (typ (:hash a b)))
        (hpp q hta)
        (equal (hp-type q) (typ (:hash a b)))
        (force (ex1$prop)))
   (equal (hp= (hp-and
                (hp= (hap* (fst (typ (:arrow* (:hash a b) a))) p)
                     (hap* (fst (typ (:arrow* (:hash a b) a))) q))
                (hp= (hap* (snd (typ (:arrow* (:hash a b) b))) p)
                     (hap* (snd (typ (:arrow* (:hash a b) b))) q)))
               (hp= p q))
          (hp-true))))
