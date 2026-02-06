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

; The call below can be generated as follows.
;   (include-book "projects/hol-in-acl2/examples/ex1-thy" :dir :system)
;   (in-package "HOL")
;   (find-goal pair_fst_snd_eq)
; Although the call below of defgoal expands to a corresponding defthm call
; with name HOL{PAIR_FST_SND_EQ}, it first checks that its formula is the
; translation of the defhol form with the given name (in this case,
; pair_fst_snd_eq) from the corresponding defhol form (in this case, at the end
; of file ex1.defhol).
(DEFGOAL
  PAIR_FST_SND_EQ
  (IMPLIES (AND (ALIST-SUBSETP (EX1$HTA) HTA)
                (HPP P HTA)
                (EQUAL (HP-TYPE P) (TYP (:HASH A B)))
                (HPP Q HTA)
                (EQUAL (HP-TYPE Q) (TYP (:HASH A B)))
                (FORCE (EX1$PROP)))
           (EQUAL (HP= (HP-AND (HP= (HAP* (FST (TYP (:ARROW* (:HASH A B) A)))
                                          P)
                                    (HAP* (FST (TYP (:ARROW* (:HASH A B) A)))
                                          Q))
                               (HP= (HAP* (SND (TYP (:ARROW* (:HASH A B) B)))
                                          P)
                                    (HAP* (SND (TYP (:ARROW* (:HASH A B) B)))
                                          Q)))
                       (HP= P Q))
                  (HP-TRUE))))
