; Copyright (C) 2025, Matt Kaufmann and Konrad Slind
; Written by Matt Kaufmann and Konrad Slind
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; For background, see file README.txt.

; This book provides a nice presentation of the result proved in
; eval-poly-proof.lisp.  See that book for comments.  Here we include
; non-locally only the translated HOL development from eval-poly-thy.lisp,
; exhibiting the desired theorem proved from that translated HOL development.

; See eval-poly-proof.lisp for comments about the proof, in particular about
; how to view the main result as a formalization of this prettier statement.

#|
(EQUAL (= (EVAL_POLY (SUM_POLYS X Y) V)
          (+ (EVAL_POLY X V) (EVAL_POLY Y V)))
       HP-TRUE)
|#

(in-package "HOL")

(include-book "eval-poly-thy") ; translated HOL development

(local (include-book "eval-poly-proof"))

(DEFGOAL EVAL_SUM_POLY_DISTRIB
 (IMPLIES
  (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
       (HPP X HTA)
       (EQUAL (HP-TYPE X)
              (TYP (:LIST (:HASH :NUM :NUM))))
       (HPP Y HTA)
       (EQUAL (HP-TYPE Y)
              (TYP (:LIST (:HASH :NUM :NUM))))
       (HPP V HTA)
       (EQUAL (HP-TYPE V) (TYP :NUM))
       (FORCE (EVAL-POLY$PROP)))
  (EQUAL
   (HP-IMPLIES
       (HP-AND (HAP* (POLYP (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                          :BOOL)))
                     X)
               (HAP* (POLYP (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                          :BOOL)))
                     Y))
       (HP= (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                           :NUM :NUM)))
                  (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM)))))
                        X Y)
                  V)
            (HP+ (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                :NUM :NUM)))
                       X V)
                 (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                :NUM :NUM)))
                       Y V))))
   (HP-TRUE))))
