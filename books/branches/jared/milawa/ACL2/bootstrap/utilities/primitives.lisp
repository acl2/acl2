;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "primitives-6")

(defmacro %cdr-induction (x)
  `(%induct (rank ,x)
            ((not (consp ,x))
             nil)
            ((consp ,x)
             (((,x (cdr ,x)))))))

(defmacro %cdr-cdr-induction (x y)
  `(%induct (rank ,x)
            ((or (not (consp ,x))
                 (not (consp ,y)))
             nil)
            ((and (consp ,x)
                  (consp ,y))
             (((,x (cdr ,x))
               (,y (cdr ,y)))))))

(defmacro %cdr-cdr-cdr-induction (x y z)
  `(%induct (rank ,x)
            ((or (not (consp ,x))
                 (not (consp ,y))
                 (not (consp ,z)))
             nil)
            ((and (consp ,x)
                  (consp ,y)
                  (consp ,z))
             (((,x (cdr ,x))
               (,y (cdr ,y))
               (,z (cdr ,z)))))))

(defmacro %four-cdrs-induction (a b c d)
  `(%induct (rank ,a)
            ((or (not (consp ,a))
                 (not (consp ,b))
                 (not (consp ,c))
                 (not (consp ,d)))
             nil)
            ((and (consp ,a)
                  (consp ,b)
                  (consp ,c)
                  (consp ,d))
             (((,a (cdr ,a))
               (,b (cdr ,b))
               (,c (cdr ,c))
               (,d (cdr ,d)))))))

(defmacro %dec-induction (a)
  `(%induct (nfix ,a)
            ((zp ,a)
             nil)
            ((not (zp ,a))
             (((,a (- ,a 1)))))))

(defmacro %dec-dec-induction (a b)
  `(%induct (nfix ,a)
            ((or (zp ,a)
                 (zp ,b))
             nil)
            ((and (not (zp ,a))
                  (not (zp ,b)))
             (((,a (- ,a '1))
               (,b (- ,b '1)))))))

(defmacro %sub-induction (a b)
  `(%induct (nfix ,a)
            ((zp ,b)
             nil)
            ((and (not (zp ,b))
                  (< ,a ,b))
             nil)
            ((and (not (zp ,b))
                  (not (< ,a ,b)))
             (((,a (- ,a ,b))
               (,b ,b))))))

(defmacro %car-cdr-induction (x)
  `(%induct (rank ,x)
            ((not (consp ,x))
             nil)
            ((consp ,x)
             (((,x (car ,x)))
              ((,x (cdr ,x)))))))


(%ensure-exactly-these-rules-are-missing
 "../../utilities/primitives"
 ;; These should be missing because we don't want to add extra axioms for
 ;; them yet.
; DEFINITION-OF-BITWISE-NTH
; DEFINITION-OF-BITWISE-XOR
; DEFINITION-OF-BITWISE-OR
; DEFINITION-OF-BITWISE-AND
; DEFINITION-OF-BITWISE-SHR
; DEFINITION-OF-BITWISE-SHL
; DEFINITION-OF-EXPT
; DEFINITION-OF-MOD
; DEFINITION-OF-FLOOR
; DEFINITION-OF-*
 ;; This is only needed to tell ACL2 to use ord< as its wfr.
 ORD<-IS-WELL-FOUNDED
 ;; This is only needed to tell ACL2 to use car-cdr-elim automatically; we
 ;; use the %car-cdr-elim tactic instead
 CAR-CDR-ELIM

 ;; BOZO why is this rule missing?
 ;; Aah, it ought to be local in the ACL2 file but we forgot to keep it local. Stupid us.
 ;; Relocalize it in the ACL2 file and get rid of it from this list.
 NATURAL-LESS-THAN-ONE-IS-ZERO

 ;; This isn't part of the logic.
; UNBOUNDED-RANK

 ;; This one was added to account for changes in ACL2 6.2.
 EQUAL-OF-CONS-REWRITE-CONSTANTS
 )


(%save-events "primitives.events")