; ACL2 Parser for Java
; Copyright (C) 2013 Battelle Memorial Institute
;
; Contact:
;  David Rager, ragerdl@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: David Rager <ragerdl@cs.utexas.edu>


(in-package "ACL2")

(include-book "countereg-gen/top" :dir :system)

(acl2s-defaults :set testing-enabled t)

(acl2s-defaults :set verbosity-level 3)

(defconst *pstate-values*
  '((:PSTATE (CONDITION . "G")
             (SUBTREE "S")
             (DOT . 0)
             (CONSTITUENT-INDEX . 0)
             (DOT-INDEX . 0)
             (SOURCE-STATES))
    (:PSTATE (CONDITION . "NP")
             (SUBTREE "det" "nominal")
             (DOT . 0)
             (CONSTITUENT-INDEX . 0)
             (DOT-INDEX . 0)
             (SOURCE-STATES))
    (:PSTATE (CONDITION . "NP")
             (SUBTREE "proper-noun")
             (DOT . 0)
             (CONSTITUENT-INDEX . 0)
             (DOT-INDEX . 0)
             (SOURCE-STATES))
    (:PSTATE (CONDITION . "VP")
             (SUBTREE "verb")
             (DOT . 0)
             (CONSTITUENT-INDEX . 0)
             (DOT-INDEX . 0)
             (SOURCE-STATES))
    (:PSTATE (CONDITION . "VP")
             (SUBTREE "verb" "NP")
             (DOT . 0)
             (CONSTITUENT-INDEX . 0)
             (DOT-INDEX . 0)
             (SOURCE-STATES))
    (:PSTATE (CONDITION . "VP")
             (SUBTREE "verb")
             (DOT . 1)
             (CONSTITUENT-INDEX . 0)
             (DOT-INDEX . 1)
             (SOURCE-STATES (:PSTATE (CONDITION . "verb")
                                     (SUBTREE "book")
                                     (DOT . 1)
                                     (CONSTITUENT-INDEX . 0)
                                     (DOT-INDEX . 1)
                                     (SOURCE-STATES))))
    (:PSTATE
     (CONDITION . "S")
     (SUBTREE "VP")
     (DOT . 1)
     (CONSTITUENT-INDEX . 0)
     (DOT-INDEX . 1)
     (SOURCE-STATES (:PSTATE (CONDITION . "VP")
                             (SUBTREE "verb")
                             (DOT . 1)
                             (CONSTITUENT-INDEX . 0)
                             (DOT-INDEX . 1)
                             (SOURCE-STATES (:PSTATE (CONDITION . "verb")
                                                     (SUBTREEb "book")
                                                     (DOT . 1)
                                                     (CONSTITUENT-INDEX . 0)
                                                     (DOT-INDEX . 1)
                                                     (SOURCE-STATES))))))))

(register-custom-type pstate 10 *pstate-values* pstate-p)

(test? (natp x))

#|
(skip-proofs
 (defdata
   (pstate (list (cons :condition  string)
                 (cons :subtree true-list)
                 (cons :dot  nat)
                 (cons :dot-index  nat) ; optional
                 (cons :constituent-index  nat)
                 (cons :pstate-list pstate-list)))
   (pstate-list (oneof nil
                       (cons pstate pstate-list)))))

(register-custom-type nat t nth-nat natp)
|#

#|
(defun pstate->print (pstate)
  (declare (xargs :guard (pstate-p pstate)
                  :guard-debug t))
  (let ((condition (pstate->condition pstate))
        (subtree (pstate->subtree pstate))
        (dot (nfix (pstate->dot pstate))))
    (cw "#{~@0 -> ~*1. ~*2 [~x3,~x4]}"
        condition
        `("" "~@*" "~@* " "~@* " ,(subseq subtree 0 dot))
        `("" "~@*" "~@* " "~@* " ,(subseq subtree dot (len subtree)))
        (pstate->constituent-index pstate)
        (pstate->dot-index pstate))))

:pts

(DEFUNS
  (NTH-PSTATE
   (X)
   (DECLARE (XARGS :MEASURE (NFIX X)))
   (LET
    ((INFXLST (DEFDATA::SPLIT-NAT 2 (NFIX X))))
    (CONS
     (LET ((X (NTH 0 INFXLST)))
          (LET ((INFXLST (LIST (NFIX X))))
               (CONS ':CONDITION
                     (LET ((X (NTH 0 INFXLST)))
                          (NTH-STRING X)))))
     (LET
      ((X (NTH 1 INFXLST)))
      (LET
       ((INFXLST (DEFDATA::SPLIT-NAT 2 (NFIX X))))
       (CONS
        (LET ((X (NTH 0 INFXLST)))
             (LET ((INFXLST (LIST (NFIX X))))
                  (CONS ':SUBTREE
                        (LET ((X (NTH 0 INFXLST)))
                             (NTH-TRUE-LIST X)))))
        (LET
         ((X (NTH 1 INFXLST)))
         (LET
          ((INFXLST (DEFDATA::SPLIT-NAT 2 (NFIX X))))
          (CONS
           (LET ((X (NTH 0 INFXLST)))
                (LET ((INFXLST (LIST (NFIX X))))
                     (CONS ':DOT
                           (LET ((X (NTH 0 INFXLST)))
                                (NTH-NAT X)))))
           (LET
            ((X (NTH 1 INFXLST)))
            (LET
             ((INFXLST (DEFDATA::SPLIT-NAT 2 (NFIX X))))
             (CONS
              (LET ((X (NTH 0 INFXLST)))
                   (LET ((INFXLST (LIST (NFIX X))))
                        (CONS ':DOT-INDEX
                              (LET ((X (NTH 0 INFXLST)))
                                   (NTH-NAT X)))))
              (LET
               ((X (NTH 1 INFXLST)))
               (LET
                ((INFXLST (DEFDATA::SPLIT-NAT 2 (NFIX X))))
                (CONS
                 (LET ((X (NTH 0 INFXLST)))
                      (LET ((INFXLST (LIST (NFIX X))))
                           (CONS ':CONSTITUENT-INDEX
                                 (LET ((X (NTH 0 INFXLST)))
                                      (NTH-NAT X)))))
                 (LET
                  ((X (NTH 1 INFXLST)))
                  (LET ((INFXLST (LIST (NFIX X))))
                       (CONS (LET ((X (NTH 0 INFXLST)))
                                  (LET ((INFXLST (LIST (NFIX X))))
                                       (CONS ':PSTATE-LIST
                                             (LET ((X (NTH 0 INFXLST)))
                                                  (NTH-PSTATE-LIST X)))))
                             'NIL))))))))))))))))))
  (NTH-PSTATE-LIST (X)
                   (DECLARE (XARGS :MEASURE (NFIX X)))
                   (IF (OR (NOT (INTEGERP X)) (< X 1))
                       'NIL
                       (LET ((X (- X 1)))
                            (LET ((INFXLST (DEFDATA::SPLIT-NAT 2 (NFIX X))))
                                 (CONS (LET ((X (NTH 0 INFXLST)))
                                            (NTH-PSTATE X))
                                       (LET ((X (NTH 1 INFXLST)))
                                            (NTH-PSTATE-LIST X))))))))

|#

