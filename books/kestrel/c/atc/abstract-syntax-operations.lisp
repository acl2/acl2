; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-abstract-syntax-operations
  :parents (atc-implementation atc-abstract-syntax)
  :short "Operations on the C abstract syntax for ATC."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binop-strictp ((op binopp))
  :returns (yes/no booleanp)
  :short "Check if a binary operator is strict."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the binary operators except logical conjunction and disjunction
     are strict."))
  (and (member-eq (binop-kind op)
                  (list :mul
                        :div
                        :rem
                        :add
                        :sub
                        :shl
                        :shr
                        :lt
                        :gt
                        :le
                        :ge
                        :eq
                        :ne
                        :bitand
                        :bitxor
                        :bitior
                        :asg
                        :asg-mul
                        :asg-div
                        :asg-rem
                        :asg-add
                        :asg-sub
                        :asg-shl
                        :asg-shr
                        :asg-and
                        :asg-xor
                        :asg-ior))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binop-purep ((op binopp))
  :returns (yes/no booleanp)
  :short "Check if a binary operator is pure."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the binary operators except (simple and compound) assignments
     are pure."))
  (and (member-eq (binop-kind op)
                  (list :mul
                        :div
                        :rem
                        :add
                        :sub
                        :shl
                        :shr
                        :lt
                        :gt
                        :le
                        :ge
                        :eq
                        :ne
                        :bitand
                        :bitxor
                        :bitior
                        :logand
                        :logor))
       t)
  :hooks (:fix))
