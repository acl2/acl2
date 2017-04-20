;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; July 2016

;; Automatic definition and proofs for simple linear vector modules of
;; primitives or other modules.  VECTOR-MODULE is defined in
;; "vector-macros.lisp".

(in-package "FM9001")

(include-book "unbound")
(include-book "vector-macros")

;; ======================================================================

;; VECTOR-MODULE-INDUCTION
;; The induction scheme for vector modules.

(defun vector-module-induction (body m n bindings state-bindings netlist)
  (if (zp n)
      (list body m bindings state-bindings netlist)
    (vector-module-induction
     (cdr body)
     (1+ m)
     (1- n)
     (se-occ-bindings 1 body bindings state-bindings netlist)
     state-bindings
     netlist)))

;; V-BUF
;; V-OR
;; V-XOR
;; V-PULLUP
;; V-WIRE

(vector-module v-buf (g (y) b-buf (a)) ((v-threefix a)))

(vector-module v-or (g (y) b-or (a b)) ((fv-or a b)) :enable (fv-or))

(vector-module v-xor (g (y) b-xor (a b)) ((fv-xor a b)) :enable (fv-xor))

(vector-module v-pullup (g (y) pullup (a)) ((v-pullup a)) :enable (v-pullup))

(vector-module v-wire (g (y) t-wire (a b)) ((v-wire a b)) :enable (v-wire))
