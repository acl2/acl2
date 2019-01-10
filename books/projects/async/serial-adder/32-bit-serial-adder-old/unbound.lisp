;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

;; For doing proofs of recursive module generators, it is often necessary to
;; know that a signal name is "unbound", i.e., does not appear further in the
;; generated body.  By a "body" we mean an occurrence body, and by "bound" we
;; mean assigned a value in the ALIST created by SE-OCC.  This concept is
;; eloquently summed up in the final two lemmas of this file.

(in-package "ADE")

(include-book "de")

;; ======================================================================

;; UNBOUND-IN-BODY

(defun unbound-in-body (name body)
  (if (atom body)
      t
    (let ((occurrence (car body)))
      (let ((outputs (occ-outs occurrence)))
        (and (not (member name outputs))
             (unbound-in-body name (cdr body)))))))

(defthm unbound-in-body-atom
  (implies (atom body)
           (unbound-in-body name body)))

(defthm unbound-in-body-listp
  (equal (unbound-in-body name (cons occurrence rest))
         (let ((outputs (occ-outs occurrence)))
           (and (not (member name outputs))
                (unbound-in-body name rest)))))

(in-theory (disable unbound-in-body))

;; ALL-UNBOUND-IN-BODY

(defun all-unbound-in-body (names body)
  (if (atom body)
      t
    (let ((occurrence (car body)))
      (let ((outputs (occ-outs occurrence)))
        (and (disjoint names outputs)
             (all-unbound-in-body names (cdr body)))))))

(defthm all-unbound-in-body-atom
  (implies (atom body)
           (all-unbound-in-body names body)))

(defthm all-unbound-in-body-listp
  (equal (all-unbound-in-body names (cons occurrence rest))
         (let ((outputs (occ-outs occurrence)))
           (and (disjoint names outputs)
                (all-unbound-in-body names rest)))))

(defthm all-unbound-in-body-append
  (equal (all-unbound-in-body (append names1 names2) body)
         (and (all-unbound-in-body names1 body)
              (all-unbound-in-body names2 body))))

(defthm all-unbound-in-body-cons
  (equal (all-unbound-in-body (cons name names) body)
         (and (unbound-in-body name body)
              (all-unbound-in-body names body))))

(defthm all-unbound-in-body-atom-names
  (implies (atom names)
           (all-unbound-in-body names body)))

(in-theory (disable all-unbound-in-body))

;; Lemmas

(defthm unbound-in-body-se-occ
  (implies (unbound-in-body name body)
           (equal (assoc-eq-value name
                                  (se-occ body
                                          bindings
                                          state-bindings
                                          netlist))
                  (assoc-eq-value name bindings)))
  :hints (("Goal"
           :induct (se-occ-induct body bindings state-bindings netlist))))

(defthm all-unbound-in-body-se-occ
  (implies (all-unbound-in-body names body)
           (equal (assoc-eq-values
                   names
                   (se-occ body bindings state-bindings netlist))
                  (assoc-eq-values names bindings)))
  :hints (("Goal"
           :induct (se-occ-induct body bindings state-bindings netlist))))
