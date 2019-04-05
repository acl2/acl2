;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

(in-package "ADE")

;; ======================================================================

;; The database.
;; The list below identifies the primitive functions and their
;; respective arities.

(defconst *primitives*
  ;; name                  ins  outs st
  '((b-and                  2    1    0)
    (b-and3                 3    1    0)
    (b-and4                 4    1    0)
    (b-and5                 5    1    0)
    (b-bool                 1    1    0)
    (b-buf                  1    1    0)
    (b-equv                 2    1    0)
    (b-if                   3    1    0)
    (b-nand                 2    1    0)
    (b-nand3                3    1    0)
    (b-nand4                4    1    0)
    (b-nand5                5    1    0)
    (b-nand6                6    1    0)
    (b-nand8                8    1    0)
    (b-nor                  2    1    0)
    (b-nor3                 3    1    0)
    (b-nor4                 4    1    0)
    (b-nor5                 5    1    0)
    (b-nor6                 6    1    0)
    (b-nor8                 8    1    0)
    (b-not                  1    1    0)
    (b-or                   2    1    0)
    (b-or3                  3    1    0)
    (b-or4                  4    1    0)
    (b-or5                  5    1    0)
    (b-xnor                 2    1    0)
    (b-xor                  2    1    0)

    (ff                     2    2    1)
    (latch                  2    2    1)
    (link-cntl              2    1    1)

    (par-shift-reg32       35   32    1)
    (pullup                 1    1    0)
    (shift-reg32            2   32    1)
    (t-buf                  2    1    0)
    (t-wire                 2    1    0)
    (vdd                    0    1    0)
    (vss                    0    1    0)
    (wire                   1    1    0)))

(defthm symbol-alistp-*primitives*
  ;; Sanity check
  (symbol-alistp *primitives*))

(defun primp (fn)
  (declare (xargs :guard t))
  (assoc-eq fn *primitives*))

(defun primp-ins  (fn)
  (declare (xargs :guard t))
  (cadr (primp fn)))

(defun primp-outs (fn)
  (declare (xargs :guard t))
  (caddr (primp fn)))

(defun primp-st  (fn)
  (declare (xargs :guard t))
  (cadddr (primp fn)))

(defthm natp-primp-ins
  (implies (primp fn)
           (natp (primp-ins fn)))
  :rule-classes
  (:type-prescription
   (:linear
    :corollary
    (implies (primp fn)
             (<= 0 (primp-ins fn))))))

(defthm posp-primp-outs
  (implies (primp fn)
           (posp (primp-outs fn)))
  :rule-classes
  (:type-prescription
   (:linear
    :corollary
    (implies (primp fn)
             (< 0 (primp-outs fn))))))

(defthm natp-primp-st
  (implies (primp fn)
           (natp (primp-st fn)))
  :rule-classes
  (:type-prescription
   (:linear
    :corollary
    (implies (primp fn)
             (<= 0 (primp-st fn))))))

(in-theory (disable primp primp-ins primp-outs primp-st))
