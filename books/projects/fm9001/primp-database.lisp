;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; August 2016

(in-package "FM9001")

;; ======================================================================

;; Abbreviations

(defconst *dp-ram-16x32-inputs*
  '(read-a0 read-a1 read-a2 read-a3
            write-b0 write-b1 write-b2 write-b3
            wen
            d0  d1  d2  d3  d4  d5  d6  d7
            d8  d9  d10 d11 d12 d13 d14 d15
            d16 d17 d18 d19 d20 d21 d22 d23
            d24 d25 d26 d27 d28 d29 d30 d31))

(defconst *mem-32x32-inputs*
  '(rw- strobe-

        a0  a1  a2  a3  a4  a5  a6  a7
        a8  a9  a10 a11 a12 a13 a14 a15
        a16 a17 a18 a19 a20 a21 a22 a23
        a24 a25 a26 a27 a28 a29 a30 a31

        d0  d1  d2  d3  d4  d5  d6  d7
        d8  d9  d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23
        d24 d25 d26 d27 d28 d29 d30 d31
        ))

;; ;; CONS-UP builds a quoted expression suitable for EVAL$.

;; (defun cons-up (list)
;;   (declare (xargs :guard t))
;;   (cond
;;    ((null list) ''NIL)
;;    (t `(CONS ,(car list) ,(cons-up (cdr list))))))

;; The database.
;; The list below identifies the primitive functions and their
;; respective arities.

(defconst *primitives*
  ;; name                  ins  outs sts
  '((ao2                    4    1    0)
    ;; (ao4                    4    1    0)
    (ao6                    3    1    0)
    ;; (ao7                    3    1    0)

    (b-and                  2    1    0)
    (b-and3                 3    1    0)
    (b-and4                 4    1    0)
    (b-buf                  1    1    0)
    (b-equv                 2    1    0)
    (b-equv3                3    1    0)
    (b-if                   3    1    0)
    (b-nand                 2    1    0)
    (b-nand3                3    1    0)
    (b-nand4                4    1    0)
    (b-nand5                5    1    0)
    (b-nand6                6    1    0)
    (b-nand8                8    1    0)
    (b-nbuf                 1    2    0)
    (b-nor                  2    1    0)
    (b-nor3                 3    1    0)
    (b-nor4                 4    1    0)
    (b-nor5                 5    1    0)
    (b-nor6                 6    1    0)
    (b-nor8                 8    1    0)
    (b-not                  1    1    0)
    (b-not-b4ip             1    1    0)
    ;; (b-not-ivap             1    1    0)
    (b-or                   2    1    0)
    (b-or3                  3    1    0)
    (b-or4                  4    1    0)
    (b-xor                  2    1    0)
    ;; (b-xor3                 3    1    0)
    ;; (del2                   1    1    0)
    (del4                   1    1    0)
    ;; (del10                  1    1    0)
    (procmon                4    1    0)
    (dp-ram-16x32          41   32    1)

    (fd1                    2    2    1)
    (fd1s                   4    2    1)
    ;; (fd1sp                  4    2    1)
    (fd1slp                 5    2    1)

    (id                     1    1    0)

    (mem-32x32             66   33    1)
    (ram-enable-circuit     4    1    0)

    (t-buf                  2    1    0)
    (t-wire                 2    1    0)
    (pullup                 1    1    0)
    (ttl-bidirect           4    3    0)
    (ttl-clk-input          2    2    0)
    (ttl-input              2    2    0)
    (ttl-output             1    1    0)
    (ttl-output-parametric  1    1    0)
    (ttl-output-fast        1    1    0)
    (ttl-tri-output         2    1    0)
    (ttl-tri-output-fast    2    1    0)
    (vdd                    0    1    0)
    (vdd-parametric         0    1    0)
    (vss                    0    1    0)))

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

(defun primp-sts  (fn)
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

(defthm natp-primp-sts
  (implies (primp fn)
           (natp (primp-sts fn)))
  :rule-classes
  (:type-prescription
   (:linear
    :corollary
    (implies (primp fn)
             (<= 0 (primp-sts fn))))))

(in-theory (disable primp primp-ins primp-outs primp-sts))
