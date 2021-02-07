;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "de")
(include-book "fm9001-spec")
(include-book "macros")

(local (include-book "list-rewrites"))

;; ======================================================================

;; An inverting 7-to-1 mux, with an implied F for the 8th data input.

(fn-to-module
 store-resultp-mux (s0 s1 s2 d0 d1 d2 d3 d4 d5 d6)
 (declare (xargs :guard t))
 (let ((s0- (b-not s0))
       (s1- (b-not s1))
       (s2- (b-not s2)))
   (let ((x01 (ao2 s0- d0 s0 d1))
         (x23 (ao2 s0- d2 s0 d3))
         (x45 (ao2 s0- d4 s0 d5))
         (x67 (b-nand s0- d6)))
     (let ((x0123 (ao2 s1- x01 s1 x23))
           (x4567 (ao2 s1- x45 s1 x67)))
       (ao2 s2- x0123 s2 x4567)))))

;;; Alternate definition of store-resultp.

(defun b-store-resultp (store-cc flags)
  (declare (xargs :guard (and (true-listp store-cc)
                              (true-listp flags))))
  (let ((s0 (car store-cc))
        (s1 (cadr store-cc))
        (s2 (caddr store-cc))
        (s3 (cadddr store-cc))
        (z (car flags))
        (n (cadr flags))
        (v (caddr flags))
        (c (cadddr flags)))
    (b-xor s0 (store-resultp-mux
               s1 s2 s3
               c v n z
               (b-or c z) (b-xor n v) (b-or z (b-xor n v))))))

(defun f$b-store-resultp (store-cc flags)
  (declare (xargs :guard (and (true-listp store-cc)
                              (true-listp flags))))
  (let ((s0 (car store-cc))
        (s1 (cadr store-cc))
        (s2 (caddr store-cc))
        (s3 (cadddr store-cc))
        (z (car flags))
        (n (cadr flags))
        (v (caddr flags))
        (c (cadddr flags)))
    (f-xor s0 (f$store-resultp-mux
               s1 s2 s3
               c v n z
               (f-or c z) (f-xor n v) (f-or z (f-xor n v))))))

(defthm f$b-store-resultp=b-store-resultp
  (implies (and (bvp store-cc)
                (bvp flags))
           (equal (f$b-store-resultp store-cc flags)
                  (b-store-resultp store-cc flags)))
  :hints (("Goal" :in-theory (e/d (bvp) (b-gates)))))

(in-theory (disable b-store-resultp f$b-store-resultp))

(defconst *b-store-resultp*
  (cons
   '(b-store-resultp
     (s0 s1 s2 s3 z n v c)
     (result)
     ()
     ((g0 (cz) b-or (c z))
      (g1 (nv) b-xor (n v))
      (g2 (znv) b-or (z nv))
      (g3 (mux) store-resultp-mux (s1 s2 s3 c v n z cz nv znv))
      (g4 (result) b-xor (s0 mux))))

   *store-resultp-mux*))

(defthmd b-store-resultp-okp
  (and (net-syntax-okp *b-store-resultp*)
       (net-arity-okp *b-store-resultp*)))

(defund b-store-resultp& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (netlist-hyps netlist b-store-resultp)
       (store-resultp-mux& (delete-to-eq 'b-store-resultp netlist))))

;; Proof of equivalence.

(defthm b-store-resultp=store-resultp$help
  (implies (and (booleanp s0) (booleanp s1) (booleanp s2) (booleanp s3)
                (booleanp s4) (booleanp s5) (booleanp s6) (booleanp s7))
           (equal (b-store-resultp (list s0 s1 s2 s3) (list s4 s5 s6 s7))
                  (store-resultp (list s0 s1 s2 s3) (list s4 s5 s6 s7))))
  :hints (("Goal" :in-theory (enable b-store-resultp
                                     store-resultp-mux
                                     store-resultp
                                     c-flag v-flag n-flag z-flag))))

(defthm b-store-resultp=store-resultp
  (implies (and (bvp store-cc) (equal (len store-cc) 4)
                (bvp flags) (equal (len flags) 4))
           (equal (b-store-resultp store-cc flags)
                  (store-resultp store-cc flags)))
  :hints (("Goal"
           :use ((:instance equal-len-4-as-collected-nth
                            (l store-cc))
                 (:instance equal-len-4-as-collected-nth
                            (l flags))
                 (:instance b-store-resultp=store-resultp$help
                            (s0 (car store-cc))
                            (s1 (cadr store-cc))
                            (s2 (caddr store-cc))
                            (s3 (cadddr store-cc))
                            (s4 (car flags))
                            (s5 (cadr flags))
                            (s6 (caddr flags))
                            (s7 (cadddr flags))))
           :in-theory (enable bvp))))

(defthmd b-store-resultp$value
  (implies (and (b-store-resultp& netlist)
                (true-listp store-cc) (equal (len store-cc) 4)
                (true-listp store-cc) (equal (len flags) 4))
           (equal (se 'b-store-resultp
                      (append store-cc flags)
                      sts netlist)
                  (list (f$b-store-resultp store-cc flags))))
  :hints (("Goal"
           :in-theory (enable se-rules
                               b-store-resultp&
                               f$b-store-resultp
                               store-resultp-mux$value))))
