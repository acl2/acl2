;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

(in-package "ADE")

(include-book "adder")
(include-book "../vector-module")

(include-book "ihs/basic-definitions" :dir :system)

;; ======================================================================

;; DE Module Generator of RIPPLE-SUB

(module-generator
 ripple-sub* (n)
 (si 'ripple-sub n)
 (append (sis 'a 0 n)
         (sis 'b 0 n))
 (sis 's 0 (1+ n))
 ()
 (list
  (list 'g0
        (sis 'b~ 0 n)
        (si 'v-not n)
        (sis 'b 0 n))

  '(g1 (high) vdd ())

  (list 'sub
        (sis 's 0 (1+ n))
        (si 'ripple-add n)
        (cons 'high (append (sis 'a 0 n) (sis 'b~ 0 n)))))

 (declare (xargs :guard (natp n))))

;; DE netlist generator.  A generated netlist will contain an instance of
;; RIPPLE-SUB.

(defund ripple-sub$netlist (n)
  (declare (xargs :guard (natp n)))
  (cons (ripple-sub* n)
        (union$ (v-not$netlist n)
                (ripple-add$netlist n)
                :test 'equal)))

;; Recognizer for RIPPLE-SUB

(defund ripple-sub& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (b* ((subnetlist (delete-to-eq (si 'ripple-sub n) netlist)))
    (and (equal (assoc (si 'ripple-sub n) netlist)
                (ripple-sub* n))
         (v-not& subnetlist n)
         (ripple-add& subnetlist n))))

;; Sanity check

(local
 (defthmd check-ripple-sub$netlist-64
   (and (net-syntax-okp (ripple-sub$netlist 64))
        (net-arity-okp (ripple-sub$netlist 64))
        (ripple-sub& (ripple-sub$netlist 64) 64))))

;; The value lemma for RIPPLE-SUB

(defthm ripple-sub$value
  (implies (and (ripple-sub& netlist n)
                (natp n)
                (true-listp a)
                (true-listp b)
                (equal n (len a))
                (equal n (len b)))
           (equal (se (si 'ripple-sub n) (append a b) st netlist)
                  (fv-adder t a (fv-not b))))
  :hints (("Goal"
           :expand (:free (inputs n)
                          (se (si 'ripple-sub n) inputs st netlist))
           :in-theory (e/d* (de-rules
                             ripple-sub&
                             ripple-sub*$destructure)
                            (de-module-disabled-rules)))))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (local
   (defthm ripple-add-2-comp-sub-aux-1
     (implies (and (posp n)
                   (rationalp a)
                   (rationalp b))
              (equal (logext n
                             (+ a (- (expt 2 n) b)))
                     (logext n
                             (- a b))))))

  (local
   (set-default-hints
    '((nonlinearp-default-hint stable-under-simplificationp
                               hist pspv))))

  (local
   (defthm ripple-add-2-comp-sub-aux-2
     (implies (bvp x)
              (equal (v-to-nat (v-not x))
                     (- (1- (expt 2 (len x)))
                        (v-to-nat x))))
     :hints (("Goal" :in-theory (enable bvp v-to-nat v-not)))))

  (defthm v-adder-sub-works
    (implies (bv2p a b)
             (equal (v-to-nat (v-adder c a (v-not b)))
                    (+ (if c 0 -1)
                       (expt 2 (len a))
                       (- (v-to-nat a)
                          (v-to-nat b))))))

  (local
   (defthm v-to-nat-of-repeat-nil-is-zero
     (equal (v-to-nat (repeat n nil)) 0)
     :hints (("Goal" :in-theory (enable v-to-nat repeat)))))

  (local
   (defthm v-to-nat-of-take
     (implies (<= 0 n)
              (equal (v-to-nat (take n l))
                     (- (v-to-nat l)
                        (* (expt 2 n) (v-to-nat (nthcdr n l))))))
     :hints (("Goal" :in-theory (enable bvp v-to-nat)))))

  (local
   (defun nthcdr-v-adder-sub-induct (n c a b)
     (if (zp n)
         (list c a b)
       (nthcdr-v-adder-sub-induct (1- n)
                                  (b-or3 (b-and (car a) (not (car b)))
                                         (b-and (car a) c)
                                         (b-and (not (car b)) c))
                                  (cdr a)
                                  (cdr b)))))

  (local
   (defthm nthcdr-v-adder-sub-1
     (implies (and (natp n)
                   (booleanp c)
                   (equal n (len a))
                   (equal (v-to-nat b) (v-to-nat a))
                   (bv2p a b))
              (equal (nthcdr n (v-adder c a (v-not b)))
                     (list c)))
     :hints (("Goal"
              :in-theory (enable bvp v-adder v-not)))))

  (local
   (defthm nthcdr-v-adder-sub-2
     (implies (and (natp n)
                   (booleanp c)
                   (equal n (len a))
                   (< (v-to-nat b) (v-to-nat a))
                   (bv2p a b))
              (equal (nthcdr n (v-adder c a (v-not b)))
                     (list t)))
     :hints (("Goal"
              :induct (nthcdr-v-adder-sub-induct n c a b)
              :in-theory (enable bvp v-adder v-to-nat v-not)))))

  (defthm v-to-nat-of-take-of-v-adder-sub
    (implies (and (natp n)
                  (equal n (len a))
                  (<= (v-to-nat b) (v-to-nat a))
                  (bv2p a b))
             (equal (v-to-nat (v-adder-output t a (v-not b)))
                    (- (v-to-nat a)
                       (v-to-nat b))))
    :hints (("Goal"
             :in-theory (enable v-adder-output)
             :use (:instance nthcdr-v-adder-sub-2
                             (c t)))))

  (defthm ripple-add-2-comp-sub
    (implies (and (posp n)
                  (equal n (len a))
                  (bv2p a b))
             (equal (logext n (v-to-nat (v-adder t a (v-not b))))
                    (logext n (- (v-to-nat a) (v-to-nat b)))))
    :hints (("Goal"
             :in-theory (disable logext)
             :use (:instance ripple-add-2-comp-sub-aux-1
                             (a (v-to-nat a))
                             (b (v-to-nat b))))))
  )

(defthm ripple-sub$value-correct
  (implies (and (ripple-sub& netlist n)
                (posp n) ;; n must be positive.
                (equal n (len a))
                (bv2p a b))
           (equal (logext n
                          (v-to-nat
                           (se (si 'ripple-sub n)
                               (append a b)
                               st
                               netlist)))
                  (logext n (- (v-to-nat a) (v-to-nat b)))))
  :hints (("Goal" :in-theory (e/d (ripple-sub$value)
                                  (logext
                                   v-adder-works
                                   v-adder-sub-works)))))




