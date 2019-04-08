;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2018

(in-package "ADE")

(include-book "control-modules")

;; ======================================================================

;; Definitions of the control states for the control logic

(defconst *control-states*
  '((v00000  . *v00000*)
    (v00001  . *v00001*)
    (v00010  . *v00010*)
    (v00011  . *v00011*)

    (v00100  . *v00100*)
    (v00101  . *v00101*)
    (v00110  . *v00110*)
    (v00111  . *v00111*)

    (v01000  . *v01000*)
    (v01001  . *v01001*)
    (v01010  . *v01010*)
    (v01011  . *v01011*)

    (v01100  . *v01100*)
    (v01101  . *v01101*)
    (v01110  . *v01110*)
    (v01111  . *v01111*)

    (v10000  . *v10000*)
    (v10001  . *v10001*)
    (v10010  . *v10010*)
    (v10011  . *v10011*)

    (v10100  . *v10100*)
    (v10101  . *v10101*)
    (v10110  . *v10110*)
    (v10111  . *v10111*)

    (v11000  . *v11000*)
    (v11001  . *v11001*)
    (v11010  . *v11010*)
    (v11011  . *v11011*)

    (v11100  . *v11100*)
    (v11101  . *v11101*)
    (v11110  . *v11110*)
    (v11111  . *v11111*)))

(defmacro define-control-states-events ()
  `(progn
     ,@(define-control-states *control-states*)

     (deftheory vector-states
       ',(add-prefix-to-state-names "V_" *control-states*))

     (deftheory natural-states
       ',(add-prefix-to-state-names "N_" *control-states*))

     (in-theory (disable vector-states natural-states))))

(define-control-states-events)

;; ======================================================================

;; State Transition Table

(defconst *state-table*
  '((v00000 v00001)
    (v00001 v00010)
    (v00010 v00011)
    (v00011 v00100)

    (v00100 v00101)
    (v00101 v00110)
    (v00110 v00111)
    (v00111 v01000)

    (v01000 v01001)
    (v01001 v01010)
    (v01010 v01011)
    (v01011 v01100)

    (v01100 v01101)
    (v01101 v01110)
    (v01110 v01111)
    (v01111 v10000)

    (v10000 v10001)
    (v10001 v10010)
    (v10010 v10011)
    (v10011 v10100)

    (v10100 v10101)
    (v10101 v10110)
    (v10110 v10111)
    (v10111 v11000)

    (v11000 v11001)
    (v11001 v11010)
    (v11010 v11011)
    (v11011 v11100)

    (v11100 v11101)
    (v11101 v11110)
    (v11110 v00000)
    (v11111 v00000)))

(defun define-next-state-1 (state-table)
  (b* ((state-names (strip-cars state-table))
       (next-st (add-prefix-to-names "NEXT-" state-names))
       (unwinded-next-st (unwind-next-st state-table))
       (spec (compute-next-st state-names unwinded-next-st)))
    `((defun next-state (decoded-state)
        (declare (xargs :guard (true-listp decoded-state)))
        (b* ,(append (bind-values state-names 0 'decoded-state)
                     spec)
          (list ,@next-st)))

      (defun f$next-state (decoded-state)
        (declare (xargs :guard (true-listp decoded-state)))
        (b* ,(append (bind-values state-names 0 'decoded-state)
                     (b-to-f spec))
          (list ,@next-st)))

      (defthm f$next-state=next-state
        (implies (bvp decoded-state)
                 (equal (f$next-state decoded-state)
                        (next-state decoded-state)))
        :hints (("Goal" :in-theory (e/d (nth-of-bv-is-boolean)
                                        (b-gates)))))

      (in-theory (disable f$next-state next-state))

      (defun next-state* ()
        (declare (xargs :guard t))
        (list
         'next-state
         (sis 's 0 32)
         ',next-st
         ()
         (append (list ,@(wire-occs state-names 's 0))
                 ',(fn-to-module-body 0 (flatten-binding 'x 0 spec t)))))

      (defun next-state$netlist ()
        (declare (xargs :guard t))
        (list (next-state*)))

      (defthmd next-state$netlist-okp
        (and (net-syntax-okp (next-state$netlist))
             (net-arity-okp (next-state$netlist))))

      (defund next-state& (netlist)
        (declare (xargs :guard (alistp netlist)))
        (equal (assoc 'next-state netlist)
               (next-state*)))

      )))

;; The NEXT-STATE logic is synthesized from the *STATE-TABLE*.

(defmacro define-next-state-events ()
  `(progn
     ,@(define-next-state-1 *state-table*)

     (defthm bvp-next-state
       (implies (bvp decoded-state)
                (bvp (next-state decoded-state)))
       :hints (("Goal" :in-theory (enable bvp next-state)))
       :rule-classes (:rewrite :type-prescription))

     (defthm len-next-state
       (equal (len (next-state decoded-state))
              32)
       :hints (("Goal" :in-theory (enable next-state))))

     (defthm len-f$next-state
       (equal (len (f$next-state decoded-state))
              32)
       :hints (("Goal" :in-theory (enable f$next-state))))

     (defthm next-state$value
       (implies (and (next-state& netlist)
                     (true-listp decoded-state)
                     (equal (len decoded-state) 32))
                (equal (se 'next-state
                           decoded-state
                           st
                           netlist)
                       (f$next-state decoded-state)))
       :hints (("Goal"
                :expand (se 'next-state
                            decoded-state
                            st
                            netlist)
                :in-theory (e/d (de-rules
                                 next-state&
                                 f$next-state)
                                ((next-state*)
                                 de-module-disabled-rules)))))
     ))

(define-next-state-events)

;; ======================================================================

(defun next-cntl-state (st)
  (declare (xargs :guard (true-listp st)))
  (encode-32 (nth 0 (next-state (decode-5 st)))
             (nth 1 (next-state (decode-5 st)))
             (nth 2 (next-state (decode-5 st)))
             (nth 3 (next-state (decode-5 st)))
             (nth 4 (next-state (decode-5 st)))
             (nth 5 (next-state (decode-5 st)))
             (nth 6 (next-state (decode-5 st)))
             (nth 7 (next-state (decode-5 st)))
             (nth 8 (next-state (decode-5 st)))
             (nth 9 (next-state (decode-5 st)))
             (nth 10 (next-state (decode-5 st)))
             (nth 11 (next-state (decode-5 st)))
             (nth 12 (next-state (decode-5 st)))
             (nth 13 (next-state (decode-5 st)))
             (nth 14 (next-state (decode-5 st)))
             (nth 15 (next-state (decode-5 st)))
             (nth 16 (next-state (decode-5 st)))
             (nth 17 (next-state (decode-5 st)))
             (nth 18 (next-state (decode-5 st)))
             (nth 19 (next-state (decode-5 st)))
             (nth 20 (next-state (decode-5 st)))
             (nth 21 (next-state (decode-5 st)))
             (nth 22 (next-state (decode-5 st)))
             (nth 23 (next-state (decode-5 st)))
             (nth 24 (next-state (decode-5 st)))
             (nth 25 (next-state (decode-5 st)))
             (nth 26 (next-state (decode-5 st)))
             (nth 27 (next-state (decode-5 st)))
             (nth 28 (next-state (decode-5 st)))
             (nth 29 (next-state (decode-5 st)))
             (nth 30 (next-state (decode-5 st)))
             (nth 31 (next-state (decode-5 st)))))

(defthm bvp-next-cntl-state
  (bvp (next-cntl-state st))
  :rule-classes (:rewrite :type-prescription))

(defthm len-next-cntl-state
  (equal (len (next-cntl-state st))
         5))

(defthm v-to-nat-of-next-cntl-state
 (implies (< (v-to-nat cntl) 30)
          (equal (v-to-nat (next-cntl-state cntl))
                 (1+ (v-to-nat cntl))))
 :hints (("Goal" :in-theory (enable v-to-nat
                                    next-state
                                    encode-32
                                    decode-5))))

(in-theory (disable next-cntl-state))

(defun f$next-cntl-state (st)
  (declare (xargs :guard (true-listp st)))
  (f$encode-32 (nth 0 (f$next-state (f$decode-5 st)))
               (nth 1 (f$next-state (f$decode-5 st)))
               (nth 2 (f$next-state (f$decode-5 st)))
               (nth 3 (f$next-state (f$decode-5 st)))
               (nth 4 (f$next-state (f$decode-5 st)))
               (nth 5 (f$next-state (f$decode-5 st)))
               (nth 6 (f$next-state (f$decode-5 st)))
               (nth 7 (f$next-state (f$decode-5 st)))
               (nth 8 (f$next-state (f$decode-5 st)))
               (nth 9 (f$next-state (f$decode-5 st)))
               (nth 10 (f$next-state (f$decode-5 st)))
               (nth 11 (f$next-state (f$decode-5 st)))
               (nth 12 (f$next-state (f$decode-5 st)))
               (nth 13 (f$next-state (f$decode-5 st)))
               (nth 14 (f$next-state (f$decode-5 st)))
               (nth 15 (f$next-state (f$decode-5 st)))
               (nth 16 (f$next-state (f$decode-5 st)))
               (nth 17 (f$next-state (f$decode-5 st)))
               (nth 18 (f$next-state (f$decode-5 st)))
               (nth 19 (f$next-state (f$decode-5 st)))
               (nth 20 (f$next-state (f$decode-5 st)))
               (nth 21 (f$next-state (f$decode-5 st)))
               (nth 22 (f$next-state (f$decode-5 st)))
               (nth 23 (f$next-state (f$decode-5 st)))
               (nth 24 (f$next-state (f$decode-5 st)))
               (nth 25 (f$next-state (f$decode-5 st)))
               (nth 26 (f$next-state (f$decode-5 st)))
               (nth 27 (f$next-state (f$decode-5 st)))
               (nth 28 (f$next-state (f$decode-5 st)))
               (nth 29 (f$next-state (f$decode-5 st)))
               (nth 30 (f$next-state (f$decode-5 st)))
               (nth 31 (f$next-state (f$decode-5 st)))))

(defthm len-f$next-cntl-state
  (equal (len (f$next-cntl-state st))
         5))

(defthm f$next-cntl-state=next-cntl-state
  (implies (bvp st)
           (equal (f$next-cntl-state st)
                  (next-cntl-state st)))
  :hints (("Goal" :in-theory (e/d (next-cntl-state
                                   f$next-state=next-state
                                   nth-of-bv-is-boolean)
                                  (nth)))))

(in-theory (disable f$next-cntl-state))

(module-generator
 next-cntl-state* ()
 'next-cntl-state
 (sis 'state 0 5)
 (list* 'false 'done- (sis 'next-state 0 5))
 ()
 (list
  '(low (false) vss ())
  (list 'g0 '(done-) 'b-nand4 (sis 'state 1 4))
  ;; The decoded state
  (list 'dstate
        (sis 'decoded-state 0 32)
        'decode-5
        (sis 'state 0 5))
  ;; The next decoded state
  (list 'ndstate
        (sis 'next-decoded-state 0 32)
        'next-state
        (sis 'decoded-state 0 32))
  ;; The next encoded state
  (list 'nstate
        (sis 'next-state 0 5)
        'encode-32
        (sis 'next-decoded-state 0 32)))

 (declare (xargs :guard t)))

(defun next-cntl-state$netlist ()
  (declare (xargs :guard t))
  (cons (next-cntl-state*)
        (union$ *decode-5*
                (next-state$netlist)
                *encode-32*
                :test 'equal)))

(defthmd next-cntl-state$netlist-okp
  (and (net-syntax-okp (next-cntl-state$netlist))
       (net-arity-okp (next-cntl-state$netlist))))

(defund next-cntl-state& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'next-cntl-state netlist)
              (next-cntl-state*))
       (b* ((netlist (delete-to-eq 'next-cntl-state netlist)))
         (and (decode-5& netlist)
              (next-state& netlist)
              (encode-32& netlist)))))

(defthm check-next-cntl-state$netlist
  (next-cntl-state& (next-cntl-state$netlist)))

(defun compute-done- (x)
  (declare (xargs :guard (true-listp x)))
  (f-nand4 (cadr x)
           (caddr x)
           (cadddr x)
           (car (cddddr x))))

(defthm booleanp-compute-done-
  (implies (bvp x)
           (booleanp (compute-done- x)))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes :type-prescription)

(defthm compute-done--lemma
 (implies (and (< (v-to-nat cntl) 30)
               (bvp cntl))
          (equal (compute-done- cntl) t))
 :hints (("Goal" :in-theory (enable v-to-nat bvp))))

(in-theory (disable compute-done-))

(defthm next-cntl-state$value
  (implies (and (next-cntl-state& netlist)
                (true-listp inputs)
                (equal (len inputs) 5))
           (equal (se 'next-cntl-state inputs st netlist)
                  (list* nil
                         (compute-done- inputs)
                         (f$next-cntl-state inputs))))
  :hints (("Goal"
           :expand (se 'next-cntl-state inputs st netlist)
           :in-theory (e/d (de-rules
                            next-cntl-state&
                            next-cntl-state*$destructure
                            f$next-cntl-state
                            compute-done-)
                           ((next-cntl-state*)
                            de-module-disabled-rules)))))

