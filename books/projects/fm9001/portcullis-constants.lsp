;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

;; ======================================================================

;; PLUS

(defun plus (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (+ x y))

(defthm natp-plus
  (implies (and (natp x) (natp y))
           (natp (plus x y)))
  :rule-classes :type-prescription)

(in-theory (disable plus))

;; ADD1

(defun add1 (x)
  (declare (xargs :guard (acl2-numberp x)))
  (plus 1 x))

(defthm natp-add1
  (implies (natp x)
           (natp (add1 x)))
  :rule-classes :type-prescription)

;; Timing contants

;; T_initial-state->final-state is an expression for the amount of time
;; necessary to execute the indicated section of the state diagram.
;; CT_initial-state->final-state is an expression for the memory delay oracle
;; at the end of the sequence.

(defconst *t_fetch0->fetch0*
  1)

(defconst *ct_fetch0->fetch0*
  'CLOCK)

(defconst *w_fetch1->decode*
  '(NFIX (CAR CLOCK)))

(defconst *ct_fetch1->decode*
  '(CDR CLOCK))

(defconst *t_rega->rega*
  1)

(defconst *ct_rega->rega*
  'CLOCK)

(defconst *t_regb->update*
  2)

(defconst *ct_regb->update*
  'CLOCK)

(defconst *t_update->update*
  1)

(defconst *ct_update->update*
  'CLOCK)

(defconst *w_reada0->reada3*
  '(NFIX (CAR CLOCK)))

(defconst *ct_reada0->reada3*
  '(CDR CLOCK))

(defconst *w_readb0->readb3*
  '(NFIX (CAR CLOCK)))

(defconst *ct_readb0->readb3*
  '(CDR CLOCK))

(defconst *w_write0->write3*
  '(NFIX (CAR CLOCK)))

(defconst *ct_write0->write3*
  '(CDR CLOCK))

(defconst *t_sefa0->sefa1*
  2)

(defconst *ct_sefa0->sefa1*
  'CLOCK)

(defconst *t_sefb0->sefb1*
  2)

(defconst *ct_sefb0->sefb1*
  'CLOCK)

(defconst *t_sefb1->sefb1*
  1)

(defconst *ct_sefb1->sefb1*
  'CLOCK)

(defconst *t_fetch1->decode*
  '(add1 (add1 (plus #.*w_fetch1->decode* 2))))

(defconst *t_reada0->reada3*
  '(add1 (add1 (add1 (plus #.*w_reada0->reada3* 1)))))

(defconst *t_readb0->readb3*
  '(add1 (add1 (add1 (plus #.*w_readb0->readb3* 1)))))

(defconst *t_write0->write3*
  '(add1 (add1 (add1 (plus #.*w_write0->write3* 1)))))

