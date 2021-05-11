; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;; Error in mom-swap-fields fixed Spring 2021:
#||
ACL2 Error in ACL2-INTERFACE:  Implementation error: unexpected form
of stobj-let encountered by oneify!.
||#

(in-package "ACL2")

(defstobj kid1 fld1)

(defstobj kid2 fld2)

(defstobj kid2a fld2a :congruent-to kid2)
(defstobj kid2b fld2b :congruent-to kid2)
(defstobj kid2c fld2c :congruent-to kid2)

(defstobj mom
  (kid1-field :type kid1)
  (ar1 :type (array kid2 (5)))
  (ar2 :type (array kid2 (5)))
  last-op)

; We need some lemmas in order to admit mom-swap-fields.

(defthm ar1p-forward-to-true-list-listp
  (implies (ar1p x)
           (true-list-listp x))
  :rule-classes :forward-chaining)

(defthm ar2p-forward-to-true-list-listp
  (implies (ar2p x)
           (true-list-listp x))
  :rule-classes :forward-chaining)

(defthm true-listp-nth
  (implies (true-list-listp x)
           (true-listp (nth n x)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth n x)))))

(defthm update-mom-guard-lemma-1
  (and (implies (ar1p kid2-ar)
                (equal (cdr (nth index kid2-ar))
                       nil))
       (implies (ar2p kid2-ar)
                (equal (cdr (nth index kid2-ar))
                       nil))))

(defthm update-mom-guard-lemma-2
  (and (implies (and (ar1p kid2-ar)
                     (natp index)
                     (< index (len kid2-ar)))
                (consp (nth index kid2-ar)))
       (implies (and (ar2p kid2-ar)
                     (natp index)
                     (< index (len kid2-ar)))
                (consp (nth index kid2-ar)))))

; Error in version 8.3 (perhaps earlier) into Spring 2021.
(defun mom-swap-fields (i1 i2 i3 i4 mom)
  (declare (xargs :stobjs mom
                  :guard (and (nat-listp (list i1 i2 i3 i4))
                              (< i1 (ar1-length mom))
                              (< i2 (ar1-length mom))
                              (< i3 (ar2-length mom))
                              (< i4 (ar2-length mom))
			      (no-duplicatesp (list i1 i2))
                              (no-duplicatesp (list i3 i4)))))
  (stobj-let
   ((kid1 (kid1-field mom))
    (kid2 (ar1i i1 mom))
    (kid2a (ar1i i2 mom))
    (kid2b (ar2i i3 mom))
    (kid2c (ar2i i4 mom)))
   (kid1 kid2 kid2a kid2b kid2c)
   (let* ((val1 (fld1 kid1))
          (val2 (fld2 kid2))
          (kid1 (update-fld1 val2 kid1))
          (kid2 (update-fld2 val1 kid2)))
     (mv kid1 kid2 kid2a kid2b kid2c))
   (update-last-op 'swap mom)))

(defun mom-swap-fields-program (i1 i2 i3 i4 mom)
  (declare (xargs :stobjs mom
                  :mode :program))
  (mom-swap-fields i1 i2 i3 i4 mom))

(defun mom-get-fields (i1 i2 mom)
  (declare (xargs :stobjs mom
                  :guard (and (nat-listp (list i1 i2))
                              (< i1 (ar1-length mom))
                              (< i2 (ar1-length mom))
			      (no-duplicatesp (list i1 i2)))))
  (stobj-let
   ((kid1 (kid1-field mom))
    (kid2 (ar1i i1 mom))
    (kid2a (ar1i i2 mom)))
   (val1 val2 val3)
   (let* ((val1 (fld1 kid1))
          (val2 (fld2 kid2))
          (val3 (fld2a kid2a)))
     (mv val1 val2 val3))
   (mv val3 val2 val1)))

(defun mom-get-fields-program (i1 i2 mom)
  (declare (xargs :stobjs mom
                  :mode :program))
  (mom-get-fields i1 i2 mom))

;(untranslate (body 'MOM-SWAP-FIELDS nil (w state)) nil (w state))

;;; Some examples for checking error messages.
#||

; ok
(mom-swap-fields 1 2 3 4 mom)

; guard violation error:
(mom-swap-fields 1 1 3 4 mom)

; guard violation error (was a hard error at one point):
(with-guard-checking :none (mom-swap-fields 1 1 3 4 mom))

; guard violation error:
(let ((x 4)) (mom-swap-fields 1 2 4 x mom))

; guard violation error after invariant-risk warning
(mom-swap-fields-program 1 1 3 4 mom)

; ok
(mom-get-fields 1 2 mom)

; guard violation error (was a hard error at one point):
(mom-get-fields 1 1 mom)

; guard violation error (was a hard error at one point):
(with-guard-checking :none (mom-get-fields 1 1 mom))

; no error
(mom-get-fields-program 1 1 mom)

(set-check-invariant-risk nil)
; No error!
(mom-swap-fields-program 1 1 3 4 mom)

;;; Guard-debug is helpful:
(ubt 'mom-swap-fields)
(defun mom-swap-fields (i1 i2 i3 i4 mom)
  (declare (ignore i2))
  (declare (xargs :stobjs mom :guard-debug t
                  :guard (and (nat-listp (list i1 i2 i3 i4))
                              (< i1 (ar1-length mom))
                              (< i2 (ar1-length mom))
                              (< i3 (ar2-length mom))
                              (< i4 (ar2-length mom))
			      (no-duplicatesp (list i1 i2))
                              (no-duplicatesp (list i3 i4)))))
  (stobj-let
   ((kid1 (kid1-field mom))
    (kid2 (ar1i i1 mom))
    (kid2a (ar1i 1 mom))
    (kid2b (ar2i i3 mom))
    (kid2c (ar2i i4 mom)))
   (kid1 kid2 kid2a kid2b kid2c)
   (let* ((val1 (fld1 kid1))
          (val2 (fld2 kid2))
          (kid1 (update-fld1 val2 kid1))
          (kid2 (update-fld2 val1 kid2)))
     (mv kid1 kid2 kid2a kid2b kid2c))
   (update-last-op 'swap mom)))

||#
