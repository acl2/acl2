; Tests of the prune machinery
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "prune")
(include-book "kestrel/utilities/assert-with-stobjs" :dir :system)

;; todo: eventually drop this
(defun prune-term-test-wrapper (term assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
  (declare (xargs :stobjs state :verify-guards nil))
  (mv-let (erp changep result state)
    (prune-term term assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
    (declare (ignore changep))
    (mv erp result state)))

(assert-equal-with-stobjs2 (prune-term-test-wrapper '(myif (equal x y) (myif (equal x y) v w) z)
                                                       nil
                                                       nil
                                                       nil
                                                       nil
                                                       nil
                                                       state)
                           '(myif (equal x y) v z)
                           :stobjs (state))

;; TODO: Simplify the (booland 't ...) below
(assert-equal-with-stobjs2 (prune-term-test-wrapper '(myif (equal x y) (booland (equal x y) z) w)
                                                       nil
                                                       nil
                                                       nil
                                                       nil
                                                       nil
                                                       state)
                           '(myif (equal x y) (booland 't z) w)
                           :stobjs (state))

(assert-equal-with-stobjs2 (prune-term-test-wrapper '(boolif 't x y)
                                                       nil
                                                       nil
                                                       nil
                                                       nil
                                                       nil
                                                       state)
                           '(bool-fix$inline x)
                           :stobjs (state))

(assert-equal-with-stobjs2 (prune-term-test-wrapper '(boolif 'nil x y)
                                                       nil
                                                       nil
                                                       nil
                                                       nil
                                                       nil
                                                       state)
                           '(bool-fix$inline y)
                           :stobjs (state))

;; todo:
;; (assert-equal-with-stobjs2 (prune-term-test-wrapper '(boolif '3 x y)
;;                                                        nil
;;                                                        nil
;;                                                        nil
;;                                                        nil
;;                                                        state)
;;                            '(bool-fix$inline x)
;;                            :stobjs (state))
