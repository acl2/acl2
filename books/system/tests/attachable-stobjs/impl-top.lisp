; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Defabsstobj Example involving attachments: Generic stobj with attachment

(in-package "ACL2")

(include-book "impl")

; The event just above defines an implementation stobj and includes an
; attach-stobj event to attach that implementation to a future generic stobj,
; st.  Before we introduce st and play with it, let's check that some erroneous
; attempts to introduce st fail (as they should).

; Here we set up for the introduction of st.
(include-book "gen-support")

(encapsulate
  ()
   
  (local (include-book "std/testing/must-fail" :dir :system))

  (must-fail ; Order of exports is switched.
   (defabsstobj st
     :exports ((update :exec update-mem$ci)
               (lookup :exec mem$ci)
               misc update-misc)
     :attachable t))

  (must-fail
   (defabsstobj st ; Misc field is missing.
     :exports ((lookup :exec mem$ci)
               (update :exec update-mem$ci)
               update-misc)
     :attachable t)))

; The :exec field for misc in st and for corresponding misc2 in st2 is misc$c+,
; which causes an error.  But the :exec field for corresponding misc{impl} in
; st{impl} does not cause an error, so st{impl} is what we want to be attached
; to st.  Just as an extra bit of testing, we do that attachment indirectly:
; st{impl} is attached to st2 (where export misc2 of st2 causes an error when
; st2 has no attachment), which is attached to st.

(attach-stobj st2 st{impl})
(include-book "impl2")

(attach-stobj st st2)
(include-book "gen")

; The following fails if ACL2 is careless by loading the original compiled code
; for the generic stobj, which doesn't account for the attached implementation.
; In an incomplete implementation, we overcame this by executing
; (set-compiler-enabled nil state)
; before including this book without any further forms, and then evaluating
; (value-triple (misc st)).

(defun f1 (st)
  (declare (xargs :stobjs st))
  (misc st))

(value-triple (f1 st))

(defun g0 (st)
  (declare (xargs :stobjs st
                  :guard (eql (misc st) 0)
                  :verify-guards nil))
  (lookup 0 st))

(value-triple (g0 st))

(verify-guards g0)

(value-triple (g0 st))

(defun g0a (st)
  (declare (xargs :stobjs st
                  :guard (eql (misc st) 0)))
  (lookup 0 st))

(value-triple (g0a st))

(defun g1 (st)
  (declare (xargs :stobjs st
                  :guard (eql (f1 st) 0)
                  :verify-guards nil))
  (lookup 0 st))

(value-triple (g1 st))

(verify-guards g1)

(value-triple (g1 st))

(defun g1a (st)
  (declare (xargs :stobjs st
                  :guard (eql (f1 st) 0)))
  (lookup 0 st))

(value-triple (g1a st))

(defun-inline f2 (st)
  (declare (xargs :stobjs st))
  (misc st))

(defun g2 (st)
  (declare (xargs :stobjs st))
  (f2 st))

(value-triple (g2 st))

(defun g2a (st)
  (declare (xargs :stobjs st
                  :guard (eql (f2 st) 0)))
  (lookup 0 st))

(value-triple (g2a st))

(defun g3 (st)
  (declare (xargs :stobjs st))
  (g2 st))

(value-triple (g3 st))
