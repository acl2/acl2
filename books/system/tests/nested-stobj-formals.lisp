; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here is an example extracted from one sent by Sol Swords, showing an issue
; fixed after Version 7.4 for stobj-let and guard proofs.  Before the fix, the
; guard proof failed; afterwards, it succeeds.  The problem was that for a
; parent stobj, child stobj accesses were represented by the formal, V, rather
; than by the child stobj name, which apparently defeated the "stobj-opt"
; optimization for guard proofs.

(in-package "ACL2")

(defstobj child (child-field :type (array integer (0))
                             :initially 0 :resizable t))

(defstobj parent (parent-arr :type child))

(defun parent-resize-array (size parent)
  (declare (xargs :stobjs parent :guard (natp size)
                  :guard-hints (("goal" :do-not-induct t))))
  (stobj-let ((child (parent-arr parent)))
             (child)
             (resize-child-field size child)
             parent))

