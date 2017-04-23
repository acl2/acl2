; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See register-invariant-risk.lisp for discussion.  This supporting book
; defines a :program mode function that normally would incur invariant-risk
; (see :doc invariant-risk, but does not do so because its definition is in the
; scope of an execution of (set-register-invariant-risk nil).

; Portcullis command:
; (progn (defttag t) (set-register-invariant-risk nil) (defttag nil))

(in-package "ACL2")

(defstobj st (fld :type integer :initially 0))

(defun foo (n st)
  (declare (xargs :stobjs st :verify-guards nil))
  (update-fld n st))

(defun foo-program-wrapper (n st)
  (declare (xargs :stobjs st :mode :program))
  (if (integerp n) ; avoid invariant-risk possibility
      (foo n st)
    (prog2$ (cw "No change due to bad argument: ~x0"
                n)
            st)))
