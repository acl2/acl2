; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file assumes that events in mem.lisp have been evaluated up to the point
; where this file is loaded (from mem.lisp) with include-raw.

(in-package "ACL2")

(defun special-address-list (mem)
  (declare (ignore mem))
  '(10 30 50))

(defun read-mem-special (addr mem)

; Return a special value based on addr, possibly with side effects.

  (declare (type (integer 0 *) addr))
  (declare (ignore mem))
  ;; We can do any sort of raw Lisp stuff here to return a value, presumably an
  ;; (unsigned-byte 8) since that's what we'd expect from mem.  But here I'll
  ;; keep it simple.
  (cw "~|NOTE: Calling read-mem-special on address ~x0.~|~%"
      addr)
  (mod (1+ addr) 256))

(defun write-mem-special (addr val mem)

; Cause a side effect based on addr.  Note that this function isn't intended to
; affect what is returned by write-mem -- it's only for side effect.

  (declare (type (integer 0 *) addr))
  (declare (ignore mem))
  (cw "~|NOTE: Calling write-mem-special on address ~x0.~|~%"
      addr))
