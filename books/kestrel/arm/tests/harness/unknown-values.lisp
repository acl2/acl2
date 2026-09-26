; Executing ARM32 instructions whose results include UNKNOWN values
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

;; The model represents an UNKNOWN result (see pseudocode.lisp) as a call of
;; unknown-bits, a constrained function with no executable body.  This book
;; attaches an executable function to unknown-bits with defattach.  An
;; attachment affects evaluation only: the logical model and its theorems are
;; unchanged, and only books that include this one see the attachment.

;; The attached function returns a recognizable marker, #xDEADBEEF chopped to
;; the width, XORed with a "filling" stored in the oracle field of the state (a
;; field the model does not currently use).  The filling is needed because one
;; run cannot tell whether a narrow field depends on an UNKNOWN: a one-bit
;; UNKNOWN, the common case (the multiply flags on ARMv4), is 0 or 1 whatever
;; its source.  The harness therefore runs each vector under the fillings 0 and
;; #xFFFFFFFF, whose UNKNOWN values differ in every bit, and reports a field
;; whose value changes between the two runs as depending on an UNKNOWN.

;; Note that we may replace this mechanism by one that provides symbolic
;; oracle values for UNKNOWN results -- when that happens, this book
;; will go away and the harness will fill the oracle directly.

(include-book "../../pseudocode") ; for unknown-bits

;; Makes FILLING the filling for unknown-bits-marker.
(defun set-unknown-filling (filling arm)
  (declare (xargs :guard (unsigned-byte-p 32 filling)
                  :stobjs arm))
  (update-oracle (list filling) arm))

;; Returns the N-bit marker XORed with the filling.
(defun unknown-bits-marker (n val arm)
  (declare (xargs :guard t :stobjs arm)
           (ignore val))
  (let* ((oracle (oracle arm))
         (filling (if (consp oracle) (ifix (car oracle)) 0)))
    (bvchop (nfix n) (logxor #xDEADBEEF filling))))

(defattach unknown-bits unknown-bits-marker)
