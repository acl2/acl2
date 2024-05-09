; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file assumes that events in mem.lisp have been evaluated up to the point
; where this file is loaded with include-raw.

(in-package "ACL2")

(defg *special-address-list* '(10 30 50))

; We won't use the following two, but we could avoid having to look up the old
; definitions if we use them with funcall.  I can explain further if asked.
(defvar *old-ari* (symbol-function 'ari))
(defvar *old-update-ari* (symbol-function 'update-ari))

; Implementation note:
; Here are the original raw Lisp definitions, obtained by evaluating
; (trace$ defstobj-raw-defs)
; before evaluating the defstobj for in mem.lisp

#|
(defun ari (i mem)
  (declare (type (and fixnum (integer 0 *)) i))
  (the$ (unsigned-byte 8)
        (aref (the (simple-array (unsigned-byte 8) (*))
                   mem)
              (the (and fixnum (integer 0 *)) i))))

(defun update-ari (i v mem)
  (declare (type (and fixnum (integer 0 *)) i)
           (type (unsigned-byte 8) v))
  (progn (memoize-flush nil)
         (setf (aref (the (simple-array (unsigned-byte 8) (*))
                          mem)
                     (the (and fixnum (integer 0 *)) i))
               (the$ (unsigned-byte 8) v))
         mem))
|#

; Now we modify the definitions above to account for special behavior for
; addresses in the list *special-address-list*.

(defun ari (i mem)
  (declare (type (and fixnum (integer 0 *)) i))
  (cond
   ((member i *special-address-list*)
    (cw "~|NOTE: Returning result for read at special address ~x0.~|~%"
        i)
    (the$ (unsigned-byte 8)
          (mod (1+ i) 256)))
   (t (the$ (unsigned-byte 8)
            (aref (the (simple-array (unsigned-byte 8) (*))
                       mem)
                  (the (and fixnum (integer 0 *)) i))))))

(defun update-ari (i v mem)

; Cause a side effect based on i.  Note that this function isn't intended to
; affect what is returned by write-mem -- it's only for side effect.

  (declare (type (and fixnum (integer 0 *)) i)
           (type (unsigned-byte 8) v))
  (when (member i *special-address-list*)
    (cw "~|NOTE: Calling update-ari on special address ~x0.~|~%"
        i))
  (progn (memoize-flush nil)
         (setf (aref (the (simple-array (unsigned-byte 8) (*))
                          mem)
                     (the (and fixnum (integer 0 *)) i))
               (the$ (unsigned-byte 8) v))
         mem))
