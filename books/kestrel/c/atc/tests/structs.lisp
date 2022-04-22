; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib) (:open-output-channel!)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some examples to test code generation for structuress.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some shallowly embedded structure types, also to test DEFSTRUCT.

(c::defstruct |point2D|
              (|x| c::sint)
              (|y| c::sint))

(c::defstruct |point3D|
              (|x| c::slong)
              (|y| c::slong)
              (|z| c::slong))

(c::defstruct |integers|
              (|uchar| c::uchar)
              (|schar| c::schar)
              (|ushort| c::ushort)
              (|sshort| c::sshort)
              (|uint| c::uint)
              (|sint| c::sint)
              (|ulong| c::ulong)
              (|slong| c::slong)
              (|ullong| c::ullong)
              (|sllong| c::sllong))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read members from structures.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |read_x_from_point2D| (|s|)
  (declare (xargs :guard (struct-|point2D|-p |s|)))
  (struct-|point2D|-read-|x| |s|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |read_y_from_point2D| (|s|)
  (declare (xargs :guard (struct-|point2D|-p |s|)))
  (struct-|point2D|-read-|y| |s|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |allpos| (|point|)
  (declare (xargs :guard (struct-|point3D|-p |point|)))
  (c::sint-from-boolean
   (and (c::boolean-from-sint
         (c::gt-slong-slong (struct-|point3D|-read-|x| |point|)
                            (c::slong-dec-const 0)))
        (c::boolean-from-sint
         (c::gt-slong-slong (struct-|point3D|-read-|y| |point|)
                            (c::slong-dec-const 0)))
        (c::boolean-from-sint
         (c::gt-slong-slong (struct-|point3D|-read-|z| |point|)
                            (c::slong-dec-const 0))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Return structures unchanged.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return1| (|s|)
  (declare (xargs :guard (struct-|point2D|-p |s|)))
  |s|)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return2| (|s| |t|)
  (declare (xargs :guard (and (struct-|point2D|-p |s|)
                              (struct-|point3D|-p |t|))))
  (declare (ignore |t|))
  |s|)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return3| (|s| |t|)
  (declare (xargs :guard (and (struct-|point2D|-p |s|)
                              (struct-|point3D|-p |t|))))
  (mv |t| |s|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Write members to structures.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |write_x_to_point2D| (|point|)
  (declare (xargs :guard (struct-|point2D|-p |point|)))
  (let ((|point| (struct-|point2D|-write-|x| (c::sint-dec-const 99) |point|)))
    |point|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |write_y_to_point2D| (|point|)
  (declare (xargs :guard (struct-|point2D|-p |point|)))
  (let ((|point| (struct-|point2D|-write-|y| (c::sint-dec-const 99) |point|)))
    |point|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |point2D|
        |point3D|
        |integers|
        |read_x_from_point2D|
        |read_y_from_point2D|
        |allpos|
        |return1|
        |return2|
        |return3|
        |write_x_to_point2D|
        |write_y_to_point2D|
        :output-file "structs.c")
