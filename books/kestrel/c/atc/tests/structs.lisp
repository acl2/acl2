; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib) (:open-output-channel!)))

(include-book "defstruct") ; reuse these DEFSTRUCTs

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some examples to test code generation for structuress.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read members from structures.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |read_x_from_point2D_by_value| (|s|)
  (declare (xargs :guard (struct-|point2D|-p |s|)))
  (struct-|point2D|-read-|x| |s|))

;;;;;;;;;;;;;;;;;;;;

(defun |read_x_from_point2D_by_pointer| (|s|)
  (declare (xargs :guard (c::star (struct-|point2D|-p |s|))))
  (struct-|point2D|-read-|x| |s|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |read_y_from_point2D_by_value| (|s|)
  (declare (xargs :guard (struct-|point2D|-p |s|)))
  (struct-|point2D|-read-|y| |s|))

;;;;;;;;;;;;;;;;;;;;

(defun |read_y_from_point2D_by_pointer| (|s|)
  (declare (xargs :guard (c::star (struct-|point2D|-p |s|))))
  (struct-|point2D|-read-|y| |s|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |allpos_by_value| (|point|)
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

;;;;;;;;;;;;;;;;;;;;

(defun |allpos_by_pointer| (|point|)
  (declare (xargs :guard (c::star (struct-|point3D|-p |point|))))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |read_scalar_by_value| (|a|)
  (declare (xargs :guard (struct-|scalar_and_array|-p |a|)))
  (struct-|scalar_and_array|-read-|scalar| |a|))

;;;;;;;;;;;;;;;;;;;;

(defun |read_scalar_by_pointer| (|a|)
  (declare (xargs :guard (c::star (struct-|scalar_and_array|-p |a|))))
  (struct-|scalar_and_array|-read-|scalar| |a|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |read_aggreg_by_value| (|i| |a|)
  (declare
   (xargs
    :guard
    (and
     (c::sintp |i|)
     (struct-|scalar_and_array|-p |a|)
     (struct-|scalar_and_array|-|aggreg|-index-okp |i|))))
  (struct-|scalar_and_array|-read-|aggreg|-element |i| |a|))

;;;;;;;;;;;;;;;;;;;;

(defun |read_aggreg_by_pointer| (|i| |a|)
  (declare
   (xargs
    :guard
    (and
     (c::sintp |i|)
     (c::star (struct-|scalar_and_array|-p |a|))
     (c::star (struct-|scalar_and_array|-|aggreg|-index-okp |i|)))))
  (struct-|scalar_and_array|-read-|aggreg|-element |i| |a|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |read_flex_last| (|fl| |i|)
  (declare (xargs :guard (and (c::star (struct-|flex|-p |fl|))
                              (c::sintp |i|)
                              (struct-|flex|-|last|-index-okp |i| |fl|))))
  (struct-|flex|-read-|last|-element |i| |fl|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Return structures unchanged, by value and by pointer.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return1| (|s|)
  (declare (xargs :guard (struct-|point2D|-p |s|)))
  |s|)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return2| (|s|)
  (declare (xargs :guard (c::star (struct-|point2D|-p |s|))))
  |s|)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return3| (|s| |t|)
  (declare (xargs :guard (and (struct-|point2D|-p |s|)
                              (struct-|point3D|-p |t|))))
  (declare (ignore |t|))
  |s|)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return4| (|s| |t|)
  (declare (xargs :guard (and (struct-|point2D|-p |s|)
                              (struct-|point3D|-p |t|))))
  (declare (ignore |s|))
  |t|)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return5| (|s| |t|)
  (declare (xargs :guard (and (c::star (struct-|point2D|-p |s|))
                              (c::star (struct-|point3D|-p |t|)))))
  (declare (ignore |t|))
  |s|)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return6| (|s| |t|)
  (declare (xargs :guard (and (c::star (struct-|point2D|-p |s|))
                              (c::star (struct-|point3D|-p |t|)))))
  (declare (ignore |s|))
  |t|)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return7| (|s| |t|)
  (declare (xargs :guard (and (c::star (struct-|point2D|-p |s|))
                              (c::star (struct-|point3D|-p |t|)))))
  (mv |t| |s|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return8| (|s| |t|)
  (declare (xargs :guard (and (struct-|point2D|-p |s|)
                              (c::star (struct-|point3D|-p |t|)))))
  (declare (ignore |t|))
  |s|)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return9| (|s| |t|)
  (declare (xargs :guard (and (struct-|point2D|-p |s|)
                              (c::star (struct-|point3D|-p |t|)))))
  (declare (ignore |s|))
  |t|)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return10| (|s| |t|)
  (declare (xargs :guard (and (struct-|point2D|-p |s|)
                              (c::star (struct-|point3D|-p |t|)))))
  (mv |s| |t|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Write members to structures.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |write_x_to_point2D_by_value| (|point|)
  (declare (xargs :guard (struct-|point2D|-p |point|)))
  (let ((|point| (struct-|point2D|-write-|x| (c::sint-dec-const 99) |point|)))
    |point|))

;;;;;;;;;;;;;;;;;;;;

(defun |write_x_to_point2D_by_pointer| (|point|)
  (declare (xargs :guard (c::star (struct-|point2D|-p |point|))))
  (let ((|point| (struct-|point2D|-write-|x| (c::sint-dec-const 99) |point|)))
    |point|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |write_y_to_point2D_by_value| (|point|)
  (declare (xargs :guard (struct-|point2D|-p |point|)))
  (let ((|point| (struct-|point2D|-write-|y| (c::sint-dec-const 99) |point|)))
    |point|))

;;;;;;;;;;;;;;;;;;;;

(defun |write_y_to_point2D_by_pointer| (|point|)
  (declare (xargs :guard (c::star (struct-|point2D|-p |point|))))
  (let ((|point| (struct-|point2D|-write-|y| (c::sint-dec-const 99) |point|)))
    |point|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |write_scalar_by_value| (|v| |a|)
  (declare (xargs :guard (and (c::sintp |v|)
                              (struct-|scalar_and_array|-p |a|))))
  (let ((|a| (struct-|scalar_and_array|-write-|scalar| |v| |a|)))
    |a|))

;;;;;;;;;;;;;;;;;;;;

(defun |write_scalar_by_pointer| (|v| |a|)
  (declare (xargs :guard (and (c::sintp |v|)
                              (c::star (struct-|scalar_and_array|-p |a|)))))
  (let ((|a| (struct-|scalar_and_array|-write-|scalar| |v| |a|)))
    |a|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |write_aggreg_by_value| (|i| |v| |a|)
  (declare
   (xargs
    :guard
    (and
     (c::sintp |i|)
     (c::ucharp |v|)
     (struct-|scalar_and_array|-p |a|)
     (struct-|scalar_and_array|-|aggreg|-index-okp |i|))))
  (let ((|a| (struct-|scalar_and_array|-write-|aggreg|-element |i| |v| |a|)))
    |a|))

;;;;;;;;;;;;;;;;;;;;

(defun |write_aggreg_by_pointer| (|i| |v| |a|)
  (declare
   (xargs
    :guard
    (and
     (c::sintp |i|)
     (c::ucharp |v|)
     (c::star (struct-|scalar_and_array|-p |a|))
     (c::star (struct-|scalar_and_array|-|aggreg|-index-okp |i|)))))
  (let ((|a| (struct-|scalar_and_array|-write-|aggreg|-element |i| |v| |a|)))
    |a|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |write_flex_last| (|fl| |i| |c|)
  (declare (xargs :guard (and (c::star (struct-|flex|-p |fl|))
                              (c::sintp |i|)
                              (struct-|flex|-|last|-index-okp |i| |fl|)
                              (c::ucharp |c|))))
  (let ((|fl| (struct-|flex|-write-|last|-element |i| |c| |fl|)))
    |fl|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |point2D|
        |point3D|
        |integers|
        |scalar_and_array|
        |flex|
        |read_x_from_point2D_by_value|
        |read_x_from_point2D_by_pointer|
        |read_y_from_point2D_by_value|
        |read_y_from_point2D_by_pointer|
        |allpos_by_value|
        |allpos_by_pointer|
        |read_scalar_by_value|
        |read_scalar_by_pointer|
        |read_aggreg_by_value|
        |read_aggreg_by_pointer|
        |read_flex_last|
        |return1|
        |return2|
        |return3|
        |return4|
        |return5|
        |return6|
        |return7|
        |return8|
        |return9|
        |return10|
        |write_x_to_point2D_by_value|
        |write_x_to_point2D_by_pointer|
        |write_y_to_point2D_by_value|
        |write_y_to_point2D_by_pointer|
        |write_scalar_by_value|
        |write_scalar_by_pointer|
        |write_aggreg_by_value|
        |write_aggreg_by_pointer|
        |write_flex_last|
        :file-name "structs"
        :header t)
