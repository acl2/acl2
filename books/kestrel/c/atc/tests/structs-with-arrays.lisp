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

; Some examples to test just DEFSTRUCT with arrays.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::defstruct |scalar_and_array|
              (|scalar| c::sint)
              (|aggreg| (c::uchar 10)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |read_scalar| (|a|)
  (declare (xargs :guard (struct-|scalar_and_array|-p |a|)))
  (struct-|scalar_and_array|-read-|scalar| |a|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |write_scalar| (|v| |a|)
  (declare (xargs :guard (and (c::sintp |v|)
                              (struct-|scalar_and_array|-p |a|))))
  (let ((|a| (struct-|scalar_and_array|-write-|scalar| |v| |a|)))
    |a|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |read_aggreg| (|i| |a|)
  (declare
   (xargs
    :guard (and (c::sintp |i|)
                (struct-|scalar_and_array|-p |a|)
                (struct-|scalar_and_array|-|aggreg|-sint-index-okp |i| |a|))))
  (struct-|scalar_and_array|-read-|aggreg|-sint |i| |a|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |write_aggreg| (|i| |v| |a|)
  (declare
   (xargs
    :guard (and (c::sintp |i|)
                (c::ucharp |v|)
                (struct-|scalar_and_array|-p |a|)
                (struct-|scalar_and_array|-|aggreg|-sint-index-okp |i| |a|))))
  (let ((|a| (struct-|scalar_and_array|-write-|aggreg|-sint |i| |v| |a|)))
    |a|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |scalar_and_array|
        |read_scalar|
        |write_scalar|
        |read_aggreg|
        |write_aggreg|
        :output-file "structs-with-arrays.c"
        :proofs nil)
