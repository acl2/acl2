; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2024 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib) (:open-output-channel!)))

(include-book "std/basic/mbt-dollar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some examples to test that IF tests with MBT
; have their tests and 'else' branches ignored.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |mbt1| (|x|)
  (declare (xargs :guard (c::sintp |x|)))
  (if (mbt (c::sintp |x|))
      (c::lt-sint-sint |x| (c::sint-dec-const 100))
    (list :this-is-not-translated-to-c)))

;;;;;;;;;;;;;;;;;;;;

(defun |mbt2| (|x|)
  (declare (xargs :guard (and (c::sintp |x|)
                              (<= 0 (c::integer-from-sint |x|))
                              (<= (c::integer-from-sint |x|) 10))
                  :guard-hints (("Goal"
                                 :in-theory
                                 (enable c::minus-sint-okp
                                         c::sint-integerp-alt-def)))))
  (if (mbt (c::sintp |x|))
      (c::minus-sint |x|)
    (list :this-is-not-translated-to-c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |mbt_dollar| (|x|)
  (declare (xargs :guard (c::sintp |x|)))
  (if (mbt$ (c::sintp |x|))
      (c::lt-sint-sint |x| (c::sint-dec-const 100))
    (list :this-is-not-translated-to-c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |mbt1|
        |mbt2|
        |mbt_dollar|
        :file-name "mbt"
        :header t)
