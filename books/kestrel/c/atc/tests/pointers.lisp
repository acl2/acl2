; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib) (:open-output-channel!)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some examples to test code generation for integers manipulated by pointer.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |f1| (|x|)
  (declare (xargs :guard (c::star (c::sintp |x|))))
  (c::bitnot-sint (c::sint-read |x|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |f2| (|x| |y|)
  (declare (xargs :guard (and (c::star (c::uintp |x|))
                              (c::star (c::uintp |y|)))))
  (c::add-uint-uint (c::uint-read |x|)
                    (c::uint-read |y|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |g1| (|a|)
  (declare (xargs :guard (c::star (c::sllongp |a|))))
  (c::sllong-read |a|))

(defun |g2| (|a|)
  (declare (xargs :guard (c::star (c::sllongp |a|))))
  |a|)

(defun |g3| (|a|)
  (declare (xargs :guard (c::star (c::sllongp |a|))))
  (mv (c::sint-dec-const 1) |a|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |h1| (|n| |e|)
  (declare (xargs :guard (and (c::star (c::ushortp |n|))
                              (c::ushortp |e|))))
  (declare (ignore |n|))
  (let ((|n| (c::ushort-write |e|)))
    |n|))

(defun |h2| (|e| |m|)
  (declare (xargs :guard (and (c::uintp |e|)
                              (c::star (c::uintp |m|)))))
  (let ((|m| (c::uint-write (c::add-uint-uint (c::uint-read |m|) |e|))))
    (mv (c::sint-dec-const 11) |m|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |swap_uints| (|x| |y|)
  (declare (xargs :guard (and (c::star (c::uintp |x|))
                              (c::star (c::uintp |y|)))
                  :guard-hints (("Goal" :in-theory (enable c::declar)))))
  (let* ((|temp| (c::declar (c::uint-read |x|)))
         (|x| (c::uint-write (c::uint-read |y|)))
         (|y| (c::uint-write |temp|)))
    (mv |x| |y|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |f1| |f2|
        |g1| |g2| |g3|
        |h1| |h2|
        |swap_uints|
        :file-name "pointers" :header t)
