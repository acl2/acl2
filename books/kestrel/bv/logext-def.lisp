; BV Library: A lightweight book providing logext
;
; Copyright (C) 2022 Kestrel Institute
; The definitions in this file come from books/ihs. See the copyright there.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Same as in books/ihs/basic-definitions.lisp

(include-book "logapp-def")

(defun logext (size i)
  (declare (type unsigned-byte size))
  (declare (xargs :guard (and (and (integerp size) (< 0 size))
                              (integerp i))))
  (declare (xargs :split-types t))
  (let ((__function__ 'logext))
    (declare (ignorable __function__))
    (let* ((size-1 (- size 1)))
      (declare (type unsigned-byte size-1))
      (logapp size-1
              i
              (if (logbitp size-1 i) -1 0)))))
