; Tests about how ACL2 treats duplicate xargs.
;
; Copyright (C) 2018-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The tests in this book help justify what merge-xargs does.

(include-book "kestrel/utilities/deftest" :dir :system)

;; Examples of xargs where conflicting values are illegal:

(must-fail
 (defun foo (x)
   (declare (xargs :guard-debug nil))
   (declare (xargs :guard-debug t))
   (if (zp x) 0 (+ 1 (foo (+ -1 x))))))

(must-fail
 (defun foo (x)
   (declare (xargs :measure x))
   (declare (xargs :measure (acl2-count x)))
   (if (zp x) 0 (+ 1 (foo (+ -1 x))))))

(must-fail
 (defun foo (x)
   (declare (xargs :measure-debug nil))
   (declare (xargs :measure-debug t))
   (if (zp x) 0 (+ 1 (foo (+ -1 x))))))

(must-fail
 (defun foo (x)
   (declare (xargs :mode :program))
   (declare (xargs :mode :logic))
   x))

(must-fail
 (defun foo (x)
   (declare (xargs :non-executable t))
   (declare (xargs :non-executable nil))
   x))

(must-fail
 (defun foo (x)
   (declare (xargs :normalize t))
   (declare (xargs :normalize nil))
   x))

(must-fail
 (defun foo (x)
   (declare (xargs :otf-flg t))
   (declare (xargs :otf-flg nil))
   x))

(must-fail
 (defun foo (x)
   (declare (xargs :ruler-extenders (cons)))
   (declare (xargs :ruler-extenders nil))
   x))

(must-fail
 (defun foo (x)
   (declare (xargs :split-types t))
   (declare (xargs :split-types nil))
   x))

(must-fail
 (defun foo (x)
   (declare (xargs :verify-guards t))
   (declare (xargs :verify-guards nil))
   x))

(must-fail
 (defun foo (x)
   (declare (xargs :well-founded-relation o<))
   (declare (xargs :well-founded-relation <))
   x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Examples of xargs where several values get combined:

;; multiple :stobjs xargs get appended:
(deftest
  (defun foo (state)
    (declare (xargs :stobjs nil))
    (declare (xargs :stobjs (state)))
    state))

;; multiple :stobjs xargs get appended (here 'state' represents a singleton list):
(deftest
  (defun foo (state)
    (declare (xargs :stobjs nil))
    (declare (xargs :stobjs state))
    state))

;; multiple :hints xargs get appended
(deftest
  (defun foo (x)
    (declare (xargs :hints (("Goal" :in-theory (enable natp)))))
    (declare (xargs :hints (("Goal" :in-theory (enable posp)))))
    (if (zp x) 0 (+ 1 (foo (+ -1 x))))))

;; multiple :guard-hints xargs get appended
(deftest
  (defun foo (x)
    (declare (xargs :guard-hints (("Goal" :in-theory (enable natp)))))
    (declare (xargs :guard-hints (("Goal" :in-theory (enable posp)))))
    (if (zp x) 0 (+ 1 (foo (+ -1 x))))))
