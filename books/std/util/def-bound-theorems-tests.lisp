; Tests of def-bound-theorems
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STD")

;; TODO: Add tests of defthm-natp and defthm-signed-byte-p

(include-book "def-bound-theorems")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Basic test:

(defund foo (x) (if (unsigned-byte-p 8 x) x 0))

(defthm-unsigned-byte-p unsigned-byte-p-foo
  :bound 8
  :concl (foo x)
  :gen-type t
  :gen-linear t
  :hints (("Goal" :in-theory (enable foo))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test the bound=1 case in which the :type-prescription rule uses bitp:

(defund bar (x) (if (unsigned-byte-p 1 x) x 0))

(defthm-unsigned-byte-p unsigned-byte-p-bar
  :bound 1
  :concl (bar x)
  :gen-type t
  :gen-linear t
  :hints (("Goal" :in-theory (enable bar))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test :hyp :

(defund decrement (x) (+ -1 x))

(defthm-unsigned-byte-p unsigned-byte-p-decrement
  :bound 8
  :hyp (and (unsigned-byte-p 8 x) (< 0 x))
  :concl (decrement x)
  :gen-type t
  :gen-linear t
  :hints (("Goal" :in-theory (enable decrement))))
