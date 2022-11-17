; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   http://www.russinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

;; (include-book "log")

(set-enforce-redundancy nil)

(include-book "../lib1/top")

(set-inhibit-warnings "theory") ; avoid warning in the next event


(defthm bcevp-nencode
  (implies (and (equal k (+ p q))
                (natp p)
                (natp q))
           (bvecp (nencode x p q) k))
  :hints (("Goal" :in-theory (enable nencode))))
