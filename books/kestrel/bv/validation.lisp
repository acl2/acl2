; Theorems to validate the STP translation of the BV operators
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Formalize and prove some of the "Note"s on:
;; https://stp.readthedocs.io/en/stable/cvc-input-language.html

(include-book "bvuminus")
(include-book "bvminus")
(include-book "bvnot")

;; From https://stp.readthedocs.io/en/stable/cvc-input-language.html:
;; BVUMINUS(t) is a short-hand for BVPLUS(n,~t,0bin1), where n is the length of t.

(thm
  (equal (bvuminus n x) ; uses x instead of t, since t means "true"
         (bvplus n (bvnot n x) 1))
  :hints (("Goal" :in-theory (enable bvuminus bvplus bvnot
                                     bvchop-of-sum-cases lognot))))


;; From https://stp.readthedocs.io/en/stable/cvc-input-language.html:
;; BVSUB(n,t1,t2)) is a short-hand for BVPLUS(n,t1,BVUMINUS(t2)).
(thm
  (equal (bvminus n t1 t2) ; Axe translates bvminus to bvsub
         (bvplus n t1 (bvuminus n t2)))
  :hints (("Goal" :in-theory (enable bvuminus bvplus bvnot
                                     bvchop-of-sum-cases lognot))))
