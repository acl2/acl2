#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; top.lisp
;;
;; Includes the entire alists library.  You might prefer to include
;; only the portion of the library that you actually need, but this
;; is probably convenient for hacking.

(in-package "ALIST")

(include-book "equiv")
(include-book "strip")
(include-book "clearkey")
(include-book "deshadow")
(include-book "preimage")
