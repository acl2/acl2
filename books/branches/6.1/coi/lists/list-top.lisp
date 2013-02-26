#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; list-top.lisp
;;
;; This file includes all of the list theorems.  You might try including
;; basic.lisp instead, if you don't need theorems about repeat, nth and
;; update-nth.

(in-package "LIST")

(include-book "basic")
(include-book "memberp")
(include-book "map-cons")
(include-book "repeat")
(include-book "nth-and-update-nth")
(include-book "update-nth-array") ; should this be here? -ews
