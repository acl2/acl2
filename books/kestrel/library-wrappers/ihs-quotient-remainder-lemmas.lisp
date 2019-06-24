; Disable some things from ihs/quotient-remainder-lemmas.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; NOTE: This book should probably only be used if you also include our books
;; that replace the things from IHS that are disabled here (see comments below).

(include-book "ihs/quotient-remainder-lemmas" :dir :system)

(in-theory (disable mod-minus)) ;we have better rules in bv/mod.lisp

(in-theory (disable mod-x-y-=-x+y-for-rationals)) ;causes lots of problems

(in-theory (disable floor-type-1 floor-bounded-by-/)) ;these do forcing

(in-theory (disable rem-x-y-=-x)) ;ours (in bv/bv) is better

(in-theory (disable mod-=-0)) ;problems due to forcing?  and we have equal-of-0-and-mod
