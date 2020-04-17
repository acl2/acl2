; Oset Utilities -- Tests
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "osets")

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (set::list-in '(32 #\a 2) (set::mergesort '(1 2 5 32 #\a g))))

(assert! (not (set::list-in '(3 4) (set::mergesort '("3" 4)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (set::set-all-natp nil))

(assert! (set::set-all-natp '(2 55 65)))

(assert! (not (set::set-all-natp (set::mergesort '(#\a 5 9)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (set::nat-setp nil))

(assert! (set::nat-setp '(2 55 65)))

(assert! (not (set::nat-setp 44)))

(assert! (not (set::nat-setp '(-4))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (set::set-all-integerp nil))

(assert! (set::set-all-integerp '(-2 55 65)))

(assert! (not (set::set-all-integerp (set::mergesort '(#\a 5 -9)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (set::integer-setp nil))

(assert! (set::integer-setp '(-2 55 65)))

(assert! (not (set::integer-setp 44)))

(assert! (not (set::integer-setp '(#\4))))
