; Representation of Natural Numbers as Digits in Arbitrary Bases -- Tests
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "core")
(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (dab-basep 0)))

(assert! (not (dab-basep 1)))

(assert! (dab-basep 2))

(assert! (dab-basep 8))

(assert! (dab-basep 10))

(assert! (dab-basep 16))

(assert! (dab-basep 60))

(assert! (not (dab-basep "10")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm dab-base-fix-test1
  (equal (dab-base-fix 0) 2))

(defthm dab-base-fix-test2
  (equal (dab-base-fix 1) 2))

(defthm dab-base-fix-test3
  (equal (dab-base-fix "10") 2))

(assert-equal (dab-base-fix 2) 2)

(assert-equal (dab-base-fix 8) 8)

(assert-equal (dab-base-fix 10) 10)

(assert-equal (dab-base-fix 16) 16)

(assert-equal (dab-base-fix 60) 60)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (dab-digitp 10 #\8)))

(assert! (not (dab-digitp 2 -1)))

(assert! (dab-digitp 10 8))

(assert! (dab-digitp 256 255))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm dab-digit-fix-test1
  (equal (dab-digit-fix 10 #\8) 0))

(defthm dab-digit-fix-test2
  (equal (dab-digit-fix 2 -1) 0))

(assert-equal (dab-digit-fix 10 8) 8)

(assert-equal (dab-digit-fix 256 255) 255)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (dab-digit-listp 12 5)))

(assert! (not (dab-digit-listp 16 '(10 11 "12"))))

(assert! (not (dab-digit-listp 20 '(4 0 20 10 -1))))

(assert! (dab-digit-listp 10 nil))

(assert! (dab-digit-listp 10 '(6 4 3 0)))

(assert! (dab-digit-listp 2 '(1 1 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm dab-digit-list-fix-test1
  (equal (dab-digit-list-fix 12 5) nil))

(defthm dab-digit-list-fix-test2
  (equal (dab-digit-list-fix 16 '(10 11 "12")) '(10 11 0)))

(defthm dab-digit-list-fix-test3
  (equal (dab-digit-list-fix 20 '(4 0 20 10 -1)) '(4 0 0 10 0)))

(assert-equal (dab-digit-list-fix 10 nil) nil)

(assert-equal (dab-digit-list-fix 10 '(6 4 3 0)) '(6 4 3 0))

(assert-equal (dab-digit-list-fix 2 '(1 1 0)) '(1 1 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (lendian=>nat 10 nil) 0)

(assert-equal (lendian=>nat 10 '(3 6 4)) 463)

(assert-equal (lendian=>nat 2 '(1 0 1 1)) 13)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (nat=>lendian* 10 0) nil)

(assert-equal (nat=>lendian* 10 86373) '(3 7 3 6 8))

(assert-equal (nat=>lendian* 16 240) '(0 15))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (nat=>lendian+ 10 0) '(0))

(assert-equal (nat=>lendian+ 10 86373) '(3 7 3 6 8))

(assert-equal (nat=>lendian+ 16 240) '(0 15))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (nat=>lendian 10 5 0) '(0 0 0 0 0))

(assert-equal (nat=>lendian 10 5 86373) '(3 7 3 6 8))

(assert-equal (nat=>lendian 16 4 240) '(0 15 0 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (bendian=>nat 10 nil) 0)

(assert-equal (bendian=>nat 10 '(4 6 3)) 463)

(assert-equal (bendian=>nat 2 '(1 1 0 1)) 13)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (nat=>bendian* 10 0) nil)

(assert-equal (nat=>bendian* 10 86373) '(8 6 3 7 3))

(assert-equal (nat=>bendian* 16 240) '(15 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (nat=>bendian+ 10 0) '(0))

(assert-equal (nat=>bendian+ 10 86373) '(8 6 3 7 3))

(assert-equal (nat=>bendian+ 16 240) '(15 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (nat=>bendian 10 5 0) '(0 0 0 0 0))

(assert-equal (nat=>bendian 10 5 86373) '(8 6 3 7 3))

(assert-equal (nat=>bendian 16 4 240) '(0 0 15 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (trim-bendian* '(0 0 8 7 5)) '(8 7 5))

(assert-equal (trim-bendian* '(8 7 5)) '(8 7 5))

(assert-equal (trim-bendian* '(8 0 0)) '(8 0 0))

(assert-equal (trim-bendian* '(0 0)) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (trim-lendian* '(1 1 0)) '(1 1))

(assert-equal (trim-lendian* '(0 1)) '(0 1))

(assert-equal (trim-lendian* '(0 0)) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (trim-bendian+ '(0 0 8 7 5)) '(8 7 5))

(assert-equal (trim-bendian+ '(8 7 5)) '(8 7 5))

(assert-equal (trim-bendian+ '(8 0 0)) '(8 0 0))

(assert-equal (trim-bendian+ '(0 0)) '(0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (trim-lendian+ '(1 1 0)) '(1 1))

(assert-equal (trim-lendian+ '(0 1)) '(0 1))

(assert-equal (trim-lendian+ '(0 0)) '(0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (group-bendian 2 8 '(1 1 1 1 0 0 0 0 1 1 0 0 0 0 0 0)) '(240 192))

(assert-equal (group-bendian 10 2 '(1 2 3 4 5 6)) '(12 34 56))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (group-lendian 2 8 '(1 1 1 1 0 0 0 0 1 1 0 0 0 0 0 0)) '(15 3))

(assert-equal (group-lendian 10 2 '(1 2 3 4 5 6)) '(21 43 65))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ungroup-bendian 2 8 '(254 1)) '(1 1 1 1 1 1 1 0 0 0 0 0 0 0 0 1))

(assert-equal (ungroup-bendian 10 2 '(98 8 0)) '(9 8 0 8 0 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ungroup-lendian 2 8 '(254 1)) '(0 1 1 1 1 1 1 1 1 0 0 0 0 0 0 0))

(assert-equal (ungroup-lendian 10 2 '(98 8 0)) '(8 9 8 0 0 0))
