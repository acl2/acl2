; Converting a nat to a string
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/typed-lists-light/all-digit-charsp" :dir :system)
(local (include-book "coerce"))
(local (include-book "our-digit-char-p"))
(local (include-book "explode-nonnegative-integer"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Converts the natural N into a base-10 representation as a list of characters.
(defund nat-to-chars (n)
  (declare (xargs :guard (natp n)
                  :split-types t)
           (type (integer 0 *) n))
  (explode-nonnegative-integer n 10 nil))

(defthm character-listp-of-nat-to-chars
  (character-listp (nat-to-chars n))
  :hints (("Goal" :in-theory (enable nat-to-chars))))

;; NAT-TO-CHARS is essentially injective.
(defthm equal-of-nat-to-chars-and-nat-to-chars
  (equal (equal (nat-to-chars n1)
                (nat-to-chars n2))
         (equal (nfix n1) (nfix n2)))
  :hints (("Goal" :in-theory (enable nat-to-chars))))

(defthm all-digit-charsp-of-nat-to-chars-and-10
  (all-digit-charsp (nat-to-chars n) 10)
  :hints (("Goal" :in-theory (enable nat-to-chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Converts the natural N into a base-10 representation as a string.
(defund nat-to-string (n)
  (declare (xargs :guard (natp n)
                  :split-types t)
           (type (integer 0 *) n))
  (coerce (nat-to-chars n) 'string))

;; NAT-TO-STRING is essentially injective.
(defthm equal-of-nat-to-string-and-nat-to-string
  (equal (equal (nat-to-string n1)
                (nat-to-string n2))
         (equal (nfix n1) (nfix n2)))
  :hints (("Goal" :in-theory (enable nat-to-string))))

(defthm not-equal-of-nat-to-string-and-empty-string
  (not (equal (nat-to-string n) ""))
  :hints (("Goal" :in-theory (enable nat-to-string))))
