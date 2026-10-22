; Tests of functions stated to return booleans
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These are the functions mentioned in :doc generalized-booleans:

(thm
 (and (booleanp (/= x y))
      (booleanp (< x y))
      (booleanp (= x y))
      (booleanp (alpha-char-p x))
      (booleanp (atom x))
      (booleanp (char-equal x y))
      (booleanp (char< x y))
      (booleanp (char<= x y))
      (booleanp (char> x y))
      (booleanp (char>= x y))
      (booleanp (characterp x))
      (booleanp (consp x))
      (booleanp (endp x))
      (booleanp (eq x y))
      (booleanp (eql x y))
      (booleanp (equal x y))
      (booleanp (evenp x))
      (booleanp (integerp x))
      (booleanp (keywordp x))
      (booleanp (listp x))
      (booleanp (logbitp x y))
      (booleanp (logtest x y))
      (booleanp (lower-case-p x))
      (booleanp (minusp x))
      (booleanp (oddp x))
      (booleanp (plusp x))
      (booleanp (rationalp x))
      (booleanp (standard-char-p x))
      (booleanp (string-equal x y))
      (booleanp (stringp x))
      (booleanp (subsetp x y))
      (booleanp (symbolp x))
      (booleanp (upper-case-p x))
      (booleanp (zerop x))

      (booleanp (acl2-numberp x))
      (booleanp (complex-rationalp x)))
 :hints (("Goal" :in-theory (enable lower-case-p upper-case-p alpha-char-p))))
