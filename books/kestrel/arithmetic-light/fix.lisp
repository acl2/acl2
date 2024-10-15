; A lightweight book about the built-in function fix.
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Normally, since this book is about fix, we would disable fix.  But I'm not
;; sure that is the best strategy, and it seemed to cause problems.
;; (in-theory (disable fix))

(defthm fix-when-acl2-numberp
  (implies (acl2-numberp x)
           (equal (fix x)
                  x))
  :hints (("Goal" :in-theory (enable fix))))

;; Disabled by default to avoid introducing rationalp out of nowhere.
(defthmd fix-when-rationalp
  (implies (rationalp x)
           (equal (fix x)
                  x))
  :hints (("Goal" :in-theory (enable fix))))

;; Disabled by default to avoid introducing integerp out of nowhere.
(defthmd fix-when-integerp
  (implies (integerp x)
           (equal (fix x)
                  x))
  :hints (("Goal" :in-theory (enable fix))))

;; Disabled by default to avoid introducing natp out of nowhere.
(defthmd fix-when-natp
  (implies (natp x)
           (equal (fix x)
                  x))
  :hints (("Goal" :in-theory (enable fix))))
