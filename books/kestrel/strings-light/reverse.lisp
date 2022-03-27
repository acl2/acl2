; A lightweight book the built-in function reverse, when applied to strings
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that reverse can operate on both strings and lists.  This book focuses
;; on reversing strings.

(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;; If this causes problems, you may want to include [books]/kestrel/lists-light/reverse.
(in-theory (disable reverse))

(defthm stringp-of-reverse
  (equal (stringp (reverse x))
         (stringp x))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm reverse-of-reverse-when-stringp
  (implies (stringp x)
           (equal (reverse (reverse x))
                  x))
  :hints (("Goal" :in-theory (enable reverse))))
