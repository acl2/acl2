; A book about the built-in function msgp
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable msgp))

(defthm msgp-compound-recognizer
  (if (msgp x)
      (or (stringp x)
          (and (consp x)
               (true-listp x)))
    (not (stringp x)))
  :rule-classes :compound-recognizer
  :hints (("Goal" :in-theory (enable msgp))))

(defthm msgp-of-cons
  (equal (msgp (cons str alist))
         (and (stringp str)
              (character-alistp alist)))
  :hints (("Goal" :in-theory (enable msgp))))
