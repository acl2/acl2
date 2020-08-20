; A lightweight book about the built-in function coerce
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/len" :dir :system))

(defthm consp-of-coerce-of-list
  (equal (consp (coerce x 'list))
         (and (stringp x)
              (not (equal x ""))))
  :hints (("Goal" :use (:instance coerce-inverse-2)
           :cases ((coerce x 'list)))))

(defthm equal-of-len-of-coerce-of-list-and-0
  (equal (equal (len (coerce str 'list)) 0)
         (or (not (stringp str))
             (equal str ""))))

(defthm equal-of-coerce-when-quotep
  (implies (and (syntaxp (quotep str))
                (character-listp x))
           (equal (equal (coerce x 'string) str)
                  (and (stringp str)
                       ;; the call to coerce here gets computed:
                       (equal x (coerce str 'list))))))
