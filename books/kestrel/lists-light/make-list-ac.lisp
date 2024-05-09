; A lightweight book about the built-in function make-list-ac
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable make-list-ac))

(defthm len-of-make-list-ac
  (equal (len (make-list-ac n val acc))
         (+ (nfix n) (len acc)))
  :hints (("Goal" :in-theory (enable make-list-ac))))

(defthm true-listp-of-make-list-ac-type
  (implies (true-listp acc)
           (true-listp (make-list-ac n val acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable make-list-ac))))

;; Or this could go in typed-lists-light.
;; Tweaked to match what's in std, despite the use of the param name X:
(defthm character-listp-of-make-list-ac
  (equal (character-listp (make-list-ac n x ac))
         (and (character-listp ac)
              (or (characterp x)
                  (zp n))))
  :hints (("Goal" :in-theory (enable make-list-ac))))
