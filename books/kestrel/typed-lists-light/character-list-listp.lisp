; A recognizer for lists of lists of characters
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/lists/flatten" :dir :system)

(defund character-list-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (character-listp (car x))
         (character-list-listp (cdr x)))))

(defthm character-list-listp-of-cons
  (equal (character-list-listp (cons a x))
         (and (character-listp a)
              (character-list-listp x)))
  :hints (("Goal" :in-theory (enable character-list-listp))))

(defthm character-list-listp-forward-to-true-list-listp
  (implies (character-list-listp x)
           (true-list-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable character-list-listp))))

(defthm true-list-listp-when-character-list-listp
  (implies (character-list-listp x)
           (true-list-listp x))
  :hints (("Goal" :in-theory (enable character-list-listp))))

(defthm true-listp-when-character-list-listp
  (implies (character-list-listp x)
           (true-listp x))
  :hints (("Goal" :in-theory (enable character-list-listp))))

(defthm character-listp-of-flatten
  (implies (character-list-listp x)
           (character-listp (flatten x)))
  :hints (("Goal" :in-theory (enable character-list-listp)))
  :rule-classes :type-prescription)
