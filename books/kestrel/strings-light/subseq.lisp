; A lightweight book about the built-in function subseq.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/utilities/coerce" :dir :system)) ; drop?
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system)) ;drop?
(local (include-book "kestrel/lists-light/subseq-list" :dir :system))

(in-theory (disable subseq))

;; move?  why needed?
(local
  (defthm equal-of-coerce-and-empty-string
    (implies (character-listp x)
             (equal (equal (coerce x 'string) "")
                    (not (consp x))))))

(defthm stringp-of-subseq
  (implies (stringp seq)
           (stringp (subseq seq start end)))
  :hints (("Goal" :in-theory (enable subseq))))

(defthm equal-of-subseq-and-empty-string
  (implies (and (<= end (length seq))
                (natp start)
                (natp end))
           (equal (equal (subseq seq start end) "")
                  (and (stringp seq)
                       (<= end start))))
  :hints (("Goal" :in-theory (enable subseq))))
