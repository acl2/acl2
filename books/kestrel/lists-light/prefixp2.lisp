; Additional theorems about prefixp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book mixes prefixp with other non-built-in functions.

(include-book "prefixp")
(include-book "add-to-end")
(include-book "firstn")
(local (include-book "len"))

(defthm prefixp-of-add-to-end
  (equal (prefixp (add-to-end item lst) lst2)
         (and (prefixp lst lst2)
              (< (len lst) (len lst2))
              (equal item (nth (len lst) lst2))))
  :hints (("Goal" :in-theory (enable prefixp add-to-end))))

;using this can lead to loops?
(defthmd prefixp-rewrite
  (implies (true-listp x)
           (equal (prefixp x y)
                  (equal x (firstn (len x) y))))
  :hints (("Goal" :in-theory (enable prefixp))))

;replace the other
(defthmd prefixp-rewrite-gen
  (equal (prefixp x y)
         (equal (true-list-fix x) (firstn (len x) y)))
  :hints (("Goal" :in-theory (enable prefixp true-list-fix))))
