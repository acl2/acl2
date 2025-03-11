; Mapping reverse-list over a list.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: move this book to typed-lists/

(include-book "kestrel/sequences/defmap" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)
(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(include-book "kestrel/typed-lists-light/all-all-integerp" :dir :system)
(include-book "kestrel/typed-lists-light/all-integerp2" :dir :system) ; localize?
(include-book "all-all-unsigned-byte-p")
(include-book "all-unsigned-byte-p2") ;localize?
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;; todo: move
(defmap map-reverse-list (items) (reverse-list items)
  :declares ((xargs :guard (all-true-listp items))))

(defthm true-list-listp-of-map-reverse-list
  (true-list-listp (map-reverse-list x))
  :hints (("Goal" :in-theory (enable map-reverse-list))))

(defthm all-true-listp-of-map-reverse-list
  (all-true-listp (map-reverse-list x))
  :hints (("Goal" :in-theory (enable map-reverse-list all-true-listp))))

(defthm items-have-len-of-map-reverse-list
  (equal (items-have-len len (map-reverse-list x))
         (items-have-len len x))
  :hints (("Goal" :in-theory (enable map-reverse-list items-have-len))))

;fixme gen to any double-mapped predicate somehow??
(defthm all-all-unsigned-byte-p-of-map-reverse-list
  (equal (all-all-unsigned-byte-p width (map-reverse-list x))
         (all-all-unsigned-byte-p width x))
  :hints (("Goal" :in-theory (enable map-reverse-list all-all-unsigned-byte-p))))

(defthm all-all-integerp-of-map-reverse-list
  (implies (all-all-integerp x)
           (all-all-integerp (map-reverse-list x)))
  :hints (("Goal" :in-theory (enable all-all-integerp))))

(local
 (defun double-cdr-induct (x y)
   (if (endp x)
       (list x y)
       (double-cdr-induct (cdr x) (cdr y)))))

;move hyps to conclusion?
(defthm equal-of-map-reverse-list-and-map-reverse-list
  (implies (and (all-true-listp x)
                (all-true-listp y)
                (true-listp x)
                (true-listp y)
                )
           (equal (equal (map-reverse-list x) (map-reverse-list y))
                  (equal x y)))
  :hints (("Goal" :induct (double-cdr-induct x y)
           :in-theory (enable MAP-REVERSE-LIST))))
