; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/defrule" :dir :system)

(include-book "../../set-defs")
(include-book "../../in-defs")
(include-book "../../to-oset-defs")
(include-book "../../min-max-defs")
(include-book "../cursor-defs")
(include-book "../before-after-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/oset" :dir :system))

(local (include-book "../../min-max"))
(local (include-book "../../insert"))
(local (include-book "../cursor"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This book relates before and after to the zipper's sequences, for use in
;; the proofs of the other cursor books. All rules are disabled.

(defruled in-of-before-becomes-member-equal
  (equal (in x (before cursor))
         (and (member-equal x (zip-before (cursor-fix cursor))) t))
  :enable before)

(defruled in-of-after-becomes-member-equal
  (equal (in x (after cursor))
         (and (member-equal x (zip-after (cursor-fix cursor))) t))
  :enable after)

(defruled emptyp-of-before-becomes-not-consp
  (equal (emptyp (before cursor))
         (not (consp (zip-before (cursor-fix cursor)))))
  :enable before)

(defruled emptyp-of-after-becomes-not-consp
  (equal (emptyp (after cursor))
         (not (consp (zip-after (cursor-fix cursor)))))
  :enable after)

;;;;;;;;;;;;;;;;;;;;

(defruled zip-before-of-cursor-fix-becomes-to-oset-of-before
  (equal (zip-before (cursor-fix cursor))
         (to-oset (before cursor)))
  :enable (before
           zip-oset-before-becomes-zip-before
           bstp-of-zip-plug-of-cursor-fix))

(defruled zip-after-of-cursor-fix-becomes-to-oset-of-after
  (equal (zip-after (cursor-fix cursor))
         (to-oset (after cursor)))
  :enable (after
           zip-oset-after-becomes-zip-after
           bstp-of-zip-plug-of-cursor-fix))

;;;;;;;;;;;;;;;;;;;;

(defruled min-of-after-becomes-car-of-zip-after
  (equal (min (after cursor))
         (car (zip-after (cursor-fix cursor))))
  :enable zip-after-of-cursor-fix-becomes-to-oset-of-after)

(defruled max-of-before-becomes-car-of-last-of-zip-before
  (equal (max (before cursor))
         (car (last (zip-before (cursor-fix cursor)))))
  :enable zip-before-of-cursor-fix-becomes-to-oset-of-before)
