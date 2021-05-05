; Converting a boolean to a bit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/booleans/bool-fix" :dir :system)
(include-book "bitnot")

;; Convert a boolean (t or nil) to a bit (1 or 0).
(defund bool-to-bit (test)
  (declare (xargs :guard (booleanp test))) ;trying this
  (if test 1 0))

(defthm equal-of-bool-to-bit-and-0
  (equal (equal 0 (bool-to-bit x))
         (not x))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

(defthm equal-of-bool-to-bit-and-1
  (equal (equal 1 (bool-to-bit x))
         (bool-fix x))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

(defthm bool-to-bit-of-equal-of-0-when-unsigned-byte-p
  (implies (unsigned-byte-p 1 bit)
           (equal (bool-to-bit (equal 0 bit))
                  (bitnot bit)))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

(defthm bool-to-bit-of-equal-of-1-when-unsigned-byte-p
  (implies (unsigned-byte-p 1 bit)
           (equal (bool-to-bit (equal 1 bit))
                  bit))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

;; This helps justify some things that Axe does:
(defcong iff equal (bool-to-bit x) 1 :hints (("Goal" :in-theory (enable bool-to-bit))))

(defthm unsigned-byte-p-1-of-bool-to-bit
  (unsigned-byte-p 1 (bool-to-bit x))
  :hints (("Goal" :in-theory (enable bool-to-bit))))
