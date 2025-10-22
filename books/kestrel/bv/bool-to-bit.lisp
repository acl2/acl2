; Converting a boolean to a bit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See bool-to-bit-def.lisp for the definition of bool-to-bit.

(include-book "bool-to-bit-def")
(include-book "kestrel/booleans/bool-fix" :dir :system)
(include-book "bitnot")

(defthm equal-of-0-and-bool-to-bit
  (equal (equal 0 (bool-to-bit x))
         (not x))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

(defthm equal-of-bool-to-bit-and-0
  (equal (equal (bool-to-bit x) 0)
         (not x))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

(defthm equal-of-1-and-bool-to-bit
  (equal (equal 1 (bool-to-bit x))
         (bool-fix x))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

(defthm equal-of-bool-to-bit-and-1
  (equal (equal (bool-to-bit x) 1)
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

(defthm unsigned-byte-p-of-bool-to-bit
  (implies (posp size)
           (unsigned-byte-p size (bool-to-bit bool)))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

(defthm getbit-0-of-bool-to-bit
  (equal (getbit 0 (bool-to-bit x))
         (bool-to-bit x))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

;use bitnot?
(defthm bool-to-bit-of-equal-0-getbit-1
  (equal (bool-to-bit (equal 0 (getbit n x)))
         (bvnot 1 (getbit n x)))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

;use bitnot?
(defthm bool-to-bit-of-equal-0-getbit-2
  (equal (bool-to-bit (equal (getbit n x) 0))
         (bvnot 1 (getbit n x)))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

;just run the function!
(defthmd bool-to-bit-of-nil
  (equal (bool-to-bit nil)
         0))

;just run the function!
(defthmd bool-to-bit-of-t
  (equal (bool-to-bit t)
         1))

(defthm bool-to-bit-of-not
  (equal (bool-to-bit (not x))
         (bitnot (bool-to-bit x)))
  :hints (("Goal" :in-theory (enable bool-to-bit))))
