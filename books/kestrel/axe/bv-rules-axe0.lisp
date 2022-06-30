; Basic Axe rules about BVs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Simple rules needed by Axe but not by ACL2 (e.g., because ACL2 uses
;; :type-prescription rules but Axe does not).  Unlike bv-rules-axe.lisp, this
;; file does not use the Axe syntax functions.

(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/bvor" :dir :system)
(include-book "kestrel/bv/bvnot" :dir :system)
(include-book "kestrel/bv/bvand" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv/sbvlt" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)
(include-book "kestrel/bv/rotate" :dir :system)

(defthmd integerp-of-floor
  (integerp (floor i j)))

(defthmd rationalp-of-floor
  (rationalp (floor i j)))

(defthmd acl2-numberp-of-floor
  (acl2-numberp (floor i j)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd acl2-numberp-of-mod
  (acl2-numberp (mod x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd integerp-of-bvplus
  (integerp (bvplus size x y)))

(defthmd natp-of-bvplus
  (natp (bvplus size x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd integerp-of-leftrotate
  (integerp (leftrotate width amt val)))

(defthmd natp-of-leftrotate
  (natp (leftrotate width amt val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd integerp-of-leftrotate32
  (integerp (leftrotate32 amt val)))

(defthmd natp-of-leftrotate32
  (natp (leftrotate32 amt val)))

(defthmd leftrotate32-non-negative
  (not (< (leftrotate32 amt val) 0))
  :hints (("Goal" :in-theory (enable leftrotate32))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd integerp-of-rightrotate
  (integerp (rightrotate width amt val)))

(defthmd natp-of-rightrotate
  (natp (rightrotate width amt val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd integerp-of-rightrotate32
  (integerp (rightrotate32 amt val)))

(defthmd natp-of-rightrotate32
  (natp (rightrotate32 amt val))
  :hints (("Goal" :in-theory (enable rightrotate32))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd integerp-of-bvcat
  (integerp (bvcat highsize highval lowsize lowval)))

(defthmd natp-of-bvcat
  (natp (bvcat highsize highval lowsize lowval)))

;improve logapp-<-0?
(defthmd bvcat-non-negative
  (not (< (bvcat highsize highval lowsize lowval) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd integerp-of-bvxor
  (integerp (bvxor size x y)))

(defthmd natp-of-bvxor
  (natp (bvxor size x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd integerp-of-bitxor
  (integerp (bitxor x y)))

(defthmd natp-of-bitxor
  (natp (bitxor x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd integerp-of-bvand
  (integerp (bvand size x y)))

(defthmd natp-of-bvand
  (natp (bvand size x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd integerp-of-bvor
  (integerp (bvor size x y)))

(defthmd natp-of-bvor
  (natp (bvor size x y)))

(defthmd bvor-non-negative
  (not (< (bvor size x y) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd integerp-of-bvnot
  (integerp (bvnot size x)))

(defthmd natp-of-bvnot
  (natp (bvnot size x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd booleanp-of-sbvlt
  (booleanp (sbvlt size x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd booleanp-of-sbvle
  (booleanp (sbvle size x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;or just open bvle
(defthmd booleanp-of-bvle
  (booleanp (bvle size x y)))
