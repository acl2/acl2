; Basic Axe rules about BVs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
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

; TODO: Disable all of these?

(defthm integerp-of-bvplus
  (integerp (bvplus size x y)))

(defthm natp-of-bvplus
  (natp (bvplus size x y)))

(defthm integerp-of-floor
  (integerp (floor i j)))

(defthm rational-of-floor
  (rationalp (floor i j)))

(defthm acl2-numberp-of-floor
  (acl2-numberp (floor i j)))

(defthm integerp-of-leftrotate
  (integerp (leftrotate width amt val)))

(defthm integerp-of-leftrotate32
  (integerp (leftrotate32 amt val)))

(defthm natp-of-leftrotate
  (natp (leftrotate width amt val)))

(defthm natp-of-leftrotate32
  (natp (leftrotate32 amt val))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthm leftrotate32-non-negative
  (not (< (leftrotate32 amt val) 0))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthm integerp-of-rightrotate
  (integerp (rightrotate width amt val)))

(defthm integerp-of-rightrotate32
  (integerp (rightrotate32 amt val)))

(defthm natp-of-rightrotate
  (natp (rightrotate width amt val)))

(defthm natp-of-rightrotate32
  (natp (rightrotate32 amt val))
  :hints (("Goal" :in-theory (enable rightrotate32))))

(defthm integerp-of-bvcat
  (integerp (bvcat highsize highval lowsize lowval)))

;improve logapp-<-0?
(defthm bvcat-non-negative
  (not (< (bvcat highsize highval lowsize lowval) 0))
  :hints (("Goal" :in-theory (e/d (bvcat natp) ()))))

(defthm integerp-of-bvxor
  (integerp (bvxor size x y)))

(defthm natp-of-bvxor
  (natp (bvxor size x y)))

(defthm integerp-of-bitxor
  (integerp (bitxor x y)))

(defthm natp-of-bitxor
  (natp (bitxor x y)))

(defthm natp-of-bvcat
  (natp (bvcat highsize highval lowsize lowval)))

(defthm integerp-of-bvand
  (integerp (bvand size x y)))

(defthm natp-of-bvand
  (natp (bvand size x y)))

(defthm integerp-of-bvor
  (integerp (bvor size x y)))

(defthm natp-of-bvor
  (natp (bvor size x y)))

(defthm bvor-non-negative
  (not (< (bvor size x y) 0)))

;only needed by Axe
(defthm integerp-of-bvnot
  (integerp (bvnot size x)))

;only needed by Axe
(defthm natp-of-bvnot
  (natp (bvnot size x)))

;only needed by Axe
(defthm acl2-numberp-of-mod
  (acl2-numberp (mod x y)))

;; Only needed for Axe
(defthm booleanp-of-sbvlt
  (booleanp (sbvlt size x y)))

;; Only needed for Axe
(defthm booleanp-of-sbvle
  (booleanp (sbvle size x y)))

;; Only needed for Axe
;or just open bvle
(defthm booleanp-of-bvle
  (booleanp (bvle size x y)))
