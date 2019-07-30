; BV Library: logorc1
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../arithmetic-light/minus"))
(local (include-book "logior"))

(in-theory (disable logorc1))

(defthm logorc1-of-0-arg1
  (equal (logorc1 0 j)
         -1)
  :hints (("Goal" :in-theory (enable logorc1 logior))))

(defthm logorc1-of--1-arg1
  (equal (logorc1 -1 j)
         (ifix j))
  :hints (("Goal" :in-theory (enable logorc1))))

(defthm logorc1-of-0-arg2
  (equal (logorc1 i 0)
         (lognot i))
  :hints (("Goal" :in-theory (enable logorc1 logior))))

(defthm logorc1-of--1-arg2
  (equal (logorc1 i -1)
         -1)
  :hints (("Goal" :in-theory (enable logorc1))))

(defthm logorc1-negative
  (implies (and (integerp i)
                (integerp j))
           (equal (< (logorc1 i j) 0)
                  (or (< j 0)
                      (<= 0 i))))
  :hints (("Goal" :in-theory (enable logorc1))))

(defthmd logorc1-of-lognot-arg1
  (equal (logorc1 (lognot i) j)
         (logior i j))
  :hints (("Goal" :in-theory (enable logorc1))))

(theory-invariant (incompatible (:rewrite logorc1-of-lognot-arg1) (:definition logorc1)))

(defthm logorc1-when-not-integerp-arg1
  (implies (not (integerp i))
           (equal (logorc1 i j)
                  -1))
  :hints (("Goal" :in-theory (enable logorc1))))

(defthm logorc1-when-not-integerp-arg2
  (implies (not (integerp j))
           (equal (logorc1 i j)
                  (lognot i)))
  :hints (("Goal" :in-theory (enable logorc1))))

(defthm logorc1-of-lognot-same-arg1
  (equal (LOGORC1 (LOGNOT I) I)
         (ifix i))
  :hints (("Goal" :in-theory (enable logorc1))))

(defthm logorc1-of-lognot-same-arg2
  (equal (logorc1 i (lognot i))
         (lognot i))
  :hints (("Goal" :in-theory (enable logorc1))))
