; BV Library: logeqv
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
(local (include-book "logand"))
(local (include-book "lognot"))
(local (include-book "logior"))

(in-theory (disable binary-logeqv))

(defthm commutativity-of-logeqv
  (equal (logeqv i j)
         (logeqv j i))
  :hints (("Goal" :in-theory (enable logeqv logorc1 logand))))

(defthm logeqv-of-0
  (equal (logeqv 0 j)
         (lognot j))
  :hints (("Goal" :in-theory (enable logeqv))))

(defthm logeqv-of--1
  (equal (logeqv -1 j)
         (ifix j))
  :hints (("Goal" :in-theory (enable logeqv))))

(defthm logeqv-of-lognot-same
  (equal (logeqv i (lognot i))
         0)
  :hints (("Goal" :in-theory (enable logeqv))))

(defthm logeqv-negative
  (implies (and (integerp n)
                (<= 0 n)
                (integerp i)
                (integerp j)
                )
           (equal (< (logeqv i j) 0)
                  (or (and (< i 0)
                           (< j 0))
                      (and (<= 0 i)
                           (<= 0 j)))))
  :hints (("Goal" :in-theory (enable logeqv))))

(defthmd logeqv-of-lognot
  (equal (logeqv i (lognot j))
         (lognot (logeqv i j)))
  :hints (("Goal"
           :cases ((and (integerp j) (integerp i))
                   (and (not (integerp j)) (integerp i))
                   (and (integerp j) (not (integerp i))))
           :in-theory (e/d (logeqv logorc1 ;logior
                                   lognot-of-logand)
                           (lognot)))))

(defthm lognot-of-logeqv
  (equal (lognot (logeqv i j))
         (logeqv i (lognot j)))
  :hints (("Goal" :by logeqv-of-lognot)))

(defthm logeqv-of-lognot-arg1
  (equal (logeqv (lognot j) i)
         (lognot (logeqv i j)))
  :hints (("Goal"
           :cases ((and (integerp j) (integerp i))
                   (and (not (integerp j)) (integerp i))
                   (and (integerp j) (not (integerp i))))
           :in-theory (e/d (logeqv logorc1 ;logior
                                   lognot-of-logand
                                   )
                           (lognot)))))
;move
(defthm logand-of-lognot-same-three
  (equal (logand i (lognot i) j)
         0)
  :hints (("Goal"
           :cases ((and (integerp j) (integerp i))
                   (and (not (integerp j)) (integerp i))
                   (and (integerp j) (not (integerp i))))
           :use (:instance logand-associative
                           (i i)
                           (j (lognot i))
                           (k j))
           :in-theory (disable logand-associative))))

(defthm logeqv-associative
  (implies (integerp k)
           (equal (logeqv (logeqv i j) k)
                  (logeqv i (logeqv j k))))
  :hints (("Goal" :cases ((and (integerp j) (integerp i))
                          (and (not (integerp j)) (integerp i))
                          (and (integerp j) (not (integerp i))))
           :in-theory (enable logeqv lognot-of-logeqv logorc1 lognot-of-logand))))

(defthm logeqv-when-not-integerp-arg1
  (implies (not (integerp i))
           (equal (logeqv i j)
                  (lognot j)))
  :hints (("Goal" :in-theory (enable logeqv))))

(defthm logeqv-when-not-integerp-arg2
  (implies (not (integerp j))
           (equal (logeqv i j)
                  (lognot i)))
  :hints (("Goal" :in-theory (enable logeqv))))
