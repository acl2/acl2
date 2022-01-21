; A lightweight book about the built-in function signed-byte-p
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/arithmetic-light/expt2" :dir :system)) ;drop

(in-theory (disable signed-byte-p))

(defthm signed-byte-p-cases
  (equal (signed-byte-p 1 x)
         (or (equal 0 x)
             (equal -1 x)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm signed-byte-when-not-integerp-cheap
  (implies (not (integerp bits))
           (not (signed-byte-p bits x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm signed-byte-when-<=-of-0-cheap
  (implies (<= bits 0)
           (not (signed-byte-p bits x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm sbp-32-of-one-more
  (implies (and (signed-byte-p 32 x)
                (< x free)
                (signed-byte-p 32 free))
           (signed-byte-p 32 (+ 1 x)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm signed-byte-p-when-signed-byte-p
  (implies (and (signed-byte-p freesize x)
                (<= freesize size)
                (posp size))
           (signed-byte-p size x))
  :hints (("Goal" :in-theory (enable signed-byte-p))))
