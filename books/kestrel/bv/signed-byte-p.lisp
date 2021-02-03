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
