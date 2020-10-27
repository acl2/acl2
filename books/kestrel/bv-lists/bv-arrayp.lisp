; A predicate to recognize arrays of bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)

(defun bv-arrayp (element-width length val)
  (declare (xargs :guard t))
  (and (all-unsigned-byte-p element-width val)
       (true-listp val)
       (equal (len val) length)))

(defthm len-when-bv-arrayp
  (implies (bv-arrayp bytesize numcols item1)
           (equal (len item1)
                  numcols))
  :hints (("Goal" :in-theory (enable bv-arrayp))))

(defthm true-listp-when-bv-arrayp
  (implies (bv-arrayp bytesize numcols item1)
           (true-listp item1))
  :hints (("Goal" :in-theory (enable bv-arrayp))))

;; this breaks the array abstraction
(defthm bv-arrayp-of-cons
  (equal (bv-arrayp bytesize len (cons item items))
         (and (unsigned-byte-p bytesize item)
              (bv-arrayp bytesize (+ -1 len) items)))
  :hints (("Goal" :in-theory (enable bv-arrayp))))

(defthm all-unsigned-byte-p-when-bv-arrayp
 (implies (bv-arrayp bytesize len input)
          (all-unsigned-byte-p bytesize input))
 :hints (("Goal" :in-theory (enable bv-arrayp))))

(defthm bv-arrayp-when-length-is-0
  (equal (bv-arrayp bytesize 0 val)
         (equal val nil))
  :hints (("Goal" :in-theory (enable bv-arrayp))))
