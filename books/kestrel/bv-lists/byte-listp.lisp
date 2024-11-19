; Rules about byte-listp.
;
; Copyright (C) 2020-2024 Kestrel Institute
; The definition of byte-listp is in books/kestrel/fty/byte-list.lisp.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The purpose of this book is to provide rules about byte-listp without bringing
;; in lots of other machinery.

(include-book "byte-listp-def")
(include-book "kestrel/bv/bytep" :dir :system)

(defthm byte-listp-forward-to-true-listp
  (implies (byte-listp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable byte-listp))))

(defthm unsigned-byte-p-8-of-nth-when-byte-listp
  (implies (and (byte-listp bytes)
                (natp n)
                (< n (len bytes)))
           (unsigned-byte-p 8 (nth n bytes)))
  :hints (("Goal" :in-theory (enable byte-listp nth))))

(defthm byte-listp-of-cons
  (equal (byte-listp (cons a x))
         (and (bytep a)
              (byte-listp x)))
  :hints (("Goal" :in-theory (enable byte-listp))))

;avoid name clash with std
(defthm byte-listp-of-append-2
  (equal (byte-listp (append x y))
         (and (byte-listp (true-list-fix x))
              (byte-listp y)))
  :hints (("Goal" :in-theory (enable byte-listp append))))

(defthm byte-listp-of-revappend
  (equal (byte-listp (revappend x y))
         (and (byte-listp (true-list-fix x))
              (byte-listp y)))
  :hints (("Goal" :in-theory (enable byte-listp revappend))))

(defthm byte-listp-of-cdr
  (implies (byte-listp x)
           (byte-listp (cdr x)))
  :hints (("Goal" :in-theory (enable byte-listp))))

;; name avoids clash with byte-listp-of-nthcdr, which calls double-rewrite
(defthm byte-listp-of-nthcdr-simple
  (implies (byte-listp x)
           (byte-listp (nthcdr n x)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm byte-listp-of-take-simple
  (implies (byte-listp x)
           (equal (byte-listp (take n x))
                  (<= (nfix n) (len x))))
  :hints (("Goal" :in-theory (enable take byte-listp))))

;; Avoids name clash with weaker rule in FTY
(defthm bytep-of-nth-when-byte-listp-2
  (implies (byte-listp bytes)
           (equal (bytep (nth n bytes))
                  (< (nfix n) (len bytes))))
  :hints (("Goal" :in-theory (enable byte-listp))
          ("subgoal *1/1" :cases ((< n (+ 1 (len (cdr bytes))))))))

;; Avoids name clash with weaker rule in FTY
(defthm bytep-of-car-when-byte-listp-2
  (implies (byte-listp bytes)
           (equal (bytep (car bytes))
                  (consp bytes)))
  :hints (("Goal" :in-theory (enable byte-listp))))
