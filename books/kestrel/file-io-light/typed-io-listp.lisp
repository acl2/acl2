; A lightweight book about the built-in function typed-io-listp
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/unsigned-byte-listp-def" :dir :system)

(in-theory (disable typed-io-listp))

(defthm typed-io-listp-of-revappend
  (equal (typed-io-listp (revappend l1 l2) typ)
         (and (typed-io-listp (true-list-fix l1) typ)
              (typed-io-listp l2 typ)))
  :hints (("Goal" :in-theory (enable typed-io-listp revappend true-list-fix))))

(defthm typed-io-listp-of-character-becomes-character-listp
  (equal (typed-io-listp l :character)
         (character-listp l))
  :hints (("Goal" :in-theory (enable character-listp typed-io-listp))))

(defthmd nat-listp-when-typed-io-listp-of-byte
  (implies (typed-io-listp l :byte)
           (nat-listp l))
  :hints (("Goal" :in-theory (enable typed-io-listp nat-listp))))

(defthmd unsigned-byte-listp-when-typed-io-listp-of-byte
  (implies (typed-io-listp l :byte)
           (unsigned-byte-listp 8 l))
  :hints (("Goal" :in-theory (enable typed-io-listp unsigned-byte-listp))))

(defthm typed-io-listp-of-cdr
  (implies (typed-io-listp l typ)
           (typed-io-listp (cdr l) typ))
  :hints (("Goal" :in-theory (enable typed-io-listp revappend true-list-fix))))
