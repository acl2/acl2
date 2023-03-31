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

(defthm typed-io-listp-of-revappend
  (equal (typed-io-listp (revappend x y) typ)
         (and (typed-io-listp (true-list-fix x) typ)
              (typed-io-listp y typ)))
  :hints (("Goal" :in-theory (enable typed-io-listp revappend true-list-fix))))

(defthm typed-io-listp-of-character-becomes-character-listp
  (equal (typed-io-listp x :character)
         (character-listp x))
  :hints (("Goal" :in-theory (enable character-listp typed-io-listp))))

(defthmd nat-listp-when-typed-io-listp-of-byte
  (implies (typed-io-listp vals :byte)
           (nat-listp vals))
  :hints (("Goal" :in-theory (enable typed-io-listp nat-listp))))

(defthmd unsigned-byte-listp-when-typed-io-listp-of-byte
  (implies (typed-io-listp vals :byte)
           (unsigned-byte-listp 8 vals))
  :hints (("Goal" :in-theory (enable typed-io-listp unsigned-byte-listp))))

(defthmd character-listp-when-typed-io-listp-of-character
  (implies (typed-io-listp vals :character)
           (character-listp vals))
  :hints (("Goal" :in-theory (enable typed-io-listp character-listp))))
