; A little-endian version of unpackbv
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unpackbv")
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(local (include-book "kestrel/typed-lists-light/all-integerp2" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local
 (defthm byte-listp-of-reverse-list
   (equal (byte-listp (reverse-list x))
          (byte-listp (true-list-fix x)))
   :hints (("Goal" :in-theory (enable reverse-list byte-listp)))))

;num is the number of chunks, size is the number of bits per chunk.
;The least significant part of BV comes first in the result.
(defund unpackbv-little (num size bv)
  (declare (type (integer 0 *) size) ;todo: disallow 0?
           (type (integer 0 *) num)
           (type integer bv))
  (reverse-list (unpackbv num size bv)))

(defthm len-of-unpackbv-little
  (equal (len (unpackbv-little num size bv))
         (nfix num))
  :hints (("Goal" :in-theory (enable unpackbv-little))))

(defthm byte-listp-of-unpackbv-little
  (byte-listp (unpackbv-little num 8 bv))
  :hints (("Goal" :in-theory (enable unpackbv-little))))
