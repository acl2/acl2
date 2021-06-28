; BV Lists Library: Rules about bits-to-byte-little
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bits-to-byte-little")
(include-book "kestrel/bv/getbit" :dir :system)
(include-book "kestrel/bv/putbits" :dir :system)
(local (include-book "kestrel/bv/bvcat" :dir :system))

(defthm getbit-of-bits-to-byte-little
  (equal (getbit n (bits-to-byte-little bits))
         (if (< (nfix n) 8)
             (bvchop 1 (nth (nfix n) bits))
           0))
  :hints (("Goal" :in-theory (enable bits-to-byte-little))))

(defthm bits-to-byte-little-of-update-nth
  (equal (bits-to-byte-little (update-nth n bit bits))
         (putbit 8 (nfix n) bit (bits-to-byte-little bits)))
  :hints (("Goal" :in-theory (enable bits-to-byte-little))))
