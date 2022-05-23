; Rules about bv-array-read
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-array-read")
(include-book "kestrel/bv/unsigned-byte-p-forced" :dir :system)

(defthm unsigned-byte-p-forced-of-bv-array-read
  (implies (and (<= element-size n)
                (natp n)
                (natp element-size))
           (unsigned-byte-p-forced n (bv-array-read element-size len index data)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))
