; More theorems about bytes-to-bits
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bytes-to-bits")
(include-book "len-mult-of-8p")
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "bvchop-list")
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(defthm bytes-to-bits-of-bvchop-list
  (equal (bytes-to-bits (bvchop-list 8 lst))
         (bytes-to-bits lst))
  :hints (("Goal" :in-theory (enable bytes-to-bits
                                     byte-to-bits ;why?
                                     bvchop-list))))

(defopeners bytes-to-bits :disable t)

(defthm len-mult-of-8p-of-bytes-to-bits
  (len-mult-of-8p (bytes-to-bits x))
  :hints (("Goal" :in-theory (enable len-mult-of-8p))))
