; More theorems about bits-to-bytes-little
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/bits-to-bytes-little" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "unsigned-byte-listp")

(defopeners bits-to-bytes-little :disable t)

(defthm unsigned-byte-listp-of-bits-to-bytes-little
  (unsigned-byte-listp 8 (bits-to-bytes-little bits))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp-rewrite))))

(defthm all-integerp-of-bits-to-bytes-little
  (all-integerp (bits-to-bytes-little bits))
  :hints (("Goal" :in-theory (enable bits-to-bytes-little))))
