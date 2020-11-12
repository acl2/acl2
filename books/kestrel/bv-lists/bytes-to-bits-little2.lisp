; Rules about bytes-to-bits-little
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bytes-to-bits-little")
(include-book "len-mult-of-8p")
(include-book "../utilities/defopeners")
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(defopeners bytes-to-bits-little :disable t)

(defthm len-mult-of-8p-of-bytes-to-bits-little
  (len-mult-of-8p (bytes-to-bits-little x))
  :hints (("Goal" :in-theory (enable len-mult-of-8p))))

;; (defthmd byte-to-bits-little-redef
;;   (equal (byte-to-bits-little byte)
;;          (reverse-list (unpackbv 8 1 byte)))
;;   :hints (("Goal" :in-theory (enable byte-to-bits-little CAR-BECOMES-NTH-OF-0))))
