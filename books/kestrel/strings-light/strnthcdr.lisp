; Dropping the first N characters from a string
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/utilities/coerce" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))

;; This is essentially nthcdr for strings.
(defund strnthcdr (n str)
  (declare (xargs :guard (and (natp n)
                              (stringp str)
                              (<= n (length str)))))
  (subseq str n (length str)))

(defthm stringp-of-strnthcdr
  (implies (stringp str)
           (stringp (strnthcdr n str)))
  :hints (("Goal" :in-theory (enable strnthcdr))))

;; (strnthcdr 3 "ABCDE")

(defthm length-of-strnthcdr
  (implies (and (<= n (length str))
                (natp n))
           (equal (length (strnthcdr n str))
                  (- (length str) n)))
    :hints (("Goal" :in-theory (enable strnthcdr length))))
