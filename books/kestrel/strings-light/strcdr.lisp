; Dropping the first character from a string
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/utilities/coerce" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))

;; Drops the first character
(defund strcdr (str)
  (declare (xargs :guard (and (stringp str)
                              (not (equal "" str)))))
  (subseq str 1 (length str)))

(defthm stringp-of-strcdr
  (implies (stringp str)
           (stringp (strcdr str)))
  :hints (("Goal" :in-theory (enable strcdr))))

(defthm length-of-strcdr
  (implies (stringp str)
           (equal (length (strcdr str))
                  (if (equal "" str)
                      0
                    (+ -1 (length str)))))
  :hints (("Goal" ;:use (:instance equal-of-empty-string-when-stringp (x str))
           :in-theory (enable strcdr))))
