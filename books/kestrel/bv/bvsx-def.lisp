; Sign-extension
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat-def")
(include-book "getbit-def")
(include-book "repeatbit")

;we expect old-size <= new-size
(defund bvsx (new-size old-size val)
  (declare (xargs :guard (and (integerp val)
                              (posp old-size) ; so there's a bit to copy
                              (integerp new-size)
                              (<= old-size new-size))
                  :split-types t
                  :guard-hints (("Goal" :in-theory (enable repeatbit))))
           (type integer val)
           (type (integer 1 *) old-size)
           (type integer new-size))
  (if (not (mbt (posp old-size)))
      0 ;; special case guarantees the result fits in 0 bits
    (if (not (mbt (<= old-size new-size)))
        (bvchop new-size val) ;ensure the result fits in new-size bits (any sign extension is happening above the relevant bits)
      (bvcat (- new-size old-size)
             (repeatbit (- new-size old-size)
                        (getbit (+ -1 old-size) val))
             old-size
             val))))
