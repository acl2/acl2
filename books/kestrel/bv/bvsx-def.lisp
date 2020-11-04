; Sign-extension
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat-def")
(include-book "getbit-def")
(include-book "repeatbit")

;we expect old-size <= new-size -- what should happen in the other case?  should it chop?
;what if old-size = 0?
(defund bvsx (new-size old-size val)
  (declare (type integer val)
           (type (integer 1 *) old-size)
           (type integer new-size)
           (xargs :guard (<= old-size new-size)
                  :guard-hints (("Goal" :in-theory (enable repeatbit))))
           )
  (if (not (mbt (posp old-size)))
      0 ;; special case guarantees the result fits in 0 bits
    (if (not (mbt (<= old-size new-size)))
        (bvchop new-size val) ;any sign extension is happening above the relevant bits
      (bvcat (+ 1 (- new-size old-size))
             (repeatbit (+ 1 (- new-size old-size))
                        (getbit (+ -1 old-size) val))
             (+ -1 old-size)
             val))))
