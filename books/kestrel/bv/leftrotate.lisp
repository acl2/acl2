; BV Library: leftrotate
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat-def")
(include-book "slice-def")
(local (include-book "../arithmetic-light/mod"))
(local (include-book "bvcat"))

(local (in-theory (disable expt)))

;; Rotate VAL to the left by AMT positions within a field of width WIDTH.  We
;; reduce the rotation amount modulo the width.
(defund leftrotate (width amt val)
  (declare (type integer val amt)
           (type (integer 0 *) width))
  (if (= 0 width)
      0
    (let* ((amt (mod (nfix amt) width)))
      (bvcat (- width amt)
             (slice (+ -1 width (- amt)) 0 val)
             amt
             (slice (+ -1 width) (+ width (- amt)) val)))))

(defthm unsigned-byte-p-of-leftrotate
  (implies (natp size)
           (unsigned-byte-p size (leftrotate size x y)))
  :hints (("Goal" :in-theory (enable leftrotate natp))))

(defund leftrotate16 (amt val)
  (declare (type integer amt val))
  (leftrotate 16 amt val))

(defund leftrotate32 (amt val)
  (declare (type integer amt val))
  (leftrotate 32 amt val))

(defund leftrotate64 (amt val)
  (declare (type integer amt val))
  (leftrotate 64 amt val))
