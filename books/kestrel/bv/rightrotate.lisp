; BV Library: rightrotate
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

;; Rotate VAL to the right by AMT positions within a field of width WIDTH.  We
;; reduce the rotation amount modulo the width.
(defund rightrotate (width amt val)
  (declare (type integer val amt)
           (type (integer 0 *) width))
  (if (= 0 width)
      0
    (let* ((amt (mod (nfix amt) width)))
      (bvcat amt
             (slice (+ -1 amt) 0 val)
             (- width amt)
             (slice (+ -1 width) amt val)))))

(defthm unsigned-byte-p-of-rightrotate
  (implies (natp size)
           (unsigned-byte-p size (rightrotate size x y)))
  :hints (("Goal" :in-theory (enable rightrotate natp))))

(defund rightrotate16 (amt val)
  (declare (type integer amt val))
  (rightrotate 16 amt val))

(defund rightrotate32 (amt val)
  (declare (type integer amt val))
  (rightrotate 32 amt val))

(defund rightrotate64 (amt val)
  (declare (type integer amt val))
  (rightrotate 64 amt val))
