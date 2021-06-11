; BV Library: leftrotate
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat-def")
(include-book "slice-def")
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/plus-and-minus"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/times"))
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

(defthm leftrotate-of-0-arg2
  (equal (leftrotate width 0 val)
         (bvchop width val))
  :hints (("Goal" :in-theory (enable leftrotate))))

(defthm leftrotate-of-0-arg3
  (equal (leftrotate width amt 0)
         0)
  :hints (("Goal" :in-theory (enable leftrotate))))

;gen!
(defthm leftrotate-of-plus
  (IMPLIES (natp AMT) ;was integerp
           (EQUAL (LEFTROTATE 32 (+ 32 AMT) VAL)
                  (LEFTROTATE 32 AMT VAL)))
  :hints (("Goal" :in-theory (enable LEFTROTATE))))

(defthm leftrotate-of-mod-same
  (implies (and (natp width)
                (natp amt))
           (equal (leftrotate width (mod amt width) val)
                  (leftrotate width (nfix amt) val)))
  :hints (("Goal" :in-theory (enable leftrotate))))

(defthm leftrotate-of-leftrotate
  (implies (and (natp width)
                (natp amt1)
                (natp amt2))
           (equal (leftrotate width amt1 (leftrotate width amt2 val))
                  (leftrotate width (+ amt1 amt2) val)))
  :hints (("Goal" :in-theory (enable leftrotate mod-sum-cases))))
