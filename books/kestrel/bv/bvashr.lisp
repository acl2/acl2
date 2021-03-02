; Arithmetic (sign-preserving) right shift
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvsx")
(include-book "bvshr")
(local (include-book "bvcat"))

;; NOTE: Currently, the shift amount must be less than the width.
;; TODO: Result may may be wrong if we shift all the way out! consider: (acl2::bvashr 32 -1 32)
(defun bvashr (width x shift-amount)
  (declare (type (integer 0 *) shift-amount)
           (type integer x)
           (type integer width)
           (xargs :guard (< shift-amount width)) ;what happens if they're equal?
           )
  (bvsx width
        (- width shift-amount)
        (bvshr width x shift-amount)))

(defthm integerp-of-bvashr
  (integerp (bvashr width x shift-amount)))

(defthm natp-of-bvashr
  (natp (bvashr width x shift-amount)))

;todo: gen
(defthm bvchop-of-bvashr
  (equal (bvchop '8 (bvashr '32 x '8))
         (slice 15 8 x))
  :hints (("Goal" :in-theory (enable ))))

(defthmd bvashr-rewrite-for-constant-shift-amount
  (implies (and (syntaxp (quotep shift-amount))
                (syntaxp (quotep width)) ; will usually be true
                )
           (equal (bvashr width x shift-amount)
                  (bvsx width (- width shift-amount)
                        (bvshr width x shift-amount))))
  :hints (("Goal" :in-theory (enable bvashr))))
