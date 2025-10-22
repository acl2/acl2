; Axe-specific rules about arithmetic
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm equal-of-+-combine-constants-alt
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)))
           (equal (equal (+ k2 x) k1)
                  (and (acl2-numberp k1)
                       (equal (- k1 k2)
                              (fix x))))))

;used by axe
(defthmd natp-of-+
  (implies (and (natp x)
                (natp y))
           (natp (+ x y))))

;used by axe
(defthmd natp-of-nfix
  (natp (nfix x)))

;move
;shouldn't this get commuted?
(defthmd equal-of-+-of-minus-same
  (equal (+ (- x) x)
         0))

;move
(defthm equal-of-fix-same
  (equal (equal (fix x) x) ;fixme why didn't this get reordered in the rc4 proof?
         (acl2-numberp x)))

(defthm <-of-constant-and-+-of-constant
  (implies (syntaxp (and (quotep k1) (quotep k2)))
           (equal (< k1 (+ k2 X))
                  (< (- k1 k2) x)))
  :hints (("Goal" :cases ((< k1 (+ k2 X))))))
