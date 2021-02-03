; Prime fields library: Tests of bind-free rules
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

;; TODO: Split this file
;; TODO: Add more tests

(include-book "equal-of-add-cancel-bind-free")
(include-book "equal-of-add-move-negs-bind-free")

(in-theory (disable mod))

(defstub foo (x) t)

;;;
;;; test moving negations:
;;;

;; We wrap the equality in a stub to keep acl2 from assuming anything about it

(thm
 (implies (posp p)
          (equal (foo (equal (add x (add y (neg z p) p) p) (neg w p)))
                 ;; normally the mod and the ifix would go away:
                 (foo (equal (add x (add y w p) p) (mod (ifix z) p))))))

(thm
 (implies (and (posp p)
               (fep z p))
          ;;wrap the equality in a stub to keep acl2 from assuming anything about it:
          (equal (foo (equal (add x (add y (neg z p) p) p) (neg w p)))
                 (foo (equal (add x (add y w p) p) z)))))

;;;
;;; test cancellation:
;;;

(thm
 (implies (and (posp p)
               (fep x p))
          (equal (foo (equal (add x (add y z p) p) (add w (add x v p) p)))
                 (foo (equal (add y z p) (add w v p))))))

(thm
 (implies (and (posp p)
               (fep x p)
               (fep y p))
          (equal (foo (equal x (add x y p)))
                 (foo (equal 0 y)))))
