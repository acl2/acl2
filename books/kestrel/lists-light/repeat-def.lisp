; The definition of repeat.
;
; Copyright (C) 2018-2022 Kestrel Institute
; See books/std/lists/list-defuns.lisp for the copyright on repeat itself.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book provides the repeat function from std/lists without bringing in
;; anything else from std/lists.

;; From books/std/lists/list-defuns.lisp:
(defund repeat (n x)
  (declare (xargs :guard (natp n)
                  :verify-guards nil ;; done below
                  ))
  (mbe :logic (if (zp n)
                  nil
                (cons x (repeat (- n 1) x)))
       :exec (make-list n :initial-element x)))

(local
 ;;matches std
 (defthm repeat-when-zp
   (implies (zp n)
            (equal (repeat n a)
                   nil))
   :hints (("Goal" :in-theory (enable repeat)))))

(local
 ;; This can be viewed as an alternate definition of repeat that adds values at
 ;; the end.
 (defthmd repeat-alt-def
   (implies (posp n)
            (equal (repeat n val)
                   (append (repeat (+ -1 n) val) (list val))))
   :hints (("Goal" :induct (repeat n val)
            :in-theory (enable repeat append)))))

(local
 (defthm make-list-ac-rewrite
   (equal (make-list-ac n val ac)
          (append (repeat n val) ac))
   :hints (("subGoal *1/2" :use (:instance repeat-alt-def)
            :in-theory (disable repeat-alt-def)))))

(verify-guards repeat :hints (("Goal" :in-theory (enable repeat))))
