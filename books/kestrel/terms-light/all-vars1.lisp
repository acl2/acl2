; Rules about the built-in function all-vars1
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See free-vars-in-term.lisp for a simpler function than all-vars1.

(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))

(in-theory (disable all-vars1))

(make-flag all-vars1)

(defthm-flag-all-vars1
  (defthm subsetp-equal-of-all-vars1-same
    (subsetp-equal ans (all-vars1 term ans))
    :flag all-vars1)
  (defthm subsetp-equal-of-all-vars1-lst-same
    (subsetp-equal ans (all-vars1-lst lst ans))
    :flag all-vars1-lst)
  :hints (("Goal" :in-theory (enable all-vars1))))

;; (defthm-flag-all-vars1
;;   (defthm theorem-for-all-vars1
;;     (implies (subsetp-equal ans0 ans)
;;              (subsetp-equal (all-vars1 term ans0)
;;                             (all-vars1 term ans)))
;;     :flag all-vars1)
;;   (defthm theorem-for-all-vars1-lst
;;     (implies (subsetp-equal ans0 ans)
;;              (subsetp-equal (all-vars1-lst lst ans0)
;;                             (all-vars1-lst lst ans)))
;;     :flag all-vars1-lst)
;; ;  :hints (("Goal" :in-theory (enable subsetp-equal)))
;;   )
