; Making an IF with a hint to avoid consing
;
; Copyright (C) 2024-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Make an if from TEST, THEN, and ELSE, except return HINT (and avoid consing)
;; if HINT is that IF.
;; Let's try leaving this enabled, since its :logic part is nice.
(defun make-if-with-hint (test
                          then
                          else
                          hint ; (if <test> <then> <else>)
                          )
  (declare (xargs :guard (and (true-listp hint)
                              (= 4 (len hint))
                              (eq 'if (car hint)))))
  (mbe :exec (if (and (equal test (cadr hint))
                      (equal then (caddr hint))
                      (equal else (cadddr hint)))
                 hint ; reuse the hint, to avoid consing
               `(if ,test ,then ,else))
       :logic `(if ,test ,then ,else)))

;; (defthmd logic-fnsp-of-cons-of-make-if-with-hint
;;   (implies (consp hint)
;;            (equal (logic-fnsp (make-if-with-hint test then else hint) w)
;;                   (and (logicp 'if w)
;;                        (logic-fnsp test w)
;;                        (logic-fnsp then w)
;;                        (logic-fnsp else w))))
;;   :hints (("Goal" :in-theory (enable logic-fnsp))))
