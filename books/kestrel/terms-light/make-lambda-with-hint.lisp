; Making a lambda with a hint to avoid consing
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; Make a lambda from FORMALS and BODY, except return HINT (and avoid consing)
;; if HINT is that lambda.
(defund make-lambda-with-hint (formals
                               body
                               hint ; (lambda <formals> <body>)
                               )
  (declare (xargs :guard (and (true-listp hint)
                              (= 3 (len hint))
                              (eq 'lambda (car hint)))))
  (mbe :exec (if (and (equal formals (cadr hint))
                      (equal body (caddr hint)))
                 hint ; reuse the hint, to avoid consing
               `(lambda ,formals ,body))
       :logic `(lambda ,formals ,body)))

(defthm make-lambda-with-hint-opener
  (implies (and (true-listp hint)
                (= 3 (len hint))
                (eq 'lambda (car hint)))
           (equal (make-lambda-with-hint formals body hint)
                  `(lambda ,formals ,body)))
  :hints (("Goal" :in-theory (enable make-lambda-with-hint))))

(defthm lambda-formals-of-make-lambda-with-hint
  (equal (lambda-formals (make-lambda-with-hint formals body hint))
         formals)
  :hints (("Goal" :in-theory (enable make-lambda-with-hint))))

(defthm lambda-body-of-make-lambda-with-hint
  (equal (lambda-body (make-lambda-with-hint formals body hint))
         body)
  :hints (("Goal" :in-theory (enable make-lambda-with-hint))))

(defthm logic-fnsp-of-cons-of-make-lambda-with-hint
  (implies (consp hint)
           (equal (logic-fnsp (cons (make-lambda-with-hint formals body hint) args) w)
                  (and (logic-fnsp body w)
                       (logic-fns-listp args w))))
  :hints (("Goal" :in-theory (enable logic-fnsp))))
