; Making a lambda with a hint to avoid consing
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(defund make-lambda-with-hint (formals body
                                       hint ; (lambda <formals> <body>)
                                       )
  (declare (xargs :guard (and (true-listp hint)
                              (= 3 (len hint))
                              (eq 'lambda (car hint)))))
  (if (and (equal formals (cadr hint))
           (equal body (caddr hint)))
      hint ; reuse the hint, to avoid consing
    `(lambda ,formals ,body)))

(defthm make-lambda-with-hint-opener
  (implies (and (true-listp hint)
                (= 3 (len hint))
                (eq 'lambda (car hint)))
           (equal (make-lambda-with-hint formals body hint)
                  `(lambda ,formals ,body)))
  :hints (("Goal" :in-theory (enable make-lambda-with-hint))))
