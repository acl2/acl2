; A simple utility to make a lambda application (drops ignored vars)
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also make-lambda-term-simple.
;; See proof of correctness in make-lambda-application-simple-proof.lisp

(include-book "free-vars-in-term")
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(local (in-theory (disable mv-nth)))

;; Returns (mv formals actuals) where the FORMALS returned are the members of
;; FORMALS-TO-KEEP and the ACTUALS returned are their corresponding actuals.
(defund filter-formals-and-actuals (formals actuals formals-to-keep)
  (declare (xargs :guard (and (symbol-listp formals)
                              (symbol-listp formals-to-keep)
                              (equal (len formals) (len actuals)))))
  (if (endp formals)
      (mv nil nil)
    (mv-let (formals-res actuals-res)
      (filter-formals-and-actuals (rest formals) (rest actuals) formals-to-keep)
      (if (member-eq (first formals) formals-to-keep)
          (mv (cons (first formals) formals-res)
              (cons (first actuals) actuals-res))
        (mv formals-res
            actuals-res)))))

(defthm true-listp-of-mv-nth-0-of-filter-formals-and-actuals
  (true-listp (mv-nth 0 (filter-formals-and-actuals formals actuals formals-to-keep)))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm true-listp-of-mv-nth-1-of-filter-formals-and-actuals
  (true-listp (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep)))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm symbol-listp-of-mv-nth-0-of-filter-formals-and-actuals
  (implies (symbol-listp formals)
           (symbol-listp (mv-nth 0 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm pseudo-term-listp-of-mv-nth-1-of-filter-formals-and-actuals
  (implies (pseudo-term-listp actuals)
           (pseudo-term-listp (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm len-of-mv-nth-1-of-filter-formals-and-actuals
  (equal (len (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep)))
         (len (mv-nth 0 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

;; Similar to make-lambda-application, but make-lambda-application is worse because of the accumulator in all-vars1.
(defund make-lambda-application-simple (formals actuals body)
  (declare (xargs :guard (and (pseudo-termp body)
                              (symbol-listp formals)
                              (pseudo-term-listp actuals)
                              (equal (len formals)
                                     (len actuals)))))
  (let* ((free-vars (free-vars-in-term body))
         ;; These have to be added to ensure the lambda is closed:
         (extra-vars (set-difference-eq free-vars formals)))
    ;; Removes any formals not mentioned in the body (and their actuals):
    (mv-let (reduced-formals reduced-actuals)
      (filter-formals-and-actuals formals actuals free-vars)
      ;; Binds the formals to their actuals and all other vars to themselves:
      (let ((new-formals (append reduced-formals extra-vars))
            (new-actuals (append reduced-actuals extra-vars)))
        (if (equal new-formals new-actuals) ; also handles the case where new-formals is empty
            body ; no need to make a lambda at all (it would be trivial)
          `((lambda ,new-formals ,body) ,@new-actuals))))))

(defthm pseudo-termp-of-make-lambda-application-simple
  (implies (and (pseudo-termp body)
                (symbol-listp formals)
                (pseudo-term-listp actuals)
                (equal (len actuals) (len formals)))
           (pseudo-termp (make-lambda-application-simple formals actuals body)))
  :hints (("Goal" :in-theory (enable make-lambda-application-simple))))

;; (make-lambda-application-simple '(x y) '((+ '1 x) (+ '1 y)) '(cons x y))
;; (make-lambda-application-simple '(x y) '((+ '1 x) (+ '1 y)) ''2) ; doesn't make a lambda
;; (make-lambda-application-simple '(x y) '(x y) '(cons x y)) ; doesn't make a lambda
;; (make-lambda-application-simple nil nil '(cons x y)) ; doesn't make a lambda
