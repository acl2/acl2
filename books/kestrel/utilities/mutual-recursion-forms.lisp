; Utilities for processing mutual-recursion forms
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defun-forms")

;;;
;;; lists of defuns
;;;

(defund all-defun-formp (forms)
  (declare (xargs :guard t))
  (if (atom forms)
      t
    (and (defun-formp (first forms))
         (all-defun-formp (rest forms)))))

(defthm defun-formp-of-car
  (implies (all-defun-formp forms)
           (equal (defun-formp (car forms))
                  (consp forms)))
  :hints (("Goal" :in-theory (enable all-defun-formp))))

(defthm all-defun-formp-of-cdr
  (implies (all-defun-formp forms)
           (all-defun-formp (cdr forms)))
  :hints (("Goal" :in-theory (enable all-defun-formp))))

;todo: rename find-defun-in-list?
(defun find-defun-in-mut-rec (fn defuns)
  (declare (xargs :guard (and (symbolp fn)
                              (true-listp defuns)
                              (all-defun-formp defuns))
                  :guard-hints (("Goal" :in-theory (enable all-defun-formp
                                                           defun-formp)))))
  (if (endp defuns)
      nil
    (if (eq fn (second (first defuns)))
        (first defuns)
      (find-defun-in-mut-rec fn (rest defuns)))))

(defthm defun-formp-of-find-defun-in-mut-rec
  (implies (all-defun-formp defuns)
           (iff (defun-formp (find-defun-in-mut-rec fn defuns))
                (find-defun-in-mut-rec fn defuns)))
  :hints (("Goal" :in-theory (enable find-defun-in-mut-rec))))

;TODO: Consider stobj declarations (these act like guards?)
(defun any-defun-has-explicit-guardp (defuns)
  (declare (xargs :guard (all-defun-formp defuns)))
  (if (atom defuns)
      nil
    (or (defun-has-explicit-guardp (first defuns))
        (any-defun-has-explicit-guardp (rest defuns)))))


(defun any-defun-has-verify-guards-nilp (defuns)
  (declare (xargs :guard (all-defun-formp defuns)))
  (if (atom defuns)
      nil
    (or (defun-has-verify-guards-nilp (first defuns))
        (any-defun-has-verify-guards-nilp (rest defuns)))))

(defund replace-xarg-in-defuns (xarg val defuns)
  (declare (xargs :guard (and (keywordp xarg)
                              (true-listp defuns)
                              (all-defun-formp defuns))))
  (if (endp defuns)
      nil
    (cons (replace-xarg-in-defun xarg val (first defuns))
          (replace-xarg-in-defuns xarg val (rest defuns)))))

;;;
;;; mutual-recursion forms
;;;

;add more to this!
(defund mutual-recursion-formp (mut-rec)
  (declare (xargs :guard t))
  (and (consp mut-rec)
       (eq 'mutual-recursion (car mut-rec))
       (true-listp mut-rec)
       (all-defun-formp (fargs mut-rec))))

(defthm mutual-recursion-formp-forward-to-equal-of-car
  (implies (mutual-recursion-formp mut-rec)
           (equal (car mut-rec)
                  'mutual-recursion))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable mutual-recursion-formp))))

(defund replace-xarg-in-mutual-recursion (xarg val mutual-recursion)
  (declare (xargs :guard (and (keywordp xarg)
                              (mutual-recursion-formp mutual-recursion))
                  :guard-hints (("Goal" :in-theory (enable mutual-recursion-formp)))))
  `(mutual-recursion ,@(replace-xarg-in-defuns xarg val (fargs mutual-recursion))))
