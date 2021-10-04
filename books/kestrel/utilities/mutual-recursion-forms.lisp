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

(defthm all-defun-formp-of-cons
  (equal (all-defun-formp (cons form forms))
         (and (defun-formp form)
              (all-defun-formp forms)))
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

;; Note that :STOBJS xargs and TYPE declares both count as guards.
(defun any-defun-has-a-guardp (defuns)
  (declare (xargs :guard (all-defun-formp defuns)))
  (if (atom defuns)
      nil
    (or (defun-has-a-guardp (first defuns))
        (any-defun-has-a-guardp (rest defuns)))))

(defun any-defun-has-verify-guards-nilp (defuns)
  (declare (xargs :guard (all-defun-formp defuns)))
  (if (atom defuns)
      nil
    (or (defun-has-verify-guards-nilp (first defuns))
        (any-defun-has-verify-guards-nilp (rest defuns)))))

(defun any-defun-has-verify-guards-tp (defuns)
  (declare (xargs :guard (all-defun-formp defuns)))
  (if (atom defuns)
      nil
    (or (defun-has-verify-guards-tp (first defuns))
        (any-defun-has-verify-guards-tp (rest defuns)))))

(defund replace-xarg-in-defuns (xarg val defuns)
  (declare (xargs :guard (and (keywordp xarg)
                              (true-listp defuns)
                              (all-defun-formp defuns))))
  (if (endp defuns)
      nil
    (cons (replace-xarg-in-defun xarg val (first defuns))
          (replace-xarg-in-defuns xarg val (rest defuns)))))

(defthm all-defun-formp-of-replace-xarg-in-defuns
  (implies (and (all-defun-formp defuns)
                (keywordp xarg))
           (all-defun-formp (replace-xarg-in-defuns xarg val defuns)))
  :hints (("Goal" :in-theory (enable replace-xarg-in-defuns))))

(defund remove-xarg-in-defuns (xarg defuns)
  (declare (xargs :guard (and (keywordp xarg)
                              (true-listp defuns)
                              (all-defun-formp defuns))))
  (if (endp defuns)
      nil
    (cons (remove-xarg-in-defun xarg (first defuns))
          (remove-xarg-in-defuns xarg (rest defuns)))))

(defund remove-hints-from-defuns (defuns)
  (declare (xargs :guard (and (true-listp defuns)
                              (all-defun-formp defuns))))
  (if (endp defuns)
      nil
    (cons (remove-hints-from-defun (first defuns))
          (remove-hints-from-defuns (rest defuns)))))

(defthm all-defun-formp-of-remove-xarg-in-defuns
  (implies (and (all-defun-formp defuns)
                (keywordp xarg))
           (all-defun-formp (remove-xarg-in-defuns xarg defuns)))
  :hints (("Goal" :in-theory (enable remove-xarg-in-defuns))))

(defthm consp-of-remove-xarg-in-defuns
  (equal (consp (remove-xarg-in-defuns xarg defuns))
         (consp defuns))
  :hints (("Goal" :in-theory (enable remove-xarg-in-defuns))))

(defund any-defun-demands-guard-verificationp (defuns)
  (declare (xargs :guard (and (all-defun-formp defuns)
                              (true-listp defuns))))
  (if (endp defuns)
      nil
    (or (defun-demands-guard-verificationp (first defuns))
        (any-defun-demands-guard-verificationp (rest defuns)))))


;;;
;;; mutual-recursion forms
;;;

;add more to this!
(defund mutual-recursion-formp (mut-rec)
  (declare (xargs :guard t))
  (and (consp mut-rec)
       (eq 'mutual-recursion (car mut-rec))
       (true-listp mut-rec)
       (all-defun-formp (cdr mut-rec))
       (consp (cdr mut-rec)) ; must be at least 1 form
       ))

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

(defthm mutual-recursion-formp-forward-to-all-defun-formp-of-cdr
  (implies (mutual-recursion-formp mut-rec)
           (all-defun-formp (cdr mut-rec)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable mutual-recursion-formp))))

(defthm mutual-recursion-formp-forward-to-true-listp-of-cdr
  (implies (mutual-recursion-formp mut-rec)
           (true-listp (cdr mut-rec)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable mutual-recursion-formp))))

(defund mutual-recursion-demands-guard-verificationp (mut-rec)
  (declare (xargs :guard (mutual-recursion-formp mut-rec)))
  (let ((defuns (cdr mut-rec)))
    (or (any-defun-has-verify-guards-tp defuns)
        (and (any-defun-has-a-guardp defuns)
             (not (any-defun-has-verify-guards-nilp defuns))))))

;; This assumes the verify-guard-eagerness is 1 (the usual value).
;; This avoids leaving in an unnecessary :verify-guards t.
(defund ensure-mutual-recursion-demands-guard-verification (mut-rec)
  (declare (xargs :guard (mutual-recursion-formp mut-rec)
                  :guard-hints (("Goal" :in-theory (enable mutual-recursion-formp)))))
  (let* ((defuns (cdr mut-rec))
         ;; remove any :verify-guards xargs, no matter whether they are t or nil:
         (defuns (remove-xarg-in-defuns :verify-guards defuns)))
    (if (any-defun-has-a-guardp defuns)
        ;; no need for explict :verify-guards:
        `(mutual-recursion ,@defuns)
      ;; Add :verify-guards t to the first defun:
      `(mutual-recursion ,(add-verify-guards-t-to-defun (first defuns))
                         ,@(rest defuns)))))

(defund remove-hints-from-mutual-recursion (mut-rec)
  (declare (xargs :guard (mutual-recursion-formp mut-rec)
                  :guard-hints (("Goal" :in-theory (enable mutual-recursion-formp)))))
  (let ((defuns (cdr mut-rec)))
    `(mutual-recursion ,@(remove-hints-from-defuns defuns))))
