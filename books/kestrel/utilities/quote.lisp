; Utilities dealing with quoted objects
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "myquotep")
(local (include-book "equal-of-booleans"))

;; STATUS: IN-PROGRESS


;; A variant of UNQUOTE with a more suitable guard.
;; Note that quotep is not a strong enough guard for us to unquote here (that's
;; why myquotep exists).
(defun-inline unquote$ (x)
  (declare (xargs :guard (myquotep x)))
  (unquote x))

;use kwote?
(defmacro enquote (val)
  `(list 'quote ,val))

;;;
;;; all-myquotep (TODO: Move to a new book, in typed-lists-light)
;;;

(defund all-myquotep (items)
  (declare (xargs :guard (true-listp items)))
  (if (endp items)
      t
    (and (myquotep (first items))
         (all-myquotep (rest items)))))

(defthm all-myquotep-of-cdr-cheap
  (implies (all-myquotep lst)
           (all-myquotep (cdr lst)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-myquotep))))

(defthm all-myquotep-of-cons
  (equal (all-myquotep (cons item lst))
         (and (myquotep item)
              (all-myquotep lst)))
  :hints (("Goal" :in-theory (enable all-myquotep))))

(defthm all-myquotep-when-not-consp
  (implies (not (consp lst))
           (all-myquotep lst))
  :hints (("Goal" :in-theory (enable all-myquotep))))

(defthmd consp-of-cdr-of-nth-when-all-myquotep
  (implies (and (all-myquotep args)
                (natp n))
           (equal (consp (cdr (nth n args)))
                  (< n (len args)))))

(defthmd consp-of-nth-when-all-myquotep
  (implies (and (all-myquotep args)
                (natp n))
           (equal (consp (nth n args))
                  (< n (len args)))))

;; (defthmd not-cddr-when-all-myquotep
;;   (implies (and (all-myquotep items)
;;                 (member-equal item items))
;;            (not (cddr item)))
;;   :hints (("Goal" :in-theory (enable all-myquotep))))

(defthmd myquotep-when-all-myquotep-and-member-equal
  (implies (and (all-myquotep items)
                (member-equal item items))
           (myquotep item))
  :hints (("Goal" :in-theory (enable all-myquotep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
