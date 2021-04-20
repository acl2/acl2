; Utilities dealing with quoted objects
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "equal-of-booleans"))

;; STATUS: IN-PROGRESS

;use kwote?
(defmacro enquote (val)
  `(list 'quote ,val))

;quotep by itself is not a sufficient guard for doing unquote!
(defun myquotep (item)
  (declare (xargs :guard t))
  (and (quotep item)
       (consp (cdr item))
       (null (cdr (cdr item)))))

(defthm myquotep-forward
  (implies (myquotep item)
           (equal (car item) 'quote))
  :rule-classes :forward-chaining)

(defthm myquotep-forward-to-consp
  (implies (myquotep item)
           (and (consp item)
                (true-listp item)))
  :rule-classes :forward-chaining)

(defthm myquotep-forward-to-equal-of-len
  (implies (myquotep x)
           (equal 2 (len x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable myquotep))))

;;;
;;; all-myquotep
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

;;;
;;; unquote-list
;;;

(defund unquote-list (lst)
  (declare (xargs :guard (and (true-listp lst)
                              (all-myquotep lst))))
  (cond ((not (consp lst)) nil)
        (t (cons (unquote (car lst))
                 (unquote-list (cdr lst))))))

(defthm myquotep-of-list-of-quote
  (myquotep (list 'quote x))
  :hints (("Goal" :in-theory (enable myquotep))))

(defthmd not-cddr-when-all-myquotep
  (implies (and (all-myquotep items)
                (member-equal item items))
           (not (cddr item)))
  :hints (("Goal" :in-theory (enable all-myquotep))))
