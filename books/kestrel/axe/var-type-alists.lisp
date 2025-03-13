; Alists from vars to axe-types
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also nodenum-type-alists.lisp

(include-book "axe-types")
(include-book "kestrel/alists-light/lookup-equal-def" :dir :system)

;; Recognizes an alist that maps vars to axe-types
;; See also test-case-type-alistp.
(defund var-type-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((entry (first alist)))
      (and (consp entry)
           (let ((var (car entry))
                 (type (cdr entry)))
             (and (symbolp var)
                  (axe-typep type)
                  (var-type-alistp (rest alist))))))))

(defthm var-type-alistp-forward-to-alistp
  (implies (var-type-alistp alist)
           (alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable var-type-alistp))))

;; Since nil is not an axe-type (see not-axe-typep-of-nil), nil means no type
(defthm axe-typep-of-lookup-equal-when-var-type-alistp
  (implies (var-type-alistp alist)
           (iff (axe-typep (lookup-equal var alist))
                (lookup-equal var alist)))
  :hints (("Goal" :in-theory (enable var-type-alistp lookup-equal assoc-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Like var-type-alistp but excludes the most-general-type and the empty-type.
;; todo: allow most-general-type (represented by t??) once test-case-typep allows that
(defund strict-var-type-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((entry (first alist)))
      (and (consp entry)
           (let ((var (car entry))
                 (type (cdr entry)))
             (and (symbolp var)
                  (axe-typep type)
                  (not (most-general-typep type)) ; note this
                  (not (empty-typep type)) ; note this
                  (strict-var-type-alistp (rest alist))))))))

(defthm var-type-alistp-when-strict-var-type-alistp
  (implies (strict-var-type-alistp alist)
           (var-type-alistp alist))
  :hints (("Goal" :in-theory (enable var-type-alistp
                                     strict-var-type-alistp))))
