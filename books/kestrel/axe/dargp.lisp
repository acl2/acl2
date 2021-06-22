; Arguments in DAG exprs that are function calls
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/quote" :dir :system)

;; Recognizes a function argument that appears in a DAG. For a DAG node that is
;; a function call, each argument of the call should satisfy dargp.  Each such
;; argument is either a quoted constant or a node number.
(defun dargp (item)
  (declare (xargs :guard t))
  (or (myquotep item)
      (natp item)))

(defthm dargp-when-myquotep-cheap
  (implies (myquotep item)
           (dargp item))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthmd dargp-when-myquotep
  (implies (myquotep item)
           (dargp item))
  :hints (("Goal" :in-theory (enable dargp))))

(defthm dargp-when-natp-cheap
  (implies (natp item)
           (dargp item))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable dargp))))

(defthmd dargp-when-natp
  (implies (natp x)
           (dargp x)))

(defthm dargp-of-list-of-quote
  (dargp (list 'quote x))
  :hints (("Goal" :in-theory (enable dargp))))

(defthm dargp-when-consp-cheap
  (implies (consp item)
           (equal (dargp item)
                  (myquotep item)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable dargp))))

(defthm dargp-when-equal-of-quote-and-car-cheap
  (implies (equal 'quote (car item))
           (equal (dargp item)
                  (myquotep item)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable dargp))))

;; These are kept disabled by default, for speed

(defthmd <=-of-0-when-dargp
  (implies (dargp item)
           (<= 0 item)))

(defthmd myquotep-when-dargp
  (implies (dargp item)
           (equal (myquotep item)
                  (consp item))))

;we use consp as the normal form
(defthmd integerp-when-dargp
  (implies (dargp item)
           (equal (integerp item)
                  (not (consp item)))))

;we use consp as the normal form
(defthmd consp-of-cdr-when-dargp
  (implies (dargp darg)
           (equal (consp (cdr darg))
                  (consp darg))))

;we use consp as the normal form
(defthmd cdr-when-dargp-iff
  (implies (dargp darg)
           (iff (cdr darg)
                (consp darg))))

(defthmd not-cddr-when-dargp
  (implies (dargp darg)
           (not (cddr darg))))

(defthmd true-listp-when-dargp
  (implies (dargp darg)
           (equal (true-listp darg)
                  (consp darg))))

(deftheory dargp-rules
  '(myquotep-when-dargp
    integerp-when-dargp
    consp-of-cdr-when-dargp
    cdr-when-dargp-iff
    not-cddr-when-dargp
    true-listp-when-dargp)
  :redundant-okp flg)
