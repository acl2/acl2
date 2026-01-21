; Recognize a true-list of dargs ("dag args")
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

(include-book "dargp")
(include-book "kestrel/typed-lists-light/all-consp" :dir :system)
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)

;; Recognizes a list of dargs, e.g., the arguments in a DAG node that is a function call.
(defund darg-listp (items)
  (declare (xargs :guard t))
  (if (atom items)
      (null items)
    (and (dargp (first items))
         (darg-listp (rest items)))))

(defthmd true-list-when-darg-listp
  (implies (darg-listp x)
           (true-listp x))
  :hints (("Goal" :in-theory (enable darg-listp))))

(defthm darg-listp-forward-to-true-listp
  (implies (darg-listp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable darg-listp))))

(defthm darg-listp-of-append
  (equal (darg-listp (append x y))
         (and (darg-listp (true-list-fix x))
              (darg-listp y)))
  :hints (("Goal" :in-theory (enable darg-listp))))

(defthm darg-listp-of-cons
  (equal (darg-listp (cons a x))
         (and (dargp a)
              (darg-listp x)))
:hints (("Goal" :in-theory (enable darg-listp))))

(defthm darg-listp-of-cdr
  (implies (darg-listp x)
           (darg-listp (cdr x)))
  :hints (("Goal" :in-theory (enable darg-listp))))

(defthm dargp-of-car-when-darg-listp
  (implies (darg-listp x)
           (equal (dargp (car x))
                  (consp x)))
  :hints (("Goal" :in-theory (enable darg-listp))))

(defthm darg-listp-when-not-consp
  (implies (not (consp items))
           (equal (darg-listp items)
                  (equal items nil)))
  :hints (("Goal" :in-theory (enable darg-listp))))

;; Our normal form is to express everything in terms of whether the item is a consp.
(defthmd integerp-of-car-when-darg-listp
  (implies (darg-listp dargs)
           (equal (integerp (car dargs))
                  (if (consp dargs)
                      (not (consp (car dargs)))
                    nil)))
  :hints (("Goal" :in-theory (enable darg-listp))))

(defthm not-equal-of-header-and-nth-when-darg-listp
  (implies (darg-listp dargs)
           (not (equal :header (nth n dargs))))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

;disable usually?
(defthm natp-of-nth-when-darg-listp
  (implies (and (darg-listp dargs)
                (natp n)
                (< n (len dargs)))
           (equal (natp (nth n dargs))
                  (not (consp (nth n dargs)))))
  :hints (("Goal" :in-theory (enable darg-listp))))

;; too expensive to leave enabled
(defthmd integerp-of-nth-when-darg-listp
  (implies (and (darg-listp dargs)
                (natp n)
                (< n (len dargs)))
           (equal (integerp (nth n dargs))
                  (not (consp (nth n dargs)))))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

(defthm acl2-numberp-of-nth-when-darg-listp
  (implies (and (darg-listp dargs)
                (natp n)
                (< n (len dargs)))
           (equal (acl2-numberp (nth n dargs))
                  (not (consp (nth n dargs)))))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

;;disabled because we are not really using all-consp as a normal form (yet).
(defthmd all-myquotep-when-darg-listp
  (implies (darg-listp items)
           (equal (all-myquotep items)
                  (all-consp items)))
  :hints (("Goal" :in-theory (enable all-myquotep darg-listp all-consp))))

;; Uses consp as the normal form
(defthmd consp-of-cdr-of-nth-when-darg-listp
  (implies (and (darg-listp dargs)
                (< n (len dargs))
                (natp n))
           (equal (consp (cdr (nth n dargs)))
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

;; Uses consp as the normal form
(defthmd myquotep-of-nth-when-darg-listp
  (implies (and (darg-listp dargs)
                (< n (len dargs))
                (natp n))
           (equal (myquotep (nth n dargs))
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

(defthmd dargp-of-nth-when-darg-listp
  (implies (and (darg-listp dargs)
                (< n (len dargs))
                (natp n))
           (dargp (nth n dargs)))
  :hints (("Goal" :in-theory (enable darg-listp))))

;; too expensive to leave enabled
(defthmd true-listp-of-cdr-of-nth-when-darg-listp
  (implies (and (darg-listp dargs)
                (natp n)
                ;; (< n (len dargs))
                )
           (true-listp (cdr (nth n dargs))))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

;; too expensive to leave enabled
(defthmd <-of-len-of-nth-and-3-when-darg-listp
  (implies (and (darg-listp dargs)
                (natp n)
                ;; (< n (len dargs))
                )
           (< (len (nth n dargs)) 3))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

;; too expensive to leave enabled
(defthmd equal-of-len-of-nth-and-2-when-darg-listp
  (implies (and (darg-listp dargs)
                (natp n)
                (< n (len dargs)))
           (equal (equal (len (nth n dargs)) 2)
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

;; too expensive to leave enabled
(defthmd <-of-1-and-len-of-nth-when-darg-listp
  (implies (and (darg-listp dargs)
                (natp n)
                (< n (len dargs)))
           (equal (< 1 (len (nth n dargs)))
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

(defthmd not-<-of-0-and-nth-when-darg-listp
  (implies (and (darg-listp dargs)
                ;; (natp n)
                ;; (< n (len dargs))
                )
           (not (< (nth n dargs) 0)))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

;; too expensive to leave enabled
(defthmd not-cddr-of-nth-when-darg-listp
  (implies (and (darg-listp dargs)
                (natp n)
                (< n (len dargs)))
           (not (cddr (nth n dargs))))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

;; same as below except uses car instead of nth 0
(defthmd equal-of-quote-and-car-of-nth-when-darg-listp
  (implies (and (darg-listp dargs)
                (< n (len dargs))
                (natp n))
           (equal (equal 'quote (car (nth n dargs)))
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

(defthmd equal-of-quote-and-nth-0-of-nth-when-darg-listp
  (implies (and (darg-listp dargs)
                (< n (len dargs))
                (natp n))
           (equal (equal 'quote (nth 0 (nth n dargs)))
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

(defthm darg-listp-forward-helper
  (implies (and (darg-listp items)
                (not (consp (car items)))
                (consp items))
           (natp (car items)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable darg-listp))))

(defthm darg-listp-when-all-myquotep-cheap
  (implies (all-myquotep dargs)
           (equal (darg-listp dargs)
                  (true-listp dargs)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable darg-listp all-myquotep))))

(defthm dargp-of-cdr-of-assoc-equal-when-darg-listp-of-strip-cdrs ; avoid name clash
  (implies (and (darg-listp (strip-cdrs alist))
                (assoc-equal var alist))
           (dargp (cdr (assoc-equal var alist))))
  :hints (("Goal" :in-theory (enable strip-cdrs darg-listp))))

(defthm darg-listp-of-reverse-list
  (equal (darg-listp (reverse-list x))
         (darg-listp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable darg-listp reverse-list))))
