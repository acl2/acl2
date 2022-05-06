; Recognize a list of dag-args
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dargp")
(include-book "kestrel/sequences/defforall" :dir :system)
(include-book "kestrel/typed-lists-light/all-consp" :dir :system)

;; Recognizes a list of dargs, e.g., the arguments in a DAG node that is a function call.
(defforall all-dargp (items) (dargp items)
  :declares ((type t items)))

;; Our normal form is to express everything in terms of whether the item is a consp.
(defthmd integerp-of-car-when-all-dargp
  (implies (all-dargp dargs)
           (equal (integerp (car dargs))
                  (if (consp dargs)
                      (not (consp (car dargs)))
                    nil)))
  :hints (("Goal" :in-theory (enable all-dargp))))

(defthm not-equal-of-header-and-nth-when-all-dargp
  (implies (all-dargp dargs)
           (not (equal :header (nth n dargs))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;disable usually?
(defthm natp-of-nth-when-all-dargp
  (implies (and (all-dargp dargs)
                (natp n)
                (< n (len dargs)))
           (equal (natp (nth n dargs))
                  (not (consp (nth n dargs)))))
  :hints (("Goal" :in-theory (enable all-dargp))))

;; too expensive to leave enabled
(defthmd integerp-of-nth-when-all-dargp
  (implies (and (all-dargp dargs)
                (natp n)
                (< n (len dargs)))
           (equal (integerp (nth n dargs))
                  (not (consp (nth n dargs)))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

(defthm acl2-numberp-of-nth-when-all-dargp
  (implies (and (all-dargp dargs)
                (natp n)
                (< n (len dargs)))
           (equal (acl2-numberp (nth n dargs))
                  (not (consp (nth n dargs)))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;;disabled because we are not really using all-consp as a normal form (yet).
(defthmd all-myquotep-when-all-dargp
  (implies (all-dargp items)
           (equal (all-myquotep items)
                  (all-consp items)))
  :hints (("Goal" :in-theory (enable all-myquotep all-dargp all-consp))))

;; Uses consp as the normal form
(defthmd consp-of-cdr-of-nth-when-all-dargp
  (implies (and (all-dargp dargs)
                (< n (len dargs))
                (natp n))
           (equal (consp (cdr (nth n dargs)))
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;; Uses consp as the normal form
(defthmd myquotep-of-nth-when-all-dargp
  (implies (and (all-dargp dargs)
                (< n (len dargs))
                (natp n))
           (equal (myquotep (nth n dargs))
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

(defthmd dargp-of-nth-when-all-dargp
  (implies (and (all-dargp dargs)
                (< n (len dargs))
                (natp n))
           (dargp (nth n dargs)))
  :hints (("Goal" :in-theory (enable all-dargp))))


;; too expensive to leave enabled
(defthmd true-listp-of-cdr-of-nth-when-all-dargp
  (implies (and (all-dargp dargs)
                (natp n)
                (< n (len dargs)))
           (true-listp (cdr (nth n dargs))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;; too expensive to leave enabled
(defthmd <-of-len-of-nth-and-3-when-all-dargp
  (implies (and (all-dargp dargs)
                (natp n)
                (< n (len dargs)))
           (< (len (nth n dargs)) 3))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;; too expensive to leave enabled
(defthmd equal-of-len-of-nth-and-2-when-all-dargp
  (implies (and (all-dargp dargs)
                (natp n)
                (< n (len dargs)))
           (equal (equal (len (nth n dargs)) 2)
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;; too expensive to leave enabled
(defthmd <-of-1-and-len-of-nth-when-all-dargp
  (implies (and (all-dargp dargs)
                (natp n)
                (< n (len dargs)))
           (equal (< 1 (len (nth n dargs)))
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

(defthmd not-<-of-0-and-nth-when-all-dargp
  (implies (and (all-dargp dargs)
                ;; (natp n)
                ;; (< n (len dargs))
                )
           (not (< (nth n dargs) 0)))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;; too expensive to leave enabled
(defthmd not-cddr-of-nth-when-all-dargp
  (implies (and (all-dargp dargs)
                (natp n)
                (< n (len dargs)))
           (not (cddr (nth n dargs))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;; same as below except uses car instead of nth 0
(defthmd equal-of-quote-and-car-of-nth-when-all-dargp
  (implies (and (all-dargp dargs)
                (< n (len dargs))
                (natp n))
           (equal (equal 'quote (car (nth n dargs)))
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

(defthmd equal-of-quote-and-nth-0-of-nth-when-all-dargp
  (implies (and (all-dargp dargs)
                (< n (len dargs))
                (natp n))
           (equal (equal 'quote (nth 0 (nth n dargs)))
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

(defthm all-dargp-forward-helper
  (implies (and (all-dargp items)
                (not (consp (car items)))
                (consp items))
           (natp (car items)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable all-dargp))))

(defthm all-dargp-when-all-myquotep-cheap
  (implies (all-myquotep dargs)
           (all-dargp dargs))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-myquotep))))

(defthm dargp-of-cdr-of-assoc-equal
  (implies (and (all-dargp (strip-cdrs alist))
                (assoc-equal var alist))
           (dargp (cdr (assoc-equal var alist))))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm all-dargp-of-reverse-list
  (equal (all-dargp (reverse-list x))
         (all-dargp x))
  :hints (("Goal" :in-theory (enable all-dargp reverse-list))))
