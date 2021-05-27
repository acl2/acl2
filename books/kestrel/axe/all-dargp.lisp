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

;;;
;;; all-dargp
;;;

;; This recognizes a list of args in a DAG node that is a function call.
;; Todo: Rename this all-dargp.
(defforall all-dargp (items) (dargp items)
  :declares ((type t items)))

;; Our normal form is to express everything in terms of whether the item is a consp.
(defthmd integerp-of-car-when-all-dargp
  (implies (all-dargp args)
           (equal (integerp (car args))
                  (if (consp args)
                      (not (consp (car args)))
                    nil)))
  :hints (("Goal" :in-theory (enable all-dargp))))

(defthm not-equal-of-header-and-nth-when-all-dargp
  (implies (all-dargp args)
           (not (equal :header (nth n args))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;disable usually?
(defthm natp-of-nth-when-all-dargp
  (implies (and (all-dargp args)
                (natp n)
                (< n (len args)))
           (equal (natp (nth n args))
                  (not (consp (nth n args)))))
  :hints (("Goal" :in-theory (enable all-dargp))))

;; too expensive to leave enabled
(defthmd integerp-of-nth-when-all-dargp
  (implies (and (all-dargp args)
                (natp n)
                (< n (len args)))
           (equal (integerp (nth n args))
                  (not (consp (nth n args)))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

(defthm acl2-numberp-of-nth-when-all-dargp
  (implies (and (all-dargp args)
                (natp n)
                (< n (len args)))
           (equal (acl2-numberp (nth n args))
                  (not (consp (nth n args)))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;;disabled because we are not really using all-consp as a normal form (yet).
(defthmd all-myquotep-when-all-dargp
  (implies (all-dargp items)
           (equal (all-myquotep items)
                  (all-consp items)))
  :hints (("Goal" :in-theory (enable all-myquotep all-dargp all-consp))))

(defthmd consp-of-cdr-of-nth-when-all-dargp
  (implies (and (all-dargp args)
                (< n (len args))
                (natp n))
           (equal (consp (cdr (nth n args)))
                  (consp (nth n args))))
  :hints (("Goal" :in-theory (e/d (all-dargp nth) ()))))

(defthmd myquotep-of-nth-when-all-dargp
  (implies (and (all-dargp args)
                (< n (len args))
                (natp n))
           (equal (myquotep (nth n args))
                  (consp (nth n args))))
  :hints (("Goal" :in-theory (e/d (all-dargp nth) ()))))

(defthmd dargp-of-nth-when-all-dargp
  (implies (and (all-dargp args)
                (< n (len args))
                (natp n))
           (dargp (nth n args)))
  :hints (("Goal" :in-theory (e/d (all-dargp) ()))))


;; too expensive to leave enabled
(defthmd true-listp-of-cdr-of-nth-when-all-dargp
  (implies (and (all-dargp args)
                (natp n)
                (< n (len args)))
           (true-listp (cdr (nth n args))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;; too expensive to leave enabled
(defthmd <-of-len-of-nth-and-3-when-all-dargp
  (implies (and (all-dargp args)
                (natp n)
                (< n (len args)))
           (< (len (nth n args)) 3))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;; too expensive to leave enabled
(defthmd equal-of-len-of-nth-and-2-when-all-dargp
  (implies (and (all-dargp args)
                (natp n)
                (< n (len args)))
           (equal (equal (len (nth n args)) 2)
                  (consp (nth n args))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;; too expensive to leave enabled
(defthmd <-of-1-and-len-of-nth-when-all-dargp
  (implies (and (all-dargp args)
                (natp n)
                (< n (len args)))
           (equal (< 1 (len (nth n args)))
                  (consp (nth n args))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

(defthmd not-<-of-0-and-nth-when-all-dargp
  (implies (and (all-dargp args)
                (natp n)
                (< n (len args)))
           (not (< (nth n args) 0)))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;; too expensive to leave enabled
(defthmd not-cddr-of-nth-when-all-dargp
  (implies (and (all-dargp args)
                (natp n)
                (< n (len args)))
           (not (cddr (nth n args))))
  :hints (("Goal" :in-theory (enable all-dargp nth))))

;; same as below except uses car instead of nth 0
(defthmd equal-of-quote-and-car-of-nth-when-all-dargp
  (implies (and (all-dargp args)
                (< n (len args))
                (natp n))
           (equal (equal 'quote (car (nth n args)))
                  (consp (nth n args))))
  :hints (("Goal" :in-theory (e/d (all-dargp nth) ()))))

(defthmd equal-of-quote-and-nth-0-of-nth-when-all-dargp
  (implies (and (all-dargp args)
                (< n (len args))
                (natp n))
           (equal (equal 'quote (nth 0 (nth n args)))
                  (consp (nth n args))))
  :hints (("Goal" :in-theory (e/d (all-dargp nth) ()))))

(defthm all-dargp-forward-helper
  (implies (and (all-dargp items)
                (not (consp (car items)))
                (consp items))
           (natp (car items)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable all-dargp))))

(defthm all-dargp-when-all-myquotep-cheap
  (implies (all-myquotep args)
           (all-dargp args))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-myquotep))))

(defthm dargp-of-cdr-of-assoc-equal
  (implies (and (all-dargp (strip-cdrs alist))
                (assoc-equal var alist))
           (dargp (cdr (assoc-equal var alist))))
  :hints (("Goal" :in-theory (e/d (strip-cdrs)
                                  ()))))
