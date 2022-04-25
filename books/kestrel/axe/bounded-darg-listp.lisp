; Lists of DAG function args ("dargs") whose nodenum elemements are bounded
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "dargp-less-than")
(include-book "all-dargp")

(defund bounded-darg-listp (dargs bound)
  (declare (xargs :guard (natp bound)
                  :split-types t)
           (type (integer 0 *) bound))
  (if (atom dargs)
      (null dargs)
    (and (dargp-less-than (first dargs) bound)
         (bounded-darg-listp (rest dargs) bound))))

(defthm bounded-darg-listp-when-not-consp
  (implies (not (consp dargs))
           (equal (bounded-darg-listp dargs bound)
                  (null dargs)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm bounded-darg-listp-of-cons
  (equal (bounded-darg-listp (cons darg dargs) bound)
         (and (dargp-less-than darg bound)
              (bounded-darg-listp dargs bound)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm bounded-darg-listp-of-append
  (equal (bounded-darg-listp (append dargs1 dargs2) bound)
         (and (bounded-darg-listp (true-list-fix dargs1) bound)
              (bounded-darg-listp dargs2 bound)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm bounded-darg-listp-of-revappend
  (equal (bounded-darg-listp (revappend dargs1 dargs2) bound)
         (and (bounded-darg-listp (true-list-fix dargs1) bound)
              (bounded-darg-listp dargs2 bound)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp revappend))))

(defthm bounded-darg-listp-of-cdr
  (implies (bounded-darg-listp dargs bound)
           (bounded-darg-listp (cdr dargs) bound))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm dargp-less-than-of-car-when-bounded-darg-listp
  (implies (bounded-darg-listp dargs bound)
           (equal (dargp-less-than (car dargs) bound)
                  (consp dargs)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm bounded-darg-listp-forward-to-true-listp
  (implies (bounded-darg-listp dargs bound)
           (true-listp dargs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthmd bounded-darg-listp-when-non-positive
  (implies (<= n 0)
           (equal (bounded-darg-listp items n)
                  (and (all-myquotep items)
                       (true-listp items))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp all-myquotep))))

(defthm bounded-darg-listp-of-reverse-list
  (equal (bounded-darg-listp (reverse-list items) bound)
         (bounded-darg-listp (true-list-fix items) bound))
  :hints (("Goal" :in-theory (enable bounded-darg-listp
                                     reverse-list))))

(defthm all-dargp-when-bounded-darg-listp
  (implies (bounded-darg-listp items free)
           (all-dargp items))
  :hints (("Goal" :in-theory (enable bounded-darg-listp all-dargp dargp-less-than))))

(defthm <-of-0-when-bounded-darg-listp
  (implies (and (bounded-darg-listp args bound)
                (not (consp (nth 0 args))))
           (not (< (nth 0 args) 0)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthm integerp-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp args bound)
                (not (consp (nth n args)))
                (natp n)
                (< n (len args)))
           (integerp (nth n args)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthm integerp-of-nth-when-bounded-darg-listp-special
  (implies (and (bounded-darg-listp (cdr expr) bound)
                (not (consp (nth n expr)))
                (posp n)
                (< n (len expr)))
           (integerp (nth n expr)))
  :hints (("Goal" :in-theory (e/d (bounded-darg-listp nth) (;NTH-OF-CDR
                                                            )))))

(defthm true-listp-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp args bound)
                (natp n)
                (< n (len args)))
           (equal (true-listp (nth n args))
                  (consp (nth n args))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthm true-listp-of-car-when-bounded-darg-listp
  (implies (and (bounded-darg-listp args bound)
                (natp n)
                (< 0 (len args)))
           (equal (true-listp (car args))
                  (consp (car args))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthm <-of-nth-0-when-bounded-darg-listp
  (implies (and (bounded-darg-listp args bound)
                (not (consp (nth 0 args)))
                (consp args))
           (< (nth 0 args) bound))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthmd <-of-car-when-bounded-darg-listp
  (implies (and (bounded-darg-listp vals bound)
                (consp vals)
                (not (consp (car vals))))
           (< (car vals) bound))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthm not-<-of-car-when-bounded-darg-listp-2
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                (bounded-darg-listp vals bound)
                (consp vals)
                (not (consp (car vals))))
           (not (< (car vals) k)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

;gen?
(defthmd not-<-of-car-when-bounded-darg-listp
  (implies (and (bounded-darg-listp vals bound2)
                (<= bound2 (+ 1 bound))
                (integerp bound)
                (integerp bound2)
                (consp vals)
                (not (consp (car vals))))
           (not (< bound (car vals))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

;we use consp as the normal form
(defthm integerp-of-car-when-bounded-darg-listp
  (implies (bounded-darg-listp args len)
           (equal (integerp (car args))
                  (if (consp args)
                      (not (consp (car args)))
                      nil)))
  :hints (("Goal" :in-theory (enable all-dargp dargp-less-than bounded-darg-listp))))

;todo: gen some of these rules about nth 0

;; too expensive to leave enabled
(defthmd <-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp args bound)
                (not (consp (nth n args)))
                (natp n)
                (< n (len args)))
           (< (nth n args) bound))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthm <-of-nth-when-bounded-darg-listp-free
  (implies (and (bounded-darg-listp args bound2)
                (<= bound2 bound)
                (not (consp (nth n args)))
                (natp n)
                (< n (len args)))
           (< (nth n args) bound))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm bounded-darg-listp-monotone
  (implies (and (bounded-darg-listp items m)
                (<= m n))
           (bounded-darg-listp items n))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthm bounded-darg-listp-when-all-myquotep-cheap
  (implies (all-myquotep items)
           (equal (bounded-darg-listp items bound)
                  (true-listp items)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp
                                     all-myquotep))))

(defthm bounded-darg-listp-of-0
  (equal (bounded-darg-listp items 0)
         (and (all-myquotep items)
              (true-listp items)))
  :hints (("Goal" :in-theory (enable all-myquotep))))

;not tight?
(defthmd bound-lemma-for-car-when-bounded-darg-listp
  (implies (and (bounded-darg-listp items n)
                (consp items)
                (not (consp (car items))))
           (not (< n (car items))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm <-of-1-and-len-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp args bound)
                (natp n)
                (< n (len args)))
           (equal (< 1 (len (nth n args)))
                  (consp (nth n args))))
  :hints (("Goal" :in-theory (e/d (bounded-darg-listp dargp-less-than nth) ()))))

(defthm natp-of-nth-when-bounded-darg-listp-gen
  (implies (and (bounded-darg-listp vals bound)
                (natp n)
                (< n (len vals)))
           (equal (natp (nth n vals))
                  (not (consp (nth n vals)))))
  :hints
  (("Goal" :in-theory (enable bounded-darg-listp))))

;true whether it's a quotep or nodenum
(defthmd not-cddr-when-bounded-darg-listp
  (implies (and (bounded-darg-listp items bound)
         ;       (consp item)
                (member-equal item items))
           (not (cddr item)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm not-cddr-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp args bound) ;bound is a free var
                (natp n)
                (< n (len args)))
           (not (cddr (nth n args))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm dargp-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp args bound)
                (< n (len args))
                (natp n))
           (dargp (nth n args)))
  :hints (("Goal" :in-theory (e/d (all-dargp) ()))))
