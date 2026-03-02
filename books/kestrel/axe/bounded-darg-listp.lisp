; Lists of DAG function args ("dargs") whose nodenum elemements are bounded
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(include-book "dargp-less-than")
(include-book "darg-listp")
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))

;; BOUND is often a nodenum whose expression is call of a function on DARGS.
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

(defthm bounded-darg-listp-of-reverse-list
  (equal (bounded-darg-listp (reverse-list dargs) bound)
         (bounded-darg-listp (true-list-fix dargs) bound))
  :hints (("Goal" :in-theory (enable bounded-darg-listp
                                     reverse-list))))

(defthm bounded-darg-listp-of-cdr
  (implies (bounded-darg-listp dargs bound)
           (bounded-darg-listp (cdr dargs) bound))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm bounded-darg-listp-of-take
  (implies (and (bounded-darg-listp dargs bound)
                (<= (nfix n) (len dargs)))
           (bounded-darg-listp (take n dargs) bound))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

;; Usually we use nth to extract particular dargs, but sometimes we walk through the list of dargs
(defthm dargp-less-than-of-car-when-bounded-darg-listp
  (implies (bounded-darg-listp dargs bound)
           (equal (dargp-less-than (car dargs) bound)
                  (consp dargs)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm bounded-darg-listp-forward-to-darg-listp
  (implies (bounded-darg-listp dargs bound)
           (darg-listp dargs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthmd bounded-darg-listp-when-non-positive
  (implies (<= n 0)
           (equal (bounded-darg-listp dargs n)
                  (and (all-myquotep dargs)
                       (true-listp dargs))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp all-myquotep))))

;; drop since we have the forward-chaining rule?
(defthmd darg-listp-when-bounded-darg-listp
  (implies (bounded-darg-listp dargs free)
           (darg-listp dargs))
  :hints (("Goal" :in-theory (enable bounded-darg-listp darg-listp dargp-less-than))))

(defthm <-of-0-when-bounded-darg-listp
  (implies (and (bounded-darg-listp dargs bound)
                ;;(not (consp (nth 0 dargs)))
                )
           (not (< (nth 0 dargs) 0)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthm integerp-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp dargs bound)
                (not (consp (nth n dargs)))
                (natp n)
                (< n (len dargs)))
           (integerp (nth n dargs)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

;; ;drop?  should use nth of dargs as the normal form
;; (defthmd integerp-of-nth-when-bounded-darg-listp-speciala
;;   (implies (and (bounded-darg-listp (cdr expr) bound)
;;                 (not (consp (nth n expr)))
;;                 (posp n)
;;                 (< n (len expr)))
;;            (integerp (nth n expr)))
;;   :hints (("Goal" :in-theory (e/d (bounded-darg-listp nth) (;NTH-OF-CDR
;;                                                             )))))

(defthm true-listp-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp dargs bound)
                (natp n)
                (< n (len dargs)))
           (equal (true-listp (nth n dargs))
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthmd true-listp-of-car-when-bounded-darg-listp
  (implies (and (bounded-darg-listp dargs bound)
                (natp n)
                (< 0 (len dargs)))
           (equal (true-listp (car dargs))
                  (consp (car dargs))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthm <-of-nth-0-when-bounded-darg-listp
  (implies (and (bounded-darg-listp dargs bound)
                (not (consp (nth 0 dargs)))
                (consp dargs))
           (< (nth 0 dargs) bound))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

;; todo: almost the same as the above
(defthmd <-of-car-when-bounded-darg-listp
  (implies (and (bounded-darg-listp dargs bound)
                (consp dargs)
                (not (consp (car dargs))))
           (< (car dargs) bound))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthmd not-<-of-car-when-bounded-darg-listp-2
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                (bounded-darg-listp dargs bound)
                (consp dargs)
                (not (consp (car dargs))))
           (not (< (car dargs) k)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

;gen?
(defthmd not-<-of-car-when-bounded-darg-listp
  (implies (and (bounded-darg-listp dargs bound2)
                (<= bound2 (+ 1 bound))
                (integerp bound)
                (integerp bound2)
                (consp dargs)
                (not (consp (car dargs))))
           (not (< bound (car dargs))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

;we use consp as the normal form
(defthmd integerp-of-car-when-bounded-darg-listp
  (implies (bounded-darg-listp dargs len)
           (equal (integerp (car dargs))
                  (if (consp dargs)
                      (not (consp (car dargs)))
                      nil)))
  :hints (("Goal" :in-theory (enable darg-listp dargp-less-than bounded-darg-listp))))

;todo: gen some of these rules about nth 0

;; too expensive to leave enabled
(defthmd <-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp dargs bound)
                (not (consp (nth n dargs)))
                (natp n)
                (< n (len dargs)))
           (< (nth n dargs) bound))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthm <-of-nth-when-bounded-darg-listp-free
  (implies (and (bounded-darg-listp dargs bound2)
                (<= bound2 bound)
                (not (consp (nth n dargs)))
                (natp n)
                (< n (len dargs)))
           (< (nth n dargs) bound))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm bounded-darg-listp-monotone
  (implies (and (bounded-darg-listp dargs m)
                (<= m n))
           (bounded-darg-listp dargs n))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than))))

(defthm bounded-darg-listp-when-all-myquotep-cheap
  (implies (all-myquotep dargs)
           (equal (bounded-darg-listp dargs bound)
                  (true-listp dargs)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp
                                     all-myquotep))))

;drop?
(defthm bounded-darg-listp-of-0
  (equal (bounded-darg-listp dargs 0)
         (and (all-myquotep dargs)
              (true-listp dargs)))
  :hints (("Goal" :in-theory (enable all-myquotep))))

;not tight?
(defthmd bound-lemma-for-car-when-bounded-darg-listp
  (implies (and (bounded-darg-listp dargs n)
                (consp dargs)
                (not (consp (car dargs))))
           (not (< n (car dargs))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm <-of-1-and-len-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp dargs bound)
                (natp n)
                (< n (len dargs)))
           (equal (< 1 (len (nth n dargs)))
                  (consp (nth n dargs))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than nth))))

(defthm natp-of-nth-when-bounded-darg-listp-gen
  (implies (and (bounded-darg-listp dargs bound)
                (natp n)
                (< n (len dargs)))
           (equal (natp (nth n dargs))
                  (not (consp (nth n dargs)))))
  :hints
  (("Goal" :in-theory (enable bounded-darg-listp))))

;; ;true whether it's a quotep or nodenum
;; (defthmd not-cddr-when-bounded-darg-listp
;;   (implies (and (bounded-darg-listp dargs bound)
;;          ;       (consp item)
;;                 (member-equal item dargs))
;;            (not (cddr item)))
;;   :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm not-cddr-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp dargs bound) ;bound is a free var
                (natp n)
                (< n (len dargs)))
           (not (cddr (nth n dargs))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm dargp-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp dargs bound)
                (< n (len dargs))
                (natp n))
           (dargp (nth n dargs)))
  :hints (("Goal" :in-theory (enable darg-listp))))

;drop?
(defthm bounded-darg-listp-when-bounded-darg-listp-of-cdr-cheap
  (implies (bounded-darg-listp (cdr dargs) bound)
           (equal (bounded-darg-listp dargs bound)
                  (if (not (consp dargs))
                      (null dargs)
                    (dargp-less-than (car dargs) bound))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))
