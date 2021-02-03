; Apply dargp-less-than to all elements of a list
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

(include-book "dargp-less-than")
(include-book "all-dargp")

;;;
;;; all-dargp-less-than
;;;

;recognizes the args of a function call node in the dag
(defforall all-dargp-less-than (items bound) (dargp-less-than items bound)
  :fixed bound
  :declares ((type (integer 0 *) bound)))

(in-theory (disable all-dargp-less-than))

(defthmd all-dargp-less-than-when-non-positive
  (implies (<= n 0)
           (equal (all-dargp-less-than items n)
                  (all-myquotep items)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than all-myquotep))))

(defthm all-dargp-less-than-of-reverse-list
  (equal (all-dargp-less-than (reverse-list items) bound)
         (all-dargp-less-than items bound))
  :hints (("Goal" :in-theory (enable all-dargp-less-than
                                     reverse-list))))

(defthm all-dargp-when-all-dargp-less-than
  (implies (all-dargp-less-than items free)
           (all-dargp items))
  :hints (("Goal" :in-theory (enable all-dargp-less-than all-dargp dargp-less-than))))

(defthm <-of-0-when-all-dargp-less-than
  (implies (and (all-dargp-less-than args bound)
                (not (consp (nth 0 args))))
           (not (< (nth 0 args) 0)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than dargp-less-than))))

(defthm integerp-of-nth-when-all-dargp-less-than
  (implies (and (all-dargp-less-than args bound)
                (not (consp (nth n args)))
                (natp n)
                (< n (len args)))
           (integerp (nth n args)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than dargp-less-than))))

(defthm true-listp-of-nth-when-all-dargp-less-than
  (implies (and (all-dargp-less-than args bound)
                (natp n)
                (< n (len args)))
           (equal (true-listp (nth n args))
                  (consp (nth n args))))
  :hints (("Goal" :in-theory (enable all-dargp-less-than dargp-less-than))))

(defthm true-listp-of-car-when-all-dargp-less-than
  (implies (and (all-dargp-less-than args bound)
                (natp n)
                (< 0 (len args)))
           (equal (true-listp (car args))
                  (consp (car args))))
  :hints (("Goal" :in-theory (enable all-dargp-less-than dargp-less-than))))

(defthm <-of-nth-0-when-all-dargp-less-than
  (implies (and (all-dargp-less-than args bound)
                (not (consp (nth 0 args)))
                (consp args))
           (< (nth 0 args) bound))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than dargp-less-than))))

(defthmd <-of-car-when-all-dargp-less-than
  (implies (and (all-dargp-less-than vals bound)
                (consp vals)
                (not (consp (car vals))))
           (< (car vals) bound))
  :hints (("Goal" :in-theory (enable all-dargp-less-than dargp-less-than))))

(defthm not-<-of-car-when-all-dargp-less-than-2
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                (all-dargp-less-than vals bound)
                (consp vals)
                (not (consp (car vals))))
           (not (< (car vals) k)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than dargp-less-than))))

;gen?
(defthmd not-<-of-car-when-all-dargp-less-than
  (implies (and (all-dargp-less-than vals bound2)
                (<= bound2 (+ 1 bound))
                (integerp bound)
                (integerp bound2)
                (consp vals)
                (not (consp (car vals))))
           (not (< bound (car vals))))
  :hints (("Goal" :in-theory (enable all-dargp-less-than dargp-less-than))))

;we use consp as the normal form
(defthm integerp-of-car-when-all-dargp-less-than
  (implies (all-dargp-less-than args len)
           (equal (integerp (car args))
                  (if (consp args)
                      (not (consp (car args)))
                      nil)))
  :hints (("Goal" :in-theory (enable all-dargp dargp-less-than))))

;todo: gen some of these rules about nth 0

;; too expensive to leave enabled
(defthmd <-of-nth-when-all-dargp-less-than
  (implies (and (all-dargp-less-than args bound)
                (not (consp (nth n args)))
                (natp n)
                (< n (len args)))
           (< (nth n args) bound))
  :hints (("Goal" :in-theory (enable all-dargp-less-than dargp-less-than))))

(defthm <-of-nth-when-all-dargp-less-than-free
  (implies (and (all-dargp-less-than args bound2)
                (<= bound2 bound)
                (not (consp (nth n args)))
                (natp n)
                (< n (len args)))
           (< (nth n args) bound))
  :hints (("Goal" :in-theory (enable all-dargp-less-than))))

(defthm all-dargp-less-than-monotone
  (implies (and (all-dargp-less-than items m)
                (<= m n))
           (all-dargp-less-than items n))
  :hints (("Goal" :in-theory (enable all-dargp-less-than dargp-less-than))))

(defthm all-dargp-less-than-when-all-myquotep-cheap
  (implies (all-myquotep items)
           (all-dargp-less-than items bound))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than
                                     all-myquotep))))
