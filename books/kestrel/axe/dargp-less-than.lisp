; Bounded dag args
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

(include-book "kestrel/utilities/myquotep" :dir :system)
(include-book "dargp")

;; Recognize an argument to a function in a DAG node that is a function call
(defund dargp-less-than (item bound)
  (declare (xargs :guard (natp bound)
                  :split-types t)
           (type (integer 0 *) bound))
  (or (myquotep item)
      (and (natp item)
           (< (the (integer 0 *) item)
              bound))))

(defthm dargp-less-than-forward
  (implies (dargp-less-than item bound)
           (or (natp item)
               (consp item)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable dargp-less-than))))

(defthm len-when-dargp-less-than
  (implies (dargp-less-than item bound)
           (equal (len item)
                  (if (consp item)
                      2
                    0)))
  :hints (("Goal" :in-theory (enable dargp-less-than))))

(defthm dargp-less-than-when-consp-cheap
  (implies (consp item)
           (equal (dargp-less-than item bound)
                  (myquotep item)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable dargp-less-than))))

(defthm dargp-less-than-when-not-consp-cheap
  (implies (not (consp item))
           (equal (dargp-less-than item bound)
                  (and (natp item)
                       (< item bound))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable dargp-less-than))))

(defthm dargp-less-than-when-natp-cheap
  (implies (natp item)
           (equal (dargp-less-than item bound)
                  (< item bound)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable dargp-less-than))))

(defthmd dargp-less-than-when-natp
  (implies (natp item)
           (equal (dargp-less-than item bound)
                  (< item bound)))
  :hints (("Goal" :in-theory (enable dargp-less-than))))

(defthm dargp-less-than-when-quotep-cheap
  (implies (and (syntaxp (quotep item))
                (myquotep item))
           (dargp-less-than item bound))
  :hints (("Goal" :in-theory (enable dargp-less-than))))

(defthmd dargp-less-than-when-myquotep
  (implies (myquotep item)
           (dargp-less-than item bound))
  :hints (("Goal" :in-theory (enable dargp-less-than))))

;we go to consp as the normal form
(defthm integerp-when-dargp-less-than
  (implies (dargp-less-than item bound)
           (equal (integerp item)
                  (not (consp item)))))

(defthm dargp-less-than-forward-to-<
  (implies (and (dargp-less-than item bound)
                (not (consp item)))
           (< item bound))
  :rule-classes :forward-chaining)

;; Keep disabled by default
(defthmd <-when-dargp-less-than
  (implies (and (dargp-less-than item bound)
                (not (consp item)))
           (< item bound)))

;disable?
(defthm nonneg-when-dargp-less-than
  (implies (dargp-less-than item bound)
           (<= 0 item)))

;we go to consp as the normal form
(defthm myquotep-when-dargp-less-than
  (implies (dargp-less-than item bound)
           (equal (myquotep item)
                  (consp item))))

(defthm dargp-when-dargp-less-than
  (implies (dargp-less-than item bound) ;bound is a free var
           (dargp item))
  :hints (("Goal" :in-theory (enable dargp-less-than))))

(defthm dargp-less-than-mono
  (implies (and (dargp-less-than items bound2)
                (<= bound2 bound))
           (dargp-less-than items bound))
  :hints (("Goal" :in-theory (enable dargp-less-than))))

(defthm dargp-less-than-when-equal-of-car-and-quote
  (implies (equal 'quote (car item))
           (equal (dargp-less-than item bound)
                  (myquotep item)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable dargp-less-than))))

(defthm dargp-less-than-of-list-of-quote
  (dargp-less-than (cons 'quote (cons x nil)) bound)
  :hints (("Goal" :in-theory (enable dargp-less-than))))

(defthmd dargp-less-than-when-dargp
  (implies (dargp item)
           (equal (dargp-less-than item bound)
                  (if (consp item)
                      t
                    (< item bound))))
  :hints (("Goal" :in-theory (enable dargp-less-than))))
