; A lightweight book about the built-in function aref1
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "alen1")
(include-book "bounded-integer-alistp")
(local (include-book "default"))
(local (include-book "dimensions"))
(local (include-book "array1p"))

(in-theory (disable aref1))

(defthmd normalize-aref1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aref1 name l n)
                  (aref1 :fake-name l n)))
  :hints (("Goal" :in-theory (enable aref1 normalize-default-name))))

;; Disabled since this can be expensive and is rarely needed.
(defthmd aref1-when-too-large
  (implies (and (<= (alen1 array-name array) n)
                (array1p array-name array)
                (natp n))
           (equal (aref1 array-name array n)
                  (default array-name array)))
  :hints (("Goal" :in-theory (enable AREF1 ARRAY1P-rewrite HEADER not-assoc-equal-when-bounded-integer-alistp-out-of-bounds))))

(defthm aref1-when-too-large-cheap
  (implies (and (<= (alen1 array-name array) n)
                (array1p array-name array)
                (natp n))
           (equal (aref1 array-name array n)
                  (default array-name array)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (enable aref1-when-too-large))))

(defthm aref1-of-cons-of-cons-of-header
  (implies (natp n)
           (equal (aref1 array-name (cons (cons :header header) alist) n)
                  (if (assoc-equal n alist)
                      (aref1 array-name alist n)
                    (cadr (assoc-keyword :default header)))))
  :hints (("Goal" :in-theory (enable aref1 header))))

(defthm aref1-of-acons-of-header
  (implies (natp n)
           (equal (aref1 array-name (acons :header header alist) n)
                  (if (assoc-equal n alist)
                      (aref1 array-name alist n)
                    (cadr (assoc-keyword :default header)))))
  :hints (("Goal" :in-theory (enable acons))))

;; This one has no IF in the RHS
(defthm aref1-of-cons-of-cons-of-header-alt
  (implies (and ;(natp n)
                (equal (default array-name array)
                       (cadr (assoc-keyword :default header-args))))
           (equal (aref1 array-name (cons (cons :header header-args) array) n)
                  (aref1 array-name array n)))
  :hints (("Goal" :in-theory (enable aref1 header))))

(defthmd aref1-when-not-assoc-equal
  (implies (not (assoc-equal n alist))
           (equal (aref1 array-name alist n)
                  (default array-name alist)))
  :hints (("Goal" :in-theory (enable aref1))))
