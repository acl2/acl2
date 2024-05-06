; A lightweight book about the built-in function array1p
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

(include-book "constants")
(include-book "alen1")
(local (include-book "dimensions"))
(local (include-book "bounded-integer-alistp"))
(local (include-book "maximum-length"))
(local (include-book "header"))

(in-theory (disable array1p
                    array1p-linear ; does not reflect our normal form for alen1
                    ))

;; This is perhaps how array1p should be defined (but see the comment about
;; array1p in the ACL2 sources).
(defthmd array1p-rewrite
  (equal (array1p name l)
         (and
          (symbolp name)
          (alistp l)
          (let
              ((header-keyword-list (cdr (header name l))))
            (and
             (keyword-value-listp header-keyword-list)
             (let* ((dimensions (dimensions name l))
                    (len (car dimensions))
                    (maximum-length (maximum-length name l)))
               (and (true-listp dimensions)
                    (equal (len dimensions) 1)
                    (integerp len)
                    (integerp maximum-length)
                    (< 0 len)
                    (< len maximum-length)
                    (<= maximum-length *max-array-maximum-length*)
                    (bounded-integer-alistp l len)))))))
  :hints (("Goal" :in-theory (e/d (array1p header dimensions maximum-length)
                                  (dimensions-intro
                                   maximum-length-intro)))))

;; Here we also introduce alen1
(defthmd array1p-rewrite2
  (equal (array1p name l)
         (and
          (symbolp name)
          (alistp l)
          (let
              ((header-keyword-list (cdr (header name l))))
            (and
             (keyword-value-listp header-keyword-list)
             (let* ((dimensions (dimensions name l))
                    (len (alen1 name l))
                    (maximum-length (maximum-length name l)))
               (and (true-listp dimensions)
                    (equal (len dimensions) 1)
                    (integerp len)
                    (integerp maximum-length)
                    (< 0 len)
                    (< len maximum-length)
                    (<= maximum-length *max-array-maximum-length*)
                    (bounded-integer-alistp l len)))))))
  :hints (("Goal" :in-theory (enable array1p-rewrite))))

(defthmd normalize-array1p-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (array1p name l)
                  (and (symbolp name)
                       (array1p :fake-name l))))
  :hints (("Goal" :in-theory (enable array1p))))

(defthm array1p-of-cons-header
  (equal (ARRAY1P NAME2 (CONS (LIST :HEADER
                                    :DIMENSIONS (LIST dim)
                                    :MAXIMUM-LENGTH max
                                    :DEFAULT NIL
                                    :NAME NAME)
                              ALIST))
         (and (bounded-integer-alistp alist dim)
              (posp dim)
              (< dim max)
              (symbolp name2)
              (<= MAX *max-array-maximum-length*)
              (integerp max)))
  :hints (("Goal" :in-theory (enable ARRAY1P-rewrite))))

(defthm array1p-of-acons-header
  (equal (ARRAY1P NAME2 (aCONS :header (LIST
                                         :DIMENSIONS (LIST dim)
                                         :MAXIMUM-LENGTH max
                                         :DEFAULT NIL
                                         :NAME NAME)
                               ALIST))
         (and (bounded-integer-alistp alist dim)
              (posp dim)
              (< dim max)
              (symbolp name2)
              (<= MAX *max-array-maximum-length*)
              (integerp max)))
  :hints (("Goal" :in-theory (enable ARRAY1P-rewrite))))

(defthm array1p-forward-to-<=-of-alen1
  (implies (array1p array-name array)
           (<= (alen1 array-name array)
               *max-1d-array-length*))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable array1p-rewrite))))

(defthm array1p-forward-to-<=-of-alen1-2
  (implies (array1p array-name array)
           (<= 1 (alen1 array-name array)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable array1p-rewrite))))

(defthm array1p-of-cons-of-header-and-nil
  (equal (array1p array-name
                  (list (list :header
                              :dimensions dims
                              :maximum-length maximum-length
                              :default default
                              :name array-name)))
         (and (symbolp array-name)
              (equal 1 (len dims))
              (true-listp dims)
              (posp (car dims))
              (natp maximum-length)
              (< (car dims) maximum-length)
              (<= maximum-length *max-array-maximum-length*)))
  :hints (("Goal" :in-theory (enable array1p-rewrite))))

(defthm assoc-equal-when-array1p-and-out-of-bounds
  (implies (and (<= (alen1 name array) n)
                (integerp n)
                (array1p name2 array))
           (equal (assoc-equal n array)
                  nil))
  :hints (("Goal" :in-theory (enable array1p-rewrite
                                     not-assoc-equal-when-bounded-integer-alistp-out-of-bounds
                                     normalize-alen1-name))))
