; A library for reasoning about ACL2 arrays (aref1, aset1, etc.)
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

(include-book "kestrel/lists-light/reverse-list" :dir :system) ;make local?
(include-book "bounded-nat-alists")
(include-book "alen1")
(include-book "aref1")
(include-book "aset1")
(include-book "default")
(include-book "header")
(include-book "array1p")
(include-book "bounded-integer-alistp")
(include-book "dimensions") ; make local?
(include-book "compress1") ; make local?
(include-book "compress11") ; make local?
(include-book "maximum-length") ; make local?
(include-book "make-empty-array")
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/utilities/assoc-keyword" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;; We disable functions about arrays, because this book introduces rules about
;; them:
(in-theory (disable dimensions
                    header
                    default
                    maximum-length
                    array1p
                    aset1
                    aref1
                    compress1
                    compress11
                    bounded-integer-alistp
                    array-order))

(local (in-theory (disable true-listp
                           assoc-keyword)))

;;;
;;; Normalize names (most of these functions ignore the name param)
;;;

(local (in-theory (enable normalize-alen1-name
                          normalize-header-name
                          normalize-default-name
                          normalize-maximum-length-name
                          normalize-dimensions-name
                          normalize-compress11-name
                          normalize-compress1-name
                          normalize-aref1-name
                          normalize-aset1-name)))

(defthmd normalize-compress211-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress211 name l i x j default)
                  (compress211 :fake-name l i x j default)))
  :hints (("Goal" :in-theory (enable compress211))))

(local (in-theory (enable normalize-compress211-name)))

(defthmd normalize-compress21-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress21 name l n i j default)
                  (compress21 :fake-name l n i j default)))
  :hints (("Goal" :in-theory (enable compress21))))

(local (in-theory (enable normalize-compress21-name)))

(defthmd normalize-compress2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress2 name l)
                  (compress2 :fake-name l)))
  :hints (("Goal" :in-theory (enable compress2))))

(local (in-theory (enable normalize-compress2-name)))

(defthmd normalize-aset2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aset2 name l i j val)
                  (aset2 :fake-name l i j val)))
  :hints (("Goal" :in-theory (enable aset2))))

;; (local (in-theory (enable normalize-aset2-name)))

(defthmd normalize-aref2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aref2 name l i j)
                  (aref2 :fake-name l i j)))
  :hints (("Goal" :in-theory (enable aref2))))

;; (local (in-theory (enable normalize-aref2-name)))

(local (in-theory (enable normalize-array1p-name)))

(defthmd normalize-array2p-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (array2p name l)
                  (and (symbolp name)
                       (array2p :fake-name l))))
  :hints (("Goal" :in-theory (enable array2p))))

;; (local (in-theory (enable normalize-array2p-name)))

(local
  (defthm alistp-of-reverse-list
    (equal (alistp (reverse-list x))
           (alistp (true-list-fix x)))
    :hints (("Goal" :in-theory (enable alistp reverse-list)))))

;; (defthm alistp-of-reverse-list
;;   (implies (alistp x)
;;            (alistp (reverse-list x)))
;;   :hints (("Goal" :in-theory (enable reverse-list))))

(local
  (defthm assoc-equal-of-reverse-list-iff
    (implies (or (alistp x)
                 key)
             (iff (assoc-equal key (reverse-list x))
                  (assoc-equal key x)))
    :hints (("Goal" :in-theory (enable reverse-list)))))

(local (in-theory (enable revappend-becomes-append-of-reverse-list)))

;use list fix in concl?
(defthm bounded-integer-alistp-of-reverse-list
  (implies (true-listp x)
           (equal (bounded-integer-alistp (reverse-list x) n)
                  (bounded-integer-alistp x n)))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp reverse-list))))

(defthmd assoc-equal-when-assoc-equal-of-reverse-list
  (implies (and (assoc-equal key (reverse-list alist))
                (alistp alist))
           (assoc-equal key alist))
  :hints (("Goal" :in-theory (enable assoc-equal reverse-list))))

;; ;might be better to strip the keys and call NO-DUPLICATESP?
(defun myduplicate-keysp (alist)
  (cond ((endp alist) nil)
        ((assoc-equal (caar alist) (cdr alist))
         t)
        (t (myduplicate-keysp (cdr alist)))))

(defthm assoc-equal-of-reverse-list
  (implies (and (not (myduplicate-keysp alist))
                (alistp alist))
           (equal (assoc-equal key (reverse-list alist))
                  (assoc-equal key alist)))
  :hints (("Goal" :in-theory (enable assoc-equal reverse-list
                                     assoc-equal-when-assoc-equal-of-reverse-list))))


;; ;can be expensive?
;; (defthmd consp-when-true-listp-and-non-nil
;;   (implies (and x ;limit?
;;                 (true-listp x))
;;            (consp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm natp-of-car-of-assoc-equal
;;   (equal (natp (car (assoc-equal :header array)))
;;          nil)
;;   :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm not-of-myduplicate-keysp-of-compress11
  (not (myduplicate-keysp (compress11 name l i n default)))
  :hints (("Goal" :in-theory (enable compress11))))

;; (in-theory (disable (:i assoc-equal)))

;move this and all the supporting stuff above!
(defthm aref1-of-aset1-same
  (implies (and (array1p array-name array) ;;(alistp array)
                (natp index)
                (< index (alen1 array-name array))
                )
           (equal (aref1 array-name (aset1 array-name2 array index val) index)
                  val))
  :hints (("Goal" :in-theory (e/d (aref1
                                   array1p-rewrite
                                   ;compress1
                                   header
                                   default
                                   aset1
                                   dimensions
                                   alen1)
                                  (dimensions-intro
                                   default-intro
                                   alen1-intro
                                   alen1-intro2)))))

(defthm aref1-of-aset1-diff
  (implies (and (not (equal index1 index2))
                (array1p array-name array)
                (natp index1)
                ;; (< index1 (alen1 array-name array))
                (natp index2)
                (< index2 (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name array index1 val) index2)
                  (aref1 array-name array index2)))
  :hints (("Goal" :in-theory (e/d (aref1
                                   array1p-rewrite
                                   compress1
                                   header
                                   default
                                   aset1
                                   dimensions
                                   alen1)
                                  (dimensions-intro
                                   default-intro
                                   alen1-intro
                                   alen1-intro2)))))

(defthm aref1-of-aset1-both
  (implies (and (array1p array-name array)
                (natp index1)
                (< index1 (alen1 array-name array))
                (natp index2)
                (< index2 (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name array index1 val) index2)
                  (if (equal index1 index2)
                      val
                    (aref1 array-name array index2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Not quite true...
;; (defthm aset1-of-aset1-same
;;   (implies (and (array1p array-name array)
;;                 (natp index)
;;                 (< index (alen1 array-name array)))
;;            (equal (aset1 array-name (aset1 array-name array index val1) index val2)
;;                   (aset1 array-name array index val2)))
;;   :hints (("Goal" :in-theory (e/d (array1p-rewrite
;;                                    compress1
;;                                    header
;;                                    default
;;                                    aset1
;;                                    dimensions
;;                                    alen1)
;;                                   (dimensions-intro
;;                                    alen1-intro
;;                                    alen1-intro2)))))

;; A simple theorem like aset1-of-aset1-same would not be true
(defthm aref1-of-aset1-of-aset1-same
  (implies (and (array1p array-name array)
                (natp index)
                ;; (< index (alen1 array-name array))
                (natp read-index)
                (< read-index (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name (aset1 array-name array index val1) index val2) read-index)
                  (aref1 array-name (aset1 array-name array index val2) read-index)))
  :hints (("Goal" :in-theory (e/d (aref1
                                   array1p-rewrite
                                   compress1
                                   header
                                   default
                                   aset1
                                   dimensions
                                   alen1)
                                  (dimensions-intro
                                   default-intro
                                   alen1-intro
                                   alen1-intro2)))))

(defthm aref1-of-aset1-of-aset1-same-diff
  (implies (and (syntaxp (smaller-termp index2 index1))
                (not (equal index1 index2))
                (array1p array-name array)
                (natp index1)
                (< index1 (alen1 array-name array))
                (natp index2)
                (< index2 (alen1 array-name array))
                (natp read-index)
                (< read-index (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name (aset1 array-name array index1 val1) index2 val2) read-index)
                  (aref1 array-name (aset1 array-name (aset1 array-name array index2 val2) index1 val1) read-index)))
  :hints (("Goal" :in-theory (e/d (aref1
                                   array1p-rewrite
                                   compress1
                                   header
                                   default
                                   aset1
                                   dimensions
                                   alen1)
                                  (dimensions-intro
                                   default-intro
                                   alen1-intro
                                   alen1-intro2)))))

(defthm aref1-of-aset1-of-aset1-same-both
  (implies (and (syntaxp (smaller-termp index2 index1)) ;prevent loops
                (array1p array-name array)
                (natp index1)
                (< index1 (alen1 array-name array))
                (natp index2)
                (< index2 (alen1 array-name array))
                (natp read-index)
                (< read-index (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name (aset1 array-name array index1 val1) index2 val2) read-index)
                  (if (equal index1 index2)
                      (aref1 array-name (aset1 array-name array index2 val2) read-index)
                    (aref1 array-name (aset1 array-name (aset1 array-name array index2 val2) index1 val1) read-index)))))
