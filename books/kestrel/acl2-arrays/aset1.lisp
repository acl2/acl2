; A lightweight book about the built-in function aset1
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

(in-theory (disable aset1))

(include-book "alen1")
(local (include-book "compress1"))
(local (include-book "dimensions"))
(local (include-book "default"))
(local (include-book "header"))
(local (include-book "maximum-length"))

(defthm dimensions-of-aset1
  (equal (dimensions array-name (aset1 array-name array n val))
         (if (eq :header n)
             (cadr (assoc-keyword :dimensions val))
           (dimensions array-name array)))
  :hints (("Goal" :in-theory (enable aset1))))

(defthm default-of-aset1
  (implies (integerp n)
           (equal (default array-name (aset1 array-name array n val))
                  (default array-name array)))
  :hints (("Goal" :in-theory (enable aset1))))

(defthm array1p-of-aset1-simple
  (implies (and (natp index)
                (< index (car (dimensions array-name array))) ; same as (< index (alen1 array-name array))
                (array1p array-name array))
           (array1p array-name (aset1 array-name array index val)))
  :hints (("Goal" :in-theory (e/d (aset1 dimensions header)
                                  (dimensions-intro header-intro)))))

(defthm header-of-aset1
  (implies (integerp n) ;gen?
           (equal (header name (aset1 name l n val))
                  (header name l)))
  :hints (("Goal" :in-theory (enable aset1))))

(defthmd normalize-aset1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aset1 name l n val)
                  (aset1 :fake-name l n val)))
  :hints (("Goal" :in-theory (enable aset1
                                     normalize-compress1-name
                                     normalize-header-name
                                     normalize-maximum-length-name))))

(defthm alen1-of-aset1
  (equal (alen1 array-name (aset1 array-name array n val))
         (if (eq :header n)
             (car (cadr (assoc-keyword :dimensions val)))
           (alen1 array-name array)))
  :hints (("Goal" :in-theory (e/d (alen1)
                                  (alen1-intro alen1-intro2)))))

(defthm array1p-of-aset1
  (implies (and (natp index)
                (< index (alen1 array-name array))
                (array1p array-name array))
           (array1p array-name (aset1 array-name array index val)))
  :hints (("Goal" :in-theory (e/d (aset1
                                   maximum-length-intro
                                   header-intro
                                   normalize-alen1-name ; todo: be consistent on whether these are enabled
                                   )
                                  ()))))
