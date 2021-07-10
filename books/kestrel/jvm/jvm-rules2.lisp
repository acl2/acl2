; More rules about the jvm
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Organize the material in this book

(include-book "jvm-rules")
(local (include-book "kestrel/lists-light/len" :dir :system))

;use a defforall-simple?
(defun all-non-nullp (refs)
  (if (atom refs)
      t
    (and (not (null-refp (first refs)))
         (all-non-nullp (rest refs)))))

(defthm not-null-refp-of-nth-when-all-non-nullp
  (implies (all-non-nullp refs)
           (not (null-refp (nth n refs))))
  :hints (("Goal" :in-theory (enable (:i nth)))))

;use a defforall-simple?
(defun all-bound-in-rkeys (refs heap)
  (if (atom refs)
      t
    (and (set::in (first refs) (rkeys heap))
         (all-bound-in-rkeys (rest refs) heap))))

(defthm in-rkeys-of-nth-when-all-bound-in-rkeys
  (implies (and (all-bound-in-rkeys refs heap)
                (natp n)
                (< n (len refs)))
           (set::in (nth n refs) (rkeys heap)))
  :hints (("Goal" :in-theory (enable (:i nth)))))

(defund all-addresses-bound-to-object-of-type
  (contents element-type heap)
  (declare (xargs :guard (and (true-listp contents)
                              (jvm::typep element-type)
                              (jvm::heapp heap))))
  (if (endp contents)
      t
      (let ((item (first contents)))
           (and (addressp item)
                (equal element-type (get-class item heap))
                (all-addresses-bound-to-object-of-type
                 (rest contents)
                 element-type heap)))))

(defthm all-null-or-addresses-bound-to-object-of-type-when-all-non-nullp
  (implies (all-non-nullp items)
           (equal (all-null-or-addresses-bound-to-object-of-type items element-type heap)
                  (all-addresses-bound-to-object-of-type items element-type heap)))
  :hints (("Goal" :in-theory (enable all-addresses-bound-to-object-of-type))))

(defthm get-field-of-nth-when-all-addresses-bound-to-object-of-type
  (implies (and (all-addresses-bound-to-object-of-type items element-type heap)
                (natp n)
                (< n (len items)))
           (equal (get-field (nth n items) '(:special-data . :class) heap)
                  element-type))
  :hints (("Goal" :in-theory (enable all-addresses-bound-to-object-of-type
                                      (:I nth)))))

(defthm get-class-of-nth-of-array-contents-when-array-refp
  (implies (and (array-refp ref dims class-name heap) ;ref is an array of object refs
                (all-non-nullp (array-contents ref heap)) ;none of the object refs are null
                (equal 1 (len dims))
                (true-listp dims)
                (posp (first dims))
                (natp n)
                (< n (first dims))
                (jvm::class-namep class-name))
           (equal (GET-FIELD (NTH n
                                  (GET-FIELD ref
                                             (array-contents-pair)
                                             HEAP))
                             '(:SPECIAL-DATA . :CLASS)
                             HEAP)
                  class-name))
  :hints (("Goal" :cases ((null-refp (NTH N
                                          (GET-FIELD REF
                                                     (array-contents-pair)
                                                     HEAP))))
           :in-theory (e/d (array-refp array-ref-listp ARRAY-CONTENTS-OKP)
                           (null-refp))
           :expand ((ARRAY-REFP REF dims CLASS-NAME HEAP)))))

;move
(defthm GET-INTERNED-STRING-of-myif
  (equal (JVM::GET-INTERNED-STRING STRING (myif test INTERN-TABLE1 intern-table2))
         (myif test
               (JVM::GET-INTERNED-STRING STRING INTERN-TABLE1)
               (JVM::GET-INTERNED-STRING STRING intern-table2)))
  :hints (("Goal" :in-theory (enable myif))))

;move
(defthm jvm::get-interned-string-of-set-interned-string-diff
  (implies (not (equal string1 string2))
           (equal (jvm::get-interned-string string1 (jvm::set-interned-string string2 ad intern-table))
                  (jvm::get-interned-string string1 intern-table)))
  :hints (("Goal" :in-theory (enable jvm::set-interned-string
                                     jvm::get-interned-string))))

;; Test whether the type of the indicated field of the object at AD is TYPE.
;; AD should be non-null
(defun field-has-type (ad class-field-pair type heap)
  (let ((ref (get-field ad class-field-pair heap)))
    (and (not (null-refp ref))
         (equal (get-field ref '(:special-data . :class) heap)
                type))))


;;all the ADS are references to objects whose FIELD field is an object of type TYPE in HEAP
;; The ADS should all be non-null.
(defun all-fields-have-type (ads class-field-pair type heap)
  (if (endp ads)
      t
    (and (field-has-type (first ads) class-field-pair type heap)
         (all-fields-have-type (rest ads) class-field-pair type heap))))

(defthm get-class-when-all-fields-have-type
  (implies (and (all-fields-have-type ads field type heap)
                (natp index)
                (< index (len ads)))
           (equal (get-field (get-field (nth index ads) field heap) '(:special-data . :class) heap)
                  type))
  :hints (("Goal" :in-theory (e/d (nth) (;nth-of-cdr
                                         )))))


(defthm in-of-rkeys-when-all-fields-have-type
  (implies (and (all-fields-have-type ads field type heap)
                (natp index)
                (< index (len ads))
                type ;type can't be nil
                )
           (set::in (get-field (nth index ads) field heap) (rkeys heap)))
  :hints (("Goal" :in-theory (e/d (nth) (;nth-of-cdr
                                         )))))

(defthm not-null-refp-when-all-fields-have-type
  (implies (and (all-fields-have-type ads field type heap)
                (natp index)
                (< index (len ads)))
           (not (null-refp (get-field (nth index ads) field heap))))
  :hints (("Goal" :in-theory (e/d (nth) (;nth-of-cdr
                                         )))))

(defthm not-equal-nth-new-ad-when-class-non-nil
  (implies (get-field x '(:special-data . :class) heap)
           (not (equal x (nth-new-ad n (rkeys heap)))))
  :hints (("Goal" :in-theory (enable get-field-when-not-in-rkeys))))

(defthm not-equal-nth-new-ad-when-class-non-nil-alt
  (implies (get-field x '(:special-data . :class) heap)
           (not (equal (nth-new-ad n (rkeys heap)) x)))
  :hints (("Goal" :in-theory (enable get-field-when-not-in-rkeys))))

(defthm not-equal-new-ad-when-class-non-nil
  (implies (get-field x '(:special-data . :class) heap)
           (not (equal x (new-ad (rkeys heap)))))
  :hints (("Goal" :in-theory (enable get-field-when-not-in-rkeys))))

(defthm not-equal-new-ad-when-class-non-nil-alt
  (implies (get-field x '(:special-data . :class) heap)
           (not (equal (new-ad (rkeys heap)) x)))
  :hints (("Goal" :in-theory (enable get-field-when-not-in-rkeys))))
