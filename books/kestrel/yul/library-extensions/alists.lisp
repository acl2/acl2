; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Extensions of the alist library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If a CONS pair is in an alist,
; the CAR is in the STRIP-CARS list
; and the CDR is in the STRIP-CDRS list.
; This does not actually require the alist to satisfy ALISTP.

(defthmd member-of-strip-cars-when-cons-member
  (implies (member-equal (cons a b) alist)
           (member-equal a (strip-cars alist))))

(defthmd member-of-strip-cdrs-when-cons-member
  (implies (member-equal (cons a b) alist)
           (member-equal b (strip-cdrs alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Conversely:
; if something is in the STRIP-CARs list,
; there must be a CONS pair in the alist with that value as CAR;
; if something is in the STRIP-CDRS list,
; there must be a CONS pair in the alist with the value as CDR.
; We introduce functions that retrieve the CDR and CAR (respectively)
; of the CONS pair in question.
; None of this requires the alist to satisfy ALISTP.

(defund member-strip-cars-find-cdr (a alist)
  (cond ((atom alist) nil)
        ((equal a (caar alist)) (cdar alist))
        (t (member-strip-cars-find-cdr a (cdr alist)))))

(defund member-strip-cdrs-find-car (b alist)
  (cond ((atom alist) nil)
        ((equal b (cdar alist)) (caar alist))
        (t (member-strip-cdrs-find-car b (cdr alist)))))

(defthmd member-strip-cars-find-cdr-membership
  (implies (and (alistp alist)
                (member-equal a (strip-cars alist)))
           (member-equal (cons a (member-strip-cars-find-cdr a alist)) alist))
  :hints (("Goal" :in-theory (enable member-strip-cars-find-cdr))))

(defthmd member-strip-cdrs-find-car-membership
  (implies (and (alistp alist)
                (member-equal b (strip-cdrs alist)))
           (member-equal (cons (member-strip-cdrs-find-car b alist) b) alist))
  :hints (("Goal" :in-theory (enable member-strip-cdrs-find-car))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If an alist is a subset of another,
; the CARs and CDRs of the first are a subset of the ones of the second.

(defruled subsetp-equal-of-strip-cars
  (implies (and (alistp x)
                (alistp y)
                (subsetp-equal x y))
           (subsetp-equal (strip-cars x)
                          (strip-cars y)))
  :prep-lemmas
  ((defrule lemma
     (implies (and (alistp x)
                   (member-equal a x))
              (member-equal (car a) (strip-cars x))))))

(defruled subsetp-equal-of-strip-cdrs
  (implies (and (alistp x)
                (alistp y)
                (subsetp-equal x y))
           (subsetp-equal (strip-cdrs x)
                          (strip-cdrs y)))
  :prep-lemmas
  ((defrule lemma
     (implies (and (alistp x)
                   (member-equal a x))
              (member-equal (cdr a) (strip-cdrs x))))))
