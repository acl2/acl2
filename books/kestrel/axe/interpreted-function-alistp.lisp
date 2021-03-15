; Alists mapping functions to definitions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/sequences/defforall" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/alists-light/symbol-alistp" :dir :system)
(include-book "kestrel/alists-light/acons" :dir :system)

(in-theory (disable getprops
                    acons))

;; For each interpreted function, we store its formals and body.
;; TODO: Check that the vars in the body are a subset of the formals.
(defun interpreted-function-infop (info)
  (declare (xargs :guard t))
  (and (true-listp info)
       (= 2 (len info))
       (symbol-listp (first info))
       (pseudo-termp (second info))))

;; Defines all-interpreted-function-infop.
(defforall-simple interpreted-function-infop :guard t)

;;
;; interpreted-function-alistp
;;

;; An interpreted-function-alist maps function names (symbols) to items of the
;; form (list formals body). TODO: Consider making the items in the alist cons
;; pairs instead.

(defund interpreted-function-alistp (alist)
  (declare (xargs :guard t))
  (and (symbol-alistp alist)
       (all-interpreted-function-infop (strip-cdrs alist))))

(defthm interpreted-function-alistp-forward-to-alistp
  (implies (interpreted-function-alistp alist)
           (alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable interpreted-function-alistp))))

(defthm interpreted-function-alistp-forward-to-symbol-alistp
  (implies (interpreted-function-alistp alist)
           (symbol-alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable interpreted-function-alistp))))

(defthm interpreted-function-alistp-of-acons
  (equal (interpreted-function-alistp (acons fn info alist))
         (and (interpreted-function-alistp alist)
              (symbolp fn)
              (interpreted-function-infop info)))
  :hints (("Goal" :in-theory (enable interpreted-function-alistp))))

(defthm interpreted-function-infop-of-cdr-of-assoc-equal
  (implies (and (all-interpreted-function-infop (strip-cdrs interpreted-function-alist))
                (assoc-equal fn interpreted-function-alist))
           (interpreted-function-infop (cdr (assoc-equal fn interpreted-function-alist))))
  :hints (("Goal" :in-theory (disable interpreted-function-infop))))

(defthm interpreted-function-infop-of-lookup-equal-when-interpreted-function-alistp
  (implies (and (interpreted-function-alistp interpreted-function-alist)
                (lookup-equal fn interpreted-function-alist))
           (interpreted-function-infop (lookup-equal fn interpreted-function-alist)))
  :hints (("Goal" ; :induct t
           :in-theory (e/d (interpreted-function-alistp
                            lookup-equal
                            assoc-equal
                            strip-cdrs
                            all-interpreted-function-infop)
                           (interpreted-function-infop)))))

;maybe use a custom lookup and handle this rule of it?
(defthmd true-listp-of-cadr-of-assoc-equal-when-interpreted-function-alistp
  (implies (and (interpreted-function-alistp interpreted-function-alist)
                (assoc-equal fn interpreted-function-alist))
           (true-listp (cadr (assoc-equal fn interpreted-function-alist))))
  :hints (("Goal" :use (:instance interpreted-function-infop-of-cdr-of-assoc-equal)
           :in-theory (e/d (interpreted-function-alistp)
                           (interpreted-function-infop-of-cdr-of-assoc-equal)))))

(defthmd symbol-listp-of-cadr-of-assoc-equal-when-interpreted-function-alistp
  (implies (and (interpreted-function-alistp interpreted-function-alist)
                (assoc-equal fn interpreted-function-alist))
           (symbol-listp (cadr (assoc-equal fn interpreted-function-alist))))
  :hints (("Goal" :use (:instance interpreted-function-infop-of-cdr-of-assoc-equal)
           :in-theory (e/d (interpreted-function-alistp)
                           (interpreted-function-infop-of-cdr-of-assoc-equal)))))

(defthmd pseudo-termp-of-caddr-of-assoc-equal-when-interpreted-function-alistp
  (implies (and (interpreted-function-alistp interpreted-function-alist)
                (assoc-equal fn interpreted-function-alist))
           (pseudo-termp (caddr (assoc-equal fn interpreted-function-alist))))
  :hints (("Goal" :use (:instance interpreted-function-infop-of-cdr-of-assoc-equal)
           :in-theory (e/d (interpreted-function-alistp)
                           (interpreted-function-infop-of-cdr-of-assoc-equal)))))

(defthmd true-listp-of-cadr-of-assoc-equal-when-interpreted-function-alistp
  (implies (and (interpreted-function-alistp interpreted-function-alist)
                (assoc-equal fn interpreted-function-alist))
           (true-listp (cadr (assoc-equal fn interpreted-function-alist))))
  :hints (("Goal" :in-theory (enable interpreted-function-alistp assoc-equal))))

(defthmd symbol-listp-of-cadr-of-assoc-equal-when-interpreted-function-alistp
  (implies (and (interpreted-function-alistp interpreted-function-alist)
                (assoc-equal fn interpreted-function-alist))
           (symbol-listp (cadr (assoc-equal fn interpreted-function-alist))))
  :hints (("Goal" :in-theory (enable interpreted-function-alistp assoc-equal))))

(defthmd consp-of-cdr-of-assoc-equal-when-interpreted-function-alistp
  (implies (and (interpreted-function-alistp interpreted-function-alist)
                (assoc-equal fn interpreted-function-alist))
           (consp (cdr (assoc-equal fn interpreted-function-alist))))
  :hints (("Goal" :in-theory (enable interpreted-function-alistp assoc-equal))))

(defthmd cddr-of-assoc-equal-when-interpreted-function-alistp
  (implies (interpreted-function-alistp interpreted-function-alist)
           (iff (cddr (assoc-equal fn interpreted-function-alist))
                (assoc-equal fn interpreted-function-alist)))
  :hints (("Goal" :in-theory (enable interpreted-function-alistp assoc-equal))))

(defthmd consp-of-cddr-of-assoc-equal-when-interpreted-function-alistp
  (implies (interpreted-function-alistp interpreted-function-alist)
           (iff (consp (cddr (assoc-equal fn interpreted-function-alist)))
                (assoc-equal fn interpreted-function-alist)))
  :hints (("Goal" :in-theory (enable interpreted-function-alistp assoc-equal))))

(defthmd consp-of-car-when-interpreted-function-alistp
  (implies (and (interpreted-function-alistp alist)
                (consp alist))
           (consp (car alist)))
  :hints (("Goal" :in-theory (enable interpreted-function-alistp))))
