; A lightweight book about the built-in function alistp
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

(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(in-theory (disable alistp))

(defthm alistp-of-cons
  ;; [Jared] tweaked variable names for compatibility with std
  (equal (alistp (cons a x))
         (and (consp a)
              (alistp x)))
  :hints (("Goal" :in-theory (enable alistp))))

(defthm alistp-of-acons
  (equal (alistp (acons key datum alist))
         (alistp alist))
  :hints (("Goal" :in-theory (enable alistp acons))))

(defthm alistp-of-append
  ;; [Jared] changed for compatibility with std/alists/alistp.lisp
  (equal (alistp (append x y))
         (and (alistp (true-list-fix x))
              (alistp y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm alistp-true-list-fix
  (implies (alistp x)
           (alistp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm alistp-of-union-equal
  (equal (alistp (union-equal x y))
         (and (alistp (true-list-fix x))
              (alistp y)))
  :hints (("Goal" :in-theory (enable union-equal))))

;todo: name clash with std without the -2
(defthm alistp-of-revappend-2
  (equal (alistp (revappend x y))
         (and (alistp (true-list-fix x))
              (alistp y)))
  :hints (("Goal" :in-theory (enable alistp revappend))))

;todo: name clash with std without the -2
(defthm alistp-of-reverse-2
  (equal (alistp (reverse x))
         (if (stringp x)
             nil ; unusual case
           (alistp (true-list-fix x))))
  :hints (("Goal" :in-theory (enable alistp))))

(defthmd consp-of-nth-when-alistp
  (implies (alistp alist)
           (equal (consp (nth n alist))
                  (< (nfix n) (len alist))))
  :hints (("Goal" :in-theory (enable nth len))))

(defthmd consp-of-nth-when-alistp-cheap
  (implies (alistp alist)
           (equal (consp (nth n alist))
                  (< (nfix n) (len alist))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable nth len))))

(defthm alistp-of-cdr
  (implies (alistp x)
           (alistp (cdr x)))
  :hints (("Goal" :in-theory (enable alistp))))

;; Avoid name clash with the version in std
;; Keep disabled to avoid inappropriate backchaining to alistp.
(defthmd consp-of-car-when-alistp-alt
  (implies (alistp x)
           (equal (consp (car x))
                  (consp x)))
  :hints (("Goal" :in-theory (enable alistp))))

(defthm consp-of-car-when-alistp-cheap
  (implies (alistp x)
           (equal (consp (car x))
                  (consp x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable alistp))))

;; Keep disabled to avoid inappropriate backchaining to alistp.
(defthmd car-when-alistp-iff
  (implies (alistp x)
           (iff (car x)
                (consp x)))
  :hints (("Goal" :in-theory (enable alistp))))

(defthm car-when-alistp-iff-cheap
  (implies (alistp x)
           (iff (car x)
                (consp x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable alistp))))

(defthm alistp-of-remove1-equal
  (implies (alistp alist)
           (alistp (remove1-equal pair alist)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

;; (defthm len-of-car-when-alistp-cheap
;;   (implies (alistp alist)
;;            (equal (len (car alist))
;;                   (if (consp alist)
;;                       1
;;                     0)))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (enable alistp))))
