; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/defrule" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule assoc-equal-of-revappend-under-iff
  (implies (or (alistp x)
               key)
           (iff (assoc-equal key (revappend x y))
                (or (assoc-equal key x)
                    (assoc-equal key y))))
  :induct t
  :enable revappend)

(defrule assoc-equal-of-reverse-under-iff
  (implies (or (alistp alist)
               key)
           (iff (assoc-equal key (reverse alist))
                (assoc-equal key alist)))
  :enable reverse)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled assoc-equal-of-revappend-cdr
  (implies (and (or (alistp alist0)
                    key)
                (or (assoc-equal key (cdr alist0))
                    (not (equal (caar alist0) key))))
           (equal (assoc-equal key (revappend (cdr alist0) alist1))
                  (assoc-equal key (revappend alist0 alist1))))
  :induct t
  :enable (revappend
           acl2::revappend-normalize-acc))

(defrule assoc-equal-of-revappend-when-assoc-equal-cdr-cheap
  (implies (and (assoc-equal key (cdr alist0))
                (or (alistp alist0)
                    key))
           (equal (assoc-equal key (revappend alist0 alist1))
                  (assoc-equal key (revappend (cdr alist0) alist1))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :by assoc-equal-of-revappend-cdr)

;;;;;;;;;;;;;;;;;;;;

(defruled assoc-equal-of-reverse-cdr
  (implies (and (or (alistp alist)
                    key)
                (or (assoc-equal key (cdr alist))
                    (not (equal (caar alist) key))))
           (equal (assoc-equal key (reverse alist))
                  (assoc-equal key (reverse (cdr alist)))))
  :use (:instance assoc-equal-of-revappend-cdr
                  (alist0 alist)
                  (alist1 nil))
  :enable reverse)

(defrule assoc-equal-of-reverse-when-assoc-equal-cdr-cheap
  (implies (and (assoc-equal key (cdr alist))
                (or (alistp alist)
                    key))
           (equal (assoc-equal key (reverse alist))
                  (assoc-equal key (reverse (cdr alist)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :by assoc-equal-of-reverse-cdr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled assoc-equal-of-revappend-when-not-assoc-equal-of-cdr
  (implies (and (alistp alist0)
                (not (assoc-equal key (cdr alist0))))
           (equal (assoc-equal key (revappend alist0 alist1))
                  (assoc-equal key (append alist0 alist1)))))

(defruled assoc-equal-of-reverse-when-not-assoc-equal-of-cdr
  (implies (and (alistp alist)
                (not (assoc-equal key (cdr alist))))
           (equal (assoc-equal key (reverse alist))
                  (assoc-equal key alist)))
  :enable reverse)

(defrule assoc-equal-of-reverse-when-not-assoc-equal-of-cdr-cheap
  (implies (and (not (assoc-equal key (cdr alist)))
                (alistp alist))
           (equal (assoc-equal key (reverse alist))
                  (assoc-equal key alist)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :by assoc-equal-of-reverse-when-not-assoc-equal-of-cdr)
