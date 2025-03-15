; A predicate that checks whether two alists agree on a given list of keys
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "assoc-equal"))
(local (include-book "strip-cars"))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

;; Checks whether ALIST1 and ALIST2 are equivalent wrt the KEYS.  For these
;; purposes, not having a binding for a key is equivalent to binding it to nil.
(defund alists-equiv-on (keys alist1 alist2)
  (if (endp keys)
      t
    (let ((key (first keys)))
      (and (equal (cdr (assoc-equal key alist1)) ; ok if bound to nil in one alist and not bound in the other
                  (cdr (assoc-equal key alist2)))
           (alists-equiv-on (rest keys) alist1 alist2)))))

(defthm alists-equiv-on-when-not-consp
  (implies (not (consp keys))
           (alists-equiv-on keys alist1 alist2))
  :hints (("Goal" :in-theory (enable alists-equiv-on))))

(defthm alists-equiv-on-same
  (alists-equiv-on keys alist1 alist1)
  :hints (("Goal" :in-theory (enable alists-equiv-on))))

(defthm alists-equiv-on-of-union-equal
  (equal (alists-equiv-on (union-equal keys1 keys2) alist1 alist2)
         (and (alists-equiv-on keys1 alist1 alist2)
              (alists-equiv-on keys2 alist1 alist2)))
  :hints (("Goal" :in-theory (enable alists-equiv-on))))

(defthm alists-equiv-on-of-cons-and-cons-same
  (implies (alists-equiv-on keys alist1 alist2)
           (alists-equiv-on keys
                            (cons pair alist1)
                            (cons pair alist2)))
  :hints (("Goal" :in-theory (enable alists-equiv-on))))

(defthm alists-equiv-on-of-cons-and-cons-same-2
  (implies (alists-equiv-on (remove-equal (car pair) keys) alist1 alist2)
           (alists-equiv-on keys
                            (cons pair alist1)
                            (cons pair alist2)))
  :hints (("Goal" :in-theory (enable alists-equiv-on))))

(defthm equal-of-cdr-of-assoc-equal-and-cdr-of-assoc-equal-when-alists-equiv-on
  (implies (and (alists-equiv-on keys alist1 alist2)
                (member-equal key keys))
           (equal (equal (cdr (assoc-equal key alist1))
                         (cdr (assoc-equal key alist2)))
                  t))
  :hints (("Goal" :in-theory (enable alists-equiv-on))))

(local
 (defun cdr-remove-caar-induct (x y)
   (if (endp x)
       (list x y)
     (cdr-remove-caar-induct (cdr x) (remove-equal (caar x) y)))))

(defthm alists-equiv-on-of-append-and-append-same
  (implies (and (alists-equiv-on (set-difference-equal keys (strip-cars alist1))
                                 alist2
                                 alist3)
                (alistp alist1)
;                (no-duplicatesp-equal (strip-cars alist1)) ;drop?
                )
           (alists-equiv-on keys
                            (append alist1 alist2)
                            (append alist1 alist3)))
  :hints (;("subgoal *1/2" :cases ((equal (car keys) (caar alist1))))
          ("Goal" :expand ((STRIP-CARS ALIST1)
                           (ALISTS-EQUIV-ON KEYS (APPEND ALIST1 ALIST2)
                                            (APPEND ALIST1 ALIST3)))
           :induct (cdr-remove-caar-induct ALIST1 keys)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable append alists-equiv-on))))

;;rename
(defthm alists-equiv-on-of-cons-same
  (implies (alists-equiv-on keys
                            a2
                            a)
           (alists-equiv-on keys
                            (cons (cons key (cdr (assoc-equal key a))) a2)
                            a))
  :hints (("Goal" :in-theory (enable alists-equiv-on))))

(defthm alists-equiv-on-of-append-arg1
  (implies (alistp x)
           (equal (alists-equiv-on keys (append x y) z)
                  (and (alists-equiv-on (intersection-equal keys (strip-cars x))
                                        x
                                        z)
                       (alists-equiv-on (set-difference-equal keys (strip-cars x))
                                        y
                                        z))))
  :hints (("Goal" :in-theory (enable alists-equiv-on
                                     (:d set-difference-equal)
                                     (:i intersection-equal)
                                     intersection-equal
                                     member-equal-of-strip-cars-iff))))

(defthm alists-equiv-on-of-append-arg2
  (implies (alistp x)
           (equal (alists-equiv-on keys z (append x y))
                  (and (alists-equiv-on (intersection-equal keys (strip-cars x))
                                        z
                                        x)
                       (alists-equiv-on (set-difference-equal keys (strip-cars x))
                                        z
                                        y))))
  :hints (("Goal" :in-theory (enable alists-equiv-on
                                     (:d set-difference-equal)
                                     intersection-equal
                                     member-equal-of-strip-cars-iff))))

(defthm alists-equiv-on-of-alists-equiv-on-when-alists-equiv-on-arg1
  (implies (alists-equiv-on keys1 alist1 alist2)
           (alists-equiv-on (intersection-equal keys1 keys2) alist1 alist2))
  :hints (("Goal" :in-theory (enable alists-equiv-on))))

(defthm alists-equiv-on-of-alists-equiv-on-when-alists-equiv-on-arg2
  (implies (alists-equiv-on keys2 alist1 alist2)
           (alists-equiv-on (intersection-equal keys1 keys2) alist1 alist2))
  :hints (("Goal" :in-theory (enable alists-equiv-on intersection-equal))))
