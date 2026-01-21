; Applying lookup-equal to a list of keys
;
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lookup-equal")

;; See also lookup-eq-lst (todo: rename that map-lookup-eq).

;; Look up all of the KEYS in the ALIST, returning a list of the results.
(defund map-lookup-equal (keys alist)
  (declare (xargs :guard (and (true-listp keys)
                              (alistp alist))))
  (if (endp keys)
      nil
    (cons (lookup-equal (first keys) alist)
          (map-lookup-equal (rest keys) alist))))

(defthm len-of-map-lookup-equal
  (equal (len (map-lookup-equal terms a))
         (len terms))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

;gen?
(defthm map-lookup-equal-of-cons-of-cons-irrel
  (implies (not (member-equal key keys))
           (equal (map-lookup-equal keys (cons (cons key val) alist))
                  (map-lookup-equal keys alist)))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

(defthm map-lookup-equal-when-not-consp
  (implies (not (consp keys))
           (equal (map-lookup-equal keys alist)
                  nil))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

(defthm car-of-map-lookup-equal
  (equal (car (map-lookup-equal keys alist))
         (if (consp keys)
             (lookup-equal (car keys) alist)
           nil))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

(defthm map-lookup-equal-of-cons
  (equal (map-lookup-equal (cons key keys) alist)
         (cons (lookup-equal key alist)
               (map-lookup-equal keys alist)))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

(defthm map-lookup-equal-of-append
  (equal (map-lookup-equal (append keys1 keys2) alist)
         (append (map-lookup-equal keys1 alist)
                 (map-lookup-equal keys2 alist)))
  :hints (("Goal" :in-theory (enable map-lookup-equal append))))

(defthm cdr-of-assoc-equal-of-pairlis$-of-map-lookup-equal
  (implies (member-equal key keys)
           ;; can we remove the cdrs here?:
           (equal (cdr (assoc-equal key (pairlis$ keys (map-lookup-equal keys a))))
                  (cdr (assoc-equal key a))))
  :hints (("Goal" :in-theory (enable pairlis$
                                     map-lookup-equal
                                     lookup-equal ;todo
                                     ))))

(defthm map-lookup-equal-of-pairlis$-same
  (implies (no-duplicatesp-equal keys)
           (equal (map-lookup-equal keys (pairlis$ keys vals))
                  (take (len keys) vals)))
  :hints (("Goal" :in-theory (enable map-lookup-equal pairlis$ no-duplicatesp-equal take))))
