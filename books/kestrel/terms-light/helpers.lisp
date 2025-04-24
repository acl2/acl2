; Helper rules for the proofs in this directory
;
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These mix various notions, about terms, alists, etc.
;; TODO: Separate out this stuff better

(include-book "no-nils-in-termp")
(include-book "lambdas-closed-in-termp")
(include-book "filter-formals-and-actuals")
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "non-trivial-formals-and-args")
(include-book "non-trivial-formals")
(include-book "trivial-formals")
(include-book "kestrel/alists-light/map-lookup-equal" :dir :system)
(include-book "kestrel/alists-light/alists-equiv-on" :dir :system)
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))

(defthm no-nils-in-termp-of-lookup-equal
  (implies (no-nils-in-termsp (strip-cdrs alist))
           (iff (no-nils-in-termp (lookup-equal key alist))
                (member-equal key (strip-cars alist)))))

(defthm no-nils-in-termsp-of-map-lookup-equal
  (implies (no-nils-in-termsp (strip-cdrs alist))
           (iff (no-nils-in-termsp (map-lookup-equal keys alist))
                (subsetp-equal keys (strip-cars alist))))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

(defthm no-duplicate-lambda-formals-in-termsp-of-map-lookup-equal
  (implies (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist))
           (no-duplicate-lambda-formals-in-termsp (map-lookup-equal keys alist)))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

;strong
(defthm mv-nth-0-of-non-trivial-formals-and-args
  (equal (mv-nth 0 (non-trivial-formals-and-args formals args))
         (non-trivial-formals formals args))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args
                                     non-trivial-formals))))

(defthm formals-get-shorter ;rename
 (implies
  (and
   (symbol-listp formals)
   (pseudo-term-listp actuals)
   (equal (len formals) (len actuals)))
  (<=
   (len
    (non-trivial-formals
     (mv-nth 0 (filter-formals-and-actuals formals actuals formals-to-keep))
     (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep))))
   (len (non-trivial-formals formals actuals))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable non-trivial-formals filter-formals-and-actuals))))

(defthm no-duplicate-lambda-formals-in-termsp-of-mv-nth-1-of-non-trivial-formals-and-args
  (implies (no-duplicate-lambda-formals-in-termsp args)
           (no-duplicate-lambda-formals-in-termsp (mv-nth 1 (non-trivial-formals-and-args formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))

(defthm not-member-equal-of-trivial-formals-when-member-equal-of-non-trivial-formals
  (implies (and (member-equal var (non-trivial-formals formals args))
                (no-duplicatesp-equal formals))
           (not (member-equal var (trivial-formals formals args))))
  :hints (("Goal" :in-theory (enable trivial-formals non-trivial-formals))))

(defthm member-equal-of-trivial-formals-when-not-member-equal-of-non-trivial-formals
  (implies (and (not (member-equal var (non-trivial-formals formals args)))
                (no-duplicatesp-equal formals)
                (member-equal var formals))
           (member-equal var (trivial-formals formals args)))
  :hints (("Goal" :in-theory (enable trivial-formals non-trivial-formals))))

(defthm member-equal-of-non-trivial-formals-becomes-not-member-equal-of-non-trivial-formals
  (implies (and  (no-duplicatesp-equal formals)
                 (member-equal var formals))
           (iff (member-equal var (non-trivial-formals formals args))
                (not (member-equal var (trivial-formals formals args)))))
  :hints (("Goal" :in-theory (enable trivial-formals non-trivial-formals))))

(defthm no-nils-in-termsp-of-mv-nth-1-of-non-trivial-formals-and-args
  (implies (and (no-nils-in-termsp args)
                (equal (len formals) (len args)))
           (no-nils-in-termsp (mv-nth 1 (non-trivial-formals-and-args formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))

(defthm no-duplicatesp-equal-of-non-trivial-formals
  (implies (no-duplicatesp-equal formals)
           (no-duplicatesp-equal (non-trivial-formals formals args)))
  :hints (("Goal" :in-theory (enable non-trivial-formals no-duplicatesp-equal))))

(defthm lookup-equal-of-pairlis$-when-member-equal-of-trivial-formals
  (implies (and (member-equal formal (trivial-formals formals args))
                (no-duplicatesp-equal formals))
           (equal (lookup-equal formal (pairlis$ formals args))
                  formal))
  :hints (("Goal" :in-theory (enable trivial-formals pairlis$ lookup-equal assoc-equal))))

(defthm lambdas-closed-in-termsp-of-mv-nth-1-of-non-trivial-formals-and-args
  (implies (lambdas-closed-in-termsp args)
           (lambdas-closed-in-termsp (mv-nth 1 (non-trivial-formals-and-args formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))

(defthm lambdas-closed-in-termsp-of-map-lookup-equal
  (implies (and ;(subsetp-equal keys (strip-cars alist))
                (lambdas-closed-in-termsp (strip-cdrs alist)))
           (lambdas-closed-in-termsp (map-lookup-equal keys alist)))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

(defthm cdr-of-assoc-equal-of-pairlis$_when-member-equal-of-trivial-formals
  (implies (and (MEMBER-EQUAL VAR (TRIVIAL-FORMALS FORMALS ARGS))
                (no-duplicatesp-equal formals))
           (equal (CDR (ASSOC-EQUAL VAR (PAIRLIS$ FORMALS ARGS)))
                  var))
  :hints (("Goal" :in-theory (enable PAIRLIS$ trivial-formals))))

(defthm LOOKUP-EQUAL-of-PAIRLIS$-of-NON-TRIVIAL-FORMALS-and-mv-nth-1-of-NON-TRIVIAL-FORMALS-AND-ARGS
 (implies (no-duplicatesp-equal formals)
          (equal (LOOKUP-EQUAL var (PAIRLIS$ (NON-TRIVIAL-FORMALS FORMALS ARGS)
                                             ;; could name this non-trivial-args:
                                             (MV-NTH 1 (NON-TRIVIAL-FORMALS-AND-ARGS FORMALS ARGS))))
                 (if (member-equal var (NON-TRIVIAL-FORMALS FORMALS ARGS))
                     (lookup-equal var (pairlis$ formals args))
                   nil)))
 :hints (("Goal" :in-theory (enable NON-TRIVIAL-FORMALS NON-TRIVIAL-FORMALS-and-args pairlis$))))

     ;todo: nested induction
(defthmd alists-equiv-on-of-cons-arg2-fw
  (implies (if (member-equal (car pair) keys)
               (and (equal (cdr pair) (cdr (assoc-equal (car pair) a2)))
                    (alists-equiv-on (remove-equal (car pair) keys) a1 a2))
             (alists-equiv-on keys a1 a2))
           (alists-equiv-on keys (cons pair a1) a2))
  :hints (("Goal" :in-theory (enable alists-equiv-on remove-equal))))

(defthmd alists-equiv-on-of-cons-arg2-back
  (implies (alists-equiv-on keys (cons pair a1) a2)
           (if (member-equal (car pair) keys)
               (and (equal (cdr pair) (cdr (assoc-equal (car pair) a2)))
                    (alists-equiv-on (remove-equal (car pair) keys) a1 a2))
             (alists-equiv-on keys a1 a2)))
  :hints (("Goal" :in-theory (enable alists-equiv-on))))

(defthm alists-equiv-on-of-cons-arg2
  (equal (alists-equiv-on keys (cons pair a1) a2)
         (if (member-equal (car pair) keys)
             (and (equal (cdr pair) (cdr (assoc-equal (car pair) a2)))
                  (alists-equiv-on (remove-equal (car pair) keys) a1 a2))
           (alists-equiv-on keys a1 a2)))
  :hints (("Goal" :use (alists-equiv-on-of-cons-arg2-fw
                        alists-equiv-on-of-cons-arg2-back))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv foundp bad-guy)
(defun bad-guy-for-alists-equiv-on-aux (keys a1 a2)
  (if (endp keys)
      (mv nil nil)
    (let ((key (first keys)))
      (if (not (equal (lookup-equal key a1) (lookup-equal key a2)))
          (mv t key)
        (mv-let (foundp bad-guy)
          (bad-guy-for-alists-equiv-on-aux (rest keys) a1 a2)
          (if foundp
              (mv t bad-guy)
            (mv nil nil)))))))

;; If A1 and A2 differ on any of the keys, this returns such a key.
(defund bad-guy-for-alists-equiv-on (keys a1 a2)
  (mv-let (foundp bad-guy)
    (bad-guy-for-alists-equiv-on-aux keys a1 a2)
    (if foundp
        bad-guy
      (first keys))))

(defthmd alists-equiv-on-when-agree-on-bad-guy-helper
  (iff (alists-equiv-on keys a1 a2)
       (not (mv-nth 0 (bad-guy-for-alists-equiv-on-aux keys a1 a2)))
       )
  :hints (("Goal" :in-theory (enable alists-equiv-on lookup-equal))))

;; The "bad guy trick" for alists-equiv-on.  To show that 2 alists agree with
;; respect to a set of keys, it suffices to show that they agree for the
;; bad-guy key.
(defthmd alists-equiv-on-when-agree-on-bad-guy
  (equal (alists-equiv-on keys a1 a2)
         (or (not (consp keys))
             (equal (lookup-equal (bad-guy-for-alists-equiv-on keys a1 a2) a1)
                    (lookup-equal (bad-guy-for-alists-equiv-on keys a1 a2) a2))))
  :hints (("Goal" :in-theory (enable lookup-equal
                                     bad-guy-for-alists-equiv-on
                                     alists-equiv-on-when-agree-on-bad-guy-helper))))

(defthm member-equal-of-bad-guy-for-alists-equiv-on-sam
  (implies (consp keys)
           (member-equal (bad-guy-for-alists-equiv-on keys a1 a2) keys))
  :hints (("Goal" :in-theory (enable bad-guy-for-alists-equiv-on))))

(defthm member-equal-of-bad-guy-for-alists-equiv-when-subsetp-equal
  (implies (and (subsetp-equal keys keys+)
                (consp keys))
           (member-equal (bad-guy-for-alists-equiv-on keys a1 a2)
                         keys+)))

(defthm symbolp-of-bad-guy-for-alists-equiv-on
  (implies (symbol-listp keys)
           (symbolp (bad-guy-for-alists-equiv-on keys a1 a2)))
  :hints (("Goal" :in-theory (enable bad-guy-for-alists-equiv-on))))

(defthm bad-guy-for-alists-equiv-on-not-nil
  (implies (and (not (member-equal nil keys))
                )
           (iff (bad-guy-for-alists-equiv-on keys a1 a2)
                (consp keys)))
  :hints (("Goal" :in-theory (enable bad-guy-for-alists-equiv-on member-equal))))

(defthm member-equal-of-lookup-equal-of-pairlis$-same
  (implies (and (member-equal key keys)
                (equal (len keys) (len terms)))
           (member-equal (lookup-equal key (pairlis$ keys terms)) terms)))

(defthm subsetp-equal-of-free-vars-in-terms-of-map-lookup-equal-of-pairlis$
  (implies (and (subsetp-equal keys1 keys2)
                (equal (len keys2) (len terms)))
           (subsetp-equal (free-vars-in-terms (map-lookup-equal keys1 (pairlis$ keys2 terms)))
                          (free-vars-in-terms terms)))
  :hints (("Goal" :in-theory (enable map-lookup-equal subsetp-equal))))

; strong
;todo: nested induction
(defthmd alists-equiv-on-redef
  (equal (alists-equiv-on keys a1 a2)
         (equal (map-lookup-equal keys a1)
                (map-lookup-equal keys a2)))
  :hints (("Goal" :in-theory (enable alists-equiv-on map-lookup-equal))))

(defthm map-lookup-equal-of-cons-of-cons-irrel
  (implies (not (member-equal key keys))
           (equal (map-lookup-equal keys (cons (cons key val) alist))
                  (map-lookup-equal keys alist)))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

(defthm mv-nth-1-of-FILTER-FORMALS-AND-ACTUALS
  (implies (no-duplicatesp-equal formals)
           (equal (mv-nth 1 (filter-formals-and-actuals formals actuals vars))
                  (map-lookup-equal (intersection-equal formals vars)
                                    (pairlis$ formals actuals))))
  :hints (("Goal" :in-theory (enable FILTER-FORMALS-AND-ACTUALS
                                     INTERSECTION-EQUAL
                                     map-lookup-equal
                                     PAIRLIS$) )))

(defthm lookup-equal-of-pairlis$-of-map-lookup-equal-when-memberp-equal
  (implies (member-equal key all-keys)
           (equal (lookup-equal key (pairlis$ all-keys (map-lookup-equal all-keys alist)))
                  (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable  pairlis$ subsetp-equal))))

(defthm map-lookup-equal-of-pairlis$-of-map-lookup-equal-when-subsetp-equal
  (implies (subsetp-equal keys all-keys)
           (equal (map-lookup-equal keys (pairlis$ all-keys (map-lookup-equal all-keys alist)))
                  (map-lookup-equal keys alist)))
  :hints (("Goal" :in-theory (enable map-lookup-equal pairlis$ subsetp-equal))))

;todo: nested induction
;todo: not used?
(defthm alists-equiv-on-of-pairlis$-same
  (implies (and (equal (len keys) (len vals))
                (no-duplicatesp-equal keys) ; todo
                (true-listp vals))
           (equal (alists-equiv-on keys (pairlis$ keys vals) alist)
                  (equal vals (map-lookup-equal keys alist))))
  :hints (("Goal" :in-theory (enable alists-equiv-on pairlis$ lookup-equal map-lookup-equal))))
