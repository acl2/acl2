; Helper rules for the proofs in this directory
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These mix various notions, about terms, alists, etc.
;; TODO: Separate out this stuff better

(include-book "no-nils-in-termp")
(include-book "filter-formals-and-actuals")
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "non-trivial-formals-and-args")
(include-book "non-trivial-formals")
(include-book "trivial-formals")
(include-book "kestrel/alists-light/map-lookup-equal" :dir :system)

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
