; Get nodenums with no result in the result-array
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

(include-book "bounded-darg-listp")
(include-book "kestrel/typed-lists-light/all-natp" :dir :system)
(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "keep-nodenum-dargs")
(include-book "bounded-dag-exprs")
(include-book "dag-arrays") ;for pseudo-dag-arrayp-list
(local (include-book "rational-lists"))

;either returns nil (no args are untagged) or extends acc with the untagged args
;; See also extend-with-not-done-args (different behavior when no args are untagged) and get-args-not-done-array.
(defund get-args-not-done (args result-array-name result-array acc untagged-foundp)
  (declare (xargs :guard (and (array1p result-array-name result-array)
                              (bounded-darg-listp args (alen1 result-array-name result-array)))))
  (if (endp args)
      (if untagged-foundp
          acc
        nil)
    (let* ((arg (first args)))
      (if (or (consp arg) ;it's a quotep, so skip it
              (aref1 result-array-name result-array arg) ;it's tagged as done, so skip it
              )
          (get-args-not-done (rest args) result-array-name result-array acc untagged-foundp)
        ;; add the arg and record the fact that we found an untagged arg:
        (get-args-not-done (rest args) result-array-name result-array (cons arg acc) t)))))

(defthm natp-of-maxelem-of-get-args-not-done
  (implies (and (darg-listp args)
                (all-natp acc)
                (true-listp acc)
                (get-args-not-done args result-array-name result-array acc untagged-foundp))
           (natp (maxelem (get-args-not-done args result-array-name result-array acc untagged-foundp))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (get-args-not-done) (natp)))))

(defthm all-<-of-get-args-not-done
  (implies (and (bounded-darg-listp args bound)
                (all-< acc bound))
           (all-< (get-args-not-done args result-array-name result-array acc untagged-foundp)
                  bound))
  :hints (("Goal" :in-theory (enable get-args-not-done))))

(defthm all-natp-of-get-args-not-done
  (implies (and (darg-listp args)
                (all-natp acc)
                (true-listp acc))
           (all-natp (get-args-not-done args result-array-name result-array acc untagged-foundp)))
  :hints (("Goal" :in-theory (enable get-args-not-done))))

(defthm true-listp-of-get-args-not-done
  (implies (true-listp acc)
           (true-listp (get-args-not-done args result-array-name result-array acc untagged-foundp)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable get-args-not-done))))

(defthm get-args-not-done-when-not-consp-of-keep-nodenum-dargs
  (implies (not (consp (keep-nodenum-dargs args)))
           (equal (get-args-not-done args result-array-name result-array acc untagged-foundp)
                  (if untagged-foundp acc nil)))
  :hints (("Goal" :in-theory (enable get-args-not-done keep-nodenum-dargs))))

(defthm maxelem-of-get-args-not-done-bound
  (implies (and (darg-listp args)
                (all-natp acc)
                (true-listp acc)
                (get-args-not-done args result-array-name result-array acc untagged-foundp))
           (<= (maxelem (get-args-not-done args result-array-name result-array acc untagged-foundp))
               (max (maxelem (keep-nodenum-dargs args))
                    (maxelem acc))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable get-args-not-done keep-nodenum-dargs))))

;todo: remove pseudo-dag-arrayp-list stuff from this file
(defthm pseudo-dag-arrayp-list-of-get-args-not-done
  (implies (and (pseudo-dag-arrayp-list args dag-array-name dag-array)
                (pseudo-dag-arrayp-list acc dag-array-name dag-array))
           (pseudo-dag-arrayp-list (get-args-not-done args size-array-name size-array acc untagged-foundp) dag-array-name dag-array))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp-list get-args-not-done))))

;; (defthm all-natp-of-get-args-not-done-2
;;   (implies (and (all-natp acc)
;;                 (all-natp args))
;;            (all-natp (get-args-not-done args result-array-name result-array acc untagged-foundp))))

(defthm get-args-not-done-when-consp-and-untagged-foundp
  (implies (consp acc)
           (get-args-not-done args result-array-name result-array acc t))
  :hints (("Goal" :in-theory (enable get-args-not-done))))
