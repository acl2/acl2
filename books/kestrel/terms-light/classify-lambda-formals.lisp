; Substituting lambda vars that only appear once
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: reduce what this book exports

(include-book "free-vars-in-term")
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/alists-light/map-lookup-equal" :dir :system)
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp2" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
;(local (include-book "kestrel/lists-light/union-equal" :dir :system))
;(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/remove-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/list-sets" :dir :system))
(local (include-book "kestrel/alists-light/term-alists" :dir :system))

(local (in-theory (disable mv-nth)))

(local (in-theory (disable strip-cdrs
                           strip-cars
                           symbol-alistp
                           intersection-equal-symmetric-iff)))

(local (in-theory (enable pseudo-term-listp-when-symbol-listp)))

(defthm intersection-equal-of-union-equal-arg2-iff
  (iff (intersection-equal x (union-equal y z))
       (or (intersection-equal x y)
           (intersection-equal x z)))
  :hints (("Goal" :in-theory (enable union-equal intersection-equal))))

(defthm subsetp-equal-of-set-difference-equal-and-set-difference-equal
  (implies (and (subsetp-equal x1 x2)
                (subsetp-equal z y))
           (subsetp-equal (set-difference-equal x1 y) (set-difference-equal x2 z)))
  :hints (("Goal" :in-theory (enable subsetp-equal set-difference-equal))))

(local
  (defthm map-lookup-equal-of-reverse-list
    (equal (map-lookup-equal (reverse-list keys) alist)
           (reverse-list (map-lookup-equal keys alist)))
    :hints (("Goal" :in-theory (enable map-lookup-equal reverse-list)))))

(local
  (defthm subsetp-equal-of-free-vars-in-terms-of-reverse-list
    (subsetp-equal (free-vars-in-terms (reverse-list terms))
                   (free-vars-in-terms terms))
    :hints (("Goal" :in-theory (enable (:I len) reverse-list) :induct (len terms)))))

(defthm subsetp-equal-of-free-vars-in-terms-of-reverse
  (implies (true-listp acc)
           (iff (subsetp-equal (free-vars-in-terms (map-lookup-equal (reverse acc) alist)) y)
                (subsetp-equal (free-vars-in-terms (map-lookup-equal acc alist)) y)))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; May drop some of the formals-to-maybe-subst.
;; whose actuals mention any of the formals-to-keep.
;; Returns (mv formals-to-maybe-subst formals-to-keep).
(defund classify-lambda-formals-aux (formals-to-maybe-subst formal-arg-alist formals-to-keep)
  (declare (xargs :guard (and (symbol-listp formals-to-maybe-subst)
                              (symbol-alistp formal-arg-alist)
                              (pseudo-term-listp (strip-cdrs formal-arg-alist))
                              (symbol-listp formals-to-keep)
                              (subsetp-equal formals-to-maybe-subst (strip-cars formal-arg-alist))
                              (subsetp-equal formals-to-keep (strip-cars formal-arg-alist)))))
  (if (endp formals-to-maybe-subst)
      (mv nil nil)
    (let* ((formal (first formals-to-maybe-subst))
           (arg (lookup-eq formal formal-arg-alist))
           (arg-vars (free-vars-in-term arg)))
      (if (intersection-eq arg-vars formals-to-keep)
          ;; We cannot substitute for this formal, because its arg mentions bad vars.
          ;; todo: optimise by adding it to the formals-to-keep now?
          (mv-let (x y)
            (classify-lambda-formals-aux (rest formals-to-maybe-subst) formal-arg-alist formals-to-keep)
            (mv x (cons formal y)))
        ;; No problem currently with this formal:
          (mv-let (x y)
            (classify-lambda-formals-aux (rest formals-to-maybe-subst) formal-arg-alist formals-to-keep)
            (mv (cons formal x) y))))))

(defthm symbol-listp-of-mv-nth-0-of-classify-lambda-formals-aux
  (implies (symbol-listp formals-to-maybe-subst)
           (symbol-listp (mv-nth 0 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))))
  :hints (("Goal" :in-theory (enable classify-lambda-formals-aux))))

(defthm symbol-listp-of-mv-nth-1-of-classify-lambda-formals-aux
  (implies (symbol-listp formals-to-maybe-subst)
           (symbol-listp (mv-nth 1 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))))
  :hints (("Goal" :in-theory (enable classify-lambda-formals-aux))))

(defthm subsetp-equal-of-mv-nth-0-of-classify-lambda-formals-aux
  (subsetp-equal (mv-nth 0 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))
                 formals-to-maybe-subst)
  :hints (("Goal" :in-theory (enable classify-lambda-formals-aux))))

(defthm classify-lambda-formals-aux-correct
  (implies (and (symbol-listp formals-to-maybe-subst)
                (symbol-alistp formal-arg-alist)
                (pseudo-term-listp (strip-cdrs formal-arg-alist))
                (symbol-listp formals-to-keep)
                (subsetp-equal formals-to-maybe-subst (strip-cars formal-arg-alist))
                (subsetp-equal formals-to-keep (strip-cars formal-arg-alist))
                )
           (not (intersection-equal (free-vars-in-terms (map-lookup-equal (mv-nth 0 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)) formal-arg-alist))
                                    formals-to-keep)))
  :hints (("Goal" :in-theory (enable classify-lambda-formals-aux))))

(defthm len-of-mv-nth-0-of-classify-lambda-formals-aux-linear
  (<= (len (mv-nth 0 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))
      (len formals-to-maybe-subst))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable classify-lambda-formals-aux))))

(defthm classify-lambda-formals-aux-stopping
  (iff (equal (len (mv-nth 0 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))
              (len formals-to-maybe-subst))
       (not (intersection-eq (free-vars-in-terms (map-lookup-equal formals-to-maybe-subst formal-arg-alist))
                             formals-to-keep)))
  :hints (("Goal" :in-theory (enable classify-lambda-formals-aux))))

(defthm classify-lambda-formals-aux-stopping-2
  (iff (< (len (mv-nth 0 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))
          (len formals-to-maybe-subst))
       (intersection-eq (free-vars-in-terms (map-lookup-equal formals-to-maybe-subst formal-arg-alist))
                        formals-to-keep))
  :hints (("Goal" :in-theory (enable classify-lambda-formals-aux))))

(defthm subsetp-equal-of-mv-nth-1-of-classify-lambda-formals-aux
  (subsetp-equal (mv-nth 1 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))
                 formals-to-maybe-subst)
  :hints (("Goal" :in-theory (enable classify-lambda-formals-aux))))

(defthm classify-lambda-formals-aux-correct-1
  (subsetp-equal (set-difference-equal formals-to-maybe-subst
                                       (mv-nth 0 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))
                 (mv-nth 1 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))
  :hints (("Goal" :in-theory (enable classify-lambda-formals-aux set-difference-equal))))

(defthm classify-lambda-formals-aux-correct-1-alt
  (implies (no-duplicatesp-equal formals-to-maybe-subst)
           (subsetp-equal (mv-nth 1 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))
                          (set-difference-equal formals-to-maybe-subst
                                                (mv-nth 0 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))))
  :hints (("Goal" :in-theory (enable classify-lambda-formals-aux set-difference-equal))))

(defthm classify-lambda-formals-aux-correct-1-alt-strong
  (implies (no-duplicatesp-equal formals-to-maybe-subst)
           (equal (mv-nth 1 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))
                  (set-difference-equal formals-to-maybe-subst
                                        (mv-nth 0 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))))
  :hints (("Goal" :in-theory (enable classify-lambda-formals-aux set-difference-equal))))

(defthm no-duplicatesp-equal-of-mv-nth-0-of-classify-lambda-formals-aux
  (implies (no-duplicatesp-equal formals-to-maybe-subst)
           (no-duplicatesp-equal (mv-nth 0 (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))))
  :hints (("Goal" :in-theory (enable classify-lambda-formals-aux))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Decides which of the formals-to-maybe-subst we can actually substitute without name clashes.
;; We have to exclude any formal whose corresponding actual mentions any of the
;; formals-to-keep, or any of the formals so excluded, and so on.
;; optimize?
;; Returns (mv reduced-formals-to-maybe-subst extended-formals-to-keep).
(defund classify-lambda-formals (formals-to-maybe-subst formal-arg-alist formals-to-keep)
  (declare (xargs :guard (and (symbol-listp formals-to-maybe-subst)
                              (symbol-alistp formal-arg-alist)
                              (pseudo-term-listp (strip-cdrs formal-arg-alist))
                              (symbol-listp formals-to-keep)
                              (subsetp-equal formals-to-maybe-subst (strip-cars formal-arg-alist))
                              (subsetp-equal formals-to-keep (strip-cars formal-arg-alist)))
                  :measure (len formals-to-maybe-subst)))
  (mv-let (new-formals-to-maybe-subst extra-formals-to-keep)
    (classify-lambda-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)
    (if (>= (len new-formals-to-maybe-subst) (len formals-to-maybe-subst)) ; can't actually be greater
        (mv formals-to-maybe-subst formals-to-keep) ; done!
      (classify-lambda-formals new-formals-to-maybe-subst formal-arg-alist (append extra-formals-to-keep formals-to-keep)))))

(defthm classify-lambda-formals-correct
  (implies (and (symbol-listp formals-to-maybe-subst)
                (symbol-alistp formal-arg-alist)
                (pseudo-term-listp (strip-cdrs formal-arg-alist))
                (symbol-listp formals-to-keep)
                (subsetp-equal formals-to-maybe-subst (strip-cars formal-arg-alist))
                (subsetp-equal formals-to-keep (strip-cars formal-arg-alist)))
           (not (intersection-equal (free-vars-in-terms (map-lookup-equal (mv-nth 0 (classify-lambda-formals formals-to-maybe-subst formal-arg-alist formals-to-keep)) formal-arg-alist))
                                    (mv-nth 1 (classify-lambda-formals formals-to-maybe-subst formal-arg-alist formals-to-keep)))))
  :hints (("Goal" :in-theory (e/d (classify-lambda-formals) (intersection-equal-symmetric-iff)))))

;sanity check
;needed?
(thm
  (implies (and ;(subsetp-equal formals-to-maybe-subst oformals-to-maybe-subst)
             ;(no-duplicatesp-equal formals-to-maybe-subst)
             )
           (subsetp-equal formals-to-keep
                          (mv-nth 1 (classify-lambda-formals formals-to-maybe-subst formal-arg-alist formals-to-keep))))
  :hints (("Goal" :in-theory (enable classify-lambda-formals))))

(defthm symbol-listp-of-mv-nth-0-of-classify-lambda-formals
  (implies (symbol-listp formals-to-maybe-subst)
           (symbol-listp (mv-nth 0 (classify-lambda-formals formals-to-maybe-subst formal-arg-alist formals-to-keep))))
  :hints (("Goal" :in-theory (enable classify-lambda-formals))))

(defthm set-helper1
  (equal (subsetp-equal (set-difference-equal x this) (append (set-difference-equal y this) z))
         (subsetp-equal (set-difference-equal x this) (append y z)))
  :hints (("Goal" :in-theory (enable set-difference-equal set-difference-equal))))

;; (thm
;;   (equal (subsetp-equal (set-difference-equal x this) (append (set-difference-equal y this) z))
;;          (subsetp-equal (set-difference-equal x this) (append y z)))
;;   :hints (("Goal" :in-theory (enable set-difference-equal set-difference-equal))))

(defthm set-helper2
  (implies (subsetp-equal (set-difference-equal oformals-to-maybe-subst formals-to-maybe-subst) formals-to-keep)
           (subsetp-equal (set-difference-equal oformals-to-maybe-subst xxx) (append formals-to-maybe-subst formals-to-keep)))
  :hints (("Goal" :in-theory (enable set-difference-equal set-difference-equal))))

;; ;; the final formals-to-keep should include all the formals-to-maybe-subst that we had to drop:
;; (thm
;;   (implies (and; (subsetp-equal formals-to-maybe-subst oformals-to-maybe-subst)
;;              (subsetp-equal (set-difference-equal formals-to-maybe-subst formals-to-maybe-subst)
;;                             formals-to-keep)
;;              (no-duplicatesp-equal formals-to-maybe-subst)
;;              )
;;            (subsetp-equal (set-difference-equal formals-to-maybe-subst
;;                                                 (mv-nth 0 (classify-lambda-formals formals-to-maybe-subst formal-arg-alist formals-to-keep)))
;;                           (mv-nth 1 (classify-lambda-formals formals-to-maybe-subst formal-arg-alist formals-to-keep))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable classify-lambda-formals))))

;; the final formals-to-keep should include all the formals-to-maybe-subst that we had to drop:
(defthm classify-lambda-formals-lemma ;rename
    (implies (and (subsetp-equal formals-to-maybe-subst oformals-to-maybe-subst)
                  (subsetp-equal (set-difference-equal oformals-to-maybe-subst formals-to-maybe-subst) formals-to-keep)
                  (no-duplicatesp-equal formals-to-maybe-subst))
             (subsetp-equal (set-difference-equal oformals-to-maybe-subst
                                                  (mv-nth 0 (classify-lambda-formals formals-to-maybe-subst formal-arg-alist formals-to-keep)))
                            (mv-nth 1 (classify-lambda-formals formals-to-maybe-subst formal-arg-alist formals-to-keep))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (classify-lambda-formals) (intersection-equal-symmetric-iff)))))

(defthm call-of-classify-lambda-formals-ok
  (implies (and (subsetp-equal try-vars non-trivial-formals)
                (symbol-listp try-vars)
                (symbol-alistp alist)
                (pseudo-term-listp (strip-cdrs alist))
                (symbol-listp non-trivial-formals)
                (subsetp-equal try-vars (strip-cars alist))
                (subsetp-equal non-trivial-formals (strip-cars alist))
                (no-duplicatesp-equal try-vars))
           (not
             (intersection-equal (free-vars-in-terms (map-lookup-equal (mv-nth 0 (classify-lambda-formals try-vars alist (set-difference-equal non-trivial-formals try-vars))) alist))
                                 (set-difference-equal non-trivial-formals (mv-nth '0 (classify-lambda-formals try-vars alist (set-difference-equal non-trivial-formals try-vars)))))))
  :hints (("Goal" :use (:instance classify-lambda-formals-correct
                                  (formals-to-maybe-subst try-vars)
                                  (formal-arg-alist alist)
                                  (formals-to-keep (set-difference-equal non-trivial-formals try-vars)))
           :in-theory (disable classify-lambda-formals-correct))))

(defthm subsetp-equal-of-mv-nth-0-of-classify-lambda-formals
  (subsetp-equal (mv-nth 0 (classify-lambda-formals formals-to-maybe-subst formal-arg-alist formals-to-keep))
                 formals-to-maybe-subst)
  :hints (("Goal" :in-theory (enable classify-lambda-formals))))

(defthm subsetp-equal-of-mv-nth-0-of-classify-lambda-formals-gen
  (implies (subsetp-equal formals-to-maybe-subst x)
           (subsetp-equal (mv-nth 0 (classify-lambda-formals formals-to-maybe-subst formal-arg-alist formals-to-keep))
                          x))
  :hints (("Goal" :in-theory (enable classify-lambda-formals))))
