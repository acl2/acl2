; Proofs about serialize-lambdas-in-term
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lambdas-closed-in-termp")
(include-book "serialize-lambdas-in-term")
(include-book "all-lambdas-serialized-in-termp")
(include-book "non-trivial-formals")
(include-book "no-duplicate-lambda-formals-in-termp")
(local (include-book "make-lambda-nest-proofs"))
(local (include-book "sublis-var-simple-proofs")) ;drop
(local (include-book "subst-var-alt-proofs"))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(local (in-theory (disable mv-nth)))

;; TODO: Prove that serialize-lambdas-in-term preserves the meaning of terms.

;move?
(local
 (defthm lambdas-closed-in-termsp-of-strip-cdrs-of-non-trivial-bindings
   (implies (lambdas-closed-in-termsp vals)
            (lambdas-closed-in-termsp (strip-cdrs (non-trivial-bindings vars vals))))
   :hints (("Goal" :in-theory (enable non-trivial-bindings)))))

(defthm lambdas-closed-in-termsp-of-strip-cdrs-of-mv-nth-1-of-find-safe-binding
  (implies (and (symbol-alistp bindings)
                (pseudo-term-listp (strip-cdrs bindings))
                (symbol-alistp earlier-bindings-rev)
                (pseudo-term-listp (strip-cdrs earlier-bindings-rev))
                (lambdas-closed-in-termsp (strip-cdrs bindings))
                (lambdas-closed-in-termsp (strip-cdrs earlier-bindings-rev)))
           (lambdas-closed-in-termsp (strip-cdrs (mv-nth 1 (find-safe-binding bindings earlier-bindings-rev)))))
  :hints (("Goal" :in-theory (enable find-safe-binding))))

(defthm lambdas-closed-in-termp-of-cdr-of-mv-nth-0-of-find-safe-binding
  (implies (and (symbol-alistp bindings)
                (pseudo-term-listp (strip-cdrs bindings))
                (symbol-alistp earlier-bindings-rev)
                (pseudo-term-listp (strip-cdrs earlier-bindings-rev))
                (lambdas-closed-in-termsp (strip-cdrs bindings))
                (lambdas-closed-in-termsp (strip-cdrs earlier-bindings-rev)))
           (lambdas-closed-in-termp (cdr (mv-nth 0 (find-safe-binding bindings earlier-bindings-rev)))))
  :hints (("Goal" :in-theory (enable find-safe-binding))))

(defthm lambdas-closed-in-termsp-of-strip-cdrs-of-serialize-bindings
  (implies (and (lambdas-closed-in-termsp (strip-cdrs bindings))
                (symbol-alistp bindings)
                (pseudo-term-listp (strip-cdrs bindings)))
           (lambdas-closed-in-termsp (strip-cdrs (serialize-bindings bindings names-to-avoid))))
  :hints (("Goal" :in-theory (enable serialize-bindings))))

;; Serialize-lambdas-in-term doesn't create any unclosed lambdas.
(defthm-flag-serialize-lambdas-in-term
  (defthm lambdas-closed-in-termp-of-serialize-lambdas-in-term
    (implies (and (pseudo-termp term)
                  (lambdas-closed-in-termp term))
             (lambdas-closed-in-termp (serialize-lambdas-in-term term vars-to-avoid)))
    :flag serialize-lambdas-in-term)
  (defthm lambdas-closed-in-termp-of-serialize-lambdas-in-terms
    (implies (and (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms))
             (lambdas-closed-in-termsp (serialize-lambdas-in-terms terms vars-to-avoid)))
    :flag serialize-lambdas-in-terms)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable serialize-lambdas-in-term
                              serialize-lambdas-in-terms
                              lambdas-closed-in-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm all-lambdas-serialized-in-termp-of-make-lambda-nest
  (implies (and (symbol-alistp bindings)
                (pseudo-term-listp (strip-cdrs bindings))
                (all-lambdas-serialized-in-termsp (strip-cdrs bindings))
                (all-lambdas-serialized-in-termp body)
                (pseudo-termp body))
           (all-lambdas-serialized-in-termp (make-lambda-nest bindings body)))
  :hints (("Goal" :in-theory (enable make-lambda-nest))))

(defthm all-lambdas-serialized-in-termp-of-cdr-of-mv-nth-0-of-find-safe-binding
  (implies (all-lambdas-serialized-in-termsp (strip-cdrs bindings))
           (all-lambdas-serialized-in-termp (cdr (mv-nth 0 (find-safe-binding bindings earlier-bindings-rev)))))
  :hints (("Goal" :in-theory (enable find-safe-binding))))

(defthm all-lambdas-serialized-in-termsp-of-strip-cdrs-of-mv-nth-1-of-find-safe-binding
  (implies (and (all-lambdas-serialized-in-termsp (strip-cdrs bindings))
                (all-lambdas-serialized-in-termsp (strip-cdrs earlier-bindings-rev)))
           (all-lambdas-serialized-in-termsp (strip-cdrs (mv-nth 1 (find-safe-binding bindings earlier-bindings-rev)))))
  :hints (("Goal" :in-theory (enable find-safe-binding))))

;move
(defthm sublis-var-simple-lst-of-cons
  (equal (sublis-var-simple-lst alist (cons term terms))
         (cons (sublis-var-simple alist term)
               (sublis-var-simple-lst alist terms)))
  :hints (("Goal" :in-theory (enable sublis-var-simple-lst))))

;move
(defthm sublis-var-simple-lst-of-nil-arg2
  (equal (sublis-var-simple-lst alist nil)
         nil)
  :hints (("Goal" :in-theory (enable sublis-var-simple-lst))))

(defthm all-lambdas-serialized-in-termp-of-cdr-of-assoc-equal
  (implies (all-lambdas-serialized-in-termsp (strip-cdrs alist))
           (all-lambdas-serialized-in-termp (cdr (assoc-equal term alist))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;rename
;; todo: not true!
;; (defthm-flag-sublis-var-simple
;;   (defthm theorem-for-sublis-var-simple
;;     (implies (and (symbol-alistp alist)
;;                   (pseudo-termp term)
;;                   (all-lambdas-serialized-in-termp term)
;;                   (all-lambdas-serialized-in-termsp (strip-cdrs alist)))
;;              (all-lambdas-serialized-in-termp (sublis-var-simple alist term)))
;;     :flag sublis-var-simple)
;;   (defthm theorem-for-sublis-var-simple-lst
;;     (implies (and (symbol-alistp alist)
;;                   (pseudo-term-listp terms)
;;                   (all-lambdas-serialized-in-termsp terms)
;;                   (all-lambdas-serialized-in-termsp (strip-cdrs alist)))
;;              (all-lambdas-serialized-in-termsp (sublis-var-simple-lst alist terms)))
;;     :flag sublis-var-simple-lst)
;;   :hints (("Goal" :in-theory (enable sublis-var-simple))))

(defthm all-lambdas-serialized-in-termsp-of-strip-cdrs-of-cdr
  (implies (all-lambdas-serialized-in-termsp (strip-cdrs bindings))
           (all-lambdas-serialized-in-termsp (strip-cdrs (cdr bindings)))))

(defthm no-duplicate-lambda-formals-in-termsp-of-strip-cdrs-of-cdr
  (implies (no-duplicate-lambda-formals-in-termsp (strip-cdrs bindings))
           (no-duplicate-lambda-formals-in-termsp (strip-cdrs (cdr bindings)))))

(defthm pseudo-term-listp-of-strip-cdrs-of-cdr
  (implies (pseudo-term-listp (strip-cdrs bindings))
           (pseudo-term-listp (strip-cdrs (cdr bindings)))))

(defthm no-duplicate-lambda-formals-in-termsp-of-revappend
  (implies (and (no-duplicate-lambda-formals-in-termsp terms1)
                (no-duplicate-lambda-formals-in-termsp terms2))
           (no-duplicate-lambda-formals-in-termsp
            (revappend terms1 terms2))))

(defthm no-duplicate-lambda-formals-in-termsp-of-strip-cdrs-of-mv-nth-1-of-find-safe-binding
  (implies (and (no-duplicate-lambda-formals-in-termsp (strip-cdrs bindings))
                (no-duplicate-lambda-formals-in-termsp (strip-cdrs earlier-bindings-rev)))
           (no-duplicate-lambda-formals-in-termsp (strip-cdrs
                                              (mv-nth
                                               1
                                               (find-safe-binding bindings earlier-bindings-rev)))))
  :hints (("Goal" :in-theory (enable find-safe-binding))))

(defthm all-lambdas-serialized-in-termsp-of-strip-cdrs-of-serialize-bindings
  (implies (and (all-lambdas-serialized-in-termsp (strip-cdrs bindings))
                (pseudo-term-listp (strip-cdrs bindings))
                (no-duplicate-lambda-formals-in-termsp (strip-cdrs bindings))
                (symbol-alistp bindings))
           (all-lambdas-serialized-in-termsp (strip-cdrs (serialize-bindings bindings names-to-avoid))))
  :hints (("Goal" :in-theory (enable serialize-bindings))))

(local
 (defthm all-lambdas-serialized-in-termsp-of-strip-cdrs-of-non-trivial-bindings
   (implies (all-lambdas-serialized-in-termsp vals)
            (all-lambdas-serialized-in-termsp (strip-cdrs (non-trivial-bindings vars vals))))
   :hints (("Goal" :in-theory (enable non-trivial-bindings)))))

(local
 (defthm no-duplicate-lambda-formals-in-termsp-of-strip-cdrs-of-non-trivial-bindings
   (implies (no-duplicate-lambda-formals-in-termsp vals)
            (no-duplicate-lambda-formals-in-termsp (strip-cdrs (non-trivial-bindings vars vals))))
   :hints (("Goal" :in-theory (enable non-trivial-bindings)))))

(local (include-book "kestrel/lists-light/remove1-equal" :dir :system))
;move
(defthm not-member-equal-of-remove1-equal-same
  (implies (no-duplicatesp-equal l)
           (not (member-equal x (remove1-equal x l))))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm no-duplicate-lambda-formals-in-termsp-of-remove1-equal
  (implies (no-duplicate-lambda-formals-in-termsp terms)
           (no-duplicate-lambda-formals-in-termsp (remove1-equal term terms)))
  :hints (("Goal" :in-theory (enable no-duplicate-lambda-formals-in-termsp
                                     remove1-equal))))

(defthm no-duplicate-lambda-formals-in-termp-of-make-lambda-nest
  (implies (and (symbol-alistp bindings)
                (pseudo-term-listp (strip-cdrs bindings))
                (no-duplicate-lambda-formals-in-termsp (strip-cdrs bindings))
                (no-duplicate-lambda-formals-in-termp body)
                (pseudo-termp body))
           (no-duplicate-lambda-formals-in-termp (make-lambda-nest bindings body)))
  :hints (("Goal" :in-theory (enable make-lambda-nest no-duplicate-lambda-formals-in-termp))))

(defthm no-duplicate-lambda-formals-in-termp-of-cdr-of-mv-nth-0-of-find-safe-binding
  (implies (and (symbol-alistp bindings)
                (pseudo-term-listp (strip-cdrs bindings))
                (symbol-alistp earlier-bindings-rev)
                (pseudo-term-listp (strip-cdrs earlier-bindings-rev))
                (no-duplicate-lambda-formals-in-termsp (strip-cdrs bindings))
                (no-duplicate-lambda-formals-in-termsp (strip-cdrs earlier-bindings-rev)))
           (no-duplicate-lambda-formals-in-termp (cdr (mv-nth 0 (find-safe-binding bindings earlier-bindings-rev)))))
  :hints (("Goal" :in-theory (enable find-safe-binding))))

(defthm no-duplicate-lambda-formals-in-termsp-of-strip-cdrs-of-serialize-bindings
  (implies (and (no-duplicate-lambda-formals-in-termsp (strip-cdrs bindings))
                (pseudo-term-listp (strip-cdrs bindings))
                (no-duplicate-lambda-formals-in-termsp (strip-cdrs bindings))
                (symbol-alistp bindings))
           (no-duplicate-lambda-formals-in-termsp (strip-cdrs (serialize-bindings bindings names-to-avoid))))
  :hints (("Goal" :in-theory (enable serialize-bindings))))

(defthm-flag-serialize-lambdas-in-term
  (defthm no-duplicate-lambda-formals-in-termp-of-serialize-lambdas-in-term
    (implies (and (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term)
                  ;(symbol-listp vars-to-avoid)
                  )
             (no-duplicate-lambda-formals-in-termp (serialize-lambdas-in-term term vars-to-avoid)))
    :flag serialize-lambdas-in-term)
  (defthm no-duplicate-lambda-formals-in-termsp-of-serialize-lambdas-in-terms
    (implies (and (pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms)
                  ;(symbol-listp vars-to-avoid)
                  )
             (no-duplicate-lambda-formals-in-termsp (serialize-lambdas-in-terms terms vars-to-avoid)))
    :flag serialize-lambdas-in-terms)
  :hints (("Goal" :in-theory (e/d (serialize-lambdas-in-terms
                                   serialize-lambdas-in-term
                                   no-duplicate-lambda-formals-in-termp) (symbol-listp)))))

;; serialize-lambdas-in-term correctly serializes all lambdas
(defthm-flag-serialize-lambdas-in-term
  (defthm all-lambdas-serialized-in-termp-of-serialize-lambdas-in-term
    (implies (and (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (all-lambdas-serialized-in-termp (serialize-lambdas-in-term term vars-to-avoid)))
    :flag serialize-lambdas-in-term)
  (defthm all-lambdas-serialized-in-termsp-of-serialize-lambdas-in-terms
    (implies (and (pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (all-lambdas-serialized-in-termsp (serialize-lambdas-in-terms terms vars-to-avoid)))
    :flag serialize-lambdas-in-terms)
  :hints (("Goal" :in-theory (e/d (serialize-lambdas-in-terms
                                     serialize-lambdas-in-term
                                     no-duplicate-lambda-formals-in-termp) (symbol-listp)))))
