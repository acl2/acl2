; Proofs about serialize-lambdas-in-term
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lambdas-closed-in-termp")
(include-book "serialize-lambdas-in-term")
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(local (in-theory (disable mv-nth)))

;move?
(defthm lambdas-closed-in-termsp-of-strip-cdrs-of-non-trivial-bindings
  (implies (lambdas-closed-in-termsp vals)
           (lambdas-closed-in-termsp (strip-cdrs (non-trivial-bindings vars vals))))
  :hints (("Goal" :in-theory (enable non-trivial-bindings))))

;move?
(defthm lambdas-closed-in-termsp-of-strip-cdrs-of-revappend
  (implies (and (lambdas-closed-in-termsp (strip-cdrs terms1))
                (lambdas-closed-in-termsp (strip-cdrs terms2)))
           (lambdas-closed-in-termsp (strip-cdrs (revappend terms1 terms2))))
  :hints (("Goal" :in-theory (enable revappend))))

;move?
(defthm lambdas-closed-in-termp-of-cdr-of-assoc-equal
  (implies (lambdas-closed-in-termsp (strip-cdrs alist))
           (lambdas-closed-in-termp (cdr (assoc-equal term alist))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;move?
(defthm-flag-sublis-var-simple
  (defthm lambdas-closed-in-termp-of-sublis-var-simple
    (implies (and (pseudo-termp term)
                  (lambdas-closed-in-termp term)
                  (lambdas-closed-in-termsp (strip-cdrs alist)))
             (lambdas-closed-in-termp (sublis-var-simple alist term)))
    :flag sublis-var-simple)
  (defthm lambdas-closed-in-termp-of-sublis-var-lst-simple
    (implies (and (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms)
                  (lambdas-closed-in-termsp (strip-cdrs alist)))
             (lambdas-closed-in-termsp (sublis-var-simple-lst alist terms)))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable sublis-var-simple
                              sublis-var-simple-lst
                              lambdas-closed-in-termp))))

(defthm lambdas-closed-in-termp-of-make-lambda-nest
  (implies (and (symbol-alistp bindings)
                (pseudo-term-listp (strip-cdrs bindings))
                (lambdas-closed-in-termsp (strip-cdrs bindings))
                (pseudo-termp body)
                (lambdas-closed-in-termp body))
           (lambdas-closed-in-termp (make-lambda-nest bindings body)))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termp))))

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