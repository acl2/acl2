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
(include-book "non-trivial-formals")
(local (include-book "make-lambda-nest-proofs"))
(local (include-book "sublis-var-simple-proofs"))
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

(mutual-recursion
 ;; Checks whether every lambda in TERM has at most 1 non-trivial formal.
 (defun all-lambdas-serialized-in-termp (term)
   (declare (xargs :guard (pseudo-termp term)))
   (if (or (variablep term)
           (quotep term))
       t
     ;; TERM is a function call (perhaps a lambda application)
     (let ((args (fargs term)))
       (and (all-lambdas-serialized-in-termsp args)
            (let ((fn (ffn-symb term)))
              (if (not (flambdap fn))
                  t
                ;; more than one non-trivial formal would mean the lambda has not been serialized
                (and (<= (len (non-trivial-formals (lambda-formals fn) args)) 1)
                     (all-lambdas-serialized-in-termp (lambda-body fn)))))))))

 (defun all-lambdas-serialized-in-termsp (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       t
       (and (all-lambdas-serialized-in-termp (first terms))
            (all-lambdas-serialized-in-termsp (rest terms))))))

;; todo: the induction-depth limit here prevents me from seeing all the checkpoints, even though I used :otf-flg
;; (thm
;;  (implies (and (symbol-alistp bindings)
;;                (pseudo-term-listp (strip-cdrs bindings))
;;                (all-lambdas-serialized-in-termsp (strip-cdrs bindings))
;;                (pseudo-termp body))
;;           (all-lambdas-serialized-in-termp (make-lambda-nest bindings body)))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (enable make-lambda-nest))))

(defthm all-lambdas-serialized-in-termsp-of-remove1-equal
  (implies (all-lambdas-serialized-in-termsp terms)
           (all-lambdas-serialized-in-termsp (remove1-equal term terms))))

(defthm all-lambdas-serialized-in-termsp-of-take
  (implies (all-lambdas-serialized-in-termsp terms)
           (all-lambdas-serialized-in-termsp (take n terms))))

(defthm all-lambdas-serialized-in-termsp-of-revappend
  (implies (and (all-lambdas-serialized-in-termsp terms1)
                (all-lambdas-serialized-in-termsp terms2))
           (all-lambdas-serialized-in-termsp (revappend terms1 terms2))))

(defthm all-lambdas-serialized-in-termsp-when-symbol-listp
  (implies (symbol-listp terms)
           (all-lambdas-serialized-in-termsp terms)))

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

;; zz
;; (thm
;;  (implies (all-lambdas-serialized-in-termsp (strip-cdrs bindings))
;;           (all-lambdas-serialized-in-termsp (strip-cdrs (serialize-bindings bindings names-to-avoid))))
;;  :hints (("Goal" :in-theory (enable serialize-bindings))))

;; (defthm-flag-serialize-lambdas-in-term
;;   (defthm theorem-for-serialize-lambdas-in-term
;;     (implies (and (pseudo-termp term)
;;                   (symbol-listp vars-to-avoid))
;;              (all-lambdas-serialized-in-termp (serialize-lambdas-in-term term vars-to-avoid)))
;;     :flag serialize-lambdas-in-term)
;;   (defthm theorem-for-serialize-lambdas-in-terms
;;     (implies (and (pseudo-term-listp terms)
;;                   (symbol-listp vars-to-avoid))
;;              (all-lambdas-serialized-in-termsp (serialize-lambdas-in-terms terms vars-to-avoid)))
;;     :flag serialize-lambdas-in-terms)
;;   :hints (("Goal" :in-theory (enable serialize-lambdas-in-terms
;;                                      serialize-lambdas-in-term))))
