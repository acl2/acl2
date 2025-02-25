; A utility for adding a node but normalizing its xors first.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-array-builders")
(include-book "def-dag-builder-theorems")
(include-book "leaves-of-normalized-bitxor-nest")
(include-book "leaves-of-normalized-bvxor-nest")
(include-book "merge-and-remove-dups")
(include-book "add-bitxor-nest-to-dag-array")
(include-book "add-bvxor-nest-to-dag-array")
(include-book "rewrite-stobj")
(include-book "rewrite-stobj2")
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local
 (defthm consp-of-cdr-forward-to-consp
   (implies (consp (cdr x))
            (consp x))
   :rule-classes :forward-chaining))

(defthm bounded-darg-listp-of-merge-and-remove-dups
  (implies (and (bounded-darg-listp lst1 dag-len)
                (bounded-darg-listp lst2 dag-len)
                (bounded-darg-listp acc dag-len))
           (bounded-darg-listp (merge-and-remove-dups lst1 lst2 acc) dag-len))
  :hints (("Goal" :in-theory (enable merge-and-remove-dups))))

;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; TODO: Don't pass through the dag-variable-alist?
(defund add-and-normalize-expr (fn
                                simplified-args
                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (declare (xargs :guard (and (symbolp fn)
                              (not (eq 'quote fn))
                              ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              ;; (bounded-darg-listp args dag-len)
                              ;; (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              ;; (dag-constant-alistp dag-constant-alist)
                              ;; (equal (alen1 'dag-array dag-array)
                              ;;        (alen1 'dag-parent-array dag-parent-array)))
                              (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (bounded-darg-listp simplified-args dag-len))))
  (if (and (eq fn 'bvxor)
           ;; normalize-xors
           (consp (cdr (cdr simplified-args))) ; for guards
           (darg-quoted-natp (first simplified-args)) ; relax?
           )
      ;;it's a bvxor. note that since the args are simplified, if they are bvxor nests they are *normalized* bvxor nests
      (b* ((bvxor-width (unquote (first simplified-args)))
           ;; get xors from arg2 (TODO: Consider memoizing):
           ((mv arg2-constant arg2-leaves-increasing)
            (leaves-of-normalized-bvxor-nest (second simplified-args) bvxor-width dag-array dag-len))
           ;; get xors from arg3 (TODO: Consider memoizing):
           ((mv arg3-constant arg3-leaves-increasing)
            (leaves-of-normalized-bvxor-nest (third simplified-args) bvxor-width dag-array dag-len))
           ;; Make the leaves of the new nest:
           (nodenum-leaves-decreasing (merge-and-remove-dups arg2-leaves-increasing arg3-leaves-increasing nil))
           (accumulated-constant (bvxor bvxor-width arg2-constant arg3-constant))
           (leaves-increasing (if (eql 0 accumulated-constant)
                                  (reverse-list nodenum-leaves-decreasing) ;if the constant is 0, drop it
                                (revappend nodenum-leaves-decreasing
                                           (list (enquote accumulated-constant)))))
           ;; (- (cw "(BVXOR nest with ~x0 leaves.)~%" (len leaves-increasing)))
           )
        ;; Build the new nest: ;; TODO: handle the constant separately
        (add-bvxor-nest-to-dag-array leaves-increasing ; reverse of the order we want them in
                                     bvxor-width
                                     (enquote bvxor-width)
                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
    (if (and (eq fn 'bitxor)
             ;; normalize-xors
             (consp (cdr simplified-args)) ; for guards
             )
        ;;it's a bitxor. note that since the args are simplified, if they are bitxor nests they are *normalized* bitxor nests
        (b* ( ;; get xors from arg1 (TODO: Consider memoizing):
             ((mv arg1-constant arg1-leaves-increasing)
              (leaves-of-normalized-bitxor-nest (first simplified-args) dag-array dag-len))
             ;; get xors from arg2 (TODO: Consider memoizing):
             ((mv arg2-constant arg2-leaves-increasing)
              (leaves-of-normalized-bitxor-nest (second simplified-args) dag-array dag-len))
             ;; Make the leaves of the new nest:
             (nodenum-leaves-decreasing (merge-and-remove-dups arg1-leaves-increasing arg2-leaves-increasing nil))
             (accumulated-constant (bitxor arg1-constant arg2-constant))
             (leaves-increasing (if (eql 0 accumulated-constant)
                                    (reverse-list nodenum-leaves-decreasing) ;if the constant is 0, drop it
                                  (revappend nodenum-leaves-decreasing
                                             (list (enquote accumulated-constant)))))
             ;; (- (cw "(BITXOR nest with ~x0 leaves.)~%" (len leaves-increasing)))
             )
          ;; Build the new nest: ;; TODO: handle the constant separately
          (add-bitxor-nest-to-dag-array leaves-increasing ; reverse of the order we want them in
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
      ;; Not a function that we handle specially:
      (b* (((mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist)
            (add-function-call-expr-to-dag-array fn simplified-args ;(if any-arg-was-simplifiedp (cons fn args) tree) ;could put back the any-arg-was-simplifiedp trick to save this cons
                                                 dag-array dag-len dag-parent-array dag-constant-alist)))
        (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))

(local
  (def-dag-builder-theorems (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    :recursivep nil
    :hyps ((symbolp fn)
           (not (eq 'quote fn))
           ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
           ;; (bounded-darg-listp args dag-len)
           ;; (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
           ;; (dag-constant-alistp dag-constant-alist)
           ;; (equal (alen1 'dag-array dag-array)
           ;;        (alen1 'dag-parent-array dag-parent-array)))
           (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
           (bounded-darg-listp simplified-args dag-len))))

(local
  (defthmd dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
    (implies (and (symbolp fn)
                  (not (eq 'quote fn))
                  ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  ;; (bounded-darg-listp args dag-len)
                  ;; (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                  ;; (dag-constant-alistp dag-constant-alist)
                  ;; (equal (alen1 'dag-array dag-array)
                  ;;        (alen1 'dag-parent-array dag-parent-array)))
                  (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                  (bounded-darg-listp simplified-args dag-len)
                  (not (mv-nth 0 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
             (dargp-less-than (mv-nth 1 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                              (mv-nth 3 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
    :hints (("Goal" :in-theory (enable add-and-normalize-expr)))))

(local
  (defthmd dargp-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
    (implies (and (symbolp fn)
                  (not (eq 'quote fn))
                  ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  ;; (bounded-darg-listp args dag-len)
                  ;; (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                  ;; (dag-constant-alistp dag-constant-alist)
                  ;; (equal (alen1 'dag-array dag-array)
                  ;;        (alen1 'dag-parent-array dag-parent-array)))
                  (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                  (bounded-darg-listp simplified-args dag-len)
                  (not (mv-nth 0 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
             (dargp (mv-nth 1 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
    :hints (("Goal" :use dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
             :in-theory (disable dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr)))))

(local
  (defthm dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr-gen
    (implies (and (<= (mv-nth 3 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)) bound)
                  (symbolp fn)
                  (not (eq 'quote fn))
                  ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  ;; (bounded-darg-listp args dag-len)
                  ;; (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                  ;; (dag-constant-alistp dag-constant-alist)
                  ;; (equal (alen1 'dag-array dag-array)
                  ;;        (alen1 'dag-parent-array dag-parent-array)))
                  (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                  (bounded-darg-listp simplified-args dag-len)
                  (not (mv-nth 0 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
             (dargp-less-than (mv-nth 1 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                              bound))
    :hints (("Goal" :use (dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr)
             :in-theory (disable dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr)))))

;; Uses consp as the normal form
(local
  (defthm myquotep-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
    (implies (and (symbolp fn)
                  (not (eq 'quote fn))
                  ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  ;; (bounded-darg-listp args dag-len)
                  ;; (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                  ;; (dag-constant-alistp dag-constant-alist)
                  ;; (equal (alen1 'dag-array dag-array)
                  ;;        (alen1 'dag-parent-array dag-parent-array)))
                  (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                  (bounded-darg-listp simplified-args dag-len)
                  (not (mv-nth 0 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
             (equal (myquotep (mv-nth 1 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                    (consp (mv-nth 1 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
    :hints (("Goal" :use (:instance dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr)
             :in-theory (disable dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
                                 dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr-gen)))))

;; Uses consp as the normal form
(local
  (defthm natp-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
    (implies (and (symbolp fn)
                  (not (eq 'quote fn))
                  ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  ;; (bounded-darg-listp args dag-len)
                  ;; (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                  ;; (dag-constant-alistp dag-constant-alist)
                  ;; (equal (alen1 'dag-array dag-array)
                  ;;        (alen1 'dag-parent-array dag-parent-array)))
                  (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                  (bounded-darg-listp simplified-args dag-len)
                  (not (mv-nth 0 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
             (equal (natp (mv-nth 1 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                    (not (consp (mv-nth 1 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))))
    :hints (("Goal" :use (:instance dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr)
             :in-theory (disable dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
                                 dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr-gen)))))

;drop?
(local
  (defthm <-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
    (implies (and (symbolp fn)
                  (not (eq 'quote fn))
                  ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  ;; (bounded-darg-listp args dag-len)
                  ;; (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                  ;; (dag-constant-alistp dag-constant-alist)
                  ;; (equal (alen1 'dag-array dag-array)
                  ;;        (alen1 'dag-parent-array dag-parent-array)))
                  (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                  (bounded-darg-listp simplified-args dag-len)
                  (not (mv-nth 0 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (not (consp (mv-nth 1 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
                  )
             (< (mv-nth 1 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                (mv-nth 3 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
    :hints (("Goal" :use (:instance dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr)
             :in-theory (disable dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
                                 dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr-gen)))))

(local
  (defthm <-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr-gen
    (implies (and (<= (mv-nth 3 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)) bound)
                  (symbolp fn)
                  (not (eq 'quote fn))
                  ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  ;; (bounded-darg-listp args dag-len)
                  ;; (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                  ;; (dag-constant-alistp dag-constant-alist)
                  ;; (equal (alen1 'dag-array dag-array)
                  ;;        (alen1 'dag-parent-array dag-parent-array)))
                  (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                  (bounded-darg-listp simplified-args dag-len)
                  (not (mv-nth 0 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (not (consp (mv-nth 1 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
                  )
             (< (mv-nth 1 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                bound))
    :hints (("Goal" :use <-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
             :in-theory (disable <-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr)))))

(local
  (defthm dag-constant-alistp-mv-nth-5-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
    (implies (and (symbolp fn)
                  (not (eq 'quote fn))
                  ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  ;; (bounded-darg-listp args dag-len)
                  ;; (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                  ;; (dag-constant-alistp dag-constant-alist)
                  ;; (equal (alen1 'dag-array dag-array)
                  ;;        (alen1 'dag-parent-array dag-parent-array)))
                  (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                  (bounded-darg-listp simplified-args dag-len)
                  (not (mv-nth 0 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
             (dag-constant-alistp (mv-nth 5 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
    :hints (("Goal" :use (type-of-add-and-normalize-expr)
             :in-theory (disable type-of-add-and-normalize-expr)))))

(local
  (defthm dag-variable-alistp-mv-nth-6-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
    (implies (and (symbolp fn)
                  (not (eq 'quote fn))
                  ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  ;; (bounded-darg-listp args dag-len)
                  ;; (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                  ;; (dag-constant-alistp dag-constant-alist)
                  ;; (equal (alen1 'dag-array dag-array)
                  ;;        (alen1 'dag-parent-array dag-parent-array)))
                  (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                  (bounded-darg-listp simplified-args dag-len)
                  (not (mv-nth 0 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
             (dag-variable-alistp (mv-nth 6 (add-and-normalize-expr fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
    :hints (("Goal" :use (type-of-add-and-normalize-expr)
             :in-theory (disable type-of-add-and-normalize-expr)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp nodenum-or-quotep rewrite-stobj2).
(defund add-and-maybe-normalize-expr (fn args rewrite-stobj rewrite-stobj2)
  (declare (xargs :guard (and (symbolp fn)
                              (not (eq 'quote fn))
                              ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              ;; (bounded-darg-listp args dag-len)
                              ;; (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              ;; (dag-constant-alistp dag-constant-alist)
                              ;; (equal (alen1 'dag-array dag-array)
                              ;;        (alen1 'dag-parent-array dag-parent-array)))
                              (wf-rewrite-stobj2 rewrite-stobj2)
                              (bounded-darg-listp args (get-dag-len rewrite-stobj2)))
                  :stobjs (rewrite-stobj rewrite-stobj2)
                  :guard-hints (("Goal" :in-theory (e/d (wf-rewrite-stobj2) (WF-REWRITE-STOBJ2-CONJUNCTS))))))
  (b* (((mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (if (not (get-normalize-xors rewrite-stobj))
            ;; not normalizing xors:
            (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist) ; no dag-variable-alist
              (add-function-call-expr-to-dag-array fn args ;(if any-arg-was-simplifiedp (cons fn args) tree) ;could put back the any-arg-was-simplifiedp trick to save this cons
                                                   (get-dag-array rewrite-stobj2) (get-dag-len rewrite-stobj2) (get-dag-parent-array rewrite-stobj2) (get-dag-constant-alist rewrite-stobj2))
              (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist (get-dag-variable-alist rewrite-stobj2)))
          ;; normalizing xors:
          (add-and-normalize-expr fn args ; can we often save consing FN onto ARGS in this?
                                  (get-dag-array rewrite-stobj2) (get-dag-len rewrite-stobj2) (get-dag-parent-array rewrite-stobj2) (get-dag-constant-alist rewrite-stobj2) (get-dag-variable-alist rewrite-stobj2))))
       ((when erp) (mv erp nodenum-or-quotep rewrite-stobj2))
       ;; todo: optimize this stuf by building versions of the dag-builders that traffic in the rewrite-stobj2
       (rewrite-stobj2 (put-dag-array dag-array rewrite-stobj2))
       (rewrite-stobj2 (put-dag-len dag-len rewrite-stobj2))
       (rewrite-stobj2 (put-dag-parent-array dag-parent-array rewrite-stobj2))
       (rewrite-stobj2 (put-dag-constant-alist dag-constant-alist rewrite-stobj2))
       (rewrite-stobj2 (put-dag-variable-alist dag-variable-alist rewrite-stobj2)))
    (mv (erp-nil) nodenum-or-quotep rewrite-stobj2)))

(defthm add-and-maybe-normalize-expr-return-type
  (implies (and (symbolp fn) ; needed?
                (not (eq 'quote fn))
                ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                ;; (bounded-darg-listp args dag-len)
                ;; (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                ;; (dag-constant-alistp dag-constant-alist)
                ;; (equal (alen1 'dag-array dag-array)
                ;;        (alen1 'dag-parent-array dag-parent-array)))
                (rewrite-stobj2p rewrite-stobj2)
                (wf-rewrite-stobj2 rewrite-stobj2)
                (bounded-darg-listp args (get-dag-len rewrite-stobj2)))
           (mv-let (erp darg new-rewrite-stobj2)
             (add-and-maybe-normalize-expr fn args rewrite-stobj rewrite-stobj2)
             (implies (not erp)
                      (and (dargp darg)
                           (equal (natp darg) (not (consp darg))) ; use consp as the normal form
                           (dargp-less-than darg (get-dag-len new-rewrite-stobj2))
                           (implies (not (consp darg))
                                    (< darg (get-dag-len new-rewrite-stobj2)))
                           (rewrite-stobj2p new-rewrite-stobj2)
                           (wf-rewrite-stobj2 new-rewrite-stobj2)
                           ;; dag doesn't get shorter:
                           (<= (get-dag-len rewrite-stobj2) (get-dag-len new-rewrite-stobj2))
                           ))))
  :hints (("Goal"
           :use (:instance type-of-add-and-normalize-expr
                           (simplified-args args)
                           (dag-array (get-dag-array rewrite-stobj2))
                           (dag-len (get-dag-len rewrite-stobj2))
                           (dag-parent-array (get-dag-parent-array rewrite-stobj2))
                           (dag-constant-alist (get-dag-constant-alist rewrite-stobj2))
                           (dag-variable-alist (get-dag-variable-alist rewrite-stobj2)))

           :in-theory (e/d (add-and-maybe-normalize-expr
                            wf-rewrite-stobj2
                            wf-dagp
                            dargp-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
                            dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr)
                           (type-of-add-and-normalize-expr
                            wf-rewrite-stobj2-conjuncts)))))

;; a bit gross, as it makes a claim about a single component of the stobj
;; but this helps to support some rewriter rules with very few hyps.
(defthm add-and-maybe-normalize-expr-return-type-2
  (implies (natp (get-dag-len rewrite-stobj2))
           (mv-let (erp darg new-rewrite-stobj2)
             (add-and-maybe-normalize-expr fn args rewrite-stobj rewrite-stobj2)
             (declare (ignore darg erp))
             (natp (get-dag-len new-rewrite-stobj2))))
  :hints (("Goal"
           :use (:instance type-of-add-and-normalize-expr
                           (simplified-args args)
                           (dag-array (get-dag-array rewrite-stobj2))
                           (dag-len (get-dag-len rewrite-stobj2))
                           (dag-parent-array (get-dag-parent-array rewrite-stobj2))
                           (dag-constant-alist (get-dag-constant-alist rewrite-stobj2))
                           (dag-variable-alist (get-dag-variable-alist rewrite-stobj2)))
           :in-theory (e/d (add-and-maybe-normalize-expr
                            wf-rewrite-stobj2
                            wf-dagp
                            dargp-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
                            dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr)
                           (type-of-add-and-normalize-expr
                            wf-rewrite-stobj2-conjuncts
                            natp)))))
