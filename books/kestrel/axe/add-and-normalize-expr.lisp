; A utility for adding a node but normalizing its xors first.
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

(include-book "dag-array-builders")
(include-book "def-dag-builder-theorems")
(include-book "leaves-of-normalized-bitxor-nest")
(include-book "leaves-of-normalized-bvxor-nest")
(include-book "merge-and-remove-pairs-of-dups")
(include-book "add-bitxor-nest-to-dag-array")
(include-book "add-bvxor-nest-to-dag-array")
(include-book "rewrite-stobj")
(include-book "rewrite-stobj2")
(include-book "normalize-xors")
(local (include-book "rational-lists"))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "merge-sort-less-than-rules"))

(local (in-theory (e/d (rationalp-when-natp all-rationalp-when-nat-listp) (natp))))

(local
 (defthm consp-of-cdr-forward-to-consp
   (implies (consp (cdr x))
            (consp x))
   :rule-classes :forward-chaining))

(defthm bounded-darg-listp-of-merge-and-remove-pairs-of-dups
  (implies (and (bounded-darg-listp lst1 dag-len)
                (bounded-darg-listp lst2 dag-len)
                (bounded-darg-listp acc dag-len))
           (bounded-darg-listp (merge-and-remove-pairs-of-dups lst1 lst2 acc) dag-len))
  :hints (("Goal" :in-theory (enable merge-and-remove-pairs-of-dups))))

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
           (nodenum-leaves-decreasing (merge-and-remove-pairs-of-dups arg2-leaves-increasing arg3-leaves-increasing nil))
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
             (nodenum-leaves-decreasing (merge-and-remove-pairs-of-dups arg1-leaves-increasing arg2-leaves-increasing nil))
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
    :hints (("Goal" :use dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
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
    :hints (("Goal" :use dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
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
    :hints (("Goal" :use dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
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

;; Returns (mv erp nodenum rewrite-stobj2).
;move?
(defund add-function-call-expr-to-rewrite-array-stobj (fn dargs rewrite-stobj2)
  (declare (xargs :guard (and (symbolp fn)
                              (not (eq 'quote fn))
                              (wf-rewrite-stobj2p rewrite-stobj2)
                              (bounded-darg-listp dargs (get-dag-len rewrite-stobj2)))
                  :stobjs rewrite-stobj2))
  (b* ((dag-array (get-dag-array rewrite-stobj2))
       (dag-len (get-dag-len rewrite-stobj2))
       (dag-parent-array (get-dag-parent-array rewrite-stobj2))
       (dag-constant-alist (get-dag-constant-alist rewrite-stobj2))
       ((mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist) ; no dag-variable-alist
        (add-function-call-expr-to-dag-array fn dargs dag-array dag-len dag-parent-array dag-constant-alist))
       ((when erp) (mv erp 0 rewrite-stobj2))
       (rewrite-stobj2 (put-dag-array dag-array rewrite-stobj2))
       (rewrite-stobj2 (put-dag-len dag-len rewrite-stobj2))
       (rewrite-stobj2 (put-dag-parent-array dag-parent-array rewrite-stobj2))
       (rewrite-stobj2 (put-dag-constant-alist dag-constant-alist rewrite-stobj2)))
    (mv (erp-nil) nodenum rewrite-stobj2)))

(defthm add-function-call-expr-to-rewrite-array-stobj-return-type
  (implies (and (symbolp fn)
                (not (eq 'quote fn))
                (wf-rewrite-stobj2p rewrite-stobj2)
                (bounded-darg-listp dargs (get-dag-len rewrite-stobj2))
                (rewrite-stobj2p rewrite-stobj2))
           (mv-let (erp nodenum new-rewrite-stobj2)
             (add-function-call-expr-to-rewrite-array-stobj fn dargs rewrite-stobj2)
             (implies (not erp)
                      (and (natp nodenum)
                           (< nodenum (get-dag-len new-rewrite-stobj2))
                           (rewrite-stobj2p new-rewrite-stobj2)
                           (wf-rewrite-stobj2p new-rewrite-stobj2)))))
  :hints (("Goal" :in-theory (e/d (add-function-call-expr-to-rewrite-array-stobj
                                   wf-rewrite-stobj2p)
                                  (wf-rewrite-stobj2p-conjuncts)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Gets the leaves of the bitxor nest that would result from bitxoring darg1 and darg2.
;; No translation-array in this one.
;; We put the constant before other leaves, which we sort.
(defun bitxor-nest-leaves2 (darg1 darg2 dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (dargp-less-than darg1 dag-len)
                              (dargp-less-than darg2 dag-len))
                  :guard-hints (("Goal" :in-theory (enable all-integerp-when-all-natp)))))
  (b* (((mv nodenum-leaves1 accumulated-constant1)
        (if (consp darg1)
            (mv nil (ifix (unquote darg1)))
          (bitxor-nest-leaves-aux (list darg1) 'dag-array dag-array dag-len nil 0)))
       ((mv nodenum-leaves2 accumulated-constant2)
        (if (consp darg2)
            (mv nil (ifix (unquote darg2)))
          (bitxor-nest-leaves-aux (list darg2) 'dag-array dag-array dag-len nil 0))))
    (cons (enquote (bitxor accumulated-constant1 accumulated-constant2))
          ;; todo: sorting may be unneeded.  maybe reverse?
          (merge-sort-< (append nodenum-leaves1 nodenum-leaves2)))))



;; Gets the leaves of the bvxor nest that would result from bvxoring darg1 and
;; darg2 (using size as the first argument to bvxor).
;; No translation-array in this one.
;; We put the constant before other leaves, which we sort.
(defun bvxor-nest-leaves2 (darg1 darg2 size dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (dargp-less-than darg1 dag-len)
                              (dargp-less-than darg2 dag-len)
                              (natp size) ; unquoted
                              )
                  :guard-hints (("Goal" :in-theory (enable all-integerp-when-all-natp)))))
  (b* (((mv nodenum-leaves1 accumulated-constant1)
        (if (consp darg1)
            (mv nil (ifix (unquote darg1)))
          (bvxor-nest-leaves-aux (list darg1) size 'dag-array dag-array dag-len nil 0)))
       ((mv nodenum-leaves2 accumulated-constant2)
        (if (consp darg2)
            (mv nil (ifix (unquote darg2)))
          (bvxor-nest-leaves-aux (list darg2) size 'dag-array dag-array dag-len nil 0))))
    (cons (enquote (bvxor size accumulated-constant1 accumulated-constant2))
          ;; todo: sorting may be unneeded.  maybe reverse?
          (merge-sort-< (append nodenum-leaves1 nodenum-leaves2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a nodenum, or nil
(defun find-bitxor-node-with-same-leaves (candidates target-bitxor-leaves dag-array dag-len)
  (declare (xargs :guard (and (nat-listp candidates)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (all-< candidates dag-len))))
  (if (endp candidates)
      nil
    (let ((candidate (first candidates)))
      (if (equal target-bitxor-leaves
                 (mv-let (nodenum-leaves accumulated-constant)
                   ;; if the node is a bvxor rather than a bitxor it will have only itself as a bitxor leaf
                   (bitxor-nest-leaves-aux (list candidate) 'dag-array dag-array dag-len nil 0)
                   ;; todo: try not to sort here:
                   ;; todo: avoid consing
                   (cons (enquote accumulated-constant) (merge-sort-< nodenum-leaves))))
          (prog2$ (cw "XOR hit!~%")
                  candidate)
        (prog2$ (cw "XOR miss.~%")
                (find-bitxor-node-with-same-leaves (rest candidates) target-bitxor-leaves dag-array dag-len))))))

(defthm natp-of-find-bitxor-node-with-same-leaves
  (implies (and (find-bitxor-node-with-same-leaves candidates target-bvxor-leaves dag-array dag-len) ; no error
                (nat-listp candidates))
           (natp (find-bitxor-node-with-same-leaves candidates target-bvxor-leaves dag-array dag-len)))
  :hints (("Goal" :in-theory (enable find-bitxor-node-with-same-leaves))))

(defthm not-consp-of-find-bitxor-node-with-same-leaves
  (implies (and (find-bitxor-node-with-same-leaves candidates target-bvxor-leaves dag-array dag-len) ; no error
                (nat-listp candidates))
           (not (consp (find-bitxor-node-with-same-leaves candidates target-bvxor-leaves dag-array dag-len))))
  :hints (("Goal" :in-theory (enable find-bitxor-node-with-same-leaves))))

;; Returns a nodenum, or nil
(defun find-bvxor-node-with-same-leaves (candidates size target-bvxor-leaves dag-array dag-len)
  (declare (xargs :guard (and (nat-listp candidates)
                              (natp size)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (all-< candidates dag-len))))
  (if (endp candidates)
      nil
    (let ((candidate (first candidates)))
      (if (equal target-bvxor-leaves
                 (mv-let (nodenum-leaves accumulated-constant)
                   ;; if the node is not a bvxor of the right size, it will have only itself as a bvxor leaf
                   (bvxor-nest-leaves-aux (list candidate) size 'dag-array dag-array dag-len nil 0)
                   ;; todo: try not to sort here:
                   (cons (enquote accumulated-constant) (merge-sort-< nodenum-leaves))))
          (prog2$ (cw "XOR hit!~%")
                  candidate)
        (prog2$ (cw "XOR miss.~%")
                (find-bvxor-node-with-same-leaves (rest candidates) size target-bvxor-leaves dag-array dag-len))))))

(defthm natp-of-find-bvxor-node-with-same-leaves
  (implies (and (find-bvxor-node-with-same-leaves candidates size target-bvxor-leaves dag-array dag-len) ; no error
                (nat-listp candidates))
           (natp (find-bvxor-node-with-same-leaves candidates size target-bvxor-leaves dag-array dag-len)))
  :hints (("Goal" :in-theory (enable find-bvxor-node-with-same-leaves))))

(defthm not-consp-of-find-bvxor-node-with-same-leaves
  (implies (and (find-bvxor-node-with-same-leaves candidates size target-bvxor-leaves dag-array dag-len) ; no error
                (nat-listp candidates))
           (not (consp (find-bvxor-node-with-same-leaves candidates size target-bvxor-leaves dag-array dag-len))))
  :hints (("Goal" :in-theory (enable find-bvxor-node-with-same-leaves))))

(local
  (defthm eqlablep-when-natp
    (implies (natp x)
             (eqlablep x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This is for the :compact normalize-xors option.
;; Returns (mv erp nodenum rewrite-stobj2).
(defund add-function-call-expr-to-dag-array-compact (fn dargs rewrite-stobj2)
  (declare (xargs :guard (and (symbolp fn)
                              (not (eq 'quote fn))
                              (wf-rewrite-stobj2p rewrite-stobj2)
                              (bounded-darg-listp dargs (get-dag-len rewrite-stobj2)))
                  :guard-hints (("Goal" :in-theory (enable all-rationalp-when-nat-listp)))
                  :stobjs rewrite-stobj2))
  (if (and (eq fn 'bitxor)
           (consp (cdr dargs)) ; for guards
           )
      (b* ((sig (bitxor-signature (first dargs) (second dargs) rewrite-stobj2))
           ;; get all the nodes with the same signature:
           (candidates (xor-signature-to-nodenums-map-get sig rewrite-stobj2))
           (dag-array (get-dag-array rewrite-stobj2))
           (dag-len (get-dag-len rewrite-stobj2))
           ((when (not (all-< candidates dag-len))) ; todo: drop, but need a way to get all keys of a hash table, to strengthen the invariant
            (er hard? 'add-function-call-expr-to-dag-array-compact "Candidate too big.")
            (mv :candidate-too-big nil rewrite-stobj2))
           ;; combine the leaves from both args:
           (bitxor-leaves (bitxor-nest-leaves2 (first dargs) (second dargs) dag-array dag-len))
           ;; (- (cw "~x0 candidates.~%" (len candidates)))
           (maybe-equivalent-nodenum (find-bitxor-node-with-same-leaves candidates bitxor-leaves dag-array dag-len))
           ((when (and maybe-equivalent-nodenum
                       (not (< maybe-equivalent-nodenum dag-len)) ; todo: prove this can't happen
                       ))
            (er hard? 'add-function-call-expr-to-dag-array-compact "Node too big.")
            (mv :candidate-too-big nil rewrite-stobj2)))
        (if maybe-equivalent-nodenum
            (mv (erp-nil) maybe-equivalent-nodenum rewrite-stobj2)
          ;; no pre-existing node found:
          (b* (((mv erp nodenum rewrite-stobj2)
                (add-function-call-expr-to-rewrite-array-stobj fn dargs rewrite-stobj2))
               ((when erp) (mv erp nodenum rewrite-stobj2))
               ;; since we are adding a node, we must update the xor info:
               ;; Set the signature for this node:
               ;; (- (cw "Adding sig ~x0 for ~x1.~%" sig nodenum))
               (rewrite-stobj2 (nodenum-to-xor-signature-map-put nodenum sig rewrite-stobj2))
               ;; Add this node to the list of nodes that have this signature: -- todo: this mixes bvxor (of all sizes) and bitxor
               (nodes-with-this-sig (xor-signature-to-nodenums-map-get sig rewrite-stobj2))
               (nodes-with-this-sig (cons nodenum nodes-with-this-sig))
               ;; (- (cw "New nodes with this sig: ~x0.~%" nodes-with-this-sig))
               (rewrite-stobj2 (xor-signature-to-nodenums-map-put sig nodes-with-this-sig rewrite-stobj2)))
            (mv (erp-nil) nodenum rewrite-stobj2))))
    (if (and (eq 'bvxor fn) ; (bvxor size x y)
             (consp (cddr dargs))
             (consp (first dargs)) ; checks for quotep
             (natp (unquote (first dargs))))
        (b* ((quoted-size (first dargs))
             (size (unquote quoted-size))
             (sig (bvxor-signature size (second dargs) (third dargs) rewrite-stobj2))
             ;; get all the nodes with the same signature:
             (candidates (xor-signature-to-nodenums-map-get sig rewrite-stobj2))
             (dag-array (get-dag-array rewrite-stobj2))
             (dag-len (get-dag-len rewrite-stobj2))
             ((when (not (all-< candidates dag-len))) ; todo: drop, but need a way to get all keys of a hash table
              (er hard? 'add-function-call-expr-to-dag-array-compact "Candidate too big.")
              (mv :candidate-too-big nil rewrite-stobj2))
             (bvxor-leaves (bvxor-nest-leaves2 (second dargs) (third dargs) (unquote (first dargs)) dag-array dag-len))
             ;; (- (cw "~x0 candidates.~%" (len candidates)))
             (maybe-equivalent-nodenum (find-bvxor-node-with-same-leaves candidates size bvxor-leaves dag-array dag-len))
             ((when (and maybe-equivalent-nodenum
                         (not (< maybe-equivalent-nodenum dag-len)) ; todo: prove this can't happen
                         ))
              (er hard? 'add-function-call-expr-to-dag-array-compact "Node too big.")
              (mv :candidate-too-big nil rewrite-stobj2)))
          (if maybe-equivalent-nodenum
              (mv (erp-nil) maybe-equivalent-nodenum rewrite-stobj2)
            ;; no pre-existing node found:
            (b* (((mv erp nodenum rewrite-stobj2)
                  (add-function-call-expr-to-rewrite-array-stobj fn dargs rewrite-stobj2))
                 ((when erp) (mv erp nodenum rewrite-stobj2))
                 ;; since we are adding a node, we must update the xor info:
                 ;; Set the signature for this node:
                 ;; (- (cw "Adding sig ~x0 for ~x1.~%" sig nodenum))
                 (rewrite-stobj2 (nodenum-to-xor-signature-map-put nodenum sig rewrite-stobj2))
                 ;; Add this node to the list of nodes that have this signature: -- todo: this mixes bvxor (of all sizes) and bitxor
                 (nodes-with-this-sig (xor-signature-to-nodenums-map-get sig rewrite-stobj2))
                 (nodes-with-this-sig (cons nodenum nodes-with-this-sig))
                 ;; (- (cw "New nodes with this sig: ~x0.~%" nodes-with-this-sig))
                 (rewrite-stobj2 (xor-signature-to-nodenums-map-put sig nodes-with-this-sig rewrite-stobj2)))
              (mv (erp-nil) nodenum rewrite-stobj2))))
      ;; not an xor:
      (add-function-call-expr-to-rewrite-array-stobj fn dargs rewrite-stobj2))))

(defthm add-function-call-expr-to-dag-array-compact-return-type
  (implies (and (symbolp fn)
                (not (eq 'quote fn))
                (wf-rewrite-stobj2p rewrite-stobj2)
                (rewrite-stobj2p rewrite-stobj2)
                (bounded-darg-listp dargs (get-dag-len rewrite-stobj2)))
           (mv-let (erp nodenum rewrite-stobj2)
             (add-function-call-expr-to-dag-array-compact fn dargs rewrite-stobj2)
             (implies (not erp)
                      (and (natp nodenum)
                           (rewrite-stobj2p rewrite-stobj2)
                           (wf-rewrite-stobj2p rewrite-stobj2)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-compact))))


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
                              (wf-rewrite-stobj2p rewrite-stobj2)
                              (bounded-darg-listp args (get-dag-len rewrite-stobj2)))
                  :stobjs (rewrite-stobj rewrite-stobj2)
                  :guard-hints (("Goal" :in-theory (e/d (wf-rewrite-stobj2p) (WF-REWRITE-STOBJ2P-CONJUNCTS))))))
  (let ((normalize-xors (get-normalize-xors rewrite-stobj)))
    (if (eq :compact normalize-xors)
        (add-function-call-expr-to-dag-array-compact fn args rewrite-stobj2)
      (b* (((mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (if (not normalize-xors)
                ;; not normalizing xors:
                ;; todo: can we call add-function-call-expr-to-rewrite-array-stobj?
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
        (mv (erp-nil) nodenum-or-quotep rewrite-stobj2)))))

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
                (wf-rewrite-stobj2p rewrite-stobj2)
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
                           (wf-rewrite-stobj2p new-rewrite-stobj2)
                           ;; dag doesn't get shorter:
                           (<= (get-dag-len rewrite-stobj2) (get-dag-len new-rewrite-stobj2))
                           ))))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
           :use (:instance type-of-add-and-normalize-expr
                           (simplified-args args)
                           (dag-array (get-dag-array rewrite-stobj2))
                           (dag-len (get-dag-len rewrite-stobj2))
                           (dag-parent-array (get-dag-parent-array rewrite-stobj2))
                           (dag-constant-alist (get-dag-constant-alist rewrite-stobj2))
                           (dag-variable-alist (get-dag-variable-alist rewrite-stobj2)))
           :in-theory (e/d (add-and-maybe-normalize-expr
                            ;wf-rewrite-stobj2p
                            ;wf-dagp
                            dargp-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
                            dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
                            dargp-when-natp
                            add-function-call-expr-to-dag-array-compact
                            add-function-call-expr-to-rewrite-array-stobj
                            wf-dagp
                            wf-rewrite-stobj2p
                            dargp-less-than-when-natp)
                           (type-of-add-and-normalize-expr
                            wf-rewrite-stobj2p-conjuncts
                            )))))

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
                            wf-rewrite-stobj2p
                            wf-dagp
                            dargp-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
                            dargp-less-than-of-mv-nth-1-of-add-and-normalize-expr-and-mv-nth-3-of-add-and-normalize-expr
                            add-function-call-expr-to-dag-array-compact
                            add-function-call-expr-to-rewrite-array-stobj)
                           (type-of-add-and-normalize-expr
                            wf-rewrite-stobj2p-conjuncts
                            natp)))))
