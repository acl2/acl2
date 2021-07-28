; Simple utilities about declares
;
; Copyright (C) 2015-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; Simple utilities about declares (e.g., in defuns).  Unlike declares.lisp,
;; this file does not deal with manipulation of untranslated terms.

;; Note that a function can have multiple DECLAREs, each possibly containing an
;; XARGS (or several), etc.

(include-book "keyword-value-lists2")
(include-book "conjunctions")
(include-book "std/lists/list-defuns" :dir :system) ;for flatten
(include-book "std/util/bstar" :dir :system)

;; Recognize the "arguments" of an xargs declare (a list of alternating keys
;; and values). TODO: Add checks for the values supplied for the various kinds
;; of keys.
(defun xargsp (xargs)
  (declare (xargs :guard t))
  (keyword-value-listp xargs))

(defthm xargsp-of-cons-of-cons
  (equal (xargsp (cons key (cons val lst)))
         (and (keywordp key)
              (xargsp lst)))
  :hints (("Goal" :in-theory (enable xargsp))))

;; Recognize an "argument" to a declare, such as (xargs ...) or (type ... ...).
;; TODO: Add more checks for the various kinds of declares.
(defun declare-argp (declare-arg)
  (declare (xargs :guard t))
  (and (true-listp declare-arg)
       (consp declare-arg)
       (member-eq (ffn-symb declare-arg) '(ignore ignorable irrelevant type xargs optimize))
       (implies (eq 'xargs (car declare-arg))
                (xargsp (cdr declare-arg)))))

(defun all-declare-argp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (declare-argp (first x))
         (all-declare-argp (rest x)))))

(defthm all-declare-argp-of-append
  (equal (all-declare-argp (append x y))
         (and (all-declare-argp x)
              (all-declare-argp y))))

(defthm all-declare-argp-of-cdr
  (implies (all-declare-argp declare-args)
           (all-declare-argp (cdr declare-args))))

;; Recognize a declare, such as (declare (xargs ...) (type ...)).
(defund declarep (declare)
  (declare (xargs :guard t))
  (and (consp declare)
       (eq 'declare (ffn-symb declare))
       (true-listp (fargs declare))
       (all-declare-argp (fargs declare))))

(defthm declarep-of-cons
  (equal (declarep (cons a x))
         (and (equal a 'declare)
              (true-listp x)
              (all-declare-argp x)))
  :hints (("Goal" :in-theory (enable declarep))))

(defthm declarep-forward-to-true-lisp
  (implies (declarep declare)
           (true-listp declare))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable declarep))))

(defthm all-declare-argp-of-cdr-when-declarep
  (implies (declarep declare)
           (all-declare-argp (cdr declare)))
  :hints (("Goal" :in-theory (enable declarep))))

;(defforall-simple declarep) ;introduces all-declarep
;(verify-guards all-declarep)

(defun all-declarep (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
      (and (declarep (first x))
           (all-declarep (rest x)))))

(defthm declarep-of-car
  (implies (and (all-declarep declares)
                (consp declares))
           (declarep (car declares))))

(defthm all-declarep-of-cons
  (equal (all-declarep (cons declare declares))
         (and (declarep declare)
              (all-declarep declares)))
  :hints (("Goal" :in-theory (enable all-declarep))))

(defthm all-declarep-of-take
  (implies (and (all-declarep declares)
                (<= (nfix n) (len declares)))
           (all-declarep (take n declares)))
  :hints (("Goal" :in-theory (enable all-declarep))))

;;; Extract the xargs from some declares

;returns a keyword-value-listp
(defun get-xargs-from-declare-arg (declare-arg)
  (declare (xargs :guard (declare-argp declare-arg)))
  (if (eq 'xargs (ffn-symb declare-arg))
      (fargs declare-arg)
    nil))

;returns a keyword-value-listp
(defun get-xargs-from-declare-args (declare-args)
  (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (append (get-xargs-from-declare-arg (first declare-args))
            (get-xargs-from-declare-args (rest declare-args)))))

(defthm keyword-value-listp-of-get-xargs-from-declare-args
  (implies (all-declare-argp declare-args)
           (keyword-value-listp (get-xargs-from-declare-args declare-args))))

;returns a keyword-value-listp
(defun get-xargs-from-declare (declare)
  (declare (xargs :guard (declarep declare)))
  (get-xargs-from-declare-args (fargs declare)))

;; Merge and/or check consistency of the two values for the given xarg. Returns
;; a single value to use for the xarg, or throws an error in case of
;; inconsistency.
(defund merge-xargs (key val1 val2)
  (declare (xargs :guard (symbolp key)))
  (if (eq key :guard)
      ;; Multiple guards get conjoined:
      (if (equal val1 val2)
          val1
        `(and ,val1 ,val2))
    ;; These must be consistent
    (if (member-eq key '(:guard-debug
                         :measure
                         :measure-debug
                         :mode
                         :non-executable
                         :normalize
                         :otf-flg
                         :ruler-extenders
                         :split-types
                         :verify-guards
                         :well-founded-relation))
        (if (not (equal val1 val2))
            (er hard? 'merge-xargs "Incompatible values, ~x0 and ~x1, for xarg ~x2."
                val1 val2 key)
          val1)
      ;; If more than one of these is given, we take the union:
      (if (member-eq key '(:hints :guard-hints))
          (if (not (true-listp val1))
              (er hard? 'merge-xargs "Bad xarg, ~x0, for ~x1." val1 key)
            (if (not (true-listp val2))
                (er hard? 'merge-xargs "Bad xarg, ~x0, for ~x1." val2 key)
              (union-equal val1 val2)))
        (if (eq key :stobjs)
            ;; We essentually take the union of stobj lists, but we have to
            ;; handle the case of a single symbol given to represent a
            ;; singleton list:
            (let* ((stobjs1 (if (symbolp val1)
                                (list val1)
                              (if (not (symbol-listp val1))
                                  (er hard? 'merge-xargs "Bad :stobjs xarg, ~x0" val1)
                                val1)))
                   (stobjs2 (if (symbolp val2)
                                (list val2)
                              (if (not (symbol-listp val2))
                                  (er hard? 'merge-xargs "Bad :stobjs xarg, ~x0" val2)
                                val2))))
              ;; todo: Consider replacing a singleton lists with just the
              ;; symbol again:
              (union-eq stobjs1 stobjs2))
          (er hard? 'merge-xargs "Unknown kind of xargs: ~x0." key))))))

;; Returns a keyword-value-list.
(defun combine-xargs-for-keys (keys keyword-value-list1 keyword-value-list2)
  (declare (xargs :guard (and (keyword-listp keys)
                              (keyword-value-listp keyword-value-list1)
                              (keyword-value-listp keyword-value-list2))))
  (if (endp keys)
      nil
    (let* ((key (first keys))
           (res1 (assoc-keyword key keyword-value-list1))
           (res2 (assoc-keyword key keyword-value-list2))
           (pair-for-key (if (not res1)
                             (if (not res2)
                                 (er hard? 'combine-xargs-for-keys "Missing key: ~x0." key)
                               ;; key is only in keyword-value-list2, so use the (key and) value there
                               (list (car res2)
                                     (cadr res2)))
                           (if (not res2)
                               ;; key is only in keyword-value-list1, so use the (key and) value there
                               (list (car res1)
                                     (cadr res1))
                             ;; key is in both lists, so we have to merge the values or reject inconsistencies
                             (list key
                                   (merge-xargs key (cadr res1) (cadr res2)))))))
      (append pair-for-key
              (combine-xargs-for-keys (rest keys) keyword-value-list1 keyword-value-list2)))))

(defthm keyword-value-listp-of-combine-xargs-for-keys
  (implies (and (keyword-listp keys)
                (keyword-value-listp keyword-value-list1)
                (keyword-value-listp keyword-value-list2))
           (keyword-value-listp (combine-xargs-for-keys keys keyword-value-list1 keyword-value-list2))))

(defun combine-keyword-value-lists-for-xargs (keyword-value-list1 keyword-value-list2)
  (declare (xargs :guard (and (keyword-value-listp keyword-value-list1)
                              (keyword-value-listp keyword-value-list2))))
  (let ((all-keys (remove-duplicates-eq (append (keyword-value-list-keys keyword-value-list1)
                                                (keyword-value-list-keys keyword-value-list2)))))
    (combine-xargs-for-keys all-keys keyword-value-list1 keyword-value-list2)))

;; ;; Combine two sets of xargs.
;; ;; If there are multiple instances of :guard, this makes the conjunction (because multiple :guards is an error)
;; (defun combine-keyword-value-lists-for-xargs (keyword-value-list1 keyword-value-list2)
;;   (declare (xargs :guard (and (keyword-value-listp keyword-value-list1)
;;                               (keyword-value-listp keyword-value-list2))))
;;   (if (endp keyword-value-list1)
;;       keyword-value-list2
;;     (let ((keyword (first keyword-value-list1))
;;           (value (second keyword-value-list1)))
;;       (if (and (eq :guard keyword)
;;                (assoc-keyword :guard keyword-value-list2))
;;           ;; must combine the guards
;;           (let* ((guard2 (lookup-keyword :guard keyword-value-list2))
;;                  (new-guard `(and ,value
;;                                   ,guard2)))
;;             (cons :guard
;;                   (cons new-guard
;;                         (combine-keyword-value-lists-for-xargs (rest (rest keyword-value-list1))
;;                                                                (clear-key-in-keyword-value-list :guard keyword-value-list2)))))
;;         (cons keyword
;;               (cons value
;;                     (combine-keyword-value-lists-for-xargs (rest (rest keyword-value-list1))
;;                                                            keyword-value-list2)))))))

;; This previously reversed the order
;;(equal (combine-keyword-value-lists-for-xargs '(:foo foox :bar barx) nil) '(:FOO FOOX :BAR BARX))

(defthm keyword-value-listp-of-combine-keyword-value-lists-for-xargs
  (implies (and (keyword-value-listp x)
                (keyword-value-listp y))
           (keyword-value-listp (combine-keyword-value-lists-for-xargs x y))))

;returns a keyword-value-listp
;there may be multiple declares with xargs!  this combines all the keyword-value-lists
(defun get-xargs-from-declares (declares)
  (declare (xargs :guard (all-declarep declares)
                  :verify-guards nil ;done below
                  ))
  (if (atom declares)
      nil
    (let ((declare (first declares)))
      (combine-keyword-value-lists-for-xargs
       (get-xargs-from-declare declare)
       (get-xargs-from-declares (rest declares))))))

(defthm keyword-value-listp-of-get-xargs-from-declares
  (implies (all-declarep declares)
           (keyword-value-listp (get-xargs-from-declares declares)))
  :hints (("Goal" :in-theory (disable len))))

(verify-guards get-xargs-from-declares)

;;; Extract the non-xargs things from some declares

(defun get-non-xargs-from-declare-args (declare-args)
  (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (let ((declare-arg (first declare-args)))
      (if (eq 'xargs (ffn-symb declare-arg))
          ;; skip it because it is an xarg:
          (get-non-xargs-from-declare-args (rest declare-args))
        ;; include it because it is a non-xarg:
        (cons declare-arg (get-non-xargs-from-declare-args (rest declare-args)))))))

(defthm all-declare-argp-of-get-non-xargs-from-declare-args
  (implies (all-declare-argp declare-args)
           (all-declare-argp (get-non-xargs-from-declare-args declare-args))))

;; Returns a list of all the non-xargs declare-args.
(defun get-non-xargs-from-declare (declare)
  (declare (xargs :guard (declarep declare)))
  (get-non-xargs-from-declare-args (fargs declare)))

;; Returns a list of all the non-xargs declare-args.
(defun get-non-xargs-from-declares (declares)
  (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
      nil
    (let ((declare (first declares)))
      (append (get-non-xargs-from-declare declare)
              (get-non-xargs-from-declares (rest declares))))))

(defun declare-arg-has-a-guard-or-type (declare-arg)
  (declare (xargs :guard (declare-argp declare-arg)))
  (let ((kind (ffn-symb declare-arg)))
    (or (eq 'type kind)
        (and (eq 'xargs kind)
             (assoc-keyword :guard (fargs declare-arg))))))

(defun some-declare-arg-has-a-guard-or-type (declare-args)
  (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (or (declare-arg-has-a-guard-or-type (first declare-args))
        (some-declare-arg-has-a-guard-or-type (rest declare-args)))))

(defun declare-has-a-guard-or-type (declare)
  (declare (xargs :guard (declarep declare)))
  (some-declare-arg-has-a-guard-or-type (fargs declare)))

(defun some-declare-has-a-guard-or-type (declares)
  (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
     nil
    (or (declare-has-a-guard-or-type (first declares))
        (some-declare-has-a-guard-or-type (rest declares)))))

;; not right.  see get-irrelevant-formals-from-declares
;; (defun get-types-from-declares (declares)
;;   (declare (xargs :guard (all-declarep declares)))
;;   (if (atom declares)
;;       nil
;;     (let ((declare (first declares)))
;;       (if (eq 'type (ffn-symb declare))
;;           (cons declare (get-types-from-declares (rest declares)))
;;         (get-types-from-declares (rest declares))))))

;returns a list of formals
(defun get-irrelevant-formals-from-declare-arg (declare-arg)
  (declare (xargs :guard (declare-argp declare-arg)))
  (if (eq 'irrelevant-formals (ffn-symb declare-arg))
      (fargs declare-arg)
    nil))

;returns a list of formals
(defun get-irrelevant-formals-from-declare-args (declare-args)
  (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (append (get-irrelevant-formals-from-declare-arg (first declare-args))
            (get-irrelevant-formals-from-declare-args (rest declare-args)))))

;returns a list of formals
(defun get-irrelevant-formals-from-declare (declare)
  (declare (xargs :guard (declarep declare)))
  (get-irrelevant-formals-from-declare-args (fargs declare)))

;returns a list of formals
(defun get-irrelevant-formals-from-declares (declares)
  (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
      nil
    (append (get-irrelevant-formals-from-declare (first declares))
            (get-irrelevant-formals-from-declares (rest declares)))))

(local (in-theory (disable len)))

;returns a singleton list of declares
(defun clean-up-declares (declares)
  (declare (xargs :guard (and (true-listp declares)
                              (all-declarep declares))))
  (let* ((xargs-key-vals (get-xargs-from-declares declares))
         (other-declare-args (get-non-xargs-from-declares declares)))
    `((declare ,@other-declare-args
               (xargs ,@xargs-key-vals)))))

;; Returns a new declare
(defun clean-up-declare (declare)
  (declare (xargs :guard (declarep declare)))
  (let* ((xargs-key-vals (get-xargs-from-declare declare))
         (other-declare-args (get-non-xargs-from-declare declare)))
    `(declare ,@other-declare-args
              (xargs ,@xargs-key-vals))))

;If there is already a "verify-guards t", we remove it from the declares.
;; TODO: Preserve more of the original order of things?
;; TODO: Generalize to any xarg
(defun set-verify-guards-in-declares (declares verify-guards)
  (declare (xargs :guard (and (true-listp declares)
                              (all-declarep declares)
                              (member-eq verify-guards '(t nil)))))
  (let* ((xargs-key-vals (get-xargs-from-declares declares))
         (other-declare-args (get-non-xargs-from-declares declares))
         (xargs-key-vals (clear-key-in-keyword-value-list :verify-guards xargs-key-vals))
         (xargs-key-vals `(:verify-guards ,verify-guards ,@xargs-key-vals)))
    `((declare ,@other-declare-args
               (xargs ,@xargs-key-vals)))))

;; todo: rename to set-verify-guards-nil
(defund add-verify-guards-nil (declares)
  (declare (xargs :guard (and (true-listp declares)
                              (all-declarep declares))))
  (set-verify-guards-in-declares declares nil))

(defthm all-declarep-of-add-verify-guards-nil
  (implies (all-declarep declares)
           (all-declarep (add-verify-guards-nil declares)))
  :hints (("Goal" :in-theory (enable add-verify-guards-nil))))

;; todo: rename to set-verify-guards-t
(defund add-verify-guards-t (declares)
  (declare (xargs :guard (and (true-listp declares)
                              (all-declarep declares))))
  (set-verify-guards-in-declares declares t))

(defthm all-declarep-of-add-verify-guards-t
  (implies (all-declarep declares)
           (all-declarep (add-verify-guards-t declares)))
  :hints (("Goal" :in-theory (enable add-verify-guards-t))))

(defun add-normalize-nil (declares)
  (declare (xargs :guard (and (true-listp declares)
                              (all-declarep declares))))
  (let* ((xargs-key-vals (get-xargs-from-declares declares))
         (other-declare-args (get-non-xargs-from-declares declares))
         (xargs-key-vals (clear-key-in-keyword-value-list :normalize xargs-key-vals)) ;clear any existing :normalize xarg
         (xargs-key-vals `(:normalize nil ,@xargs-key-vals)))
    `((declare ,@other-declare-args
               (xargs ,@xargs-key-vals)))))

;If there is already a "verify-guards t", we remove it from the declares.
;Adds CONJUNCT as the last conjunct in DECLARES.  See also add-guard-conjunct-as-first-conjunct.
(defun add-guard-conjunct (conjunct declares)
  (declare (xargs :guard (and (true-listp declares)
                              (all-declarep declares))))
  (let* ((xargs-key-vals (get-xargs-from-declares declares))
         (other-declare-args (get-non-xargs-from-declares declares))
         (guard (if (assoc-keyword :guard xargs-key-vals)
                    ;;add the new item at the end:
                    (add-conjunct-to-item conjunct
                                          (cadr (assoc-keyword :guard xargs-key-vals)))
                  conjunct)) ;no existing guard
         (xargs-key-vals (clear-key-in-keyword-value-list :guard xargs-key-vals))
         (xargs-key-vals `(:guard ,guard ,@xargs-key-vals)))
    `((declare ,@other-declare-args
               (xargs ,@xargs-key-vals)))))

(defund add-guard-conjunct-as-first-conjunct (conjunct declares)
  (declare (xargs :guard (and (true-listp declares)
                              (all-declarep declares))))
  (let* ((xargs-key-vals (get-xargs-from-declares declares))
         (other-declare-args (get-non-xargs-from-declares declares))
         (guard (if (assoc-keyword :guard xargs-key-vals)
                    `(and ,conjunct
                          ,(cadr (assoc-keyword :guard xargs-key-vals)))
                  conjunct))
         (xargs-key-vals (clear-key-in-keyword-value-list :guard xargs-key-vals))
         (xargs-key-vals `(:guard ,guard ,@xargs-key-vals)))
    `((declare ,@other-declare-args
               (xargs ,@xargs-key-vals)))))

(defun remove-declare-args (type declare-args)
  (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (let ((declare-arg (first declare-args)))
      (if (eq type (ffn-symb declare-arg))
          (remove-declare-args type (rest declare-args))
        (cons declare-arg (remove-declare-args type (rest declare-args)))))))

(defthm all-declare-argp-of-remove-declare-args
  (implies (all-declare-argp declare-args)
           (all-declare-argp (remove-declare-args type declare-args))))

(defun remove-declares (type declares)
  (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
      nil
    (let* ((declare (first declares))
           (args (fargs declare))
           (new-args (remove-declare-args type args)))
      (if new-args
          (cons `(declare ,@new-args)
                (remove-declares type (rest declares)))
        ;; drop this declare since all its args got dropped:
        (remove-declares type (rest declares))))))

(defthm all-declarep-of-remove-declares
  (implies (all-declarep declares)
           (all-declarep (remove-declares type declares)))
  :hints (("Goal" :in-theory (enable))))

(assert-event (equal (remove-declares 'xargs '((declare (xargs :guard (all-declarep declares)))))
                     nil))
(assert-event (equal (remove-declares 'ignore '((declare (xargs :guard (all-declarep declares))) (declare (ignore x))))
                     '((DECLARE (XARGS :GUARD (ALL-DECLAREP DECLARES))))))

(defun add-declare-arg (declare-arg declares)
  (declare (xargs :guard (and (declare-argp declare-arg)
                              (all-declarep declares))))
  (if (atom declares)
      `((declare ,declare-arg))
    (let* ((first-declare (first declares))
           (declare-args (fargs first-declare))
           (first-declare `(declare ,declare-arg ,@declare-args)))
      (cons first-declare (rest declares)))))

(defthm all-declare-argp-of-get-non-xargs-from-declares
  (implies (all-declarep declares)
           (all-declare-argp (get-non-xargs-from-declares declares))))



;returns a measure or nil
(defun get-measure-from-xargs (xargs)
  (declare (xargs :guard (keyword-value-listp xargs)))
  (let ((res (assoc-keyword :measure xargs)))
    (if res
        (cadr res)
      nil)))

;returns a measure or nil
(defun get-measure-from-declare-arg (declare-arg)
  (declare (xargs :guard (declare-argp declare-arg)))
  (if (eq 'xargs (ffn-symb declare-arg))
      (get-measure-from-xargs (fargs declare-arg))
    nil))

;returns a measure or nil
(defun get-measure-from-declare-args (declare-args)
  (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (or (get-measure-from-declare-arg (first declare-args))
        (get-measure-from-declare-args (rest declare-args)))))

;returns a measure or nil
(defun get-measure-from-declare (declare)
  (declare (xargs :guard (declarep declare)))
  (get-measure-from-declare-args (fargs declare)))

;returns a measure or nil
;what if there are multiple declares with a measure? maybe can't happen?
(defun get-measure-from-declares (declares)
  (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
      nil
    (let ((declare (first declares)))
      (or (get-measure-from-declare declare)
          (get-measure-from-declares (rest declares))))))

(assert-event (equal (get-measure-from-declares '((declare (xargs :guard (and (clause-listp clauses)
                                                                              (natp count))
                                                                  :measure (acl2-count count)))))
                     '(acl2-count count)))



(defun remove-xarg (xarg xargs)
  (declare (xargs :guard (and (keywordp xarg)
                              (xargsp xargs))))
  (if (endp xargs)
      nil
    (if (eq xarg (first xargs))
        (remove-xarg xarg (cddr xargs))
      `(,(first xargs) ,(second xargs) ,@(remove-xarg xarg (cddr xargs))))))

(defthm keyword-value-listp-of-remove-xarg
  (implies (keyword-value-listp xargs)
           (keyword-value-listp (remove-xarg xarg xargs)))
  :hints (("Goal" :in-theory (enable remove-xarg keyword-value-listp))))

(defun remove-xarg-in-declare-args (xarg declare-args)
  (declare (xargs :guard (and (keywordp xarg)
                              (all-declare-argp declare-args))))
  (if (atom declare-args)
      nil
    (let ((arg (first declare-args)))
      (if (eq 'xargs (ffn-symb arg))
          (cons `(xargs ,@(remove-xarg xarg (fargs arg)))
                (remove-xarg-in-declare-args xarg (rest declare-args)))
        (cons arg (remove-xarg-in-declare-args xarg (rest declare-args)))))))

(defthm all-declare-argp-of-remove-xarg-in-declare-args
  (implies (all-declare-argp declare-args)
           (all-declare-argp (remove-xarg-in-declare-args xarg declare-args)))
  :hints (("Goal" :in-theory (enable remove-xarg-in-declare-args declare-argp))))

(defund remove-xarg-in-declare (xarg declare)
  (declare (xargs :guard (and (keywordp xarg)
                              (declarep declare))))
  `(declare ,@(remove-xarg-in-declare-args xarg (fargs declare))))

(defthm declarep-of-remove-xarg-in-declare
  (implies (declarep declare)
           (declarep (remove-xarg-in-declare xarg declare)))
  :hints (("Goal" :in-theory (enable declarep remove-xarg-in-declare))))

(defund add-xarg-in-declare (xarg val declare)
  (declare (xargs :guard (and (keywordp xarg)
                              (declarep declare))))
  (let ((declare `(declare (xargs ,xarg ,val)
                           ,@(fargs declare))))
    (clean-up-declare declare)))

;; (add-xarg-in-declare :mode :program '(declare (xargs :guard (keywordp x)))) = (DECLARE (XARGS :MODE :PROGRAM :GUARD (KEYWORDP X)))

(defthm declarep-of-add-xarg-in-declare
  (implies (and (declarep declare)
                (keywordp xarg))
           (declarep (add-xarg-in-declare xarg val declare)))
  :hints (("Goal" :in-theory (enable add-xarg-in-declare))))

;;  Replace the value of XARG with VAL in DECLARE if it's present.  If it's not
;;  present, add it with value VAL.
(defun replace-xarg-in-declare (xarg val declare)
  (declare (xargs :guard (and (keywordp xarg)
                              (declarep declare))
                  :guard-hints (("Goal" :in-theory (disable declarep) ;make global
                                 ))))
  (add-xarg-in-declare xarg val (remove-xarg-in-declare xarg declare)))

(defthm declarep-of-replace-xarg-in-declare
  (implies (and (declarep declare)
                (keywordp xarg))
           (declarep (replace-xarg-in-declare xarg val declare)))
  :hints (("Goal" :in-theory (enable add-xarg-in-declare))))

(defund remove-xarg-in-declares (xarg declares)
  (declare (xargs :guard (and (keywordp xarg)
                              (all-declarep declares))))
  (if (atom declares)
      nil
    (cons (remove-xarg-in-declare xarg (first declares))
          (remove-xarg-in-declares xarg (rest declares)))))

(defthm all-declare-argp-of-remove-xarg-in-declares
  (implies (all-declarep declares)
           (all-declarep (remove-xarg-in-declares xarg declares)))
  :hints (("Goal" :in-theory (enable remove-xarg-in-declares))))

(defund add-xarg-in-declares (xarg val declares)
  (declare (xargs :guard (and (keywordp xarg)
                              (true-listp declares)
                              (all-declarep declares))))
  (clean-up-declares (cons `(declare (xargs ,xarg ,val)) declares)))

(defthm len-of-add-xarg-in-declares
  (equal (len (add-xarg-in-declares xarg val declares))
         1)
  :hints (("Goal" :in-theory (enable add-xarg-in-declares len))))

(defthm all-declarep-of-add-xarg-in-declares
  (implies (and (keywordp xarg)
                (true-listp declares)
                (all-declarep declares))
           (all-declarep (add-xarg-in-declares xarg val declares)))
  :hints (("Goal" :in-theory (enable add-xarg-in-declares))))

;;  Replace the value of XARG with VAL in DECLARES if it's present.  If it's
;;  not present, add it with value VAL.
;; TODO: Preserve more of the original structure of things?
(defund replace-xarg-in-declares (xarg val declares)
  (declare (xargs :guard (and (keywordp xarg)
                              (true-listp declares)
                              (all-declarep declares))))
  (add-xarg-in-declares xarg val (remove-xarg-in-declares xarg declares)))

(defthm len-of-replace-xarg-in-declares
  (equal (len (replace-xarg-in-declares xarg val declares))
         1)
  :hints (("Goal" :in-theory (enable replace-xarg-in-declares))))

(defthm all-declarep-of-replace-xarg-in-declares
  (implies (and (keywordp xarg)
                (true-listp declares)
                (all-declarep declares))
           (all-declarep (replace-xarg-in-declares xarg val declares)))
  :hints (("Goal" :in-theory (enable replace-xarg-in-declares))))


(defthm get-non-xargs-from-declare-args-of-append
  (equal (get-non-xargs-from-declare-args (append x y))
         (append (get-non-xargs-from-declare-args x)
                 (get-non-xargs-from-declare-args y))))

;;; Remove entire :measure (if any)

(defun remove-measure-from-xargs (xargs)
  (declare (xargs :guard (and (xargsp xargs))))
  (if (endp xargs)
      nil
    (if (eq :measure (first xargs))
        (cddr xargs) ;can only be one measure...
      `(,(first xargs) ,(second xargs) ,@(remove-measure-from-xargs (cddr xargs))))))

(defun remove-measure-from-declare-args (declare-args)
  (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (let ((arg (first declare-args)))
      (if (eq 'xargs (ffn-symb arg))
          (cons `(xargs ,@(remove-measure-from-xargs (fargs arg)))
                (remove-measure-from-declare-args (rest declare-args)))
        (cons arg (remove-measure-from-declare-args (rest declare-args)))))))

(defun remove-measure-from-declares (declares)
  (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
      nil
    (cons `(declare ,@(remove-measure-from-declare-args (fargs (first declares))))
          (remove-measure-from-declares (rest declares)))))


;;; Remove entire :hints (if any) -- TODO: Generalize this to remove any given xarg... (might occur more than once?)

(defun remove-termination-hints-from-xargs (xargs)
  (declare (xargs :guard (and (xargsp xargs))))
  (if (endp xargs)
      nil
    (if (eq :hints (first xargs))
        (cddr xargs) ;can only be one termination-hints...
      `(,(first xargs) ,(second xargs) ,@(remove-termination-hints-from-xargs (cddr xargs))))))

(defun remove-termination-hints-from-declare-args (declare-args)
  (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (let ((arg (first declare-args)))
      (if (eq 'xargs (ffn-symb arg))
          (cons `(xargs ,@(remove-termination-hints-from-xargs (fargs arg)))
                (remove-termination-hints-from-declare-args (rest declare-args)))
        (cons arg (remove-termination-hints-from-declare-args (rest declare-args)))))))

(defun remove-termination-hints-from-declares (declares)
  (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
      nil
    (cons `(declare ,@(remove-termination-hints-from-declare-args (fargs (first declares))))
          (remove-termination-hints-from-declares (rest declares)))))

;;;
;;; get-guard-hints-...
;;;

;returns a list of hints
(defun get-guard-hints-from-xargs (xargs)
  (declare (xargs :guard (keyword-value-listp xargs)))
  (let ((res (assoc-keyword :guard-hints xargs)))
    (if res
        (let ((guard-hints (cadr res)))
          (if (not (true-listp guard-hints))
              (er hard? 'get-guard-hints-from-xargs "Guard hints, ~x0, are not a true list." guard-hints)
            guard-hints))
      nil)))

;returns a list of hints
(defun get-guard-hints-from-declare-arg (declare-arg)
  (declare (xargs :guard (declare-argp declare-arg)))
  (if (eq 'xargs (ffn-symb declare-arg))
      (get-guard-hints-from-xargs (fargs declare-arg))
    nil))

;returns a list of hints
(defun get-guard-hints-from-declare-args (declare-args)
  (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (append (get-guard-hints-from-declare-arg (first declare-args))
            (get-guard-hints-from-declare-args (rest declare-args)))))

;returns a list of hints
(defun get-guard-hints-from-declare (declare)
  (declare (xargs :guard (declarep declare)))
  (get-guard-hints-from-declare-args (fargs declare)))

;returns a list of hints.  All :guard-hints in the declares get appended together.
(defun get-guard-hints-from-declares (declares)
  (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
      nil
    (let ((declare (first declares)))
      (append (get-guard-hints-from-declare declare)
              (get-guard-hints-from-declares (rest declares))))))

;;;
;;; get-xarg
;;;

;; Returns (mv foundp val) where foundp is t or nil depending on whether the
;; given XARG exists, and, if foundp is t, then val is the first value of an
;; xarg called XARG.
(defun get-xarg-from-xargs (xarg xargs)
  (declare (xargs :guard (keyword-value-listp xargs)))
  (let ((res (assoc-keyword xarg xargs)))
    (if res
        (mv t (cadr res))
      (mv nil nil))))

;; Returns (mv foundp val) where foundp is t or nil depending on whether the
;; given XARG exists, and, if foundp is t, then val is the first value of an
;; xarg called XARG.
(defun get-xarg-from-declare-arg (xarg declare-arg)
  (declare (xargs :guard (and (keywordp xarg)
                              (declare-argp declare-arg))))
  (if (eq 'xargs (ffn-symb declare-arg))
      (get-xarg-from-xargs xarg (fargs declare-arg))
    (mv nil nil)))

;; Returns (mv foundp val) where foundp is t or nil depending on whether the
;; given XARG exists, and, if foundp is t, then val is the first value of an
;; xarg called XARG.
(defun get-xarg-from-declare-args (xarg declare-args)
  (declare (xargs :guard (and (keywordp xarg)
                              (all-declare-argp declare-args))))
  (if (atom declare-args)
      (mv nil nil)
    (mv-let (res val)
      (get-xarg-from-declare-arg xarg (first declare-args))
      (if res
          (mv res val)
        (get-xarg-from-declare-args xarg (rest declare-args))))))

;; todo: compare to get-xargs...
;; Returns (mv foundp val) where foundp is t or nil depending on whether the
;; given XARG exists, and, if foundp is t, then val is the first value of an
;; xarg called XARG.
(defun get-xarg-from-declare (xarg declare)
  (declare (xargs :guard (and (keywordp xarg)
                              (declarep declare))))
  (get-xarg-from-declare-args xarg (fargs declare)))

;; Returns (mv foundp val) where foundp is t or nil depending on whether the
;; given XARG exists, and, if foundp is t, then val is the first value of an
;; xarg called XARG.
(defun get-xarg-from-declares (xarg declares)
  (declare (xargs :guard (and (keywordp xarg)
                              (all-declarep declares))))
  (if (atom declares)
      (mv nil nil)
    (b* ((declare (first declares))
         ((mv foundp val) (get-xarg-from-declare xarg declare))
         )
      (if foundp
          (mv foundp val)
        (get-xarg-from-declares xarg (rest declares))))))

;;;
;;; get-all-values-of-xarg
;;;

;returns a list of all values of the xarg
;; There can only be one instance of xarg in the keyword-value-list
(defun get-all-values-of-xarg-from-xargs (xarg xargs)
  (declare (xargs :guard (and (keywordp xarg)
                              (keyword-value-listp xargs))))
  (let ((res (assoc-keyword xarg xargs)))
    (if res
        (list (cadr res))
      nil)))

;returns a list of all values of the xarg
(defun get-all-values-of-xarg-from-declare-arg (xarg declare-arg)
  (declare (xargs :guard (and (keywordp xarg)
                              (declare-argp declare-arg))))
  (if (eq 'xargs (ffn-symb declare-arg))
      (get-all-values-of-xarg-from-xargs xarg (fargs declare-arg))
    nil))

;returns a list of all values of the xarg
(defun get-all-values-of-xarg-from-declare-args (xarg declare-args)
  (declare (xargs :guard (and (keywordp xarg)
                              (all-declare-argp declare-args))))
  (if (atom declare-args)
      nil
    (append (get-all-values-of-xarg-from-declare-arg xarg (first declare-args))
            (get-all-values-of-xarg-from-declare-args xarg (rest declare-args)))))

;returns a list of all values of the xarg
(defun get-all-values-of-xarg-from-declare (xarg declare)
  (declare (xargs :guard (and (keywordp xarg)
                              (declarep declare))))
  (get-all-values-of-xarg-from-declare-args xarg (fargs declare)))

;returns a list of all values of the xarg.
(defun get-all-values-of-xarg-from-declares (xarg declares)
  (declare (xargs :guard (and (keywordp xarg)
                              (all-declarep declares))))
  (if (atom declares)
      nil
    (let ((declare (first declares)))
      (append (get-all-values-of-xarg-from-declare xarg declare)
              (get-all-values-of-xarg-from-declares xarg (rest declares))))))

;; TODO: define get-guard-hints-from-declares by calling
;; get-all-values-of-xarg-from-declares and then flatten.

;returns a singleton list of declares
(defun append-to-xarg-in-declares (val xarg declares)
  (declare (xargs :guard (and (true-listp val)
                              (keywordp xarg)
                              (all-declarep declares)
                              (true-listp declares))))
  (let* ((existing-vals (get-all-values-of-xarg-from-declares xarg declares))
         (list-of-vals (flatten existing-vals))
         (new-list-of-vals (append val list-of-vals)))
    (replace-xarg-in-declares xarg new-list-of-vals declares)))

(defthm len-of-append-to-xarg-in-declares
  (equal (len (append-to-xarg-in-declares val xarg declares))
         1)
  :hints (("Goal" :in-theory (enable append-to-xarg-in-declares))))

;;test:
;; (append-to-xarg-in-declares '(("Goal" :in-theory (enable natp)))
;;                             :guard-hints
;;                             '((declare (xargs :guard (natp x) :guard-hints (("subgoal 1" :in-theory (enable posp)))))
;;                               (declare (xargs :guard-hints (("subgoal 2" :in-theory (enable len)))))))

;; TODO: Inline and drop
(defun replace-mode-with-program-in-declares (declares)
  (declare (xargs :guard (and (all-declarep declares)
                              (true-listp declares))))
  (replace-xarg-in-declares :mode :program declares))

;; TODO: Inline and drop
(defun replace-termination-hints-in-declares (declares new-termination-hints)
  (declare (xargs :guard (and (all-declarep declares)
                              (true-listp declares))))
  (replace-xarg-in-declares :hints new-termination-hints declares))

;; This was wrong before (gave two copies of :program:
;; (replace-mode-with-program-in-declares '((declare (xargs :guard t) (xargs :guard (natp x)))))
