; The main (old-style) Axe evaluator
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

;; See evaluator-basic.lisp for a newer evaluator which may often be more useful.

(include-book "evaluator-support")
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))

;; TODO: This introduces a skip-proofs for termination
;think this stuff through
(make-evaluator axe-evaluator
                (axe-evaluator-function-info)
;                 :error    ;throw an error if we are given an unknown function
;                nil       ;don't quote result
                )

(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(local (in-theory (disable aset1 aref1 array1p alen1 dimensions symbol-alistp)))

;;(skip-proofs (make-flag apply-axe-evaluator))

;; (defthm-flag-apply-axe-evaluator
;;   ;; (defthm theorem-for-apply-axe-evaluator
;;   ;;   (implies (and (or (symbolp fn) (pseudo-lambdap fn))
;;   ;;                 (true-listp args)
;;   ;;                 (interpreted-function-alistp interpreted-function-alist)
;;   ;;                 (natp array-depth))
;;   ;;            (prop (apply-axe-evaluator fn args interpreted-function-alist
;;   ;;                                       array-depth)))
;;   ;;   :flag apply-axe-evaluator)
;;   ;; (defthm theorem-for-eval-axe-evaluator
;;   ;;   (implies (and (symbol-alistp alist)
;;   ;;                 (pseudo-termp form)
;;   ;;                 (interpreted-function-alistp interpreted-function-alist)
;;   ;;                 (natp array-depth))
;;   ;;            (prop (eval-axe-evaluator alist form interpreted-function-alist
;;   ;;                                      array-depth)))
;;   ;;   :flag eval-axe-evaluator)
;;   (defthm theorem-for-eval-list-axe-evaluator
;;     (implies (and (symbol-alistp alist)
;;                   (pseudo-term-listp form-lst)
;;                   (interpreted-function-alistp interpreted-function-alist)
;;                   (natp array-depth))
;;              (true-listp (eval-list-axe-evaluator alist
;;                                             form-lst interpreted-function-alist
;;                                             array-depth)))
;;     :flag eval-list-axe-evaluator)
;;   ;; (defthm theorem-for-dag-val-with-axe-evaluator
;;   ;;   (implies (and (or (quotep dag)
;;   ;;                     (and (pseudo-dagp dag)
;;   ;;                          (< (len dag) 1152921504606846974)))
;;   ;;                 (symbol-alistp alist)
;;   ;;                 (interpreted-function-alistp interpreted-function-alist)
;;   ;;                 (natp array-depth))
;;   ;;            (prop (dag-val-with-axe-evaluator dag alist interpreted-function-alist
;;   ;;                                              array-depth)))
;;   ;;   :flag dag-val-with-axe-evaluator)
;;   (defthm theorem-for-eval-dag-with-axe-evaluator
;;     (implies (and (nat-listp nodenum-worklist)
;;                   (or (not (consp nodenum-worklist))
;;                       (pseudo-dag-arrayp dag-array-name dag-array
;;                                          (+ 1 (maxelem nodenum-worklist))))
;;                   (symbol-alistp var-value-alist)
;;                   (symbolp eval-array-name)
;;                   (or (not (consp nodenum-worklist))
;;                       (eval-arrayp eval-array-name eval-array
;;                                    (+ 1 (maxelem nodenum-worklist))))
;;                   (interpreted-function-alistp interpreted-function-alist)
;;                   (natp array-depth))
;;              (eval-arrayp dag-array-name
;;                           (eval-dag-with-axe-evaluator nodenum-worklist
;;                                                        dag-array-name dag-array
;;                                                        var-value-alist eval-array-name
;;                                                        eval-array interpreted-function-alist
;;                                                        array-depth)
;;                           (+ 1 (maxelem nodenum-worklist))))
;;     :flag eval-dag-with-axe-evaluator)
;;   :skip-others t
;;   :hints (("Goal" :in-theory (enable eval-dag-with-axe-evaluator))))

;move
(defthm maxelem-of-cdr-linear-alt
  (implies (consp (cdr lst))
           (<= (maxelem (cdr lst)) (maxelem lst)))
  :rule-classes ((:linear :trigger-terms ((maxelem (cdr lst)))))
  :hints (("Goal" :in-theory (enable maxelem))))

(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
;ffffixme could lead to crashes?
; could use the trick of calling eval-in-logic more
; need return-type theorem for the clique first (see above)
(skip-proofs
(verify-guards apply-axe-evaluator
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (true-list-fix
                                   true-listp-of-cadr-of-assoc-equal-when-interpreted-function-alistp
                                   symbol-listp-of-cadr-of-assoc-equal-when-interpreted-function-alistp
                                   pseudo-termp-of-caddr-of-assoc-equal-when-interpreted-function-alistp
                                   true-listp-of-cdr-of-assoc-equal-when-interpreted-function-alistp
                                   consp-of-cddr-of-assoc-equal-when-interpreted-function-alistp
                                   true-listp-of-assoc-equal-when-interpreted-function-alistp)
                                  (interpreted-function-alistp ;todo
                                   natp
                                   ))
           :do-not '(generalize eliminate-destructors)
           :do-not-induct t)))
)

;fffixme could lead to crashes?
(skip-proofs (verify-guards apply-axe-evaluator-to-quoted-args))

(make-event (add-tracing-to-evaluator 'axe-evaluator))

;fffixme could lead to crashes?
(skip-proofs (verify-guards apply-axe-evaluator-with-tracing))

;; ;;BBOZO, yikes i think the guards might sometimes fail to be satisfied, since we sometimes evaluate both branches of an if...
;; ;so the skip-proofs can lead to bad things...

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; ;hiding the bvplus should cause it to get sucked into the dag
;; (defthm hide-bvplus-constant-dag
;;   (implies (and (syntaxp (and (quotep k)
;;                               (quotep size)))
;;                 )
;;            (equal (BVPLUS size k (hide (DAG-VAL2-no-array dag alist)))
;;                   (hide (BVPLUS size k (hide (DAG-VAL2-NO-ARRAY dag alist))))))
;;   :hints (("Goal" :expand ((hide (BVPLUS size k (hide (DAG-VAL2-NO-ARRAY dag alist))))))))

;; ;hiding the bvplus should cause it to get sucked into the dag
;; (defthm hide-bvplus-dag-dag
;;   (implies (syntaxp (quotep size))
;;            (equal (BVPLUS size
;;                           (hide (DAG-VAL2-NO-ARRAY dag alist))
;;                           (hide (DAG-VAL2-NO-ARRAY dag2 alist2)))
;;                   (hide (BVPLUS size
;;                                 (hide (DAG-VAL2-NO-ARRAY dag alist))
;;                                 (hide (DAG-VAL2-NO-ARRAY dag2 alist2))))))
;;   :hints (("Goal" :expand ((hide (BVPLUS size
;;                                 (hide (DAG-VAL2-NO-ARRAY dag alist))
;;                                 (hide (DAG-VAL2-NO-ARRAY dag2 alist2))))))))

;; ;BOZO lots more like this!
;; (defthm integerp-hide-dag-val-bvplus
;;   (implies (equal (second (car dag)) 'bvplus)
;;            (integerp (hide (dag-val2-no-array dag alist))))
;;   :hints (("Goal" :in-theory (enable eval-fn eval-fn-ternary dag-val2-no-array
;;                                      )
;;            :expand ((hide (dag-val2-no-array dag alist))
;;                     (eval-dag2-no-array dag alist)))))

;; (local
;;  (defthm equal-of-true-list-fix-and-list-of-car
;;    (equal (equal (true-list-fix l)
;;                  (list (car l)))
;;           (equal 1 (len l)))
;;    :hints (("Goal" :in-theory (enable true-list-fix)))))

;(in-theory (disable LIST::LEN-EQUAL-1-REWRITE)) ;yuck

;; (local
;;  (defthm consp-of-lookup-equal-when-items-have-len-of-strip-cdrs
;;    (implies (and (items-have-len n (strip-cdrs l))
;;                  (lookup-equal key l)
;;                  (posp n))
;;             (consp (lookup-equal key l)))
;;    :hints (("Goal" :in-theory (enable lookup-equal
;;                                       ITEMS-HAVE-LEN
;;                                       assoc-equal)))))

;todo: generalize this (it has *axe-evaluator-functions* baked in)
;include the fns themselves if they are not base fns
;fixme do we need the ones called in nested dag-val calls?
;todo: compare to get-non-built-in-supporting-fns-list
(defund supporting-non-base-fns (count fns interpreted-function-alist throw-errorp acc)
  (declare (xargs :guard (and (symbol-listp fns)
                              (symbol-listp acc)
                              (interpreted-function-alistp interpreted-function-alist))
                  :measure (nfix (+ 1 count))
                  :guard-hints (("Goal" :in-theory (e/d (lookup-equal interpreted-function-alistp)
                                                        (interpreted-function-infop-of-lookup-equal-when-interpreted-function-alistp
                                                         member-equal ; for speed
                                                         ))
                                 :use (:instance interpreted-function-infop-of-lookup-equal-when-interpreted-function-alistp (fn (car fns)))
                                 ))))
  (if (not (natp count))
      (er hard? 'supporting-non-base-fns "count reached.")
    (if (endp fns)
        acc
      (let* ((fn (first fns)))
        (if (or (member-eq fn acc)
                (eq 'dag-val-with-axe-evaluator fn) ;what about eval-dag-with-axe-evaluator?
                (member-eq fn *axe-evaluator-functions*))
            (supporting-non-base-fns (+ -1 count) (cdr fns) interpreted-function-alist throw-errorp acc)
          (let* ((entry (if throw-errorp
                            (lookup-eq-safe fn interpreted-function-alist)
                          (lookup-eq fn interpreted-function-alist))))
            (if (not entry) ;fixme print a warning -or get rid of this case and always throw the error (once the decompiler passed in ifns for all jvm functions)
                (supporting-non-base-fns (+ -1 count)
                                         (cdr fns)
                                         interpreted-function-alist
                                         throw-errorp
                                         acc ;(cons fn acc)
                                         )
              (let* ((body (second entry))
                     (called-fns (get-fns-in-term body)))
                (supporting-non-base-fns (+ -1 count)
                                         (append called-fns (cdr fns))
                                         interpreted-function-alist
                                         throw-errorp
                                         (cons fn acc))))))))))

;fixme can we omit ones mentioned only in nested calls to dag-val (since they will be given values in those calls)?
(defund supporting-interpreted-function-alist (fns interpreted-function-alist throw-errorp)
  (let ((supporting-non-base-fns (supporting-non-base-fns 1000000000 fns interpreted-function-alist throw-errorp nil)))
    (get-entries-eq supporting-non-base-fns interpreted-function-alist)))

;todo: use this more?
;; interpreted-function-alist must give meaning to all non-built-in functions in DAG.
(defund wrap-dag-in-dag-val (dag interpreted-function-alist)
  (if (quotep dag)
      dag
    (let* ((dag-vars (dag-vars-unsorted dag))
           (dag-fns (dag-fns dag)))
      `(dag-val-with-axe-evaluator ',dag
                                   ,(make-acons-nest dag-vars)
                                   ',(supporting-interpreted-function-alist dag-fns interpreted-function-alist
                                                                            nil ;fixme change this to t, or change the code to always throw an error
                                                                            )
                                   '0))))

;; Create a term equivalent to DAG, where the meaning of any non-built-in
;; functions that support DAG comes from WRLD.
;todo: use this more?
(defund embed-dag-in-term (dag wrld)
  (declare (xargs :guard (and (or (quotep dag)
                                  (weak-dagp dag))
                              (plist-worldp wrld))))
  (if (quotep dag)
      dag
    (let ((dag-vars (dag-vars-unsorted dag))
          (dag-fns (dag-fns dag)))
      (if (not (function-symbolsp dag-fns wrld))
          (er hard? 'embed-dag-in-term "Some functions are not in the world: ~X01." dag-fns nil)
        (let* ((supporting-fns (get-non-built-in-supporting-fns-list dag-fns
                                                                     *axe-evaluator-functions* ;(append *acl2-primitives* *axe-evaluator-functions*) ;stops when it hits one of these..
                                                                     wrld))
               (supporting-interpreted-function-alist (make-interpreted-function-alist supporting-fns wrld)))
          `(dag-val-with-axe-evaluator ',dag
                                       ,(make-acons-nest dag-vars)
                                       ',supporting-interpreted-function-alist
                                       '0))))))
