; DAG builders that depend on the evaluator
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/alists-light/lookup-eq-lst" :dir :system)
(include-book "dag-array-builders2")
(include-book "evaluator") ; brings in skip-proofs (try the basic evaluator?)
(include-book "renaming-array")
(include-book "supporting-nodes")
(include-book "axe-trees")
(include-book "def-dag-builder-theorems")
(include-book "make-dag-indices")
(include-book "consecutivep2")
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp2" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars2" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system)) ;why does this break a proof below?
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))

(in-theory (disable bounded-dag-exprp)) ;move?

(local (in-theory (disable member-equal
                           subsetp-equal
                           ;; axe-treep
                           all-axe-treep
                           )))

;dup
(local
 (defthm maxelem-bound
  (implies (and (all-natp x)
                (consp x))
           (<= 0 (maxelem x)))))

;dup
(local
 (defthm integerp-of-maxelem2
  (implies (and (all-natp x) ;relax?
                (consp x))
           (integerp (maxelem x)))))

;;move
(defthmd <-of-car-of-car-when-all-<-of-strip-cars
  (implies (and (all-< (strip-cars x) bound)
                (consp x))
           (< (car (car x)) bound))
  :hints (("Goal" :in-theory (enable strip-cars))))

(local (in-theory (enable <-of-car-of-car-when-all-<-of-strip-cars
                          revappend-lemma)))

(in-theory (disable strip-cdrs
                    ;strip-cars todo
                    ;;revappend-removal ;todo
                    ;; for speed:
                    use-all-consp-for-car
                    all-consp-when-not-consp
                    set-difference-equal))

(local (in-theory (enable strip-cars))) ;why?

(defthm all-<-of-strip-cars-of-cdr
  (implies (all-< (strip-cars alist) bound)
           (all-< (strip-cars (cdr alist)) bound))
  :hints (("Goal" :in-theory (enable strip-cars))))

(defthm alistp-of-set-difference-equal
  (implies (alistp x)
           (alistp (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(local
 (defthmd consp-when-true-listp-iff
   (implies (true-listp x)
            (iff (consp x)
                 x))))

;move or drop
(defthm <-self
  (equal (< x x)
         nil))

;move to len.lisp?  or just include it?
(defthm cdr-when-equal-of-len-and-1-cheap
  (implies (and (equal (len x) 1)
                (true-listp x))
           (equal (cdr x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(local (in-theory (enable consp-of-cdr
                          bounded-renaming-entriesp-of-aset1-special-gen
                          <-of-lookup-equal-when-all-dargp-less-than-of-strip-cdrs)))

(local (in-theory (disable consp-from-len-cheap
                           all-axe-treep-when-pseudo-term-listp
                           ;;list::nth-with-large-index-2
                           ;cdr-non-nil
                           ;nth1-when-not-cdr
                           ;list::nth-with-large-index
                           all-dargp-less-than-when-<-of-largest-non-quotep
                           dargp-less-than
                           dargp
                           default-cdr
                           default-car
                           ;weak-dagp-aux ;todo uncomment, but that breaks some proofs
                           symbol-alistp ;prevent induction
                           nat-listp ;for speed
                           pseudo-dag-arrayp
                           true-listp-of-nth-1-of-nth-0-when-axe-treep)))

;; Merge the DAG nodes in rev-dag-lst into the DAG-ARRAY, applying any substitution indicated by variable-replacement-alist to nodes that are vars.
;; Returns (mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; When this is used to merge in an embedded dag, variable-replacement-alist must be used to replace the vars. - fixme generalize to something like rebuild-nodes?
;;does not deal with lambdas or (inlinable?) calls to the evaluator, because those should not appear in dags
;;what about (evaluatable) ground terms?  maybe those should not appear either?
;; This is very similar to merge-nodes-into-dag-array in dagify.lisp, except this one also substitutes for vars (and passes array names, and uses a different name for the renaming-array).
;todo: compare to merge-nodes-into-dag-array.  This one does take a variable-replacement-alist.
(defund merge-embedded-dag-into-dag-array (rev-dag-lst
                                           variable-replacement-alist ;maps vars in rev-dag-lst to a quotep or nodenum in dag-array (need not map all the vars)
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                           renaming-array ;maps each already-processed nodenum from rev-dag-lst to a quotep or nodenum in dag-array (can a quotep ever happen?)
                                           interpreted-function-alist ;irrelevant!
                                           )
  (declare (xargs :guard (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              (alistp variable-replacement-alist)
                              (all-dargp-less-than (strip-cdrs variable-replacement-alist) dag-len)
                              (weak-dagp-aux rev-dag-lst)
                              ;; have to know that the rev-dag-lst nodenums increase:
                              (if (consp rev-dag-lst)
                                  (and (renaming-arrayp 'renaming-array-FOR-MERGE-EMBEDDED-DAG-INTO-DAG-ARRAY renaming-array (car (car rev-dag-lst)))
                                       (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array-FOR-MERGE-EMBEDDED-DAG-INTO-DAG-ARRAY renaming-array) ;orig-len
                                              )
                                       (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array-FOR-MERGE-EMBEDDED-DAG-INTO-DAG-ARRAY renaming-array dag-len)
                                       )
                                t)
                              (consecutivep (strip-cars rev-dag-lst)))
                  :guard-hints (("Goal" :do-not '(generalize eliminate-destructors)
                                 :expand ((STRIP-CARS REV-DAG-LST)
                                          (WEAK-DAGP-AUX REV-DAG-LST))
                                 :in-theory (e/d (<-of-lookup-equal-when-all-dargp-less-than-of-strip-cdrs
                                                  car-of-cadr-when-consecutivep-of-strip-cars
                                                  dargp-when-natp
                                                  dargp-when-myquotep
                                                  )
                                                 (dargp
                                                  ;;arith-rule
                                                  PSEUDO-DAG-ARRAYP))))))
  (declare (irrelevant interpreted-function-alist))
  (if (endp rev-dag-lst)
      (mv (erp-nil) renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (let* ((entry (first rev-dag-lst))
           (nodenum (car entry))
           (expr (cdr entry)))
      (if (variablep expr) ;variable, so check whether the variable-replacement-alist maps it to something
          (let ((new-nodenum-or-quotep (lookup-eq expr variable-replacement-alist)))
            (if new-nodenum-or-quotep
                ;; a substitution is being applied to this var
                (merge-embedded-dag-into-dag-array (rest rev-dag-lst)
                                                   variable-replacement-alist
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                   (aset1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array nodenum new-nodenum-or-quotep)
                                                   interpreted-function-alist)
              ;; no substitution is being applied to this var:
              (mv-let (erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                (add-variable-to-dag-array-with-name expr dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
                (if erp
                    (mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                  (merge-embedded-dag-into-dag-array (rest rev-dag-lst)
                                                     variable-replacement-alist
                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                     (aset1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array nodenum new-nodenum)
                                                     interpreted-function-alist)))))
        (let ((fn (ffn-symb expr)))
          (if (eq 'quote fn)
              ;; quoted constant:
              (merge-embedded-dag-into-dag-array (rest rev-dag-lst) variable-replacement-alist
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                 (aset1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array nodenum expr)
                                                 interpreted-function-alist)
            ;;fixme what about ground terms?!
            (let* ((args (dargs expr))
                   (renamed-args (rename-args args 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array)
                                 ))
              (mv-let (erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                (add-function-call-expr-to-dag-array-with-name fn renamed-args
                                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
                (if erp
                    (mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                  (merge-embedded-dag-into-dag-array (rest rev-dag-lst)
                                                     variable-replacement-alist
                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                     (aset1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array nodenum new-nodenum)
                                                     interpreted-function-alist))))))))))


(defthmd caadr-when-consecutivep-of-strip-cars
  (implies (and (consecutivep (strip-cars x))
                (< 1 (len x)))
           (equal (car (car (cdr x)))
                  (+ 1 (car (car x))))))
;(local (in-theory (enable caadr-when-consecutivep-of-strip-cars)))

;(local (in-theory (enable strip-cars))) ;todo

(local (in-theory (disable MYQUOTEP)))

(def-dag-builder-theorems
  (merge-embedded-dag-into-dag-array rev-dag-lst
                                     variable-replacement-alist
                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                     renaming-array
                                     interpreted-function-alist
                                     )
  (mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((alistp variable-replacement-alist)
         (all-dargp-less-than (strip-cdrs variable-replacement-alist) dag-len)
         (weak-dagp-aux rev-dag-lst)
         (all-< (strip-cars rev-dag-lst)
                (alen1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array))
         (if (consp rev-dag-lst)
             (and (renaming-arrayp 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array (car (car rev-dag-lst)))
                  (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array dag-len))
           t)
         (consecutivep (strip-cars rev-dag-lst)))
  :dag-parent-array-name dag-parent-array-name
  :dag-array-name dag-array-name)

(defthm renaming-arrayp-of-mv-nth-1-of-merge-embedded-dag-into-dag-array
  (implies (and (consp rev-dag-lst) ;or else the call of last in the conclusion is a problem
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (alistp variable-replacement-alist)
                (all-dargp-less-than (strip-cdrs variable-replacement-alist) dag-len)
                (weak-dagp-aux rev-dag-lst)
                (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array) ;orig-len
                       )
                (renaming-arrayp 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array (car (car rev-dag-lst)))
                (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array dag-len)

                (consecutivep (strip-cars rev-dag-lst))
                (not (mv-nth 0 (merge-embedded-dag-into-dag-array rev-dag-lst
                                                                  variable-replacement-alist
                                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                  renaming-array
                                                                  interpreted-function-alist)))
                (natp num)
                (<= num (+ 1 (car (car (last rev-dag-lst)))))
                ;;(<= n (car (car (last rev-dag-lst))))
                )
           (renaming-arrayp 'renaming-array-for-merge-embedded-dag-into-dag-array
                            (mv-nth 1 (merge-embedded-dag-into-dag-array rev-dag-lst variable-replacement-alist
                                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                         renaming-array interpreted-function-alist))
                            num))
  :hints (("subgoal *1/7" :cases ((equal num (+ 1 (car (car rev-dag-lst))))))
          ("subgoal *1/5" :cases ((equal num (+ 1 (car (car rev-dag-lst))))))
          ("subgoal *1/4" :cases ((equal num (+ 1 (car (car rev-dag-lst))))))
          ("subgoal *1/2" :cases ((equal num (+ 1 (car (car rev-dag-lst))))))
          ("Goal" :induct t
           :in-theory (enable merge-embedded-dag-into-dag-array))))

(defthm bounded-renaming-entriesp-after-merge-embedded-dag-into-dag-array
  (implies (and (consp rev-dag-lst) ;or else the call of last in the conclusion is a problem
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (alistp variable-replacement-alist)
                (all-dargp-less-than (strip-cdrs variable-replacement-alist) dag-len)
                (weak-dagp-aux rev-dag-lst)
                (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array) ;orig-len
                       )
                (renaming-arrayp 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array (car (car rev-dag-lst)))
                (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array dag-len)
                (consecutivep (strip-cars rev-dag-lst))
                (not (mv-nth 0 (merge-embedded-dag-into-dag-array rev-dag-lst
                                                                  variable-replacement-alist
                                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                  renaming-array
                                                                  interpreted-function-alist
                                                                  )))
                (<= n (car (car (last rev-dag-lst))))
                (natp n)
                )
           (bounded-renaming-entriesp n
                                      'renaming-array-for-merge-embedded-dag-into-dag-array
                                      (mv-nth 1 (merge-embedded-dag-into-dag-array rev-dag-lst variable-replacement-alist
                                                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                                   renaming-array interpreted-function-alist))
                                      (mv-nth 3 (merge-embedded-dag-into-dag-array rev-dag-lst variable-replacement-alist
                                                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                                   renaming-array interpreted-function-alist))))
  :hints (("subgoal *1/7" :cases ((equal n (car (car rev-dag-lst)))))
          ("subgoal *1/5" :cases ((equal n (car (car rev-dag-lst)))))
          ("subgoal *1/4" :cases ((equal n (car (car rev-dag-lst)))))
          ("subgoal *1/2" :cases ((equal n (car (car rev-dag-lst)))))
          ("Goal" :induct t
           :in-theory (enable merge-embedded-dag-into-dag-array))))

;todo: rename
(defthm alen1-of-mv-nth-1-of-merge-embedded-dag-into-dag-array
  (implies (and (consp rev-dag-lst) ;or else the call of last in the conclusion is a problem
                (alistp variable-replacement-alist)
                (all-dargp-less-than (strip-cdrs variable-replacement-alist) dag-len)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (weak-dagp-aux rev-dag-lst)
                (bounded-dag-parent-arrayp dag-parent-array-name dag-parent-array dag-len)
                (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array) ;orig-len
                       )
                (renaming-arrayp 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array (car (car rev-dag-lst)))
                (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array dag-len)
                (consecutivep (strip-cars rev-dag-lst))
                (not (mv-nth 0 (merge-embedded-dag-into-dag-array rev-dag-lst
                                                                  variable-replacement-alist
                                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                  renaming-array
                                                                  interpreted-function-alist
                                                                  ))))
           (and (array1p 'renaming-array-for-merge-embedded-dag-into-dag-array
                         (mv-nth 1 (merge-embedded-dag-into-dag-array rev-dag-lst variable-replacement-alist
                                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                         renaming-array interpreted-function-alist)))
                (equal (alen1 'renaming-array-for-merge-embedded-dag-into-dag-array
                              (mv-nth 1 (merge-embedded-dag-into-dag-array rev-dag-lst variable-replacement-alist
                                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                           renaming-array interpreted-function-alist)))
                       (alen1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array))))
  :hints (("subgoal *1/7" :cases ((equal n (car (car rev-dag-lst)))))
          ("subgoal *1/5" :cases ((equal n (car (car rev-dag-lst)))))
          ("subgoal *1/4" :cases ((equal n (car (car rev-dag-lst)))))
          ("subgoal *1/2" :cases ((equal n (car (car rev-dag-lst)))))
          ("Goal" :induct t
           :in-theory (enable merge-embedded-dag-into-dag-array))))

(defthm dag-parent-arrayp-of-mv-nth-4-of-merge-embedded-dag-into-dag-array
  (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
;                (<= dag-len 2147483645)
                (not (mv-nth 0 (merge-embedded-dag-into-dag-array rev-dag-lst
                                                                  variable-replacement-alist
                                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                  renaming-array
                                                                  interpreted-function-alist)))
                ;; (<= (+ (len rev-dag-lst)
                ;;        dag-len)
                ;;     2147483645)
                (if (consp rev-dag-lst)
                    (and (renaming-arrayp 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array (car (car rev-dag-lst)))
                         (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array dag-len))
                  t)
                (weak-dagp-aux rev-dag-lst)
                (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array) ;orig-len
                       )
                (consecutivep (strip-cars rev-dag-lst))
                (alistp variable-replacement-alist)
                (all-dargp-less-than (strip-cdrs variable-replacement-alist) dag-len))
           (dag-parent-arrayp dag-parent-array-name (mv-nth
                                                     4
                                                     (merge-embedded-dag-into-dag-array rev-dag-lst
                                                                                        variable-replacement-alist
                                                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                                        renaming-array
                                                                                        interpreted-function-alist))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-embedded-dag-into-dag-array
                            bounded-renaming-entriesp-of-aset1-special-gen
                            <-of-lookup-equal-when-all-dargp-less-than-of-strip-cdrs)
                           (pseudo-dag-arrayp
                            ;;bounded-dag-parent-arrayp
                            dargp)))))

(defthm alen1-of-mv-nth-4-of-merge-embedded-dag-into-dag-array
  (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (if (consp rev-dag-lst)
                    (and (renaming-arrayp 'renaming-array-FOR-MERGE-EMBEDDED-DAG-INTO-DAG-ARRAY renaming-array (car (car rev-dag-lst)))
                         (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array-FOR-MERGE-EMBEDDED-DAG-INTO-DAG-ARRAY renaming-array dag-len))
                  t)
                (weak-dagp-aux rev-dag-lst)
                (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array-FOR-MERGE-EMBEDDED-DAG-INTO-DAG-ARRAY renaming-array) ;orig-len
                       )
                (consecutivep (strip-cars rev-dag-lst))
                (alistp variable-replacement-alist)
                (all-dargp-less-than (strip-cdrs variable-replacement-alist) dag-len)
                (not (mv-nth 0 (merge-embedded-dag-into-dag-array rev-dag-lst
                                                                  variable-replacement-alist
                                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                  renaming-array
                                                                  interpreted-function-alist))))
           (equal (alen1 dag-parent-array-name (mv-nth
                                                     4
                                                     (merge-embedded-dag-into-dag-array rev-dag-lst
                                                                                        variable-replacement-alist
                                                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                                        renaming-array
                                                                                        interpreted-function-alist)))
                  (alen1 dag-array-name (mv-nth
                                              2
                                              (merge-embedded-dag-into-dag-array rev-dag-lst
                                                                                 variable-replacement-alist
                                                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                                 renaming-array
                                                                                 interpreted-function-alist)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-embedded-dag-into-dag-array
                            bounded-renaming-entriesp-of-aset1-special-gen
                            <-of-lookup-equal-when-all-dargp-less-than-of-strip-cdrs)
                           (pseudo-dag-arrayp
                            dargp)))))

(defthm dag-constant-alistp-of-mv-nth-5-of-merge-embedded-dag-into-dag-array
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len))
           (dag-constant-alistp (mv-nth
                                 5
                                 (merge-embedded-dag-into-dag-array rev-dag-lst
                                                                    variable-replacement-alist
                                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                    renaming-array
                                                                    interpreted-function-alist))))
  :hints (("Goal" :in-theory (enable merge-embedded-dag-into-dag-array))))

;; ;;should follow from wf-dagp.  should def-dag-builder-theorems generate this or not?
;; (defthm bounded-dag-constant-alistp-of-mv-nth-5-of-merge-embedded-dag-into-dag-array
;;   (implies (and (bounded-dag-constant-alistp dag-constant-alist dag-len)
;;                 (natp dag-len))
;;            (bounded-dag-constant-alistp (mv-nth
;;                                          5
;;                                          (merge-embedded-dag-into-dag-array rev-dag-lst
;;                                                                             variable-replacement-alist
;;                                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
;;                                                                             renaming-array
;;                                                                             interpreted-function-alist))
;;                                         (mv-nth
;;                                          3
;;                                          (merge-embedded-dag-into-dag-array rev-dag-lst
;;                                                                             variable-replacement-alist
;;                                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
;;                                                                             renaming-array
;;                                                                             interpreted-function-alist))))
;;   :hints (("Goal" :in-theory (enable merge-embedded-dag-into-dag-array))))

(defthm dag-variable-alistp-of-mv-nth-6-of-merge-embedded-dag-into-dag-array
  (implies (and (dag-variable-alistp dag-variable-alist)
                (weak-dagp-aux rev-dag-lst)
                (natp dag-len))
           (dag-variable-alistp (mv-nth
                                 6
                                 (merge-embedded-dag-into-dag-array rev-dag-lst
                                                                    variable-replacement-alist
                                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                    renaming-array
                                                                    interpreted-function-alist))))
  :hints (("Goal" :in-theory (enable merge-embedded-dag-into-dag-array))))

;; todo: get rid of some of the theorems just above? -- but they may have fewer hyps that those generated by the macro

;acc maps vars to nodenums in dag-array
;; Returns (mv erp result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist), where RESULT maps vars to their nodes.
(defund make-nodes-for-vars-with-name (vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name)
  (declare (xargs :guard (and (symbol-listp vars)
                              (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              (dargp-less-than alist-nodenum dag-len))))
  (if (endp vars)
      (mv (erp-nil) acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (let* ((var (car vars)))
      (mv-let (erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (add-function-call-expr-to-dag-array-with-name 'lookup-eq `(',var ,alist-nodenum) ;use lookup-equal? ;simplify using lookup-equal and acons?
                                                             dag-array dag-len dag-parent-array
                                                             dag-constant-alist dag-variable-alist
                                                             dag-array-name dag-parent-array-name)
        (if erp
            (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          (make-nodes-for-vars-with-name (cdr vars)
                                         alist-nodenum
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         (acons-fast var nodenum acc)
                                         dag-array-name dag-parent-array-name))))))

(def-dag-builder-theorems
  (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name)
  (mv erp result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((alistp variable-replacement-alist)
         (symbol-listp vars)
         (and (natp alist-nodenum)
              (< alist-nodenum dag-len)))
  :dag-parent-array-name dag-parent-array-name
  :dag-array-name dag-array-name)

(defthm <-of-mv-nth-3-of-make-nodes-for-vars-with-name
  (implies (and (<= bound dag-len)
                (natp dag-len)
                )
           (<= bound (mv-nth 3 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable make-nodes-for-vars-with-name))))

(defthm alistp-of-mv-nth-1-of-make-nodes-for-vars-with-name
  (implies (alistp acc)
           (alistp (mv-nth 1 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable make-nodes-for-vars-with-name))))

(defthm all-dargp-less-than-of-strip-cdrs-of-mv-nth-1-of-make-nodes-for-vars-with-name
  (implies (and (all-dargp-less-than (strip-cdrs acc) dag-len)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (natp alist-nodenum)
                (< alist-nodenum dag-len)
                (not (mv-nth 0 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))))
           (all-dargp-less-than (strip-cdrs (mv-nth 1 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name)))
                                           (mv-nth 3 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))
                                           ))
  :hints (("Goal" :in-theory (enable make-nodes-for-vars-with-name))))

;; (defthm bounded-dag-parent-arrayp-of-mv-nth-4-of-make-nodes-for-vars-with-name
;;   (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
;;                 (dargp-less-than alist-nodenum dag-len))
;;            (bounded-dag-parent-arrayp dag-parent-array-name
;;                                (mv-nth 4 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))
;;                                (mv-nth 3 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))
;;                                ))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (make-nodes-for-vars-with-name)
;;                            (pseudo-dag-arrayp)))))

(defthm dag-constant-alistp-of-mv-nth-5-of-make-nodes-for-vars-with-name
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len))
           (dag-constant-alistp (mv-nth 5 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable make-nodes-for-vars-with-name))))

;; (defthm all-<-strip-cdrs-of-mv-nth-5-of-make-nodes-for-vars-with-name
;;   (implies (and (bounded-dag-constant-alistp dag-constant-alist dag-len)
;;                 (natp dag-len)
;;                 (all-< (strip-cdrs dag-constant-alist) dag-len))
;;            (all-< (strip-cdrs (mv-nth 5 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name)))
;;                   (mv-nth 3 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))))
;;   :hints (("Goal" :in-theory (enable make-nodes-for-vars-with-name))))

(defthm bounded-dag-constant-alistp-of-mv-nth-5-of-make-nodes-for-vars-with-name
  (implies (and (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (natp dag-len))
           (bounded-dag-constant-alistp (mv-nth 5 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))
                                       (mv-nth 3 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable make-nodes-for-vars-with-name))))

(defthm dag-variable-alistp-of-mv-nth-6-of-make-nodes-for-vars-with-name
  (implies (and (dag-variable-alistp dag-variable-alist)
                ;; (natp dag-len)
                )
           (dag-variable-alistp (mv-nth 6 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable make-nodes-for-vars-with-name))))

;; (defthm all-<-strip-cdrs-of-mv-nth-6-of-make-nodes-for-vars-with-name
;;   (implies (and (dag-variable-alistp dag-variable-alist)
;;                 (natp dag-len)
;;                 (ALL-< (STRIP-CDRS DAG-variable-ALIST) DAG-LEN))
;;            (all-< (strip-cdrs (mv-nth 6 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name)))
;;                   (mv-nth 3 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))))
;;   :hints (("Goal" :in-theory (enable make-nodes-for-vars-with-name))))

(defthm bounded-dag-variable-alistp-of-mv-nth-6-of-make-nodes-for-vars-with-name
  (implies (and (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (natp dag-len))
           (bounded-dag-variable-alistp (mv-nth 6 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))
                                        (mv-nth 3 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable make-nodes-for-vars-with-name))))

(defthm pseudo-dag-arrayp-after-make-nodes-for-vars-with-name
  (implies (and (all-dargp-less-than (strip-cdrs acc) dag-len)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (natp alist-nodenum)
                (< alist-nodenum dag-len)
                (not (mv-nth 0 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))))
           (pseudo-dag-arrayp dag-array-name
                              (mv-nth 2 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))
                              (mv-nth 3 (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc dag-array-name dag-parent-array-name))
                              ))
  :hints (("Goal" :in-theory (enable make-nodes-for-vars-with-name))))

;this inlines any dag found inside a call to the dag evaluator, but only if the interpreted-function-alist is a subset of the one passed in
;could consider returning an interpreted-function-alist for the created dag?
;fixme what if there are several levels of dags nested within terms, etc.? should work ok?  what about array name clashes? might be okay..
;could make a version of this that requires pseudo-termp, disallowing nodenums.
;todo: consider passing an alist to replace vars in the term, and then using that facility in the lambda case
;see also substitute-and-merge-term-into-dag-array in rewriter-new.lisp

(mutual-recursion
 ;;TREE is a tree over variables, nodenums in the dag, and quoteps
 ;;variable names are shared between TREE and DAG-ARRAY, except those changed by the var-replacement-alist
 ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
 ;; where nodenum-or-quotep is equivalent to the tree passed in, and nodes already in the dag passed in remain unchanged (and the aux. data structures have been updated, of course)
 ;; todo: when this is called on a term, we could instead call a simpler version that only works on terms
 (defund merge-tree-into-dag-array (tree
                                    var-replacement-alist ;maps vars in the term to nodenums/quoteps
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                    interpreted-function-alist)
   (declare (xargs :guard (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                               (axe-treep tree)
                               (bounded-axe-treep tree dag-len)
                               (symbol-alistp var-replacement-alist)
                               (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                               ;;(<= (+ (len vars) dag-len) 2147483645)
                               (interpreted-function-alistp interpreted-function-alist))
                   :verify-guards nil
                   ))
   (if (atom tree)
       (if (symbolp tree)
           (let ((match (assoc-eq tree var-replacement-alist)))
             (if match
                 (mv (erp-nil) (cdr match) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
               ;; tree is a variable:
               (add-variable-to-dag-array-with-name tree dag-array dag-len
                                                          dag-parent-array ;;just passed through (slow?)
                                                          dag-constant-alist ;;just passed through (slow?)
                                                          dag-variable-alist dag-array-name dag-parent-array-name)))
         ;; tree is a nodenum:
         (mv (erp-nil) tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
     (let ((fn (ffn-symb tree)))
       (if (eq 'quote fn)
           ;; tree is a quoted constant:
           (mv (erp-nil) tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
         ;; tree is a function call:
         (let* ((args (fargs tree)))
           ;;begin by adding the args to the dag:
           (mv-let
             (erp arg-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (merge-trees-into-dag-array args var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)
             (if erp
                 (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
               ;;check for the special case of a call to dag-val-with-axe-evaluator where we can inline the dag:
               ;;todo: maybe call call-of-dag-val-with-axe-evaluator-with-inlineable-dagp here?
               (let ((dag-val-with-inlineable-dagp
                      (and (eq 'dag-val-with-axe-evaluator fn)
                           (= 4 (len arg-nodenums-or-quoteps))
                           ;; it's of the form: (dag-val-with-axe-evaluator DAG ALIST INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
                           (if (consp (first arg-nodenums-or-quoteps)) ;the dag to inline -- could it ever be the nodenum of a quotep?
                               t
                             (prog2$ (cw "(WARNING found a call to dag-val-with-axe-evaluator, but the dag isn't a quoted constant.)~%") ;print more?
                                     nil))
                           (not (consp (second arg-nodenums-or-quoteps)))  ;todo: handle the case of a constant alist?
                           (pseudo-dagp (unquote (first arg-nodenums-or-quoteps)))
                           (<= (len (unquote (first arg-nodenums-or-quoteps))) 2147483646)
                           ;;the interpreted-function-alist for the embedded dag must be consistent with the one passed in: - or maybe the dag only includes built in fns?  what if its the nodenum of a quotep?
                           (consp (third arg-nodenums-or-quoteps)) ;must be quoted
                           (interpreted-function-alistp (unquote (third arg-nodenums-or-quoteps)))
                           (if (subsetp-equal (unquote (third arg-nodenums-or-quoteps))
                                              interpreted-function-alist)
                               t
                             (let ((difference (set-difference-equal (unquote (third arg-nodenums-or-quoteps)) interpreted-function-alist)))
                               (prog2$ (cw "(WARNING: merge-tree-into-dag-array found a call to dag-val-with-axe-evaluator, but the interpreted-function-alist isn't a subset of the one passed in.  Thus, we are not inlining.  Offending entries: ~x0.  Corresponding entries in alist: ~x1)~%"
                                           (strip-cars difference) ;(set-difference-eq (strip-cars (unquote (third arg-nodenums-or-quoteps))) (strip-cars interpreted-function-alist))
                                           (lookup-eq-lst (strip-cars difference) interpreted-function-alist)
                                           )
                                       nil))))))
                 (if dag-val-with-inlineable-dagp
                     ;;tree is a call of dag-val-with-axe-evaluator, and we can inline its embedded dag
                     (b* ((quoted-dag (first arg-nodenums-or-quoteps))
                          (dag (unquote quoted-dag))
                          (vars (dag-vars dag))
                          (alist (second arg-nodenums-or-quoteps))
                          ((mv erp variable-node-alist-for-dag dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                           (make-nodes-for-vars-with-name vars alist dag-array dag-len dag-parent-array
                                                          dag-constant-alist dag-variable-alist nil dag-array-name dag-parent-array-name))
                          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                          ((mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                           (merge-embedded-dag-into-dag-array (reverse dag)
                                                              variable-node-alist-for-dag
                                                              dag-array dag-len dag-parent-array
                                                              dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                              (make-empty-array 'renaming-array-for-merge-embedded-dag-into-dag-array (+ 1 (top-nodenum dag))) ; nil ;the translation-alist
                                                              interpreted-function-alist))
                          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                          )
                       ;;fixme are the aux data structures updated right?
                       (mv (erp-nil)
                           (aref1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array (top-nodenum dag)) ;(lookup (top-nodenum dag) translation-alist)
                           dag-array dag-len dag-parent-array
                           dag-constant-alist dag-variable-alist))
                   (if (consp fn) ;tests for ((lambda <formals> <body>) ...<actuals>...) ;move this case up?
                       (merge-tree-into-dag-array (lambda-body fn)
                                                  (pairlis$-fast (lambda-formals fn) arg-nodenums-or-quoteps) ;save this consing?
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                  interpreted-function-alist)
                     ;;normal function call:
                     ;;ffixme what about ground terms?
                     ;;maybe move the dag-val-with-inlineable-dagp case into add-function-call-expr-to-dag-array-with-name?
                     (add-function-call-expr-to-dag-array-with-name fn arg-nodenums-or-quoteps
                                                                          dag-array dag-len dag-parent-array
                                                                          dag-constant-alist dag-variable-alist
                                                                          dag-array-name dag-parent-array-name)))))))))))

 ;;TREES are trees with variables, nodenums (new!), and quoteps at the leaves
 ;;returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
 (defund merge-trees-into-dag-array (trees
                                     var-replacement-alist
                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                     interpreted-function-alist)
   (declare (xargs :guard (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                               (true-listp trees)
                               (all-axe-treep trees)
                               (all-bounded-axe-treep trees dag-len)
                               (symbol-alistp var-replacement-alist)
                               (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                               ;;(<= (+ (len vars) dag-len) 2147483645)
                               (interpreted-function-alistp interpreted-function-alist))))
   (if (endp trees)
       (mv (erp-nil) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
     (b* (((mv erp car-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           (merge-tree-into-dag-array (first trees) var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))
          ((when erp) (mv erp nil  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
          ((mv erp cdr-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           (merge-trees-into-dag-array (rest trees) var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))
          ((when erp) (mv erp nil  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
       (mv (erp-nil)
           (cons car-nodenum-or-quotep cdr-nodenums-or-quoteps)
           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))

(make-flag merge-tree-into-dag-array)

(defthm-flag-merge-tree-into-dag-array
  (defthm natp-of-mv-nth-3-of-merge-tree-into-dag-array
    (implies (natp dag-len)
             (natp (mv-nth 3 (merge-tree-into-dag-array
                              tree
                              var-replacement-alist
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                              interpreted-function-alist))))
    :rule-classes (:rewrite :type-prescription)
    :flag merge-tree-into-dag-array)
  (defthm natp-of-mv-nth-3-of-merge-trees-into-dag-array
    (implies (natp dag-len)
             (natp (mv-nth 3 (merge-trees-into-dag-array
                              trees
                              var-replacement-alist
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                              interpreted-function-alist))))
    :rule-classes (:rewrite :type-prescription)
    :flag merge-trees-into-dag-array)
  :hints (("Goal" :in-theory (e/d (merge-tree-into-dag-array
                                   merge-trees-into-dag-array) (natp)))))

(defthm-flag-merge-tree-into-dag-array
  (defthm true-listp-of-mv-nth-1-of-merge-tree-into-dag-array
    t ;not needed
    :rule-classes nil
    :flag merge-tree-into-dag-array)
  (defthm true-listp-of-mv-nth-1-of-merge-trees-into-dag-array
    (true-listp
     (mv-nth 1
             (merge-trees-into-dag-array trees
                                         var-replacement-alist
                                         dag-array dag-len dag-parent-array
                                         dag-constant-alist dag-variable-alist
                                         dag-array-name dag-parent-array-name
                                         interpreted-function-alist)))
    :flag merge-trees-into-dag-array)
  :hints (("Goal"
           :expand (merge-trees-into-dag-array trees var-replacement-alist
                                               dag-array dag-len dag-parent-array
                                               dag-constant-alist dag-variable-alist
                                               dag-array-name dag-parent-array-name
                                               interpreted-function-alist)
           :in-theory (enable (:i len) merge-trees-into-dag-array))))

(defthm-flag-merge-tree-into-dag-array
  (defthm len-of-mv-nth-1-of-merge-trees-into-dag-array-dummy ;this one is not actually needed
    t
    :rule-classes nil
    :flag merge-tree-into-dag-array)
  (defthm len-of-mv-nth-1-of-merge-trees-into-dag-array
    (implies (not (mv-nth 0 (merge-trees-into-dag-array trees var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
             (equal (len (mv-nth 1 (merge-trees-into-dag-array trees var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                    (len trees)))
    :flag merge-trees-into-dag-array)
  :hints (("Goal" :expand ((merge-trees-into-dag-array trees var-replacement-alist
                                                       dag-array dag-len dag-parent-array
                                                       dag-constant-alist dag-variable-alist
                                                       dag-array-name dag-parent-array-name
                                                       interpreted-function-alist))
           :in-theory (enable merge-trees-into-dag-array))))

(defthm-flag-merge-tree-into-dag-array
  (defthm <=-of-mv-nth-3-of-merge-tree-into-dag-array
    (implies (natp dag-len)
             (<= dag-len
                 (mv-nth 3 (merge-tree-into-dag-array
                            tree
                            var-replacement-alist
                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                            interpreted-function-alist))))
    :flag merge-tree-into-dag-array)
  (defthm <=-of-mv-nth-3-of-merge-trees-into-dag-array
    (implies (natp dag-len)
             (<= dag-len
                 (mv-nth 3 (merge-trees-into-dag-array
                            trees
                            var-replacement-alist
                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                            interpreted-function-alist))))
    :flag merge-trees-into-dag-array)
  :hints (("Goal" :in-theory (e/d (merge-tree-into-dag-array
                                   merge-trees-into-dag-array) (natp)))))

(defthm-flag-merge-tree-into-dag-array
  (defthm merge-tree-into-dag-array-return-type
    (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  ;; no error:
                  (not (mv-nth 0 (merge-tree-into-dag-array
                                  tree
                                  var-replacement-alist
                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                  interpreted-function-alist)))
                  (axe-treep tree)
                  (bounded-axe-treep tree dag-len)
                  (symbol-alistp var-replacement-alist)
                  (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
;                  (interpreted-function-alistp interpreted-function-alist)
                  )
             (and (dargp-less-than (mv-nth 1 (merge-tree-into-dag-array
                                                         tree
                                                         var-replacement-alist
                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                         interpreted-function-alist))
                                              (mv-nth 3 (merge-tree-into-dag-array
                                                         tree
                                                         var-replacement-alist
                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                         interpreted-function-alist)))
                  (wf-dagp dag-array-name
                           (mv-nth 2
                                   (merge-tree-into-dag-array tree
                                                              var-replacement-alist
                                                              dag-array dag-len dag-parent-array
                                                              dag-constant-alist dag-variable-alist
                                                              dag-array-name dag-parent-array-name
                                                              interpreted-function-alist))
                           (mv-nth 3
                                   (merge-tree-into-dag-array tree
                                                              var-replacement-alist
                                                              dag-array dag-len dag-parent-array
                                                              dag-constant-alist dag-variable-alist
                                                              dag-array-name dag-parent-array-name
                                                              interpreted-function-alist))
                           dag-parent-array-name
                           (mv-nth 4
                                   (merge-tree-into-dag-array tree
                                                              var-replacement-alist
                                                              dag-array dag-len dag-parent-array
                                                              dag-constant-alist dag-variable-alist
                                                              dag-array-name dag-parent-array-name
                                                              interpreted-function-alist))
                           (mv-nth 5 (merge-tree-into-dag-array
                                      tree
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           (mv-nth 6 (merge-tree-into-dag-array tree
                                                                var-replacement-alist
                                                                dag-array dag-len dag-parent-array
                                                                dag-constant-alist dag-variable-alist
                                                                dag-array-name dag-parent-array-name
                                                                interpreted-function-alist)))))
    :flag merge-tree-into-dag-array)
  (defthm merge-trees-into-dag-array-return-type
    (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  ;; no error:
                  (not (mv-nth 0 (merge-trees-into-dag-array
                                  trees
                                  var-replacement-alist
                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                  interpreted-function-alist)))
                  (true-listp trees)
                  (all-axe-treep trees)
                  (all-bounded-axe-treep trees dag-len)
                  (symbol-alistp var-replacement-alist)
                  (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
;                  (interpreted-function-alistp interpreted-function-alist)
                  )
             (and
              (all-dargp-less-than (mv-nth 1 (merge-trees-into-dag-array
                                                         trees
                                                         var-replacement-alist
                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                         interpreted-function-alist))
                                              (mv-nth 3 (merge-trees-into-dag-array
                                                         trees
                                                         var-replacement-alist
                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                         interpreted-function-alist)))
              (wf-dagp dag-array-name
                       (mv-nth 2 (merge-trees-into-dag-array
                                  trees
                                  var-replacement-alist
                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                  interpreted-function-alist))
                       (mv-nth 3
                               (merge-trees-into-dag-array
                                trees
                                var-replacement-alist
                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                interpreted-function-alist))
                       dag-parent-array-name
                       (mv-nth 4
                               (merge-trees-into-dag-array
                                trees
                                var-replacement-alist
                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                interpreted-function-alist))
                       (mv-nth 5
                               (merge-trees-into-dag-array
                                trees
                                var-replacement-alist
                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                interpreted-function-alist))
                       (mv-nth 6
                               (merge-trees-into-dag-array
                                trees
                                var-replacement-alist
                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                interpreted-function-alist)))))
    :flag merge-trees-into-dag-array)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d ( ;nth-0-of-nth-of-len-minus1-when-pseudo-dagp
                                   car-becomes-nth-of-0
                                   merge-tree-into-dag-array
                                   merge-trees-into-dag-array)
                                  (natp)))))

(defthm merge-tree-into-dag-array-return-type-2
  (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                (axe-treep tree)
                (bounded-axe-treep tree dag-len)
                (not (mv-nth 0 (merge-tree-into-dag-array tree var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                (symbol-alistp var-replacement-alist)
                (interpreted-function-alistp interpreted-function-alist)
                )
           (and (dargp (mv-nth 1 (merge-tree-into-dag-array
                                             tree
                                             var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             interpreted-function-alist)))
                (<= (mv-nth 3 (merge-tree-into-dag-array
                               tree
                               var-replacement-alist
                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                               interpreted-function-alist))
                    2147483646)))
  :hints (("Goal" :use (:instance merge-tree-into-dag-array-return-type)
           :in-theory (e/d () (merge-tree-into-dag-array-return-type
                               pseudo-dag-arrayp-monotone
                               axe-treep)))))

(defthm merge-trees-into-dag-array-return-type-2
  (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                (all-axe-treep trees)
                (true-listp trees)
                (all-bounded-axe-treep trees dag-len)
                (not (mv-nth 0 (merge-trees-into-dag-array trees var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                (symbol-alistp var-replacement-alist)
                (interpreted-function-alistp interpreted-function-alist))
           (and
            (all-dargp (mv-nth 1 (merge-trees-into-dag-array
                                             trees
                                             var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             interpreted-function-alist)))
            (<= (mv-nth 3 (merge-trees-into-dag-array
                           trees
                           var-replacement-alist
                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                           interpreted-function-alist))
                2147483646)))
  :hints (("Goal" :use (:instance merge-trees-into-dag-array-return-type)
           :in-theory (disable merge-trees-into-dag-array-return-type))))

(defthm dargp-less-than-of-mv-nth-1-of-merge-tree-into-dag-array
  (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                (axe-treep tree)
                (bounded-axe-treep tree dag-len)
                (not (mv-nth 0 (merge-tree-into-dag-array tree var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                (symbol-alistp var-replacement-alist)
                (interpreted-function-alistp interpreted-function-alist))
           (dargp-less-than (mv-nth 1 (merge-tree-into-dag-array
                                                  tree
                                                  var-replacement-alist
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                  interpreted-function-alist))
                                       2147483646))
  :hints (("Goal" :use (:instance merge-tree-into-dag-array-return-type)
           :in-theory (disable merge-tree-into-dag-array-return-type
                               axe-treep))))

(defthm integerp-of-mv-nth-1-of-merge-tree-into-dag-array
  (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                (axe-treep tree)
                (bounded-axe-treep tree dag-len)
                (not (mv-nth 0 (merge-tree-into-dag-array tree var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                (symbol-alistp var-replacement-alist)
                (interpreted-function-alistp interpreted-function-alist))
           (equal (integerp (mv-nth 1 (merge-tree-into-dag-array tree var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                  (not (consp (mv-nth 1 (merge-tree-into-dag-array tree var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))))
  :hints (("Goal" :use (:instance dargp-less-than-of-mv-nth-1-of-merge-tree-into-dag-array)
           :in-theory (disable dargp-less-than-of-mv-nth-1-of-merge-tree-into-dag-array
                               merge-tree-into-dag-array-return-type
                               axe-treep))))

(defthm nonneg-of-mv-nth-1-of-merge-tree-into-dag-array
  (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                (axe-treep tree)
                (bounded-axe-treep tree dag-len)
                (not (mv-nth 0 (merge-tree-into-dag-array tree var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                (symbol-alistp var-replacement-alist)
                (interpreted-function-alistp interpreted-function-alist))
           (<= 0 (mv-nth 1 (merge-tree-into-dag-array tree var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
  :hints (("Goal" :use (:instance dargp-less-than-of-mv-nth-1-of-merge-tree-into-dag-array)
           :in-theory (disable dargp-less-than-of-mv-nth-1-of-merge-tree-into-dag-array
                               merge-tree-into-dag-array-return-type
                               axe-treep))))

(defthm bound-of-mv-nth-1-of-merge-tree-into-dag-array
  (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                (axe-treep tree)
                (bounded-axe-treep tree dag-len)
                (not (mv-nth 0 (merge-tree-into-dag-array tree var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                (symbol-alistp var-replacement-alist)
                (interpreted-function-alistp interpreted-function-alist))
           (<= (mv-nth 1 (merge-tree-into-dag-array tree var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))
               2147483645))
  :hints (("Goal" :use (integerp-of-mv-nth-1-of-merge-tree-into-dag-array
                        dargp-less-than-of-mv-nth-1-of-merge-tree-into-dag-array)
           :in-theory (disable dargp-less-than-of-mv-nth-1-of-merge-tree-into-dag-array
                               merge-tree-into-dag-array-return-type
                               integerp-of-mv-nth-1-of-merge-tree-into-dag-array))))

(verify-guards merge-tree-into-dag-array
   :otf-flg t
   :hints (("Goal" :in-theory (e/d (axe-treep
                                    car-becomes-nth-of-0
                                    cadr-becomes-nth-of-1
                                    consp-of-cdr-of-nth-when-all-dargp
                                    <-of-nth-when-all-dargp-less-than
                                    true-listp-of-nth-1-of-nth-0-when-axe-treep
                                    consp-when-true-listp-iff)
                                   (all-axe-treep
                                    axe-treep
                                    myquotep
                                    natp
                                    dargp
                                    pseudo-dag-arrayp))
            :do-not '(generalize eliminate-destructors))))

(in-theory (disable MERGE-TREE-INTO-DAG-ARRAY-RETURN-TYPE)) ;needed for the call to def-dag-builder-theorems

(def-dag-builder-theorems
  (merge-tree-into-dag-array tree var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)
  (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((axe-treep tree)
         (bounded-axe-treep tree dag-len)
         (symbol-alistp var-replacement-alist)
         (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
         ;;(<= (+ (len vars) dag-len) 2147483645)
         ;(interpreted-function-alistp interpreted-function-alist)
         )
  :recursivep nil
  :hints (("Goal" ;:expand (merge-tree-into-dag-array tree var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)
           :in-theory (disable wf-dagp)
           :use (:instance merge-tree-into-dag-array-return-type)
           ))
  :dag-parent-array-name dag-parent-array-name
  :dag-array-name dag-array-name)

;returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;will nodenum-or-quotep always be a quotep or the top node?
(defund make-term-into-dag-array (term dag-array-name dag-parent-array-name interpreted-function-alist)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp dag-array-name)
                              (symbolp dag-parent-array-name)
                              (interpreted-function-alistp interpreted-function-alist))))
  (merge-tree-into-dag-array term ;overkill since this can't contain nodenums?
                             nil ;initial var-replacement-alist
                             (make-empty-array dag-array-name 10) ;fixme why 10?
                             0 ;initial dag-len
                             (make-empty-array dag-parent-array-name 10)
                             nil         ;dag-constant-alist
                             nil         ;dag-variable-alist
                             dag-array-name dag-parent-array-name
                             interpreted-function-alist))

;; (def-dag-builder-theorems
;;   (make-term-into-dag-array term dag-array-name dag-parent-array-name interpreted-function-alist)
;;   (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;   :hyps ((pseudo-termp term)
;;          (symbolp dag-array-name)
;;          (symbolp dag-parent-array-name)
;;          (interpreted-function-alistp interpreted-function-alist))
;;   :recursivep nil
;;   :hints (("Goal" :in-theory (enable MAKE-TERM-INTO-DAG-ARRAY)))
;;   :dag-parent-array-name dag-parent-array-name
;;   :dag-array-name dag-array-name)

;edited from what def-dag-builder-theorems produces
(DEFTHM TYPE-OF-MAKE-TERM-INTO-DAG-ARRAY
  (IMPLIES (AND
                (NOT
                 (MV-NTH 0
                         (MAKE-TERM-INTO-DAG-ARRAY TERM
                                                   DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
                                                   INTERPRETED-FUNCTION-ALIST)))
                (PSEUDO-TERMP TERM)
                (SYMBOLP DAG-ARRAY-NAME)
                (SYMBOLP DAG-PARENT-ARRAY-NAME)
                  ;(INTERPRETED-FUNCTION-ALISTP INTERPRETED-FUNCTION-ALIST)
                )
           (AND
            (WF-DAGP
             DAG-ARRAY-NAME
             (MV-NTH 2
                     (MAKE-TERM-INTO-DAG-ARRAY TERM
                                               DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
                                               INTERPRETED-FUNCTION-ALIST))
             (MV-NTH 3
                     (MAKE-TERM-INTO-DAG-ARRAY TERM
                                               DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
                                               INTERPRETED-FUNCTION-ALIST))
             DAG-PARENT-ARRAY-NAME
             (MV-NTH 4
                     (MAKE-TERM-INTO-DAG-ARRAY TERM
                                               DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
                                               INTERPRETED-FUNCTION-ALIST))
             (MV-NTH 5
                     (MAKE-TERM-INTO-DAG-ARRAY TERM
                                               DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
                                               INTERPRETED-FUNCTION-ALIST))
             (MV-NTH 6
                     (MAKE-TERM-INTO-DAG-ARRAY TERM
                                               DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
                                               INTERPRETED-FUNCTION-ALIST)))
            (<=
             (MV-NTH 3
                     (MAKE-TERM-INTO-DAG-ARRAY TERM
                                               DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
                                               INTERPRETED-FUNCTION-ALIST))
             2147483646)))
  :OTF-FLG T
  :HINTS (("Goal" :IN-THEORY (ENABLE MAKE-TERM-INTO-DAG-ARRAY))))

;;do we need this?
(defthm pseudo-dag-arrayp-of-mv-nth-2-of-make-term-into-dag-array
  (implies (and (pseudo-termp term)
                (not (mv-nth 0 (make-term-into-dag-array term dag-array-name dag-parent-array-name interpreted-function-alist)))
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name))
           (pseudo-dag-arrayp dag-array-name
                              (mv-nth 2
                                      (make-term-into-dag-array term dag-array-name dag-parent-array-name interpreted-function-alist))
                              (mv-nth 3
                                      (make-term-into-dag-array term dag-array-name dag-parent-array-name interpreted-function-alist))))
  :hints (("Goal" :use (:instance TYPE-OF-MAKE-TERM-INTO-DAG-ARRAY)
           :in-theory (disable TYPE-OF-MAKE-TERM-INTO-DAG-ARRAY))))

;returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
(defund make-terms-into-dag-array (terms dag-array-name dag-parent-array-name interpreted-function-alist)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (symbolp dag-array-name)
                              (symbolp dag-parent-array-name)
                              (interpreted-function-alistp interpreted-function-alist))))
  (merge-trees-into-dag-array terms
                              nil ;initial var-replacement-alist
                              (make-empty-array dag-array-name 1000) ;fixme why 1000?
                              0 ;initial dag-len
                              (make-empty-array dag-parent-array-name 1000)
                              nil ;empty dag-constant-alist
                              nil ;empty dag-variable-alist
                              dag-array-name dag-parent-array-name
                              interpreted-function-alist))

;; Returns (mv erp dag-or-quotep).  Uses arrays to do the work.
(defund make-term-into-dag (term interpreted-function-alist)
  (declare (xargs :guard (and (pseudo-termp term)
                              (interpreted-function-alistp interpreted-function-alist))
                  :guard-hints (("Goal" :use (:instance pseudo-dag-arrayp-of-mv-nth-2-of-make-term-into-dag-array
                                                        (dag-array-name 'make-term-into-dag-array)
                                                        (dag-parent-array-name 'make-term-into-dag-parent-array))
                                 :in-theory (disable pseudo-dag-arrayp-of-mv-nth-2-of-make-term-into-dag-array)))))
  (mv-let (erp nodenum-or-quotep ;this will always be the top nodenum, right?
               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (make-term-into-dag-array term 'make-term-into-dag-array 'make-term-into-dag-parent-array interpreted-function-alist)
    (declare (ignore dag-parent-array dag-constant-alist dag-variable-alist))
    (if erp
        (mv erp nil)
      (if (consp nodenum-or-quotep)
          (mv (erp-nil) nodenum-or-quotep)
        (mv (erp-nil) (array-to-alist 'make-term-into-dag-array dag-array dag-len))))))

;; Returns (mv erp dag-or-quotep).
;; Convert term to a DAG (or quoted constant).  Uses arrays to do the work.
;doesn't handle inlined constants in the embedded dags?
;compare to make-term-into-dag
(defund dagify-term (term)
  (declare (xargs :guard (pseudo-termp term)))
  (make-term-into-dag term nil))

;; (mutual-recursion
;;  (defun term-size (term)
;;    (declare (xargs :guard (pseudo-termp term)))
;;    (if (

;; ;; Returns the DAG.  Requires TERM to be small enough to avoid the dag size
;; ;; limit.  Thus, this doesn't return an error.
;; (defund dagify-small-term (term)
;;   (declare (xargs :guard (and (pseudo-termp term)
;;                               (< (term-size term) 1000))))
;;   (make-term-into-dag term nil))

;; Returns (mv erp dag).
(defund dagify-term2 (term)
  (declare (xargs :guard (pseudo-termp term)))
  (make-term-into-dag term nil))

;; Suppresses any error and returns the dag.
(defund dagify-term! (term)
  (declare (xargs :guard (pseudo-termp term)))
  (b* (((mv erp dag) (dagify-term2 term)))
    (if erp
        :error
      dag)))

;; Returns (mv erp nodenum-or-quotep dag-lst).  Uses arrays to do the work.
;leaves pre-existing nodenums in dag unchanged
;; Nodenums in TREE refer to DAG-LIST.  Vars in tree may be replaced by
;; var-replacement-alist; otherwise, they are the same as the vars in DAG-LST.
;; todo: make a specialized version of this for terms?
(defund merge-tree-into-dag (tree dag-lst ;can now be a quotep
                                  ;;interpreted-function-alist
                                  var-replacement-alist
                                  )
  (declare (xargs :guard (and (axe-treep tree)
                              (or (myquotep dag-lst)
                                  (and (pseudo-dagp dag-lst)
                                       (<= (len dag-lst) 2147483646)))
                              (symbol-alistp var-replacement-alist)
                              (if (quotep dag-lst)
                                  t
                                (all-dargp-less-than (strip-cdrs var-replacement-alist) (+ 1 (top-nodenum dag-lst)))))
                  :verify-guards nil ;issue with calling make-into-array on an empty array
                  ))
  (let* ((dag-lst (if (quotep dag-lst) nil dag-lst))
         (dag-len (+ 1 (top-nodenum dag-lst)))
         (dag-array-name 'dag-array-for-merge-tree-into-dag)
         (dag-parent-array-name 'dag-parent-array-for-merge-tree-into-dag)
         (dag-array (make-into-array dag-array-name dag-lst)))
    (mv-let (dag-parent-array dag-constant-alist dag-variable-alist)
      (make-dag-indices dag-array-name dag-array dag-parent-array-name dag-len)
      (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (merge-tree-into-dag-array tree
                                   var-replacement-alist
                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                   nil ;interpreted-function-alist
                                   )
        (declare (ignore dag-parent-array dag-constant-alist dag-variable-alist))
        (if erp
            (mv erp nil nil)
          (mv (erp-nil) nodenum-or-quotep (array-to-alist dag-array-name dag-array dag-len)))))))

;; Merge the TREE into the dag and drop from the result any DAG nodes that don't support the top node of the tree.
;; Returns (mv erp res) where res is a dag-lst or quotep.  Uses arrays to do the work.
;; If the tree contains integers, they are nodenums in DAG.
(defund compose-tree-and-dag (tree dag ;can now be a quotep
                                   ;;interpreted-function-alist
                                   var-replacement-alist
                                   )
  (declare (xargs :guard (and (axe-treep tree)
                              (or (myquotep dag)
                                  (pseudo-dagp dag))
                              (symbol-alistp var-replacement-alist)
                              (if (quotep dag)
                                  t
                                (all-dargp-less-than (strip-cdrs var-replacement-alist) (+ 1 (top-nodenum dag)))))
                  :verify-guards nil))
  (mv-let (erp nodenum-or-quotep new-dag)
    (merge-tree-into-dag tree dag var-replacement-alist) ;todo: this converts the array back to a list, but get-subdag converts it back to an array
    (if erp
        (mv erp nil)
      (mv (erp-nil)
          (get-subdag nodenum-or-quotep new-dag)))))

;; fixme does all the stuff handle lambdas?

;; Returns (mv erp dag-or-quote), where dag-or-quote is equivalent to TERM with
;; VAR-TO-REPLACE replaced by DAG. Other vars in term are left unchanged. Node
;; numbers in DAG are not preserved.
;TODO: Generalize to take an alist from vars to dags instead of a single var and DAG.
;could easily add support for term being an axe tree?
;does not inline embedded dags with ifns (since no ifns are passed in to this)?
(defun compose-term-and-dag (term var-to-replace dag)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp var-to-replace)
                              (or (myquotep dag)
                                  (pseudo-dagp dag)))
                  :verify-guards nil))
  (if (quotep dag) ;do we need this special case?
      ;; Unusual case (dag is just a constant):
      (dagify-term (sublis-var-simple ;-and-eval   ;todo: call something simpler that doesn't use arrays?  ;consider sublis-var-and-eval?
                    (acons var-to-replace dag nil)
                    term))
    ;;Normal case (dag is a dag-lst):
    ;;todo: maybe call something here that just works on terms?
    (compose-tree-and-dag term dag (acons var-to-replace (top-nodenum dag) nil))))

;;(equal (compose-term-and-dag '(foo x) 'x (dagify-term '(bar (baz x)))) ((3 FOO 2) (2 BAR 1) (1 BAZ 0) (0 . X)))
;;(equal (compose-term-and-dag '(foo x) 'x ''2) ((0 FOO '2)))

;fffixme use this more!
;; TODO: Consider returning the dag-array, etc. if we are just going to turn the result of this into an array anyway.
;; Returns (mv erp dag-or-quote).
(defun compose-term-and-dag-safe-fn (term var-to-replace dag extra-vars)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp var-to-replace)
                              (or (myquotep dag)
                                  (pseudo-dagp dag)))
                  :verify-guards nil))
  (let ((term-vars (all-vars term)))
    (if (not (member-eq var-to-replace term-vars))
        (prog2$ (er hard? 'compose-term-and-dag-safe "Var to be replaced, ~x0, is not among the vars in the term ~x1." var-to-replace term)
                (mv (erp-t) nil))
      (if (not (subsetp-eq term-vars (cons var-to-replace extra-vars))) ;todo: consider putting this check back, but we'll have to declare some extra vars
          (prog2$ (er hard? 'compose-term-and-dag-safe "expected: ~x0. extra vars: ~x1. term: ~x2" var-to-replace (remove-eq var-to-replace term-vars) term)
                  (mv (erp-t) nil))
        (compose-term-and-dag term var-to-replace dag)))))

;; Returns (mv erp dag-or-quote).
(defmacro compose-term-and-dag-safe (term var-to-replace dag &key (extra-vars 'nil))
  `(compose-term-and-dag-safe-fn ,term ,var-to-replace ,dag ,extra-vars))

;; ;can't we directly merge the term into the dag?
;; (defun equate-term-and-dag (term dag)
;;   (make-equality-dag dag
;;                      (dagify-term term)))

;;
;; compose-dags
;;

;it may be common for subdag-for-var to be large but main-dag to be small - as when we are extracting a tiny piece of a big dag
;replaces the given var in main-dag with subdag-for-var and returns a dag
;i hope it's safe to assume that subdag-for-var is already simplified
;; Returns (mv erp dag-lst-or-quotep).
;move!
(defun compose-dags (main-dag var-to-replace subdag-for-var check-varsp)
  (declare (xargs :guard (and (or (myquotep main-dag)
                                  (pseudo-dagp main-dag))
                              (symbolp var-to-replace)
                              (or (myquotep subdag-for-var)
                                  (pseudo-dagp subdag-for-var))
                              (<= (+ (if (myquotep main-dag)
                                         0
                                       (LEN MAIN-DAG))
                                     (if (myquotep SUBDAG-FOR-VAR)
                                         0
                                       (LEN SUBDAG-FOR-VAR)))
                                  2147483645))
                  :verify-guards nil
                  :guard-hints (("Goal" :in-theory (disable DARGP PSEUDO-DAG-ARRAYP)))
                  ))
  (if (quotep main-dag)
      (if check-varsp
          (prog2$ (er hard? 'compose-dags "var ~x0 isn't present in DAG ~X12" var-to-replace main-dag nil)
                  (mv (erp-t) nil))
        (mv (erp-nil) main-dag))
    (let ((main-dag-vars (dag-vars main-dag)))
      (if (and check-varsp
               (not (member-eq var-to-replace main-dag-vars)))
          (prog2$ (er hard? 'compose-dags "var ~x0 isn't present in DAG ~X12" var-to-replace main-dag nil)
                  (mv (erp-t) nil))
        (if (quotep subdag-for-var)
            (b* ( ;; make the subdag into a dag array:
                 (dag-len 0)
                 (dag-array (make-empty-array 'dag-array (+ 1 (top-nodenum main-dag))))
                 (dag-parent-array (make-empty-array 'dag-parent-array (+ 1 (top-nodenum main-dag))))
                 (dag-constant-alist nil)
                 (dag-variable-alist nil)
                 ;; initially empty (the var gets renamed by the alist):
                 (renaming-array (make-empty-array 'renaming-array-for-merge-embedded-dag-into-dag-array (+ 1 (top-nodenum main-dag))))
                 ((mv erp renaming-array dag-array & & & &)
                  (merge-embedded-dag-into-dag-array (reverse-list main-dag)
                                                     (acons var-to-replace subdag-for-var nil) ;map the var to the quotep
                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist 'dag-array 'dag-parent-array
                                                     renaming-array
                                                     nil ;todo: interpreted-function-alist
                                                     ))
                 ((when erp) (mv erp nil))
                 (top-nodenum (aref1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array (top-nodenum main-dag))))
              (mv (erp-nil) (drop-non-supporters-array 'dag-array dag-array top-nodenum nil)))
          (b* ( ;; make the subdag into a dag array:
               (dag-len (+ 1 (top-nodenum subdag-for-var)))
               (dag-array (make-into-array-with-len 'dag-array subdag-for-var (+ dag-len 1 (top-nodenum main-dag))))
               ((mv dag-parent-array dag-constant-alist dag-variable-alist)
                (make-dag-indices 'dag-array dag-array 'dag-parent-array dag-len))
               ;; initially empty (the var gets renamed by the alist):
               (renaming-array (make-empty-array 'renaming-array-for-merge-embedded-dag-into-dag-array (+ 1 (top-nodenum main-dag))))
               ((mv erp renaming-array dag-array & & & &)
                (merge-embedded-dag-into-dag-array (reverse-list main-dag)
                                                   (acons var-to-replace (top-nodenum subdag-for-var) nil)
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist 'dag-array 'dag-parent-array
                                                   renaming-array
                                                   nil ;todo: interpreted-function-alist
                                                   ))
               ((when erp) (mv erp nil))
               (top-nodenum (aref1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array (top-nodenum main-dag))))
            (mv (erp-nil) (drop-non-supporters-array 'dag-array dag-array top-nodenum nil))))))))

;;(compose-dags ''3 'x ''4 nil)
;;(compose-dags ''3 'x '((2 foo 1) (1 bar 0) (0 . x)) nil)
;;(compose-dags '((2 foo 1) (1 bar 0) (0 . x)) 'x ''3 t)
;;(compose-dags '((2 foo 1) (1 bar 0) (0 . x)) 'x '((2 baz 1) (1 box 0) (0 . newvar)) t)

;;use elsewhere?
(defund-inline evaluatable-fn-and-argsp (fn arg-nodenums-or-quoteps interpreted-function-alist)
  (declare (xargs :guard (and ;(symbolp fn)
                          (all-dargp arg-nodenums-or-quoteps)
                          (symbol-alistp interpreted-function-alist))))
  (and (all-consp arg-nodenums-or-quoteps) ;all args must be quoted constants
       (or (member-eq fn *axe-evaluator-functions*)
           (eq fn 'dag-val-with-axe-evaluator) ;fixme add to *axe-evaluator-functions*? or use a different list? fixme add the other generated fn names?
           (assoc-eq fn interpreted-function-alist))))

(defthm all-myquotep-when-evaluatable-fn-and-argsp
  (implies (and (evaluatable-fn-and-argsp fn arg-nodenums-or-quoteps interpreted-function-alist)
                (all-dargp arg-nodenums-or-quoteps))
           (all-myquotep arg-nodenums-or-quoteps))
  :hints (("Goal" :in-theory (enable evaluatable-fn-and-argsp  all-myquotep-when-all-dargp))))

(defthm alistp-of-set-difference-equal
  (implies (alistp x)
           (alistp (set-difference-equal x y))))

;;use elsewhere?
;; recoginize a suitable call of the form (dag-val-with-axe-evaluator dag alist interpreted-function-alist array-depth).
(defund-inline call-of-dag-val-with-axe-evaluator-with-inlineable-dagp (fn arg-nodenums-or-quoteps interpreted-function-alist)
  (declare (xargs :guard (and ;(symbolp fn)
                          (all-dargp arg-nodenums-or-quoteps)
                          (symbol-alistp interpreted-function-alist))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))
                  ))
  (and (eq 'dag-val-with-axe-evaluator fn)
       (= 4 (len arg-nodenums-or-quoteps))
       ;; it's of the form: (dag-val-with-axe-evaluator DAG ALIST INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
       (if (consp (first arg-nodenums-or-quoteps)) ;the dag to inline -- could it ever be the nodenum of a quotep?
           t
         (prog2$ (cw "(WARNING Found a call to dag-val-with-axe-evaluator, but the dag isn't a quoted constant.)~%") ;print more?
                 nil))
       (not (consp (second arg-nodenums-or-quoteps)))  ;todo: handle the case of a constant alist? ;uncomment?
       (if (pseudo-dagp (unquote (first arg-nodenums-or-quoteps)))
           t
         (prog2$ (cw "(WARNING Found a call to dag-val-with-axe-evaluator, but the dag is ill-formed.)~%") ;print more?
                 nil))
       (<= (len (unquote (first arg-nodenums-or-quoteps))) 2147483646)
       ;;the interpreted-function-alist for the embedded dag must be consistent with the one passed in: - or maybe the dag only includes built in fns?  what if its the nodenum of a quotep?
       (consp (third arg-nodenums-or-quoteps))
       (interpreted-function-alistp (unquote (third arg-nodenums-or-quoteps)))
       (if (subsetp-equal (unquote (third arg-nodenums-or-quoteps))
                          interpreted-function-alist)
           t
         (let ((difference (set-difference-equal (unquote (third arg-nodenums-or-quoteps)) interpreted-function-alist)))
           (prog2$ (cw "(WARNING Found a call to dag-val-with-axe-evaluator, but the interpreted-function-alist isn't a subset of the one passed in.  Thus, we are not inlining.  Offending entries: ~x0.  Corresponding entried in alist: ~x1)~%"
                       difference ;(set-difference-eq (strip-cars (unquote (third arg-nodenums-or-quoteps))) (strip-cars interpreted-function-alist))
                       (lookup-eq-lst (strip-cars difference) interpreted-function-alist)
                       )
                   nil)))))

(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-0
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (consp (nth 0 arg-nodenums-or-quoteps)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp))))

;; (defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-0b
;;   (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
;;            (equal (len (nth 0 arg-nodenums-or-quoteps))
;;                   2))
;;   :rule-classes :forward-chaining
;;   :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp))))

(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-1
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (consp (cadr (first arg-nodenums-or-quoteps))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp))))

(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-2
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (weak-dagp-aux (cadr (first arg-nodenums-or-quoteps))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp))))

(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-3
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (equal (len arg-nodenums-or-quoteps) 4))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp))))

(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-4
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (not (consp (nth 1 arg-nodenums-or-quoteps))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp))))

;the bottom node of the embedded dag is 0
(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-5
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (equal (nth 0 (nth (+ -1 (len (nth 1 (nth 0 arg-nodenums-or-quoteps))))
                              (nth 1 (nth 0 arg-nodenums-or-quoteps))))
                  0))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp
                                     car-becomes-nth-of-0))))

;; top nodenum is a nat
(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-6
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (natp (nth 0 (nth 0 (nth 1 (nth 0 arg-nodenums-or-quoteps))))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp
                                     car-becomes-nth-of-0))))

;; top nodenum is bounded
(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-7
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (not (< 2147483645
                   (nth 0 (nth 0 (nth 1 (nth 0 arg-nodenums-or-quoteps)))))))
  :rule-classes (:forward-chaining :linear)
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp
                                     car-becomes-nth-of-0))))

(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-8
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (pseudo-dagp (nth 1 (nth 0 arg-nodenums-or-quoteps))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp
                                     car-becomes-nth-of-0))))

(local (in-theory (disable myquotep)))

(defthm assoc-equal-when-lookup-equal-cheap
  (implies (lookup-equal term var-replacement-alist)
           (assoc-equal term var-replacement-alist))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthm dargp-less-than-of-lookup-equal
  (implies (and (lookup-equal term var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist)
                                                dag-len))
           (dargp-less-than (lookup-equal term var-replacement-alist) dag-len))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthm symbol-listp-of-cadr-of-car-when-pseudo-termp-cheap ;the ;lambda vars
  (implies (and (pseudo-termp term)
                (consp (car term)))
           (symbol-listp (cadr (car term))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(defthm symbol-listp-of-true-list-fix
  (implies (symbol-listp x)
           (symbol-listp (true-list-fix x))))

;move?
;; TODO: Consider handling other versions of IF top-down.
(mutual-recursion
 ;;This one replaces the vars in term using var-replacement-alist.
 ;;TERM is a tree over variables and quoteps (fixme and nodenums, currently - fixme)
 ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
 ;; where nodenum-or-quotep is equivalent to the term passed in, and nodes already in the dag passed in remain unchanged (and the aux. data structures have been updated, of course)
 (defund merge-term-into-dag-array (term
                                   var-replacement-alist ;maps all vars in TERM to quoteps or nodenums in dag-array
                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                   interpreted-function-alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                               (symbol-alistp var-replacement-alist)
                               (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                               (interpreted-function-alistp interpreted-function-alist))
                   :guard-hints (("Goal" :in-theory (disable merge-term-into-dag-array)))
                   :verify-guards nil ; see below
                   ))
   (if (variablep term)
       ;;it's a variable, so look up its possible replacement:
       (let ((nodenum-or-quotep (lookup-eq term var-replacement-alist)))
         (if nodenum-or-quotep
             (mv (erp-nil) nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           ;; no substitution applied to this var:
           (add-variable-to-dag-array-with-name term dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           ;; term is a quoted constant:
           (mv (erp-nil) term dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
         ;; term is a function call:
         (let* ((args (fargs term)))
           (if (eq 'if fn) ;fixme handle other IFs?
               (mv-let (erp test-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                 (merge-term-into-dag-array (first args) var-replacement-alist
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                            interpreted-function-alist)
                 (if erp
                     (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                   (if (consp test-nodenum-or-quotep) ;tests for quotep
                       ;;the test was resolved:
                       (merge-term-into-dag-array (if (unquote test-nodenum-or-quotep) (second args) (third args)) var-replacement-alist
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                  interpreted-function-alist)
                     ;;could not resolve the test:
                     (mv-let (erp then-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                       (merge-term-into-dag-array (second args) var-replacement-alist
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                  interpreted-function-alist)
                       (if erp
                           (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                         (mv-let (erp else-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                           (merge-term-into-dag-array (third args) var-replacement-alist
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                      interpreted-function-alist)
                           (if erp
                               (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                             ;;treat it like a normal function call (we know it's not a ground term because the if-test is not a constant)
                             (progn$ ;(cw "Adding (~x0 : ~x1).~%" fn arg-nodenums-or-quoteps)
                              (add-function-call-expr-to-dag-array-with-name fn (list test-nodenum-or-quotep then-nodenum-or-quotep else-nodenum-or-quotep)
                                                                                   dag-array dag-len dag-parent-array
                                                                                   dag-constant-alist dag-variable-alist
                                                                                   dag-array-name dag-parent-array-name)))))))))
             ;;begin by adding the args to the dag: (expensive to cons this up, if they are ground terms?)
             (mv-let
               (erp arg-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
               (merge-terms-into-dag-array args var-replacement-alist
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                           interpreted-function-alist)
               (if erp
                   (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                 ;;check for the special case of a call to dag-val-with-axe-evaluator where we can inline the dag:
                 (if (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
                     ;;term is a call of dag-val-with-axe-evaluator, and we can inline its embedded dag:
                     (b* ((quoted-dag (first arg-nodenums-or-quoteps))
                          (dag (unquote quoted-dag))
                          (vars (dag-vars dag))
                          (alist-nodenum (second arg-nodenums-or-quoteps)) ;todo: handle a constant alist
                          ((mv erp variable-node-alist-for-dag dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                           (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array
                                                          dag-constant-alist dag-variable-alist nil dag-array-name dag-parent-array-name))
                          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                          ((mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                           (merge-embedded-dag-into-dag-array (reverse-list dag)
                                                              variable-node-alist-for-dag
                                                              dag-array dag-len dag-parent-array
                                                              dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                              (make-empty-array 'renaming-array-for-merge-embedded-dag-into-dag-array (+ 1 (top-nodenum dag))) ; nil ;the translation-alist
                                                              interpreted-function-alist))
                          ;;fixme are the aux data structures updated right?
                          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                       (mv (erp-nil)
                           (aref1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array (top-nodenum dag)) ;(lookup (top-nodenum dag) translation-alist)
                           dag-array dag-len dag-parent-array
                           dag-constant-alist dag-variable-alist))
                   (if (consp fn) ;tests for ((lambda <formals> <body>) ...<actuals>...) ;move this case up?
                       (let* ((formals (lambda-formals fn))
                              (body (lambda-body fn)))
                         (merge-term-into-dag-array body
                                                    (pairlis$-fast formals arg-nodenums-or-quoteps) ;save this consing?
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                    interpreted-function-alist))
                     ;; normal function call:
                     (if (evaluatable-fn-and-argsp fn arg-nodenums-or-quoteps interpreted-function-alist)
                         ;;it's a ground term:
                         (mv (erp-nil)
                             (enquote (apply-axe-evaluator-to-quoted-args fn arg-nodenums-or-quoteps interpreted-function-alist 0))
                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                       ;;not a ground term; just add it to the dag:
                       (progn$ ;(cw "Adding (~x0 : ~x1).~%" fn arg-nodenums-or-quoteps)
                        (add-function-call-expr-to-dag-array-with-name fn arg-nodenums-or-quoteps
                                                                             dag-array dag-len dag-parent-array
                                                                             dag-constant-alist dag-variable-alist
                                                                             dag-array-name dag-parent-array-name)))))))))))))

 ;;TERMS are trees with variables, nodenums (new!), and quoteps at the leaves
 ;; Returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;fixme use a changep flag to not recons the list of the terms are constants
 (defund merge-terms-into-dag-array (terms
                                    var-replacement-alist
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                    interpreted-function-alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (true-listp terms)
                               (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                               (symbol-alistp var-replacement-alist)
                               (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                               (interpreted-function-alistp interpreted-function-alist))))
   (if (endp terms)
       (mv (erp-nil) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
     (b* (((mv erp car-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           (merge-term-into-dag-array (first terms) var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
          ((mv erp cdr-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           (merge-terms-into-dag-array (rest terms) var-replacement-alist
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                       interpreted-function-alist))
          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
       (mv (erp-nil)
           (cons car-nodenum-or-quotep cdr-nodenums-or-quoteps)
           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))

(make-flag merge-term-into-dag-array)

(defthm-flag-merge-term-into-dag-array
  (defthm natp-of-mv-nth-3-of-merge-term-into-dag-array-2 ;dup? with something generated by def-dag-builder-theorems
    (implies (natp dag-len)
             (natp (mv-nth 3 (merge-term-into-dag-array
                              term var-replacement-alist dag-array dag-len dag-parent-array
                              dag-constant-alist dag-variable-alist
                              dag-array-name dag-parent-array-name
                              interpreted-function-alist))))
    :flag merge-term-into-dag-array)
  (defthm natp-of-mv-nth-3-of-merge-terms-into-dag-array-2 ;dup?
    (implies (natp dag-len)
             (natp (mv-nth 3 (merge-terms-into-dag-array
                              terms var-replacement-alist
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                              interpreted-function-alist))))
    :flag merge-terms-into-dag-array)
  :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array merge-terms-into-dag-array) (natp)))))

(defthm-flag-merge-term-into-dag-array
  (defthmd <=-of-mv-nth-3-of-merge-term-into-dag-array-2 ;dup? with something generated by def-dag-builder-theorems
    (implies (natp dag-len)
             (<= dag-len (mv-nth 3 (merge-term-into-dag-array
                                    term var-replacement-alist dag-array dag-len dag-parent-array
                                    dag-constant-alist dag-variable-alist
                                    dag-array-name dag-parent-array-name
                                    interpreted-function-alist))))
    :flag merge-term-into-dag-array)
  (defthmd <=-of-mv-nth-3-of-merge-terms-into-dag-array-2 ;dup?
    (implies (natp dag-len)
             (<= dag-len (mv-nth 3 (merge-terms-into-dag-array
                                    terms var-replacement-alist
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                    interpreted-function-alist))))
    :flag merge-terms-into-dag-array)
  :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array merge-terms-into-dag-array) (natp)))))

(defthmd <=-of-mv-nth-3-of-merge-term-into-dag-array-2-linear ;dup? with something generated by def-dag-builder-theorems
  (implies (natp dag-len)
           (<= dag-len (mv-nth 3 (merge-term-into-dag-array
                                  term var-replacement-alist dag-array dag-len dag-parent-array
                                  dag-constant-alist dag-variable-alist
                                  dag-array-name dag-parent-array-name
                                  interpreted-function-alist))))
  :rule-classes :linear
  :hints (("Goal" :use <=-of-mv-nth-3-of-merge-term-into-dag-array-2)))

(defthmd <=-of-mv-nth-3-of-merge-terms-into-dag-array-2-linear ;dup?
  (implies (natp dag-len)
           (<= dag-len (mv-nth 3 (merge-terms-into-dag-array
                                  terms var-replacement-alist
                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                  interpreted-function-alist))))
  :rule-classes :linear
  :hints (("Goal" :use <=-of-mv-nth-3-of-merge-terms-into-dag-array-2)))

(defthmd <=-of-mv-nth-3-of-merge-term-into-dag-array-2-gen ;dup? with something generated by def-dag-builder-theorems
  (implies (and (natp dag-len)
                (<= bound dag-len))
           (<= bound (mv-nth 3 (merge-term-into-dag-array
                                term var-replacement-alist dag-array dag-len dag-parent-array
                                dag-constant-alist dag-variable-alist
                                dag-array-name dag-parent-array-name
                                interpreted-function-alist))))
  :hints (("Goal" :use (:instance <=-of-mv-nth-3-of-merge-term-into-dag-array-2)
           :in-theory (disable <=-of-mv-nth-3-of-merge-term-into-dag-array-2))))

(defthmd <=-of-mv-nth-3-of-merge-terms-into-dag-array-2-gen ;dup?
  (implies (and (natp dag-len)
                (<= bound dag-len))
           (<= bound (mv-nth 3 (merge-terms-into-dag-array
                                terms var-replacement-alist
                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                interpreted-function-alist))))
  :hints (("Goal" :use (:instance  <=-of-mv-nth-3-of-merge-terms-into-dag-array-2)
           :in-theory (disable  <=-of-mv-nth-3-of-merge-terms-into-dag-array-2))))

;drop?
(defthm-flag-merge-term-into-dag-array
  (defthm dag-constant-alistp-of-mv-nth-5-of-merge-term-into-dag-array
    (implies (and (dag-constant-alistp dag-constant-alist)
                  (natp dag-len))
             (dag-constant-alistp (mv-nth 5 (merge-term-into-dag-array
                                             term var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             interpreted-function-alist))))
    :flag merge-term-into-dag-array)
  (defthm dag-constant-alistp-of-mv-nth-5-of-merge-terms-into-dag-array
    (implies (and (dag-constant-alistp dag-constant-alist)
                  (natp dag-len))
             (dag-constant-alistp (mv-nth 5 (merge-terms-into-dag-array
                                             terms var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             interpreted-function-alist))))
    :flag merge-terms-into-dag-array)
    :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array merge-terms-into-dag-array) ()))))

;drop?
(defthm-flag-merge-term-into-dag-array
  (defthm dag-variable-alistp-of-mv-nth-6-of-merge-term-into-dag-array
    (implies (and (pseudo-termp term)
                  (dag-variable-alistp dag-variable-alist)
                  (natp dag-len))
             (dag-variable-alistp (mv-nth 6 (merge-term-into-dag-array
                                             term var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             interpreted-function-alist))))
    :flag merge-term-into-dag-array)
  (defthm dag-variable-alistp-of-mv-nth-6-of-merge-terms-into-dag-array
    (implies (and (pseudo-term-listp terms)
                  (dag-variable-alistp dag-variable-alist)
                  (natp dag-len))
             (dag-variable-alistp (mv-nth 6 (merge-terms-into-dag-array
                                             terms var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             interpreted-function-alist))))
    :flag merge-terms-into-dag-array)
  :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array
                                   merge-terms-into-dag-array
                                   call-of-dag-val-with-axe-evaluator-with-inlineable-dagp ;somewhat slow. why didn't the forward-chaining rules suffice?
                                   )
                                  ()))))

(local (in-theory (disable use-all-<-for-car
                           all-dargp-less-than-when-<-of-largest-non-quotep
                           ;;all-dargp-less-than-when-all-consp
                           )))

(set-case-split-limitations 'nil)
(set-case-split-limitations '(10 10))

(local (in-theory (disable consp-from-len-cheap
                           ;use-all-consp-for-car
                           default-+-2 default-cdr
                           quote-lemma-for-all-dargp-less-than-gen-alt)))

(local (in-theory (disable symbol-alistp))) ;don't induct

;; (thm
;;  (implies (and (pseudo-termp term)
;;                (posp n)
;;                (not (equal 'quote (nth 0 term))))
;;           (pseudo-termp (nth n term)))
;;  :hints (("Goal" :in-theory (e/d (pseudo-termp nth) (NTH-OF-CDR)))))

;dup, needed?
(defthm dargp-of-lookup-equal-when-all-dargp-of-strip-cdrs
  (implies (all-dargp (strip-cdrs alist))
           (iff (dargp (lookup-equal var alist))
                (assoc-equal var alist)))
  :hints (("Goal" :induct t
           :in-theory (e/d (all-dargp lookup-equal strip-cdrs)
                           (myquotep)))))

;;zz

(defthm-flag-merge-term-into-dag-array
  (defthm merge-term-into-dag-array-return-type
    (implies (and (pseudo-termp term)
                  (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (symbol-alistp var-replacement-alist)
                  (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                  ;;no errors:
                  (not (mv-nth 0 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
             (and (dargp-less-than (mv-nth 1 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))
                                              (mv-nth 3 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                  ;could prove later, as a corollary?
                  (dargp (mv-nth 1 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))

                  (wf-dagp dag-array-name
                           (mv-nth 2 (merge-term-into-dag-array
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           (mv-nth 3 (merge-term-into-dag-array
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           dag-parent-array-name
                           (mv-nth 4 (merge-term-into-dag-array
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           (mv-nth 5 (merge-term-into-dag-array
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           (mv-nth 6 (merge-term-into-dag-array
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist)))
                  (<= dag-len
                      (mv-nth 3 (merge-term-into-dag-array
                                 term
                                 var-replacement-alist
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                 interpreted-function-alist)))))
    :flag merge-term-into-dag-array)
  (defthm merge-terms-into-dag-array-return-type
    (implies (and (pseudo-term-listp terms)
                  (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (symbol-alistp var-replacement-alist)
                  (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                  ;;no errors:
                  (not (mv-nth 0 (merge-terms-into-dag-array terms var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
             (and (true-listp (mv-nth 1 (merge-terms-into-dag-array
                                         terms
                                         var-replacement-alist
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                         interpreted-function-alist)))
                  (equal (len (mv-nth 1 (merge-terms-into-dag-array
                                         terms
                                         var-replacement-alist
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                         interpreted-function-alist)))
                         (len terms))
                  (all-dargp (mv-nth 1 (merge-terms-into-dag-array
                                                   terms
                                                   var-replacement-alist
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                   interpreted-function-alist)))
                  (all-dargp-less-than (mv-nth 1 (merge-terms-into-dag-array
                                                             terms
                                                             var-replacement-alist
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                             interpreted-function-alist))
                                                  (mv-nth 3 (merge-terms-into-dag-array
                                                             terms
                                                             var-replacement-alist
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                             interpreted-function-alist)))
                  (wf-dagp dag-array-name
                           (mv-nth 2 (merge-terms-into-dag-array
                                                terms
                                                var-replacement-alist
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                interpreted-function-alist))
                           (mv-nth 3 (merge-terms-into-dag-array
                                                 terms
                                                 var-replacement-alist
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                 interpreted-function-alist))
                           dag-parent-array-name
                           (mv-nth 4 (merge-terms-into-dag-array
                                                 terms
                                                 var-replacement-alist
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                 interpreted-function-alist))
                           (mv-nth 5 (merge-terms-into-dag-array
                                                  terms
                                                  var-replacement-alist
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                  interpreted-function-alist))
                           (mv-nth 6 (merge-terms-into-dag-array
                                                  terms
                                                  var-replacement-alist
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                  interpreted-function-alist)))

                  (<= dag-len
                      (mv-nth 3 (merge-terms-into-dag-array
                                 terms
                                 var-replacement-alist
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                 interpreted-function-alist)))))
    :flag merge-terms-into-dag-array)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-term-into-dag-array merge-terms-into-dag-array car-becomes-nth-of-0 ;wf-dagp
                                                      )
                           (natp dargp pseudo-term-listp pseudo-termp)))))

;; todo: def-dag-builder-theorems has trouble with this
(DEFTHM BOUND-ON-MV-NTH-3-OF-MERGE-TERM-INTO-DAG-ARRAY-3
  (IMPLIES
   (AND
    (WF-DAGP DAG-ARRAY-NAME DAG-ARRAY DAG-LEN
             DAG-PARENT-ARRAY-NAME DAG-PARENT-ARRAY
             DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST)
    ;; ;; needed?:
    ;; (not (MV-NTH 0
    ;;              (MERGE-TERM-INTO-DAG-ARRAY TERM VAR-REPLACEMENT-ALIST
    ;;                                         DAG-ARRAY DAG-LEN DAG-PARENT-ARRAY
    ;;                                         DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST
    ;;                                         DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
    ;;                                         INTERPRETED-FUNCTION-ALIST)))
    (PSEUDO-TERMP TERM)
    (SYMBOL-ALISTP VAR-REPLACEMENT-ALIST)
    (ALL-DARGP-LESS-THAN (STRIP-CDRS VAR-REPLACEMENT-ALIST)
                                    DAG-LEN)
    (INTERPRETED-FUNCTION-ALISTP INTERPRETED-FUNCTION-ALIST)
    (NATP DAG-LEN))
   (<=
    DAG-LEN
    (MV-NTH
     3
     (MERGE-TERM-INTO-DAG-ARRAY TERM VAR-REPLACEMENT-ALIST
                                DAG-ARRAY DAG-LEN DAG-PARENT-ARRAY
                                DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST
                                DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
                                INTERPRETED-FUNCTION-ALIST))))
  :RULE-CLASSES
  ((:LINEAR
    :TRIGGER-TERMS
    ((MV-NTH
      3
      (MERGE-TERM-INTO-DAG-ARRAY TERM VAR-REPLACEMENT-ALIST
                                 DAG-ARRAY DAG-LEN DAG-PARENT-ARRAY
                                 DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST
                                 DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
                                 INTERPRETED-FUNCTION-ALIST)))))
  :HINTS (("Goal" :in-theory (enable <=-of-mv-nth-3-of-merge-term-into-dag-array-2))))

(def-dag-builder-theorems
  (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)
  (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist) ;should I have to give this?
         (pseudo-termp term)
         (symbol-alistp var-replacement-alist)
         (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
         (interpreted-function-alistp interpreted-function-alist))
  :recursivep nil
  :hyps-everywhere t
  :hints (("Goal" ;:expand (merge-tree-into-dag-array tree var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)
;           :in-theory (disable wf-dagp)
           :use (:instance merge-tree-into-dag-array-return-type)
           ))
  :dag-parent-array-name dag-parent-array-name
  :dag-array-name dag-array-name)

; drop some of these?:

(defthm merge-term-into-dag-array-return-type-corollary
  (implies (and (<= bound dag-len)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
           (<= bound
               (mv-nth 3 (merge-term-into-dag-array
                          term
                          var-replacement-alist
                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                          interpreted-function-alist))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-return-type)
           :in-theory (e/d () (merge-term-into-dag-array-return-type)))))

(defthm merge-term-into-dag-array-return-type-corollary2
  (implies (and (<= (mv-nth 3 (merge-term-into-dag-array
                               term
                               var-replacement-alist
                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                               interpreted-function-alist)) bound)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)

                (symbol-alistp var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
           (DARGP-LESS-THAN
            (mv-nth 1 (merge-term-into-dag-array
                       term
                       var-replacement-alist
                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                       interpreted-function-alist))
            bound))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-return-type)
           :in-theory (e/d (wf-dagp) (merge-term-into-dag-array-return-type)))))

(defthm merge-term-into-dag-array-return-type-corollary3
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                (not (consp (mv-nth 1 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
                )
           (< (mv-nth 1 (merge-term-into-dag-array
                         term
                         var-replacement-alist
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                         interpreted-function-alist))
              (mv-nth 3 (merge-term-into-dag-array
                         term
                         var-replacement-alist
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                         interpreted-function-alist))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-return-type)
           :in-theory (e/d (wf-dagp) (merge-term-into-dag-array-return-type
                               MERGE-TERM-INTO-DAG-ARRAY-RETURN-TYPE-COROLLARY2
                               MERGE-TERM-INTO-DAG-ARRAY-RETURN-TYPE-COROLLARY)))))

(defthm merge-term-into-dag-array-return-type-corollary4
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)

                (symbol-alistp var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                (not (consp (mv-nth 1 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
                )
           (natp (mv-nth 1 (merge-term-into-dag-array
                            term
                            var-replacement-alist
                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                            interpreted-function-alist))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-return-type)
           :in-theory (e/d (wf-dagp) (merge-term-into-dag-array-return-type)))))

(defthmd not-equal-of-len-and-1-when-dargp
  (implies (dargp x)
           (not (equal (len x) 1)))
  :hints (("Goal" :in-theory (enable dargp myquotep))))

(verify-guards merge-term-into-dag-array
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-term-into-dag-array merge-terms-into-dag-array car-becomes-nth-of-0
                                                      not-equal-of-len-and-1-when-dargp
                                                      call-of-dag-val-with-axe-evaluator-with-inlineable-dagp
                                                      <-of-nth-when-all-dargp-less-than
                                                      true-listp-of-nth-1-of-nth-0-when-axe-treep
                                                      ;wf-dagp
                                                      ;wf-dagp-expander
                                                      )
                           (natp dargp pseudo-term-listp pseudo-termp)))))

;; Returns (mv erp dag)
(defun dag-or-term-to-dag (item wrld)
  (declare (xargs :mode :program)) ;; because this calls translate-term
  (if (eq nil item) ; we assume nil is the constant nil, not an empty DAG
      (mv (erp-nil) *nil*)
    (if (weak-dagp item)
        (mv (erp-nil) item) ;already a DAG
      ;; translate the given form to obtain a pseudo-term and then make that into a DAG:
      (dagify-term2 (translate-term item 'dag-or-term-to-dag wrld)))))


;; does not translate the term
;todo: reduce to take wlrd instead of state?
(defun dag-or-term-to-term (item state)
  (declare (xargs :stobjs state))
  (if (eq nil item) ; we assume nil is the constant nil, not an empty DAG
      *nil*
    (if (weak-dagp item)
        ;; we embed a DAG in a call to dag-val-with-axe-evaluator, to avoid
        ;; explosion in the term size:
        `(dag-val-with-axe-evaluator ',item
                                     ,(make-acons-nest (dag-vars item))
                                     ',(make-interpreted-function-alist (get-non-built-in-supporting-fns-list (dag-fns item) (w state)) (w state))
                                     '0 ;array depth (not very important)
                                     )
      item)))
