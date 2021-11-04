; Simplifying a DAG using contextual information
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

(include-book "contexts")
(include-book "dags")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))

(local
 (defthm <-of-if-arg2
   (equal (< x (if test y z))
          (if test
              (< x y)
            (< x z)))))

(local (in-theory (enable <-OF-IF-ARG1)))
(local (in-theory (disable len)))

(defthm not-<-of-caar-and-caadr-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (not (< (CAR (CAR DAG))
                   (CAR (CAR (CDR DAG))))))
  :hints (("Goal" :in-theory (enable pseudo-dagp PSEUDO-DAGP-AUX))))

(defthm not-<-of-caar-and-caadr-when-pseudo-dagp-aux
  (implies (pseudo-dagp-aux dag current-nodenum)
           (not (< (CAR (CAR DAG))
                   (CAR (CAR (CDR DAG))))))
  :hints (("Goal" :in-theory (enable PSEUDO-DAGP-AUX))))

(defthm pseudo-dagp-forward-to-natp-of-caadr
  (implies (and (pseudo-dagp dag)
                (consp (cdr dag)))
           (natp (car (car (cdr dag)))))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand (PSEUDO-DAGP-AUX DAG (CAR (CAR DAG)))
           :in-theory (enable pseudo-dagp pseudo-dagp-aux
                              ))))

(defthm pseudo-dagp-aux-forward-to-natp-of-caadr
  (implies (and (pseudo-dagp-aux dag current-nodenum)
                (integerp current-nodenum)
                (consp (cdr dag)))
           (natp (car (car (cdr dag)))))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand ((pseudo-dagp-aux dag current-nodenum)
                           (PSEUDO-DAGP-AUX (CDR DAG)
                                            (+ -1 (CAR (CAR DAG)))))
           :in-theory (enable ;pseudo-dagp-aux
                       ))))

(defthm pseudo-dagp-of-cdr
  (implies (pseudo-dagp dag)
           (equal (pseudo-dagp (cdr dag))
                  (consp (cdr dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux))))

;; Takes an entry of the form: (nodenum . expr) and returns such an entry.
;for ITEs and boolean exprs, puts in constants for arguments known from context
;fixme should we look up the nodenum itself in the context? probably not?
;could just do it for all operators?  but only in positions where iff is the equivalence relation (well, if we know it's nil we can always put in nil...)
;we could write a general purpose version of this that takes the congruence table (indicates which args of which functions can be rewritten using iff)
(defund concretize-entry-with-context (entry context-array)
  (declare (xargs :guard (and (consp entry) ; todo: need to check arities
                              (natp (car entry))
                              (dag-exprp0 (cdr entry))
                              (context-arrayp 'context-array context-array (+ 1 (car entry))))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))))
  (let ((expr (cdr entry)))
    (if (variablep expr)
        entry
      (let ((fn (ffn-symb expr)))
        (if (or (eq 'myif fn)
                (eq 'boolif fn)
                (eq 'if fn) ;shouldn't happen if IF is getting turned into MYIF
                )
            (if (not (= 3 (len (dargs expr))))
                entry
              (let* ((nodenum (car entry))
                     (context (aref1 'context-array context-array nodenum))
                     (test (darg1 expr))
                     (test-result (look-up-in-context test context))) ;ffixme could look up the other args of a boolif..
                (if (eq t test-result)
                    (cons nodenum `(,fn ,*t* ,(darg2 expr) ,(darg3 expr)))
                  (if (eq nil test-result)
                      (cons nodenum `(,fn ,*nil* ,(darg2 expr) ,(darg3 expr)))
                    entry))))
          (if (eq 'bvif fn) ;;(bvif size test x y)
              (if (not (= 4 (len (dargs expr))))
                  entry
                (let* ((nodenum (car entry))
                       (context (aref1 'context-array context-array nodenum))
                       (test (darg2 expr))
                       (test-result (look-up-in-context test context)))
                  (if (eq t test-result)
                      (cons nodenum `(bvif ,(darg1 expr) ,*t* ,(darg3 expr) ,(darg4 expr)))
                    (if (eq nil test-result)
                        (cons nodenum `(bvif ,(darg1 expr) ,*nil* ,(darg3 expr) ,(darg4 expr)))
                      entry))))
            (if (or (eq 'booland fn) ;handle bool-xor?  bool-fix$inline?
                    (eq 'boolor fn))
                (if (not (= 2 (len (dargs expr))))
                    entry
                  (let* ((nodenum (car entry))
                         (context (aref1 'context-array context-array nodenum))
                         (arg1 (darg1 expr))
                         (arg2 (darg2 expr))
                         (arg1-result (look-up-in-context arg1 context))
                         (arg2-result (look-up-in-context arg2 context)))
                    (if (and (eq :unknown arg1-result)
                             (eq :unknown arg2-result))
                        ;; the usual case: don't bother to recons entry;
                        entry
                      (cons nodenum `(,fn
                                      ,(if (eq :unknown arg1-result) arg1 (if arg1-result *t* *nil*))
                                      ,(if (eq :unknown arg2-result) arg2 (if arg2-result *t* *nil*)))))))
              entry)))))))

;returns (mv changep rev-new-dag-lst)
(defund concretize-entries-with-contexts (dag-lst context-array acc changep)
  (declare (xargs :guard (and (weak-dagp-aux dag-lst)
                              (if (consp dag-lst)
                                  (pseudo-dagp-aux dag-lst (caar dag-lst))
                                t)
                              (context-arrayp 'context-array context-array (+ 1 (top-nodenum dag-lst)))
                              (true-listp acc)
                              (booleanp changep))
                  :guard-hints (("Goal" :cases ((consp (cdr dag-lst)))
                                 :expand ((pseudo-dagp-aux dag-lst (car (car dag-lst))))
                                 :do-not '(generalize eliminate-destructors)))))
  (if (endp dag-lst)
      (mv changep acc) ;if caller uses acc, it should reverse acc
    (let* ((entry (first dag-lst))
           (concretized-entry (concretize-entry-with-context entry context-array))) ;have concretize-entry-with-context return a changep flag?
      (concretize-entries-with-contexts (rest dag-lst)
                                        context-array
                                        (cons concretized-entry acc)
                                        (if (not (equal entry concretized-entry)) ;would be faster to check changep first but we want to print
                                            (prog2$ (cw "concretizing ~x0 to ~x1~%" entry concretized-entry)
                                                    t)
                                          changep)))))

(defthm true-listp-of-mv-nth-1-of-concretize-entries-with-contexts
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (concretize-entries-with-contexts dag-lst context-array acc changep))))
  :hints (("Goal" :in-theory (enable concretize-entries-with-contexts))))


;returns a new dag-lst equivalent to dag-lst (but internal nodes are not necessarily equivalent!)
;computes the context of each node and tries to use that to simplify the node (e.g., if c is in the context of (if c x y) then it becomes (if t x y)
;;one should call the rewriter after this to simplify away things like (if t x y) -> x
;;why not do that here?  may want to use some rules when we do it?
;; this could report whether any changes were made?
;smashes 'dag-parent-array and 'context-array
;fixme does this do anything that rewriting with internal contexts can't?
(defund concretize-using-contexts (dag-lst)
  (declare (xargs :guard (or (myquotep dag-lst)
                             (and (pseudo-dagp dag-lst)
                                  (< (LEN DAG-LST) 2147483647)))
                  :guard-hints (("Goal" :in-theory (enable PSEUDO-DAGP)))
                  ))
  (prog2$ (cw "(Concretizing using contexts:~%")
          (if (quotep dag-lst)
              (prog2$ (cw ")~%")
                      dag-lst)
            (let* ((dag-len (len dag-lst))
                   (dag-array (make-into-array 'dag-array dag-lst))
                   (context-array (make-full-context-array 'dag-array dag-array dag-len)))
              (mv-let (changep rev-new-dag-lst)
                      (concretize-entries-with-contexts dag-lst context-array nil nil)
                      (let ((dag-lst (if changep
                                         (reverse rev-new-dag-lst)
                                       dag-lst)))
                        (prog2$ (cw ")~%")
                                dag-lst)))))))
