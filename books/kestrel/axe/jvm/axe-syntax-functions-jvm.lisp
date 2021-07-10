; JVM-related syntactic tests
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book defines JVM-related functions used in axe-syntaxp and axe-bind-free rules.

(include-book "kestrel/jvm/jvm" :dir :system) ; for jvm::pc
;(include-book "kestrel/axe/dags" :dir :system) ;for dargs
;(include-book "kestrel/axe/dag-arrays" :dir :system) ;for pseudo-dag-arrayp
(include-book "kestrel/axe/dag-array-printing" :dir :system)
(include-book "kestrel/axe/axe-syntax-functions" :dir :system) ; for count-myif-branches
(include-book "kestrel/utilities/erp" :dir :system)
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(in-theory (disable member-equal-becomes-memberp)) ;causes problems

;call-stack is now either a nodenum or a quotep
;now pops count as -1 (because terms are often represented as a push of a new frame onto a pop of the old stack)
(defund count-pushes-above-base (call-stack base-stack dag-array)
  (declare (xargs :guard (and (or (myquotep call-stack)
                                  (and (natp call-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 call-stack))))
                              (or (myquotep base-stack)
                                  (and (natp base-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack)))))
                  :measure (if (consp call-stack) ;check for quotep
                               0
                             (+ 1 (nfix call-stack)))
                  :verify-guards nil ;done below
                  ))
  (if (equal call-stack base-stack); (dag-exprs-equal call-stack base-stack dag-array 1000000000) ;gross bound  ;todo: why not just compare the nodenums?
      0
    (if (or (consp call-stack) ;check for quotep ;todo: think about this (what if call-stack and base-stack are both quoteps?)
            (not (mbt (integerp call-stack))))
        nil
      (let ((call-stack-expr (aref1 'dag-array dag-array call-stack)))
        (if (and (consp call-stack-expr)
                 (eq (car call-stack-expr) 'jvm::push-frame)
                 (= 2 (len (dargs call-stack-expr)))
                 ;; for termination:
                 (mbt (or (quotep (darg2 call-stack-expr))
                          (and (natp (darg2 call-stack-expr))
                               (< (darg2 call-stack-expr) call-stack)))))
            (let ((rec (count-pushes-above-base (darg2 call-stack-expr) base-stack dag-array)))
              (if rec
                  (+ 1 rec)
                nil))
          (if (and (consp call-stack-expr)
                   (eq (car call-stack-expr) 'jvm::pop-frame) ;can this happen?
                   (= 1 (len (dargs call-stack-expr)))
                   ;; for termination:
                   (mbt (or (quotep (darg1 call-stack-expr))
                            (and (natp (darg1 call-stack-expr))
                                 (< (darg1 call-stack-expr) call-stack)))))
              (let ((rec (count-pushes-above-base (darg1 call-stack-expr) base-stack dag-array)))
                (if rec
                    (+ -1 rec)
                  nil))
            (progn$ (er hard? 'count-pushes-above-base "Unrecognized call stack: ~x0 in dag: ~x1.~%" call-stack dag-array)
                    nil)))))))

(defthm acl2-numberp-of-count-pushes-above-base
  (implies (count-pushes-above-base call-stack base-stack dag-array)
           (acl2-numberp (count-pushes-above-base call-stack base-stack dag-array))))

(verify-guards count-pushes-above-base
  :hints (("Goal" :in-theory (enable car-becomes-nth-of-0))))

;tag these with -dag or -axe?
;returns (mv stack-height pc) where both are integers- need to turn the stack height into some expression? - or an mv with at least one nil for failure
;bozo this only works if the make-state looks just so - add error checking?
;handle more errors?

;move
;not a great linear rule due to the free var
(defthm maxelem-of-keep-atoms-bound
  (implies (and (all-dargp-less-than items n)
                (natp n)
                (consp (keep-atoms items)) ;there must be at least one atom
                )
           (< (maxelem (keep-atoms items)) n))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable all-dargp-less-than))))

;;move
;;not a great linear rule due to the free var
(defthm <-of-maxelem-of-keep-atoms-of-dargs-when-bounded-dag-exprp
  (implies (and (bounded-dag-exprp n expr)
                (consp expr)
                (natp n)
                (consp (dargs expr))
                (not (eq 'quote (car expr)))
                (consp (keep-atoms (dargs expr))))
           (< (maxelem (keep-atoms (dargs expr)))
              n))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

;move
(defthm <-of-maxelem-of-keep-atoms-of-dargs-when-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array n)
                (consp (aref1 dag-array-name dag-array n))
                (not (equal 'quote (car (aref1 dag-array-name dag-array n))))
                (consp (keep-atoms (dargs (aref1 dag-array-name dag-array n))))
                (natp n))
           (< (maxelem (keep-atoms (dargs (aref1 dag-array-name dag-array n))))
              n))
  :rule-classes (:rewrite :linear))

;; Returns (mv erp pc) where PC is the PC (if it is a call to make-frame).
(defund get-pc-from-frame (frame dag-array)
  (declare (xargs :guard (or (myquotep frame)
                             (and (natp frame)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 frame))))))
  (if (consp frame) ;check for quotep
      (if (jvm::framep (unquote frame))
          (mv (erp-nil) (jvm::pc (unquote frame)))
        (prog2$ (er hard? 'get-pc-from-frame "Unexpected constant frame")
                (mv (erp-t) nil)))
    (let ((expr (aref1 'dag-array dag-array frame)))
      (if (and (call-of 'jvm::make-frame expr)
               ;;(true-listp expr)
               (= 6 (len (dargs expr)))
               (myquotep (darg1 expr))
               (natp (unquote (darg1 expr))))
          (mv (erp-nil) (unquote (darg1 expr))) ;todo: what if the pc is not a quoted constant?
        (progn$ (cw "Error DAG:~%")
                (if (or (quotep expr)
                        (not (consp expr)))
                    (cw "~x0" expr)
                  (if (not (keep-atoms (dargs expr)))
                      (cw "All args are constants so not printing a DAG.~%")
                    (print-dag-only-supporters-of-nodes 'dag-array dag-array (keep-atoms (dargs expr)))))
                (er hard? 'get-pc-from-frame "Unexpected frame: ~x0.  See DAG just above." expr)
                (mv (erp-t) nil))))))

(defthm get-stack-height-and-pc-from-frame-type
  (implies (not (mv-nth 0 (get-pc-from-frame call-stack dag-array)))
           (natp (mv-nth 1 (get-pc-from-frame call-stack dag-array))))
  :hints (("Goal" :in-theory (enable get-pc-from-frame))))

;; Returns (mv erp stack-height-difference pc) where stack-height-difference is the number of frames about base-stack.  If it is 0, the PC is irrelevant.
(defund get-stack-height-and-pc-from-call-stack (call-stack base-stack dag-array)
  (declare (xargs :guard (and (or (myquotep call-stack)
                                  (and (natp call-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 call-stack))))
                              (or (myquotep base-stack)
                                  (and (natp base-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack)))))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0 count-pushes-above-base)))
                  ))
  (let ((pushes (count-pushes-above-base call-stack base-stack dag-array)))
    (if (not (natp pushes))
        (prog2$ (er hard? 'get-stack-height-and-pc-from-call-stack "Failed to find base-stack.")
                (mv (erp-t) nil nil))
      (if (= 0 pushes)
          (progn$ ;(er hard? 'get-stack-height-and-pc-from-call-stack "Base-stack encountered with no dummy frame above it.") ;; This can happen legitimately in the compositional unrolling lifter.
           (mv (erp-nil) 0 0)) ;return a PC of 0 here for now.  we need to avoid trying to get the PC of the frame on the top of base-stack (this means the run is done)
        (if (consp call-stack) ;checks for quotep
            (mv (erp-t) nil nil) ;fail! (should we allow a constant call-stack?)
          ;; get the PC of the top frame:
          (let ((expr (aref1 'dag-array dag-array call-stack)))
            (if (not (and (consp expr)
                          (eq 'jvm::push-frame (ffn-symb expr))
                          (= 2 (len (dargs expr)))))
                ;; there must be at least one frame pushed on:
                (prog2$ (er hard? 'get-stack-height-and-pc-from-call-stack "Unexpected expression: ~x0." expr)
                        (mv (erp-t) nil nil))
              (mv-let (erp pc)
                (get-pc-from-frame (darg1 expr) dag-array)
                (if erp
                    (mv erp nil nil)
                  (mv (erp-nil) pushes pc))))))))))

(local (in-theory (disable natp)))

(defthm get-stack-height-and-pc-from-call-stack-type
  (implies (not (mv-nth 0 (get-stack-height-and-pc-from-call-stack call-stack base-stack dag-array)))
           (natp (mv-nth 1 (get-stack-height-and-pc-from-call-stack call-stack base-stack dag-array))))
  :hints (("Goal" :in-theory (enable get-stack-height-and-pc-from-call-stack))))

(defthm get-stack-height-and-pc-from-call-stack-type-2
  (implies (not (mv-nth 0 (get-stack-height-and-pc-from-call-stack call-stack base-stack dag-array)))
           (natp (mv-nth 2 (get-stack-height-and-pc-from-call-stack call-stack base-stack dag-array))))
  :hints (("Goal" :in-theory (enable get-stack-height-and-pc-from-call-stack))))

;; ;; Returns (mv stack-height-difference pc) where if either is nil, there is a failure.
;; (defund get-stack-height-and-pc-from-thread (thread base-stack dag-array)
;;   (declare (xargs :guard (and (or (myquotep thread)
;;                                   (and (natp thread)
;;                                        (pseudo-dag-arrayp 'dag-array dag-array (+ 1 thread))))
;;                               (or (myquotep base-stack)
;;                                   (and (natp base-stack)
;;                                        (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack)))))
;;                   :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))))
;;   (if (consp thread) ;checks for quotep
;;       (mv nil nil)   ;fail (should we allow a constant thread?)
;;     (let ((expr (aref1 'dag-array dag-array thread)))
;;       (if (not (and (consp expr)
;;                     (eq 'jvm::make-thread (ffn-symb expr))
;;                     (= 1 (len (dargs expr)))))
;;           (mv (er hard? 'get-stack-height-and-pc-from-thread "Unexpected term.")
;;               nil)
;;         (get-stack-height-and-pc-from-call-stack (darg1 expr) base-stack dag-array)))))

;; Returns (mv erp stack-height-difference pc).
(defund get-stack-height-and-pc-from-thread-table (thread-table base-stack dag-array)
  (declare (xargs :guard (and (or (myquotep thread-table)
                                  (and (natp thread-table)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 thread-table))))
                              (or (myquotep base-stack)
                                  (and (natp base-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack)))))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0 natp)))))
  (if (consp thread-table) ;checks for quotep
      (prog2$ (er hard? 'get-stack-height-and-pc-from-thread-table "Unsupported constant thread-table: ~x0." thread-table)
              (mv (erp-t) nil nil))         ;fail (should we allow a constant thread-table?)
    (let ((expr (aref1 'dag-array dag-array thread-table)))
      (if (not (and (consp expr)
                    (eq 'jvm::bind (ffn-symb expr))
                    (= 3 (len (dargs expr))))) ;a call to bind for thread 0 (TODO: check the thread ID!)
          (prog2$ (er hard? 'get-stack-height-and-pc-from-thread-table "Unexpected term.")
                  (mv (erp-t) nil nil))
        (get-stack-height-and-pc-from-call-stack (darg2 expr) base-stack dag-array)))))

(defthm get-stack-height-and-pc-from-thread-table-type
  (implies (not (mv-nth 0 (get-stack-height-and-pc-from-thread-table thread-table base-stack dag-array)))
           (natp (mv-nth 1 (get-stack-height-and-pc-from-thread-table thread-table base-stack dag-array))))
  :hints (("Goal" :in-theory (enable get-stack-height-and-pc-from-thread-table))))

(defthm get-stack-height-and-pc-from-thread-table-type-2
  (implies (not (mv-nth 0 (get-stack-height-and-pc-from-thread-table thread-table base-stack dag-array)))
           (natp (mv-nth 2 (get-stack-height-and-pc-from-thread-table thread-table base-stack dag-array))))
  :hints (("Goal" :in-theory (enable get-stack-height-and-pc-from-thread-table))))

;; Returns (mv erp stack-height-difference pc)
(defund get-stack-height-and-pc-from-make-state (make-state base-stack dag-array)
  (declare (xargs :guard (and (and (natp make-state)
                                   (pseudo-dag-arrayp 'dag-array dag-array (+ 1 make-state)))
                              (or (myquotep base-stack)
                                  (and (natp base-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack)))))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0 natp)))))
  (let ((expr (aref1 'dag-array dag-array make-state)))
    (if (not (and (consp expr)
                  (eq 'jvm::make-state (ffn-symb expr))
                  (= 8 (len (dargs expr)))))
        (prog2$ (er hard? 'get-stack-height-and-pc-from-make-state "Unexpected state term.")
                (mv (erp-t) nil nil))
      (get-stack-height-and-pc-from-thread-table (darg1 expr) base-stack dag-array))))

(defthm get-stack-height-and-pc-from-make-state-type
  (implies (not (mv-nth 0 (get-stack-height-and-pc-from-make-state nest base-stack dag-array)))
           (natp (mv-nth 1 (get-stack-height-and-pc-from-make-state nest base-stack dag-array))))
  :hints (("Goal" :in-theory (enable get-stack-height-and-pc-from-make-state))))

(defthm get-stack-height-and-pc-from-make-state-type-2
  (implies (not (mv-nth 0 (get-stack-height-and-pc-from-make-state nest base-stack dag-array)))
           (natp (mv-nth 2 (get-stack-height-and-pc-from-make-state nest base-stack dag-array))))
  :hints (("Goal" :in-theory (enable get-stack-height-and-pc-from-make-state))))

(defund strip-steps (nest dag-array)
  (declare (xargs :guard (or (myquotep nest)
                             (and (natp nest)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
                  :guard-hints (("Goal" :in-theory (enable CAR-BECOMES-NTH-OF-0 natp)))
                  :measure (if (consp nest) ;check for quotep
                               0
                             (+ 1 (nfix nest)))))
  (if (or (consp nest) ;test for a quotep
          (not (mbt (integerp nest))))
      nest
    (let ((expr (aref1 'dag-array dag-array nest)))
      (if (and (call-of 'step-state-with-pc-and-call-stack-height expr)
               (= 3 (len (dargs expr)))
               ;; for termination:
               (mbt (or (myquotep (darg3 expr))
                        (and (natp (darg3 expr))
                             (< (darg3 expr) nest)))))
          (strip-steps (darg3 expr) dag-array)
        (if (and (call-of 'step-state-with-pc-designator-stack expr)
                 (= 2 (len (dargs expr)))
                 ;; for termination:
                 (mbt (or (myquotep (darg2 expr))
                          (and (natp (darg2 expr))
                               (< (darg2 expr) nest)))))
            (strip-steps (darg2 expr) dag-array)
          nest)))))

(defthm natp-of-strip-steps
  (implies (and (or (myquotep nest)
                    (and (natp nest)
                         (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
                (not (consp (strip-steps nest dag-array))))
           (natp (strip-steps nest dag-array)))
  :hints (("Goal" :in-theory (enable strip-steps))))

(defthm integerp-of-strip-steps
  (implies (and (or (myquotep nest)
                    (and (natp nest)
                         (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
                (not (consp (strip-steps nest dag-array))))
           (integerp (strip-steps nest dag-array)))
  :hints (("Goal" :in-theory (enable strip-steps))))

(defthm <=-of-strip-steps-and-0
  (implies (and (or (myquotep nest)
                    (and (natp nest)
                         (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
                (not (consp (strip-steps nest dag-array))))
           (<= 0 (strip-steps nest dag-array)))
  :hints (("Goal" :in-theory (enable strip-steps))))

(defthm <-of-strip-steps
  (Implies (and (or (myquotep nest)
                    (and (natp nest)
                         (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
                (not (consp (STRIP-STEPS nest DAG-ARRAY))))
           (< (STRIP-STEPS nest DAG-ARRAY)
              (alen1 'DAG-ARRAY DAG-ARRAY)))
  :hints (("Goal" :in-theory (enable STRIP-STEPS))))

;;NEST is usually a nodenum in DAG-ARRAY that represents a MYIF nest with
;;make-states at the leaves, but the leaves may also be calls of the exception
;;wrapper or other things we don't want to execute (such as code to trigger an
;;assert); such leaves may be pruned later as unreachable.  Returns (mv status
;;stack-height pc) where status is :ready, :finished (all leaves of the MYIF
;;nest are done executing or represent something we don't want to execute),
;;:step-present (indicating that perhaps we hit a step limit), or :error .  If
;;status is :ready, then PC and STACK-HEIGHT are integers.  Normally, MYIf
;;branches will be eventually be merged, leading to a term that is not a MYIF.
;;TODO: Consider adding support for regular old IF in addition to myif.
(defund get-stack-height-and-pc-to-step-from-myif-nest-helper (nest base-stack dag-array)
  (declare (xargs :guard (and (or (myquotep nest)
                                  (and (natp nest)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
                              (or (myquotep base-stack)
                                  (and (natp base-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack)))))

                  :verify-guards nil ;done below
                  :measure (if (quotep nest)
                               0
                             (+ 1 (nfix nest)))))
  (if (consp nest) ;check for quotep
      (prog2$ (and (not (equal nest '':irrelevant)) ;todo: why does this occur?  remove this case once we prevent :irrelevant from appearing
                   (er hard? 'get-stack-height-and-pc-to-step-from-myif-nest-helper "NOTE: Unexpected (constant) state term: ~x0.~%" nest))
              (mv :error nil nil))
    (if (not (mbt (integerp nest))) ;for termination
        (mv :error nil nil)         ; can't happen
      (let ((expr (aref1 'dag-array dag-array nest)))
        (if (not (consp expr))
            (prog2$ (er hard? 'get-stack-height-and-pc-to-step-from-myif-nest-helper "Unexpected state term: ~x0.  Got a variable, but expected a make-state.~%" nest)
                    (mv :error nil nil))
          (let ((fn (ffn-symb expr)))
            (if (eq 'jvm::make-state fn)
                (mv-let (erp stack-height pc)
                  (get-stack-height-and-pc-from-make-state nest base-stack dag-array)
                  (if erp
                      (mv :error nil nil)
                    (if (= stack-height 0)
                        (mv :finished nil nil)
                      (mv :ready stack-height pc))))
              (if (and (eq 'myif fn)
                       (= 3 (len (dargs expr))))
                  (let ((then-branch (darg2 expr))
                        (else-branch (darg3 expr)))
                    (if (not (mbt (and (or (quotep then-branch) ;for termination
                                           (and (natp then-branch)
                                                (< then-branch nest)))
                                       (or (quotep else-branch)
                                           (and (natp else-branch)
                                                (< else-branch nest))))))
                        (mv :error nil nil) ;; can't happen
                      (b* (((mv left-status left-sh left-pc)
                            (get-stack-height-and-pc-to-step-from-myif-nest-helper then-branch base-stack dag-array))
                           ((when (eq :error left-status)) (mv :error nil nil))
                           ((mv right-status right-sh right-pc)
                            (get-stack-height-and-pc-to-step-from-myif-nest-helper else-branch base-stack dag-array))
                           ((when (eq :error right-status)) (mv :error nil nil)))
                        (if (eq :ready left-status)
                            (if (eq :ready right-status)
                                ;; First compare the stack heights (preferring to
                                ;; step the state with the taller stack), then
                                ;; compare the PCs (preferring to step the state with
                                ;; the smaller PC):
                                (if (< left-sh right-sh)
                                    (mv :ready right-sh right-pc)
                                  (if (< right-sh left-sh)
                                      (mv :ready left-sh left-pc)
                                    (if (< left-pc right-pc) ;BOZO do something more sophisticated than comparing pcs?
                                        (mv :ready left-sh left-pc)
                                      (mv :ready right-sh right-pc))))
                              ;; Only left is ready:
                              (mv :ready left-sh left-pc))
                          ;; Left is not ready:
                          (if (eq :ready right-status)
                              ;; Only right is ready:
                              (mv :ready right-sh right-pc)
                            ;; Neither is ready:
                            (if (or (eq :step-present left-status) (eq :step-present right-status))
                                (mv :step-present nil nil)
                              (mv :finished nil nil)))))))
                (if (eq 'jvm::obtain-and-throw-exception fn)
                    (progn$ (cw "(Exception branch detected (will try to prune it later).)~%")
                            (mv :finished nil nil))
                  (if (eq 'jvm::error-state fn)
                      (progn$ (cw "(Error branch detected (may try to prune it later).)~%")
                              (mv :finished nil nil))
                  (if (and (eq 'jvm::execute-new fn)
                           (= 3 (len (dargs expr)))
                           (equal (darg1 expr) ''(:NEW "java.lang.AssertionError")))
                      (progn$ (cw "(Assertion branch detected (will try to prune it later).)~%")
                              (mv :finished nil nil))
                    (if (or (and (eq fn 'step-state-with-pc-and-call-stack-height)
                                 (= 3 (len (dargs expr))))
                            (and (eq fn 'step-state-with-pc-designator-stack)
                                 (= 2 (len (dargs expr)))))
                        ;; Need to determine whether the step functions are stacked up around a make-state or an error state:
                        (let ((stripped-state (strip-steps (if (eq fn 'step-state-with-pc-and-call-stack-height)
                                                               (darg3 expr)
                                                             (darg2 expr))
                                                           dag-array)))
                          (if (consp stripped-state)
                              (prog2$ (er hard? 'get-stack-height-and-pc-to-step-from-myif-nest-helper "NOTE: Unexpected (constant) state term, after stripping step calls: ~x0.~%" stripped-state)
                                      (mv :error nil nil))
                            (let ((stripped-expr (aref1 'dag-array dag-array stripped-state)))
                              (if (not (consp stripped-expr))
                                  (prog2$ (er hard? 'get-stack-height-and-pc-to-step-from-myif-nest-helper "Unexpected state term: ~x0, after stripping step calls.  Got a variable, but expected a make-state.~%" stripped-expr)
                                          (mv :error nil nil))
                                (let ((stripped-expr-fn (ffn-symb stripped-expr)))
                                  (if (eq 'jvm::make-state stripped-expr-fn)
                                      (mv :step-present nil nil)
                                    ;; Avoid printing anything here, because steps can stack up around a call to jvm::obtain-and-throw-exception.
                                    (if (member-eq stripped-expr-fn '(jvm::obtain-and-throw-exception jvm::execute-new))
                                        (mv :finished nil nil)
                                      (prog2$ (er hard? 'get-stack-height-and-pc-to-step-from-myif-nest-helper "Unexpected state term: ~x0, after stripping step calls.~%" stripped-expr)
                                              (mv :error nil nil)))))))))
                      (progn$ (print-dag-only-supporters 'dag-array dag-array nest)
                              (er hard? 'get-stack-height-and-pc-to-step-from-myif-nest-helper "Unexpected state term: ~X01.~%" expr nil)
                              (mv :error nil nil))))))))))))))

(local
 (defthm rationalp-when-natp
   (implies (natp x)
            (rationalp x))))

(defthm rationalp-of-mv-nth-1-of-get-stack-height-and-pc-to-step-from-myif-nest-helper
  (implies (eq :ready (mv-nth 0 (get-stack-height-and-pc-to-step-from-myif-nest-helper nest base-stack dag-array)))
           (rationalp (mv-nth 1 (get-stack-height-and-pc-to-step-from-myif-nest-helper nest base-stack dag-array))))
  :hints (("Goal" :in-theory (enable get-stack-height-and-pc-to-step-from-myif-nest-helper))))

(defthm rationalp-of-mv-nth-0-of-get-stack-height-and-pc-to-step-from-myif-nest-helper
  (implies (eq :ready (mv-nth 0 (get-stack-height-and-pc-to-step-from-myif-nest-helper nest base-stack dag-array)))
           (rationalp (mv-nth 2 (get-stack-height-and-pc-to-step-from-myif-nest-helper nest base-stack dag-array))))
  :hints (("Goal" :in-theory (enable get-stack-height-and-pc-to-step-from-myif-nest-helper
                                     get-stack-height-and-pc-from-call-stack
                                     get-stack-height-and-pc-from-thread-table
                                     ;get-stack-height-and-pc-from-thread
                                     get-stack-height-and-pc-from-make-state
                                     get-pc-from-frame))))

(verify-guards get-stack-height-and-pc-to-step-from-myif-nest-helper :otf-flg t
  :hints (("Goal" :in-theory (enable car-becomes-nth-of-0 natp))))

;; ;bozo combine this walk of the nest with the main one?
;; (skip- proofs
;;  (defun myif-nest-of-make-statesp (expr dag-array)
;;    (and (consp expr)
;;         (if (equal 'myif (ffn-symb expr))
;;             (and (myif-nest-of-make-statesp (get-expr (darg2 expr) dag-array) dag-array)
;;                  (myif-nest-of-make-statesp (get-expr (darg3 expr) dag-array) dag-array))
;;           ;fixme - why would it ever be a bvif?
;;           (if (equal 'bvif (ffn-symb expr))
;;               (and (myif-nest-of-make-statesp (get-expr (darg3 expr) dag-array) dag-array)
;;                    (myif-nest-of-make-statesp (get-expr (darg4 expr) dag-array) dag-array))
;;             (equal 'jvm::make-state (ffn-symb expr)))))))

;Check whether NEST is a nest of myifs with make-states at the leaves
;; (defun myif-nest-of-make-statesp (nest dag-array)
;;   (declare (xargs :guard (or (myquotep nest)
;;                              (and (natp nest)
;;                                   (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
;;                   :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))
;;                   :measure (if (quotep nest) 0 (+ 1 (nfix nest)))
;;                   ))
;;   (if (consp nest) ;test for quotep
;;       (prog2$ (cw "NOTE: Unexpected state term: ~x0.  Expected a make-state.~%" nest)
;;               nil)
;;     (if (not (mbt (integerp nest))) ;for termination?
;;         nil
;;       ;; it's a nodenum, so look it up:
;;       (let ((expr (aref1 'dag-array dag-array nest)))
;;         ;; must be a call of make-state or myif
;;         (if (not (consp expr))
;;             (prog2$ (cw "NOTE: Unexpected state term: ~x0.  Expected a make-state.~%" expr)
;;                     nil)
;;           (if (eq 'jvm::make-state (ffn-symb expr)) ;todo: check the args?
;;               t
;;             (if (eq 'myif (ffn-symb expr))
;;                 (and (true-listp (dargs expr))
;;                      (= 3 (len (dargs expr)))
;;                      (let ((then-branch (darg2 expr))
;;                            (else-branch (darg3 expr)))
;;                        (and (mbt (or (quotep then-branch)
;;                                      (and (natp then-branch)
;;                                           (< then-branch nest))))
;;                             (mbt (or (quotep else-branch)
;;                                      (and (natp else-branch)
;;                                           (< else-branch nest))))
;;                             ;; both the then and else branches must be myif nests of make-states
;;                             (myif-nest-of-make-statesp then-branch dag-array)
;;                             (myif-nest-of-make-statesp else-branch dag-array))))
;;               )))))))

;; Choose a state in the myif nest to step and return its stack-height
;; (relative to BASE-STACK) and its PC.  NEST must be the nodenum of a myif
;; nest with states at the leaves.  For use in axe-bind-free functions.
;; Returns an alist binding the vars sh2 and pc, or nil to indicate that there
;; is no state to step.  This now supports things at branches that we don't
;; expect, such as exception branches, since maybe they will later be pruned
;; away.  Just ignore them while pushing the other states forward.  Then, we
;; use rules like run-until-return-from-stack-height-of-myif-axe-split-1 to
;; push the run-until-return.. into the myif nest when nothing more can be done
;; (since any exception branches that remain will prevent the joins from
;; happening).
(defund get-stack-height-and-pc-to-step-from-myif-nest (nest base-stack dag-array)
  (declare (xargs :guard (and (or (myquotep nest)
                                  (and (natp nest)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
                              (or (myquotep base-stack)
                                  (and (natp base-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack)))))))
  (if (consp nest) ;check for quotep
      (er hard? 'get-stack-height-and-pc-to-step-from-myif-nest "Unexpected arguments.")
    (progn$
     ;; Uncomment this to print info on branches:
     ;; (cw "(~x0 branches in myif nest.)~%" (count-myif-branches nest dag-array))
     ;;(cw "Dag: ~x0.~%" (print-dag-only-supporters-list (list nest) 'dag-array dag-array))
     (mv-let (status stack-height pc)
       (get-stack-height-and-pc-to-step-from-myif-nest-helper nest base-stack dag-array)
       (if (eq :ready status)
           (acons 'sh2 (list 'quote stack-height)
                  (acons 'pc (list 'quote pc) nil))
         nil ;failure
         )))))

;; Check that there are no MYIF branches in NEST that we want to step.  If this
;; is true of both branches of a MYIF, we might as well push the
;; run-until-return over the branches of the MYIF.  NOTE: Assumes the presens
;; of a dummy frame, so any state to be stepped must have at least 2 frames
;; about base-stack.
(defund no-state-to-step-p (nest base-stack dag-array)
  (declare (xargs :guard (and (or (myquotep nest)
                                  (and (natp nest)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
                              (or (myquotep base-stack)
                                  (and (natp base-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack)))))))
  (if (consp nest)    ;check for quotep
      (er hard? 'no-state-to-step-p "Unexpected (constant) argument.")
    (mv-let (status stack-height pc)
      (get-stack-height-and-pc-to-step-from-myif-nest-helper nest base-stack dag-array)
      ;; (declare (ignore stack-height pc)) ;todo: don't bother to compute these?
      (declare (ignore pc)) ;todo: don't bother to compute?
      (if (and (eq :ready status)
               (= 1 stack-height))
          t ;; since we assume there is a dummy frame above base stack, if the height above base-stack is 1, only the dummy remains and we are done
        ;; NOTE: If status is :step-present, we may do a step in the next chunk of execution, so this branch is not done!
        (eq :finished status)))))

;; (defun is-a-make-statep (item dag-array)
;;   (declare (xargs :guard (or (myquotep item)
;;                              (and (natp item)
;;                                   (pseudo-dag-arrayp 'dag-array dag-array (+ 1 item))))))
;;   (if (consp item) ;test for quotep
;;       nil
;;     ;; it's a nodenum, so look it up:
;;     (let ((expr (aref1 'dag-array dag-array item)))
;;       (and (consp expr)
;;            (eq 'jvm::make-state (ffn-symb expr)))))) ;todo: check the args or arity?
