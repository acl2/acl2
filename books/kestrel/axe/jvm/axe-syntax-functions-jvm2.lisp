; Additional JVM-related syntactic tests
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

;; These are only used when lifting loops.

;(include-book "../jvm/symbolic-execution-common")
(include-book "kestrel/jvm/pc-designators" :dir :system)
(include-book "../dag-arrays")
(include-book "../axe-syntax-functions")
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; TODO: Can we combine the get-pc-designator-stack machinery with the extract-control-information-from-stack machinery?

(local (in-theory (disable jvm::method-namep
                           true-listp)))

(defund pc-designator-listp (s)
  (declare (xargs :guard t))
  (if (atom s)
      (null s)
    (and (pc-designatorp (first s))
         (pc-designator-listp (rest s)))))

(defthm pc-designator-listp-forward-to-true-listp
  (implies (pc-designator-listp pc-designators)
           (true-listp pc-designators))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pc-designator-listp))))

;; Returns a pc-designator or :error
(defund get-pc-designator-from-symbolic-frame-axe (frame dag-array)
  (declare (xargs :guard (or (myquotep frame)
                             (and (natp frame)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 frame))))))
  (if (consp frame) ;check for quotep
      (let ((frame (unquote frame)))
        (if (jvm::framep frame)
            (get-pc-designator-from-frame frame)
          (prog2$ (er hard? 'get-pc-designator-from-symbolic-frame-axe "Unexpected constant frame")
                  :error)))
    (let ((expr (aref1 'dag-array dag-array frame)))
      (if (and (call-of 'jvm::make-frame expr)
               (true-listp expr)
               (eql 6 (len (dargs expr)))
               (myquotep (darg1 expr)) ;this may be a non-constant if we have returned to the dummy frame (something like the PC plus the length of the invoke instruction)
               (myquotep (darg6 expr))
               (jvm::pcp (unquote (darg1 expr)))
               (jvm::method-designatorp (unquote (darg6 expr)))
               )
          (make-pc-designator (first (unquote (darg6 expr)))
                              (second (unquote (darg6 expr)))
                              (third (unquote (darg6 expr)))
                              (unquote (darg1 expr)))
        (prog2$ nil
                ;;(print-dag-only-supporters 'dag-array dag-array frame)
                ;;(er hard? 'get-stack-height-and-pc-from-frame "Unexpected frame: ~x0, in DAG printed just above." expr)
                :error)))))

(defthm pc-designatorp-of-get-pc-designator-from-symbolic-frame-axe
  (implies (not (equal :error (get-pc-designator-from-symbolic-frame-axe frame dag-array)))
           (pc-designatorp (get-pc-designator-from-symbolic-frame-axe frame dag-array)))
  :hints (("Goal" :in-theory (enable get-pc-designator-from-symbolic-frame-axe jvm::framep jvm::cur-class-name jvm::method-designator
                                     make-pc-designator))))

;(local (in-theory (enable car-becomes-nth-of-0)))

;; Returns a list of pc-designators (topmost frame first), or :error.  The call
;; stack should be a bunch of pushes on top of the pop of base-stack
;; (base-stack should often be a the call stack of a state var).
(defund get-pc-designator-stack-from-symbolic-call-stack-axe (call-stack base-stack dag-array)
  (declare (xargs :guard (and (or (myquotep call-stack)
                                  (and (natp call-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 call-stack))))
                              (or (myquotep base-stack)
                                  (and (natp base-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack)))))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))
                  :measure (if (consp call-stack) ;check for quotep
                               0
                             (+ 1 (nfix call-stack)))))
  (if (consp call-stack) ;check for a constant (we expect
      (prog2$ (er hard? 'get-pc-designator-stack-from-symbolic-call-stack-axe "Unexpected stack (a constant): ~x0" call-stack)
              :error)
    (and (mbt (natp call-stack))
         (let ((call-stack-expr (aref1 'dag-array dag-array call-stack)))
           (if (and (consp call-stack-expr)
                    (eq (car call-stack-expr) 'jvm::pop-frame)
                    (eql 1 (len (dargs call-stack-expr)))
                    (equal base-stack (darg1 call-stack-expr)))
               ;; we've found "pop of base-stack" so there are no more pc-designators to gather
               nil
             (if (and (consp call-stack-expr)
                      (eq (car call-stack-expr) 'jvm::push-frame)
                      (eql 2 (len (dargs call-stack-expr)))
                      (mbt (or (quotep (darg2 call-stack-expr))
                               (and (natp (darg2 call-stack-expr))
                                    (< (darg2 call-stack-expr) call-stack)))))
                 (let ((res (get-pc-designator-from-symbolic-frame-axe (darg1 call-stack-expr) dag-array)))
                   (if (eq :error res)
                       :error
                     (let ((res2 (get-pc-designator-stack-from-symbolic-call-stack-axe (darg2 call-stack-expr) base-stack dag-array)))
                       (if (eq :error res2)
                           :error
                         (cons res
                               res2)))))
               (er hard? 'get-pc-designator-stack-from-symbolic-call-stack-axe "Unexpected stack: ~x0 (base-stack is ~x1)" call-stack-expr base-stack)))))))

(defthm pc-designator-listp-of-get-pc-designator-stack-from-symbolic-call-stack-axe
  (implies (not (equal :error (get-pc-designator-stack-from-symbolic-call-stack-axe call-stack base-stack dag-array)))
           (pc-designator-listp (get-pc-designator-stack-from-symbolic-call-stack-axe call-stack base-stack dag-array)))
  :hints (("Goal" :in-theory (enable pc-designator-listp
                                     get-pc-designator-stack-from-symbolic-call-stack-axe))))

;; (defund get-pc-designator-stack-from-symbolic-thread-axe (thread base-stack dag-array)
;;   (declare (xargs :guard (and (or (myquotep thread)
;;                                   (and (natp thread)
;;                                        (pseudo-dag-arrayp 'dag-array dag-array (+ 1 thread))))
;;                               (or (myquotep base-stack)
;;                                   (and (natp base-stack)
;;                                        (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack)))))
;;                   :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))))
;;   (if (consp thread) ;checks for quotep
;;       (prog2$ (er hard? 'get-pc-designator-stack-from-symbolic-thread-stack-axe "Unexpected thread: ~x0" thread)
;;               :error)
;;     (let ((expr (aref1 'dag-array dag-array thread)))
;;       (if (not (and (consp expr)
;;                     (eq 'jvm::make-thread (ffn-symb expr))
;;                     (= 1 (len (dargs expr)))))
;;           (prog2$ (er hard? 'get-pc-designator-stack-from-symbolic-thread-stack-axe "Unexpected thread: ~x0" expr)
;;                   :error)
;;         (get-pc-designator-stack-from-symbolic-call-stack-axe (darg1 expr) base-stack dag-array)))))

(defund get-pc-designator-stack-from-symbolic-thread-table-axe (thread-table base-stack dag-array)
  (declare (xargs :guard (and (or (myquotep thread-table)
                                  (and (natp thread-table)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 thread-table))))
                              (or (myquotep base-stack)
                                  (and (natp base-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack)))))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))))
  (if (consp thread-table) ;checks for quotep
      (prog2$ (er hard? 'get-pc-designator-stack-from-symbolic-thread-table-axe "Unexpected thread-table: ~x0" thread-table)
              :error)
    (let ((expr (aref1 'dag-array dag-array thread-table)))
      (if (not (and (consp expr)
                    (eq 'jvm::bind (ffn-symb expr))
                    (eql 3 (len (dargs expr))))) ;a call to bind for thread 0 (TODO: check the thread ID!)
          (prog2$ (er hard? 'get-pc-designator-stack-from-symbolic-thread-table-axe "Unexpected thread-table: ~x0" thread-table)
              :error)
        (get-pc-designator-stack-from-symbolic-call-stack-axe (darg2 expr) base-stack dag-array)))))

;; Returns the pc-designator-stack or :error.
(defund get-pc-designator-stack-from-symbolic-state-axe (make-state base-stack dag-array)
  (declare (xargs :guard (and (or (myquotep make-state)
                                  (and (natp make-state)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 make-state))))
                              (or (myquotep base-stack)
                                  (and (natp base-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack)))))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))))
  (if (consp make-state) ;checks for quotep
      (prog2$ (er hard? 'get-pc-designator-stack-from-symbolic-state-axe "Unexpected state: ~x0" make-state)
              :error)
    (let ((expr (aref1 'dag-array dag-array make-state)))
      (if (not (and (consp expr)
                    (eq 'jvm::make-state (ffn-symb expr))
                    (eql 8 (len (dargs expr)))))
          (prog2$ (er hard? 'get-pc-designator-stack-from-symbolic-state-axe "Unexpected state: ~x0" make-state)
              :error)
        (get-pc-designator-stack-from-symbolic-thread-table-axe (darg1 expr) base-stack dag-array)))))

(defthm pc-designator-listp-of-get-pc-designator-stack-from-symbolic-state-axe
  (implies (not (equal :error (get-pc-designator-stack-from-symbolic-state-axe make-state base-stack dag-array)))
           (pc-designator-listp (get-pc-designator-stack-from-symbolic-state-axe make-state base-stack dag-array)))
  :hints (("Goal" :in-theory (enable get-pc-designator-stack-from-symbolic-state-axe
                                     ;;get-pc-designator-stack-from-symbolic-thread-axe
                                     get-pc-designator-stack-from-symbolic-thread-table-axe))))



(defund can-step-state-with-pc-designator-stack (pc-designator-stack segment-pcs loop-headers)
  (declare (xargs :guard (and (pc-designator-listp pc-designator-stack)
;                              (consp pc-designator-stack) ;drop?
                              (pc-designator-listp loop-headers)
                              (true-listp segment-pcs))
                  :guard-hints (("Goal" :in-theory (enable pc-designator-listp)))))
  (and (consp pc-designator-stack) ;height 0 means we've exited the frame that had the segment
       (b* ((stack-height (len pc-designator-stack))
            (pc-designator (car pc-designator-stack))
            (pc (pc-designator-pc pc-designator))
            )
         (and (not (member-equal pc-designator loop-headers))
              (if (< 1 stack-height) ;it's in a subroutine (and not at a loop header), so we can step it
                  t
                (if (eql 1 stack-height) ;it's at the same level as the given segment, so check whether the PC is in the segment
                    (if (member-equal pc segment-pcs) t nil)
                  nil ;stack height is 0
                  ))))))

(defthm not-can-step-state-with-pc-designator-stack-of-nil
  (not (can-step-state-with-pc-designator-stack nil segment-pcs loop-headers))
  :hints (("Goal" :in-theory (enable can-step-state-with-pc-designator-stack))))

;todo: call can-step-state-with-pc-designator-stack here?
(defund choose-pc-designator-stack-to-step (then-branch-pc-designator-stack else-branch-pc-designator-stack segment-pcs loop-headers)
  (declare (xargs :guard (and (pc-designator-listp else-branch-pc-designator-stack)
                              (pc-designator-listp then-branch-pc-designator-stack)
;                              (consp else-branch-pc-designator-stack) ;drop?
;                              (consp then-branch-pc-designator-stack) ;drop?
                              (pc-designator-listp loop-headers)
                              (true-listp segment-pcs))
                  :guard-hints (("Goal" :in-theory (enable pc-designator-listp)))))
  ;; both results are valid,
  (b* ((can-step-then-branch (can-step-state-with-pc-designator-stack then-branch-pc-designator-stack segment-pcs loop-headers))
       ;; (- (cw "(Can step then branch: ~x0.)~%" can-step-then-branch))
       (can-step-else-branch (can-step-state-with-pc-designator-stack else-branch-pc-designator-stack segment-pcs loop-headers))
       ;; (- (cw "(Can step else branch: ~x0.) ~%" can-step-else-branch))
       )
    (if can-step-then-branch
        (if (not can-step-else-branch)
            then-branch-pc-designator-stack
          (let ((then-branch-stack-height (len then-branch-pc-designator-stack))
                (else-branch-stack-height (len else-branch-pc-designator-stack)))
            ;; could step either.  choose which one we like:
            (if (< then-branch-stack-height else-branch-stack-height)
                else-branch-pc-designator-stack
              (if (< else-branch-stack-height then-branch-stack-height)
                  then-branch-pc-designator-stack
                (let* ((then-branch-pc-designator (car then-branch-pc-designator-stack))
                       (else-branch-pc-designator (car else-branch-pc-designator-stack))
                       (then-branch-pc (pc-designator-pc then-branch-pc-designator))
                       (else-branch-pc (pc-designator-pc else-branch-pc-designator)))
                  ;;both are at the same height, so choose the state with the lowest PC (a heuristic):
                  (if (< then-branch-pc else-branch-pc)
                      then-branch-pc-designator-stack
                    else-branch-pc-designator-stack))))))
      (if can-step-else-branch
          else-branch-pc-designator-stack
        :none))))

;;Returns the pc-designator-stack of the state to step, or :none, or :error.
(defund choose-state-to-step-helper (nest
                                     base-stack
                                     segment-pcs
                                     loop-headers
                                     dag-array)
  (declare (xargs :guard (and (or (myquotep nest)
                                  (and (natp nest)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
                              (or (myquotep base-stack)
                                  (and (natp base-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack))))
                              (true-listp segment-pcs)
                              (pc-designator-listp loop-headers))
                  :verify-guards nil ;done below
                  :measure (if (quotep nest)
                               0
                             (+ 1 (nfix nest)))))
  (if (consp nest) ;check for quotep
      (prog2$ (cw "NOTE: Unexpected (constant) state term: ~x0.~%" nest)
              :none)
    (if (not (mbt (integerp nest))) ;for termination
        :error                      ;should never happen
      (let ((expr (aref1 'dag-array dag-array nest)))
        (if (not (consp expr))
            (prog2$ (cw "NOTE: Unexpected state term: ~x0.  Got a variable, but expected a make-state.~%" nest)
                    :none)
          (let ((fn (ffn-symb expr)))
            (if (eq 'jvm::make-state fn)
                ;; If it's a make-state, get its info and decide if we want to step it:
                (let ((pc-designator-stack (get-pc-designator-stack-from-symbolic-state-axe nest base-stack dag-array)))
                  (if (eq pc-designator-stack :error)
                      :error
                    (if (can-step-state-with-pc-designator-stack pc-designator-stack segment-pcs loop-headers)
                        pc-designator-stack
                      :none)))
              (if (and (eq 'myif fn)
                       (eql 3 (len (dargs expr))))
                  (let ((then-branch (darg2 expr))
                        (else-branch (darg3 expr)))
                    (if (not (mbt (and (or (quotep then-branch) ;for termination
                                           (and (natp then-branch)
                                                (< then-branch nest)))
                                       (or (quotep else-branch)
                                           (and (natp else-branch)
                                                (< else-branch nest))))))
                        :error
                      (b* ((then-branch-pc-designator-stack (choose-state-to-step-helper then-branch base-stack segment-pcs loop-headers dag-array))
                           (else-branch-pc-designator-stack (choose-state-to-step-helper else-branch base-stack segment-pcs loop-headers dag-array)))
                        ;; If either is :error, chose the other one:
                        (if (eq :error then-branch-pc-designator-stack)
                            else-branch-pc-designator-stack
                          (if (eq :error else-branch-pc-designator-stack)
                              then-branch-pc-designator-stack
                            ;; neither is :error. If either is :none chose the other one:
                            (if (eq :none then-branch-pc-designator-stack)
                                else-branch-pc-designator-stack
                              (if (eq :none else-branch-pc-designator-stack)
                                  then-branch-pc-designator-stack
                                (choose-pc-designator-stack-to-step then-branch-pc-designator-stack else-branch-pc-designator-stack segment-pcs loop-headers))))))))
                (if (eq 'jvm::obtain-and-throw-exception fn)
                    (prog2$ (cw "(Unresolved exception branch detected (will try to prune it later).)~%")
                            :none)
                  (if (member-eq fn '(step-state-with-pc-and-call-stack-height step-state-with-pc-designator-stack))
                      ;; Avoid printing anything here, because these can stack up around a call to jvm::obtain-and-throw-exception.
                      :none
                    (prog2$ (cw "(NOTE: Unexpected state term: ~x0.  Expected a make-state.)~%" expr)
                            :error)))))))))))

(defthm pc-designator-listp-of-choose-state-to-step-helper
  (implies (and (not (equal :error (choose-state-to-step-helper nest base-stack segment-pcs loop-headers dag-array)))
                (not (equal :none (choose-state-to-step-helper nest base-stack segment-pcs loop-headers dag-array))))
           (pc-designator-listp (choose-state-to-step-helper nest base-stack segment-pcs loop-headers dag-array)))
  :hints (("Goal" :in-theory (enable choose-state-to-step-helper
                                     choose-pc-designator-stack-to-step))))

(verify-guards choose-state-to-step-helper :hints (("Goal" :in-theory (enable car-becomes-nth-of-0))))

;;Returns an alist binding the variable 'pc-designator-stack indicating which
;; state to step, or nil to indicate failure.  The base-stack should be the
;; call-stack of some state-var.  The result contains info about the frame
;; corresponding to the top frame of base-stack (which may however be at a
;; different PC), plus any other frames above that.
(defund choose-state-to-step (nest base-stack segment-pcs loop-headers dag-array)
  (declare (xargs :guard (and (or (myquotep nest)
                                  (and (natp nest)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
                              (or (myquotep base-stack)
                                  (and (natp base-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack))))
                              )))
  (if (not (and (atom nest) ;check for not quotep
                (myquotep loop-headers)
                (pc-designator-listp (unquote loop-headers))
                (myquotep segment-pcs)
                (true-listp (unquote segment-pcs))))
      (er hard? 'choose-state-to-step "Unexpected arguments.")
    (progn$
     ;; Uncomment this to print info on branches:
     ;; (cw "(~x0 branches in myif nest.)~%" (count-myif-branches nest dag-array))
     (if (not (and (quotep segment-pcs)
                   (quotep loop-headers)))
         (prog2$ (er hard? 'choose-state-to-step "Unexpected segment-pcs or loop-headers: ~x0 ~x1." segment-pcs loop-headers)
                 nil)
       ;;(cw "Dag: ~x0.~%" (print-dag-only-supporters-list (list nest) 'dag-array dag-array))
       (let ((res (choose-state-to-step-helper nest
                                               base-stack
                                               (unquote segment-pcs)
                                               (unquote loop-headers)
                                               dag-array)))
         (if (or (eq :none res)
                 (eq :error res))
             nil ;failure
           (acons 'pc-designator-stack (list 'quote res) nil)))))))

(defund no-state-to-step-for-loop-lifter-p (nest base-stack segment-pcs loop-headers dag-array)
  (declare (xargs :guard (and (or (myquotep nest)
                                  (and (natp nest)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
                              (or (myquotep base-stack)
                                  (and (natp base-stack)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 base-stack)))))))
  (and (natp nest)
       (myquotep loop-headers)
       (pc-designator-listp (unquote loop-headers))
       (myquotep segment-pcs)
       (true-listp (unquote segment-pcs))
       (not (choose-state-to-step nest base-stack segment-pcs loop-headers dag-array))))
