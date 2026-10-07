; Syntactic functions over JVM terms
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Note: Portions of this file may be taken from books/models/jvm/m5.  See the
; LICENSE file and authorship information there as well.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "jvm-facts0") ; reduce?

;; ;; Recognize terms like this: (jvm::pop-frame (jvm::call-stack ... ...))
;; (defun single-pop-around-call-stackp (term)
;;   (declare (xargs :guard t))
;;   (and (consp term)
;;        (equal 'jvm::pop-frame (car term))
;;        (consp (cdr term))
;;        (consp (cadr term))
;;        (equal 'jvm::call-stack (car (cadr term)))))

;; ;TERM should be a call to make-state
;; (defun get-call-stack-term-from-thread-table-term (term)
;; ;  (declare (xargs :guard t))
;;   (if (and; (consp term)
;;            (equal 'jvm::bind (car term))
;; ;           (consp (cdr term))
;;            ;(consp (cddr term))
;;            ;(consp (caddr term))
;;            ;;(equal 'jvm::make-thread (car (caddr term)))
;;            )
;;       (caddr term)
;;     (er hard 'get-call-stack-term-from-thread-table-term "Found a thread table term we don't yet handle, ~x0." term)))

;; ;seems to return a list!
;; ;computes heuristic information only?
;; ;BOZO get rid of the execute-XXX cases, since we abandoned the idea of leaving those closed up...
;; (defun get-call-stack-term-from-state-term (term)
;; ;;   (declare (xargs :hints (("Goal" :in-theory (disable MEMBERP-OF-CONS
;; ;;                                                       BAG::NOT-SUBBAGP-OF-CONS-FROM-NOT-SUBBAGP
;; ;;                                                       MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP
;; ;;                                                       BAG::SUBBAGP-OF-REMOVE-1-FROM-SUBBAGP
;; ;;                                                       BAG::SUBBAGP-MEMBERP-REMOVE-1)))))
;;   (if (equal 'jvm::bind (car (cadr term)))
;;             (get-call-stack-term-from-thread-table-term (cadr term))
;;     ;;this doesn't actually seem to be firing...
;;     (er hard 'get-call-stack-term-from-state-term "Found a state term we don't yet handle, ~x0." term)))

(defun get-height-of-stack-term (term)
  (if (and (consp term)
           (equal (car term) 'jvm::push-frame))
      (+ 1 (get-height-of-stack-term (third term)))
    (if (and (consp term)
             (equal (car term) 'jvm::pop-frame))
        (+ -1 (get-height-of-stack-term (second term)))
      0 ;i think it must be (JVM::CALL-STACK (TH) S0)
      )))

;returns a number (0 for the same height as the cutpoint PCs, -1 if we've returns, 1 if we've pushed on a frame for a subroutine, 2 for 2 subroutines, etc.
;; (defun stack-height-of-state-term (term)
;;   (let* ((stack-term (get-call-stack-term-from-state-term term)))
;;     (get-height-of-stack-term stack-term)))


;gets the PC in the top frame of the call stack
;TERM should be a call to make-state
;returns either a singleton list or else nil
;BOZO finish guard conjecture
(defun get-pc-from-thread-table-term (term)
;  (declare (xargs :guard t))
  (if (and; (consp term)
           (equal 'jvm::bind (car term))
;           (consp (cdr term))
           ;(consp (cddr term))
           ;(consp (caddr term))
           ;;(equal 'jvm::make-thread (car (caddr term)))
           ;(consp (cdr (caddr term)))
           ;(consp (cadr (caddr term)))
           (equal 'jvm::push-frame (car (caddr term)))
           ;(consp (cdr (cadr (caddr term))))
           ;(consp (car (cdr (cadr (caddr term)))))
           (equal 'jvm::make-frame (car (cadr (caddr term))))
           )
      (if (<= 0 (get-height-of-stack-term (caddr term))) ;(single-pop-around-call-stackp (caddr (cadr (caddr term)))) ;the state hasn't already returned
          (list (cadr (cadr (cadr (caddr term)))))
        nil)
    (er hard 'get-pc-from-thread-table-term "Found a thread table term we don't yet handle, ~x0." term)))

;seems to return a list!
;computes heuristic information only?
;BOZO get rid of the execute-XXX cases, since we abandoned the idea of leaving those closed up...
(defun get-pc-from-state-term (term)
  (declare (xargs :hints (("Goal" :in-theory (disable MEMBERP-OF-CONS
                                                      ;BAG::NOT-SUBBAGP-OF-CONS-FROM-NOT-SUBBAGP
                                                      MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP
                                                      ;BAG::SUBBAGP-OF-REMOVE-1-FROM-SUBBAGP
                                                      ;;BAG::SUBBAGP-MEMBERP-REMOVE-1
                                                      )))))
  (if (member-eq (first term) '(jvm::execute-iconst_x jvm::execute-aload_x jvm::execute-aaload jvm::execute-baload jvm::execute-iaload jvm::execute-dup jvm::execute-ixor jvm::execute-iand jvm::execute-iadd jvm::execute-isub jvm::execute-istore_x jvm::execute-iload_x jvm::execute-ishl jvm::execute-ishr))
      (list (list 'quote (+ 1 (unquote (car (get-pc-from-state-term (fourth term)))))))
    (if (member-eq (first term) '(jvm::execute-aload jvm::execute-istore jvm::execute-bipush))
        (list (list 'quote (+ 2 (unquote (car (get-pc-from-state-term (fourth term)))))))
      (if (member-eq (first term) '(jvm::execute-putfield jvm::execute-getfield jvm::execute-getstatic jvm::execute-sipush jvm::execute-IF_ICMPGE))
          (list (list 'quote (+ 3 (unquote (car (get-pc-from-state-term (fourth term)))))))
        (if (equal 'jvm::bind (car (cadr term)))
            (get-pc-from-thread-table-term (cadr term))
;this doesn't actually seem to be firing...
          (er hard 'get-pc-from-state-term "Found a state term we don't yet handle, ~x0." term))))))

;TERM may include calls to myif
;returns a list of the PCS for all the suitable branches
;branches corresponding to states that have returned don't generate any PCs.
;; (defun get-pcs-from-state-term (term)
;;   (if (endp term)
;;       nil
;;     (if (equal 'myif (car term))
;;         (append (get-pcs-from-state-term (caddr term))
;;                 (get-pcs-from-state-term (cadddr term)))
;;       (get-pc-from-state-term term))))

;BOZO only do it if the PC of s is "better" than the PC of s2
;how handle an arbitrary myif nest of these things?
;how about this?  define a function FOO that steps a state only if the pc is P.
;figure out which pc from the if next you want to execute and introduce FOO
;push FOO into the nest of myifs.
;for any state whose PC isn't P, the FOO is a no-op
;state with PC P do get stepped.
;do we want to normalize the myif nest to bring together states with the same PC?
;could that cause an exponential blowup?

;gather all the pcs (how?  what about those for which the state has already returned?)
;have to make sure the best PC isn't a cutpoint...
;what about the end game?  what if the branches end up at different cutpoints?
;same sort of thing?

;; (DEFTHM BRANCHER-SYMBOLIC-SIMULATION-RULE-2-myif-version
;;   (IMPLIES
;;    (AND
;;     (EQUAL SH (STACK-HEIGHT S))
;;     (EQUAL PC (PROGRAM-COUNTER S))
;;     (NOT (MEMBER PC PC-VALS))
;;     (SYNTAXP
;;      (PROG2$ (CW "__Executing the instruction at PC ~p0.~%"
;;                  PC)
;;              T))
;;     (SYNTAXP (PROG2$ (CW "__State ~p0.~%" S) T)))
;;    (EQUAL (BRANCHER-ASSERTION-TRUE-AT-CUTPOINT-OR-NO-REACHABLE-CUTPOINT SH PC-VALS S0 (myif test S s2))
;;           (BRANCHER-ASSERTION-TRUE-AT-CUTPOINT-OR-NO-REACHABLE-CUTPOINT SH PC-VALS S0 (myif test (NEXT S) s2))))
;;   :hints (("Goal" :use (:instance BRANCHER-SYMBOLIC-SIMULATION-RULE-2)
;;            :in-theory (union-theories '(myif) (theory 'minimal-theory)))))

;term1 and term2 are quoted constants for JVM?
;; (defun smaller-pc-term (term1 term2)
;;   (declare (xargs :guard (and (quotep term1)
;;                               (consp (cdr term1))
;;                               (natp (cadr term1))
;;                               (quotep term2)
;;                               (consp (cdr term2))
;;                               (natp (cadr term2)))))
;;   (if (<= (cadr term1) (cadr term2))
;;       term1
;;     term2))

;; (defund smallest-pc-term (lst)
;;   (if (endp lst)
;;       'fake-pc-term
;;     (if (endp (cdr lst))
;;         (car lst)
;;       (smaller-pc-term (car lst) (smallest-pc-term (cdr lst))))))

;; (defun quote-list (lst)
;;   (if (endp lst)
;;       nil
;;     (cons (list 'quote (car lst))
;;           (quote-list (cdr lst)))))

;; ;BOZO are the PCs integers or quoted terms?
;; (defun find-pc-to-step (term cutpoint-pc-vals)
;;   (let* ((pc-term-list (get-pcs-from-state-term term))
;;          ;;we don't want to step a PC which is already at a cutpoint...
;;          (pc-term-list (set-difference-equal pc-term-list (quote-list (unquote cutpoint-pc-vals))))
;;          )
;;     (if (endp pc-term-list)
;;         nil
;;       ;;we just pick the smallest PC.  is that smart?
;;       (acons 'pc (smallest-pc-term pc-term-list) nil))))


(mutual-recursion

 (defun state-list-size (term-list)
   (if (endp term-list)
       0
     (+ (state-size (car term-list))
        (state-list-size (cdr term-list)))))

;now just counts the connectives
 (defun state-size (term)
   (if (not (consp term))
       0
     (if (equal (car term) 'quote)
         0 ;constants count as 1
       (+ 1 (state-list-size (cdr term)))))))

(mutual-recursion

 (defun state-list-size-without-hide (term-list)
   (if (endp term-list)
       0
     (+ (state-size-without-hide (car term-list))
        (state-list-size-without-hide (cdr term-list)))))

;now just counts the connectives
 (defun state-size-without-hide (term)
   (if (not (consp term))
       0
     (if (equal (car term) 'quote)
         0 ;constants count as 1
     (if (equal (car term) 'hide)
         0 ;don't count anything in a hide
       (+ 1 (state-list-size-without-hide (cdr term))))))))

;term is a myif nest of state terms
(defun state-profile (term)
  (declare (xargs :hints (("Goal" ;:in-theory (disable 3-CDRS)
                           ))))
  (if (equal 'myif (car term))
      `(myif ,(cadr term)
             ,(state-profile (caddr term))
             ,(state-profile (cadddr term)))
    ;(state-size-without-hide term)
    (if (and (quotep (car (GET-PC-FROM-STATE-TERM term)))
             (integerp (unquote (car (GET-PC-FROM-STATE-TERM term)))))
        (car (GET-PC-FROM-STATE-TERM term))
      (car (GET-PC-FROM-STATE-TERM term)) ;term ; todo: same as then-branch
      )))
