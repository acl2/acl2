; Rules about the JVM model
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Note: Portions of this file may be taken from books/models/jvm/m5.  See the
; LICENSE file and authorship information there as well.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;This book was created by Eric Smith and includes a variety of facts about the JVM that seemed helpful for proofs.

(include-book "jvm-facts0")
(include-book "arrays")
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "kestrel/bv/bvif" :dir :system) ;todo
(local (include-book "kestrel/lists-light/len" :dir :system))

;(in-theory (disable ACL2::LOGAPP-0)) ;does forcing (todo: make a library wrapper)

;;
;; Rules to lift the IF (which is usually around the PC) after a conditional branch
;;

;; Splits the simulation after a conditional branch, introducing a MYIF of make-states.
;fixme consider the case when the two branches are for different methods but happen to have the same pc.
;; Another option could be to lift the IFs expressions for the PCs in the individual semantic functions.
(defthm make-state-when-pc-if-is-around-pc
  (equal (jvm::make-state (jvm::bind th
                                     (jvm::push-frame (jvm::make-frame (jvm::pc-if test pc1 pc2)
                                                                       locals
                                                                       stack
                                                                       locked-object
                                                                       method-info
                                                                       method-designator)
                                                      rest)
                                     tt)
                          heap ct hrt monitor-table sfm ic intern-table)
         (myif test
               (jvm::make-state (jvm::bind th
                                           (jvm::push-frame (jvm::make-frame pc1
                                                                             locals
                                                                             stack
                                                                             locked-object
                                                                             method-info
                                                                             method-designator)
                                                            rest)
                                           tt)
                                heap ct hrt monitor-table sfm ic intern-table)
               (jvm::make-state (jvm::bind th
                                           (jvm::push-frame (jvm::make-frame pc2
                                                                             locals
                                                                             stack
                                                                             locked-object
                                                                             method-info
                                                                             method-designator)
                                                            rest)
                                           tt)
                                heap ct hrt monitor-table sfm ic intern-table)))
  :hints (("Goal" :in-theory (enable jvm::pc-if myif))))

;; Do we still need this?
(defthm make-state-when-myif-is-around-method-designator
  (equal (JVM::MAKE-STATE
                    (JVM::BIND th
                              (JVM::PUSH-FRAME
                                (JVM::MAKE-FRAME pc
                                 locals stack locked-object method-info (MYIF test method-designator1 method-designator2)) rest) tt)
                    heap ct hrt monitor-table sfm ic intern-table)
         (myif test
               (JVM::MAKE-STATE
                          (JVM::BIND th
                                    (JVM::PUSH-FRAME
                                      (JVM::MAKE-FRAME
                                       pc
                                       locals stack locked-object method-info method-designator1) rest) tt)
                          heap ct hrt monitor-table sfm ic intern-table)
               (JVM::MAKE-STATE
                          (JVM::BIND th
                                    (JVM::PUSH-FRAME
                                      (JVM::MAKE-FRAME
                                       pc
                                       locals stack locked-object method-info method-designator2) rest) tt)
                          heap ct hrt monitor-table sfm ic intern-table)))
  :hints (("Goal" :in-theory (union-theories '(myif) (theory 'minimal-theory)))))

;; Do we still need this?
(defthm make-state-when-myif-is-around-method-info
  (equal (JVM::MAKE-STATE
          (JVM::BIND th
                     (JVM::PUSH-FRAME
                      (JVM::MAKE-FRAME pc
                                       locals stack locked-object
                                       (myif test method-info1 method-info2)
                                       method-designator) rest) tt)
          heap ct hrt monitor-table sfm ic intern-table)
         (myif test
               (JVM::MAKE-STATE
                (JVM::BIND th
                           (JVM::PUSH-FRAME
                            (JVM::MAKE-FRAME
                             pc
                             locals stack locked-object method-info1 method-designator) rest) tt)
                heap ct hrt monitor-table sfm ic intern-table)
               (JVM::MAKE-STATE
                (JVM::BIND th
                           (jvm::push-frame
                            (JVM::MAKE-FRAME
                             pc
                             locals stack locked-object method-info2 method-designator)
                            rest) tt)
                heap ct hrt monitor-table sfm ic intern-table)))
  :hints (("Goal" :in-theory (union-theories '(myif) (theory 'minimal-theory)))))

(defthm call-stack-of-if
  (equal (jvm::call-stack th (if test s1 s2))
         (if test (jvm::call-stack th s1) (jvm::call-stack th s2)))
  :hints (("Goal" :in-theory (union-theories '(myif) (theory 'minimal-theory)))))

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
;;     (er hard 'get-call-stack-term-from-thread-table-term "Found a thread table term we don't yet handle, ~s0." term)))

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
;;     (er hard 'get-call-stack-term-from-state-term "Found a state term we don't yet handle, ~s0." term)))

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
    (er hard 'get-pc-from-thread-table-term "Found a thread table term we don't yet handle, ~s0." term)))

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
          (er hard 'get-pcs-from-state-term "Found a state term we don't yet handle, ~s0." term))))))

;TERM may include calls to myif
;returns a list of the PCS for all the suitable branches
;branches corresponding to states that have returned don't generate any PCs.
(defun get-pcs-from-state-term (term)
  (if (endp term)
      nil
    (if (equal 'myif (car term))
        (append (get-pcs-from-state-term (caddr term))
                (get-pcs-from-state-term (cadddr term)))
      (get-pc-from-state-term term))))

;; ;nth-0 is gross.
;; (defthm myif-make-states-recombine
;;   (implies (and ;(syntaxp (equal (get-pc-from-thread-table-term tt1) (get-pc-from-thread-table-term tt2)))
;;             (equal (JVM::PC (JVM::TOP (NTH 0 (JVM::BINDING (TH) tt1))))
;;                    (JVM::PC (JVM::TOP (NTH 0 (JVM::BINDING (TH) tt2)))))
;;             )
;;            (equal (myif test (jvm::make-state tt1 h1 ct1 hrt1 sfm1 ic1) (jvm::make-state tt2 h2 ct2 hrt2 sfm2 ic2))
;;                   (jvm::make-state (myif test tt1 tt2)
;;                                   (myif test h1 h2)
;;                                   (myif test ct1 ct2)
;;                                   (myif test hrt1 hrt2)
;;                                   (myif test sfm1 sfm2)
;;                                   (myif test ic1 ic2)
;;                                   )))
;;   :hints (("Goal" :in-theory (e/d (myif) (JVM::MAKE-STATE-EQUAL-REWRITE-2)))))

(defthm jvm::myif-of-bind-and-bind
  (equal (myif test (jvm::bind x1 y1 alist1) (jvm::bind x2 y2 alist2))
         (jvm::bind (myif test x1 x2)
                    (myif test y1 y2)
                    (myif test alist1 alist2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm jvm::myif-of-push-operand-and-push-operand
  (equal (myif test (jvm::push-operand x1 y1) (jvm::push-operand x2 y2))
         (jvm::push-operand (myif test x1 x2)
                           (myif test y1 y2)))
  :hints (("Goal" :in-theory (enable myif))))

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
(defun smaller-pc-term (term1 term2)
  (declare (xargs :guard (and (quotep term1)
                              (consp (cdr term1))
                              (natp (cadr term1))
                              (quotep term2)
                              (consp (cdr term2))
                              (natp (cadr term2)))))
  (if (<= (cadr term1) (cadr term2))
      term1
    term2))

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
      (car (GET-PC-FROM-STATE-TERM term)) ;term
      )))

(defun this-threadtable-is-at-a-subroutine-call (term)
  (if (and (equal 'jvm::bind (car term))
           (equal 'jvm::push-frame (car (caddr term)))
           (equal 'jvm::make-frame (car (cadr (caddr term))))
           )
      (equal 'jvm::push-frame (car (caddr (caddr term)))) ;is the stack to which we are pushing on a frame also a push?
    (er hard 'get-pc-from-thread-table-term "Found a thread table term we don't yet handle, ~s0." term)))

(defun this-branch-is-at-a-subroutine-call (term)
  (if (equal 'jvm::bind (car (cadr term)))
      (this-threadtable-is-at-a-subroutine-call (cadr term))
    (er hard? 'this-branch-is-at-a-subroutine-call "Found a state term we don't yet handle, ~s0." term)))

;; ;term is a nest of myifs with states at the leaves
;; (defun some-branch-is-at-a-subroutine-call (term)
;;   (if (endp term)
;;       nil
;;     (if (equal 'myif (car term))
;;         (or (some-branch-is-at-a-subroutine-call (caddr term))
;;             (some-branch-is-at-a-subroutine-call (cadddr term)))
;;       (this-branch-is-at-a-subroutine-call term))))

;if neither state can be stepped (because both have reached a cutpoint or return, this function's value is meaningless)
;; (defun more-urgent-state (state1 state2 cutpoint-pc-vals)
;; ;;   (if (equal 'dummy state2)
;; ;;       t
;; ;;     (if (equal 'dummy state1)
;; ;;         nil
;;       (let* ((sh1 (stack-height-of-state-term state1))
;;              (sh2 (stack-height-of-state-term state2)))
;;         (if (> sh1 sh2) ;BOZO if we adapt this function to handle the non-inlining case, rethink some of this
;;             t
;;           (if (< sh1 sh2)
;;               nil
;;             (let* ((pc1 (unquote (car (get-pc-from-state-term state1))))
;;                    (pc2 (unquote (car (get-pc-from-state-term state2)))))
;;               (if (member-equal pc1 cutpoint-pc-vals)
;;                   nil
;;                 (if (member-equal pc2 cutpoint-pc-vals)
;;                     t
;; ;maybe we could come up with a better order than numeric order for PCs (what we want is the lagging state to catch up and be merged with the leading state, if possible.  this seems to usually correspond to stepping the one with the lower PC)
;;                   (< pc1 pc2) ;this may be a comparison of pcs from different subroutines, but i don't really know what else to do
;;                   )))))))


;))

;; (defun find-most-urgent-state (myif-nest cutpoint-pc-vals)
;;   (if (and (consp myif-nest)
;;            (equal 'myif (ffn-symb myif-nest))) ;BOZO what about umyif?
;;       (let* ((s1 (find-most-urgent-state (third myif-nest) cutpoint-pc-vals))
;;              (s2 (find-most-urgent-state (fourth myif-nest) cutpoint-pc-vals)))
;;         (if (more-urgent-state s1 s2 cutpoint-pc-vals) s1 s2) ;(more-urgent-state s1 s2 cutpoint-pc-vals)
;;         )
;;     myif-nest))

;; (defun stack-height-to-stack-height-term (stack-height)
;;   `(binary-+ ,(list 'quote stack-height) (jvm::call-stack-size (jvm::call-stack (th) s0))))

;; ;returns an alist binding pc and sh2
;; (defun find-stack-height-and-pc-to-step (term cutpoint-pc-vals)
;;   (let ((state-to-step (find-most-urgent-state term cutpoint-pc-vals)))

;;     (if (equal 'jvm::make-state (car state-to-step)) ;if for some reason it's not a make-state, don't step
;;         (let ((stack-height (stack-height-of-state-term state-to-step)))

;;           (if (<= 0 stack-height)
;;               (acons 'sh2 (stack-height-to-stack-height-term stack-height)
;;                      (acons 'pc (car (get-pc-from-state-term state-to-step))
;;                             nil))
;; ;otherwise, we've popped off the frame...
;;             nil))
;;       nil)))

;; ;rename
;; (defthm call-stack-lemma
;;   (equal (jvm::call-stack th (jvm::make-state (jvm::bind th (jvm::make-thread cs) tt) h ct hrt sfm ic))
;;          cs)
;;   :hints (("Goal" :in-theory (enable jvm::thread-top-frame jvm::call-stack jvm::make-state jvm::thread-table jvm::make-thread))))

;; (defthm call-stack-of-make-state-of-bind-of-make-thread
;;   (equal (jvm::call-stack th (jvm::make-state (jvm::bind th (jvm::make-thread callstack) threadtable)
;;                                             heap classtable hrt sfm ic))
;;          callstack)
;;   :hints
;;   (("Goal"
;;     :in-theory (enable jvm::call-stack jvm::make-state jvm::thread-table))))

;yuck? needed because top-frame does several things that should be separate?
(defthm jvm::thread-top-frame-of-make-state-of-thread-table
  (equal (jvm::thread-top-frame th (jvm::make-state (jvm::thread-table s) a b c d x ic intern-table))
         (jvm::thread-top-frame th s))
  :hints (("Goal" :in-theory (enable jvm::call-stack jvm::thread-top-frame jvm::make-state jvm::thread-table))))

;; ;yuck? needed because call-stack does two things that should be separate?
;; (defthm call-stack-of-make-state-of-thread-table
;;   (equal (jvm::call-stack th (jvm::make-state (jvm::thread-table s) a b c d x))
;;          (jvm::call-stack th s))
;;   :hints (("Goal" :in-theory (enable jvm::call-stack
;;                                      jvm::thread-table
;;                                      jvm::make-state
;;                                      ))))

;; (defthm thread-top-frame-of-make-state-of-bind-of-make-thread-of-push
;;   (equal (jvm::thread-top-frame th (jvm::make-state (jvm::bind th (jvm::make-thread (jvm::push-frame frame stack) :scheduled blah) tt) h ct hrt sfm ic))
;;          frame)
;;   :hints (("Goal" :in-theory (enable jvm::thread-top-frame jvm::make-thread jvm::call-stack jvm::thread-table))))


;; ;would rather have make-thread than list?
;; (defthm thread-top-frame-of-make-state-of-bind-of-list-of-push
;;   (equal (JVM::thread-top-frame th (JVM::MAKE-STATE (JVM::BIND th (LIST (JVM::PUSH-FRAME frame stack) :SCHEDULED blah) tt) h ct hrt sfm ic))
;;          frame)
;;   :hints (("Goal" :in-theory (enable JVM::thread-top-frame jvm::make-state JVM::CALL-STACK JVM::THREAD-TABLE))))

;; (defthm locals-lemma
;;   (equal (JVM::LOCALS (JVM::thread-top-frame th (JVM::MAKE-STATE (JVM::BIND th (LIST cs status blah) tt) h ct hrt sfm ic)))
;;          (JVM::LOCALS  (JVM::TOP CS)))
;;   :hints (("Goal" :in-theory (enable JVM::LOCALS JVM::thread-top-frame jvm::make-state JVM::CALL-STACK JVM::THREAD-TABLE))))

;; (defthm pc-lemma
;;   (equal (JVM::pc (JVM::thread-top-frame th (JVM::MAKE-STATE (JVM::BIND th (LIST cs status blah) tt) h ct hrt sfm ic)))
;;          (JVM::pc  (JVM::TOP CS)))
;;   :hints (("Goal" :in-theory (enable JVM::LOCALS JVM::thread-top-frame jvm::make-state JVM::CALL-STACK JVM::THREAD-TABLE))))

;; (defthm stack-lemma
;;   (equal (JVM::stack (JVM::thread-top-frame th (JVM::MAKE-STATE (JVM::BIND th (LIST cs status blah) tt) h ct hrt sfm ic)))
;;          (JVM::stack  (JVM::TOP CS)))
;;   :hints (("Goal" :in-theory (enable JVM::LOCALS JVM::thread-top-frame jvm::make-state JVM::CALL-STACK JVM::THREAD-TABLE))))

;; (defthm program-lemma
;;   (equal (JVM::program (JVM::thread-top-frame th (JVM::MAKE-STATE (JVM::BIND th (LIST cs status blah) tt) h ct hrt sfm ic)))
;;          (JVM::program  (JVM::TOP CS)))
;;   :hints (("Goal" :in-theory (enable JVM::LOCALS JVM::thread-top-frame jvm::make-state JVM::CALL-STACK JVM::THREAD-TABLE))))

;; (defthm sync-flag-lemma
;;   (equal (JVM::sync-flag (JVM::thread-top-frame th (JVM::MAKE-STATE (JVM::BIND th (LIST cs status blah) tt) h ct hrt sfm ic)))
;;          (JVM::sync-flag  (JVM::TOP CS)))
;;   :hints (("Goal" :in-theory (enable JVM::LOCALS JVM::thread-top-frame jvm::make-state JVM::CALL-STACK JVM::THREAD-TABLE))))

;; (defthm call-stack-of-make-state
;;   (equal (JVM::CALL-STACK th (JVM::MAKE-STATE (JVM::BIND th (CONS callstack (cons status nil)) threadtable) heap classtable hrt sfm ic))
;;          callstack)
;;   :hints (("Goal" :in-theory (enable JVM::CALL-STACK JVM::MAKE-STATE JVM::THREAD-TABLE))))

;BOZO add equality destructor rules!

;; (defun jvm::replace-operand-stack (new-operand-stack frame)
;;   (jvm::make-frame (jvm::pc frame)
;;                   (jvm::locals frame)
;;                   new-operand-stack
;;                   (jvm::program frame)
;;                   (jvm::sync-flag frame)
;;                   (jvm::method-designator frame)))

;drop?
(defun jvm::pop-call-stack (th s)
  (jvm::pop-frame (jvm::call-stack th s)))

;drop?
(defun jvm::pop-call-stack-twice (th s)
  (jvm::pop-frame (jvm::pop-frame (jvm::call-stack th s))))

;drop?
;do we already have stuff like this?
(defun jvm::second-call-frame (th s)
  (jvm::top-frame (jvm::pop-frame (jvm::call-stack th s))))

;; (defun jvm::local0 (frame)
;;   (nth 0 (jvm::locals frame)))

;; (defun jvm::local1 (frame)
;;   (nth 1 (jvm::locals frame)))

;; (defun pop-frame-and-push-return-value (return-value th s)
;;   (jvm::modify th
;;               s
;;               :call-stack
;;               (jvm::push-frame
;;                (jvm::replace-operand-stack (jvm::push-operand return-value
;;                                                     (jvm::stack (jvm::second-call-frame th s)))
;;                                           (jvm::second-call-frame th s))
;;                (jvm::pop-call-stack-twice th s))))

;drop?
;don't push any return value. used for void methods.
;fixme name clash with jvm::pop-frame
;; (defun pop-frame (th s)
;;   (jvm::modify th
;;               s
;;               :call-stack
;;               (jvm::pop-call-stack th s)))

;; (defthm integerp-tighten
;;   (implies (and (< y x)
;;                 (integerp x)
;;                 (integerp y)
;;                 )
;;            (equal (<= x (+ 1 y))
;;                   (equal x (+ 1 y)))))

;; (defthm update-nth-hack
;;   (implies (and (natp n) ;(consp x)
;;                 (< n (len x)))
;;            (equal (UPDATE-NTH n (nth n x) x)
;;                   x))
;;   :hints (("Goal" :in-theory (enable nth)
;;            :do-not '(generalize eliminate-destructors))))

;; (defthm update-nth-hack
;;   (implies (and (natp n) ;(consp x)
;;                 (< n (len x)))
;;            (equal (UPDATE-NTH 1 (cadr x) x)
;;                   x))
;;   :hints (("Goal" :in-theory (enable nth)
;;            :do-not '(generalize eliminate-destructors))))



;disable nth?
;BOZO add to rockwell's update-nth library?
;; [Jared] removing because it's redundant with sequences/seq2, which is
;; already included
;; (defthm cdr-of-update-nth
;;   (equal (cdr (update-nth n val list))
;;          (if (zp n)
;;              (cdr list)
;;            (update-nth (+ -1 n) val (cdr list))))
;;   :hints (("Goal" :in-theory (enable update-nth))))


;; (defmacro local_0 (s)
;;   `(jvm::local0 (jvm::thread-top-frame (th) ,s)))

;; (defmacro local_1 (s)
;;   `(jvm::local1 (jvm::thread-top-frame (th) ,s)))

;; (defmacro local_2 (s)
;;   `(nth 2 (jvm::locals (jvm::thread-top-frame (th) ,s))))

;; ;bozo think more about this
;; ;is this still used?
;; (defund cast-boolean-to-int (x)
;;   (if (equal x t)
;;       1
;;     (if (equal x nil)
;;         0
;;       x)))

;; (defthm cast-boolean-to-int-of-boolean-equal-1-rewrite
;;   (implies (booleanp foo)
;;            (equal (equal 1 (cast-boolean-to-int foo))
;;                   foo))
;;   :hints (("Goal" :in-theory (enable cast-boolean-to-int))))

;; (defthm CAST-BOOLEAN-TO-INT-of-boolean-equal-0-rewrite
;;   (implies (booleanp foo)
;;            (equal (EQUAL 0 (CAST-BOOLEAN-TO-INT foo))
;;                   (not foo)))
;;   :hints (("Goal" :in-theory (enable CAST-BOOLEAN-TO-INT))))

;; ;BOZO redo things to get rid of this?
;; (defthm cast-boolean-to-int-does-nothing
;;   (implies (integerp x)
;;            (equal (cast-boolean-to-int x)
;;                   x))
;;   :hints (("Goal" :in-theory (enable cast-boolean-to-int))))










;; (defthm equal-myif-false
;;   (implies (and (not (equal val1 val3))
;;                 (not (equal val2 val3)))
;;            (equal (EQUAL (MYIF test val1 val2)
;;                          val3)
;;                   nil))
;;   :hints (("Goal" :in-theory (enable myif))))

;; (defthm <-myif-true
;;   (implies (and (< val3 val1)
;;                 (< val3 val2))
;;            (equal (< val3
;;                      (MYIF test val1 val2))
;;                   t))
;;   :hints (("Goal" :in-theory (enable myif))))

;; (defthm <-myif-true-2
;;   (implies (and (< val1 val3)
;;                 (< val2 val3))
;;            (equal (< (MYIF test val1 val2)
;;                      val3)
;;                   t))
;;   :hints (("Goal" :in-theory (enable myif))))

;; (defthm <-myif-false
;;   (implies (and (not (< val3 val1))
;;                 (not (< val3 val2)))
;;            (equal (< val3
;;                      (MYIF test val1 val2))
;;                   nil))
;;   :hints (("Goal" :in-theory (enable myif))))


;; (MOD (+ -1 X) 4294967296)

;; (thm
;;  (IMPLIES (AND (EQUAL (MOD X 4294967296) 2147483648)
;;                (INTEGERP X)
;;                (<= -2147483648 X)
;;                (< X 2147483648)
;;                (NOT (INTEGERP (* 1/4294967296 X))))
;;           (EQUAL X 2147483648)))

;; (defthm step-when-myif-is-around-pc
;;   (equal (JVM::STEP th
;;                    (JVM::MAKE-STATE
;;                     (JVM::BIND th
;;                               (JVM::MAKE-THREAD
;;                                (JVM::PUSH-FRAME
;;                                 (JVM::MAKE-FRAME
;;                                  (MYIF test pc1 pc2)
;;                                  locals stack method-info method-designator) rest)) tt)
;;                     heap ct))
;;          (myif test
;;                (JVM::STEP th
;;                          (JVM::MAKE-STATE
;;                           (JVM::BIND th
;;                                     (JVM::MAKE-THREAD
;;                                      (JVM::PUSH-FRAME
;;                                       (JVM::MAKE-FRAME
;;                                        pc1
;;                                        locals stack method-info method-designator) rest)) tt)
;;                           heap ct))
;;                (JVM::STEP th
;;                          (JVM::MAKE-STATE
;;                           (JVM::BIND th
;;                                     (JVM::MAKE-THREAD
;;                                      (JVM::PUSH-FRAME
;;                                       (JVM::MAKE-FRAME
;;                                        pc2
;;                                        locals stack method-info method-designator) rest)) tt)
;;                           heap ct))))
;;   :hints (("Goal" :in-theory (union-theories '(myif) (theory 'minimal-theory)))))

;; ;drop?
;; (defun heap (s)
;;   (declare (xargs :guard (jvm::jvm-statep s)))
;;   (jvm::heap s))

;(defopeners jvm::initialize-one-dim-arrays)

;; (defthm initialize-one-dim-arrays-opener
;;   (implies (consp jvm::addrs)
;;            (equal (jvm::initialize-one-dim-arrays jvm::addrs type contents jvm::heap)
;;                   (jvm::initialize-one-dim-array
;;                    (car jvm::addrs)
;;                    type contents
;;                    (jvm::initialize-one-dim-arrays
;;                     (cdr jvm::addrs)
;;                     type contents jvm::heap))))
;;   :hints (("Goal" :in-theory (enable jvm::initialize-one-dim-arrays))))

;; (defthm initialize-one-dim-arrays-base
;;   (implies (not (consp jvm::addrs))
;;            (equal (jvm::initialize-one-dim-arrays jvm::addrs type contents jvm::heap)
;;                   jvm::heap))
;;   :hints (("Goal" :in-theory (enable jvm::initialize-one-dim-arrays))))

;; ;drop in favor of myif-of-make-state-and-make-state?
;; ;i guess the current approach is to push the if into the state components (so that at join points the branches will converge) but to lift the myif back out if the pcs differ?
;; ;why does that not loop? oh, because this requires the thread-tables to be the same -- too drastic?  what about changes to locals or stack? see myif-of-make-state-and-make-state above
;; ;fixme only do this when the current method and pc on the two branches are the same?
;; (defthm myif-make-states-recombine3
;;   (equal (myif test
;;                (jvm::make-state tt h1 ct1 hrt1 monitor-table1 sfm1 ic1 intern-table1)
;;                (jvm::make-state tt h2 ct2 hrt2 monitor-table2 sfm2 ic2 intern-table2))
;;          (jvm::make-state tt
;;                          (myif test h1 h2)
;;                          (myif test ct1 ct2)
;;                          (myif test hrt1 hrt2)
;;                          (myif test monitor-table1 monitor-table2)
;;                          (myif test sfm1 sfm2)
;;                          (myif test ic1 ic2)
;;                          (myif test  intern-table1 intern-table2)))
;;   :hints (("Goal" :in-theory (enable myif))))

;this might make proofs harder to debug, since the make-states are gone, but it might make things easier by reducing the size of the conclusion...
;dup?
(defthm make-state-equal-rewrite
  (equal (equal (jvm::make-state tt h ct hrt monitor-table sfm ic intern-table) (jvm::make-state tt2 h2 ct2 hrt2 monitor-table2 sfm2 ic2 intern-table2))
         (and (equal tt tt2)
              (equal h h2)
              (equal hrt hrt2)
              (equal monitor-table monitor-table2)
              (equal ct ct2)
              (equal sfm sfm2)
              (equal ic ic2)
              (equal intern-table intern-table2)))
  :hints (("Goal" :in-theory (e/d (jvm::make-state) (SET::DOUBLE-CONTAINMENT ;fixme
                                                    SET::DOUBLE-CONTAINMENT-EXPENSIVE
                                                    )))))

;dup?
(defthm reduce-make-state-equality-when-all-but-thread-tables-match
   (equal (equal (jvm::make-state thread-table heap class-table hrt monitor-table sfm ic intern-table)
                 (jvm::make-state thread-table2 heap class-table hrt monitor-table sfm ic intern-table))
          (equal thread-table thread-table2)))

(defopeners-mut-rec jvm::lookup-field
  :hyps ((syntaxp (quotep jvm::c))
         (syntaxp (quotep jvm::field-id))))

(defthm clr-of-initialize-one-dim-array-same
  (equal (clr ad (jvm::initialize-one-dim-array ad type contents heap))
         (clr ad heap))
  :hints (("Goal" :in-theory (e/d (JVM::INITIALIZE-ONE-DIM-ARRAY) ()))))

(defopeners gen-init-bindings)

(defopeners gen-init-bindings-for-class)

(defthmd strip-cars-opener
  (implies (not (endp bindings))
           (equal (strip-cars bindings)
                  (cons (caar bindings)
                        (strip-cars (cdr bindings)))))
  :hints (("Goal" :in-theory (enable strip-cars))))

;; (defun get-pc (s)
;;   (jvm::pc (jvm::thread-top-frame (th) s)))

;; do we still need this?
(defthm consp-of-push-frame
  (consp (jvm::push-frame x y)))

;todo: drop
(defun set-field-in-state (ad class-name-field-name-pair val s)
  (jvm::modify :dummy ;the thread is not used
               s
              :heap
              (set-field ad class-name-field-name-pair val (jvm::heap s))))

(defun update-local-in-state (localnum val th s)
  (jvm::modify th s :locals (jvm::update-nth-local localnum val (jvm::locals (jvm::thread-top-frame th s)))))

;return get contents of 1D array as a list
;bozo go back and generate calls to this for $contents
;; (defun array-contents (ref heap)
;;   (acl2::get-field ref '("ARRAY" . "contents") heap))

(defun jvm::array-element-range (start end arrayref heap)
  (subrange start end (array-contents arrayref heap)))

;move to a sequences library or drop the rule?
;(in-theory (disable JVM::NTH-OPENER)) ;BOZO trying...

;allow alists to differ?
(defthm bind-equal-bind-reduce
  (equal (equal (jvm::bind x y alist) (jvm::bind x y2 alist))
         (equal y y2))
  :hints (("Goal" :in-theory (enable jvm::bind))))

;move
;newly disabled
(defthmd bind-what-was-already-there
  (implies (and (assoc-equal key alist)
                (alistp alist)
                (equal v (cdr (assoc-equal key alist))))
           (equal (jvm::bind key v alist)
                  alist))
  :hints (("Goal" :in-theory (enable jvm::bind assoc-equal))))

;move
(defthm alistp-of-bind
  (implies (alistp alist)
           (equal (alistp (JVM::BIND x y alist))
                  t))
  :hints (("Goal" :in-theory (enable JVM::BIND alistp))))

(defthm do-inst-of-myif
  (equal (jvm::do-inst (myif test op-code1 op-code2) inst th s)
         (myif test (jvm::do-inst op-code1 inst th s)
               (jvm::do-inst op-code2 inst th s)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm thread-classp-returns-false
  (implies (and (not (equal class-name "java.lang.Thread"))
                (not (equal class-name "java.lang.ThreadGroup")) ;why?
                (not (member-equal "java.lang.Thread" (get-super-classes class-name class-table)))
                (not (member-equal "java.lang.ThreadGroup" (get-super-classes class-name class-table))) ;why?
                )
           (equal (jvm::thread-classp class-name class-table)
                  nil))
  :hints (("Goal" :in-theory (enable jvm::thread-classp))))

(defthm lookup-method-in-classes-base
  (implies (not (consp class-names))
           (equal (jvm::lookup-method-in-classes method-id class-names class-table)
                  nil))
  :hints (("Goal" :in-theory (enable jvm::lookup-method-in-classes))))

;rename?
(defthm lookup-method-in-classes-peel-off-one
  (implies (and (syntaxp (and (quotep class-names)
                              (quotep method-id)))
                (consp class-names)
                ;; a binding hyp:
                (equal first-name (car class-names)) ;bind first-name to the result of rewriting (car class-names)
                (equal (jvm::get-class-info first-name class-table)
                       free)
                (syntaxp (quotep free)))
           (equal (jvm::lookup-method-in-classes method-id class-names class-table)
                  (if (acl2::lookup-equal method-id (jvm::class-decl-methods (jvm::get-class-info (car class-names) class-table)))
                      (cons (acl2::lookup-equal method-id (jvm::class-decl-methods (jvm::get-class-info (car class-names) class-table)))
                            (car class-names))
                    (jvm::lookup-method-in-classes method-id (cdr class-names) class-table))))
  :hints (("Goal" :in-theory (enable jvm::lookup-method-in-classes))))

;; This version is for Axe and doesn't have a binding hyp.
(defthmd lookup-method-in-classes-peel-off-one-axe
  (implies (and (syntaxp (and (quotep class-names)
                              (quotep method-id)))
                (consp class-names))
           (equal (jvm::lookup-method-in-classes method-id class-names class-table)
                  (let ((res (jvm::lookup-method-in-class-info method-id (car class-names) (jvm::get-class-info (car class-names) class-table))))
                    (if res
                        res
                      (jvm::lookup-method-in-classes method-id (cdr class-names) class-table)))))
  :hints (("Goal" :in-theory (enable jvm::lookup-method-in-classes))))

;Avoid splitting
(defthm lookup-method-in-classes-of-cons-1
  (implies (jvm::lookup-method-in-class-info method-id class-name (jvm::get-class-info class-name class-table))
           (equal (jvm::lookup-method-in-classes method-id (cons class-name class-names) class-table)
                  (jvm::lookup-method-in-class-info method-id class-name (jvm::get-class-info class-name class-table))))
  :hints (("Goal" :in-theory (enable jvm::lookup-method-in-classes))))

;Avoid splitting
(defthm lookup-method-in-classes-of-cons-2
  (implies (not (jvm::lookup-method-in-class-info method-id class-name (jvm::get-class-info class-name class-table)))
           (equal (jvm::lookup-method-in-classes method-id (cons class-name class-names) class-table)
                  (jvm::lookup-method-in-classes method-id class-names class-table)))
  :hints (("Goal" :in-theory (enable jvm::lookup-method-in-classes))))


;; (defun heapref-for-class (class-name s)
;;   (jvm::get-class-info class-name (jvm::heapref-table s))
;; ;  (JVM::CLASS-DECL-HEAPREF (jvm::get-class-info class-name (JVM::CLASS-TABLE S)))
;; )

;; (defthm get-field-of-initialize-one-dim-arrays-irrel
;;  (implies (not (memberp ad ads))
;;           (equal (get-field ad pair (jvm::initialize-one-dim-arrays ads type contents heap))
;;                  (get-field ad pair heap)))
;;  :hints (("Goal" :in-theory (enable HEAD-NOT))))

;; (defthm get-contents-after-initialize-one-dim-arrays-memberp
;;   (implies (memberp ad ads)
;;            (equal (get-field ad (array-contents-pair) (jvm::initialize-one-dim-arrays ads type contents heap))
;;                   contents))
;;  :hints (("Goal" :in-theory (enable jvm::initialize-one-dim-arrays))))

;; (defthm get-length-after-initialize-one-dim-arrays-memberp
;;   (implies (memberp ad ads)
;;            (equal (array-length ad (jvm::initialize-one-dim-arrays ads type contents heap))
;;                   (len contents)))
;;   :hints (("Goal" :in-theory (enable jvm::initialize-one-dim-arrays))))

;; (defthm get-class-of-initialize-2d-array
;;   (equal (get-class ad (jvm::initialize-2d-array ad type outercount innercount heap))
;;          (jvm::make-one-dim-array-type (jvm::make-one-dim-array-type type)))
;;   :hints (("Goal" :in-theory (enable get-class))))

;; (defthm get-class-field-of-initialize-2d-array
;;   (equal (get-field ad (class-pair) (jvm::initialize-2d-array ad type outercount innercount heap))
;;          (jvm::make-one-dim-array-type (jvm::make-one-dim-array-type type))))

(defopeners jvm::initialize-static-fields)

;; (defthm initialize-static-fields-base
;;   (implies (endp jvm::static-fields)
;;            (equal (jvm::initialize-static-fields jvm::static-fields class-name jvm::static-field-map)
;;                   jvm::static-field-map)))

;; (defthm initialize-static-fields-unroll
;;   (implies (not (endp jvm::static-fields))
;;            (equal (jvm::initialize-static-fields jvm::static-fields class-name jvm::static-field-map)
;;                   (let*
;;                       ((jvm::field-info (car jvm::static-fields))
;;                        (jvm::field-name (car jvm::field-info))
;;                        (jvm::field-descriptor (cdr jvm::field-info))
;;                        (jvm::default-value (default-value jvm::field-descriptor))
;;                        (jvm::pair (cons class-name jvm::field-name)))
;;                     (jvm::initialize-static-fields (cdr jvm::static-fields)
;;                                                   class-name
;;                                                   (s jvm::pair jvm::default-value
;;                                                      jvm::static-field-map))))))

;; (defthm program-when-method-info-known
;;   (implies (equal free (jvm::method-info frame))


;; (defthm consp-when-pop-known
;;   (implies (and (equal (jvm::pop x) free)
;;                 (consp free)
;;                 )
;;            (equal (consp x)
;;                   t))
;;   :hints (("Goal" :in-theory (enable jvm::pop))))

;; (defthm len-when-pop-known
;;   (implies (and (equal (jvm::pop x) free)
;;                 )
;;            (equal (len x)
;;                   (if (consp x)
;;                       (+ 1 (len free))
;;                     0))))

(defthm lookup-method-of-singleton
  (equal (jvm::lookup-method-in-classes name-params-pair (list class-name) class-table)
         (if (lookup-equal name-params-pair (jvm::class-decl-methods (jvm::get-class-info class-name class-table)))
             (cons (lookup-equal name-params-pair
                                 (jvm::class-decl-methods (jvm::get-class-info class-name class-table)))
                   class-name)
           nil))
  :hints (("Goal" :in-theory (enable jvm::lookup-method-in-classes))))

(defthm top-frame-lemma
  (implies t;(syntaxp (quotep tt)) ;drop?
           (equal (JVM::thread-top-frame TH (JVM::MAKE-STATE tt x y z w a b intern-table))
                  (jvm::top-frame (jvm::binding th tt))))
  :hints (("Goal" :in-theory (enable JVM::thread-top-frame))))

(in-theory (disable jvm::get-static-field jvm::set-static-field))

(defthm get-static-field-of-set-static-field-same
  (equal (jvm::get-static-field class-name field-name (jvm::set-static-field class-name field-name value static-field-map))
         value)
  :hints (("Goal" :in-theory (enable jvm::get-static-field jvm::set-static-field))))

(defthm get-static-field-of-set-static-field-diff
  (implies (or (not (equal class-name1 class-name2))
               (not (equal field-name1 field-name2)))
           (equal (jvm::get-static-field class-name1 field-name1 (jvm::set-static-field class-name2 field-name2 value static-field-map))
                  (jvm::get-static-field class-name1 field-name1 static-field-map)))
  :hints (("Goal" :in-theory (enable jvm::get-static-field jvm::set-static-field))))

(defthm set-static-field-of-set-static-field-same
  (equal (jvm::set-static-field class-name field-name value1 (jvm::set-static-field class-name field-name value2 static-field-map))
         (jvm::set-static-field class-name field-name value1 static-field-map))
  :hints (("Goal" :in-theory (enable jvm::get-static-field jvm::set-static-field))))

;; We sort first by class name
(defthm set-static-field-of-set-static-field-diff-class
  (implies (and (syntaxp (acl2::smaller-termp class-name2 class-name1))
                (not (equal class-name1 class-name2)))
           (equal (jvm::set-static-field class-name1 field-name1 value1 (jvm::set-static-field class-name2 field-name2 value2 static-field-map))
                  (jvm::set-static-field class-name2 field-name2 value2 (jvm::set-static-field class-name1 field-name1 value1 static-field-map))))
  :hints (("Goal" :in-theory (enable jvm::get-static-field jvm::set-static-field))))

;; We sort second by field name (so here the class names must be the same)
(defthm set-static-field-of-set-static-field-diff-field
  (implies (and (syntaxp (acl2::smaller-termp field-name2 field-name1))
                (not (equal field-name1 field-name2)))
           (equal (jvm::set-static-field class-name field-name1 value1 (jvm::set-static-field class-name field-name2 value2 static-field-map))
                  (jvm::set-static-field class-name field-name2 value2 (jvm::set-static-field class-name field-name1 value1 static-field-map))))
  :hints (("Goal" :in-theory (enable jvm::get-static-field jvm::set-static-field))))

;; Helps prevent case splits:
(defopeners jvm::type-implementsp :hyps ((syntaxp (quotep jvm::type-s)) (syntaxp (quotep jvm::type-t))))

(defopeners jvm::resolve-method-step-2-aux)
