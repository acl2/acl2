(in-package "ACL2")

#||

  reflexive-macros.lisp
  ~~~~~~~~~~~~~~~~~~~~~

Author: Sandip Ray
Date: Wed Aug  8 13:48:22 2007

In this book, we develop a series of macros, for automating the
introduction of reflexive functions as shown in the book
reflexive-theory.lisp.  Our simplest macro defreflexive is the most
generic --- it does very little more than just a simple functional
instantiation.  We then build up on that macro to develop more
interesting macros for specific domains.


||#

(defun snoc (x e)
  (if (endp x) (list e)
    (cons (first x) (snoc (rest x) e))))

(defun lastval (x)
  (cond ((endp x) nil)
        ((endp (rest x)) (first x))
        (t (lastval (rest x)))))


;; The first version of the macro attempt.  This supports functions
;; with either one or two arguments only.  In a later function we will
;; use this to get rid of the restriction, but this is a first step.

(defun defreflexive-fn-two-params
  (run btm x st test1 test2 dst1 dst2 finish step
       rule-classes executable guard verify-guards)
  (declare (xargs :mode :program))
  (let* ((run-clk (packn (list run '-clk)))
         (run-def (packn (list run '-def)))
         (run-executable (packn (list run '-executable)))
         (run-executable-def (packn (list run-executable '-def)))
         (st2 (lastval dst2))
         (dst2term `(let ((st2 ,st2))
                      ,dst2))

         ;; Here is the key definitional axiom introduced in the
         ;; logic.  We of course allow the axiom to be introduced by
         ;; any other rule-class, not just a :definition rule.
         (logic-events

          `(encapsulate
            (((,run * *) => *))

            (set-ignore-ok t)
            (set-irrelevant-formals-ok t)

            (local (defthm finish-is-not-btm
                     (implies (not (equal ,st ,btm))
                              (not (equal ,finish ,btm)))
                     :rule-classes nil))

            (local
             (defun ,run-clk (,x ,st clk)
               (declare (xargs :measure (nfix clk)
                               :normalize nil))
               (cond ((zp clk) ,btm)
                     ((equal ,st ,btm) ,btm)
                     (,test1 ,finish)
                     (,test2
                      (,run-clk ,dst1
                                ,step
                                (1- clk)))
                     (t (let ((st2 (,run-clk ,dst1
                                             ,step
                                             (1- clk))))
                          (if (equal st2 ,btm)
                              ,btm
                            (,run-clk ,dst2term st2 (1- clk))))))))

            (local
             (defun-sk exists-enough-clk (,x ,st)
               (exists clk
                       (and (natp clk)
                            (not (equal (,run-clk ,x ,st clk)
                                        ,btm))))))
            (local
             (defun ,run (,x ,st)
               (if (exists-enough-clk ,x ,st)
                   (,run-clk ,x ,st
                             (exists-enough-clk-witness ,x ,st))
                 ,btm)))

            (local (include-book "reflexive"))


            (defthm ,run-def
              (equal (,run ,x ,st)
                     (cond ((equal ,st ,btm) ,btm)
                           (,test1 ,finish)
                           (,test2
                            (,run ,dst1 ,step))
                           (t (let ((st2 (,run ,dst1 ,step)))
                                (,run ,dst2term st2)))))
              :rule-classes ,rule-classes
              :hints
              (("Goal"
                :in-theory (theory 'minimal-theory)
                :use ((:instance
                       (:functional-instance
                        |definition of generic-run|
                        (generic-run
                         (lambda (x st)
                           (let ((,x x)
                                 (,st st))
                             (,run ,x ,st))))
                        (generic-run-clk
                         (lambda (x st clk)
                           (let ((,x x)
                                 (,st st))
                             (,run-clk ,x ,st clk))))
                        (exists-enough
                         (lambda (x st)
                           (let ((,x x)
                                 (,st st))
                             (exists-enough-clk ,x ,st))))
                        (exists-enough-witness
                         (lambda (x st)
                           (let ((,x x)
                                 (,st st))
                             (exists-enough-clk-witness ,x ,st))))
                        (generic-btm (lambda () ,btm))
                        (generic-test1 (lambda (x st)
                                         (let ((,x x)
                                               (,st st))
                                           ,test1)))
                        (generic-test2
                         (lambda (x st)
                           (let ((,x x)
                                 (,st st))
                             ,test2)))
                        (generic-finish
                         (lambda (x st)
                           (let ((,x x)
                                 (,st st))
                             ,finish)))
                        (generic-dst1
                         (lambda (x st)
                           (let ((,x x)
                                 (,st st))
                             ,dst1)))
                        (generic-dst2
                         (lambda (x st st2)
                           (let ((,x x)
                                 (,st st))
                             ,dst2)))
                        (generic-step (lambda (x st)
                                        (let ((,x x)
                                              (,st st))
                                          ,step))))
                       (x ,x)
                       (st ,st))
                      (:instance ,run)))
              ("Subgoal 5"
               :use ((:instance finish-is-not-btm
                                (,x x)
                                (,st st))))
              ("Subgoal 4"
               :use ((:instance (:definition ,run)
                                (,x x)
                                (,st st))))
              ("Subgoal 3"
               :use ((:instance (:definition ,run-clk)
                                (,x x)
                                (,st st))))
              ("Subgoal 2"
               :use ((:instance exists-enough-clk-suff
                                (,x x)
                                (,st st))))
              ("Subgoal 1"
               :use ((:instance (:definition exists-enough-clk)
                                (,x x)
                                (,st st))))))))

         (exec-events
          `(encapsulate
            ()

            (defun ,run-executable (,x ,st)
              (declare (xargs :guard ,guard
                              :verify-guards nil))
              (mbe :logic (,run ,x ,st)
                   :exec
                   (cond ((equal ,st ,btm) ,btm)
                         (,test1 ,finish)
                         (,test2
                          (,run-executable ,dst1 ,step))
                         (t (let ((st2 (,run-executable ,dst1 ,step)))
                              (,run-executable ,dst2term st2))))))

            (local (in-theory (theory 'ground-zero)))

            (defthm ,run-executable-def
              (equal (,run-executable ,x ,st)
                     (cond ((equal ,st ,btm) ,btm)
                           (,test1 ,finish)
                           (,test2
                            (,run-executable ,dst1 ,step))
                           (t (let ((st2 (,run-executable ,dst1 ,step)))
                                (,run-executable ,dst2term st2)))))
              :rule-classes ,rule-classes
              :hints (("Goal"
                       :in-theory (enable ,run-executable)
                       :use ((:instance ,run-def))))))))
    (if executable
        (if verify-guards
            `(progn ,logic-events
                    ,exec-events
                    (verify-guards
                     ,run-executable
                     :hints (("Goal"
                              :in-theory (enable ,run-executable)
                              :use ((:instance ,run-def))))))

          `(progn ,logic-events
                  ,exec-events))
      `(progn ,logic-events))))



(defun defreflexive-fn-special
  (run x st bottom test1 finish test2 rec-mod dst2 rule-classes
       executable guard verify-guards)
  (declare (xargs :mode :program))
  (let ((dst1 (first rec-mod))
        (step (second rec-mod)))
  (defreflexive-fn-two-params
    run bottom x st
    (cons test1 (list x st))
    (cons test2 (list x st))
    (cons dst1 (list x st))
    (cons dst2 (list x st 'st2))
    (cons finish (list x st))
    (cons step (list x st))
    rule-classes
    executable
    guard verify-guards)))

(defmacro defreflexive-special
  (run x st
       &key
       (bottom 'nil)
       (base-test 'test1)
       (base-case 'finish)
       (recursive-test 'test2)
       (recursive-modifier '(dst1 stp))
       (reflexive-modifier 'dst2)
       (rule-classes ':definition)
       (executable 'nil)
       (guard 't)
       (verify-guards 'nil))

  (defreflexive-fn-special run x st bottom
    base-test base-case recursive-test recursive-modifier
    reflexive-modifier
    rule-classes executable guard verify-guards))

;; Now we test the macro.

(encapsulate
 ()

 (set-ignore-ok t)
 (set-irrelevant-formals-ok t)
 (local (defun test1 (p q) (and (natp p) (natp q))))
 (local (defun test2 (p q) (and (natp p) (natp q))))
 (local (defun dst1 (p q) (+ (1- p) (1- q))))
 (local (defun dst2 (p q r) (+ (1- p) (1- q) (1- r))))
 (local (defun stp (m n) (+ (1- m) (1+ n))))
 (local (defun finish (a b) (+ a b)))
 (local (defreflexive-special run-fn a b
          :rule-classes nil)))


(encapsulate
 ()

 (set-ignore-ok t)
 (set-irrelevant-formals-ok t)
 (local (defun test1 (p q) (and (natp p) (natp q))))
 (local (defun test2 (p q) (and (natp p) (natp q))))
 (local (defun dst1 (p q) (+ (1- p) (1- q))))
 (local (defun dst2 (p q r) (+ (1- p) (1- q) (1- r))))
 (local (defun stp (m n) (+ (1- m) (1+ n))))
 (local (defun finish (a b) (+ a b)))
 (local (defreflexive-special run-fn a b
          :rule-classes :definition)))


(encapsulate
 ()
 (set-ignore-ok t)
 (set-irrelevant-formals-ok t)

 (local (defun test1 (p q) (declare (ignore p q)) t))
 (local (defun test2 (p q) (declare (ignore p q)) nil))
 (local (defun dst1 (p q) (declare (ignore p q)) 2))
 (local (defun dst2 (p q r) (declare (ignore p q r)) 3))
 (local (defun stp (m n) (declare (ignore m n)) 3))
 (local (defun finish (c d) (declare (ignore c d)) t))
 (local (verify-guards test1))
 (local (verify-guards test2))
 (local (verify-guards dst1))
 (local (verify-guards dst2))
 (local (verify-guards stp))
 (local (verify-guards finish))

 (local
  (defreflexive-special run-fn a b
    :executable t
    :guard t
    :verify-guards t
    :rule-classes nil)))

(encapsulate
 ()
 (set-ignore-ok t)
 (set-irrelevant-formals-ok t)

 (local (defun tst1 (p q) (declare (ignore p q)) t))
 (local (defun tst2 (p q) (declare (ignore p q)) nil))
 (local (defun dest1 (p q) (declare (ignore p q)) 2))
 (local (defun dest2 (p q r) (declare (ignore p q r)) 3))
 (local (defun next (m n) (declare (ignore m n)) 3))
 (local (defun finish-off (c d) (declare (ignore c d)) t))
 (local (verify-guards tst1))
 (local (verify-guards tst2))
 (local (verify-guards dest1))
 (local (verify-guards dest2))
 (local (verify-guards next))
 (local (verify-guards finish-off))

 (local
  (defreflexive-special run-fn a b
    :base-test tst1
    :base-case finish-off
    :recursive-test tst2
    :recursive-modifier (dest1 next)
    :reflexive-modifier dest2
    :executable t
    :guard t
    :verify-guards t
    :rule-classes nil)))

;; We now move on to the definterpreter macro.

;; The problem is a bit complicated for the vanilla ops, in comparison
;; to the conditional, sequence, and while operations.  The reason has
;; got to do with the interface that I have imagined.  In particular,
;; we need to deal here with "a list of alists", rather than just "an
;; alist".  So I first separate out the different things in the list
;; of alists, so that I can recur on separate lists in lock-step.

(defun find-field-val (key alst)
  (cond ((endp alst) (mv nil nil))
        ((eq key (first (first alst))) (mv t (second (first alst))))
        (t (find-field-val key (rest alst)))))

(defun find-list-val (key alst-lst default)
  (if (endp alst-lst) nil
    (mv-let (flg val)
            (find-field-val key (first alst-lst))
            (cons (if (not flg) default val)
                  (find-list-val key (rest alst-lst) default)))))

;; So now here is our different lists.

(defun find-operator-names (vanilla-interpreter)
  (find-list-val :name vanilla-interpreter nil))

(defun find-execution-terms (vanilla-interpreter mem)
  (find-list-val :interpreter vanilla-interpreter mem))

(defun find-guard-terms (vanilla-interpreter)
  (find-list-val :guard vanilla-interpreter t))

;; Now let's do the relatively simpler ones, namely the sequence,
;; conditional, and while.

(defun find-alist-flds (fld alst default)
  (if (not alst) nil
    (mv-let (flg val)
            (find-field-val fld alst)
            (if flg val default))))

(defun find-sequence-name (sequence)
  (find-alist-flds :name sequence 'sequence))

(defun find-sequence-arg1 (sequence)
  (find-alist-flds :arg1 sequence nil))

(defun find-sequence-arg2 (sequence)
  (find-alist-flds :arg2 sequence nil))

(defun find-conditional-name (conditional)
  (find-alist-flds :name conditional 'if))

(defun find-conditional-test (conditional)
  (find-alist-flds :test conditional nil))

(defun find-conditional-tbr (conditional)
  (find-alist-flds :tbr conditional nil))

(defun find-conditional-fbr (conditional)
  (find-alist-flds :fbr conditional nil))

(defun find-while-name (loop-struct)
  (find-alist-flds :name loop-struct 'while))

(defun find-while-test (loop-struct)
  (find-alist-flds :test loop-struct nil))

(defun find-while-body (loop-struct)
  (find-alist-flds :body loop-struct nil))

;; We have now set up the infrastructure to write the major functions
;; in the macro.  We now do so, namely, write functions to generate
;; the different definition bodies for test1, dst1, etc.

(defun vanilla-test1-body (ops-list)
  (if (endp ops-list)
      nil
    (cons (list (first ops-list) t)
          (vanilla-test1-body (rest ops-list)))))

(defun test1-body (op-field ops-list while sequence conditional)
  (let* ((test-body (vanilla-test1-body ops-list))
         (test-body
          (if sequence
              (snoc test-body (list (find-sequence-name sequence)
                                    nil))
            test-body))
         (test-body
          (if conditional
              (snoc test-body (list (find-conditional-name conditional)
                                    nil))
            test-body))
         (test-body
          (if while
              (snoc test-body (list (find-while-name while)
                                    (find-while-test while)))
            test-body))
         (test-body (snoc test-body `(otherwise t))))
    `(case ,op-field
       ,@test-body)))

(defun vanilla-test2-body (ops-list)
  (if (endp ops-list)
      nil
    (cons (list (first ops-list) nil)
          (vanilla-test2-body (rest ops-list)))))

(defun test2-body (op-field ops-list while sequence conditional)
  (let* ((test-body (vanilla-test2-body ops-list))
         (test-body
          (if sequence
              (snoc test-body (list (find-sequence-name sequence)
                                    nil))
            test-body))
         (test-body
          (if conditional
              (snoc test-body (list (find-conditional-name conditional)
                                    t))
            test-body))
         (test-body
          (if while
              (snoc test-body (list (find-while-name while)
                                    nil))
            test-body))
         (test-body (snoc test-body `(otherwise nil))))
    `(case ,op-field
       ,@test-body)))

(defun vanilla-dst1-body (ops-list stmt)
  (if (endp ops-list)
      nil
    (cons (list (first ops-list) stmt)
          (vanilla-dst1-body (rest ops-list) stmt))))

(defun dst1-body (op-field ops-list stmt while sequence conditional)
  (let* ((dst1-body (vanilla-dst1-body ops-list stmt))
         (dst1-body
          (if sequence
              (snoc dst1-body (list (find-sequence-name sequence)
                                    (find-sequence-arg1 sequence)))
            dst1-body))
         (dst1-body
          (if conditional
              (snoc dst1-body
                    (list (find-conditional-name conditional)
                          `(if ,(find-conditional-test conditional)
                               ,(find-conditional-tbr conditional)
                             ,(find-conditional-fbr conditional))))
            dst1-body))
         (dst1-body
          (if while
              (snoc dst1-body (list (find-while-name while)
                                    (find-while-body while)))
            dst1-body))
         (dst1-body (snoc dst1-body `(otherwise ,stmt))))
    `(case ,op-field
       ,@dst1-body)))


(defun vanilla-dst2-body (ops-list stmt)
  (if (endp ops-list)
      nil
    (cons (list (first ops-list) stmt)
          (vanilla-dst2-body (rest ops-list) stmt))))

(defun dst2-body (op-field ops-list stmt while sequence conditional)
  (let* ((dst2-body (vanilla-dst2-body ops-list stmt))
         (dst2-body
          (if sequence
              (snoc dst2-body (list (find-sequence-name sequence)
                                    (find-sequence-arg2 sequence)))
            dst2-body))
         (dst2-body
          (if conditional
              (snoc dst2-body
                    (list (find-conditional-name conditional)
                          stmt))
            dst2-body))
         (dst2-body
          (if while
              (snoc dst2-body (list (find-while-name while)
                                    stmt))
            dst2-body))
         (dst2-body (snoc dst2-body `(otherwise ,stmt))))
    `(case ,op-field
       ,@dst2-body)))

(defun vanilla-finish-body (ops-list exec-list)
  (if (endp ops-list) nil
    (cons (list (first ops-list) (first exec-list))
          (vanilla-finish-body (rest ops-list) (rest exec-list)))))

(defun finish-body (op-field ops-list exec-list mem while sequence conditional)
  (let* ((finish-body (vanilla-finish-body ops-list exec-list))
         (finish-body
          (if sequence
              (snoc finish-body (list (find-sequence-name sequence)
                                      mem))
            finish-body))
         (finish-body
          (if conditional
              (snoc finish-body
                    (list (find-conditional-name conditional) mem))
            finish-body))
         (finish-body
          (if while
              (snoc finish-body
                    (list (find-while-name while) mem))
            finish-body))
         (finish-body
          (snoc finish-body `(otherwise ,mem))))
    `(case ,op-field
       ,@finish-body)))


(defun vanilla-stp-body (ops-list mem)
  (if (endp ops-list) nil
    (cons (list (first ops-list) mem)
          (vanilla-stp-body (rest ops-list) mem))))

(defun stp-body (op-field ops-list mem while sequence conditional)
  (let* ((stp-body (vanilla-stp-body ops-list mem))
         (stp-body
          (if sequence
              (snoc stp-body (list (find-sequence-name sequence)
                                      mem))
            stp-body))
         (stp-body
          (if conditional
              (snoc stp-body
                    (list (find-conditional-name conditional) mem))
            stp-body))
         (stp-body
          (if while
              (snoc stp-body
                    (list (find-while-name while) mem))
            stp-body))
         (stp-body
          (snoc stp-body `(otherwise ,mem))))
    `(case ,op-field
       ,@stp-body)))


(defun vanilla-run-body (ops-list exec-list)
  (if (endp ops-list) nil
    (cons (list (first ops-list) (first exec-list))
          (vanilla-run-body (rest ops-list) (rest exec-list)))))

(defun run-body (op-field run stmt mem
                          ops-list exec-list sequence conditional
                          while btm)
  (let*
      ((run-body (vanilla-run-body ops-list exec-list))
       (run-body
        (if sequence
            (snoc run-body
                  (list (find-sequence-name sequence)
                        `(,run ,(find-sequence-arg2 sequence)
                               (,run ,(find-sequence-arg1 sequence)
                                     ,mem))))
          run-body))
       (run-body
        (if conditional
            (snoc run-body
                  (list (find-conditional-name conditional)
                        `(if ,(find-conditional-test conditional)
                             (,run ,(find-conditional-tbr conditional) ,mem)
                           (,run ,(find-conditional-fbr conditional) ,mem))))
          run-body))
       (run-body
        (if while
            (snoc run-body
                  (list (find-while-name while)
                        `(if ,(find-while-test while)
                             ,mem
                           (,run ,stmt
                                 (,run ,(find-while-body while)
                                       ,mem)))))
          run-body))
       (run-body (snoc run-body `(otherwise ,mem))))
    `(if (equal ,mem ,btm)
         ,btm
       (case ,op-field
         ,@run-body))))

(defun definterpreter-fn
  (run stmt mem op-field vanilla sequence conditional while btm
       rule-classes executable guard verify-guards)
  (declare (xargs :mode :program))
  (let* ((ops-list (find-operator-names vanilla))
         (exec-list (find-execution-terms vanilla mem))
         (run-interpreter (packn (list run '-interpreter)))
         (run-executable (packn (list run '-executable)))
         (run-executable-def (packn (list run-executable '-def)))
         (logic-events
          `(encapsulate
            (((,run * *) => *))

            (set-ignore-ok t)
            (set-irrelevant-formals-ok t)

            (local
             (defun test1 (,stmt ,mem)
               (declare (xargs :normalize nil))
               ,(test1-body op-field ops-list while sequence conditional)))

            (local
             (defun finish (,stmt ,mem)
               (declare (xargs :normalize nil))
               ,(finish-body op-field ops-list exec-list mem while sequence
                             conditional)))

            (local
             (defun test2 (,stmt ,mem)
               (declare (xargs :normalize nil))
               ,(test2-body op-field ops-list while sequence conditional)))

            (local
             (defun dst1 (,stmt ,mem)
               (declare (xargs :normalize nil))
               ,(dst1-body op-field ops-list stmt while sequence conditional)))

            (local
             (defun dst2 (,stmt ,mem st2)
               (declare (xargs :normalize nil))
               ,(dst2-body op-field ops-list stmt while sequence
                           conditional)))

            (local
             (defun stp (,stmt ,mem)
               (declare (xargs :normalize nil))
               ,(stp-body op-field ops-list mem while sequence conditional)))


            (local
             (defreflexive-special ,run ,stmt ,mem
               :rule-classes nil
               :recursive-modifier (dst1 stp)
               :bottom ,btm))

            (defthm ,run-interpreter
              (equal (,run ,stmt ,mem)
                     ,(run-body op-field run stmt mem
                                ops-list exec-list sequence conditional
                                while btm))
              :rule-classes ,rule-classes
              :hints (("Goal"
                       :use ((:instance
                              ,(packn (list run '-def)))))))))
         (exec-events
          `(encapsulate
            ()

            (defun ,run-executable (,stmt ,mem)
              (declare (xargs :guard ,guard
                              :verify-guards nil))
              (mbe :logic (,run ,stmt ,mem)
                   :exec ,(run-body op-field run stmt mem
                                    ops-list exec-list sequence
                                    conditional while btm)))

            (local (in-theory (theory 'ground-zero)))

            (defthm ,run-executable-def
              (equal (,run-executable ,stmt ,mem)
                     ,(run-body op-field run stmt mem
                                    ops-list exec-list sequence
                                    conditional while btm))
              :rule-classes ,rule-classes
              :hints (("Goal"
                       :in-theory (enable ,run-executable)
                       :use ((:instance ,run-interpreter))))))))
         (if executable
             (if verify-guards
                 `(progn ,logic-events
                         ,exec-events
                         (skip-proofs (verify-guards
                          ,run-executable
                          :hints (("Goal"
                                   :in-theory (enable ,run-executable)
                                   :use ((:instance ,run-interpreter)))))))

          `(progn ,logic-events
                  ,exec-events))
      `(progn ,logic-events))))

(defmacro definterpreter (run stmt mem
                               &key
                               (op-field 'nil)
                               (vanilla-interpreter 'nil)
                               (conditional 'nil)
                               (sequence 'nil)
                               (bottom 'nil)
                               (while 'nil)
                               (rule-classes 'nil)
                               (executable 'nil)
                               (guard 't)
                               (verify-guards 'nil))
  (definterpreter-fn run stmt mem op-field vanilla-interpreter
    sequence conditional while bottom rule-classes executable guard
    verify-guards))


;; Here is the solution to Bill Young's challenge.

(encapsulate
 ()

 (local
  (defun op (stmt)
    (first stmt)))

 (local
  (defun arg1 (stmt)
    (second stmt)))

 (local
  (defun arg2 (stmt)
    (third stmt)))

 (local
  (defun arg3 (stmt)
    (fourth stmt)))

 (local
  (defmacro val (key alist)
    `(cdr (assoc-equal ,key ,alist))))

 (local
  (defmacro tlistp (x n)
    `(and (true-listp ,x)
          (equal (len ,x) ,n))))

 (local
  (defun  definedp (x alist)
    (if (endp alist)
        nil
      (if (equal x (caar alist))
          t
        (definedp x (cdr alist))))))

 (local
  (defun varp (x alist)
    (and (symbolp x)
         (definedp x alist))))

 (local
  (defun exprp (x alist)
    (or (integerp x)
        (varp x alist))))

 (local
  (defun eval-expr (expr alist)
    (if (integerp expr)
        expr
      (val expr alist))))

 (local
  (defun run-assignment (stmt alist)
    (let* ((v (arg1 stmt))
           (e (arg2 stmt))
           (val (eval-expr e alist)))
      (put-assoc-equal v val alist))))

 (local
  (definterpreter run stmt mem
    :op-field (op stmt)
    :bottom nil
    :executable t
    :verify-guards nil
    ;; I have set the verify-guards as nil above since otherwise I
    ;; need to verify the guards of arg1, arg2, run-assignment, op,
    ;; etc.  If anyone wants that then they can do so.  It will then
    ;; of course become an executable function (although not
    ;; necessarily terminating).
    :vanilla-interpreter (((:name skip)
                           (:interpreter mem))
                          ((:name assign)
                           (:interpreter (run-assignment stmt mem))))
    :sequence ((:name sequence)
               (:arg1 (arg1 stmt))
               (:arg2 (arg2 stmt)))
    :conditional ((:name if)
                  (:test  (zerop (eval-expr (arg1 stmt) mem)))
                  (:tbr (arg3 stmt))
                  (:fbr (arg2 stmt)))
    :while ((:name while)
            (:test (zerop (eval-expr (arg1 stmt) mem)))
            (:body (arg2 stmt))))))

