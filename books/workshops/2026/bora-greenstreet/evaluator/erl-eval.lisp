; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "termination")
(include-book "eval-calls")
(include-book "eval-receive")

(set-induction-depth-limit 1)

; Erlang Evaluator -------------------------------------------------------------

; Evaluate the current continuation and return the next erl-val-klst
;
; Unsupported:
; - Badmatch exception are supposed to return the value that failed to 
;   match. However, in the current implementation there is no easy way to 
;   acquire that value sometimes.
; - The Erlang compiler can find out if different clauses of the same expression
;   set the same variable to different values. These variables are called
;   'unsafe' and should not allowed. (TODO: add link). To enforce this, I could
;   define a well-formed-ast-p, which would also enforce that variables are
;   always bound.
;
(define eval-k ((k erl-k-p) (s erl-state-p))
  :returns (ks erl-s-klst-p)
  (b* ((k (erl-k-fix k))
       (fuel (erl-k->fuel k))
       (k (erl-k->kont k))
       ((erl-state s) (erl-state-fix s))

       ; Return flimit if fuel has ran out.
       ((if (zp fuel)) 
        (make-erl-s-klst :s (update-erl-state->in s (make-erl-val-flimit))))
      
       ; If k is not a catch, and s has an exception, skip this continuation.
       ((if (and (equal (erl-val-kind s.in) :excpt) (not (equal (kont-kind k) :catch))))
        (if (equal (kont-kind k) :function-return)
            ; return to the right context if needed. TODO: also grow the exception stack here.
            (make-erl-s-klst :s
              (update-erl-state->bind-mod s
                (kont-function-return->bind k) (kont-function-return->module k)))
            (make-erl-s-klst :s s))))
    (kont-case k
      ; Evaluate an expression.
      (:expr (let ((x k.expr))
        (node-case x
          ; if x is an atomic term, simply return its value 
          (:integer (make-erl-s-klst :s (update-erl-state->in s (make-erl-val-integer :val x.val))))
          (:atom    (make-erl-s-klst :s (update-erl-state->in s (make-erl-val-atom :val x.val))))
          (:string  (make-erl-s-klst :s (update-erl-state->in s (string=>erl-cons x.val))))
          (:nil     (make-erl-s-klst :s (update-erl-state->in s (make-erl-val-cons :lst nil))))
          ; if x is a fun, return the corresponding fun struct
          (:fun
            (b* ((arity (erl-clause-list->arity x.cls))
                 ((if (null arity))
                  (make-erl-s-klst :s
                    (update-erl-state->in s 
                      (make-erl-val-reject :err "erl-eval: ill-formed fun clauses")))))
                (make-erl-s-klst :s
                  (update-erl-state->in s
                    (make-erl-val-fun
                      :arity arity :cls x.cls :bind s.bind :module s.module)))))
          ; if x is a list, evaluate its car and save its cdr in a continuation.
          (:cons
            (make-erl-s-klst
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.hd))
                          (make-erl-k :fuel (1- fuel)
                                      :kont (make-kont-cons :cdr-expr x.tl :bind-0 s.bind)))))
          ; if x is a tuple, evaluate its elements first.
          (:tuple
            (make-erl-s-klst 
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.lst))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-tuple)))))
          ; if x is a var, lookup its value. If the AST is well-formed, x should be bound.
          (:var
            (if (omap::assoc x.id s.bind)
                (make-erl-s-klst :s (update-erl-state->in s (omap::lookup x.id s.bind)))
                (make-erl-s-klst :s
                  (update-erl-state->in s
                    (make-erl-val-reject :err "unbound variable")))))
          (:unop
            (make-erl-s-klst
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.expr))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-unop :op x.op)))))
          ; if x is a binop, evaluate the first operand, save the operator and the second operand
          (:binop
            (make-erl-s-klst
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.left))
                          (make-erl-k :fuel (1- fuel) 
                                      :kont (make-kont-binop-expr1 :op x.op 
                                                                   :right x.right
                                                                   :bind-0 s.bind)))))
          ; if x is match, evaluate the rhs a, save the lhs in a continuation.
          (:match
            (make-erl-s-klst
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.rhs))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-match :lhs x.lhs)))))
          (:try
            (make-erl-s-klst
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-exprs :exprs x.exprs))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-catch :clauses x.err-clauses)))))
          ; if x is an if clause, invoke the clause evaluator
          (:if
            (b* (((mv (erl-state rs) body)
                  (eval-clauses nil x.clauses (update-erl-state->in s (make-erl-val-none))))
                 ((if (equal (erl-val-kind rs.in) :reject)) (make-erl-s-klst :s rs))
                 ((if (null body))
                  (make-erl-s-klst :s
                    (update-erl-state->in s
                      (make-erl-val-excpt
                        :err-class (make-erl-val-atom :val 'error)
                        :err-reason (make-erl-val-atom :val 'if_clause))))))
                (make-erl-s-klst
                  :s (update-erl-state->in s (make-erl-val-none))
                  :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr (car body)))
                              (make-erl-k :fuel (1- fuel) :kont (make-kont-exprs :exprs (cdr body)))))))
          ; if x is a case, evaluate the expression and save the clauses in a continuation.
          (:case-of
            (make-erl-s-klst
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.expr))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-case-of :clauses x.clauses)))))

          ; if x is remote call, first evaluate the arguments and then handle the call
          (:remote-call
            (make-erl-s-klst 
              :s (update-erl-state->in s (make-erl-val-none))
              :klst
                (list (make-erl-k 
                        :fuel (1- fuel) 
                        :kont (make-kont-expr :expr x.args))
                      (make-erl-k
                        :fuel (1- fuel)
                        :kont (make-kont-remote-call :module x.module :call x.fn)))))
          
          ; if x is a fun call, first evaluate the fun expr and then arguments
          (:fun-call
            (make-erl-s-klst
              :s (update-erl-state->in s (make-erl-val-none))
              :klst
                (list (make-erl-k
                        :fuel (1- fuel)
                        :kont (make-kont-expr :expr x.fun))
                      (make-erl-k
                        :fuel (1- fuel)
                        :kont (make-kont-fun-call-args :args x.args)))))
          ; if x is a local call, first evaluate the arguments and then handle the call
          (:call
            (make-erl-s-klst 
              :s (update-erl-state->in s (make-erl-val-none))
              :klst
                (list (make-erl-k 
                        :fuel (1- fuel) 
                        :kont (make-kont-expr :expr x.args))
                      (make-erl-k
                        :fuel (1- fuel)
                        :kont (make-kont-local-call :call x.fn)))))

          ; when a receive is encountered, climb backwards in the continuation tree
          (:receive
            (make-erl-s-klst :s
              (update-erl-state->in s
                (make-erl-val-receive
                  :klst
                  (list
                    (make-erl-k
                      :fuel fuel
                      :kont (make-kont-receive :clauses x.cls))))))))))

      ; Evaluate the cdr of the list, save the result of the car in a contunation
      (:cons
        (make-erl-s-klst
          :s (update-erl-state->in-bind s (make-erl-val-none) k.bind-0)
          :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr k.cdr-expr))
                      (make-erl-k :fuel (1- fuel)
                                  :kont (make-kont-cons-merge :car-val s.in 
                                                              :car-bind s.bind)))))
      ; When both the car and cdr of the list are evaluated, merge the results.
      (:cons-merge
        (if (equal (erl-val-kind s.in) :cons)
            (if (omap::compatiblep s.bind k.car-bind)
                (make-erl-s-klst :s
                  (update-erl-state->in-bind s 
                    (make-erl-val-cons :lst (cons k.car-val (erl-val-cons->lst s.in)))
                    (omap::update* s.bind k.car-bind)))
                (make-erl-s-klst :s
                  (update-erl-state->in s
                    (make-erl-val-excpt
                      :err-class (make-erl-val-atom :val 'error)
                      :err-reason (make-erl-val-tuple :lst (list (make-erl-val-atom :val 'badmatch) s.in))))))
            (make-erl-s-klst :s
              (update-erl-state->in s 
                (make-erl-val-reject :err "cons-merge expects list, pairs are not supported")))))

      ; Once all of its elements are evaluated, return the tuple.
      (:tuple
        (if (equal (erl-val-kind s.in) :cons)
            (make-erl-s-klst :s
              (update-erl-state->in s
                (make-erl-val-tuple :lst (erl-val-cons->lst (erl-state->in s)))))
            (make-erl-s-klst :s
              (update-erl-state->in s 
                (make-erl-val-reject :err "tuple expects a list of elements.")))))

      ; Apply unop to the evalutaed operand.
      (:unop (make-erl-s-klst :s (update-erl-state->in s (apply-erl-unop k.op s.in))))

      ; Evaluate the second operand of a binop, save the operator and value of the first operand                                                    
      (:binop-expr1 
        (make-erl-s-klst
          :s (update-erl-state->in-bind s (make-erl-val-none) k.bind-0)
          :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr k.right))
                      (make-erl-k :fuel (1- fuel) 
                                  :kont (make-kont-binop-expr2 :op k.op 
                                                               :val s.in
                                                               :left-bind s.bind)))))
      ; Apply the binop to the evaluated operands
      (:binop-expr2
        (if (omap::compatiblep s.bind k.left-bind)   
            (if (equal k.op '!)
                (if (pid-p k.val)
                    (make-erl-s-klst :s
                      (erl-state-send s
                        k.val s.in (omap::update* s.bind k.left-bind)))
                    (make-erl-s-klst :s
                      (update-erl-state->in s
                        (make-erl-val-excpt
                          :err-class (make-erl-val-atom :val 'error)
                          :err-reason (make-erl-val-atom :val 'badarg)))))
                (make-erl-s-klst :s
                  (update-erl-state->in-bind s
                    (apply-erl-binop k.op k.val s.in)
                    (omap::update* s.bind k.left-bind))))
            (make-erl-s-klst :s
              (update-erl-state->in s 
                (make-erl-val-excpt
                  :err-class (make-erl-val-atom :val 'error)
                  :err-reason (make-erl-val-tuple :lst
                                (list (make-erl-val-atom :val 'badmatch) s.in)))))))

      ; Once rhs is evaluated, match it to lhs
      (:match
        (b* (((erl-state ms) (eval-match k.lhs s))
             ((if (and (equal (erl-val-kind ms.in) :excpt)
                       (equal (erl-val-kind (erl-val-excpt->err-reason ms.in)) :atom)
                       (equal (erl-val-atom->val (erl-val-excpt->err-reason ms.in)) 'badmatch)))
              (make-erl-s-klst :s
                (update-erl-state->in s
                  (make-erl-val-excpt
                    :err-class (make-erl-val-atom :val 'error)
                    :err-reason (make-erl-val-tuple :lst
                                  (list (make-erl-val-atom :val 'badmatch) s.in)))))))
            (make-erl-s-klst :s ms)))

      ; Try to catch an exception. If none can be caught, propagate the value.
      (:catch
        (b* (((if (not (equal (erl-val-kind s.in) :excpt))) (make-erl-s-klst :s s))
             (cls (erl-val-excpt->err-class s.in))
             (rsn (erl-val-excpt->err-reason s.in))
             (stk (make-erl-val-cons :lst (erl-val-excpt->err-stack s.in)))
             (err-triple (make-erl-val-tuple :lst (list cls rsn stk)))
             ((mv (erl-state rs) body) (eval-clauses (list err-triple) k.clauses s))
             ((if (equal (erl-val-kind rs.in) :reject)) (make-erl-s-klst :s rs))
             ((if (null body)) (make-erl-s-klst :s s)))
            (make-erl-s-klst
              :s (update-erl-state->in rs (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr (car body)))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-exprs :exprs (cdr body)))))))

      ; Once the expression is evaluated, invoke the clause-evaluator.
      (:case-of
        (b* (((mv (erl-state rs) body) (eval-clauses (list s.in) k.clauses s))
             ((if (equal (erl-val-kind rs.in) :reject)) (make-erl-s-klst :s rs))
             ((if (null body))
              (make-erl-s-klst :s
                (update-erl-state->in s
                  (make-erl-val-excpt
                    :err-class (make-erl-val-atom :val 'error)
                    :err-reason (make-erl-val-tuple :lst
                                  (list (make-erl-val-atom :val 'case_clause) s.in)))))))
            (make-erl-s-klst
              :s (update-erl-state->in rs (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr (car body)))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-exprs :exprs (cdr body)))))))

      ; Move to the next expression to be evaluated.
      (:exprs
        (if (null k.exprs)
            (make-erl-s-klst :s s)
            (make-erl-s-klst 
              :s s
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr (car k.exprs)))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-exprs :exprs (cdr k.exprs)))))))

      ; Call a local function after the arguments have been evaluated
      (:local-call
        (b* (((if (not (equal (erl-val-kind s.in) :cons)))
              (make-erl-s-klst :s
                (update-erl-state->in s
                  (make-erl-val-reject :err "Local call: invalid arg list."))))
             ; Obtain the args from the state.
             (args (erl-val-cons->lst s.in))
             ((mv rs body) 
              (eval-local-call
                s
                k.call 
                args))
             ; if the body is nil, return the value produced by call evaluation.
             ((if (null body)) (make-erl-s-klst :s rs)))
            ; Otherwise, continue with the function body
            (make-erl-s-klst
              :s rs
              :klst
                (list
                  (make-erl-k
                    :fuel (1- fuel) :kont (make-kont-exprs :exprs body))
                  (make-erl-k
                    :fuel (1- fuel)
                    :kont (make-kont-function-return :bind s.bind :module s.module))))))

      ; Call a remote function after the arguments have been evaluated
      (:remote-call
        (b* (((if (not (equal (erl-val-kind s.in) :cons)))
              (make-erl-s-klst :s
                (update-erl-state->in s
                  (make-erl-val-reject :err "Remote call: invalid arg list."))))
             ; Obtain the args from the state.
             (args (erl-val-cons->lst s.in))
             ((mv rs body)
              (eval-remote-call s k.module k.call args))
             ; if the body is nil, return the value produced by call evaluation.
             ((if (null body)) (make-erl-s-klst :s rs)))
            ; Otherwise, continue with the function body
            (make-erl-s-klst
              :s rs
              :klst
                (list
                  (make-erl-k 
                    :fuel (1- fuel)
                    :kont (make-kont-exprs :exprs body))
                  (make-erl-k
                    :fuel (1- fuel) 
                    :kont (make-kont-function-return :bind s.bind :module s.module))))))

      ; Evalute the arguments to an anonymous call after the fun expression has been evaluated.
      (:fun-call-args
        (b* (((if (not (erl-fun-p s.in)))
              (make-erl-s-klst :s
                (update-erl-state->in s
                  (make-erl-val-excpt
                    :err-class (make-erl-val-atom :val 'error)
                    :err-reason (make-erl-val-tuple :lst
                                  (list (make-erl-val-atom :val 'badfun) s.in)))))))
            (make-erl-s-klst 
              :s (update-erl-state->in s (make-erl-val-none))
              :klst
                (list
                  (make-erl-k 
                    :fuel (1- fuel) :kont (make-kont-expr :expr k.args))
                  (make-erl-k
                    :fuel (1- fuel) :kont (make-kont-fun-call :fun s.in))))))

      ; Call an anonymous function after the arguments have been evaluated
      (:fun-call
        (b* (((if (not (equal (erl-val-kind s.in) :cons)))
              (make-erl-s-klst :s
                (update-erl-state->in s
                  (make-erl-val-reject :err "Fun call: invalid arg list."))))
             ; Obtain the args from the state.
             (args (erl-val-cons->lst s.in))
             ((mv rs body) 
              (eval-fun-call s k.fun args))
             ; if the body is nil, return the value produced by call evaluation.
             ((if (null body)) (make-erl-s-klst :s rs)))
            ; Otherwise, continue with the function body
            (make-erl-s-klst
              :s rs
              :klst
                (list
                  (make-erl-k 
                    :fuel (1- fuel) :kont (make-kont-exprs :exprs body))
                  (make-erl-k
                    :fuel (1- fuel) 
                    :kont (make-kont-function-return :bind s.bind :module s.module))))))

      ; Once a call returns, return to the correct module and scope
      (:function-return (make-erl-s-klst :s (update-erl-state->bind-mod s k.bind k.module)))

      ; Once a message is received, attempt to match the clauses of the receive expression
      (:receive
        (b* (((mv rs body) 
              (eval-receive s (kont-receive->clauses k)))
              ((if (null body)) (make-erl-s-klst :s rs)))
            (make-erl-s-klst
              :s (update-erl-state->in rs (make-erl-val-none))
              :klst
                (list
                  (make-erl-k 
                    :fuel (1- fuel)
                    :kont (make-kont-expr :expr (car body)))
                  (make-erl-k 
                    :fuel (1- fuel)
                    :kont (make-kont-exprs :exprs (cdr body)))))))))

  ///
    (defcong erl-k-equiv equal (eval-k k s) 1)
    (defcong erl-state-equiv equal (eval-k k s) 2)

    (more-returns
      (ks :name len-of-eval-k->klst
        (implies (erl-s-klst->klst ks)
          (and (consp (erl-s-klst->klst ks))
               (consp (cdr (erl-s-klst->klst ks)))
               (not (cddr (erl-s-klst->klst ks))))))

      (ks :name eval-k-decreases-fuel
        (implies (erl-s-klst->klst ks)
          (and (equal (erl-k->fuel (car (erl-s-klst->klst ks)))
                      (- (erl-k->fuel k) 1))
               (equal (erl-k->fuel (cadr (erl-s-klst->klst ks)))
                      (- (erl-k->fuel k) 1)))))

      (ks :name eval-k-decreases-klst-measure
        (< (klst-measure (append (erl-s-klst->klst ks) kl))
           (klst-measure (cons k kl)))
        :hints
          (("Goal" :in-theory (disable eval-k)
                    :use (:functional-instance eval-op-decreases-klst-measure
                            (eval-op eval-k))))))

    (defrule eval-k-of-flimit
      (implies (and (wf-state-p s) (zp (erl-k->fuel k)))
	       (equal (eval-k k s)
                (make-erl-s-klst
                  :s (update-erl-state->in (erl-state-fix s) (make-erl-val-flimit)))))))


; Recursively apply the next continuation to the state produced by the previous.
(define apply-k ((s erl-state-p) (klst erl-klst-p))
  :returns (r erl-state-p)
  :well-founded-relation l<
  :measure (klst-measure klst)
  (b* (((erl-state s) (erl-state-fix s))
       (klst (erl-klst-fix klst))

       ; Evaluation is complete when there are no more continuations.
       ((if (endp klst)) s)

       ((cons khd ktl) klst)

       ; Propagate calls to receive
       ((if (equal (erl-val-kind (erl-state->in s)) :receive))
        (update-erl-state->in s
          (make-erl-val-receive :klst
            (append (erl-val-receive->klst (erl-state->in s)) klst))))

       ; Propagate 
       ((unless (wf-state-p s)) (apply-k s ktl))

       ((erl-s-klst ks) (eval-k khd s)))
    (apply-k ks.s (append ks.klst ktl)))

  ; for termination proof
  :hints (("Goal" :in-theory (disable eval-k-decreases-klst-measure)
                  :use ((:instance eval-k-decreases-klst-measure
                          (k (car klst)) (kl (cdr klst))))))
  ///
    (local (in-theory (disable apply-k)))

    (defcong erl-state-equiv equal (apply-k s klst) 1
      :hints(("Goal" :expand ((apply-k s klst) (apply-k s-equiv klst)))))
    (defcong erl-klst-equiv equal (apply-k s klst) 2
      :hints(("Goal" :expand ((apply-k s klst) (apply-k s klst-equiv)))))

    (defrule apply-k-of-nil (equal (apply-k s nil) (erl-state-fix s))
      :hints(("Goal" :expand ((apply-k s nil)))))

    (defrule apply-k-of-not-consp
      (implies (not (consp klst))
               (equal (apply-k s klst) (erl-state-fix s)))
      :hints(("Goal" :expand ((apply-k s klst)))))

    (local (in-theory (enable apply-k)))

    (defrule apply-k-of-bad-state
      (implies
        (and (not (wf-state-p s))
             (not (equal (erl-val-kind (erl-state->in s)) :receive)))
	      (equal (apply-k s klst) (erl-state-fix s)))
      :enable wf-state-p)

    (defrule bad-state-of-apply-k-of-bad-state
      (implies
        (not (wf-state-p s))
	      (not (wf-state-p (apply-k s klst))))
      :enable wf-state-p)
               
    (defrule apply-k-when-out-of-fuel
      (implies (and (wf-state-p s) (consp klst) (zp (erl-k->fuel (car klst))))
               (equal (apply-k s klst)
                      (update-erl-state->in (erl-state-fix s) (make-erl-val-flimit))))
      :enable wf-state-p))