; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "util")

; Example 2: Reduce -----------------------------------------------------------

; Lin & Snyder style reduce, and the corresponding Erlang world.
;
; reduce({ParentPid, ChildPids}, CombineFun, Value) ->
;   reduce(ParentPid, ChildPids, CombineFun, Value).
;
; reduce(none, [], _, GrandTotal) -> GrandTotal;
; reduce(ParentPid, [], _, MyTotal) ->
;   ParentPid ! {self(), reduce_up, MyTotal},
;   receive
;     {ParentPid, reduce_down, GrandTotal} -> GrandTotal
;   end;
; reduce(Parent, [ChildHd | ChildTl], CombineFun, LeftTotal) ->
;   receive
;     {ChildHd, reduce_up, RightTotal} ->
;       GrandTotal =
;         reduce(Parent, ChildTl, CombineFun, CombineFun(LeftTotal, RightTotal)),
;       ChildHd ! {self(), reduce_down, GrandTotal},
;       GrandTotal
;   end.

(local (define reduce-world ()
  :returns (w world-p)
  '((local
      (attrs (module . local) (export) (import))
      (fn-defns
        ; reduce/3
        (((name . reduce) (arity . 3))
         ((cases
            (:tuple (:cons (:var ParentPid) (:cons (:var ChildPids) (:nil))))
            (:var CombineFun)
            (:var Value))
          (guards)
          (body
            ; reduce(ParentPid, ChildPids, CombineFun, Value)
            (:call reduce
               (:cons (:var ParentPid)
                 (:cons (:var ChildPids)
                   (:cons (:var CombineFun)
                     (:cons (:var Value) (:nil)))))))))
        ; reduce/4
        (((name . reduce) (arity . 4))
         ; reduce(none, [], _, GrandTotal)
         ((cases (:atom none) (:nil) (:var _) (:var GrandTotal))
          (guards)
          (body (:var GrandTotal)))
         ; reduce(ParentPid, [], _, MyTotal)
         ((cases (:var ParentPid) (:nil) (:var _) (:var MyTotal))
          (guards)
          (body
            ; ParentPid ! {self(), reduce_up, MyTotal}
            (:binop !
              (:var ParentPid)
              (:tuple
                (:cons (:call self (:nil))
                  (:cons (:atom reduce_up)
                    (:cons (:var MyTotal) (:nil))))))
            ; receive {ParentPid, reduce_down, GrandTotal} -> GrandTotal end
            (:receive
              (((cases
                  (:tuple
                    (:cons (:var ParentPid)
                      (:cons (:atom reduce_down)
                        (:cons (:var GrandTotal) (:nil))))))
                (guards)
                (body (:var GrandTotal)))))))
         ; reduce(Parent, [ChildHd | ChildTl], CombineFun, LeftTotal)
         ((cases (:var Parent) (:cons (:var ChildHd) (:var ChildTl))
                 (:var CombineFun) (:var LeftTotal))
          (guards)
          (body
            ; receive {ChildHd, reduce_up, RightTotal} -> ... end
            (:receive
              (((cases
                  (:tuple
                    (:cons (:var ChildHd)
                      (:cons (:atom reduce_up)
                        (:cons (:var RightTotal) (:nil))))))
                (guards)
                ; GrandTotal = reduce(...)
                (body
                  (:match
                    (:var GrandTotal)
                    (:call reduce
                      (:cons (:var Parent)
                        (:cons (:var ChildTl)
                          (:cons (:var CombineFun)
                            (:cons (:fun-call (:var CombineFun)
                                      (:cons (:var LeftTotal)
                                        (:cons (:var RightTotal) (:nil))))
                                    (:nil)))))))
                  ; ChildHd ! {self(), reduce_down, GrandTotal}
                  (:binop !
                    (:var ChildHd)
                    (:tuple
                      (:cons (:call self (:nil))
                        (:cons (:atom reduce_down)
                          (:cons (:var GrandTotal) (:nil))))))
                  ; GrandTotal
                  (:var GrandTotal)))))))))))))

; Create a process that will call reduce with the given arguments.
(local (define make-reduce-proc ((self pid-p) (parent erl-val-p) (children erl-vlst-p) (fn erl-fun-p) (value erl-val-p))
  :verify-guards nil
  (b* ((self (pid-fix self))
       (parent (erl-val-fix parent))
       (children (erl-vlst-fix children))
       (fn (erl-fun-fix fn))
       (value (erl-val-fix value)))
      (make-expr-proc
        self
        (omap::from-lists
          (list 'Parent 'ChildPids 'CombineFun 'Value)
          (list parent (make-erl-val-cons :lst children) fn value))
        (reduce-world)
        (make-node-call
          :fn 'reduce
          :args
            (make-node-cons
              :hd
                (make-node-tuple
                  :lst
                    (make-node-cons
                      :hd (make-node-var :id 'Parent)
                      :tl (make-node-cons
                            :hd (make-node-var :id 'ChildPids)
                            :tl (make-node-nil))))
                :tl (make-node-cons
                        :hd (make-node-var :id 'CombineFun)
                        :tl (make-node-cons
                              :hd (make-node-var :id 'Value)
                              :tl (make-node-nil)))))))))

; Create a worker tree of [n] processes, where each leaf has already finished the sequential work
; and is about to call reduce. This is a lot simpler than what might happen in a real Erlang program,
; where some processes could call reduce while other processes are not done with their sequential
; work yet. More importantly, in this worker tree, the PID of a process is equal to the process' index,
; which definitely would not in an Erlang program. There is another exaqmple in books/reduce-v2 that
; has a more accurate worker tree. 
(local (define create-wtree ((n natp) (par erl-val-p) (chl erl-vlst-p) (self natp) (fn erl-fun-p) (vlst erl-vlst-p))
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))
  :verify-guards nil
  :measure (nfix n)
  (b* ((n (nfix n))
       (par (erl-val-fix par))
       (chl (erl-vlst-fix chl))
       (self (nfix self))
       (fn (erl-fun-fix fn))
       (vlst (erl-vlst-fix vlst))
       ((unless (nth self vlst)) nil)
       ((if (zp n)) nil)
       ((if (equal n 1))
        (omap::update
          (make-erl-val-pid :id self)
          (make-reduce-proc (make-erl-val-pid :id self) par chl fn (nth self vlst))
          nil))
       (child-net
        (create-wtree
          (ceiling n 2)
          (make-erl-val-pid :id self)
          nil
          (+ self (floor n 2))
          fn
          vlst))
       (parent-net
        (create-wtree
          (- n (ceiling n 2))
          par
          (cons (make-erl-val-pid :id (+ self (floor n 2))) chl)
          self
          fn
          vlst))
       ((unless (omap::compatiblep parent-net child-net)) nil))
      (omap::update* parent-net child-net))))

; Reduce network with 10 processes, where CombineFun = fun(X, Y) -> X + Y end.
; Test with: (print-omap-values (erl-runner *reduce-sum* 64))
(local (defconst *reduce-sum*
  (create-wtree
    10 '(:atom none) nil 0
    (make-erl-val-fun
      :arity 2
      :cls '(((cases (:var X) (:var Y)) (guards) (body (:binop + (:var X) (:var Y)))))
      :bind nil
      :module 'local)
    (ints-to-erl-ints (list 7 16 2 19 11 6 16 8 3 12)))))

; Reduce network with 10 processes, where CombineFun = fun(X, Y) -> max(X, Y) end.
; Test with: (print-omap-values (erl-runner *reduce-max* 64))
(local (defconst *reduce-max*
  (create-wtree
    10 '(:atom none) nil 0
    (make-erl-val-fun
      :arity 2
      :cls '(((cases (:var X) (:var Y)) (guards)
              (body (:call max (:cons (:var X) (:cons (:var Y) (:nil)))))))
      :bind nil
      :module 'local)
    (ints-to-erl-ints (list 1 0 2 19 11 36 16 8 -3 12)))))