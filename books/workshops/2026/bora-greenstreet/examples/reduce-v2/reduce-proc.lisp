; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../../scheduler/top")

(set-induction-depth-limit 1)

#| Erlang worlds with the following functions defined locally:

  sum_reduce(none, [], GrandTotal) -> GrandTotal;
  sum_reduce(ParentPid, [], MyTotal) ->
    ParentPid ! {self(), MyTotal};
  sum_reduce(ParentPid, [ChildHd | ChildTl], LeftTotal) ->
    receive
      {ChildHd, RightTotal} ->
        sum_reduce(ParentPid, ChildTl, LeftTotal + RightTotal)
    end.

  We make no claim about the rest of the world, i.e. there could be other
  modules and functions.
|#
(define sum-reduce-world-p ((w world-p))
  :enabled t
  (b* (((unless (omap::assoc 'local w)) nil)
       (defns (module->fn-defns (omap::lookup 'local w)))
       (fn '((name . sum_reduce) (arity . 3)))
       ((unless (omap::assoc fn defns)) nil))
      (equal
        (omap::lookup fn defns)
        '(; sum_reduce(none, [], GrandTotal)
          ((cases (:atom none) (:nil) (:var GrandTotal)) (guards) (body (:var GrandTotal)))
          ; sum_reduce(ParentPid, [], MyTotal)
          ((cases (:var ParentPid) (:nil) (:var MyTotal)) (guards)
           (body
            ; ParentPid ! {self(), MyTotal}
            (:binop !
              (:var ParentPid)
              (:tuple (:cons (:call self (:nil)) (:cons (:var MyTotal) (:nil)))))
            (:var MyTotal)))
          ; sum_reduce(ParentPid, [ChildHd | ChildTl], LeftTotal)
          ((cases (:var ParentPid) (:cons (:var ChildHd) (:var ChildTl)) (:var LeftTotal))
           (guards)
           (body
             ; receive {ChildHd, RightTotal} -> ... end
             (:receive
               (((cases (:tuple (:cons (:var ChildHd) (:cons (:var RightTotal) (:nil)))))
                (guards)
                (body
                  ; sum_reduce(ParentPid, ChildTl, LeftTotal + RightTotal)
                  (:call sum_reduce
                    (:cons (:var ParentPid)
                      (:cons (:var ChildTl)
                        (:cons (:binop + (:var LeftTotal) (:var RightTotal)) (:nil)))))))))))))))

; Remark: The correctness proof of sum_reduce should hold for any world that satisfies [reduce-world-p].
; However, it is a lot easier to test the algorithm and get a first iteration of proofs for a concrete world.
; Thus, for the moment, I will prove eveything with respect to the following world.
(define sum-reduce-world ()
  :returns (w world-p)
  '((local
      (attrs (module . local) (export) (import))
      (fn-defns
        (((name . sum_reduce) (arity . 3))
         ; sum_reduce(none, [], GrandTotal)
         ((cases (:atom none) (:nil) (:var GrandTotal)) (guards) (body (:var GrandTotal)))
         ; sum_reduce(ParentPid, [], MyTotal)
         ((cases (:var ParentPid) (:nil) (:var MyTotal)) (guards)
          (body
            ; ParentPid ! {self(), MyTotal}
            (:binop !
              (:var ParentPid)
              (:tuple (:cons (:call self (:nil)) (:cons (:var MyTotal) (:nil)))))
            (:var MyTotal)))
         ; sum_reduce(ParentPid, [ChildHd | ChildTl], LeftTotal)
         ((cases (:var ParentPid) (:cons (:var ChildHd) (:var ChildTl)) (:var LeftTotal))
          (guards)
          (body
            ; receive {ChildHd, RightTotal} -> ... end
            (:receive
              (((cases (:tuple (:cons (:var ChildHd) (:cons (:var RightTotal) (:nil)))))
                (guards)
                (body
                  ; sum_reduce(ParentPid, ChildTl, LeftTotal + RightTotal)
                  (:call sum_reduce
                    (:cons (:var ParentPid)
                      (:cons (:var ChildTl)
                        (:cons (:binop + (:var LeftTotal) (:var RightTotal)) (:nil)))))))))))))))
  ///
    (local (defrule sum-reduce-w-well-formed
      (sum-reduce-world-p (sum-reduce-world)))))

; Create a process that will call reduce with the given arguments. This process uses its index
; as the value for reduce. This means that the end result of reduce with n processes will be
; the sum of natural numbers up to n.
(define make-reduce-proc ((self pid-p) (parent erl-val-p) (children pid-lst-p) (index natp))
  :returns (proc proc-p)
  :guard-hints (("Goal" :in-theory (enable omap::from-lists)))
  (b* ((self (pid-fix self))
       (parent (erl-val-fix parent))
       (index (nfix index))
       (children (pid-lst-fix children)))
    (make-proc
      :s
        (make-erl-state
          :self self :world (sum-reduce-world)
          :bind
            (omap::from-lists
              (list 'ChildPids 'Parent 'Index)
              (list (make-erl-val-cons :lst children) parent (make-erl-val-integer :val index))))
      :klst
        (list (make-erl-k
                :fuel (+ 100 (* 100 (len children)))
                :kont (make-kont-expr
                        :expr (make-node-call
                                :fn 'sum_reduce
                                :args (make-node-cons
                                        :hd (make-node-var :id 'Parent)
                                        :tl (make-node-cons
                                              :hd (make-node-var :id 'ChildPids)
                                              :tl (make-node-cons
                                                    :hd (make-node-var :id 'Index)
                                                    :tl (make-node-nil))))))))))
  ///
    (defcong pid-equiv equal (make-reduce-proc s p c i) 1)
    (defcong erl-val-equiv equal (make-reduce-proc s p c i) 2)
    (defcong pid-lst-equiv equal (make-reduce-proc s p c i) 3)
    (defcong nat-equiv equal (make-reduce-proc s p c i) 4)

    ; Some theorems about make-reduce-proc
    (defrule network-p-of-update-with-make-reduce-proc
      (implies
        (and (network-p net) (pid-p pid))
        (network-p (omap::update pid (make-reduce-proc pid par chl val) net)))
      :e/d ((proc->pid) (network-p-of-update))
      :use (:instance network-p-of-update
              (net net) (pid pid) (p (make-reduce-proc pid par chl val))))

    (defrule assoc-of-make-reduce=proc
      (and
        (omap::assoc 'Index
          (erl-state->bind (proc->s (make-reduce-proc self parent children index))))
        (omap::assoc 'Parent
          (erl-state->bind (proc->s (make-reduce-proc self parent children index))))
        (omap::assoc 'ChildPids
          (erl-state->bind (proc->s (make-reduce-proc self parent children index)))))
      :enable (omap::from-lists omap::lookup-of-update))

    (defrule index-of-make-reduce-proc
      (equal (omap::lookup 'Index
               (erl-state->bind (proc->s (make-reduce-proc self parent children index))))
             (make-erl-val-integer :val (nfix index)))
      :enable (omap::from-lists omap::lookup-of-update))

    (defrule parent-of-make-reduce-proc
      (equal (omap::lookup 'Parent
               (erl-state->bind (proc->s (make-reduce-proc self parent children index))))
             (erl-val-fix parent))
      :enable (omap::from-lists omap::lookup-of-update))

    (defrule childpids-of-make-reduce-proc
      (equal (omap::lookup 'ChildPids
               (erl-state->bind (proc->s (make-reduce-proc self parent children index))))
             (make-erl-val-cons :lst (pid-lst-fix children)))
      :enable (omap::from-lists omap::lookup-of-update))
    
    (defrule bindings-of-make-reduce-proc
      (implies
        (equal s (proc->s (make-reduce-proc self parent children index)))
        (equal
          (omap::from-lists
            (list 'ChildPids 'Parent 'Index)
            (list (omap::lookup 'ChildPids (erl-state->bind s))
                  (omap::lookup 'Parent (erl-state->bind s))
                  (omap::lookup 'Index (erl-state->bind s))))
          (erl-state->bind s)))
      :enable (make-reduce-proc omap::from-lists omap::lookup-of-update))
   
    ; (defrule erl-state->bind-of-make-reduce-proc
    ;   (equal
    ;     (erl-state->bind
    ;       (proc->s (make-reduce-proc self parent children index)))
    ;     (omap::from-lists
    ;       (list 'ChildPids 'Parent 'Index)
    ;       (list (make-erl-val-cons :lst (pid-lst-fix children))
    ;             (erl-val-fix parent)
    ;             (make-erl-val-integer :val (nfix index)))))
    ;   :enable omap::from-lists)
    
    (defrule natp-of-index-of-make-reduce-proc
      (implies
        (equal s (proc->s (make-reduce-proc self parent children index)))
        (natp (erl-val-integer->val
                (omap::lookup 'Index (erl-state->bind s)))))
      :rule-classes (:rewrite :type-prescription)
      :enable (omap::from-lists omap::lookup-of-update)))