; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../core/top")

(set-induction-depth-limit 1)

; Erl-State Module Theorems ----------------------------------------------------

; The theorems below reason about what happens to the module field of an
; erl-state after various operations.

(local (defrule erl-state->module-of-eval-match
  (equal (erl-state->module (eval-match p s))
         (erl-state->module s))
  :enable eval-match))

(local (defrule erl-state->module-of-match-args
  (equal (erl-state->module (match-args cs args s))
         (erl-state->module s))
  :enable match-args))

(local (defrule erl-state->module-of-eval-clauses-when-consp
  (equal (erl-state->module (mv-nth 0 (eval-clauses-when-consp args cls s)))
         (erl-state->module s))
  :enable eval-clauses-when-consp))

(local (defrule erl-state->module-of-eval-clauses
  (equal (erl-state->module (mv-nth 0 (eval-clauses args cls s)))
         (erl-state->module s))
  :enable eval-clauses))

(local (defrule erl-state->module-of-local-call
  (implies
    (and (not (mv-nth 1 (eval-local-call s c args)))
         (wf-state-p (mv-nth 0 (eval-local-call s c args))))
    (equal (erl-state->module s)
           (erl-state->module (mv-nth 0 (eval-local-call s c args)))))
  :enable (eval-local-call)))

(local (defrule erl-state->module-of-remote-call
  (implies
    (and (not (mv-nth 1 (eval-remote-call s m c args)))
         (wf-state-p (mv-nth 0 (eval-remote-call s m c args))))
    (equal (erl-state->module s)
           (erl-state->module (mv-nth 0 (eval-remote-call s m c args)))))
  :enable (eval-remote-call)))

(defrule erl-state->module-of-fun-call
  (implies
    (and (not (mv-nth 1 (eval-fun-call s c args)))
         (wf-state-p (mv-nth 0 (eval-fun-call s c args))))
    (equal (erl-state->module s)
           (erl-state->module (mv-nth 0 (eval-fun-call s c args)))))
  :enable (eval-fun-call))

(local (defrule erl-state->module-of-erl-receive
  (equal (erl-state->module (mv-nth 0 (eval-receive s clauses)))
         (erl-state->module s))
  :enable eval-receive))

(local (defrule eval-k-of-module
  (implies 
    (not (or (equal (kont-kind (erl-k->kont k)) :local-call)
             (equal (kont-kind (erl-k->kont k)) :remote-call)
             (equal (kont-kind (erl-k->kont k)) :fun-call)
             (equal (kont-kind (erl-k->kont k)) :function-return)))
    (equal (erl-state->module (erl-s-klst->s (eval-k k s)))
           (erl-state->module s)))
  :enable eval-k))

; Some Useful Lemmas -----------------------------------------------------------
(local (defrule erl-state->module-of-apply-function-return
  (implies
    (and (wf-state-p (apply-k s (list k)))
         (equal (kont-kind (erl-k->kont k)) :function-return))
    (equal (erl-state->module (apply-k s (list k)))
           (kont-function-return->module (erl-k->kont k))))
  :expand (:free (x) (apply-k x (list k)))
  :enable eval-k))

(local (defrule module-of-kont-call-when-wf-state-p
  (implies
    (and
      (consp klst)
      (erl-s-klst->klst (eval-k (car klst) s))
      (or (equal (kont-kind (erl-k->kont (car klst))) :local-call)
          (equal (kont-kind (erl-k->kont (car klst))) :remote-call)
          (equal (kont-kind (erl-k->kont (car klst))) :fun-call))
      (wf-state-p (apply-k s klst)))
    (equal (erl-state->module
             (apply-k (erl-s-klst->s (eval-k (car klst) s))
                      (erl-s-klst->klst (eval-k (car klst) s))))
           (erl-state->module s)))
  :expand ((eval-k (car klst) s))
  :use ((:instance wf-state-implies-next-wf-state))))


(local (defrule eval-k-of-module-when-null-rklst
  (implies (and (not (erl-s-klst->klst (eval-k k s)))
                (not (equal (kont-kind (erl-k->kont k)) :function-return))
                (wf-state-p (erl-s-klst->s (eval-k k s))))
           (equal (erl-state->module (erl-s-klst->s (eval-k k s)))
                  (erl-state->module s)))
  :enable (eval-k eval-remote-call eval-local-call eval-fun-call)))

; Helpers ----------------------------------------------------------------------

; Helper function that states the klst has no function-return continuations.
(local (defun no-function-return (klst)
  (if (consp klst)
      (and
        (not (equal (kont-kind (erl-k->kont (car klst))) :function-return))
        (no-function-return (cdr klst)))
      t)))

(local (defrule no-function-return-of-append
  (implies (and (no-function-return l1) (no-function-return l2))
           (no-function-return (append l1 l2)))))

(local (defrule no-function-return-of-kind
  (implies 
    (and (consp klst)
         (not (or (equal (kont-kind (erl-k->kont (car klst))) :local-call)
                  (equal (kont-kind (erl-k->kont (car klst))) :remote-call)
                  (equal (kont-kind (erl-k->kont (car klst))) :fun-call)))
         (no-function-return klst))
    (no-function-return (erl-s-klst->klst (eval-k (car klst) s))))
  :enable eval-k))

; Induction Schema -------------------------------------------------------------

(local (define module-induct (s klst)
  :measure (klst-measure klst)
  :verify-guards nil
  :enabled t
  (if (endp klst)
      t
      (b* ((k (car klst))
           (ks (eval-k k s))
           (r (erl-s-klst->s ks))
           (rklst (erl-s-klst->klst ks))
           ((if (null rklst)) (module-induct r (cdr klst)))
           (rk1 (car rklst))
           (kont (erl-k->kont k))
           ((if (not (> (erl-k->fuel rk1) 0))) t))
          (kont-case kont
            (:expr (module-induct r (append rklst (cdr klst))))
            (:exprs (module-induct r (append rklst (cdr klst))))
            (:cons (module-induct r (append rklst (cdr klst))))
            (:cons-merge (module-induct r (append rklst (cdr klst))))
            (:tuple (module-induct r (append rklst (cdr klst))))
            (:unop (module-induct r (append rklst (cdr klst))))
            (:binop-expr1 (module-induct r (append rklst (cdr klst))))
            (:binop-expr2 (module-induct r (append rklst (cdr klst))))
            (:match (module-induct r (append rklst (cdr klst))))
            (:catch (module-induct r (append rklst (cdr klst))))
            (:case-of (module-induct r (append rklst (cdr klst))))
            (:fun-call-args (module-induct r (append rklst (cdr klst))))

            ; The schema differes from apply-k in these cases
            (:local-call (module-induct (apply-k r rklst) (cdr klst)))
            (:remote-call (module-induct (apply-k r rklst) (cdr klst)))
            (:fun-call (module-induct (apply-k r rklst) (cdr klst)))
            (:function-return t)
            (:receive (module-induct r (append rklst (cdr klst)))))))

  ; for termination proof
  :hints (("Goal" :in-theory (disable eval-k-decreases-klst-measure)
                  :use ((:instance eval-k-decreases-klst-measure
                          (k (car klst)) (kl (cdr klst))))))))

; apply-k-of-module ------------------------------------------------------------

; module remains the same after apply-k if there is no function return.
(local (defrule apply-k-of-module-when-list
  (implies
    (and (no-function-return klst) (wf-state-p (apply-k s klst)))
    (equal (erl-state->module (apply-k s klst))
           (erl-state->module s)))
  :induct (module-induct s klst)
  :expand ((apply-k s klst))
  ; TODO: replace with computed hint
  :hints
    (("Subgoal *1/18"
       :in-theory (enable apply-k-of-append))
     ("Subgoal *1/17"
       :in-theory (enable apply-k-of-append))
     ("Subgoal *1/16"
       :in-theory (enable apply-k-of-append)))))

; module does not change after evaluating any continuation that is not :function-return
(defrule apply-k-of-module
  (implies 
    (and (wf-state-p (apply-k s (cons k nil)))
         (not (equal (kont-kind (erl-k->kont k)) :function-return)))
    (equal (erl-state->module (apply-k s (cons k nil)))
           (erl-state->module s)))
  :use (:instance apply-k-of-module-when-list (s s) (klst (cons k nil))))