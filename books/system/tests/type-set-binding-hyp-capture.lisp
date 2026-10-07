; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 42: type-set-relieve-hyps (type-set-b.lisp:8633) binds a
; :type-prescription rule's binding hypothesis (equal v rhs) to the
; UNINSTANTIATED rhs.  binding-hyp-p (type-set-b.lisp:7463) guarantees every
; variable of rhs IS bound in the unifying substitution -- that is one of its
; three conjuncts -- so failing to apply the substitution lets the rule's own
; variables escape into the goal's namespace, where a like-named variable of
; the conjecture satisfies the hypothesis.  The two sibling consumers of
; binding-hyp-p both instantiate: relieve-hyp (rewrite.lisp:17852) binds v to
; the REWRITTEN rhs, and pc-relieve-hyp (other-events.lisp:27562) binds it to
; (sublis-var unify-subst (fargn hyp 2)).
;
; Present since the initial population of the git trunk (2010-09-21) and
; unchanged since except for the bkptr argument added for note-4-2; the
; mechanism it belongs to is dated Version 2.7 (2002) by its own comment.
;
; This test goes GREEN when the missing instantiation is added.  Note it is
; a SOFT failure: the false theorem simply stops being provable.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(local (defun f (x) (if (consp x) 0 'a)))

; An honest theorem, admitted normally, stored with
;   :TERM (F X)   :HYPS ((EQUAL V X) (CONSP V))
(local
 (defthm f-tp
   (implies (and (equal v x)
                 (consp v))
            (integerp (f x)))
   :rule-classes ((:type-prescription :typed-term (f x)))))

(local (in-theory (disable f (:e f) (:t f))))

; FALSE: x = '(1), y = 0 gives (implies t (integerp 'a)).
; Applying F-TP to (f y) gives alist ((x . y)); the binding hypothesis must
; extend it with (v . y), but extends it with (v . x) instead, so the second
; hypothesis is checked as (consp x) -- which the conjecture supplies.
(must-fail
 (local
  (defthm bad
    (implies (consp x) (integerp (f y)))
    :rule-classes nil)))

; The same defect delivered through a forcing round: the assumption record is
; generated for the rule's variable rather than the target's.
(local (defun ff (x) (if (consp x) 0 'bad)))
(local (defun gg (x) (if (consp x) 0 'bad)))
(local
 (defthm gg-tp-forced
   (implies (and (equal v (ff x))
                 (force (natp v)))
            (natp (gg x)))
   :rule-classes ((:type-prescription :typed-term (gg x)))))
(local (in-theory (disable ff gg (:e ff) (:e gg) (:t ff) (:t gg))))

(must-fail
 (local
  (defthm bad-forced
    (implies (natp (ff x)) (natp (gg a)))
    :rule-classes nil)))
