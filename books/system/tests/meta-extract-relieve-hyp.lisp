; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug fixed before ACL2 Version 8.8.

; Finding 27: MFC-RELIEVE-HYP reports success for a *binding* hypothesis.
;
; RELIEVE-HYP (rewrite.lisp:17827-17855) has a branch, guarded by BINDING-HYP-P
; (type-set-b.lisp:7463-7507), for a hypothesis of the form (EQUAL v term) where
; v is free w.r.t. the unify substitution and term is ground w.r.t. it.  That
; branch proves NOTHING: it returns wonp = T after consing (v . rewritten-rhs)
; onto UNIFY-SUBST, and the caller's obligation is to keep that extended
; substitution.  MFC-RELIEVE-HYP-RAW (ld.lisp:4774-4778) explicitly
;   (declare (ignore step-limit failure-reason new-unify-subst memo))
; and answers T for wonp in '(t :unify-subst-list).
; META-EXTRACT-CONTEXTUAL-FACT (boot-strap-pass-2-a.lisp:1328-1332) then hands
; the metafunction (SUBLIS-VAR ALIST HYP) -- computed with the ORIGINAL alist, so
; v is still free -- as a term it may assume is TRUE for arbitrary bindings.
; Asking twice with different right-hand sides gives (EQUAL Y '3) and (EQUAL Y '4).
; Host-Lisp independent (reproduced under SBCL and CCL).
; FIX: return NIL when RELIEVE-HYP extended the unify substitution (equivalently,
; when the BIND-FLG branch was taken).  Every other wonp = T branch of
; RELIEVE-HYP returns UNIFY-SUBST unchanged.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(must-fail
 (encapsulate ()
   (defun bad (x) (declare (xargs :guard t) (ignore x)) t)
   (defthmd bad-is-t (equal (bad x) t))
   (in-theory (disable bad (:type-prescription bad) (:executable-counterpart bad)))
   (defevaluator mev mev-lst ((equal a b) (bad x)) :namedp t)
   (defun mf (term mfc state)
     (declare (xargs :stobjs state))
     (if (and (consp term)
              (eq (car term) 'bad)
              (mfc-relieve-hyp '(equal y '3) nil '(:rewrite default-car)
                               '(car '1) 1 mfc state :forcep nil)
              (mfc-relieve-hyp '(equal y '4) nil '(:rewrite default-car)
                               '(car '1) 1 mfc state :forcep nil))
         ''nil
       term))
   (defthm mf-correct
     (implies (and (mev (meta-extract-contextual-fact
                         '(:relieve-hyp (equal y '3) nil (:rewrite default-car)
                                        (car '1) 1)
                         mfc state)
                        a)
                   (mev (meta-extract-contextual-fact
                         '(:relieve-hyp (equal y '4) nil (:rewrite default-car)
                                        (car '1) 1)
                         mfc state)
                        a))
              (equal (mev term a) (mev (mf term mfc state) a)))
     :rule-classes ((:meta :trigger-fns (bad))))
   (defthm relieve-hyp-nil nil :rule-classes nil
     :hints (("Goal" :use ((:instance bad-is-t (x '0))))))))
