; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug in ACL2 Version 8.7
; fixed before ACL2 Version 8.8.  We exclude GCL, however, since (code-char
; 300) returns nil in a version of GCL circa 2025 or 2026.
; cert_param: (non-gcl)

; Finding 67: ev-synp evaluates a bind-free term without safe-mode, and
; bad-synp-alist1 accepts (QUOTE <anything>) as a "legal term", so a bind-free
; hypothesis can bind a rewrite-rule variable to a non-ACL2 object.
;
; THE TWO HALVES.
;
; (a) ev-synp (rewrite.lisp:12603) ends with
;        (ev (get-evg synp-term 'ev-synp) unify-subst2 state nil t t)
;     and the comment immediately above it, rewrite.lisp:12626-12631, records
;     the decision verbatim:
;
;        "It is tempting to bind the state global safe-mode to t here, using
;         state-global-let*.  However, we cannot do that without returning
;         state, which we want to avoid since the caller, relieve-hyp, does not
;         return state.  Since synp is only used heuristically, it really isn't
;         necessary to use safe mode..."
;
;     The stated justification is correct for SYNTAXP, whose value is only a
;     fire/don't-fire flag.  It is FALSE for BIND-FREE, whose value becomes
;     part of the unifying substitution and therefore part of the instantiated
;     rule.
;
; (b) bad-synp-alist1 (rewrite.lisp:12635) validates each binding with only
;        ((not (termp value wrld)) ...)
;     and termp's quote case (translate.lisp:27-29) is
;        ((eq (car x) 'quote) (and (consp (cdr x)) (null (cddr x))))
;     -- it never inspects the quoted object.
;
; So a :program-mode generator returning ((Y . (QUOTE #\<code 300>))) passes
; both checks, and the rule below -- which is VACUOUSLY TRUE in the logic,
; since its hypothesis (not (< (char-code y) 256)) contradicts the axiom
; char-code-linear -- fires, rewriting (bar x) to nil.
;
; THE SIBLING THAT IS PROTECTED: make-event's bad-lisp-objectp check
; (other-events.lisp:34720) was made UNCONDITIONAL before ACL2 8.8 for exactly
; this class of leak; its regression book is
; books/system/tests/make-event-bad-char.lisp.  ev-synp was not covered.
;
; The :linear rule class reaches the identical ev-synp call through
; bad-synp-hyp-msg-for-linear (defthm.lisp:2196), so the hole is not confined
; to :rewrite.
;
; POLARITY: RED while present -- BAD-RULE is admissible (it is vacuously true)
; and the MUST-FAIL on NIL-PROVED fails because the rule fires anyway.  GREEN
; once ev-synp runs in safe-mode or bad-synp-alist1 inspects the quoted object.

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

; A :program-mode generator.  ACL2 calls raw Lisp for it, so (code-char 300)
; returns a character object whose char-code is 300 -- not an ACL2 object.
(defun n91-mk ()
  (declare (xargs :mode :program))
  (list (cons 'y (list 'quote (code-char 300)))))

(defun n91-bar (x) (declare (ignore x)) t)

; Must stay provable: this is just n91-bar's definition.
(defthm n91-bar-is-t (equal (n91-bar x) t) :rule-classes nil)

; Admissible, and VACUOUSLY TRUE: no ACL2 character has char-code >= 256, so
; the hypothesis is unsatisfiable and the rule says nothing.  It must stay
; admissible after a fix -- the fix is to stop it FIRING, not to reject it.
(defthm n91-bad-rule
  (implies (and (bind-free (n91-mk) (y))
                (not (< (char-code y) 256)))
           (equal (n91-bar x) nil)))

; THE DEFECT: the vacuous rule fires, because the bad character satisfies
; (not (< (char-code y) 256)) under raw evaluation.
(must-fail
 (defthm n91-nil-proved
   nil
   :hints (("Goal" :use n91-bar-is-t :in-theory (disable n91-bar)))
   :rule-classes nil)
; Added by Matt Kaufmann, since now we get a hard error:
 :expected :hard)

; CONTROL 1: a LEGAL character binding must not fire the rule, since
; (char-code #\a) = 97 < 256.  Pins the defect to the bad object rather than
; to bind-free itself.
(defun n91-mk-ok ()
  (declare (xargs :mode :program))
  (list (cons 'y (list 'quote (code-char 97)))))

(defun n91-baz (x) (declare (ignore x)) t)
(defthm n91-baz-is-t (equal (n91-baz x) t) :rule-classes nil)
(defthm n91-ok-rule
  (implies (and (bind-free (n91-mk-ok) (y))
                (not (< (char-code y) 256)))
           (equal (n91-baz x) nil)))
(must-fail
 (defthm n91-control-legal-char
   nil
   :hints (("Goal" :use n91-baz-is-t :in-theory (disable n91-baz)))
   :rule-classes nil))

; CONTROL 2: ordinary bind-free must keep working, so the fix cannot be to ban
; it.  A :logic-mode generator binding Y to a legitimate quoted term.
(defun n91-mk-logic (x) (declare (ignore x)) (list (cons 'y (list 'quote 3))))
(defun n91-qux (x) (declare (ignore x)) 7)
(defthm n91-control-bind-free-works
  (implies (and (bind-free (n91-mk-logic x) (y))
                (equal y 3))
           (equal (n91-qux x) 7))
  :rule-classes nil)
