; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

; do-mv-capture.lisp -- a proof of NIL.
;
; No trust tag, no skip-proofs, no defaxiom, no progn!, no raw mode.
;
; ROOT CAUSE (variable capture by a "fresh" variable whose avoid-list is
; incomplete).
;
; TRANSLATE11-LOOP$ (translate.lisp:24583-24588) computes the avoid-list for
; the internal variables of a DO loop$ as
;
;    (append settable-vars
;            (set-difference-eq
;              (all-vars1-lst (list translated-mform translated-do-body
;                                   translated-fin-body) nil)
;              settable-vars))
;
; ALL-VARS1-LST collects only the FREE variables of those terms, so every
; LAMBDA-/LET-bound variable of the DO body is MISSING from the avoid-list.
;
; CMP-DO-BODY-MV-SETQ (translate.lisp:10670-10709) then generates the MV
; temporary for an MV-SETQ with
;
;    (genvar 'cmp-do-body "MV" 0 vars)        ; -> ACL2::MV0 when MV0 is not in vars
;
; and lays down  ((lambda (MV0 ...) ((lambda (v1..vk ...) <continuation>)
;                                    (mv-nth 0 MV0) ... ))
;                 <mv-expression> ...).
; A source comment there claims "mv-var really only needs to be distinct from
; v1, ... vk"; that is false.  It must also be distinct from every variable
; occurring free in <continuation>, which includes LET-bound variables of the
; DO body -- exactly the ones ALL-VARS1-LST does not report.
;
; So in BAD below, the user's (LET ((MV0 17)) ...) binding is *captured*: after
; the MV-SETQ, the reference to MV0 in (SETQ RESULT (CONS MV0 RESULT)) is
; rebound to the MV-SETQ's multiple value, and MAKE-LAMBDA-APPLICATION then
; drops the user's (LET ((MV0 17)) ..) binding altogether because MV0 no longer
; occurs free in the compiled body.  Compare :TRANS of the loop$.
;
; Consequence: the do$/lambda$ term that AXIOMATIZES the loop$ no longer means
; what the Common Lisp LOOP that IMPLEMENTS it computes.  (BAD '(1)) is
; '(1 ((NIL NIL 1))) in the logic but '(1 (17)) in raw Common Lisp.  Since
; guards are verified, raw Common Lisp is what runs.
;
; A metafunction observes the raw value: EV-FNCALL-META (rewrite.lisp:12559)
; calls EV-FNCALL! for a :COMMON-LISP-COMPLIANT metafunction, and EV-FNCALL!
; (rewrite.lisp:12547) is (mv nil (apply fn args) nil) in raw Lisp -- i.e. the
; raw function, with no safe-mode.  Hence MFN's test succeeds at rewrite time
; and fails in the logic, so the meta rule MRULE rewrites (FOO y) to 'NIL even
; though the metatheorem was proved with MFN logically the identity.

(in-package "ACL2")

(include-book "projects/apply/loop" :dir :system)

; ---------------------------------------------------------------------------
; A guard-verified DO loop$ whose logical meaning differs from its Common Lisp
; meaning, because of the capture described above.
;   logic:       (BAD '(1)) = (1 ((NIL NIL 1)))
;   common lisp: (BAD '(1)) = (1 (17))
; ---------------------------------------------------------------------------

(defun bad (x)
  (declare (xargs :guard (true-listp x)))
  (loop$ with temp = x with result = nil with len = 0
         do
         :guard (and (true-listp temp) (natp len))
         (let ((mv0 17))                     ; MV0 = genvar's first choice
           (if (null temp)
               (loop-finish)
             (progn (mv-setq (temp result len)
                             (mv (cdr temp) result (1+ len)))
                    (setq result (cons mv0 result)))))  ; MV0 used after MV-SETQ
         finally (return (list len result))))

; ---------------------------------------------------------------------------
; Route the divergence through a :META rule.
; ---------------------------------------------------------------------------

(defun foo (x) (declare (ignore x)) t)

(defevaluator evl evl-lst ((foo x)))

(defun mfn (term)
  (declare (xargs :guard (pseudo-termp term)))

; Logically (BAD '(1)) is '(1 ((NIL NIL 1))), so this is the identity and the
; metatheorem below is trivially true.  In raw Common Lisp (BAD '(1)) is
; '(1 (17)), so at rewrite time MFN maps every term to 'NIL.

  (if (equal (bad '(1)) '(1 (17)))
      *nil*
    term))

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm mrule
  (equal (evl x a) (evl (mfn x) a))
  :rule-classes ((:meta :trigger-fns (foo))))
)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm step1
  (equal (foo y) nil)
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(mrule) (theory
                                                       'minimal-theory)))))
)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal" :use ((:instance step1 (y 0))))))
)
