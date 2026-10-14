; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 55: a hash-table or stobj-table field operation on a :CONGRUENT-TO
; stobj flushes the WRONG memoization list, so a memoized reader keeps a stale
; value after the table is written.
;
; defstobj-field-fns-raw-defs (basis-a.lisp, declared :8710) emits the stobj's
; OWN name as the memoize-flush argument at the four hash-table-family sites --
; basis-a.lisp:8847 (<fld>-PUT), :8884 (<fld>-REM), :8898 (<fld>-CLEAR),
; :8906 (<fld>-INIT) -- while every array and scalar field operation correctly
; emits the congruent representative: :8973 (array resize), :9019 (array
; updater), :9037 and :9067 (scalar updaters).
;
; FLUSH-VAR is bound at basis-a.lisp:9451-9465 to nil when :non-memoizable, else
; to (congruent-stobj-rep congruent-to wrld), else to NAME.  memoize-fn registers
; a memoized function's table under (st-lst (congruent-stobj-rep ...)) --
; memoize-raw.lisp:3570-3601 -- i.e. under the REPRESENTATIVE, and
; (st-lst name) is defg'd only when congruent-to is nil (basis-a.lisp:9557-9560).
; So for h2 :congruent-to h1, (ht2-put k v h2) flushes (st-lst 'h2), which is
; permanently NIL, and never (st-lst 'h1), where the table lives.  Measured:
;   (st-lst H1) = (...MEMOIZE-HT-FOR-...RD...)        (st-lst H2) = NIL
;
; This is NOT the historical ACL2 6.1 bug (doc.lisp:96439-96445), which was about
; a :congruent-to field that was not the canonical representative and which was
; fixed by converting the scalar and array sites to FLUSH-VAR.  Hash-table and
; stobj-table fields were added much later and were never converted.  Here h1 IS
; the representative, and h2 :congruent-to h1 suffices.
;
; POLARITY: the MUST-FAIL states the CORRECT behaviour -- after (ht2-rem 0 h2)
; the read must be NIL, so (test) must be false.  RED while present.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defstobj h1 (ht1 :type (hash-table eql)))
(defstobj h2 (ht2 :type (hash-table eql)) :congruent-to h1)

(defun rd (h1) (declare (xargs :stobjs h1)) (ht1-get 0 h1))

(defun test ()
  (with-local-stobj
   h2
   (mv-let (val h2)
           (let* ((h2 (ht1-put 0 3 h2))   ; flushes (ST-LST 'H1) -- correct
                  (v1 (rd h2))            ; caches 3
                  (h2 (ht2-rem 0 h2))     ; flushes (ST-LST 'H2) -- WRONG LIST
                  (v2 (rd h2)))           ; should be NIL, is 3
             (mv (equal v1 v2) h2))
           val)))

; Before memoization the logic and the raw code agree: the value really does
; change, so (test) is false.  This is the honest half and must stay provable.
(defthm true-prop (not (test)) :rule-classes nil)

(memoize 'rd)

; THE DEFECT: with rd memoized, the stale 3 survives ht2-rem, so (test)
; evaluates to T -- one ground term with two values.
(must-fail (defthm false-prop (test) :rule-classes nil))
