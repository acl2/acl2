; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

; Soundness exploit #2: ACL2 2-D array bug in compress2's "already in normal
; form" test.
;
; /home/claude/acl2/axioms.lisp:13772-13783 .  The comment at :13756 says the
; test decides whether l has "strictly ascending keys", but the test only
; rejects a *strictly descending* adjacent pair:
;
;    ((or (> (caaar tl) (caaadr tl))
;         (and (= (caaar tl) (caaadr tl))
;              (> (cdaar tl) (cdaadr tl))))
;     (setq in-order nil) (return nil))
;
; Two adjacent EQUAL keys therefore pass as "in order", so raw compress2
; returns l unchanged, while the logical compress2 (compress21/compress211,
; which use assoc2) drops the shadowed duplicate.  The 1-D analogue in
; compress1 (axioms.lisp:13289-13296) correctly uses >= / <= .

(in-package "ACL2")

; array2p holds of *k*: dimensions (1 1), 1*1 = 1 < 3 = :maximum-length,
; keys are (0 . 0) with 0 < 1, values differ from the :default (2).
(defconst *k*
  '((:header :dimensions (1 1) :maximum-length 3 :default 2 :name a)
    ((0 . 0) . 1)
    ((0 . 0) . 1)))

; A copy of the *logical* (#+acl2-loop-only) body of COMPRESS2, under a new
; name, so that it has no raw-Lisp counterpart.
(defun my-compress2 (name l)
  (declare (xargs :guard (array2p name l) :verify-guards nil))
  (cons (header name l)
        (compress21 name l 0
                    (car (dimensions name l))
                    (cadr (dimensions name l))
                    (default name l))))

(defun raw-c2 ()
  (declare (xargs :verify-guards nil))
  (compress2 'a *k*))

(defun log-c2 ()
  (declare (xargs :verify-guards nil))
  (my-compress2 'a *k*))

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm diff
  (not (equal (raw-c2) (log-c2)))
  :hints (("Goal" :in-theory (union-theories
                              '((:executable-counterpart raw-c2)
                                (:executable-counterpart log-c2))
                              (theory 'minimal-theory))))
  :rule-classes nil)
)

(defthm compress2-is-my-compress2
  (equal (compress2 name l)
         (my-compress2 name l))
  :hints (("Goal" :in-theory (enable compress2 my-compress2))))

(defthm same
  (equal (raw-c2) (log-c2))
  :hints (("Goal" :in-theory (union-theories
                              '((:definition raw-c2)
                                (:definition log-c2)
                                compress2-is-my-compress2)
                              (theory 'minimal-theory))))
  :rule-classes nil)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm nil-proved
  nil
  :hints (("Goal" :use (diff same)
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil)
)
