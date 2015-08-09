; Here we show how to use the warnings to discover missing congruence rules.

(in-package "ACL2")

; Include the standard mini-proveall events.
(include-book "mini-proveall")

; Now let us consider the events from the above book that gave Double-rewrite
; warnings.  Each is shown followed by the warning generated and then a defcong
; that fixes the warning.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm insert-is-cons[again]
  (perm (insert a x) (cons a x)))

; Note that perm is preserved at x in (cons a x) because of this rule,
; previously-proved:
; (defcong perm perm (cons x y) 2)

#|
ACL2 Warning [Double-rewrite] in ( DEFTHM INSERT-IS-CONS[AGAIN] ...):
In a :REWRITE rule generated from INSERT-IS-CONS[AGAIN], equivalence
relation PERM is maintained at one problematic occurrence of variable
X in the right-hand side, but not at any binding occurrence of X.
Consider replacing that occurrence of X in the right-hand side with
(DOUBLE-REWRITE X).  See :doc double-rewrite for more information on
this issue.
|# ; |

(defcong perm perm (insert a x) 2)

(defthm insert-is-cons[again-no-warn]
  (perm (insert a x) (cons a x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm insert-sort-is-id[again]
  (perm (insert-sort x) x))

#|
ACL2 Warning [Double-rewrite] in ( DEFTHM INSERT-SORT-IS-ID[AGAIN]
...):  In a :REWRITE rule generated from INSERT-SORT-IS-ID[AGAIN],
equivalence relation PERM is maintained at one problematic occurrence
of variable X in the right-hand side, but not at any binding occurrence
of X.  Consider replacing that occurrence of X in the right-hand side
with (DOUBLE-REWRITE X).  See :doc double-rewrite for more information
on this issue.
|# ; |

(defcong perm perm (insert-sort x) 1)

(defthm insert-sort-is-id[again-no-warn]
  (perm (insert-sort x) x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Warns during certification of mini-proveall.lisp but not here, because of the
; defcong that immediately follows app-commutes in mini-proveall.lisp.
(defthm app-commutes[again]
  (perm (app a b) (app b a)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rev-is-id[again]
  (perm (rev x) x))

#|
ACL2 Warning [Double-rewrite] in ( DEFTHM REV-IS-ID[AGAIN] ...):  In
a :REWRITE rule generated from REV-IS-ID[AGAIN], equivalence relation
PERM is maintained at one problematic occurrence of variable X in the
right-hand side, but not at any binding occurrence of X.  Consider
replacing that occurrence of X in the right-hand side with
(DOUBLE-REWRITE X).  See :doc double-rewrite for more information on
this issue.
|# ; |

(defcong perm perm (rev x) 1)

(defthm rev-is-id[again-no-warn]
  (perm (rev x) x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rev-rev-again[again]
  (== (rev (rev x)) x))

#|
ACL2 Warning [Double-rewrite] in ( DEFTHM REV-REV-AGAIN[AGAIN] ...):
In a :REWRITE rule generated from REV-REV-AGAIN[AGAIN], equivalence
relation == is maintained at one problematic occurrence of variable
X in the right-hand side, but not at any binding occurrence of X.
Consider replacing that occurrence of X in the right-hand side with
(DOUBLE-REWRITE X).  See :doc double-rewrite for more information on
this issue.
|# ; |

(defcong == == (rev x) 1)

(defthm rev-rev-again[again-no-warn]
  (== (rev (rev x)) x))
