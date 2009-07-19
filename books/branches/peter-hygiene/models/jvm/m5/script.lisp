; You might want to comment out the certification of apprentice.lisp.

; (ld "script.lisp" :ld-pre-eval-print t)

(ld "m5.acl2")
(include-book "ordinals/e0-ordinal" :dir :system)
(certify-book "m5" 4)
(ubt! 1)
; -----------------------------------------------------------------
(include-book "m5")
(certify-book "utilities" 1)
(ubt! 1)
; -----------------------------------------------------------------
(include-book "utilities")
(certify-book "demo" 1)
(ubt! 1)
; -----------------------------------------------------------------
(include-book "utilities")
(certify-book "idemo" 1)
(ubt! 1)
; -----------------------------------------------------------------
; This next book is only around so that I can load it for demos in which
; I prove the theorem that recursive factorial is correct.

(include-book "utilities")
(certify-book "jvm-fact-setup" 1)
(ubt! 1)
; -----------------------------------------------------------------
(include-book "m5")
(certify-book "apprentice-state" 1)
(ubt! 1)
; -----------------------------------------------------------------
; The certification of apprentice.lisp takes about 50 minutes and generates about
; 70MB of output.  

(ld '((include-book "m5")
      (certify-book "apprentice" 1))
    :standard-co "apprentice.log"
    :proofs-co   "apprentice.log"
    :ld-pre-eval-print t)
(ubt! 1)
; -----------------------------------------------------------------
(certify-book "perm")
(ubt! 1)
; -----------------------------------------------------------------
(include-book "utilities")
(certify-book "isort" 1)
(ubt! 1)
; -----------------------------------------------------------------
(include-book "utilities")
(certify-book "partial" 1)
(ubt! 1)
; -----------------------------------------------------------------
(include-book "utilities")
(certify-book "universal" 1)
(ubt! 1)
; -----------------------------------------------------------------
(include-book "universal")
(certify-book "universal-never-returns" 1)
(ubt! 1)
; -----------------------------------------------------------------
(certify-book "infinite-fair-schedule")
(ubt! 1)
; -----------------------------------------------------------------