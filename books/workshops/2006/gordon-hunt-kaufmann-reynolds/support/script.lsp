; Usage:
; Start up ACL2 and then:
; (ld "script.lisp" :ld-pre-eval-print t)

(certify-book "data")
:u
(certify-book "basic")
:u
(certify-book "guarded")
:u
(certify-book "stobjs")
:u

(include-book "basic")
:comp t
(include-book "guarded")
(include-book "stobjs")

(time$ (f-put-global 'basic-result   (run   *big-instr-list* nil nil) state))
(time$ (f-put-global 'guarded-result (g$run *big-instr-list* nil nil) state))
(time$ (mv-let (vals st) (s$run *big-instr-list* st nil)
         (let ((state (f-put-global 'stobjs-result vals state)))
           (mv state st))))

(equal (@ basic-result) (@ guarded-result))
(equal (@ basic-result) (@ stobjs-result))
