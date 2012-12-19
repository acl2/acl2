#|$ACL2s-Preamble$;
;;Author - Harsh Raju Chamarthi (harshrc)
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis.lsp")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

;; Note: I apologize for the use of ttags, but they are used for engineering
;; purposes: for implementing timeouts. The above should in principle not
;; affect ACL2's soundness. Usually you would include this book while
;; developing/designing proofs and when you have all QEDs, simply remove this
;; book.


(in-package "ACL2")

(include-book "acl2s-parameter")
(include-book "main" :ttags :all)
(include-book "base")


; initialize gcs% global which keeps track of the
; number of cts/wts collected across a thm/defthm/test?
(make-event
;idempotent. everytime top.lisp is included, the
;globals for recording cts/wts are reset.
 (b* ((gcs%  (defdata::initial-gcs% 
              (acl2s-defaults :get num-counterexamples)
              (acl2s-defaults :get num-witnesses)
              0 (cons nil t)))
      (defdata::vl (acl2s-defaults :get verbosity-level))
      (defdata::ctx 'top.lisp)
      (state (defdata::put-gcs%-global gcs%))
      (state (defdata::put-s-hist-global '()))
      (- (defdata::cw? (defdata::verbose-flag defdata::vl)
              "Initializing gcs% global in top.lisp~%")))
   (value '(value-triple :gcs%-global-initialized)))
 :check-expansion t)
  


; For now lets keep the nats not more than 1000 to avoid stack-overflow
; on non-tail-recursive functions. If you dont like these, comment
; them out, or write your own custom test enumerators and attach them
(defdata-testing pos :test-enumerator nth-pos-testing)
(defdata-testing integer :test-enumerator nth-integer-testing)
(defdata-testing nat :test-enumerator nth-nat-testing)
(defdata-testing neg :test-enumerator nth-neg-testing)


; The following shows the various configuration parameters that you
; can customize.
; The usual format is (acl2s-defaults :get <param>) for getting the
; current value of the parameter named <param>. The setter is similar
; you can see examples below, where most useful parameters are set
; with their default values. Copy and change what you want, these are
; embedded events, so you can put them in books. To know more about
; these parameters, simply do :doc <param> at the ACL2 prompt.

;; (acl2s-defaults :set testing-enabled :naive) ;other values are T,NIL
;; (acl2s-defaults :set verbosity-level 1) 
;; (acl2s-defaults :set num-trials 1000)
;; (acl2s-defaults :set num-counterexamples 3)
;; (acl2s-defaults :set num-witnesses 3)
;; (acl2s-defaults :set search-strategy :simple) ;other value is :incremental
;; (acl2s-defaults :set sampling-method :random) 
;; (acl2s-defaults :set subgoal-timeout 10) ;0 turns off timeout


;; USAGE:
;; Add (include-book "countereg-gen/top" :dir :system :ttags :all)
;; Add (acl2s-defaults :set testing-enabled T) if you want to add
;; full-blown testing+theorem-proving.
;; Add (acl2s-defaults :set testing-enabled :naive) if you want to
;; do simple testing without invoking the mighty theorem prover.

;; EXAMPLES:
;; Check our testing-regression.lsp

;; NOTE: If you want to browse code, you might wonder what def, f* etc
;; mean. You should then first read basis.lisp to understand what they do