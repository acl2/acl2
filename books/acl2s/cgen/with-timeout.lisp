#|$ACL2s-Preamble$;
(begin-book t :ttags ((:acl2s-timeout)))
;$ACL2s-Preamble$|#

;Author: Harsh Raju Chamarthi
;Acknowledgements: Matt Kaufmann provided significant help.

(in-package "ACL2")

; We exclude Lisps not handled by macro with-timeout-raw in file
; with-timeout-raw.lsp (and perhaps there are other such), as follows.

; cert_param: (non-cmucl)
; cert_param: (non-lispworks)
; cert_param: (non-allegro)
; cert_param: (non-gcl)

(include-book "xdoc/top" :dir :system)
(defxdoc with-timeout
  :parents (acl2::cgen acl2::miscellaneous) ; the latter helps ACL2-only :doc
  :short  "Evaluate form with a timeout (in seconds)"
  :long
  "<p>Evaluate form with a timeout in seconds. </p>

  <p>The general form is:
  @({with-timeout duration body timeout-form})
  </p>

  <p>
  @('duration') can be any rational value.  A duration of 0 seconds disables
  the timeout mechanism, i.e its a no-op. Suppose it is not, and @('duration')
  seconds elapse during evaluation of <tt>body</tt> then the evaluation is aborted
  and the value of @('timeout-form') is returned; in the normal case the value
  of <tt>body</tt> is returned.
  </p>
  <p> The signature of <tt>body</tt> and <tt>timeout-form</tt> should be the same.  </p>

  <h3>Advanced Notes:</h3>
  <p>
  This form should be called either at the top-level or in
  an environment where state is available and <tt>body</tt> has
  no free variables other than state.
  If the timeout-form is a long running computation,
  then the purpose of with-timeout is defeated.
  </p>

  <code>
    Usage:
    (with-timeout 5 (fibonacci 40) :timed-out)
    :doc with-timeout
  </code>
"
  )

(defttag :acl2s-timeout)

(progn!
 (set-raw-mode t)
 (load (concatenate 'string (cbd) "with-timeout-raw.lsp")))

(defmacro-last with-timeout-aux)

;; Defined this way to be compatible with make-event.
;; If time is 0, we set a timeout of 2^20 seconds ~ 12 days
(defmacro with-time-limit (time form)
  `(with-prover-time-limit
    (if (equal ,time 0) (expt 2 20) ,time)
    ,form))

(defmacro with-timeout (duration form timeout-form)
"can only be called at top-level, that too only forms that are allowed
to be evaluated inside a function body. To eval defthm, use
with-timeout-ev instead"
`(if (equal 0 ,duration) ;if 0 then timeout is disabled
     ,form
   (top-level (with-timeout1 ,duration ,form ,timeout-form))))


;the following is for internal use only. I use it in timing out
;top-level-test? form, where i manually make a function body
;corresponding to the top-level-test?-fn, this way I dont have to
;worry about capturing free variables

(defmacro with-timeout1 (duration form timeout-form)
"can only be used inside a function body, and if form has
free variables other than state, then manually make a function
which takes those free variables as arguments and at the calling
context, pass the arguments, binding the free variables.
See top-level-test? macro for an example"
`(if (equal 0 ,duration) ;if 0 then timeout is disabled
    ,form
  (with-timeout-aux '(,duration ,timeout-form) ,form)))

(defttag nil) ; optional (books end with this implicitly)


