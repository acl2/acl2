#|$ACL2s-Preamble$;
(begin-book t :ttags ((:acl2s-timeout)))
;$ACL2s-Preamble$|#

;Author: Harsh Raju Chamarthi
;Acknowledgements: Many thanks to Matt Kaufmann.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defxdoc with-timeout
  :parents (testing)
  :short "Evaluate form with a timeout (in seconds)"
  :long "Evaluate form with a timeout in seconds. The syntax of
  this macro is (with-timeout <i>duration</i> <i>body</i>
  <i>timeout-form</i>). 
  A duration of 0 seconds disables the timeout mechanism, 
  i.e its a no-op. Otherwise, if <i>duration</i> seconds elapse
  during evaluation of <i>body</i> then the evaluation is
  aborted and the value of <tt>timeout-form</tt> is returned,
  otherwise returns the value of <tt>body</tt>. The signature of 
  <tt>body</tt> and <tt>timeout-form</tt> should be the same.
  
  
  Advanced Notes:
  This form should be called either at the top-level or in an environment
  where state is available and <tt>body</tt> has no free variables
  other than state.
  If the timeout-form is a long running computation, 
  then the purpose of with-timeout is defeated.

  <code>
  Usage:
  (with-timeout 5 (fibonacci 40) :timeout)
   :doc with-timeout
  </code>"
  )

(defttag :acl2s-timeout)


(defun timeout-hard-error (ctx str alist state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (er-progn
   (assign acl2::timeout-error-occurred t)
   (mv t (hard-error ctx str alist) state)))
   

(progn!
 (set-raw-mode t)
 (load (concatenate 'string (cbd) "with-timeout-raw.lsp")))


(defmacro-last with-timeout-aux)

;adapted from the macro top-level in other-events.lisp
;TODO:  I do not believe this is not a general solution --Ask Matt!
;A general solution might have to use trans-eval or ld explicitly
;inside the function body, which sounds ugly
(defmacro timed-eval-of-event (duration form timeout-form
                                        submit-eventp debug)
  "evaluate event form as a function body, so that with-timeout-aux doesnt
   complain, but also do a macroexpand1 so that forms like
  defun,defthm wont complain. Form should have no free 
  variables (other than state), i.e it should be a top-level form"
  `(with-output
    :stack :push
    :off :all
    ;:on error
    (make-event
     (acl2::state-global-let*
      ((acl2::inhibit-output-lst 
        (and (not ,debug)
             acl2::*valid-output-names*)))
   
        (mv-let 
      (erp tform state)
      (trans1-fn ',form state);do macroexpand1
      (if erp
          (er soft 'with-timeout-ev "~|Error in with-timeout-ev: To see, run ~x0~%"
              '(trans1-fn ',form state))
        (er-progn 
         (ld `((defun top-level-fn (state)
                 (declare (xargs :mode :program :stobjs state)
                          (ignorable state))
                 (with-timeout1 ,',duration ,tform ,',timeout-form))
              ; (acl2s-defaults :set verbosity-level 0);turn off testing output
;output here wjhen checking timeout
               (with-output
                :stack :pop
                (top-level-fn state)))
;Note: Suppose form is a defthm/defun, then obviously it will
;never be registered in the world as an event. And so we have an
;extra argument which specifies if the form you passed is to be submitted 
             :ld-pre-eval-print nil
             :ld-post-eval-print nil
             :ld-error-action :error
             :ld-verbose nil
             :ld-prompt nil)
;if everything went well, then obviously the form didnt timeout and
;didnt error out, i.e was successful, either QED or termination, and so
;we presume that a call without a timeout wrapper should be successful 
;and we try it. This is a common scenario in defunc. But probably this
;is not a clean way to do things
         (value (if ,submit-eventp 
                    `(with-output :stack :pop
                                  ,',form) 
                  '(value-triple :invisible))))))))))

(defmacro with-timeout-ev (duration event-form timeout-form 
                                    &key submit-eventp debug
                                    )
  `(if (zp ,duration) ;if 0 or not a int then timeout is disabled
      ,event-form
     (timed-eval-of-event ,duration ,event-form 
                          ,timeout-form
                          ,submit-eventp ,debug)))


(defmacro with-timeout (duration form timeout-form)
"can only be called at top-level, that too only forms that are allowed
to be evaluated inside a function body. To eval defthm, use
with-timeout-ev instead"
`(if (zp ,duration) ;if 0 or not a int then timeout is disabled
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
`(if (zp ,duration) ;if 0 or not a int then timeout is disabled
    ,form
  (with-timeout-aux '(,duration ,timeout-form) ,form)))

(defttag nil) ; optional (books end with this implicitly)


