(in-package "ACL2S-INTERFACE")

(acl2::include-book "xdoc/top" :dir :system)

(xdoc::defxdoc acl2s-interface
  :parents (acl2::interfacing-tools acl2::acl2-sedan)
  :short "An interface for interacting with ACL2/ACL2s from Common Lisp."
  :long " <p>WARNING: Loading this book by default will result in the
redefinition of @('comment-window-co'). This is unfortunately the only
way we found to control comment-window printing. If you would like to
disable this feature, you can add the
@('ACL2S-INTERFACE-NO-OVERWRITE') feature, e.g. by running @('(push
:ACL2S-INTERFACE-NO-OVERWRITE *features*)') in raw mode before
certifying this book.</p>")

(xdoc::defxdoc quiet-mode
  :parents (acl2s-interface)
  :short "Control whether or not the acl2s-interface attempts to suppress ACL2 printed output"
  :long "
Examples:
@({
 (quiet-mode-on)    ; from this point forward all acl2s-interface functions will
                    ; attempt to suppress all ACL2 printed output
 (quiet-mode-off)   ; (default) from this point forward all acl2s-interface
                    ; functions will print any ACL2 output as normal
})
<p>
Most of the ACL2s interface functions also take a @(':quiet') argument for
locally controlling quiet mode without affecting the global setting.
</p>

<p>
The ACL2s interface provides hooks for code that should run when quiet mode
is enabled or disabled. See @(see quiet-mode-hooks) for more information.
</p>
")

(xdoc::defxdoc quiet-mode-hooks
  :parents (acl2s-interface)
  :short "Hooks that fire when the ACL2s interface quiet mode is turned on or off."
  :long "
<b>General form</b>
@({
 (add-quiet-mode-on-hook
   name  ; A (symbol) name to associate with this hook
   hook) ; A function to call when quiet mode transitions from disabled to enabled.
         ; The return value of the hook function should be a list of ACL2 forms to
         ; be executed.

 (add-quiet-mode-off-hook
   name  ; A (symbol) name to associate with this hook
   hook) ; A function to call when quiet mode transitions from enabled to disabled.
         ; The return value of the hook function should be a list of ACL2 forms to
         ; be executed.
})
<p>
Some applications may have verbosity settings beyond the standard ACL2 ones. Quiet
mode hooks provide a way to change these settings whenever the ACL2s interface
transitions from quiet mode being enabled to disabled, and vice versa.
</p>

<p>
Upon the appropriate transition, each hook function for that transition is called.
The return values of all of the hook functions for that transition type are
appended, and the resulting list of ACL2 forms is evaluated using @(see acl2::ld)
in an environment that disables all output. Typically, hooks will perform some
stateful operation (for example, a quiet-mode-on hook might save the current value
of a setting into a variable) and then produce a list of ACL2 forms that will change
the setting to its original value (for a quiet-mode-off hook) or to a particular
quiet value (for a quiet-mode-on hook). One should <b>not</b> call any of
@('acl2s-compute'), @('acl2s-query'), or @('acl2s-event') from inside of a hook.
</p>

<p>
For each transition type, adding a hook with the same name as another hook for that
same transition type will result in the previously added hook being removed from
the list of hooks.
</p>

<b>Examples</b>
@({
  ;; Define a variable to store the last seen gag mode.
  ;; See books/acl2s/interface/acl2s-interface.lsp for the definition
  ;; of define-var, which is needed to work around SBCL and CCL quirks.
  (define-var *saved-gag-mode* (acl2::gag-mode))

  (add-quiet-mode-on-hook
    :gag-mode
    (lambda ()
      ;; Calling acl2::@ here is probably not super safe, but it seems to work...
      (setf *saved-gag-mode* (acl2::@ acl2::gag-mode))
      '((acl2::set-gag-mode t))))

  (add-quiet-mode-off-hook
    :gag-mode
    (lambda () `((acl2::set-gag-mode ,*saved-gag-mode*))))
})

<p>
See @('books/acl2s/interface/acl2s-utils/additions.lsp') for some example hooks.
</p>
")

(xdoc::defxdoc capture-output
  :parents (acl2s-interface)
  :short "Control whether or not the acl2s-interface attempts to capture ACL2 printed output"
  :long "
Examples:
@({
 (capture-output-on)    ; From this point forward all acl2s-interface functions will
                        ; attempt to capture all ACL2 printed output
 (capture-output-off)   ; (default) From this point forward all acl2s-interface
                        ; functions will print any ACL2 output as normal
 (get-captured-output)  ; Returns a string containing all captured output since the
                        ; last (get-captured-output) call. Note that the three primary
                        ; acl2s-interface functions will call this before each query.
})
<p>
Most of the ACL2s interface functions also take a @(':capture-output') argument for
locally controlling whether output is captured without affecting the global setting.
</p>
")

(xdoc::defxdoc acl2s-interface-symbol-package-tips
  :parents (acl2s-interface)
  :short "Tips for dealing with symbol package issues when using the ACL2s interface"
  :long "
<p>When using any of the ACL2s interface functions from inside of a package other than \"ACL2\", you may run into problems because the symbols inside of any query literals will default to being interned in that package. This is mainly problematic when it comes to writing expressions that call ACL2 functions.
</p>
<p>
The simplest way to solve this problem while still working in a non-ACL2 package is to fully specify the names of all functions inside your queries. For example, one would write <tt>(acl2s-compute '(acl2::expt 2 3))</tt> instead of <tt>(acl2s-compute '(expt 2 3))</tt>.
</p>
<p>
This gets painful when writing queries containing many function calls. In this case, depending on your host Lisp, you may be able to use <a href=\"http://www.sbcl.org/manual/#Extended-Package-Prefix-Syntax\">extended package prefix notation</a>. For example, in SBCL, one could write <tt>(acl2s-compute 'acl2::(expt 2 (expt 2 3)))</tt> instead of <tt>(acl2s-compute '(acl2::expt 2 (acl2::expt 2 3)))</tt>.
</p>

<p>
Note that using extended package prefix notation with a backquoted value will also affect any evaluated subexpressions. The following example shows one way of getting around this, by providing the full name of the argument @('foo::x').</p>
@({
(in-package :foo) ;; assume we've defined a package named foo in Common Lisp
(defun baz-ok-1 (x)
  (acl2s-compute `(acl2::expt 2 (acl2::expt 2 ,x))))
(defun baz-bad (x)
  (acl2s-compute `acl2::(expt 2 (expt 2 ,x)))) ;; ,x here will evaluate acl2::x instead of foo::x.
(defun baz-ok-2 (x)
  (acl2s-compute `acl2::(expt 2 (expt 2 ,foo::x)))) ;; we can just override the default package to fix this
})
")


(xdoc::defxdoc acl2s-compute
  :parents (acl2s-interface)
  :short "Run a single-value ACL2 computation from Common Lisp"
  :long "
<b>General form</b>
@({
(acl2s-compute
  form                   ; The form to evaluate. Should return a single value.
  :quiet <bool>          ; Optional. Whether or not to suppress all ACL2 printed output. Defaults to nil.
  :capture-output <bool> ; Optional. Whether or not to capture all ACL2 printed output. Defaults to nil.
  ...)       ;; Any additional arguments will be passed to ld, except for :ld-error-action
=>
(list erp val)
})
<dl>
<dt>Returns</dt>
<dd>@('erp') is @('t') if an error occurred during execution of @('form'), and is @('nil') otherwise.</dd>
<dd>@('val') is the single value that @('form') evaluated to.</dd>
</dl>

<p>
The @('form') argument should be an ACL2 expression that evaluates to a single value. Be careful about symbol packages when using @('acl2s-compute') when inside a different package - you may need to fully specify the name of an ACL2 function when calling it. See @(see acl2s-interface-symbol-package-tips) for more information.
</p>

<p>
When the @(':quiet') option is set to @('t'), @('acl2s-compute') will attempt to suppress all ACL2 printed output during evaluation of @('form'). This temporarily overrides the current @(see quiet-mode).
</p>

<p>
When the @(':capture-output') option is set to @('t'), @('acl2s-compute') will attempt capture all ACL2 printed output during evaluation of @('form'). This temporarily overrides the current @(see capture-output).
</p>

<h4>Examples</h4>

@({(acl2s-compute '(+ 1 2))})
Returns (nil 3)
@({(acl2s-compute '(+ 1 2) :quiet nil :ld-pre-eval-print t)})
Returns (nil 3), does not attempt to suppress any ACL2 printed output, and passes @(':ld-pre-eval-print t') to @(see acl2::ld)
@({(acl2s-compute '(append '(1 2) '(3 4)))})
Returns (nil (1 2 3 4))
@({(acl2s-compute '(+ 1 '(1 2)))})
Returns (t nil) and prints out a guard violation error message
@({(acl2s-compute '(mv nil t state))})
")


(xdoc::defxdoc acl2s-query
  :parents (acl2s-interface)
  :short "Run a multiple-value ACL2 computation from Common Lisp"
  :long "
<b>General form</b>
@({
(acl2s-query
  form                         ; The form to evaluate. Should evaluate to an error triple.
  :quiet <bool>                ; Optional. Whether or not to suppress all ACL2 printed output. Defaults to nil.
  :capture-output <bool>       ; Optional. Whether or not to capture all ACL2 printed output. Defaults to nil.
  :prover-step-limit <integer> ; Optional. Sets the prover step limit. Defaults to what ACL2 would have used
                               ;           for a top-level evaluation (see set-prover-step-limit).
  ...)                         ; Any additional arguments will be passed to ld, except for :ld-error-action
=>
(list erp val)
})
<dl>
<dt>Returns</dt>
<dd>@('erp') is the first value of the error triple that @('form') evaluated to, or @('nil') if an error occurred while evaluating @('form').</dd>
<dd>@('val') is the second value of the error triple that @('form') evaluated to.</dd>
</dl>

<p>
The @('form') argument should be an ACL2 expression that evaluates to an @(see acl2::error-triple). @('form') should also not change the state of the ACL2 world with respect to events. Be careful about symbol packages when using @('acl2s-query') when inside a different package - you may need to fully specify the name of an ACL2 function when calling it. See @(see acl2s-interface-symbol-package-tips) for more information.
</p>

<p>
When the @(':quiet') option is set to @('t'), @('acl2s-query') will attempt to suppress all ACL2 printed output during evaluation of @('form'). This temporarily overrides the current @(see quiet-mode).
</p>

<p>
When the @(':capture-output') option is set to @('t'), @('acl2s-query') will attempt capture all ACL2 printed output during evaluation of @('form'). This temporarily overrides the current @(see capture-output).
</p>

<p>
@('acl2s-query') evaluates @('form') inside of a @(see acl2::with-prover-step-limit), where the step-limit is set to the value provided to @(':prover-step-limit'), or ACL2's set prover-step-limit if that option is not provided. See @(see acl2::set-prover-step-limit) for more information about the prover step-limit. If you don't want to limit the number of prover steps permitted for an event, set @(':prover-step-limit') to nil.
</p>

<h4>Examples</h4>
@({(acl2s-query '(value (+ 1 2)))})
Returns (nil 3)

@({(acl2s-query '(thm (implies (natp x) (integerp x))))})
Returns (nil :invisible)

@({(acl2s-query '(mv nil t state))})
Returns (nil t)

@({(acl2s-query '(value (+ 1 2)) :quiet nil :ld-pre-eval-print t)})
Returns (nil 3), does not attempt to suppress any ACL2 printed output, and passes @(':ld-pre-eval-print t') to @(see acl2::ld)

@({(acl2s-query '(trans-eval '(+ 1 2) 'my-ctx state nil))})
Returns (nil ((nil) . 3)). See @(see acl2::trans-eval) for more information
about trans-eval's return value.

@({(acl2s-query '(test? (implies (integerp x) (natp x))))})
Returns (t nil)
")


(xdoc::defxdoc acl2s-event
  :parents (acl2s-interface)
  :short "Install an ACL2 event from Common Lisp"
  :long "
<b>General form</b>
@({
(acl2s-event
  form                         ; The form to evaluate. Should return an error triple.
  :quiet <bool>                ; Optional. Whether or not to suppress all ACL2 printed output. Defaults to nil.
  :capture-output <bool>       ; Optional. Whether or not to capture all ACL2 printed output. Defaults to nil.
  :prover-step-limit           ; Optional. Sets the prover step limit. Defaults to what ACL2 would have used
                               ;           for a top-level evaluation (see acl2::set-prover-step-limit).
  ...)                         ; Any additional arguments will be passed to ld, except for :ld-error-action.
=>
(list erp nil)
})
<dl>
<dt>Returns</dt>
<dd>@('erp') is `nil` if ld indicates that the form was successfully evaluated.</dd>
</dl>

<p>
The @('form') argument should be an ACL2 expression that evaluates to an @(see acl2::error-triple). Be careful about symbol packages when using @('acl2s-event') when inside a different package - you may need to fully specify the name of an ACL2 function when calling it. See @(see acl2s-interface-symbol-package-tips) for more information.
</p>

<p>
When the @(':quiet') option is set to @('t'), @('acl2s-event') will attempt to suppress all ACL2 printed output during evaluation of @('form'). This temporarily overrides the current @(see quiet-mode).
</p>

<p>
When the @(':capture-output') option is set to @('t'), @('acl2s-event') will attempt capture all ACL2 printed output during evaluation of @('form'). This temporarily overrides the current @(see capture-output).
</p>

<p>
@('acl2s-event') evaluates @('form') inside of a @(see acl2::with-prover-step-limit), where the step-limit is set to the value provided to @(':prover-step-limit'), or ACL2's set prover-step-limit if that option is not provided. See @(see acl2::set-prover-step-limit) for more information about the prover step-limit. If you don't want to limit the number of prover steps permitted for an event, set @(':prover-step-limit') to nil.
</p>

<h4>Examples</h4>
@({(acl2s-event '(definec f (x :int) :int (* x x)))})
Returns (nil nil), and defines the function @('f') in the ACL2 world.

@({(acl2s-event '(definec g (x :int) :int (* 5 x)) :quiet t)})
Returns (nil nil), and defines the function @('g') in the ACL2 world. Tries to suppresses all ACL2 printed output during this process.

@({(acl2s-event '(defthm triangle-inequality
                              (implies (and (natp x) (natp y))
                                       (>= (+ (abs x) (abs y)) (abs (+ x y)))))
              :prover-step-limit 200)})
Returns (t nil), indicating that the @('defthm') did not successfully execute. This is because the @('defthm') was limited to 200 prover steps, and more prover steps than that are required to prove it.

@({(acl2s-event '(defthm triangle-inequality
                              (implies (and (natp x) (natp y))
                                       (>= (+ (abs x) (abs y)) (abs (+ x y)))))
              :prover-step-limit 1000)})
Returns (nil nil), and defines the theorem @('triangle-inequality') in the ACL2 world. It limits the @('defthm') call to 1000 prover steps.
")

(xdoc::defxdoc acl2s-interface-utils
  :parents (acl2s-interface)
  :pkg "ACL2S-INTERFACE-EXTRAS"
  :short "Some utilities built into the ACL2s interface."
  :long "
<ul>
<li>@('(flatten-and l)'): Given a list of terms representing the conjunction of those terms, recursively flatten any conjunctions inside those terms.</li>
<li>@('(conjunction-terms x y)'): Given two terms, produce the conjunction of them, simplifying if either of the terms has a top-level conjunction.</li>
<li>@('(cnf-disjunct-to-or expr)'): Given a CNF disjunct, convert to an equivalent ACL2s expression by adding 'or.</li>
<li>@('(get-hyps expr)'): Get the hypotheses of an implication, returning nil if the given expression is not an implication.</li>
<li>@('(get-conc expr)'): Get the conclusion of an implication, returning nil if the given expression is not an implication.</li>
</ul>
")
