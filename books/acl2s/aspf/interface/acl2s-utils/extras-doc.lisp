(in-package "ACL2S-INTERFACE")

;; TODO: double-check note about 'acl2::?
(xdoc::defxdoc itest?-query
  :parents (acl2s-interface)
  :pkg "ACL2S-INTERFACE-EXTRAS"
  :short "Find counterexamples to an ACL2s statement."
  :long "
<b>General form</b>
@({
(itest?-query
  stmt                     ;; The statement to find counterexamples to.
  :num-counterexamples ... ;; Optional. If non-nil, the number of counterexamples to request from itest?.
  :quiet ...               ;; Optional. Whether or not to suppress all ACL2 printed output. Defaults to t.
  :prover-step-limit ...   ;; Optional. Sets the prover step limit. See @(see acl2s-query) for more information
                           ;;           about the default value.
)
=>
(list cts-found? itest?-res)
})
<dl>
<dt>Returns</dt>
<dd>@('cts-found?') is @('nil') if no counterexamples were found, or @('t') otherwise.</dd>
<dd>@('itest?-res') is a list list of the form @('(status cts wts)'), where
@('status') is either @('nil'), @(':falsifiable') or @(':?') and @('cts') and @('wts') are
assignments, with @('cts') corresponding to counterexamples and @('wts') to
witnesses returned by @('itest?'). If @('cts-found?') is @('nil') (no counterexamples) and @('itest?') proved
 the conjecture, then @('itest?-res') is of the form @('(nil nil
wts)'). If @('status') is @(':falsifiable') then @('cts') is a
non-empty list. If @('status') is @(':?') then @('cts') is @('nil'),
and the conjecture was not proved.
 </dd>
</dl>

<p>
The @('stmt') argument should be an ACL2 expression. Be careful about symbol packages when using @('itest?-query') when inside a different package - you may need to fully specify the name of an ACL2 function when calling it. See @(see acl2s-interface::acl2s-interface-symbol-package-tips) for more information.
</p>

<p>
When the @(':quiet') option is set to @('t'), @('itest?-query') will attempt to suppress all ACL2 printed output while itest? is running. This temporarily overrides the current @(see acl2s-interface::quiet-mode).
</p>

<p>
@('itest?-query') evaluates itest? inside of a @(see acl2::with-prover-step-limit), where the step-limit is set to the value provided to @(':prover-step-limit'), or ACL2's set prover-step-limit if that option is not provided. See @(see acl2::set-prover-step-limit) for more information about the prover step-limit. If you don't want to limit the number of prover steps permitted for itest?, set @(':prover-step-limit') to nil.
</p>

<p>
@(':num-counterexamples') allows one to request more counterexamples
from @('itest?') than @('acl2s-defaults') specifies. Note that
@('itest?') will not always produce the number of counterexamples
requested. You may get more or less counterexamples. See @('test?')
for a discussion of stopping conditions.
</p>

<p>
In some cases, @('itest?') may produce counterexamples where some variables are assigned the value 'acl2::?. This indicates that @('itest?') did not need to bind a value to those variables for the statement to evaluate to nil, given the other variable assignments.
</p>

<p>
See @(see acl2::test?) for more information about ACL2s' counterexample generation facilities. @('itest?') is essentially a slightly modified version of @('test?') that provides more information programmatically.
</p>

<h4>Examples</h4>
@({(itest?-query '(implies (integerp x) (natp x)))})
Returns @('(T
 (:FALSIFIABLE
  (((X -371)) ((X -1)) ((X -945)) ((X -297)) ((X -850)) ((X -487)) ((X -201))
   ((X -18)) ((X -817)))
  NIL))') (note that values for x may be different)

@({(itest?-query '(implies (natp x) (integerp x)))})
Returns @('(NIL (NIL NIL (((X 161)) ((X 5)) ((X 169)) ((X 8)) ((X 9)) ((X 417)))))')

@({(itest?-query '(implies (true-listp x) (< (length x) 50)))})
Returns @('(NIL
 (:? NIL
  (((X '(0 0))) ((X '(ACL2S::ABA))) ((X '(ACL2S::A ACL2S::A))) ((X '(0)))
   ((X NIL)) ((X '(NIL NIL NIL NIL NIL))) ((X '(-1 (0 . T))))
   ((X '((NIL . T) (((T) T) (NIL) T)))))))'). This is an example of a case where counterexamples exist (i.e. a list of 50 0's) but @('itest?') cannot find any.

@({(itest?-query '(implies (and (natp x) (natp y) (natp z) (> x 0) (> y 0) (< z 100)) (/= z (+ (* x x) (* y y)))))})
Returns @('(T
 (:FALSIFIABLE
  (((Z 85) (Y 2) (X 9)) ((Z 41) (Y 4) (X 5)) ((Z 37) (Y 6) (X 1))
   ((Z 53) (Y 7) (X 2)) ((Z 37) (Y 1) (X 6)) ((Z 29) (Y 5) (X 2)))
  (((Z 76249) (Y 260) (X 93)) ((Z 254137) (Y 484) (X 141))
   ((Z 13130) (Y 83) (X 79)))))').
")
