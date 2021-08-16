#|$ACL2s-Preamble$;
;;Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#




;; EXAMPLES:
;; See testing-regression.lsp

;; USAGE:
;; (include-book "acl2s/cgen/top" :dir :system :ttags :all)
;; (acl2s-defaults :set testing-enabled t) ;default is :naive


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


;; Note: The use of ttags is primarily for engineering
;; purposes. Usually you would include this book while
;; developing/designing proofs and when you have all QEDs,
;; simply remove this book.


(in-package "ACL2S")

(include-book "acl2s-parameter")
(include-book "prove-cgen" :ttags :all)
(include-book "acl2s/defdata/top" :dir :system :ttags :all)


(defun defdata-testing-enabled-ev (D kwd-alist wrld)
  (declare (ignore D wrld))
  `((local (acl2s-defaults :set testing-enabled
                           ,(defdata::get1 :testing-enabled kwd-alist)))))

; Add the above form at the beginning of defdata events
(table defdata-defaults-table
       :pre-pred-hook-fns
       (cons 'defdata-testing-enabled-ev
             (defdata::get1 :pre-pred-hook-fns (table-alist 'defdata-defaults-table world))))


;reset cgen globals and other state defaults
(make-event
 (er-progn
  (assign cgen::event-ctx nil)
  (assign cgen::cgen-state nil)
  (assign acl2::evalable-printing-abstractions nil)
  (value '(value-triple :invisible)))
 :check-expansion t)

(defttag t)
(defattach (acl2::initialize-event-user cgen::initialize-event-user-cgen-gv) :skip-checks t :system-ok t)
(defattach (acl2::finalize-event-user cgen::finalize-event-user-cgen-gv) :skip-checks t :system-ok t)
(defattach (cgen::print-testing-summary cgen::print-testing-summary-fn) :skip-checks t)
(defttag nil)


; For now lets keep the nats not more than 1000 to avoid stack-overflow
; on non-tail-recursive functions. If you dont like these, comment
; them out, or write your own custom test enumerators and attach them
(defdata-attach pos :test-enumerator nth-pos-testing)

(defdata-attach integer :test-enumerator nth-integer-testing)
(defdata-attach nat :test-enumerator nth-nat-testing)
(defdata-attach neg :test-enumerator nth-neg-testing)


;Note on xdoc: <= or < cannot be used inside defxdoc!!

(defun test?-fn (form hints override-defaults state)
; Jan 9th 2013, dont print summary unless there was a counterexample.
  (declare (xargs :mode :program
                  :stobjs (state)))
;        :sig ((any hints keyword-value-listp state) -> (mv erp any state))
  (b* ((ctx 'test?)

       (cgen::cgen-state (cgen::make-cgen-state-fn form (cons :USER-DEFINED ctx)
                                                   override-defaults (w state)))
;       (?defaults (cget params))
       ;(testing-enabled (cget testing-enabled))
       (vl              (cgen::cget verbosity-level))
       (pts?            (cgen::cget print-cgen-summary))

       (timeout (cgen::cget cgen-timeout))

       (hints (append '() ;acl2::*bash-skip-forcing-round-hints*
                      (acl2::add-string-val-pair-to-string-val-alist
                       "Goal" :do-not (list 'quote '(acl2::generalize acl2::fertilize))
                       (acl2::add-string-val-pair-to-string-val-alist
                        "Goal" :do-not-induct T hints))))

       ((mv res cgen::cgen-state state)
        (with-time-limit timeout
                         (prove/cgen form hints cgen::cgen-state state)))

       ((er &) (cond ((not (cgen::cgen-state-p cgen::cgen-state)) (value nil))
                     ((and (<= (acl2::access cgen::gcs% (cgen::cget gcs) :cts) 0)
                           (not pts?))
;no point in printing a summary if we specifically ask not to if no cts was found.
                      (value nil))
                     (t (cgen::print-testing-summary cgen::cgen-state ctx state))))


       ((mv cts-found? state)
        (cond ((eq res :falsifiable) (prog2$
                                      (cgen::cw? (cgen::normal-output-flag vl)
                                           "~%Test? found a counterexample.~%")
                                      (mv T state)))
              ((eq res t) (prog2$
                           (cgen::cw? (and pts? (cgen::normal-output-flag vl))
                                "~|Test? failed (probably due to a hard error).~%")
                           (mv nil state)))
;Success means the prover actually proved the conjecture under consideration
              ((eq res nil) (prog2$
                             (cgen::cw? (and pts? (cgen::normal-output-flag vl))
                                  "~%Test? proved the conjecture under consideration~s0. ~
 Therefore, no counterexamples exist. ~%" (if hints "" " (without induction)"))
                             (mv NIL state)))
; either prove failed, or we didnt call prove. Either way if we didnt find a cts
; then we say the test? succeeded! But dont print if print-cgen-summary is nil.
              (t (prog2$
                  (cgen::cw? (and pts? (cgen::normal-output-flag vl))
                       "~%Test? succeeded. No counterexamples were found.~%")
                  (mv NIL state)))))

       )

    (mv cts-found? '(value-triple :invisible) state )))

(defmacro test? (form &rest kwd-val-lst)
  (let* ((vl-entry (assoc-keyword :verbosity-level kwd-val-lst))
         (vl (and vl-entry (cadr vl-entry)))
         (debug (and (natp vl) (cgen::debug-flag vl)))
         (hints-entry (assoc-keyword :hints kwd-val-lst))
         (hints (and hints-entry (cadr hints-entry))))
    `(with-output
      :stack :push
      ,(if debug :on :off) :all
      ,@(if debug nil (list :on 'comment))
      :gag-mode ,(not debug)
     (make-event
      (test?-fn ',form ',hints ',kwd-val-lst state)))))



(defxdoc acl2::cgen
  :parents (acl2::debugging acl2::acl2-sedan acl2::testing-utilities)
  :short "Counterexample Generation a.k.a Disproving for ACL2"
  :long
"
<h3>Using Cgen</h3>
<p>
Cgen is available and enabled in all ACL2 Sedan session modes except <i>Compatible</i>.
If it is not already available, you can use Cgen simply be submitting the following
commands:
@({
  (include-book \"acl2s/cgen/top\" :dir :system :ttags :all)
  (acl2s-defaults :set testing-enabled t)
})
</p>

<h3>Introduction</h3>

<p> Cgen is a powerful debugging facility that can be used to test/check
formulas for counterexamples automatically. It is implemented as a set of
books, tightly coupled with the @(see defdata) framework. Thus for the most
profitable use of Cgen, one should specify all type-like monadic predicates
using @('defdata') or at least register such predicates as defdata types using
@('register-type').  When Cgen is in effect via the @('testing-enabled')
parameter, every checkpoint subgoal arising in event contexts such as @('thm'),
@('defthm') and @('verify-guards') is checked (searched) for
counterexamples. So although you can integrate Cgen seamlessly in your
interactive proof workflow, we recommend the use of the specially designed
macro, <i>test?</i>.  </p>

<h3>To prove use <tt>thm</tt>, to disprove use <tt>test?</tt></h3>

<p> One can use @('test?') as a drop-in replacement for @('thm')
to disprove conjectures.  @('test?') guarantees that
counterexamples are printed in terms of the top goal's
variables. See @(see test?) for more details and examples.</p>

<h3>More Powerful Theorem Proving</h3>

<p>
Cgen also defeats false generalizations. We have seen many
examples where defthms succeed with @('testing-enabled') because
Cgen falsified a bad generalization, thereby causing ACL2 to
@('backtrack') and modify its proof search path.
</p>

<h4>Example</h4>
<p>Examine the proof output to see the backtracking.</p>
@({
  (acl2s-defaults :set testing-enabled t) ;try first with nil
  (defthm no-duplicates-remove
    (implies (and (true-listp list)
                  (no-duplicatesp list))
             (no-duplicatesp (remove x list))))
})


<h3>Control Parameters</h3>

<p> The Cgen library can be configured via a collection of parameters using the
  @('acl2s-defaults') macro using the <tt>:get</tt> or <tt>:set</tt> keyword
  arguments. In particular, see @('num-trials'), @('verbosity-level'),
  @('testing-enabled'). All the control parameters are package-agnostic.  </p>

<h3> Advanced Notes </h3>


<p>The API functions/macros for Cgen library reside in the ACL2S package. Use
list (<tt>*acl2s-exports*</tt>) to import these symbols into your own
package.</p>

<h3>More details</h3>

<p> To understand more about how testing works, please refer to the following
<a href=\"http://arxiv.org/abs/1105.4394v2\">paper</a> </p>
"
 )

#!ACL2
(defpointer counter-example-generation cgen)

(defxdoc cgen::flush
  :parents (acl2::cgen)
  :short "Flush/Reset the Cgen state globals to sane values."
  :long " [DEPRECATED, IRRELEVANT]
  Flush the transient Cgen state globals (<tt>cgen::event-ctx</tt>, <tt>cgen::cgen-state</tt>) to <tt>nil</tt>.
  <code>
   Usage (at the top-level):
     (cgen::flush)
  </code>
"
)


(defxdoc test?
  :parents (acl2::cgen)
  :short "Test/Check a conjecture for counterexamples."
  :long
"
<h3>Examples</h3>
@({
  (acl2s::test? (equal (reverse (reverse x)) x))

  (test? (implies (and (posp (car x))
                       (posp (cdr x)))
                  (= (cdr x) (len x))))


  (defun perm (x y)
    (if (endp x)
      (endp y)
      (and (member (car x) y)
           (perm (cdr x) (remove1 (car x) y)))))

  (test?
    (implies (and (consp X)
                  (member a Y))
             (equal (perm (remove a X)
                          (remove a Y))
                    (perm X Y))))
})

Note: test? is in ACL2S package.

<h4>Usage:</h4>
@({
   (test? form
          [:hints hints]
          [acl2s-defaults keyword options]
   )
})

<h3>Introduction</h3>

<p> @('test?') is a powerful counterexample generation facility,
based on random testing, that is intended to be used to increase
confidence in the truth of a conjecture by providing extensive
testing.</p>

<p> @('test?') combines random testing with the power of ACL2 via our data
definition framework (@(see defdata)). It guarantees that any counterexamples
generated are truly counterexamples to the original conjecture. A
counterexample is just a binding that maps the variables in the original
conjecture to values in the ACL2 universe. In cases where the value of
variables are irrelevant, we bind the variables to the symbol @('?') : these
bindings still provide counterexamples, but should raise alarms, since chances
are that there is a specification error. </p>

<p> If no counterexample is found, there are three possibilities. First, it is
possible that the conjecture is false, in which case increasing the amount of
testing we do may lead to the discovery of a counterexample.  Second, it is
also possible that ACL2 proves that the conjecture is true, in which case we
print a message reporting success.  Finally, the conjecture may be true, but
ACL2 cannot prove it.  For all of these three cases, we consider testing to
have succeeded, so @('test?') will report success. </p>

<p>@('test?') is an embedded event and can be used in ACL2 @(see acl2::books). But it
is recommended to use them only in the design and in the debug phase, since its
use requires trust-tags.</p>

<h3> Control Parameters </h3>

<p> We can furthur control the behavior of test? using keyword options or
@('acl2s-defaults'). All the parameters in @('acl2s-defaults') are available as
keyword options to the @('test?') macro and they override the current defaults.
The most important parameters to tweak are
@(see num-trials), @(see verbosity-level), @(see testing-enabled).</p>

<h3>More Examples</h3>
@({
  (defdata small-pos (enum '(1 2 3 4 5 6 7 8 9)))
  (test?
    (implies (and (integerp c1)
                  (integerp c2)
                  (integerp c3)
                  (small-posp x1)
                  (small-posp x2)
                  (small-posp x3)
                  (< x1 x2)
                  (< x2 x3)
                  (equal 0 (+ c1 c2 c3))
                  (equal 0 (+ (* c1 x1) (* c2 x2) (* c3 x3))))
             (and (= 0 c1) (= 0 c2) (= 0 c3))))


  (defun square-root1 (i ri)
    (declare (xargs :mode :program))
    (if (>= (floor i ri) ri)
        ri
        (square-root1 i (floor (+ ri (floor i ri)) 2))))

  (defun square-root (i)
    (declare (xargs :mode :program))
    (square-root1 i (floor i 2)))

  (defun square (x)
     (* x x))


  (test?
    (implies (natp i)
             (and (<= (square (square-root i)) i)
                  (< i (square (1+ (square-root i)))))))




  (defdata triple (list pos pos pos))

  (defun trianglep (v)
    (and (triplep v)
         (< (third v) (+ (first v) (second v)))
         (< (first v) (+ (second v) (third v)))
         (< (second v) (+ (first v) (third v)))))

  (defun shape (v)
    (if (trianglep v)
        (cond ((equal (first v) (second v))
               (if (equal (second v) (third v))
                   \"equilateral\"
                 \"isosceles\"))
              ((equal (second v) (third v)) \"isosceles\")
              ((equal (first v) (third v)) \"isosceles\")
              (t \"scalene\"))
      \"error\"))

  (acl2s-defaults :set num-trials 1000000)
  (acl2s-defaults :set testing-enabled :naive)

  (test?
   (implies (and (triplep x)
                 (trianglep x)
                 (> (third x) 256)
                 (= (third x)
                    (* (second x) (first x))))
            (not (equal \"isosceles\" (shape x)))))

  (acl2s-defaults :set num-trials 1000)

  (acl2s-defaults :set testing-enabled t)


  (include-book \"arithmetic/top-with-meta\" :dir :system)

  (test?
   (implies (and (triplep x)
                 (trianglep x)
                 (> (third x) 256)
                 (= (third x)
                    (* (second x) (first x))))
            (not (equal \"isosceles\" (shape x)))))

})


<h3> Advanced Notes </h3>

<p> We note that in order to be able to generate counterexamples, we do not
allow ACL2 to use any of the following processes: induction, generalization,
and cross-fertilization. We do allow destructor-elimination, though in rare
cases, user defined elim rules may generalize the conjecture. Such situations
are recognized.  If you want to enable the above processes, use @('thm')
instead, but note that counterexamples shown might not be of the top-level
conjecture.  </p>


"
)


(defxdoc prove/cgen
  :parents (acl2::cgen)
  :short "top-level API function for Cgen/testing."
  :long
"<h3>Introduction</h3>

<p> This is the main API function to test/check a form for counterexamples with
the full power of prove (and hints), i.e. @('prove/cgen') actually calls
@('prove') as a subfunction. You can accomplish the same thing using @('thm,
defthm') with the acl2s defaults parameter @('testing-enabled') set to @('T'),
but this function gives the user/caller more control: the user is responsible
to pass @('cgen-state') (use @('make-cgen-state') to construct one), that
provides the <i>context</i> for cgen/testing; the results and statistics
summarizing Cgen/testing are collected in cgen-state and this is returned to
the caller. </p>

<h3>General Form:</h3>
@({(prove/cgen form hints cgen-state state) => (mv erp cgen-state state)})

<p> The @('erp') part of result is @('nil'), if call to @('prove') was
successful, it is @(':falsifiable') if there is at least one
counterexample (not necessarily top-level), it is @('t') if there was a error
in trans-eval call of prove (usually a hard/raw lisp error), it is @(':?')
otherwise, which points out that we could neither prove nor disprove the
conjecture under consideration </p>

<h3>Example</h3>

<p> For an example of the use of @('prove/cgen'), you can study the
implementation of the @('test?') macro itself found in cgen/top.lisp. To see
the structure of @('cgen-state'), you can study the
@('print-testing-summary-fn') function which deconstructs it and prints its
information in a human-readable form. </p>
"
)

;; Put the test-checkpoint no-op backtrack hint in the override-hints
;; (acl2s-defaults :set testing-enabled t)


; [2016-04-03 Sun] Add fixers support to Cgen
;; (make-event
;;  (if *fixers-enabled*
;;      '(progn
;;         (include-book "fixers2" :ttags :all)
;;         (include-book "fixers-gl-backend" :ttags :all)
;;         (include-book "cgen-rules")
;;         (gl::gl-satlink-mode)
;;         )
;;    '(value-triple :invisible)))

; [2017-10-06 Fri] Replaced GL backend with a greedy algorithm for
; arranging fixers
(include-book "fixers-greedy" :ttags :all)
(include-book "cgen-rules")
