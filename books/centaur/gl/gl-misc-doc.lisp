
(in-package "GL")

(defxdoc symbolic-objects
  :parents (introduction)
  :short "Format of symbolic objects in @(see gl)."

  :long "<p>Symbolic objects represent functions from the set of
environments (described below) to the set of ACL2 objects.  The value of an
object at an environment is given by an evaluator function.  Symbolic objects
are recursively structured and have a number of constructors.  We first briefly
describe evaluators (and why there can be more than one), then the structure of
environment objects, and then the symbolic object constructors.</p>


<h4>Evaluators</h4>

<p>A symbolic object evaluator is a function with the interface</p>

@({
 (EV symbolic-object environment) => value.
})

<p>There may be several evaluators defined.  The differences between evaluators
have to do with the G-APPLY symbolic object type, which represents a function
applied to symbolic arguments.  In order to evaluate such an object, the
evaluator must be defined such that it recognizes the particular function
symbol used in the G-APPLY object.  An evaluator may not evaluate a symbolic
object containing a G-APPLY construct with an unrecognized function symbol.
One evaluator, named EVAL-G-BASE, is initially defined in the GL library, and
recognizes function symbols of the predefined primitives included with the
library.</p>

<h4>Environments</h4>

<p>The basic components of symbolic objects are data structures containing
Boolean functions, represented either by BDDs or AIGs (see @(see modes)), and G-VAR
constructs, which represent unconstrained variables.  To evaluate a symbolic
object, each of these needs to be evaluated to a constant.  An environment
contains the information necessary to evaluate either kind of expression:</p>
<ul>
<li>a truth assignment for the Boolean variables used in the Boolean function
representation; in AIG mode, this is an alist mapping variable names to
Booleans, and in BDD mode, an ordered list of Booleans corresponding to the
decision levels of the BDDs.</li>
<li>an alist mapping unconstrained variable names to their values.</li>
</ul>

<h4>Symbolic Object Representation</h4>

<p>There are eight basic constructions of symbolic objects, some of which may
recursively contain other symbolic objects.  We now describe each such
construction and its evaluation.</p>

<dl>

<dt>Representation: (:G-BOOLEAN . bfr)</dt>
<dt>Constructor: (G-BOOLEAN bfr)</dt>

<dd>Takes the values T and NIL.  The evaluation of a G-BOOLEAN object is simply
the evaluation of @('<bdd>') using the list of Booleans in the
environment.</dd>

<dt>Representation: (:G-NUMBER . list-of-lists-of-bdds)</dt>
<dt>Constructor: (G-NUMBER list-of-lists-of-bdds)</dt>

<dd>Evaluates to a (complex rational) number.  @('<list-of-lists-of-bdds>')
should be a list containing four or fewer lists of UBDDs, which represent (in
order):

<ul>
<li>the numerator of the real part  (two's-complement, default 0)</li>
<li>the denominator of the real part (unsigned, default 1)</li>
<li>the numerator of the imaginary part (two's-complement, default 0)</li>
<li>the denominator of the imaginary part (unsigned, default 1).</li>
</ul>

It is most common to represent an integer, for which only the first list need
be included.  In both the two's-complement and unsigned representations, the
bits are ordered from least to most significant, with the last bit in the two's
complement representation giving the sign.  Two's complement lists may be
sign-extended by repeating the final bit, and unsigned lists may be
zero-extended by appending NILs after the final bit.</dd>

<dt>Representation (:G-CONCRETE . object)</dt>
<dt>Constructor: (G-CONCRETE object)</dt>

<dd>Evaluates to @('<object>').  While most ACL2 objects evaluate to themselves
anyway, this construct is useful for representing symbolic objects or objects
structured similarly to symbolic objects.  For example, @({
 (:G-CONCRETE . (:G-BOOLEAN . (T . NIL))) evaluates to
 (:G-BOOLEAN . (T . NIL)), whereas
 (:G-BOOLEAN . (T . NIL)) evaluates to either T or NIL.
})</dd>

<dt>Representation: (:G-VAR . name)</dt>
<dt>Constructor: (G-VAR . name)</dt>

<dd>@('<name>') may be any object.  Evaluates to the object bound to
@('<name>') in the environment.</dd>

<dt>Representation: (:G-ITE test then . else)</dt>
<dt>Constructor: (G-ITE test then else)</dt>

<dd>Each of @('<test>'), @('<then>'), and @('<else>') must be symbolic objects.
If @('<test>') evaluates to a nonnil value, then this object evaluates to the
evaluation of @('<then>'); otherwise this evaluates to the evaluation of
@('<else>').</dd>

<dt>Representation: (:G-APPLY fn . arglist)</dt>
<dt>Constructor: (G-APPLY fnsym arglist)</dt>

<dd>@('<fn>') should be a symbol and @('<arglist>') should be a symbolic
object.  If the evaluator recognizes @('<fn>') and @('<arglist>') evaluates to
@('<args>'), a true-list of length equal to the arity of the function
@('<fn>'), then this object evaluates to the application of @('<fn>') to
@('<args>').  Otherwise, the evaluation is undefined.</dd>

<dt>Representation: atom</dt>

<dd>Every atom evaluates to itself.  However, the keyword symbols
:G-BOOLEAN, :G-NUMBER, :G-CONCRETE, :G-VAR, :G-ITE, and :G-APPLY are not
themselves well-formed symbolic objects.</dd>

<dt>Representation: @('(car . cdr)')</dt>

<dd>A cons of two symbolic objects evaluates to the cons of their evaluations.
Note that since the keyword symbols that distinguish symbolic object
constructions are not themselves well-formed symbolic objects, this
construction is unambiguous.</dd>

</dl>

<h4>Miscellaneous notes about symbolic objects and evaluation</h4>

<ul>

<li>Any function from finitely many Boolean values to the universe of
ACL2 objects can be expressed using only the G-ITE, G-BOOLEAN, and
G-CONCRETE forms.</li>

<li>Most ACL2 objects are themselves well-formed symbolic objects which
evaluate to themselves.  The exceptions are ones which contain the special
keyword symbolis :G-BOOLEAN, :G-NUMBER, :G-CONCRETE, :G-VAR,
:G-ITE, and :G-APPLY.  These atoms (and out of all atoms, only these)
are not well-formed symbolic objects.  Since a cons of any two
well-formed symbolic objects is itself a well-formed symbolic objects,
only objects containing these atoms may be non-well-formed.</li>

<li>The function that checks well-formedness of symbolic objects is GOBJECTP,
and the initial evaluator function is GL::EVAL-G-BASE.  It may be useful to
read the definitions of these functions for reference in case the above
symbolic object documentation is unclear.</li>

</ul>")


(defxdoc debugging-indeterminate-results
  :parents (debugging)
  :short "Debugging indeterminate results in symbolic executions"

  :long "<p>GL includes two types of symbolic object, G-APPLY and G-VAR, whose
symbolic truth values can't be syntactically determined.  When the result of
symbolically executing the conclusion of a conjecture contains one of these
objects, usually the proof will then fail, since GL can't determine that the
result is never NIL.</p>

<p>It is common to use GL in such a way that G-VAR forms are not used, and
G-APPLY forms are unwelcome if they appear at all; when they do, they typically
result in a symbolic execution failure of some sort.  However, there are ways
of using GL in which G-VAR and G-APPLY forms are expected to exist; see @(see
term-level-reasoning).  The following are a few common situations in which
G-APPLY forms may be unexpectedly generated:</p>

<ul>

<li>The stack depth limit, or \"clock\", was exhausted.  This may happen when
symbolically executing a recursive function if the termination condition can't
be detected, though this is often caused by previous introduction of an
unexpected G-APPLY object.</li>

<li>An unsupported primitive was called.  For example, as of November 2010 we
do not yet support UNARY-/, so any call of UNARY-/ encountered during symbolic
execution will return a G-APPLY of UNARY-/ to the input argument.</li>

<li>A primitive was called on an unsupported type of symbolic object.  For
example, the symbolic counterparts for most arithmetic primitives will produce
a G-APPLY object if an input seems like it might represent a non-integer
rational.  Since symbolic operations on rationals are absurdly expensive, we
simply don't implement them for the most part.</li>

</ul>

<p>If you are not expecting GL to create G-APPLY objects but you are
encountering indeterminate results, we suggest using the following TRACE$ form
to determine why a G-APPLY object is first being created:</p>

@({
 (trace$ (gl::g-apply :entry (prog2$ (cw \"Note: G-APPLY called.~%\")
                                     (break$))
                      :exit nil))
})
<p>Then when GL::G-APPLY is called in order to create the form, @('(BREAK$)')
will be called.  Usually this will allow you to look at the backtrace and
determine in what context the first G-APPLY object is being created.</p>

<p>Alternatively, if you are expecting some G-APPLY forms to be created but
unexpected ones are cropping up, you can add a :cond to make the break
conditional on the function symbol being applied:</p>
@({
 (trace$ (gl::g-apply :cond (not (eq gl::fn 'foo))
                      :entry (prog2$ (cw \"Note: G-APPLY called.~%\")
                                     (break$))
                      :exit nil))
})

<p>Usually, the culprit is one of the last two bullets above.  Sometimes these
problems may be worked around by choosing a slightly different implementation
or by performing symbolic execution using an alternate definition of some
function (see @(see ALTERNATE-DEFINITIONS)).  If the clock was to blame, then
most likely the initial clock is set too low; use the @('HYP-CLK') or
@('CONCL-CLK') keyword arguments to @('DEF-GL-THM') and @('DEF-GL-PARAM-THM')
to set this.</p>")


(defxdoc alternate-definitions
  :parents (optimization)
  :short "Specifying alternative definitions to be used for symbolic
  execution."

  :long "<p>Sometimes the definition of some function is ill-suited for
automatic methods of symbolic execution.  For example, @('(EVENP X)') is defined
as</p>

@({
 (integerp (* x (/ 2)))
})

<p>and because currently multiplication by a non-integer is not supported in
GL, this yields a G-APPLY form in most cases.</p>

<p>In this case and several others, one may instead provide an alternate
definition for the function in question and use that as the basis for GL
symbolic execution.</p>

<p>In the case of EVENP, the following theorem works as an alternate
definition:</p>

@({
 (defthm evenp-is-logbitp
   (equal (evenp x)
          (or (not (acl2-numberp x))
              (and (integerp x)
                   (equal (logbitp 0 x) nil))))
   :rule-classes nil)
})

<p>After proving this theorem, the following form sets this alternate
definition as the one GL will use when symbolically interpreting EVENP:</p>

@({
 (gl::set-preferred-def evenp evenp-is-logbitp)
})

<p>This form produces one or more @(see table) events.</p>")


(defxdoc coverage-proofs
  :parents (introduction)
  :short "Proving the coverage obligation in GL-based proofs."

  :long "<p>In order to prove a theorem using GL, one must show that the
symbolic objects chosen to represent the inputs are sufficiently general to
cover the entire set of interest.  See @(see SHAPE-SPECS) for a more in-depth
discussion.  The @(see DEF-GL-THM) and @(see DEF-GL-PARAM-THM) events as well
as the @(see GL-HINT) hints all provide some degree of automation for coverage
proofs; often this is enough to satisfy the coverage obligation without further
user interaction.  Here we discuss how to debug coverage proofs that do not
succeed.</p>

<p>First, it is probably important to be able to re-run a coverage proof easily
without also re-running the associated symbolic execution, which may be quite
time-consuming.  To do this, in either the @(see DEF-GL-THM) or @(see
DEF-GL-PARAM-THM) forms, add the keyword argument @(':TEST-SIDE-GOALS T').
This form will then try to prove the coverage obligation in exactly the manner
it would do during the real proof, but it will not attempt to prove the theorem
itself, and will not record a new ACL2 theorem even if the proof is
successful.</p>

<p>During proof output, GL prints a message \"Now proving coverage\" when it
begins the coverage proof.  The initial goal of a coverage proof will also have
a hypothesis @('(GL::GL-CP-HINT 'GL::COVERAGE)'); this hypothesis is logically
meaningless, but a useful indicator of the beginning of a coverage proof.</p>

<p>When GL's usual set of heuristics is used, a coverage proof proceeds as
follows.  The initial goal is as follows:</p>

@({
 (implies <theorem-hyps>
          (gl::shape-spec-obj-in-range
            <list-of-input-bindings>
            <list-of-input-variables>))
})

<p>The coverage heuristics proceed by repeatedly opening up the
@('GL::SHAPE-SPEC-OBJ-IN-RANGE') function.  This effectively splits the proof
into cases for each component of each variable; for example, if one variable's
shape specifier binding is a cons of two :G-NUMBER forms, then its CAR and CDR
will be considered separately.  Eventually, this results in several subgoals,
each with conjunction of requirements for some component of some input.</p>

<p>During this process of opening the @('GL::SHAPE-SPEC-OBJ-IN-RANGE')
conclusion, the coverage heuristics also examine and manipulate the hypotheses.
When the conclusion is focused on a certain input variable or component of that
variable, and some hypothesis does not mention that variable, that hypothesis
will be dropped so as to speed up the proof.  If a hypothesis does mention that
variable, it may be expanded (if it is not a primitive) so as to try and gain
more information about that variable.  This is a useful heuristic because often
the hypotheses consist of a conjunction of predicates about different input
variables or components of input variables, and some of these predicates are
often themselves defined as conjunctions of predicates about subcomponents.</p>

<p>However, sometimes this expansion goes too far.  In many cases, some
conjuncts from the hypothesis have nothing to do with the coverage obligation.
In these cases, the @(':DO-NOT-EXPAND') keyword argument to @('DEF-GL-THM') and
@('DEF-GL-PARAM-THM') may be used.  This argument should evaluate to a list of
function symbols; the coverage heuristic is then prohibited from expanding any
of these functions.</p>

<p>For efficiency, the set of rules used in coverage proofs is very restricted.
Because of this, you may see in the proof output a goal which should be
obvious, but is not proven because the necessary rule is not included.  The
keyword argument @(':COV-THEORY-ADD') may be used to enable certain additional
rules that are not included.  The set of rules that are used is defined in the
ruleset @('GL::SHAPE-SPEC-OBJ-IN-RANGE-OPEN'), which can be listed using</p>

@({
 (get-ruleset 'gl::shape-spec-obj-in-range-open (w state)).
})

<p>The default heuristics for coverage proofs may not always be useful.
Therefore, the user may also supplement or replace the coverage heuristics with
arbitrary computed hints.  The keyword argument @(':COV-HINTS') gives a list of
computed hint forms which, according to the value of the keyword argument
@(':COV-HINTS-POSITION'), either replaces or supplements the default hints.
@(':COV-HINTS-POSITION') may be either @(':REPLACE'), in which case the
defaults are not used at all; @(':FIRST'), in which case the user-provided
@(':COV-HINTS') are tried first and the defaults afterward, or the default,
@(':LAST'), in which case the default coverage heuristic is tried before the
user-provided hints.</p>

<p>Note that subgoal names will be different between a @(':TEST-SIDE-GOALS')
and an actual attempt at proving the theorem.  Therefore, it is best not to
write computed hints that depend on the @('ID') variable.</p>")
