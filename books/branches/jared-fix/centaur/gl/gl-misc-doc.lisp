
(in-package "GL")

(include-book "gl-doc-string")

(defdoc symbolic-objects ":Doc-section ACL2::GL
Format of symbolic objects in ~il[GL].~/

Symbolic objects represent functions from the set of environments
 (described below) to the set of ACL2 objects.  The value of an object
at an environment is given by an evaluator function.  Symbolic objects
are recursively structured and have a number of constructors.  We
first briefly describe evaluators (and why there can be more than
one), then the structure of environment objects, and then the symbolic
object constructors.~/

a. Evaluators

A symbolic object evaluator is a function with the interface
~bv[]
 (EV symbolic-object environment) => value.
~ev[]

There may be several evaluators defined.  The differences between
evaluators have to do with the G-APPLY symbolic object type, which
represents a function applied to symbolic arguments.  In order to
evaluate such an object, the evaluator must be defined such that it
recognizes the particular function symbol used in the G-APPLY object.
An evaluator may not evaluate a symbolic object containing a G-APPLY
construct with an unrecognized function symbol.  One evaluator, named
EVAL-G-BASE, is initially defined in the GL library, and recognizes
function symbols of the predefined primitives included with the
library.  When new symbolic functions are created using the
MAKE-G-WORLD event, a new evaluator is created that recognizes each of
the functions for which symbolic counterparts exist, both newly
created and preexisting.

b. Environments

The basic components of symbolic objects are data structures
containing UBDDs, which represent Boolean functions of Boolean
variables, and G-VAR constructs, which represent unconstrained
variables.  To evaluate a symbolic object, each of these needs to be
evaluated to a constant.  We evaluate UBDDs to Booleans by choosing to
take either the true or false branch at each decision level; this
series of choices is described by a list of Booleans.  We evaluate
unconstrained variables by looking them up by name in a list of
bindings.  Therefore an environment is a pair containing a list of
Booleans used for evaluating UBDDs, and an association list containing
pairings of variable names and objects, used for evaluating G-VAR
constructs.

c. Symbolic Object Representation

There are eight basic constructions of symbolic objects, some of which
may recursively contain other symbolic objects.  We now describe each
such construction and its evaluation.

Representation: (:G-BOOLEAN . bdd)
Constructor: (G-BOOLEAN bdd)
Takes the values T and NIL.  The evaluation of a G-BOOLEAN object is
simply the evaluation of <bdd> using the list of Booleans in the
environment.

Representation: (:G-NUMBER . list-of-lists-of-bdds)
Constructor: (G-NUMBER list-of-lists-of-bdds)
Evaluates to a (complex rational) number.  <list-of-lists-of-bdds>
should be a list containing four or fewer lists of UBDDs, which
represent (in order):
 - the numerator of the real part  (two's-complement, default 0)
 - the denominator of the real part (unsigned, default 1)
 - the numerator of the imaginary part (two's-complement, default 0)
 - the denominator of the imaginary part (unsigned, default 1).
It is most common to represent an integer, for which only the first
list need be included.  In both the two's-complement and unsigned
representations, the bits are ordered from least to most significant,
with the last bit in the two's complement representation giving the
sign.  Two's complement lists may be sign-extended by repeating the
final bit, and unsigned lists may be zero-extended by appending NILs
after the final bit.

Representation (:G-CONCRETE . object)
Constructor: (G-CONCRETE object)
Evaluates to <object>.  While most ACL2 objects evaluate to themselves
anyway, this construct is useful for representing symbolic objects or
objects structured similarly to symbolic objects.  For example,
 (:G-CONCRETE . (:G-BOOLEAN . (T . NIL))) evaluates to
 (:G-BOOLEAN . (T . NIL)), whereas
 (:G-BOOLEAN . (T . NIL)) evaluates to either T or NIL.

Representation: (:G-VAR . name)
Constructor: (G-VAR . name)
<name> may be any object.  Evaluates to the object bound to <name> in
the environment.

Representation: (:G-ITE test then . else)
Constructor: (G-ITE test then else)
Each of <test>, <then>, and <else> must be symbolic objects.  If
<test> evaluates to a nonnil value, then this object evaluates to the
evaluation of <then>; otherwise this evaluates to the evaluation of
<else>.

Representation: (:G-APPLY fn . arglist)
Constructor: (G-APPLY fnsym arglist)
<fn> should be a symbol and <arglist> should be a symbolic object.  If
the evaluator recognizes <fn> and <arglist> evaluates to <args>, a
true-list of length equal to the arity of the function <fn>, then this
object evaluates to the application of <fn> to <args>.  Otherwise, the
evaluation is undefined; more specifically, it is provably equal to
 (APPLY-STUB <fn> <args>), where APPLY-STUB is an undefined stub
function.

Representation: atom
Every atom evaluates to itself.  However, the keyword symbols
:G-BOOLEAN, :G-NUMBER, :G-CONCRETE, :G-VAR, :G-ITE, and :G-APPLY are
not themselves well-formed symbolic objects.

Representation: (car . cdr)
A cons of two symbolic objects evaluates to the cons of their
evaluations.  Note that since the keyword symbols that distinguish
symbolic object constructions are not themselves well-formed symbolic
objects, this construction is unambiguous.


d. Miscellaneous notes about symbolic objects and evaluation

 - Any function from finitely many Boolean values to the universe of
ACL2 objects can be expressed using only the G-ITE, G-BOOLEAN, and
G-CONCRETE forms.

 - Most ACL2 objects are themselves well-formed symbolic objects which
evaluate to themselves.  The exceptions are ones which contain the
special keyword symbolis :G-BOOLEAN, :G-NUMBER, :G-CONCRETE, :G-VAR,
:G-ITE, and :G-APPLY.  These atoms (and out of all atoms, only these)
are not well-formed symbolic objects.  Since a cons of any two
well-formed symbolic objects is itself a well-formed symbolic objects,
only objects containing these atoms may be non-well-formed.

 - The function that checks well-formedness of symbolic objects is
GOBJECTP, and the initial evaluator function is GL::EVAL-G-BASE.  It
may be useful to read the definitions of these functions for reference
in case the above symbolic object documentation is unclear.

~/")


(defdoc debugging-indeterminate-results
  ":Doc-section ACL2::GL
Debugging indeterminate results in symbolic executions~/

GL includes two types of symbolic object, G-APPLY and G-VAR, whose symbolic
truth values can't be syntactically determined.  When the result of
symbolically executing the conclusion of a conjecture contains one of these
objects, usually the proof will then fail, since GL can't determine that the
result is never NIL.

Usually, however, G-VAR forms are not used, and G-APPLY forms are unwelcome if
they appear at all; they typically result in a symbolic execution failure of
some sort.  The following are a few common situations in which G-APPLY forms
are generated:

 * The stack depth limit, or \"clock\", was exhausted.

 * An unsupported primitive was called.  For example, as of November 2010 we
do not yet support UNARY-/.

 * A primitive was called on an unsupported type of symbolic object.  For
example, the symbolic counterparts for most arithmetic primitives will produce
a G-APPLY object if an input seems like it might represent a non-integer
rational.  Since symbolic operations on rationals are absurdly expensive, we
simply don't implement them for the most part.
~/

In order to determine why a G-APPLY form is being created, we suggest using the
following TRACE$ form:

~bv[]
 (trace$ (gl::g-apply :entry (prog2$ (cw \"Note: G-APPLY called.~~%\")
                                     (break$))
                      :exit nil))
~ev[]

Then when GL::G-APPLY is called in order to create the form, ~c[(BREAK$)] will
be called.  Usually this will allow you to look at the backtrace and determine
in what context the first G-APPLY object is being created.

Usually, the culprit is one of the last two bullets above.  Sometimes these
problems may be worked around by choosing a slightly different implementation
or by performing symbolic execution using an alternate definition of some
function (see ~il[GL::ALTERNATE-DEFINITIONS]).  If the clock was to blame, then
most likely the initial clock is set too low; use the ~c[HYP-CLK] or
~c[CONCL-CLK] keyword arguments to ~c[DEF-GL-THM] and ~c[DEF-GL-PARAM-THM] to
set this.~/ ")


(defdoc alternate-definitions
  ":Doc-section ACL2::GL
Specifying alternative definitions to be used for symbolic execution~/

Sometimes the definition of some function is ill-suited for automatic methods
of symbolic execution.  For example, ~c[(EVENP X)] is defined as
~bv[]
 (integerp (* x (/ 2)))
~ev[]
and because currently multiplication by a non-integer is not supported in GL,
this yields a G-APPLY form in most cases.

In this case and several others, one may instead provide an alternate
definition for the function in question and use that as the basis for GL
symbolic execution.

In the case of EVENP, the following theorem works as an alternate definition:

~bv[]
 (defthm evenp-is-logbitp
   (equal (evenp x)
          (or (not (acl2-numberp x))
              (and (integerp x)
                   (equal (logbitp 0 x) nil))))
   :rule-classes nil)
~ev[]

After proving this theorem, the following form sets this alternate definition
as the one GL will use when symbolically interpreting EVENP:

~bv[]
 (gl::set-preferred-def evenp evenp-is-logbitp)
~ev[]

This form produces one or more table events; ~l[TABLE].
~/~/")

(defdoc coverage-proofs
  ":Doc-Section ACL2::GL
Proving the coverage obligation in GL-based proofs~/

In order to prove a theorem using GL, one must show that the symbolic
objects chosen to represent the inputs are sufficiently general to
cover the entire set of interest.  See ~il[GL::SHAPE-SPECS] for a more
in-depth discussion.  The ~il[DEF-GL-THM] and ~il[DEF-GL-PARAM-THM]
events as well as the ~il[GL-HINT] hints all provide some degree
of automation for coverage proofs; often this is enough to satisfy the
coverage obligation without further user interaction.  Here we discuss
how to debug coverage proofs that do not succeed.~/

First, it is probably important to be able to re-run a coverage proof
easily without also re-running the associated symbolic execution,
which may be quite time-consuming.  To do this, in either the
~il[DEF-GL-THM] or ~il[DEF-GL-PARAM-THM] forms, add the keyword
argument ~c[:TEST-SIDE-GOALS T].  This form will then try to prove the
coverage obligation in exactly the manner it would do during the real
proof, but it will not attempt to prove the theorem itself, and will
not record a new ACL2 theorem even if the proof is successful.

During proof output, GL prints a message \"Now proving coverage\" when
it begins the coverage proof.  The initial goal of a coverage proof
will also have a hypothesis ~c[(GL::GL-CP-HINT 'GL::COVERAGE)]; this
hypothesis is logically meaningless, but a useful indicator of the
beginning of a coverage proof.

When GL's usual set of heuristics is used, a coverage proof proceeds
as follows.  The initial goal is as follows:

~bv[]
 (implies <theorem-hyps>
          (gl::shape-spec-obj-in-range
            <list-of-input-bindings>
            <list-of-input-variables>))
~ev[]

The coverage heuristics proceed by repeatedly opening up the
~c[GL::SHAPE-SPEC-OBJ-IN-RANGE] function.  This effectively splits the
proof into cases for each component of each variable; for example, if
one variable's shape specifier binding is a cons of two :G-NUMBER
forms, then its CAR and CDR will be considered separately.
Eventually, this results in several subgoals, each with conjunction of
requirements for some component of some input.

During this process of opening the ~c[GL::SHAPE-SPEC-OBJ-IN-RANGE]
conclusion, the coverage heuristics also examine and manipulate the
hypotheses.  When the conclusion is focused on a certain input
variable or component of that variable, and some hypothesis does not
mention that variable, that hypothesis will be dropped so as to speed
up the proof.  If a hypothesis does mention that variable, it may be
expanded (if it is not a primitive) so as to try and gain more
information about that variable.  This is a useful heuristic because
often the hypotheses consist of a conjunction of predicates about
different input variables or components of input variables, and some
of these predicates are often themselves defined as conjunctions of
predicates about subcomponents.

However, sometimes this expansion goes too far.  In many cases, some
conjuncts from the hypothesis have nothing to do with the coverage
obligation.  In these cases, the ~c[:DO-NOT-EXPAND] keyword argument
to ~c[DEF-GL-THM] and ~c[DEF-GL-PARAM-THM] may be used.  This argument
should evaluate to a list of function symbols; the coverage heuristic
is then prohibited from expanding any of these functions.

For efficiency, the set of rules used in coverage proofs is very
restricted.  Because of this, you may see in the proof output a goal
which should be obvious, but is not proven because the necessary
rule is not included.  The keyword argument ~c[:COV-THEORY-ADD] may be
used to enable certain additional rules that are not included.  The
set of rules that is used is defined in the ruleset
~c[GL::SHAPE-SPEC-OBJ-IN-RANGE-OPEN], which can be listed using
~bv[]
 (get-ruleset 'gl::shape-spec-obj-in-range-open (w state)).
~ev[]

The default heuristics for coverage proofs may not always be useful.
Therefore, the user may also supplement or replace the coverage
heuristics with arbitrary computed hints.  The keyword argument
~c[:COV-HINTS] gives a list of computed hint forms which, according to
the value of the keyword argument ~c[:COV-HINTS-POSITION], either
replaces or supplements the default hints.  ~c[:COV-HINTS-POSITION]
may be either ~c[:REPLACE], in which case the defaults are not used at
all; ~c[:FIRST], in which case the user-provided ~c[:COV-HINTS] are
tried first and the defaults afterward, or the default, ~c[:LAST], in
which case the default coverage heuristic is tried before the
user-provided hints.

One thing to keep in mind when replacing or supplementing the default
heuristics with your own computed hints is that subgoal names will be
different between a ~c[:TEST-SIDE-GOALS] and an actual attempt at
proving the theorem.  Therefore, it is best not to write computed
hints that depend on the ~c[ID] variable.
~/")
