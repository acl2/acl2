(in-package "ACL2")

(include-book "instantiate")
(include-book "autohide")

(defxdoc clause-processor-tools
  :parents (clause-processor proof-automation)
  :short "Noteworthy clause-processors"
  :long "<p>Some noteworthy clause-processors include:</p>

<dl>

<dt>tools/defevaluator-fast</dt>

<dd>Basically like @(see defevaluator) but faster when you have a lot of
functions in your evaluator.</dd>


<dt>clause-processor/join-thms</dt>

<dd>The @('def-join-thms') macro adds theorems about conjoin, disjoin, etc for
your evaluator.</dd>


<dt>clause-processors/unify-subst</dt>

<dd>The @('def-unify') macro proves a unify/substitution algorithm correct for
your evaluator.</dd>


<dt>clause-processors/meta-extract-user</dt>

<dd>The @('def-meta-extract') macro sets up support for using the @(see
meta-extract) stuff to assume facts from the world are correct.</dd>


<dt>misc/beta-reduce</dt>

<dd>Implements a beta-reduction function, proves it preserves pseudo-termp, and
provides a macro for proving correctness of beta-reduction for your
evaluator.</dd>


<dt>centaur/misc/beta-reduce-full</dt>

<dd>Implements a recursive beta-reducer to expand away all lambdas, proves it
preserves pseudo-termp, proves it is correct for an evaluator.</dd>

</dl>

<p>See also the clause-processors directory in general; many books are
documented only in comments.</p>

")
