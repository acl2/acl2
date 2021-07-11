; SATLINK - Link from ACL2 to SAT Solvers
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

; top.lisp -- Main file to include to use SATLINK.

(in-package "SATLINK")
(include-book "cnf")
(include-book "dimacs")
(include-book "lrat-interface")
(include-book "projects/sat/lrat/sorted/lrat-parser" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/strnatless" :dir :system)
(include-book "std/strings/defs" :dir :system) ; previously came in via tshell
(include-book "oslib/tempfile" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
(include-book "config")
(local (include-book "std/lists/nthcdr" :dir :system))

(defxdoc satlink
  :parents (acl2::boolean-reasoning)
  :short "A simple representation for Boolean formulas in <see topic='@(url
cnf)'>conjunctive normal form</see>, and a mechanism for calling SAT solvers
from within ACL2 and trusting what they say. (CCL Only)"

  :long "<p>SAT solvers are programs that can solve the <a
href='https://en.wikipedia.org/wiki/Boolean_satisfiability_problem'>Boolean
satisfiability problem</a>.  Modern solvers implement clever algorithms in fast
languages like C and C++, so they can quickly solve many large problems.
Developing faster SAT solvers is an active area of research with frequent <a
href='http://www.satcompetition.org/'>competitions</a>.</p>

<p>SAT solvers are useful because many problems can be recast as SAT problems.
For instance, the @(see gl) framework can translate many ACL2 proof goals,
e.g., bounded arithmetic problems, into SAT problems.  This allows for a large
class of theorems to be solved quickly and automatically by the SAT solver.
This is especially useful in @(see acl2::hardware-verification).</p>

<p><b>Satlink</b> is an interfacing library that allows ACL2 to make use of
off-the-shelf SAT solvers like <a
href='http://fmv.jku.at/lingeling/'>lingeling</a>, <a
href='http://www.labri.fr/perso/lsimon/glucose/'>glucose</a>, and so on; see
@(see sat-solver-options) for download and build help.  It provides:</p>

<ul>

<li>A (trivial) representation and semantics for Boolean formulas in
conjunctive normal form; see @(see cnf).</li>

<li>A function, @(see sat), that can invoke a SAT solver on a formula and
interpret its output.  This is done via @(see acl2::tshell), so the integration
is very smooth, e.g., you can interrupt the SAT solver.</li>

<li>A @(see logical-story) that allows us to <color rgb='#ff0000'><b>assume,
using a <see topic='@(url defttag)'>trust tag</see></b></color>, that when the
SAT solver claims the formula is unsatisfiable, it's correct.</li>

</ul>

<p>We don't have to assume anything when the SAT solver claims that a formula
is satisfiable, since we can just check the alleged satisfying assignment it
produces.</p>

<p>The soundness threat may be reduced by checking the output of the SAT
solver.  There has been recent progress in the SAT community toward
standardizing formats for UNSAT proofs, reducing the overhead of producing
these proofs, and developing fast tools to check these proofs.  Satlink
includes, e.g., a @('glucose-cert') script that implements this idea; see @(see
sat-solver-options).</p>


<h3>Loading the Library</h3>

<p>Satlink is a low-level library.  It would be a bit weird to want to use it
directly.  Instead, it is typically used indirectly through other tools, such
as the @(see gl) framework, or @(see acl2::aig-sat), or the @(see
aignet::aignet-cnf) translation.  These other approaches are likely to be more
convenient than using Satlink directly.</p>

<p>If you want to include Satlink directly for some reason, the book to include
is:</p>

@({
 (include-book \"centaur/satlink/top\" :dir :system)
})

<p>Once you load this book, you generally need to construct your input @(see
cnf) formula in some way, and then call @(see sat).</p>")

(defxdoc sat-solver-options
  :parents (satlink)
  :short "How to get a SAT solver that you can use with @(see satlink)."

  :long "<p>To use Satlink you will need at least one SAT solver.  Below are
some solvers that are known to work well with Satlink.  You may wish to install
several of these.  This lets you switch between solvers to figure out which
solver is best for your particular problem, and perhaps to gain some additional
confidence that a particular problem really is unsatisfiable (by checking it
with many solvers.)</p>


<h3><a href='http://www.labri.fr/perso/lsimon/glucose/'>Glucose</a> &mdash;
open source, recommended</h3>

<p>Based on our experiences using @(see gl) for proofs about hardware modules
at Centaur, we usually try Glucose first.  On Linux, version 3.0, 4.0, or 4.1
should work with Satlink without modification (though, some users have had
difficulty with 4.0).  (We have also successfully used earlier versions with
Satlink, but occasionally needed to patch them in minor ways, e.g., to print
counterexamples.)</p>

<p>Quick instructions:</p>

<ul>
<li>Download Glucose 3.0 and extract @('glucose-3.0.tgz') somewhere</li>
<li>@('cd glucose-3.0/core; make')</li>
<li>@('cd glucose-3.0/simp; make')</li>
<li>Verify that @('glucose-3.0/simp/glucose --help') prints a help message</li>
</ul>

<p>(NOTE for Mac and FreeBSD/PCBSD users: If you are building Glucose 3.0 or
4.0, the build might fail.  In that case, a solution may be first to make the
replacements shown below, where the the first in each pair (@('<')) is the
Mac/FreeBSD/PCBSD version, while the second in each pair (@('>')) is the
original source.  (Thanks to Marijn Heule and Warren Hunt for these
suggestions.)</p>

<p>In file @('../glucose-3.0/core/SolverTypes.h'):</p>

@({
<     // friend Lit mkLit(Var var, bool sign = false);
---
>     friend Lit mkLit(Var var, bool sign = false);

< inline  Lit  mkLit     (Var var, bool sign = false) { Lit p; p.x =
var + var + (int)sign; return p; }
---
> inline  Lit  mkLit     (Var var, bool sign) { Lit p; p.x = var + var + (int)sign; return p; }

})

<p>In the file @('../glucose-3.0/utils/System.cc') comment the line below, but
note that this is probably only necessary for FreeBSD/PCBSD, not for Mac:</p>

@({
   <   // double MiniSat::memUsedPeak(void) { return memUsed(); }
   ---
   >   double MiniSat::memUsedPeak(void) { return memUsed(); }
})

<p>End of NOTE for Mac and FreeBSD/PCBSD users.)</p>

<p>Now create a shell script as follows, somewhere in your @('$PATH'), named
@('glucose').  Note that the order of the arguments is important.</p>

@({
    #!/bin/sh
    /path/to/glucose-3.0/simp/glucose -model \"$@\"
})

<p>As a quick test to make sure things are working, you can try to certify this
book:</p>

@({
    cd [books]/centaur/satlink/solvers
    cert.pl test-glucose
})

<p>You should now be able to use Satlink with configurations such as:</p>

@({
    (satlink::make-config :cmdline \"glucose\")
})

<p>Glucose can (optionally) produce UNSAT proofs that can be checked by a
simpler program.  Satlink includes a script that makes it easy to run the
solver and then check any UNSAT answers.  See @(see unsat-checking) for more
information.</p>



<h3><a href='http://www.cril.univ-artois.fr/~hoessen/penelope.html'>Penelope</a></h3>

<p>Penelope is a (mostly) open-source, parallel sat solver.  The build process
is simple: run @('make') and add the resulting @('penelope') executable to your
@('PATH').  As a quick test to ensure things are working, you can try to
certify this book:</p>

@({
    cd [books]/centaur/satlink/solvers
    cert.pl test-penelope
})

<p>Note that you will usually need to point Penelope at a configuration file
that tells it, e.g., how many cores to use.  The Penelope distribution has a
@('configuration.ini') file that you can start with.  You can then use a
Satlink configuration like:</p>

@({
    (satlink::make-config
     :cmdline \"penelope -config=/path/to/configuration.ini\")
})

<p>We are not aware of any UNSAT proof support for this solver.</p>


<h3><a href='http://fmv.jku.at/lingeling/'>Lingeling</a></h3>

<p>An older version of Lingeling (Version ALA) is released under an open
source (GPL3) license.  For most of our problems, we found this version to be
somewhat slower than Glucose 2.1.  Of course, our experiences may not be
representative.</p>

<p>Newer versions of Lingeling are available under a more restrictive license.
These modern versions fared very well in the recent SAT competitions, so if the
license does not pose a problem for you, it may well be worth trying.</p>

<p>For the open source version ALA, the build process is simple: download and
extract the tarball, run @('./configure') and @('make'), and then add the
resulting @('lingeling') and/or @('plingeling') executables to your PATH.  As a
quick test to ensure things are working, you can try to certify these
books:</p>

@({
    cd [books]/centaur/satlink/solvers
    cert.pl test-lingeling
    cert.pl test-plingeling
})

<p>Newer versions of Lingeling are allegedly able to produce unsat proofs, but
we haven't figured out how to make it work.</p>


<h3><a
href='http://tools.computational-logic.org/content/riss3g.php'>Riss3G</a></h3>

<p>The Riss3g solver is a (mostly) open-source variant of Glucose that did
fairly well in recent competitions and seems to be sometimes faster than
Glucose.</p>

<p>The build process was reasonably straightforward.  After building, put the
resulting @('riss3g') and @('riss3gSimp') programs into your @('PATH').  As a
quick test to ensure things are working, you can try to certify these
books:</p>

@({
    cd [books]/centaur/satlink/solvers
    cert.pl test-riss3g
    cert.pl test-riss3gSimp
})

<p>Like Glucose, @('riss3g') has an ability to produce unsat proofs that can be
checked with an external program.  Satlink includes a script that makes it easy
to run the solver and then check any UNSAT answers.  See @(see unsat-checking)
for more information.</p>


<h3>Other Solvers</h3>

<p>In principle, Satlink should work with any SAT solver that implements the
DIMACS format.  This format is used in the <a
href='http://www.satcompetition.org/'>SAT competitions</a>, so it is
implemented by many solvers.  Accordingly, you may wish to look at, e.g., the
<a href='http://www.satcompetition.org/2013/results.shtml'>SAT Competition
Results</a> to get ideas about what SAT solvers are likely to perform well.</p>

<p>Getting a new solver to work with Satlink <i>should</i> be straightforward.
Typically you will need to install the solver, add it to your @('PATH'), and
then figure out how to run it.  Satlink expects to be able to invoke the solver
using:</p>

@({
     <solver-command> <input-file>
})

<p>Sometimes a solver may need extra command-line arguments.  For instance,
Glucose needs a @('-model') switch or it won't print the satisfying
assignment (i.e., @('v') lines) in case of SAT.  You might be able to write a
small script to supply these arguments, e.g., as in the @('glucose') script
above.</p>

<p>To test out your new solver, Satlink includes a primitive @(see
check-config) command that you can use to try your solver on a handful of
trivial problems.  This is a very good way to make sure that at least the basic
i/o contract seems to be working.  It should be easy to adapt one of the
@('test-') scripts in the @('centaur/satlink/solvers') directory to suit your
solver.</p>

<p>If the @('check-config') passes and you want a more thorough check, you
might try to run your new solver on, e.g., @('centaur/esim/tutorial/sat.lsp')
and the various files in @('centaur/regression').</p>")


(defsection unsat-checking
  :parents (sat-solver-options)
  :short "Options for running SAT solvers that produce UNSAT proofs."

  :long "<p>For higher confidence (at some cost to runtime), some SAT solvers
are able to produce UNSAT proofs.  Small programs such as <a
href='http://www.cs.utexas.edu/~marijn/drat-trim/'>drat-trim</a> can check
these proofs, to ensure the SAT solver reasoned correctly.</p>

<p>Satlink now includes Perl scripts that can make use of this capability for
the Glucose and Riss3g solvers.  In particular, see the following scripts:</p>

<ul>
<li>@('centaur/satlink/solvers/glucose-cert')</li>
<li>@('centaur/satlink/solvers/riss3g-cert')</li>
</ul>

<p>The general idea of these scripts is, e.g., for Glucose:</p>

<ul>

<li>We first call Glucose to solve the problem;</li>

<li>When Glucose reports SAT, we just exit (because Satlink can check the
satisfying assignment itself); or</li>

<li>When Glucose reports UNSAT, we check the proof using the Drat-Trim unsat
proof checker.  We only print an \"s UNSATISFIABLE\" line if Drat-Trim says
that the proof is ok.</li>

</ul>

<p>All of this works well with Satlink.  You can still see the output from the
solver and the verifier in real time, interrupt it, etc.</p>


<h3>Setup</h3>

<p>To use these tools, you will need to first:</p>

<ul>

<li>Install @('glucose') and/or @('riss3g') as described in @(see
sat-solver-options), and</li>

<li>Install the <a
href='http://www.cs.utexas.edu/~marijn/drat-trim/'>drat-trim</a> program as
@('drat-trim') somewhere in your PATH.</li>

</ul>

<p>You can then add the @('glucose-cert') or @('riss3g-cert') scripts to your
PATH.  As a quick test to ensure things are working, you can try to certify
these books:</p>

@({
    cd [books]/centaur/satlink/solvers
    cert.pl test-glucose-cert
    cert.pl test-riss3g-cert
})

<p>To use these scripts from Satlink, you can then typically just use a Satlink
configuration such as:</p>

@({
    (satlink::make-config :cmdline \"glucose-cert\" ...)
})


<h3>Skipping Proof Checking During Development</h3>

<p>The environment variable SATLINK_TRUST_SOLVER can be set to 1 to suppress
proof checking.  When this variable is set, we will NOT instruct the solver to
produce an UNSAT proof and (of course) will not check the non-existent
proof.</p>

<p>We use this feature as follows:</p>

<ul>

<li>We generally set @('SATLINK_TRUST_SOLVER=1') in our startup scripts.  This
way, when we are working with ACL2 (either interactively, or when rebuilding
books), we just trust the solver and avoid the overhead of UNSAT checking.</li>

<li>We set @('SATLINK_TRUST_SOLVER=0') for our nightly regressions.  These are
run automatically, overnight, so performance is not very important.</li>

</ul>

<p>This gives us a good blend of performance and confidence.  If the solver
somehow screws up and claims to have proven a theorem that isn't really true,
we may not find out about it until our regression fails.  But in exchange, we
can always use @('glucose-cert') with no performance impact on our everyday
work.</p>")

(defsection dimacs-interp
  :parents (dimacs)
  :short "How we interpret the DIMACS formatted output from the SAT solver.")

(define satlink-skip-ws
  :parents (dimacs-interp)
  ((x  stringp               "String we're processing")
   (n  natp                  "Current position in @('x').")
   (xl (equal xl (length x)) "Pre-computed length of @('x')."))
  :guard (<= n xl)
  :returns (new-n natp "New position after skipping whitespace.")
  :measure (nfix (- (nfix xl) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
                   :exec (int= xl n) ;; It's *really* fast
                   ))
        (lnfix n))
       (char (char x n))
       ((when (or (eql char #\Space)
                  (eql char #\Tab)))
        (satlink-skip-ws x (+ 1 (lnfix n)) xl)))
    (lnfix n))
  ///
  (defthm lower-bound-satlink-skip-ws
    (implies (natp n)
             (<= n (satlink-skip-ws x n xl)))
    :rule-classes ((:rewrite) (:linear)))
  (defthm lower-bound-satlink-skip-ws-nfix
    (<= (nfix n) (satlink-skip-ws x n xl))
    :rule-classes (:rewrite :linear))
  (defthm upper-bound-satlink-skip-ws
    (implies (and (natp n)
                  (natp xl)
                  (<= n xl))
             (<= (satlink-skip-ws x n xl) xl))
    :rule-classes ((:rewrite) (:linear))))

(define satlink-parse-variable-line
  :parents (dimacs-interp)
  :prepwork ((local (in-theory (disable ACL2::FOLD-CONSTS-IN-+))))
  ((x          stringp                "String we're processing.")
   (n          natp                   "Current position in @('x').")
   (xl         (equal xl (length x))  "Pre-computed length of @('x').")
   (saw-zero-p booleanp               "Have we seen a 0 yet?")
   (env$                              "Satisfying assignment we're populating."))
  :guard (<= n xl)
  :returns (mv (error      "True if there is an error parsing this line.")
               (saw-zero-p "Did we ever see 0?  (checked later).")
               (env$       "Updated satisfying assignment."))
  :measure (nfix (- (nfix xl) (nfix n)))
  (b* ((n (satlink-skip-ws x n xl))
       ((when (mbe :logic (zp (- (nfix xl) n))
                   :exec  (int= xl n)))
        ;; Reached end of line, all done.
        (mv nil saw-zero-p env$))
       ;; Should find a number here or a minus sign.
       (minus-p (eql (char x n) #\-))
       (n       (if minus-p (+ n 1) n))
       ((when (int= xl n))
        (cw "SATLINK: Error parsing variable line: ends with minus? ~s0" x)
        (mv t saw-zero-p env$))

       ((mv val len) (str::parse-nat-from-string x 0 0 n xl))
       ((when (zp len))
        ;; Expected a number here.
        (cw "SATLINK: Error parsing variable line: ~s0" x)
        (mv t saw-zero-p env$))
       ((when (and (zp val) saw-zero-p))
        (cw "SATLINK: Error: saw zero multiple times: ~s0" x)
        (mv t saw-zero-p env$))
       (saw-zero-p (or saw-zero-p (zp val)))
       (index (1- val)) ;; Adjusted for dimacs encoding
       (env$ (cond ((zp val)
                    env$)
                   ((< index (bits-length env$))
                    (set-bit index (if minus-p 0 1) env$))
                   (t
                    ;; Historically we caused an error here.  However, we later
                    ;; found that some SAT solvers (e.g., Riss3g) would produce
                    ;; assignments to other variables, presumably variables that
                    ;; they are inventing.  Well, this isn't really a problem,
                    ;; and we're going to check the assignment anyway, so it
                    ;; seems reasonable to tolerate this.
                    env$))))
    (satlink-parse-variable-line x (+ n len) xl saw-zero-p env$)))

(define satlink-handle-line
  :parents (dimacs-interp)
  ((line        "one line of sat solver output" stringp)
   (saw-unsat-p "have we seen an 's UNSATISFIABLE' line?")
   (saw-sat-p   "have we seen an 's SATISFIABLE' line?")
   (saw-zero-p  "have we seen a 0 in a 'v' line?")
   (env$        "evolving variable bindings"))
  :returns
  (mv (error-p "did we see something we don't understand?")
      saw-unsat-p
      saw-sat-p
      saw-zero-p
      env$)

  (b* ((len (length line))
       ((when (< len 2))
        ;; We'll ignore blank lines and lines that don't have a "x " at the
        ;; beginning, where x is "s" or "v".
        (mv nil saw-unsat-p saw-sat-p saw-zero-p env$))
       (char (char line 0))
       ((unless (and (or (eql char #\s)  ;; Result
                         (eql char #\v)) ;; Variable assignment
                     (eql (char line 1) #\Space)))
        ;; Ignore it
        (mv nil saw-unsat-p saw-sat-p saw-zero-p env$))
       ((when (eql char #\s))
        (cond ((str::strprefixp "s SATISFIABLE" line)
               (mv nil saw-unsat-p t saw-zero-p env$))
              ((str::strprefixp "s UNSATISFIABLE" line)
               (mv nil t saw-sat-p saw-zero-p env$))
              (t
               (prog2$
                (cw "SATLINK: Unrecognized result line: ~s0~%" line)
                (mv nil saw-unsat-p saw-sat-p saw-zero-p env$)))))
       ;; Else it's a variable line
       ((when saw-zero-p)
        (cw "SATLINK: Variable lines after already saw zero: ~s0~%" line)
        (mv t saw-unsat-p saw-sat-p saw-zero-p env$))
       ((mv error saw-zero-p env$)
        (satlink-parse-variable-line line 1 len nil env$)))
    (mv error saw-unsat-p saw-sat-p saw-zero-p env$)))

(define satlink-handle-lines
  :parents (dimacs-interp)
  ((lines string-listp)
   (saw-unsat-p "have we seen an 's UNSATISFIABLE' line?")
   (saw-sat-p   "have we seen an 's SATISFIABLE' line?")
   (saw-zero-p  "have we seen a 0 in a 'v' line?")
   (env$        "evolving variable bindings"))
  :returns
  (mv (error-p "did we see something we don't understand?")
      saw-unsat-p
      saw-sat-p
      saw-zero-p
      env$)
  (b* (((when (atom lines))
        (mv nil saw-unsat-p saw-sat-p saw-zero-p env$))
       ((mv error-p saw-unsat-p saw-sat-p saw-zero-p env$)
        (satlink-handle-line (car lines) saw-unsat-p saw-sat-p saw-zero-p env$))
       ((when error-p)
        (mv error-p saw-unsat-p saw-sat-p saw-zero-p env$)))
    (satlink-handle-lines (cdr lines) saw-unsat-p saw-sat-p saw-zero-p env$)))

(define satlink-parse-output
  :parents (dimacs-interp)
  ((out  string-listp "output lines from the SAT solver.")
   (env$              "empty env to populate, should be sized already."))
  :returns (mv (status "Either :failed, :sat, or :unsat")
               (env$   "Variable assignment, in the :sat case."))
  (b* (((mv error-p saw-unsat-p saw-sat-p saw-zero-p env$)
        (satlink-handle-lines out nil nil nil env$))
       ((when error-p)
        ;; Already printed a warning
        (mv :failed env$))
       ;; There are a couple of other weird things to detect.
       ((when (and saw-unsat-p saw-sat-p))
        (cw "SATLINK: solver says both SAT and UNSAT?   Uh... guys?")
        (mv :failed env$))
       ((when (and saw-sat-p (not saw-zero-p)))
        (cw "SATLINK: solver says SAT but we didn't find a 0 in variable lines?")
        (mv :failed env$))
       ((when (and saw-unsat-p saw-zero-p))
        (cw "SATLINK: solver says UNSAT but is giving us variables?")
        (mv :failed env$))
       ((when saw-unsat-p)
        (mv :unsat env$))
       ((when saw-sat-p)
        (mv :sat env$)))
    ;; Didn't see either sat or unsat.
    (mv :failed env$)))

(defsection satlink-extra-hook
  :parents (satlink)
  :short "An attachable hook for performing extra actions after successful
calls of the SAT solver."

  :long "<p>This is an advanced feature for Satlink hackers.</p>

<p>@(call satlink-extra-hook) is an attachable function (see @(see defattach))
that is called by @(see satlink-run-impl) after successful invocations of the
SAT solver.</p>

<p>The default hook does nothing, but you may be able to implement custom hooks
that do useful things.  For instance, the @(see gather-benchmarks) hook can be
used to automatically collect up the DIMACS files for Satlink problems.  These
kinds of hooks might require additional trust tags, so it is nice to keep them
out of Satlink itself.</p>

<p>A hook can access several arguments:</p>

<ul>

<li>@('cnf') is the formula we were trying to solve.</li>

<li>@('filename') is the name of the temporary input file that was given to the
SAT solver.  At the time the hook is invoked, the file should still exist, even
when we are removing temporary files.</li>

<li>@('status') says whether the SAT solver returned @(':sat') or @(':unsat').
Note that you don't have to consider @(':failed') because the hook does not get
invoked in that case.</li>

<li>@('env$') is the satisfying assignment in case of @(':sat') answers.</li>

<li>@('state') is the usual ACL2 state, which might be useful for sending some
extra information to your hook, e.g., state globals or similar.</li>

</ul>"

  (encapsulate
    (((satlink-extra-hook * * * env$ state) => *
      :formals (cnf filename status env$ state)
      :guard (and (lit-list-listp cnf)
                  (stringp filename)
                  (or (eq status :sat)
                      (eq status :unsat)))))
    (local (defun satlink-extra-hook (cnf filename status env$ state)
             (declare (xargs :stobjs (env$ state))
                      (ignorable cnf filename status env$ state))
             nil)))

  (define default-satlink-hook ((cnf      lit-list-listp)
                                (filename stringp)
                                (status   (or (eq status :sat)
                                              (eq status :unsat)))
                                (env$)
                                (state))
    (declare (ignorable cnf filename status env$ state))
    nil)

  (defattach satlink-extra-hook default-satlink-hook))

(define satlink-run-impl
  :parents (logical-story)
  :short "Core function used to run the SAT solver."
  ((config config-p       "Which solver to call, etc.")
   (cnf    lit-list-listp "The formula to solve.")
   (env$   "Empty env to populate, will usually be resized")
   &key
   (state 'state))
  :returns (mv (status ":sat, :unsat, or :failed")
               (env$ "Variable assignment, in the :sat case.")
               (lrat-proof "LRAT proof, in the :unsat case, if config.lrat-check is set.")
               (state state-p1 :hyp (state-p1 state)))
  :long "<p>This function actually runs the SAT solver: it exports the formula
into a @(see dimacs) file, invokes the SAT solver on it, and interprets the
answer.  This function is typically never used directly; instead see @(see
satlink-run).</p>"

  (b* (((config config))

       ((mv filename state) (oslib::tempfile "satlink"))
       ((unless filename)
        (cw "SATLINK: Error generating temporary filename.~%")
        (mv :failed env$ nil state))

       ((mv okp max-index state)
        (time$ (dimacs-export cnf :filename filename)
               :msg "; SATLINK: writing ~s0: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime config.mintime))

       ((unless okp)
        (cw "SATLINK: Error writing dimacs file ~s0~%" filename)
        (mv :failed env$ nil state))

       ((acl2::fun (cleanup filename config))
        (b* (((unless (config->remove-temps config))
              nil)
             ((mv & &)
              (acl2::tshell-call (str::cat "rm " filename))))
          nil))

       (cmd (str::cat config.cmdline " " filename))
       ((mv & lines)
        (time$ (acl2::tshell-call cmd
                                  ;; Print only if :verbose t is on, and use a
                                  ;; custom printing function that skips variable
                                  ;; assignment lines
                                  :print (or (and config.verbose 'satlink-echo)
                                             (and config.timing 'satlink-echo-time))
                                  :save t)
               :msg "; SATLINK: `~s0`: ~st sec, ~sa bytes~%"
               :args (list cmd)
               :mintime config.mintime))

       ((unless (string-listp lines))
        (cw "SATLINK: Tshell somehow didn't give us a string list.~%")
        (cleanup filename config)
        (mv :failed env$ nil state))
       ((mv status env$)
        (time$ (b* ((env$ (resize-bits (1+ max-index) env$))
                    ((mv status env$) (satlink-parse-output lines env$)))
                 (mv status env$))
               :msg "; SATLINK: interpreting output: ~st sec, ~sa bytes~%"
               :mintime config.mintime))
       (lrat-proof
        (if (and (eq status :unsat) config.lrat-check)
            (b* ((lrat-proof (time$ (lrat::lrat-read-file (str::cat filename ".lrat") state)
                                    :msg "; SATLINK: read lrat file: ~st sec, ~sa bytes~%"
                                    :mintime config.mintime))
                 ((unless (config->remove-temps config)) lrat-proof)
                 ((mv & &) (acl2::tshell-call (str::cat "rm " (str::cat filename ".lrat")))))
              lrat-proof)
          nil))
       (- (and (or (eq status :sat)
                   (eq status :unsat))
               ;; Successful round trips --> invoke the extra hook.  We do this
               ;; BEFORE cleaning up so that the input file still exists.
               (satlink-extra-hook cnf filename status env$ state))))
    (cleanup filename config)
    (mv status env$ lrat-proof state)))


(defsection logical-story
  :parents (satlink)
  :short "How we logically assume that the SAT solver's claims of unsat are
correct."

  :long "<p>The whole point of Satlink is to be able to call an external SAT
solver, written in C or C++, and trust its results.  Here, we explain exactly
how we do that.</p>

<p>Our assumptions about the SAT solver will be expressed as constraints about
a new function, @('satlink-run-fn').  Informally, the idea behind this function
is that it will have the following signature:</p>

<code>
 (satlink-run-fn config formula env$) &rarr; (status env$)
</code>

<dl>

<dt>Inputs</dt>

<dd>@('config') is a @(see config-p) that says which SAT solver to run and how
to run it.</dd>

<dd>@('formula') is the @(see cnf) formula to solve.</dd>

<dd>@('env$') is @(see env$), a bit array that will be used to store the
satisfying assignment from the SAT solver, in the SAT case.</dd>

<dt>Outputs</dt>

<dd>@('status') is the answer we get back from the SAT solver; in practice it
will either be @(':sat') or @(':unsat'), or perhaps @(':failed') if we run into
some kind of gross error&mdash;for instance, perhaps the SAT solver produces
output that we weren't expecting, like \"Segmentation fault\" or
\"Killed\".</dd>

<dd>@('env$') is the updated @(see env$) bit array; in the @(':sat') case it
should contain the satisfying assignment.</dd>

<dd>@('lrat-proof') will be NIL unless @('config.lrat-check') is true.  In that
case, it is expected that the solver will write a file
\"[input-filename].lrat\" containing an LRAT proof; see
\"projects/sat/lrat/README\".</dd>

</dl>

<h3>Axiomatization</h3>

<p>We use ACL2's @(see acl2::partial-encapsulate) feature to assume that the function
satisfies certain constraints.</p>

<p>To make our story as tight as possible, we would like to assume very little
about @('satlink-run-fn').  It turns out we only need three constraints, with
the first two constraints just saying that the function returns three values:</p>

@(thm true-listp-of-satlink-run-fn)
@(thm len-of-satlink-run-fn)

<p>The final constraint is the real one.  The idea here is to express:</p>

<box><p>
   if @('satlink-run-fn') returns @(':unsat'),<br/>
   then the formula evaluates to false under every environment.
</p></box>

<p>However, we don't even need to assume that if our solver outputs an LRAT
proof that can be checked by the LRAT checker in \"projects/sat/lrat\".  So if
the configuration option @('lrat-check') is set to true, then we don't assume
this.  If @('lrat-check') is @('NIL'), then we'll just assume the solver is
correct.</p>

<p>But the quantification here isn't quite right for a rewrite rule, so
instead we assume the contrapositive:</p>

<box><p>
   if NOT(the formula evaluates to false under every environment),<br/>
   and we are not checking an LRAT proof,<br/>
   then NOT( @('satlink-run-fn') returns @(':unsat') )
</p></box>

<p>Which simplifies down to:</p>

<box><p>
   if the formula evaluates to true under any environment,<br/>
   and we are not checking an LRAT proof,<br/>
   then @('satlink-run-fn') does not return @(':unsat')
</p></box>

<p>So the real constraint looks like this:</p>

@(thm satlink-run-fn-unsat-claim)


<p>And that's it.  We don't need to assume anything about what happens in the
@(':sat') case or the case where we're checking LRAT proofs, because our
top-level @(see sat) wrapper will verify those answers.</p>")

(defun satlink-useless-clauseproc (clause)
  (list clause))

(acl2::partial-encapsulate
 (((satlink-run-fn * * env$) => (mv * env$ *)
   :formals (config formula env$)
   :guard (and (config-p config)
               (lit-list-listp formula))))
 nil ;; supporters
 (local (defun satlink-run-fn (config formula env$)
          (declare (ignore config formula)
                   (xargs :stobjs env$))
          (mv :failed env$ nil)))

 (defthm true-listp-of-satlink-run-fn
   (true-listp (satlink-run-fn config formula env$))
   :rule-classes :type-prescription)

 (defthm len-of-satlink-run-fn
   (equal (len (satlink-run-fn config formula env$)) 3))

 (defthm satlink-run-fn-unsat-claim
   (implies (and (equal (eval-formula formula arbitrary-env) 1)
                 (not (config->lrat-check config)))
            (not (equal (mv-nth 0 (satlink-run-fn config formula env$))
                        :unsat)))))

(defsection satlink-run
  :parents (logical-story)
  :short "Connection between the implementation and the logical story."

  :long "<p>In the logic, this function does nothing more than call
@('satlink-run-fn'), the constrained function that is the basis of our @(see
logical-story).</p>

<p>Under the hood, through a trust tag, we smash its definition and have it
invoke @(see satlink-run-impl), which actually calls the SAT solver.</p>"

  (defun satlink-run (config formula env$)
    "Returns (MV STATUS ENV$ LRAT-PROOF)"
    (declare (xargs :stobjs env$
                    :guard (and (config-p config)
                                (lit-list-listp formula))))
    (satlink-run-fn config formula env$)))

(defttag :satlink)

; (depends-on "top-raw.lsp")
(acl2::include-raw "top-raw.lsp")


(define sat
  :parents (satlink)
  :short "Top-level function for running a SAT solver."

  ((formula "A @(see cnf) formula to solve." lit-list-listp)
   (env$    "Environment to populate with a satisfying assignment, in the case
             of SAT.  Will be emptied, in any case.")
   &key
   ((config "Configuration for running a SAT solver." config-p)
    '*default-config*))
  :returns (mv (status "@(':sat'), @(':unsat'), or @(':failed').")
               (env$   "Satisfying assignment, in the case of @(':sat')."))

  :long "<p>This is the top-level wrapper for calling SAT.  It handles the
details of clearing out the @(see env$) and checking the SAT solver's answers
when there is a counterexample or an LRAT proof available.</p>"

  (b* ((env$ (mbe :logic (non-exec nil) :exec (resize-bits 0 env$)))
       ((when (trivial-unsat-p formula))
        (mv :unsat env$))
       ((config config) config)
       ((mv status env$ lrat-proof)
        (time$ (satlink-run config formula env$)
               :msg "; SATLINK: round trip: ~st sec, ~sa bytes.~%"
               :mintime config.mintime))
       ((when (and (eq status :unsat) config.lrat-check))
        (b* ((lrat-formula (formula-to-lrat-formula formula 1))
             (ok (time$ (lrat::lrat-refutation-p$ lrat-proof lrat-formula)
                        :msg "; SATLINK: lrat check: ~st sec, ~sa bytes.~%"
                        :mintime config.mintime))
             ((unless ok)
              (cw "SAT: Supposedly unsatisfiable, but check of LRAT proof failed!~%")
              (mv :failed env$)))
          (mv :unsat env$)))
       ((unless (eq status :sat))
        (mv status env$))
       ((when (time$ (int= 0 (eval-formula formula env$))
                     :msg "; SATLINK: verifying assignment: ~st sec, ~sa bytes~%"
                     :mintime config.mintime))
        (cw "SAT: Supposedly satisfiable, but assignment is wrong~%")
        (mv :failed env$)))
    (mv :sat env$))
  ///
  (defthm sat-normalize-env
    (implies (syntaxp (not (equal env$ ''nil)))
             (equal (sat formula env$ :config config)
                    (sat formula nil :config config))))

  (defthm sat-when-sat
    (b* (((mv status new-env$) (sat formula env$ :config config)))
      (implies (equal status :sat)
               (equal (eval-formula formula new-env$) 1))))

  (defthm sat-when-unsat
    (b* (((mv status &) (sat formula env$ :config config)))
      (implies (equal (eval-formula formula env) 1)
               (not (equal status :unsat))))
    :hints (("goal" :use ((:instance lrat::main-theorem
                           (proof (mv-nth 2 (satlink-run config formula env$)))
                           (formula (formula-to-lrat-formula formula 1)))
                          (:instance lrat::satisfiable-suff
                           (assignment (env$-to-lrat-assignment (+ 1 (max-index-formula formula)) env))
                           (formula (formula-to-lrat-formula formula 1))))
             :in-theory (e/d (trivial-unsat-p-correct)
                             (lrat::lrat-refutation-p$))))))


#||

(tshell-ensure)

(sat '((1 2)) env$)

;; This is a good check to make sure writes-okp stuff is working.
(make-event
 (b* (((mv ans env$) (sat '((1 2)) env$)))
   (mv nil `(value-triple ,ans) state env$)))

||#
