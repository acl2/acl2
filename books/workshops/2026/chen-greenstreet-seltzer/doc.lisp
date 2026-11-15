;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 26th 2017)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "centaur/sv/tutorial/support" :dir :system)
;; (include-book "examples/examples")
;; (include-book "examples/ringosc")

;; ------------------------------------------------------- ;;
;;    Documentation

(include-book "xdoc/save" :dir :system)  ;; load xdoc::save

(defxdoc Smtlink
  :parents (ACL2::projects)
  :short "Tutorial and documentation for the ACL2 book, Smtlink."
  :long "<h3>Introduction</h3>
<p>A framework for integrating external SMT solvers into ACL2 based on the
  @(see ACL2::clause-processor) and the @(tsee ACL2::computed-hints)
  mechanism.</p>

<h4>Overview</h4>
<p>@('Smtlink') is a framework for representing suitable ACL2 theorems as a SMT
(Satisfiability Modulo Theories) formula, and calling SMT solvers from within
ACL2.</p>

<p>SMT solvers combine domain-specific techniques together into a SAT
(Satisfiability) Solver and solves domain-specific satisfiability problems.
Typical domain specific procedures include procedures in integer and real,
linear and non-linear arithmetic, array theory, and uninterpreted function
theory.  Modern SMT solvers benefit from the development of both the SAT
solvers and the domain-specific techniques and have become very fast at solving
some relatively large problems.</p>

<p>In the 2018 Workshop version, we call it @('smtlink 2.0'), we make major
improvements over the initial version with respect to soundness, extensibility,
ease-of-use, and the range of types and associated theory-solvers supported.
Most theorems that one would want to prove using an SMT solver must first be
translated to use only the primitive operations supported by the SMT solver --
this translation includes function expansion and type inference.  @('Smtlink
2.0') performs this translation using sequence of steps performed by verified
clause processors and computed hints.  These steps are ensured to be sound.
The final transliteration from ACL2 to Z3's Python interface requires a trusted
clause processor.  This is a great improvement in soundness and extensibility
over the the original @('Smtlink') which was implemented as a single,
monolithic, trusted clause processor.  @('Smtlink 2.0') provides support for
@(tsee acl2::FTY), @(tsee fty::defprod), @(tsee fty::deflist), @(tsee
fty::defalist), and @(tsee fty::defoption) types by using Z3's arrays and user
defined data types.</p>

<p>@('Smtlink') can be used both in ACL2 and ACL2(r).  The macro @(see
Real/rationalp) should make one's proof portable between ACL2 and ACL2(r). It
is also compatible with both Python 2 and Python 3.</p>

<p>@('Smtlink') currently only supports <a
href='https://github.com/Z3Prover/z3/wiki'>Z3</a>.  We hope to add an interface
to include the <a href='http://smtlib.cs.uiowa.edu/'>SMT-LIB</a> in near
future.</p>

<h3>Using Smtlink</h3>
<h4>Requirements</h4>
<ul>
<li>Python 2/3 is properly installed.</li>
<li>Z3 is properly installed.
<p>One needs to build Z3 on one's own instead of using the binary release.
Also, since we are using the Python interface, please follow the \"python\"
section in the \"z3 bindings\" section in <a
href='https://github.com/Z3Prover/z3/'>README</a> of Z3.</p>
<p>I've also wrote a small piece of @(see z3-installation) document about how
to install Z3 and its Python API.</p>
<p>To check if Z3 is properly installed, run Python, which will put you in an
interactive loop. Then run:</p>
@({
  from z3 import *
  x = Real('x')
  y = Real('y')
  s = Solver()
  s.add(x + y > 5, x > 1, y > 1)
  print(s.check())
  print(s.model())
  quit()
  })
<p>One should expect some results like:</p>
@({
>>> print(s.check())
sat
>>> print(s.model())
[y = 4, x = 2]
  })
</li>
<li>ACL2 and the system books are properly installed.</li>
<li>@('Smtlink') uses Unix commands.</li>
</ul>

<h4>Build Smtlink</h4>
<ul>
<li>Setup smtlink configuration in file smtlink-config in either a user
specified directory @('$SMT_HOME') or in directory @('$HOME').  When both
environment variables are set, @('$SMT_HOME') is used. The configuration takes
below format:
@({
  smt-cmd=...
  })
<box>
<p>
<b><color rgb='#FF0000'>NOTE:</color></b>
It used to be four options, we simplified it into just one @('smt-cmd').
</p>
</box>

<p>@('smt-cmd') is the command for running Z3, which is the Python command
since we are using the Python interface.  The Z3 library is imported into Python
in the scripts written out by Smtlink like is shown in the example script in
\"Requirements\".</p></li>
<li>Certify the book top.lisp in the Smtlink directory, to bake setup into
certified books.
<p>This took about 8 mins on my 4-core mac with hyperthreading @('-j 2').</p>
<box>
<p>
<b><color rgb='#FF0000'>NOTE:</color></b>
A complete recertification of Smtlink is required if one changes the
configuration in smtlink-config.
</p>
</box>
</li>

</ul>

<h4>Load and Setup Smtlink</h4>
<p>To use @('Smtlink'), one needs to include book:</p>
@({
   (include-book \"projects/smtlink/top\" :dir :system)
  })
<p>Then one needs to enable @(tsee acl2::tshell) by doing:</p>
@({
  (value-triple (tshell-ensure))
  })
<p>@(tsee value-triple) makes sure the form @('(tshell-ensure)') can be
submitted in an event context and therefore is certifiable.</p>
<p>In order to install the computed-hint, one needs to
@(see add-default-hints).</p>
@({
  (add-default-hints '((SMT::SMT-computed-hint clause)))
})
<box>
<p>
<b><color rgb='#FF0000'>NOTE:</color></b>
The computed-hint used to be called @('SMT::SMT-process-hint'), we find this name
  doesn't represent what it does. We changed the name to
  @('SMT::SMT-computed-hint').
</p>
</box>

<p>For a detail description of how to setup and get started using @('Smtlink'),
see @(tsee tutorial) and @(tsee SMT-hint).</p>

<h3>Reference</h3>
<p>@('Smtlink') has experienced a great interface and infrastructure change
since its first publication at ACL2 workshop 2015.  But you may still find below
paper useful in understanding basics of @('Smtlink'):</p>

<p>Yan Peng and Mark R. Greenstreet. <a
href='https://arxiv.org/abs/1509.06082'>Extending ACL2 with SMT Solvers</a>In
ACL2 Workshop 2015. October 2015. EPTCS 192. Pages 61-77.</p>")


(defxdoc z3-py
  :parents (Trusted)
  :short "The Z3 python interface related books."
  :long "<h3>Introduction</h3>")

(defxdoc Trusted
  :parents (Developer)
  :short "Trusted part of Smtlink."
  :long "<h3>Introduction</h3>")

(defxdoc Verified
  :parents (Developer)
  :short "Verified part of Smtlink"
  :long "<h3>Introduction</h3>")

(defxdoc Developer
  :parents (Smtlink)
  :short "The developer's reference to Smtlink."
  :long "<h3>Introduction</h3>")

(sv::deftutorial Tutorial
  :parents (Smtlink)
  :short "A tutorial to walk you through how to use Smtlink to prove ACL2 theorems."
  :long "<h3>Prerequisites</h3>
<p>Following instructions in :doc @(see Smtlink), one should have setup the
  configuration in file smtlink-config and have certified the Smtlink book
  afterwards to bake in the configurations.</p>
<p>Then the header of the ACL2 script should look like:</p>
@({
  (in-package \"ACL2\")
  (include-book \"projects/smtlink/top\" :dir :system)
  (tshell-ensure)
})
<p>Smtlink uses a sequence of computed hints and clause processors to perform
different stages.  In order to install the computed-hint, one needs to
@(see add-default-hints).</p>
@({
  (add-default-hints '((SMT::SMT-computed-hint clause)))
})
<box>
<p>
<b><color rgb='#FF0000'>NOTE:</color></b>
The computed-hint used to be called @('SMT::SMT-process-hint'), we find this name
  doesn't represent what it does. We changed the name to
  @('SMT::SMT-computed-hint').
</p>
</box>

<p>The rest of this document contains four pieces of arithmetic examples to
show what one can do with @('Smtlink') and how.  The first one shows a regular
example, the second one is proved using the extended version called
smtlink-custom, the third one is a theorem that does not pass Smtlink, and the
fourth is a list of examples for @('FTY') types.</p>"
  )

(defxdoc SMT-hint
  :parents (Smtlink SMT-hint-interface)
  :short "Describes the hints interface for Smtlink."
  :long "
@({Examples:

:smtlink(-custom)
(:functions ((my-expt :formals ((r rationalp)
                                (i rationalp))
                      :returns ((ex rationalp :hints (:in-theory (enable my-expt))))
                      :level 0)
             ...)
 :hypotheses (((< (my-expt z n) (my-expt z m))
               :hints (:use ((:instance hypo1-hint (x x)))))
              ((< 0 (expt z m)))
              ((< 0 (expt z n)))
              ...)
 :fty (acl2::integer-list)
 :main-hint (:use ((:instance main-hint (n n) (x x))))
 :int-to-rat t
 :smt-fname \"my-smt-problem.lisp\"
 :smt-dir \"/home/tmp\"
 :rm-file t)

})

<p>@(':smtlink') is a customized argument option to @(see acl2::hints).
 @('smtlink-custom') is used when one wants to use the customized version of
 Smtlink.  The next argument to @(':smtlink') we call @(see smt-hint).  These
 are the hints one wants to provide to Smtlink so that it can figure out the
 proof easily.  Let's take a look at each one of them:</p>

 <dl>

 <dt>@(':functions')</dt><p/>

 <dd><p>@('functions') are for dealing with recursive functions.  Smtlink
 translate a basic set of ACL2 functions (See @(see smt-basics)) into SMT
 functions.  Non-recursive functions defined with the basic functions are
 automatically expanded in the verified clause processor.  Recursive functions
 can be specified to expand to a given level.  The innermost function call is
 translated into an uninterpreted function.  When level equals 0, no expansion
 is done.</p>

 <p>The argument to @(':functions') is a list of functions.  For each of the
 function, for example,</p>

 @({
(my-expt :formals ((r rationalp)
                   (i rationalp))
         :returns ((ex rationalp :hints (:in-theory (enable my-expt))))
         :level 0)
})

 <p>@('my-expt') is function that has already been defined.  It has two formals,
 named as @('r') with type @('rationalp') and @('i') with type @('rationalp').
 It returns an argument called @('ex') with type @('rationalp').  Return types
 of functions are proved as one of the clauses returned by the verified clause
 processor.  One can give hints to the proof.  The hints uses a similar form as
 in @(see acl2::hints).  The only difference is that the hints will only go to a
 specific subgoal, therefore no goal specifier is needed.  @('level') is the
 expansion level.</p>
 </dd>

 <dt>@(':hypotheses')</dt><p/>

 <dd><p>@(':hypotheses') are \"facts\" that the user believes to be true and
 should help with the proof.  The facts will be returned as auxiliary clauses
 to be proved from the verified clause processor.  One can provide hints for
 proving any of the hypotheses.  It follows the format of the @(see acl2::hints),
 except that no goal specifier is needed.</p></dd>

 <dt>@(':fty')</dt><p/>

 <dd><p>@(':fty') specifies a list of FTY types to be used in this
 theorem</p></dd>

 <dt>@(':main-hint')</dt><p/>

 <dd><p>@(':main-hint') provides a hint to the main returned auxiliary theorem.
 This theorem proves the expanded clause implies the original clause.  The
 format of the hint follows that of the @(see acl2::hints), except that no goal
 specifier is needed.</p></dd>

 <dt>@(':int-to-rat')</dt><p/>

 <dd><p>Z3 has a limited solver for mixed Integer and Real number theories, but
 have a better solver for solving pure Real number problems.  Sometimes one
 might want to try raising all Integers to Reals to prove a theorem.</p></dd>

 <dt>@(':smt-fname')</dt><p/>

 <dd><p>@(':smt-fname') provides a user specified file name for the generated
 Z3 problem, instead of the default one.</p></dd>

 <dt>@(':smt-dir')</dt><p/>

 <dd><p>@(':smt-dir') provides a user specified directory for the generated Z3
 file, instead of the default one in /tmp.</p></dd>

 <dt>@(':rm-file')</dt><p/>

 <dd><p>@(':rm-file') specified whether one wants the generated Z3 file to be
 preserved, in default case, it is removed.</p></dd>

 </dl>
")

(defxdoc Status
  :parents (Smtlink)
  :short "A discussion of what theories are supported in Smtlink and what we
  intend to support in the future."
  :long "<h3>SMT solvers</h3>
<p>Currently only Z3 is supported.</p>

<h3>Theories</h3>
<p>Currently @('Smtlink') supports:</p>

<ul>
<li><b>Basic types:</b> @(tsee booleanp), @(tsee integerp), @(tsee real),
@(tsee rationalp), @(tsee real/rationalp) and @(tsee symbolp)</li>
<li><b>FTY types generated using:</b> @(tsee defprod), @(tsee deflist),
@(tsee defalist) and @(tsee defoption)</li>
<li><b>Basic functions:</b> @(tsee binary-+), @(tsee binary-*), @(tsee
unary-/), @(tsee unary--), @(tsee equal), @(tsee <), @(tsee implies), @(tsee
if), @(tsee not), and @(tsee lambda)</li>
<li><b>Functions associated with FTY types:</b>
<ul>
<li><b>defprod:</b> recognizer, fixer, constructor, and field accessors.</li>
<li><b>deflist:</b> recognizer, fixer, @(tsee cons), @(tsee car), @(tsee cdr)
and @(tsee consp).</li>
<li><b>defalist:</b> recognizer, fixer, @(tsee acons), and @(tsee
assoc-equal)</li>
<li><b>defoption:</b> recognizer, fixer, constructor, and field-accessor.</li>
</ul>
</li>
</ul>

<h3>Wishlist</h3>
<ul>
<li>Using @(tsee acl2::meta-extract) capability introduced in year 2017 Workshop for
fully verifying several of the verified clause-processors in the architecture.
This will improve performance.</li>
<li>Develop type inference engine to remove the burden on the user for
providing type information.</li>
<li>Generate ACL2 evaluatable counter-examples.</li>
<li>Adding support for SMT-LIB.</li>
<li>Build a computed hint for Smtlink so that it's automatically fired on goals
that seems likely to be solved by Smtlink, possibly recognizing induction
steps.</li>
<li>Do proof reconstruction for the trusted clause-processor so that ACL2
doesn't have to trust an external procedure.</li>
</ul>"
  )

(defxdoc Z3-installation
  :parents (Smtlink)
  :short "How to install Z3"
  :long "<h3>How I installed Z3</h3>
<p>In case you find the Z3 README page confusing, here's how I installed Z3.
  One can adjust the process to one's own needs.  The version of Z3 I used is
  @('Z3 version 4.5.0 - 64 bit'), and the version of Python I used is @('Python
  2.7.15').</p>
<ul>
<li>Download the current stable release from Z3 <a
  href='https://github.com/Z3Prover/z3/releases'>releases</a>

<p>We want to download the source code and compile it by ourselves. It might be
  doable to use the binary releases by setting up @('PYTHONPATH') and
  @('DYLD_LIBRARY_PATH') (on macos), but I haven't tried it and there's no
  instruction in Z3 telling us if that's the way to use it.</p>
</li>
<li>Assume we are in the release directory, do:
@({
python scripts/mk_make.py --prefix=$HOME/usr --python --pypkgdir=$HOME/usr/lib/python-2.7/site-packages
})
<p>I want to install it in my @('$HOME/usr') directory prefix, but you can
  replace that part of the path with your conventional path. Note that Z3
  restricts @('--prefix') to be the prefix of @('--pypkgdir'). Also,
  @('$HOME/usr') does not need to exist in order to follow these steps; that
  directory and subdirectories will be created as necessary.</p>
</li>
<li>Now make the C/C++ libraries, do:
@({
cd build; make
})
</li>
<li>Now do the installation in places specified in @('--prefix'):
@({
make install
})
<p>Now if one takes a look at @('$HOME/usr'), one will see in @('$HOME/usr/bin'),
we have the @('z3') executable, in @('$HOME/usr/include') we have all the z3
C++ header files, in @('$HOME/usr/lib') we have @('libz3.dylib') and in
@('$HOME/usr/lib/python-2.7/site-packages') we have all the z3 Python API
files.</p>
<p>Because we are using a user specified prefix, the command line produces the
message:</p>
@({
Z3Py was installed at /.../usr/lib/python-2.7/site-packages, make sure
this directory is in your PYTHONPATH environment variable. @echo Z3 was
successfully installed.
})
</li>
<li>So the last step is to add this path to PYTHONPATH. Adding this path to
  existing PYTHONPATH:
@({
export PYTHONPATH=$HOME/usr/lib/python-2.7/site-packages:$PYTHONPATH
})
If PYTHONPATH is undefined, do:
@({
export PYTHONPATH=$HOME/usr/lib/python-2.7/site-packages
})
</li>
<li>Now one should be able to import z3 into Python.
Run Python, which will put you in an interactive loop.
@({
  from z3 import *
  x = Real('x')
  y = Real('y')
  s = Solver()
  s.add(x + y > 5, x > 1, y > 1)
  print(s.check())
  print(s.model())
  quit()
  })
<p>One should expect some results like:</p>
@({
>>> print(s.check())
sat
>>> print(s.model())
[y = 4, x = 2]
  })
<p>This example asks for a satisfying assignment to the problem:
@($x + y > 5$), @($x > 1$) and @($y > 1$). It should be easy to check the
result.</p>
</li>
</ul>

<h3>Additional Notes</h3>
<p>
The instructions above explain how to install Z3 in the user's home directory.
</p>
<p>
Another option is to install Z3 in a machine-wide location.
The following instructions worked on at least two Mac machines:
</p>
<ol>
<li>
Download the latest stable release of Z3 as explained in the instructions above.
Unzip it: let @('<dir>') be the name of the resulting directory.
</li>
<li>
Move the directory to a machine-wide location, e.g.:
@({
  sudo mv <dir> /usr/local/
})
The @('sudo') is needed because @('/usr/local') is typically owned by @('root'),
and it is not good practice to change the ownership of @('/usr/local')
to a non-@('root') user.
There is no need to change the ownership of @('/usr/local/<dir>') to @('root').
</li>
<li>
Prepare to build Z3 with the Python bindings:
@({
  cd /usr/local/<dir>
  python scripts/mk_make.py --python
})
Note that no @('--prefix') or @('--pypkgdir') options are used here,
unlike the instructions given above.
This may give a warning related to Z3's restriction,
mentioned in the instructions above,
that @('--prefix') must be a prefix of @('--pypkgdir');
despite this warning, things worked on at least two Mac machines.
On Mac, ensuring that this restriction is satisfied is tricky because
Python packages are normally installed in places like
@('/Library/Frameworks/Python.framework/Versions/3.6/...') or
@('/System/Library/Frameworks/Python.framework/Versions/2.7/...'),
but prefixes of these locations normally do not hold
the @('bin'), @('lib'), and @('include') directories
that the Z3 installation creates (see below).
</li>
<li>
Build Z3:
@({
  cd build
  make
})
This may take a while to complete.
</li>
<li>
Install Z3:
@({
  sudo make install
})
The @('sudo') is needed because this will write into
@('/usr/local/bin'), @('/usr/local/lib'), and @('/usr/local/include'),
which are typically owned by @('root') (see comments above about this).
</li>
<li>
Run the Z3 example in Python described in the instructions above,
to confirm that the installation was successful.
</li>
</ol>

<h3>Allow the Build System to Find Z3</h3>
<p>To make sure ACL2's build system can find Z3, Z3 should be installed in
one's path.  There are two ways to achieve this:</p>
<ul>
<li>
Add the path to where Z3 is installed into one's path.  For example,
@({
export PATH=/path to z3 executable/:$PATH
})
</li>
<li>
Another way of achieving this purpose is to create the following bash script
called ``z3'' and put it in one's path:
@({
#!/bin/bash
/path to z3 executable/z3 \"$@\"
})
In some systems, after creating that script, one needs to run ``rehash'' in the
shell.
</li>
</ul>
")

;; (xdoc::save "./manual" :redef-okp t)  ;; write the manual
