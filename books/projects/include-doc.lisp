; projects/include-doc.lisp
;
; Jared Davis pulled together these documentation topics from README files and
; similar from within each project.  See individual topics for copyright
; information.

(in-package "ACL2")
(defmacro include-projects-doc ()
  '(progn
     (include-book "build/ifdef" :dir :system)
     (include-book "xdoc/top" :dir :system)
     (include-book "milawa/doc")
     (include-book "regex/regex-ui")
     (include-book "leftist-trees/top")
     (include-book "quadratic-reciprocity/euler")
     (include-book "sidekick/server")
     (include-book "x86isa/doc")
     (include-book "farray/farray")
     (include-book "sat/proof-checker-itp13/top")
     (include-book "sat/proof-checker-array/top")
     (include-book "sat/dimacs-reader/reader")
     (include-book "irv/top")
     (include-book "rp-rewriter/top")
     (include-book "rp-rewriter/lib/mult/doc")
     (include-book "rp-rewriter/lib/mult2/doc")
     
     (ifdef "OS_HAS_SMTLINK"
            (include-book "smtlink/doc")
            :endif)



     (defxdoc projects
       :parents (top)
       :short "The @('projects') directory of the Community Books contains a variety
of projects that have been carried out with @(see acl2).")

     (defxdoc paco
       :parents (projects)
       :short "Paco is a cut-down, simplified ACL2-like theorem prover for
pedagogical use."

       :long "<p>The ACL2 source files for paco are located in @('projects/paco').
These files can be built by running, e.g., @('make paco') from the @('books/')
directory.  After building these source files, to run paco on some examples,
you may go to the directory @('projects/paco/books') and run:</p>

@({
   (ld \"proveall.lsp\" :ld-pre-eval-print t)
})

<p>For copyright and license information, see
@('books/projects/paco/LICENSE').</p>")

     (defxdoc taspi
       :parents (projects)
       :short "Texas Analysis of Symbolic Phylogenetic Information (TASPI) is
specialized code for modeling collections of phylogenetic trees and performing
a few manipulations such as consensus analysis."

       :long "<p>The directory @('projects/taspi') contains the TASPI code.  These
ACL2 books may be built by running, e.g., @('make taspi') from the @('books/')
directory.  Please note: TASPI relies on a version of ACL2 that includes HONS
for its speed and memory requirement claims.</p>

<p>For further details, see:</p>

<ul>

<li>Serita Nelesen. <a
href='https://repositories.lib.utexas.edu/bitstream/handle/2152/ETD-UT-2009-12-529/NELESEN-DISSERTATION.pdf'>Improved Methods for Phylogenetics</a>.
PhD Dissertation, The University of Texas at Austin, Dec 2009.</li>

<li>Warren A. Hunt, Jr. and Serita M. Nelesen.  <a
href='http://www.ccs.neu.edu/home/pete/acl206/papers/hunt.pdf'>Phylogenetic
Trees in ACL2</a>.  Proceedings of the 6th International Workshop on the ACL2
Theorem Prover and its Applications, Seattle, WA, August 15-16, 2006.</li>

<li>Robert S. Boyer, Warren A. Hunt Jr and Serita M. Nelesen. <a
href='http://dx.doi.org/10.1007/11557067_29'>A Compressed Format for
Collections of Phylogenetic Trees and Improved Consensus Performance</a>. In
Algorithms in Bioinformatics: 5th International Workshop, WABI 2005, LNCS 3692,
pages 353-364, Springer Berlin / Heidelberg, 2005.</li>

</ul>


<h3>Copyright Information</h3>

<p>TASPI &mdash; Texas Analysis of Symbolic Phylogenetic Information<br/>
Copyright (C) 2011 Serita Nelesen, Robert Boyer and Warren A. Hunt, Jr.</p>

<p>This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the Free
Software Foundation; either version 2 of the License, or (at your option) any
later version.</p>

<p>This program is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.</p>

<p>You should have received a copy of the GNU General Public License along with
this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
Street, Fifth Floor, Boston, MA 02110-1301, USA.</p>")


     (defxdoc jfkr
       :parents (projects)
       :short "An executable ACL2 model of the JFKr key establishment protocol for
establishing a shared encryption key between two participants."

       :long "<p>The directory @('projects/security/jfkr') contains the ACL2 source
files for the JFKr project.  These ACL2 books may be built by running, e.g.,
@(' make jfkr ') from the @('books/') directory.  For details on this project,
see the following ACL2 workshop paper:</p>

<p>David L. Rager.  <a href='http://dx.doi.org/10.1145/1637837.1637854'>An
executable model for security protocol JFKr</a>.  Eighth International Workshop
on the ACL2 Theorem Prover and its Applications.  ACM Press.  Pages 106-109.
May, 2009.</p>

<h3>Copyright Information</h3>

<p>JFKr Model<br/>
Copyright (C) 2008 University of Texas at Austin</p>

<p>This program is free software; you can redistribute it and/or modify it
under the terms of Version 2 of the GNU General Public License as published by
the Free Software Foundation.</p>

<p>This program is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.</p>

<p>You should have received a copy of the GNU General Public License along with
this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
Street, Fifth Floor, Boston, MA 02110-1301, USA.</p>")



     (defxdoc des
       :parents (projects)
       :short "An implementation of the historically significant <a
href='http://en.wikipedia.org/wiki/Data_Encryption_Standard'>Data Encription
Standard</a>, an algorithm for encrypting data."

       :long "<p>The directory @('projects/security/des') contains the ACL2 source
files for the DES project.  These ACL2 books may be built by running, e.g.,
@('make des') from the @('books/') directory.  Please note that this DES
implementation relies on a version of ACL2 that includes HONS.</p>

<h3>Copyright Information</h3>

<p>Copyright (c) 2012, Soumava Ghosh<br/>
All rights reserved.</p>

<p>Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:</p>

<ul>

<li>Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.</li>

<li>Redistributions in binary form must reproduce the above copyright notice,
this list of conditions and the following disclaimer in the documentation
and/or other materials provided with the distribution.</li>

<li>Neither the name of the The University of Texas at Austin nor the names of
its contributors may be used to endorse or promote products derived from this
software without specific prior written permission.</li>

</ul>

<p>THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS 'AS IS'
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL SOUMAVA GHOSH BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.</p>")



     (defxdoc sha-2
       :parents (projects)
       :short "An implementation of the <a
href='http://en.wikipedia.org/wiki/SHA-2'>SHA-2</a> cryptographic hash
function."

       :long "<p>The directory @('projects/security/sha-2') contains the ACL2 source
files for the SHA-2 project.  These ACL2 books may be built by running, e.g.,
@('make sha-2') from the @('books/') directory.</p>

<h3>Copyright Information</h3>

<p>Copyright (c) 2012, Soumava Ghosh<br/>
All rights reserved.</p>

<p>Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:</p>

<ul>

<li>Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.</li>

<li>Redistributions in binary form must reproduce the above copyright notice,
this list of conditions and the following disclaimer in the documentation
and/or other materials provided with the distribution.</li>

<li>Neither the name of the The University of Texas at Austin nor the names of
its contributors may be used to endorse or promote products derived from this
software without specific prior written permission.</li>

</ul>

<p>THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS 'AS IS'
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL SOUMAVA GHOSH BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.</p>")


     (defxdoc wp-gen
       :parents (projects)
       :short "An algorithm for generating weakest preconditions as mutually
recursive functions."

       :long "<p>The directory @('projects/security/wp-gen') contains the ACL2
source files for the WP-GEN project.  These ACL2 books may be built by running,
e.g., @('make wp-gen') from the @('books/') directory.</p>

<h3>Overview</h3>

<p>This book generates weakest precondition predicates, which are admitted
as (possibly mutually recursive) ACL2 functions as described in the paper <i>A
Weakest Precondition Model for Assembly Language Programs</i> by Bill Legato,
dated January 28, 2003.</p>

<p>The input program is given in a variation of Legato's format for assembly
language programs. In this format each node of the program (where node roughly
corresponds to program line) is represetned as a sequential substitution
defining updates to state. Presently, state variables are inferred from the
given substitutions and predicates and all functions are given as functions of
full state with @(see irrelevant-formals) ignored.</p>

<p>No particular program language is required. The right hand side of a
substitution can be any function defined in the current ACL2 logical world,
although we typically think of these operations as being low-level or
primitive. Many of the examples provided with the book use pcode operations,
for which a partial semantics has been provided in
@('examples/pcode.lisp').</p>

<h3>General Form</h3>

@({ (run-wp main) })

<p>Here main is the program to be analyzed, in the format as specified below in
the section <i>Program Format</i>.  (Also, see examples directory for some
sample programs).</p>

<p>A user of this book will generally want to specify one or more of the
following options.</p>

<ul>

<li>@(':prefix') - a prefix for the generated function names, which is appended
to the node label when the WP for the node is generated. This is generally
useful for providing meaningful function names and for avoiding function naming
conflicts. If no prefix is specified, the default prefix for each function is
\"wp-\".</li>

<li>@(':count-var') - a count variable to be decremented by the substitution at
each node. This allows ACL2 to automatically calculate a measure for
the (possibly) mutually recursive WP definitions. If the count
variable is not unique from the state variables in main, run-wp will
generate an error.</li>

<li>@(':prog-mode') - Default value is nil. If prog-mode is set to t the WP
functions are defined in prog-mode, which allows ACL2 to skip proofs.</li>

<li>@(':ccg') - Default value is nil. If the ccg books are available and
included in the current ACL2 environment then setting :ccg to t will attempt to
use CCG analysis to automatically calculate a measure.</li>

<li>@(':mutrec') - Default value is t. Uses a call tree analysis to determine
which WP functions are mutually recursive, and defines those in a
mutual-recursion form. The rest are defined as individual defuns. This should
generally be on (unless it is acting buggy, in which case contact the author)
as bogus mutual recursions can make ACL2 proofs more difficult.</li>

</ul>


<h3>Program Format</h3>

<p>A program consists of a list of nodes in the following format.</p>

@({
 (:node :label    idx
        :pre      annot-pre
        :subst    sub
        :branches ((pred1 . idx1) ... (predn . idxn))
        :post     annot-post)
})

<p>where:</p>

<ul>

<li>@('idx') is a unique node label (possibly corresponding to a program line
number, e.g. l_1, l_2,...)</li>

<li>@('annot-pre') is a predicate on state prior to execution of the
line (i.e., before the given substituation on program state is applied)</li>

<li>@('sub') is a substitution representing execution as an alist</li>

<li>@('branches') specifies program control using @('(pred . idx)') pairs,
where pred is a condition on state and idx is the label of a node</li>

<li>@('annot-post') is a predicate on state after execution of the line</li>

</ul>

<h3>Miscellany</h3>

<p>To generate a list of WP functions without admitting them, use
run-wp-list:</p>

@({
 (run-wp-list main prefix count-var mutrec prog-mode)
})

<p>e.g.</p>

@({
 (include-book \"wp-gen\")
 (ld \"examples/new-program.lisp\")
 (run-wp-list (@ new-prog) 'wp-new1 'count t nil)
})

<p>Generates:</p>

@({
 (MUT-REC (DEFUN WP-NEW1-L_1 (U V W COUNT)
            (DECLARE (XARGS :MEASURE (ACL2-COUNT COUNT)))
            (IF (ZP COUNT)
                NIL
                (WP-NEW1-L_2 U (INT_XOR U 12345 32)
                             W (- COUNT 1))))
          (DEFUN WP-NEW1-L_2 (U V W COUNT)
            (DECLARE (XARGS :MEASURE (ACL2-COUNT COUNT)))
            (IF (ZP COUNT)
                NIL
                (WP-NEW1-L_3 U V (INT_ADD V 2345345299 32)
                             (- COUNT 1))))
          (DEFUN WP-NEW1-L_3 (U V W COUNT)
            (DECLARE (XARGS :MEASURE (ACL2-COUNT COUNT)))
            (IF (ZP COUNT)
                NIL
                (OR (AND (NOT (= (INT_EQUAL W 8281919193 32) 1))
                         (WP-NEW1-L_END U V W (- COUNT 1)))
                    (AND (= (INT_EQUAL W 8281919193 32) 1)
                         (WP-NEW1-L_BAD U V W (- COUNT 1))))))
          (DEFUN WP-NEW1-L_BAD (U V W COUNT)
            (DECLARE (XARGS :MEASURE (ACL2-COUNT COUNT)))
            (IF (ZP COUNT) NIL T))
          (DEFUN WP-NEW1-L_END (U V W COUNT)
            (DECLARE (XARGS :MEASURE (ACL2-COUNT COUNT)))
            (IF (ZP COUNT) NIL NIL)))
})

<p>Note: This form will generate an error from ACL2 as given, because it
contains irrelevant formals.</p>

<p>Please direct questions/comments/bugs to Sarah Weissman (<a
href='mailto:seweissman@gmail.com'>seweissman@gmail.com</a>).</p>


<h3>Copyright Information</h3>

<p>Except where otherwise specified this is a work of the U.S. Government and
is not subject to copyright protection in the United States. Foreign copyrights
may apply.</p>

<p>This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the Free
Software Foundation; either version 2 of the License, or (at your option) any
later version.</p>

<p>This program is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.</p>

<p>You should have received a copy of the GNU General Public License along with
this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
Street, Fifth Floor, Boston, MA 02110-1301, USA.</p>")



     (defxdoc concurrent-programs
       :parents (projects)
       :short "ACL2 proofs establishing the fairness of the Bakery Algorithm and the
coherence of the German Cache Protocol.")


     (defxdoc german-protocol
       :parents (concurrent-programs)
       :short "An ACL2 proof of coherence of the German Cache Protocol.  The
protocol is translated directly into ACL2 from the murphy code provided in
ccp.m.  The proof involves formalizing coherence and strengthening the property
into an inductive invariant."

       :long "<p>The directory @('projects/concurrent-programs/german-protocol')
contains the ACL2 source files for the German Protocol proof by Sandip Ray.
These ACL2 books may be built by running, e.g., @('make concurrent-programs')
from the @('books/') directory.</p>

<p>This set of books define an invariant that is strong enough to verify the
coherence of the German Cache Protocol.  The proof shows how to come up with a
sufficient inductive invariant by iterative strengthening starting from the
desired base property.  The proof also demonstrates how to define invariant
predicates for multiprocess systems both using quantification over process
indices and recursive functions, thus providing a tutorial demonstration of how
to reason about concurrent protocols.</p>

<h3>Background and Description</h3>

<p>Anna Slobodova gave this problem to the author when she was looking for
doing cache protocol proofs with ACL2.  The key is that some predicates
involved, especially the key coherence property, could be naturally stated as
quantified formulas, and the question was how we could use the standard
quantification approaches together with (possibly) recursive functions to
derive a proof in the way the human would do.</p>

<p>I looked at the protocol and decided to do a proof on my own of the protocol
in ACL2.  Previously a similar proof was done in ACL2 via predicate
abstraction, and this proof was primarily intended to show how predicate
abstraction could save labor over a standard ACL2 proof.  However, the ACL2
proof itself was not devoid of interest, since it showed how one typically
iterates over a partial invariant to define a concrete inductive invariant for
a protocol-level system.  The proof did spring some surprises, for instance as
documented in the definition of some fragments of the invariant required in the
proof.</p>

<p>However, the chief contribution of the proof is to provide a tutorial
introduction to coming up with an inductive invariant for a complicated
multiprocess protocol.  Towards this end, substantial on-the-fly commentary of
the proof is provided in the form of comments, documenting the thought process
involved in the proof.</p>

<p>For questions and concerns about these books, contact
@('sandip@cs.utexas.edu').</p>

<h3>Copyright Information</h3>

<p>An ACL2 Proof of Coherence of the German Protocol<br/>
Copyright (C) 2006 Sandip Ray</p>

<p>This program is free software; you can redistribute it and/ormodify it under
the terms of the GNU General Public Licenseas published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version. This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.You should have received a copy of the GNU General Public License along
with this program; if not, write to the Free Software Foundation, Inc., 51
Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.</p>")


     (defxdoc bakery-algorithm
       :parents (concurrent-programs)
       :short "This set of books shows how one can use stuttering trace containment
with fairness constraints to verify concurrent protocols.  We apply the method
here to prove the correctness of an implementation of the Bakery algorithm.
The implementation is interesting in the sense that it depends critically on
fair selection of processes to ensure absence of deadlock.  We show how the
requisite notions can be formalized as generic theories and used in the proof
of refinements."

       :long "<p>The directory @('projects/concurrent-programs/bakery') contains the
ACL2 source files for the Bakery Algorithm proof by Sandip Ray.  These ACL2
books may be built by running, e.g., @('make concurrent-programs') from the
@('books/') directory.</p>

<p>This set of books shows how the notion of stuttering trace containment can
be used with a formalization of fairness effectively to verify concurrent
protocols via single-step theorems.  We consider an implementation of the
Bakery algorithm, which is a well-known mutual exclusion protocol from the
literature.  The implementation makes critical use of fairness assumptions to
ensure progress.  Fairness is formalized by encapsulating the appropriate
notion of fair environments in ACL2.  The result is a proof that the
implementation is a refinement up to fairness of a simple atomic mutex
protocol.</p>

<h3>Background</h3>

<p>This work was done by the author in 2000 following up the ideas of Manolios,
Namjoshi and Sumners on well-founded bisimulations (WEBs).  The verification
was inspired by a WEB proof done by Sumners to verify a concurrent deque
implementation.  To follow up that work, this work investigates how fairness
constraints can be used together with refinement proofs and strives to
determine an effective, formal, and usable notion of fairness.  The notion we
develop here is a version of what is known in the literature as weak fairness.
We show how that notion is sufficient and useful for verifying the
protocol.</p>

<h3>History and Acknowledgements</h3>

<p>This set of books represents the author's first non-trivial proof (and
research) project with ACL2.  The proof was first done in 2000-01 using ACL2
versions 2.5 and 2.6.  Rob Sumners helped significantly in this work, and
contributed a version of the records book together with an early version of
fairness.lisp.  The notion of fairness was then refined by Sumners and the
results reported in a paper in ACL2 2003.  The work also led to the
understanding of the essence and difficulty of invariant proofs for concurrent
programs, which eventually led to the investigation of the use of predicate
abstraction to automate the process.</p>

<p>In addition to the technical interest of using refinements with fairness,
the books should also be interesting just from the perspective of proof
development in ACL2 by new users.  The proof was embarked on when the author
was a novice ACL2 user, having done no more than some of the exercises in ACL2.
So the implementors of ACL2 looking at how a novice works on a reasonably large
proof project might have an understanding of how to make ACL2 more palatable to
such users.  The proof scripts are provided essentially the way the author
created them on the first shot, with little extra massaging (other than a few
things to make the proofs work with the current version of ACL2).  [The reason
for the latter is of course the perpetual disinclination of the author to look
at successful proofs.]</p>

<p>The author is thankful to Rob Sumners for significant advice and help with
ACL2.</p>

<p>For questions and concerns about these books, contact
sandip@cs.utexas.edu.</p>

<h3>Copyright Information</h3>

<p>A Verification of the Bakery Algorithm<br/>
Copyright (C) 2006 Sandip Ray</p>

<p>Contains several key contributions by Rob Sumners, in particular a version
of the records book and a specific formalization of fairness.</p>

<p>This program is free software; you can redistribute it and/ormodify it under
the terms of the GNU General Public Licenseas published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version. This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.You should have received a copy of the GNU General Public License along
with this program; if not, write to the Free Software Foundation, Inc., 51
Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.</p>")


     (defxdoc equational
       :parents (projects)
       :short "A modest resolution/paramodulation/factoring/merging prover written
in the <a href='http://www.mcs.anl.gov/research/projects/AR/'>Argonne</a> style
with Set-Of-Support, pick-given-ratio, mild term weighting, etc."

       :long "<p>The directory @('projects/equational') contains the ACL2 source
files for the Utrecht-Texas Equational Prover v0-0 by Grant O. Passmore.  These
ACL2 books may be built by running, e.g., @('make equational') from the
@('books/') directory.</p>

<h3>Copyright Information</h3>

<p>The Utrecht-Texas Equational Prover<br/>
Copyright (C) 2006 Grant Olney Passmore (grant@math.utexas.edu)</p>

<p>This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the Free
Software Foundation; either version 2 of the License, or (at your option) any
later version.</p>

<p>This program is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.</p>

<p>You should have received a copy of the GNU General Public License along with
this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
Street, Fifth Floor, Boston, MA 02110-1301, USA.</p>")


     #+skip
; This topic is already documented in projects/leftist-trees/leftist-tree-defuns.lisp.
     (defxdoc leftist-trees
       :parents (projects)
       :short "An implementation of leftist trees as described in <a
href='http://www.cambridge.org/us/academic/subjects/computer-science/programming-languages-and-applied-logic/purely-functional-data-structures'>Purely
Functional Data Structures</a>, Chris Okasaki, Cambridge University Press 1999."

       :long "<p>The directory @('projects/leftist-trees') contains the ACL2 source
files for the Leftist Trees implementation by Ben Selfridge.  These ACL2 books
may be built by running, e.g., @('make leftist-trees') from the @('books/')
directory.</p>

<p>Leftist trees are an efficient implementation of binary heaps well-suited to
a functional language.  In this book we provide an implementation of the
leftist heap data structure and its basic operations, along with some basic
theorems regarding invariance of those operations, the rank vs. the size of the
tree, and the correctness of the associated heapsort algorithm.  We prove that
heapsort is correct and equivalent to the isort algorithm provided in the
\"sorting\" book.</p>

<h3>Copyright Information</h3>

<p>Leftist Trees Library for ACL2<br/>
Copyright (C) 2012 Ben Selfridge</p>

<p>This program is free software; you can redistribute it and/or modify it
under the terms of Version 2 of the GNU General Public License as published by
the Free Software Foundation.</p>

<p>This program is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.</p>

<p>You should have received a copy of the GNU General Public License along with
this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
Street, Fifth Floor, Boston, MA 02110-1301, USA.</p>")

     (defxdoc legacy-defrstobj
       :parents (projects)
       :short "A predecessor of the @(see defrstobj) library that wasn't based on
abstract stobjs."

       :long "<p>The directory @('projects/legacy-defrstobj') contains the ACL2
source files for the original version of the @(see defrstobj) library.  These
ACL2 books may be built by running, e.g., @('make legacy-defrstobj') from the
@('books/') directory.</p>

<p>This legacy version of record-like stobjs was written by Jared Davis before
ACL2 supported abstract stobjs.  As a result, many tricks and twists are needed
to effectively hide the true nature of the stobj and to be able to treat it
like a record.</p>

<p>The legacy version isn't bad&mdash;we used this version of rstobjs for our
microcode model at Centaur Technology for a couple of years.  But we eventually
became irritated with how long it took to define rstobjs with many fields (it's
quadratic in the number of fields).  It's likely that a sufficiently motivated
person could speed this up, and we considered a way of doing so.</p>

<p>But ultimately, we decided that with abstract stobjs, we could reimplement
defrstobj in a much simpler way.  The new approach, implemented by Sol Swords,
avoids this quadratic cost, and also has a couple of other nice features.  For
instance:</p>

<ul>

<li>You don't need to \"good stobj\" predicate in your guards, because abstract
stobjs basically give you that for free;</li>

<li>You can use the record library's @('s') and @('g') functions directly,
instead of needing \"equivalent\", stobj-specific functions.</li>

</ul>

<p>So today there is little reason to use the legacy version.  Use the new,
more modern @(see defrstobj) instead!</p>

<p>Rather than delete the original version, we decided to put it into the
@('projects') directory.  This is partly for posterity, but mostly:</p>

<ul>

<li>For pedagogical value.  The project's <b>groundwork</b> directory notably
works through several demos, uncovering along the way the tricks that we need
to support progressively more complicated stobjs as records.  This may be of
interest to anyone who is interested in doing crazy things to avoid
hypotheses.</li>

<li>For regression-testing value.  This is a very elaborate use of stobjs,
non-executablility, and MBE tricks, and may be a good exercise to put ACL2
through as it evolves.</li>

</ul>

<h3>Copyright Information</h3>

<p>Record Like Stobjs<br/>
Copyright (C) 2011-2012
<a href=\"http://www.centtech.com\">Centaur Technology</a>.</p>

<p>Contact:</p>
@({
Centaur Technology Formal Verification Group
7600-C N. Capital of Texas Highway, Suite 300
Austin, TX 78731, USA.
})

<p>License: (An MIT/X11-style license)</p>

<p>Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the \"Software\"), to deal
in the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
of the Software, and to permit persons to whom the Software is furnished to do
so, subject to the following conditions:</p>

<ul>

<li>The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.</li>

<li>THE SOFTWARE IS PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.</li>

</ul>")))

