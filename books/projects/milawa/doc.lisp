; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "xdoc/top" :dir :system)

; doc.lisp
;
; This file isn't really part of Milawa.  It just documentation about Milawa in
; XDOC format, so that Milawa can be mentioned in the Community Books manual.

(defxdoc milawa
  :parents (acl2::projects)
  :short "Milawa is a \"self-verifying\" theorem prover for an ACL2-like logic."

  :long "<h3>Introduction</h3>

<p>We begin with a simple proof checker, call it A, which is short enough to
verify by the \"social process\" of mathematics&mdash;and more recently with a
theorem prover for a more expressive logic.</p>

<p>We then develop a series of increasingly powerful proof checkers, call them
B, C, D, and so on. We show each of these programs only accepts the same
formulas as A, using A to verify B, and B to verify C, and so on. Then, since
we trust A, and A says B is trustworthy, we can trust B. Then, since we trust
B, and B says C is trustworthy, we can trust C. And so on for all the rest.  We
call this process <i>bootstrapping</i>.</p>

<p>Our final proof checker is really a theorem prover; it can carry out a
goal-directed proof search using assumptions, calculation, rewrite rules, and
so on.  We use this theorem prover to discover the bootstrapping proofs needed
to verify B, and to emit these proofs in a format that A can check.  We then
use it to discover the proof for C, and emit it in a format suitable for B, and
so on.  In this way, Milawa discovers its own soundness proof, hence
\"self-verifying\".</p>

<p>Milawa was originally developed as part of <a
href='https://www.kookamara.com/jared/'>Jared Davis'</a>
Ph.D. dissertation, <a
href='https://www.kookamara.com/jared/milawa/Documentation/dissertation.pdf'>A
self-verifying theorem prover.</a>.  The dissertation covers the process
described above, i.e., it explains how the question of trusting the prover's
tactics may be reduced to that of trusting its kernel.  The kernel and its
logical foundations are addressed informally but, at some level, its
correctness is simply assumed.</p>

<p>More recently, <a href='http://www.cl.cam.ac.uk/~mom22/index.html'>Magnus
Myreen</a> has applied ideas from his Ph.D. research to develop and formally
verify <a href='http://www.cl.cam.ac.uk/~mom22/jitawa/'>Jitawa</a>, a Lisp
runtime that is capable of running Milawa through its full bootstrapping
process.  Going further, Magnus has developed a <a
href='http://hol.sourceforge.net/'>HOL4</a>-checked proof showing that Milawa's
kernel is sound when run on Jitawa.</p>

<p>This HOL4 proof, combined with Milawa's kernel's processing of the
bootstrapping proofs, yields an impressive result: it establishes the
correctness of a heuristic, Boyer-Moore style theorem prover, all the way down
to the x86 machine code that runs it.</p>

<p>Milawa is <a href='http://www.gnu.org/philosophy/free-sw.html'>free
software</a> released under an MIT/X11 style license.</p>

<p>See @(see build) for information about how to obtain and build Milawa.</p>


<h3>Documentation</h3>

<p>The authoritative description of Milawa is:</p>

<box><p>Jared Davis.  <i><a
href=\"https://www.kookamara.com/jared/milawa/Documentation/dissertation.pdf\">A
self-verifying theorem prover</a></i>. Ph.D. thesis, University of Texas at
Austin, December 2009.  <a
href=\"https://www.kookamara.com/jared/milawa/Documentation/defense.pdf\">Defense
slides.</a> See also @(see errata).</p></box>

<p>See @(see jitawa) for information about Jitawa and the HOL4 verification of
Milawa's kernel.</p>

<p>Finally, @(see history) takes a look back at the project's timeline,
and how things went.</p>


<h4>Other, Older Papers and Talks</h4>

<ul>

<li>Jared Davis. <i><a
href=\"https://www.kookamara.com/jared/milawa/Documentation/Rewriter/rewrite.pdf\">The
Milawa rewriter<br/>and an ACL2 proof of its soundness</a></i>.  Unpublished.
October 5, 2007.</li>

<li>Jared Davis.  <i><a
href='https://www.kookamara.com/jared/milawa/Documentation/Proposal/proposal-web.pdf'>A
trustworthy, extensible theorem prover</a></i>.  Ph.D. dissertation proposal.
October 22, 2007.  Also a technical report: The University of Texas at Austin,
Department of Computer Sciences, <a
href=\"ftp://ftp.cs.utexas.edu/pub/techreports/tr08-14.pdf\">Report
#TR-08-14</a>, March 2008.  See also the <a
href='https://www.kookamara.com/jared/milawa/Documentation/Proposal/oral/proposal.pdf'>slides</a>
from the proposal talk.</li>

<li>Jared Davis.  <i><a
href=\"https://www.kookamara.com/jared/milawa/Documentation/Talks/2007-11-acl2-rewriter/rewriter.pdf\">The
Milawa rewriter and an ACL2 proof of its soundness</a></i><br/> Slides from the
<a href=\"http://www.cs.uwyo.edu/~ruben/acl2-07/\">ACL2 Workshop
2007</a>. November 16, 2007.</li>

<li>Jared Davis.  <i><a
href=\"https://www.kookamara.com/jared/milawa/Documentation/Talks/2007-03-28-acl2-meeting/Update.pdf\">Tactics
and tracing</a></i>.  Slides from an ACL2 Seminar talk, March 28, 2007.</li>

<li>Jared Davis.  <i><a
href=\"https://www.kookamara.com/jared/milawa/Documentation/Talks/2006-summer-acl2/talk.pdf\">Adding
a computation rule</a></i>.  Slides from an ACL2 Seminar talk, August 2,
2006.</li>

<li>Jared Davis.  <i><a
href=\"https://www.kookamara.com/jared/milawa/Documentation/Talks/2005-11-acl2-talk/talk.pdf\">Milawa:
an extensible proof checker</a></i>.  Slides form an ACL2 Seminar talk,
November 16, 2005.</li>

</ul>

<h3>Acknowledgments</h3>

<p>This material is based upon work supported by the <a
href='http://www.nsf.gov/'>National Science Foundation</a> under Grant No
0429591. Any opinions, findings, and conclusions or recommendations expressed
in this material are those of the author(s) and do not necessarily reflect the
views of the National Science Foundation.</p>

<p>This material is based upon work supported by the <a
href='http://www.darpa.mil/'>Defense Advanced Research Projects
Agency</a> (DARPA) under Contract NBCH30390004.</p>")


(defxdoc jitawa
  :parents (milawa)
  :short "Jitawa is a Lisp runtime developed by Magnus Myreen that is capable
of running the Milawa kernel and checking through the entire bootstrapping
process, and which is verified down to the machine code with HOL4."

  :long "<p>Magnus Myreen has used the HOL4 system to prove an unbelievably
impressive theorem: if you run the simplified Milawa kernel on his Jitawa Lisp
runtime on an 64-bit X86 system, it can only accept theorems of formulas that
are semantically true.  This theorem connects the logical semantics, down
through the kernel's source code, through the Jitawa Lisp implementation, down
to a formal HOL model of the x86 machine code!</p>

<p>The best source of information about Jitawa and these HOL4 proofs is <a
href='http://www.cl.cam.ac.uk/~mom22/jitawa/'>Magnus' Jitawa page</a>.  You may
also be interested in the following papers and slides.</p>

<ul>

<li>Magnus Myreen and Jared Davis.  <i><a
href=\"https://www.kookamara.com/jared/publications/2012-itp-milawa/2012-itp-milawa.pdf\">The
reflective Milawa theorem prover is sound (down to the machine code that runs
it)</a></i>.  Unpublished.  There are also related <a
href=\"https://www.kookamara.com/jared/milawa/Documentation/Talks/2012-northeastern/milawa-northeastern.pdf\">Slides</a>
from Jared's July 2012 talk at Northeastern University.</li>

<li>Magnus Myreen and Jared Davis.  <i><a
href=\"https://www.kookamara.com/jared/publications/2011-itp-jitawa/2011-itp-jitawa.pdf\">A
verified runtime for a verified theorem prover</a></i>.  ITP 2011.</li>

</ul>")


(defxdoc errata
  :parents (milawa)
  :short "Errata for <i>A Self-Verifying Theorem Prover</i>."
  :long "<p>Main errata</p>

<ul>

<li>Page 44.  \"This function provides a term level notion of equality, ...\"
  should be, \"Much like the [equal] function provides a term level notion of
  equality, ...\"</li>

<li>Page 65.  Definition 8.  Subsetp.  The base case is T, not NIL.<br/>
    Thanks to Dan Friedman for spotting the error!</li>

<li>Page 104.  let* is not imported.</li>

<li>Page 161.  Derived Rule 2.  Right Expansion.  The \"given\" formula should
   be \"A\", not \"A v B.\".  Thanks to Dan Connolly for spotting the error!</li>
</ul>


<p>Typos spotted by Dan Friedman:</p>

<ul>

<li>Pg. 15: \"and and\" should be \"and\"</li>
<li>Pg. 56 and 94: \"))\" should be \")))\" in the basis step</li>
<li>Pg. 84: \"a a\" should be \"a\"</li>
<li>Pg. 151: Para 2: \"then may\" should be \"then we may\"</li>

</ul>

<p>Misc. typos:</p>

<ul>
<li>Pg. 446.  \"and and\" should be \"and\"</li>
<li>Pg. 5.    \"that theorem prover\" should be \"that a theorem prover\"</li>
</ul>")


(defxdoc history
  :parents (milawa)
  :short "A short history of Milawa's development, merely for posterity."
  :long "

<h3>Prehistory (Fall 2004 - Summer 2005)</h3>

<p>I don't know exactly when I started working on a project like Milawa, but
the oldest file I found has a modification date of December 2, 2004, and that
seems about right.  During this time, I was still taking classes at UT.  I
probably first seriously talked to J about a verified theorem prover sometime
in October or November of 2004.</p>

<p>I was quite confused back then.  Looking back on the files I still have, I
do find some recognizers for terms (of literals, variables, and function
calls), but it looks like I didn't understand the difference between terms and
formulas, and for some reason I called all of the formula operations \"meta\"
operations.</p>

<p>I had written some substitution routines, and developed simple lists of the
base axioms I wanted to have.  I was apparently quite concerned about how to
extended functions, probably due to wanting to extend the proof checker itself
with new rules.  I had tried to write the evaluator with the arguments (x defs)
instead of (x defs n), and to address termination I have a long discussion
about finding or providing a measure, etc.</p>

<p>For proofs, I had first intended to use a sequential structure with named
steps, but in an early conversation J suggested trees and I remember being
quite encouraged at how much better this seemed.</p>

<p>By mid February, the project had apparently evolved to include the notion of
appeals, step checking functions, and a proof checking routine that called on
these step checkers.  In the last files from this time, dated March 4, 2005, I
had arrived at a term-only logic with instantiation and axioms, but did not
have any other rules, though comments mention the need for some kind of
equality substitution rule.</p>

<p>I had lost interest in the proof checker around this time.  I had some class
projects to work on, and spent most of my ACL2 time working reading through the
C99 standard and developing an ACL2 model of C's arithmetic expressions, which
I would later abandon when that summer I headed to Iowa for an internship with
Rockwell Collins.</p>

<p>The fall semester of 2005 would be the start of my 3rd year at UT, so during
my time at Rockwell I was looking for a dissertation project.  Near the end of
my internship, I had some discussions with Dave Greve about the limitations of
meta rules again got me interested in the verified prover, and I think I must
have reread John Harrison's technical report.</p>

<p>Then, probably around the beginning of August, I drove alone for five hours
to Minneapolis to visit some friends.  The car didn't have a CD player, so
rather than listen to rural Iowa radio stations I started discussing the
details of the project with the highway.  I remember becoming pretty excited
after figuring out how I could use computational reflection, and I also
remember coming up with the appeal-provisionally-okp function to separate out
the step checkers from proofp.  I'm pretty sure I convinced myself that this
would be my project during that car ride.</p>

<p>My last weeks at Rockwell were sufficiently busy that I had no desire to
work on a new project at home, so I didn't get started until I was back in
Austin for the Fall semester.</p>

<h3>Developing the core (Fall 2005)</h3>

<p>I started working on Milawa when I got back to UT.  I was only taking one
class, Introduction to Logic, which gave me some pretty significant time to
work on the project.</p>

<p>I started fresh.  I wanted to use something close to the ACL2 logic, so I
assembled Shoenfield's book, Shankar's dissertation, the ACL2 book, the
structured theory paper, and J's \"quick and dirty logic\" paper, from which I
was able to develop my term and formula recognizers and choose my rules of
inference.  I implemented the appeal system to represent proofs.</p>

<p>Some of the hardest work was to just come up with the basic derivations I
needed.  I think everyone who worked in the tower came by at some point or
another and tried to help with some derivation or another.  The worst was
disjoined associativity.  Sadly enough, that rule alone probably took me more
than a week to figure out.</p>

<p>I also remember spending some time on ACL2 proofs.  I know that in one of my
meetings with J, I showed him how I could prove in ACL2 that a stack of three
or four provers was sound.  This was just using commute or, right
associativity, etc. as the extensions.  That's the first time I remember him
being really excited about the project.</p>

<p>On November 16, I gave my first presentation about Milawa at the weekly ACL2
seminar.  I walked through the logic and the proof checkers, and the ACL2 proof
that proofp-2 (commute or) is sound.  At that point I'd developed a litany of
basic derivations and even developed a simplistic unconditional rewriter (no
evaluation; equality only) that could simplify if expressions if given the
right rules.</p>

<p>This was a pretty useful talk, and I walked away from it wanting more
automation and worrying about evaluation.  By Thanksgiving, I think I had
recreated Shankar's functions for tautology checking, iff substitution, and
equality substitution, and I built a tower with these extensions.  And I think
I can remember talking about my deduction rule extension at some party in
December.</p>


<h3>Evaluation (Spring 2006)</h3>

<p>I spent quite a lot of time figuring out how to handle evaluation.  I had
begun to realize that evaluation needed to have a special role in the prover:
to use a procedure reflectively, we need to be able to run it on a concrete
proof object.  But evaluation raised a lot of issues about partial functions,
termination, and paradoxes involving (eval (eval ...)).  I remember spending a
lot of time thinking about rankings or other ways to characterize when it was
safe to call eval, and I certainly wasted a lot of Matt's time with it.</p>

<p>Somehow out of this I came up with the idea of a base evaluation rule that
would only apply to the primitives.  I remember explaining some of the details
to Warren and Matt on the chalkboard, and being pretty excited at how simple
everything had become.  I think I had implemented the evaluation extension by
some time in March.</p>

<p>With evaluation in hand, I implemented a better unconditional rewriter, and
went to J and Matt for advice about conditional rewriting.  I probably spent
most of April and May working on a simplifier and trying to start the
bootstrapping process, but I didn't get very far on this.  The simplifier had
become very complicated and I had gotten too far from the builders.  I couldn't
really see how to do the proofs alongside its operation.</p>

<p>I gave a few talks about Milawa during this time.  I made a poster for
GradFest (where the prospective grad students come to see the university) and
gave a talk to Warren's CyberTrust group in March.  Then, in April, I gave a
short talk to Victor Marek who was visiting.</p>

<p>For my verification class's project, Warren also challenged me to use my
system to prove something \"real\", so I did some simple equivalence proofs for
a toy circuit and presented the work to his hardware verification class.  We
also looked into speeding up the prover with his hash consing code during
April, and we found some really promising results.</p>


<h3>Preparing to propose (Summer 2006)</h3>

<p>I was getting eager to propose, and under Warren's guidance I spent most of
the summer working on the proposal.  I spent a lot of time reading papers and
looking at other systems, and trying to present my work clearly.  I didn't
spent much time on the prover itself until probably September.</p>

<p>I did give a talk on Milawa at the beginning of August at the ACL2 seminar,
but it only covered the evaluation rule that I'd already developed that
Spring.</p>


<h3>Digressions and tactics (Sept 2006 - Nov 2006)</h3>

<p>As the fall semester started, the proposal was reviewed and informally
considered acceptable, but it could be strengthened if I could just complete
the first stage of bootstrapping.</p>

<p>My previous attempt at bootstrapping had not gone well, and after reading
about tactic-based systems, I decided I had tried to be too ACL2-like, doing
everything with a built-in simplification strategy and giving it hints when it
got stuck.  Maybe instead of trying to build a sophisticated simplifier, I
could just build up simpler tactics and then do the bootstrapping more
manually.</p>

<p>To get a feel for tactics, and also to branch out a bit, I spent some time
working with Isabelle/HOL.  I tried modelling my proof checker, figuring that
if it worked well I could perhaps prove it sound in a higher order system.  I
even gave a little talk on Isabelle to the ACL2 seminar in October, after which
I decided this had been a bad digression and had taken me off task.</p>

<p>Still, I think this was a useful in giving me a feel for tactics.  I figured
out that I could use clauses instead of sequents as the basis for tactics.  I
developed an initial system of proof \"skeletons\" that could later be filled
in by a tactic compiler, and wrote some simple tactics for removing trivial and
duplicate literals from clauses.</p>

<p>This seemed like it would work well, so I decided that my first
interesting tactic would be a clausifier and if-lifting program.  It wasn't
easy to see that the algorithm terminated, and unfortunately the proof was
interesting enough that I kept at it.  I probably spent two or three weeks on
this alone.  Eventually a working and verified clausifier was finished.</p>


<h3>Crawling (Dec 2006 - March 2007)</h3>

<p>After the clausifier was done, I returned to rewriting.  I was ready to
throw out the old conditional rewriter and take a more measured approach in
developing it.  I started by rewriting the unconditional rewriter to extend it
with iff reasoning and to make it use the same rule structures the conditional
rewriter uses.</p>

<p>It became difficult to manage the supporting derivations because of how long
they were.  I spent quite awhile developing a \"defderiv\" macro system that
would make it much easier to introduce derivations, and also improved this
macro to automatically write LaTeX versions of derivations for direct inclusion
in the proposal or other documentation.  I finished the unconditional rewriter
and its builders proofs, though these were a little difficult due to massive
case splitting.</p>

<p>February and March were really a couple of productive months.  In this time,
my difficulty with the unconditional rewriter led me to the tracing system, and
I implemented and carried out its proofs.  Also during this time, I implemented
the beginnings of my user interface, along with several tactics for splitting,
generalizing, unconditional rewriting, and induction.  There were a lot of
things that went into this, but by March 27 I had carried out a Milawa proof of
natp-of-len, my first inductive proof.  The tools I had were primitive, but the
basic interface and bootstrapping approach was largely similar to the final
setup.</p>


<h3>Walking (April 2007 - June 2007)</h3>

<p>My attention then turned to developing the conditional rewriter and its
assumption system.  By the end of April, I had developed the assumptions system
and had a working rewriter, and had translated all of the proofs in
primitives.lisp and part way through utilities.lisp.</p>

<p>Bootstrapping is largely a firefighting process.  You try to translate some
proofs.  When you have trouble, you add tools to help you figure out what went
wrong (like tracing and profiling), then try to figure out what you need to add
or do differently.  This process led me to implement iff-based assumptions and
rewriting, ancestors checking, new tactics for car-cdr elimination, improve the
sizes of various builders for splitting, etc.</p>

<p>By May 25, I'd finished bootstrapping through the utilities directory.  With
my tools improved from that effort, it took only about another week to get
through the logic directory and verify a demo extension (with just the
commutativity of or).</p>

<p>This was a big milestone, and after it was done I spent a good while working
on getting the \"core proof checker\" to run on a bunch of Lisps and actually
check the proof.</p>


<h3>Running (August 2007 - May 2008)</h3>

<p>By the end of August, my tools were getting a lot better.  I had extended
the rewriter with free-variable matching, forcing, and caching.  I added
%autoprove to the bootstrapping interface to avoid copying and pasting goals,
and developed the provisional certification mechanism to speed up
re-certification (which was really important, since my tools were still
changing a lot and this was causing me to work on updating proofs.)</p>

<p>I spent a lot of time in August and September working on a journal paper
that described my rewriter, which ended up being rejected.  This was
disappointing, but it was useful when it came time to write up the rewriter for
my dissertation.</p>

<p>In October I gave my proposal, which took a bit of time.  By the time of the
proposal, I had finished the bootstrapping through Level 4, which gave me the
ability to say that the approach indeed seemed practical, and to highlight the
reduction in proof size after introducing the intermediate levels.</p>

<p>The following months were good times.  There was a lot of work to manage and
avoid large proofs, and it was a chore to manage proofs.  There were also some
distractions; I took a few weeks to learn Ruby and write the addjob program to
be able to use more computers.  Also, at the end of November my wife and I
bought our home, and we spent the better part of two months working on that.
At any rate, by the end of April, I had finished bootstrapping through Level 8,
and was feeling that the project was getting close to done.</p>


<h3>Internship. (Summer 2008).</h3>

<p>In the summer I worked full time at Centaur, and spent almost no time
working on Milawa.  The only thing I really did during this time was writing
the fast rewriters.</p>


<h3>Writing and Working (Fall 2008 - Summer 2009).</h3>

<p>My internship at Centaur continued through the fall, but I reduced my hours
to 30 per week so that I could begin work on the dissertation.  I spent some
minor time with the code, but was mostly writing.  Our daughter, Calista, was
born in November, so I had a fair amount going on.</p>

<p>Throughout the Spring, I did a great deal of writing.  I did not really
return to the new coding until May.  To make the dissertation better, I wanted
to finish the fast rewriter proofs, and this was quite hard and took a lot of
time.</p>

<p>In August, very near my deadline, I finished those hard proofs.  Then, in
about a weekend, I did all of the bootstrapping for Level 11, and the project
reached its final state.</p>


<h3>Writing. (Jan 2009 - August 2009)</h3>

<p>Most of my effort was spent writing the dissertation.  I also worked on
improving the code somewhat during this time, and really finished the
boostrapping.  J and Matt gave me tremendously useful comments on drafts, and I
managed to answer most of their questions.</p>


<h3>Victory (September - October 2009).</h3>

<p>I defended in September and somehow passed.  It was good to meet John
Harrison, who gave me many useful comments and corrections.  We celebrated with
a nice dinner.  After a few weeks break, I finished the corrections and received
the blessings of the ruler lady, and that was that for grad school.</p>


<h3>Jitawa (June 2010 - 2012)</h3>

<p>Late one night I discovered Magnus's dissertation, and was shocked at (1)
how cool it was, and (2) the similarity between his toy Lisp and Milawa's
subset of Lisp.  I contacted Magnus and we began a (very one-sided)
collaboration, which ultimately resulted in the development of a verified Lisp
that can run Milawa.  Magnus eventually carried this through the very, very
impressive HOL result showing that Milawa's kernel is sound.</p>")


(defxdoc build
  :parents (milawa)
  :short "Instructions for obtaining and building Milawa."

  :long "<p>Milawa has a close relationship with ACL2.  All of its tactics can
be thought of as both ACL2 and Milawa functions.  The full bootstrapping proof
is first \"sketched\" in ACL2, and then \"re-discovered\" or \"formalized\"
with Milawa.</p>

<p>This documentation describes how to build the ACL2-related portion of
Milawa.  But these instructions <b>do not cover</b> Magnus Myreen's work on
@(see jitawa), and the HOL4 verification of Milawa's kernel.</p>

<p>The Milawa source code is now included in the <a
href='https://github.com/acl2/acl2'>ACL2 Community Books</a> project.
However, Milawa is not built during the \"make\" of the ordinary ACL2 Community
Books, because building it:</p>

<ul>
<li>takes several hours</li>
<li>requires a lot of memory and hard disk space, and</li>
<li>requires Clozure Common Lisp (CCL).</li>
</ul>

<p>Instead, to build Milawa, you should:</p>

<ol>

<li>Build CCL and ACL2 according to the instructions in
@('books/centaur/README.html').</li>

<li>Then run these commands:
@({
     $ cd acl2/books/projects/milawa/ACL2
     $ make -j <n>                 # n is how many jobs to run in parallel
})

Where @('<n>') is appropriate for your computer, e.g.:
<ul>
<li>As large as possible, but</li>
<li>No more than your number of CPU cores, to avoid excessive
    task switching overhead.</li>
<li>No more than (Physical_Memory / 4 GB), to avoid death by swapping.</li>
</ul></li>

</ol>

<p>A successful build should result in:</p>

<ul>

<li>Several new ACL2 images in @('acl2/books/projects/milawa/ACL2/acl2-images/')
including one called @('user-symmetry')</li>

<li>ACL2 certificates (.cert) or \"ACL2 Milawa Provisional
Certificates\" (.mpcert) for files throughout the milawa/ACL2 directory</li>

<li>Thousands of proof files throughout the @('milawa/Proofs') directory.</li>

</ul>

<p>These proof files are the \"boostrapping proofs\" that can now be checked by
the Milawa kernel.  There are many options here: Milawa has two kernels:</p>

<ul>

<li>The original kernel, a Common Lisp program that has historically been run
successfully on at least CCL, SBCL, CMUCL, and (for the very patient) CLISP, on
certain platforms.  In this case, the proof files can be processed
directly.</li>

<li>The new kernel, either a Common Lisp or Jitawa Lisp program, that can be
run on at least CCL, SBCL, and Jitawa (a verified Lisp by Magnus Myreen).  In
this case, the proof files first need to be further collected and
compressed.</li>

</ul>

<p>See @(see final-checks) for information about how to build the Milawa
kernel on your choice of Lisps, and how to use it to check these proofs.</p>")


(defxdoc final-checks
  :parents (milawa)
  :short "How to build the Milawa kernel on your choice of Lisps, and use it to
check the proofs produced by the bootstrapping process."

  :long "<p>After you have done a @(see build), you will have thousands of
proof files throughout the @('milawa/Proofs') directory.  Here, we explain how
to create a standalone Milawa proof checker, and use it to check these proofs
with a Common Lisp implementation.  The instructions for Jitawa are different;
see @(see jitawa-checks).</p>

<h3>1.  Choose a Lisp Implementation</h3>

<p>You will need to install a Lisp environment to run the proof checker.  Many
options may work.</p>

<h5><a href='http://trac.clozure.com/openmcl'>CCL</a> -- <b>Recommended</b>, free, high performance</h5>

<p>Instructions:</p>
<ul>
<li>After installing ccl, add a symlink named @('ccl') to your $PATH</li>
</ul>

<p>Performance note: at the top of @('milawa.lsp'), there are some
CCL-specific settings which configure the garbage collector to collect after
every 512 MB.  This seems to be appropriate for a system with up to 4 GB of
memory.  If your system has considerably more memory than this, increasing this
threshold may provide better performance.</p>


<h5><a href='http://sbcl.sourceforge.net/'>SBCL</a> -- free, multiplatform, good performance</h5>

<p>Instructions:</p>
<ul>
  <li>After installing, add a symlink named @('sbcl') to your $PATH</li>
</ul>

<p>Performance note: at the top of <tt>milawa.lsp</tt>, there are some
SBCL-specific settings which configure the garbage collector to collect after
every 512 MB.  This seems to be appropriate for a system with up to 4 GB of
memory.  If your system has considerably more memory than this, increasing this
threshold may provide better performance.</p>


<h4>Other Options</h4>

<p>Other Lisps <b>may or may not still work</b>.  The instructions below are
probably a good starting point, but I have not tried to use these Lisps to
check the proofs since my dissertation.</p>

<h5><a href='http://www.cons.org/cmucl/'>CMUCL</a> -- free, good performance</h5>

<p>Instructions:</p>
<ul>
 <li>After installing, add a symlink named @('lisp') to your $PATH</li>
</ul>

<p>Performance note: at the top of <tt>milawa.lsp</tt>, there are some
CMUCL-specific settings which configure the garbage collector to collect after
every 512 MB.  This seems to be appropriate for a system with up to 4 GB of
memory.  If your system has considerably more memory than this, increasing this
threshold may provide better performance.</p>


<h5><a href='http://clisp.cons.org/'>CLISP</a> -- free, VERY SLOW</h5>

<p>Instructions:</p>
<ul>
  <li>After installing, add a symlink named @('clisp') to your $PATH</li>
</ul>

<p>Macintosh note: I am unable to use <tt>clisp</tt> on a macbook because I
cannot increase the stack size (e.g., <tt>ulimit -s</tt>) beyond 16384.  In my
successful runs Linux machines, I use a ulimit of 65535.</p>


<h5><a href='http://www.franz.com/products/allegrocl/'>Allegro</a> -- commercial, fast, NOT KNOWN TO WORK</h5>

<p>Instructions:</p>
<ul>
  <li>After installing, add a symlink named @('acl') to your $PATH</li>
</ul>

<p>I only have access to a copy of Allegro on 32-bit linux, and it runs out of
memory in Level 10 on Nemesis.  I have tried to address this by using Allegro's
<a
href='http://www.allegrocache.org/support/tech_corner/lisp-heap-051508.lhtml'>build-lisp-image</a>
function to create a copy of Allegro with a larger Lisp heap size, e.g.,</p>

@({
  (build-lisp-image \"big-acl.dxl\"
                    :lisp-heap-start \"500M\"
                    :c-heap-start \"3000M\")
})

<p>Then, I used <tt>acl -I big-acl.dxl</tt> when building the base Milawa program, but this
is still not successful.  It may be that a more recent version of Allegro or more powerful
computer will be successful.</p>


<h5><a href='http://www.scieneer.com/scl/'>Scieneer</a> -- commercial,
NOT KNOWN TO WORK</h5>

<p>Instructions</p>
<ul>
  <li>After installing, add a symlink named @('scl') to your $PATH</li>
</ul>

<p>I have not been able to get <tt>scl</tt> to complete the proofs, as it
segfaults on me during the proofs in the utilities directory.  I have not spent much
effort to debug this, and perhaps the problem is specific to my platform (Linux x86-64)
or fixed in a more recent version.</p>

<h5>Other Lisps?</h5>

<p>It may not be difficult to port Milawa to another Lisp implementation.  In
my experience, you will probably need to increase various resource limits,
e.g., the maximum call-stack size, heap size, and so on, to successfully finish
the checks.  Also, you'll need to implement the <tt>save-and-exit</tt> function
for the new Lisp, or not use checkpointing.</p>


<h3>2. Build the Proof Checker</h3>

<p>The original (Common Lisp, not @(see jitawa)-Lisp) version of the Milawa
kernel is located at:</p>

@({
    acl2/books/projects/milawa/milawa.lsp
})

<p>When you load this into your Lisp, it will create a new executable.  The
proper way to do this is to go to the @('acl2/books/projects/milawa')
directory, then start your lisp and run:</p>

@({
   (defconstant image-extension \"<name>\")
   (load \"milawa.lsp\")
})

<p>The @('<name>') you give determines the file extensions for the Milawa
images that will be generated.  I typically give names like \"ccl-linux64\" or
\"sbcl-win32\", and so on, so that I know what kind of platform each image is
for. (It's perfectly fine to check the proofs with multiple Lisps.)</p>

<p>This should produce a new file named @('base.<name>'), which is the \"base
system,\" i.e., the kernel, with no theorems loaded.</p>

<p>At this point, to make sure everything is working you should run </p>

@({
     ./milawa-<lispname> base.<name>
})

<p>For instance, if you decided to use CCL, and your @('image-extension') is
@('ccl-darwin'), then you would run:</p>

@({
     ./milawa-ccl base.ccl-darwin
})

<p>The script may print a message asking you to configure it, e.g., for SBCL
and CMUCL you will need to figure out appropriate memory settings for your
host.  If all is well, it should print \"Milawa Proof Checker,\" and you can
quit by sending EOF.</p>

<h3>3. Check the Proofs.</h3>

<p>Estimated time: 1-2 days (see the benchmarks in my dissertation for a better
idea.)</p>

<p>Now that everything is set up, you can use the @('final-checks.sh') script
to check the proofs.</p>

<p>The usage is:</p>
@({
    cd acl2/books/projects/milawa
    sh final-checks.sh <lispname> <name>
})

<p>For instance:</p>
@({
    sh final-checks.sh ccl ccl-darwin
})

<p>This will result in a lot of output, and I generally @('tee') it into a
file.  After each directory, a checkpoint is taken so that in the event of a
power outage or something, you will only lose the current directory's
work (which may still be a few hours).</p>

<p>If everything is successful, the file @('user.<name>') will be produced.
This image will have the highest-level proof checker already loaded and ready
to go.</p>")


(defxdoc jitawa-checks
  :parents (milawa)
  :short "How to do the @(see final-checks) using @(see jitawa) as the host Lisp,
instead of a Common Lisp system."

  :long "<p>BOZO document me.</p>")
