; ACL2 System+Books Combined XDOC Manual
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)


(defsection math
  :parents (top)
  :short "Math-related libraries: arithmetic, algebra, bit-vectors.")

(defsection algebra
  :parents (math)
  :short "Libraries to reason about algebraic structures, e.g. groups, rings, fields, polynomials.")

(defsection arithmetic
  :parents (math)
  :short "Libraries for reasoning about basic arithmetic, bit-vector
arithmetic, modular arithmetic, etc.")

(defsection arithmetic-2
  :parents (arithmetic)
  :short "A newer arithmetic library that is considered deprecated in favor of arithmetic-5."
  :long "For more information, see @('arithmetic-2/README')."
  )

(defsection arithmetic-3
  :parents (arithmetic)
  :short "Another newer arithmetic library that is considered deprecated in favor of arithmetic-5."
  :long "For more information, see @('arithmetic-3/README').")

(defsection arithmetic-5
  :parents (arithmetic)
  :short "A powerful arithmetic library."
  :long "For more information, see @('arithmetic-5/README').")

(defsection bit-vectors
  :parents (math)
  :short "Libraries for reasoning about bit vectors.")

(defsection boolean-reasoning
  :parents (top)
  :short "Libraries related to representing and processing Boolean functions,
geared toward large-scale automatic reasoning, e.g., via SAT solving and AIG or
BDD packages."

  :long "<h3>Introduction</h3>

<p><a href='http://en.wikipedia.org/wiki/Boolean_function'>Boolean
functions</a> are widely useful throughout mathematical logic, computer
science, and computer engineering.  In formal verification, they are especially
interesting because many high-capacity, fully automatic techniques are known
for analyzing, comparing, and simplifying them; for instance, see <a
href='http://en.wikipedia.org/wiki/Binary_decision_diagram'>binary decision
diagrams</a> (bdds), <a
href='http://en.wikipedia.org/wiki/Boolean_satisfiability_problem'>SAT
solvers</a>, <a
href='http://en.wikipedia.org/wiki/And-inverter_graph'>and-inverter
graphs</a> (aigs), <a href='http://en.wikipedia.org/wiki/Model_checking'>model
checking</a>, <a
href='http://en.wikipedia.org/wiki/Formal_equivalence_checking'>equivalence
checking</a>, and so forth.</p>

<h3>Libraries for Boolean Functions</h3>

<p>We have developed some libraries for working with Boolean functions, for
instance:</p>

<ul>

<li>@(see satlink) provides a representation of <a
href='http://en.wikipedia.org/wiki/Conjunctive_normal_form'>conjunctive normal
form</a> formulas and a way to call SAT solvers from ACL2 and trust their
results.</li>

<li>Libraries like @(see aig) and @(see ubdds) provide @(see hons)-based AIG and
BDD packages.</li>

<li>@(see aignet) provides a more efficient, @(see stobj)-based AIG
representation similar to that used by <a
href='http://www.eecs.berkeley.edu/~alanmi/abc/'>ABC</a>.</li>

</ul>

<p>These libraries are important groundwork for the @(see gl) framework for
bit-blasting ACL2 theorems, and may be of interest to anyone who is trying to
develop new, automatic tools or proof techniques.</p>

<h3>Libraries for Four-Valued Logic</h3>

<p>Being able to process large-scale Boolean functions is especially important
in @(see hardware-verification).  But actually, here, to model certain circuits
and to implement certain algorithms, it can be useful to go beyond Boolean
functions and consider a richer logic.</p>

<p>You might call Boolean functions or Boolean logic a two-valued logic, since
there are just two values (true and false) that any variable can take.  It is
often useful to add a third value, usually called X, to represent an
\"unknown\" value.  In some systems, a fourth value, Z, is added to represent
an undriven wire.  For more on this, see @(see why-4v-logic).</p>

<p>We have developed two libraries to support working in four-valued logic.  Of
these, the @(see 4v) library is somewhat higher level and is generally simpler
and more convenient to work with.  It serves as the basis of the @(see esim)
hardware simulator.  Meanwhile, the @(see faig) library is a bit lower-level
and does not enjoy the very nice @(see 4v-monotonicity) property of @(see
4v-sexprs).  On the other hand, @(see faig)s are closer to @(see aig)s, and can
be useful for loading expressions into @(see aignet) or @(see satlink).</p>

<h3>Related Papers</h3>

<p>Besides the documentation here, you may find the following papers
useful:</p>

<p>Jared Davis and Sol Swords.  <a
href='http://dx.doi.org/10.4204/EPTCS.114.8'>Verified AIG Algorithms in
ACL2.</a>  In ACL2 Workshop 2013. May, 2013. EPTCS 114.  Pages 95-110.</p>

<p>Sol Swords and Jared Davis.  <a
href='http://dx.doi.org/10.4204/EPTCS.70.7'>Bit-Blasting ACL2 Theorems</a>.
In ACL2 Workshop 2011.  November, 2011.  EPTCS 70.  Pages 84-102.</p>

<p>Sol Swords and Warren A Hunt, Jr.  <a
href='http://dx.doi.org/10.1007/978-3-642-14052-5_30'>A Mechanically Verified
AIG to BDD Conversion Algorithm</a>.  In ITP 2010,LNCS 6172, Springer.  Pages
435-449.</p>")


(defsection hardware-verification
  :parents (top)
  :short "Libraries for working with hardware description languages, modeling
 circuits, etc."
 :long "Also see the (probably incomplete) <a
 href='http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html'>page
 of ACL2-related publications</a>.")

(defsection software-verification
  :parents (top)
  :short "Software verification projects, tools, etc."
  :long "Also see the (probably incomplete) <a
 href='http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html'>page
 of ACL2-related publications</a>.")

(defxdoc macro-libraries
  :parents (top macros)
  :short "Libraries of useful macros"
  :long "<p>See @(see macros) for documentation of macros that are built into
 ACL2.</p>

 <p>The subtopics below describe macros defined in the @(see community-books)
 that support writing more concise code, including frameworks for quickly
 introducing concepts like typed structures, typed lists, defining functions
 with type signatures, and automating other common tasks.</p>")

(defxdoc proof-automation
  :parents (top)
  :short "Tools, utilities, and strategies for dealing with particular kinds
of proofs.")

(defxdoc testing-utilities
  :parents (top)
  :short "Tools for developing and running tests.")


(defxdoc hint-utils
  :parents (proof-automation)
  :short "Tools that produce hints to guide the prover.")

(defxdoc community
  :parents (top)
  :short "The ACL2 Community."
  :long "<p>ACL2 has an active user community that welcomes new users.  There are several ways to get involved and to get help with ACL2.</p>

 <h3>GitHub Project</h3>
 <p>ACL2 is developed via <a href=\"https://github.com/acl2/acl2\">the ACL2 GitHub project</a>, which also contains the ACL2 libraries maintained by the community (see @(see community-books)).  The GitHub repository is very active, with thousands of commits per year.  Users are invited to contribute new developments, in the form of new @(see books) (collections of definitions, proofs, etc.), so that the community can benefit from them.  See @(see how-to-contribute), and see @(see git-quick-start).  Problems with ACL2 or with books can be reported as <a href=\"https://github.com/acl2/acl2/issues\">GitHub Issues</a>.</p>

 <h3>Mailing Lists</h3>
 <p>We maintain several mailing lists for ACL2 announcements, discussions, and questions (see @(see mailing-lists)).</p>

 <h3>Zulip Chat</h3>
 <p>Zulip is a chat application similar to Slack.  We use it to discuss many ACL2 topics and to help each other with ACL2 issues.   It is accessible at <a href=\"https://acl2.zulip.kestrel.institute\">this page</a> or via the Zulip desktop or mobile app.  Email Eric Smith at @('eric.smith@kestrel.edu') for an invitation.  As an anti-spam measure, please include in your email a sentence or two about how you heard about ACL2 and/or how you plan to use it.</p>

 <h3>ACL2 Workshops</h3>
 <p>ACL2 users gather to present their work at the ACL2 Workshops, which have taken place approximately every 18 months since 1999.  See @(see workshops) for more information.</p>

 <h3>The 100 Theorems page</h3>
 <p>We maintain a list of the theorems from the <a href=\"https://www.cs.ru.nl/~freek/100/\">Formalizing 100 Theorems</a> page that have been proved in ACL2.  See @(see 100-theorems).  Users are invited to attempt to prove additional theorems from the list, though this may be challenging!</p>

 <h3>Stack Exchange</h3>
 <p>The <a href=\"https://proofassistants.stackexchange.com/questions/tagged/acl2\">Proof Assistants Stack Exchange</a> has some questions and answers about ACL2, but the ACL2 Zulip (see above) and @('acl2-help') mailing list (see above, under Mailing Lists) are more popular.</p>")

(defxdoc workshops
  :parents (community about-acl2)
  :short "The ACL2 Workshop Series."
  :long "<p>The ACL2 Workshop series consists of conferences that are held
 regularly, as listed below.</p>

 <p>In 2010, the ACL2 Workshop did a one-time merger with TPHOLs to form the
 first International Conference on Interactive Theorem Proving (ITP).  Such a
 merger may occur again, but whether or not that happens, the ACL2 community is
 encouraged to participate in ITP.  Other conferences of particular interest to
 the ACL2 community include CAV (Computer Aided Verification) and <a
 href='http://www.cs.utexas.edu/users/hunt/FMCAD/'>FMCAD</a>
 (Formal Methods in Computer Aided Design).</p>

 <ul>

 <li><a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2025/index.html'>ACL2
 Workshop 2025</a>: May 12-13, 2025, Austin, Texas, USA and also online.</li>

 <li><a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2023/index.html'>ACL2
 Workshop 2023</a>: November 13-14, 2023, Austin, Texas, USA and also
 online.</li>

 <li><a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2022/index.html'>ACL2
 Workshop 2022</a>: May 26-27, 2022, Austin, Texas, USA and also online.</li>

 <li><a href='http://www.acl2-2020.info'>ACL2 Workshop 2020</a>: May 28-29,
 2020 (held online via video streaming).</li>

 <li><a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2018/index.html'>ACL2
 Workshop 2018</a>: November 5-6, 2018, Austin, Texas, USA.</li>

 <li><a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2017/index.html'>ACL2 Workshop 2017</a>: May 22 - 23, 2017, Austin, Texas, USA.</li>

 <li><a
href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2015/index.html'>ACL2
Workshop 2015</a>: October 1-2, 2015, Austin, Texas, USA.  (Co-located with <a
href='http://www.cs.utexas.edu/users/hunt/FMCAD/FMCAD15/index.shtml'>FMCAD
2015</a>.)</li>

 <li><a href='http://vsl2014.at/acl2/'>ACL2 Workshop 2014</a>: July 12-13,
 2014, Vienna, Austria, as an ITP-affiliated workshop of FLoC (part of the <a
 href='http://vsl2014.at/'>Vienna Summer of Logic</a>).

   <ul>
   <li><a href='http://cs.ru.nl/~freekver/acl2_14_program.html'>Slides</a></li>
   <li><a href='http://arxiv.org/html/1406.1238v1'>Proceedings</a></li>
   </ul>
 </li>

 <li><a href='http://www.cs.uwyo.edu/~ruben/acl2-13'>ACL2 Workshop 2013</a>:
 May 30-31, 2013, University of Wyoming, Laramie, Wyoming, USA.

   <ul>
   <li><a href='http://eptcs.web.cse.unsw.edu.au/content.cgi?ACL22013'>Proceedings</a></li>
   </ul>
 </li>

 <li><a href='http://www.cs.utexas.edu/users/moore/acl2/acl2-11/Home.html'>ACL2
 Workshop 2011</a>: November 3-4, 2011, Austin, Texas, USA.  (Co-located with
 <a href='http://www.cs.utexas.edu/users/ragerdl/fmcad11/'>FMCAD 2011</a>.)

   <ul>
   <li><a href='http://eptcs.web.cse.unsw.edu.au/content.cgi?ACL22011'>Proceedings</a></li>
   </ul>
 </li>

 <li><a href='http://www.cs.utexas.edu/users/kaufmann/itp-2010/'>ITP 2010:
 Int'l Conference on Interactive Theorem Proving (ITP) 2010</a>: July 11-14,
 2010, Edinburgh, Scotland; part of <a href='http://floc-conference.org'>FLoC
 2010</a>.</li>

 <li><a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2009/'>ACL2
 Workshop 2009</a>: May 11-12, 2009, Boston, Massachusetts, USA.  (<a
 href='http://portal.acm.org/citation.cfm?id=1637837&amp;coll=GUIDE&amp;dl=GUIDE&amp;CFID=101915764&amp;CFTOKEN=26521015'>Proceedings
 available from ACM Digital Library.</a>)</li>

 <li><a href='http://www.cs.uwyo.edu/~ruben/acl2-07'>ACL2 Workshop 2007</a>:
 November 15-16, 2007, Austin, Texas, USA.</li>

 <li><a href='http://www.ccs.neu.edu/home/pete/acl206/'>ACL2 Workshop 2006</a>:
 August 15-16, 2006, Seattle, Washington, USA. (<a
 href='http://portal.acm.org/toc.cfm?id=1217975&amp;coll=portal&amp;dl=ACM&amp;type=proceeding&amp;idx=SERIES10714&amp;part=Proceedings&amp;WantType=Proceedings&amp;title=ACM%20International%20Conference%20Proceeding%20Series'>Proceedings
 available from ACM Digital Library.</a>)</li>

 <li><a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2004'>ACL2
 Workshop 2004</a>: November 18-19, 2004, Austin, Texas, USA.</li>

 <li><a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2003'>ACL2
 Workshop 2003</a>: July 13-14, 2003, Boulder, Colorado, USA.</li>

 <li><a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2002'>ACL2
 Workshop 2002</a>: April 8-9, 2002, Grenoble, France. </li>

 <li><a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2000'>ACL2
 Workshop 2000</a>: October 30-31, 2000, Austin, Texas, USA.</li>

 <li><a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-1999'>ACL2
 Workshop 1999</a>: March 29-31, 1999, Austin, Texas, USA.</li>

 </ul>

 <h3>List of past ACL2 Workshop slogans:</h3>


 <ul>

 <li><i>1999</i>: It ain't over til the last Q.E.D.</li>

 <li><i>2000</i>: Just prove it.</li>

 <li><i>2002</i>: Accumulated Persistence</li>

 <li><i>2003</i>: No software too trivial. No error too obscure.</li>

 <li><i>2004</i>: Defun starts here</li>

 <li><i>2006</i>: ACM Software Systems Award Winner!</li>

 <li><i>2007</i>: Save the world. Use make-event.</li>

 <li><i>2009</i>: <i>None</i></li>

 <li><i>2011</i>: We aim to prove</li>

 <li><i>2013</i>: Pain is temporary; theorems are forever.</li>

 <li><i>2014</i>: I love the smell of parentheses in the morning.</li>

 <li><i>2015</i>: 25 years of rewriting history</li>

 <li><i>2017</i>: In Proof We Trust</li>

 <li><i>2018</i>: Sometimes you feel like alist, sometimes you don't</li>

 <li><i>2020</i>: <tt>(defaxiom acl2-2020 'Damn nil. Full speed
 ahead!' (not (lexorder 'acl2 'covid-19)))</tt></li>

 <li><i>2022</i>: supporting (in-theory ...) local events</li>

 <li><i>2023</i>: Certifiable</li>

 <li><i>2025</i>: I'm sorry, Dave: I'm afraid I can't prove that.</li>

 </ul>

 <p>Jared Davis, Keshav Kini, and Andrew Walter have graciously supplied <a
 href='https://github.com/acl2/acl2/tree/master/books/workshops/references'>a
 listing of bibtex entries for the ACL2 workshops</a> through 2023 (would be
 nice if extended past 2023; any volunteers?).</p>

 <p>ACL2 input files (@(see certifiable) @(see books)) from the preceding
 workshops are available in the <a
 href='https://github.com/acl2/acl2/'>ACL2+Books GitHub repository</a>,
 specifically, in its <a
 href='https://github.com/acl2/acl2/tree/master/books/workshops/'>subdirectory
 for workshop contributions</a>.</p>")
