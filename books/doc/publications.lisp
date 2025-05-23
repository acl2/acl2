; Copyright (C) 2025, Regents of the University of Texas
; Originally Maintained by J Moore and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Quoting the original version of file
; https://www.cs.utexas.edu/~moore/publications/acl2-papers.html from which
; this version was copied in May, 2025:

;;; <!-- This is the only copy of the ACL2 Annotated Bibliography.  It is
;;; maintained on my web publications/ directory and so can reference my papers
;;; implicitly.  It can reference any paper absolutely.  I have copied some
;;; papers to the subdirectory others/ to make them available on the web for
;;; authors who do not have web publication access.  The ACL2 Home Page (starting
;;; for Version 2.2) references this file absolutely.  So all ACL2 Home Pages,
;;; whether the "official" one or local copies, all come here when the user
;;; clicks on "Papers about ACL2 and Its Applications".  You can edit this
;;; directly, without regard for ACL2 releases or even Version numbers. -->

; NOTE: When xdoc supports more entities it might be nice to undo the following
; changes that were made when converting to xdoc.

; Gr&ouml;bner => Groebner
; Mart&iacute;n-Mateos => Martin-Mateos
; Lamb&aacute;n => Lamban
; Jim&eacute;nez => Jimenez

(in-package "PUBLICATIONS")
(include-book "xdoc/top" :dir :system)

(defun docpath (s)

; This function is used for replacing relative pathnames.  However, absolute
; pathnames based on http://www.cs.utexas.edu/users/moore/publications/ have
; been retained.

; If one has searched for
;   href='
; then one can invoke meta-x docpath in Emacs to insert the appropriate docpath
; call, after defining the Emacs keyboard macro docpath as follows.

; (fset 'docpath
;    "@(`(:raw (docpath \\\"\C-s'\C-b\\\"))`)")

  (concatenate 'string
               "https://www.cs.utexas.edu/users/moore/publications/"
               s))

(defxdoc publications
  :parents (documentation)
  :short "ACL2 Annotated Bibliography"
  :long "<p>This is the top-level topic for an annotated bibliography
  containing books and Papers about <a
  href='http://www.cs.utexas.edu/users/moore/acl2/'>ACL2</a> and Its
  Applications.</p>

 <font size='+2' color='FF0000'><b>NOTES:</b></font>

 <ol>

 <li>The lists in the subtopics are generally incomplete, and many entries are
 out-of-date.  To search for publications about some ACL2 topic we recommend a
 standard web search (e.g., Google) and that you include in your search pattern
 the name ACL2.</li>

 <li>See also <a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshops.html'>the ACL2
 workshops page</a> for proceedings of ACL2 workshops, which contain numerous
 papers, many of them recent, that are not found below.  Bibliographic
 references (BibTeX format) for most or all ACL2 workshops may be found in
 @(see community-books) directory @('books/workshops/references/').</li>

 <li>The ACL2 community is invited to add entries for missing publications.  If
 you add an entry, please try to conform to the existing style.  Each topic in
 the documentation tree below the present topic has entries that are generally
 ordered from newest to oldest.  So consider adding new papers at or near the
 top of a topic.</li>

 </ol>")

(xdoc::order-subtopics publications nil t)

(defxdoc pub-summary
  :parents (publications)
  :short "About ACL2:  Quick Summary of What Can Be Done and How to Learn ACL2"
  :long "
 <p><a
 href='http://www.cs.utexas.edu/users/moore/publications/how-to-prove-thms/index.html'>This
 link</a> will take you to a page on which you can find:
 <ul>
 <li>a brief paper about ACL2 and applications;</li>
 <li>exercises, which provide the best way to learn ACL2;</li>
 <li>a paper with lots of tips on how to program and prove theorems
 with ACL2; and</li>
 <li>additional tutorial material, including notes in Spanish and
   slides by Inmaculada Medina Bulo and Francisco Palomo Lozano.</li>
 </ul></p>")

(defxdoc pub-books
  :parents (publications)
  :short "Books Published"
  :long "
 <h3>Books about ACL2 and Its Applications</h3>

 <ul>

 <li>How to use ACL2:<br/>
     <i><a href='@(`(:raw (docpath \"acl2-books/car/index.html\"))`)'>Computer-Aided Reasoning:  An Approach</a></i>, Matt Kaufmann,
 Panagiotis Manolios, and J Strother Moore,
 Kluwer Academic Publishers,
 June, 2000.  (ISBN 0-7923-7744-3)</li>

 <li>What can be done with ACL2:<br/>
 <i><a href='@(`(:raw (docpath \"acl2-books/acs/index.html\"))`)'>Computer-Aided Reasoning:  ACL2 Case Studies</a></i>, Matt Kaufmann,
 Panagiotis Manolios, and J Strother Moore (eds.),
 Kluwer Academic Publishers,
 June, 2000.  (ISBN 0-7923-7849-0)</li>

 </ul>

 <p>
 Using the techniques described in these two books, users of the ACL2 system
 have modeled and proved properties of hardware designs, microprocessors,
 microcode programs, and software.  In addition, many theorems in mathematics
 and meta-mathematics have been proved with ACL2.
 </p>

 <p>Details:</p>

 <ul>

 <li><i><a href='@(`(:raw (docpath
 \"acl2-books/car/index.html\"))`)'>Computer-Aided Reasoning: An
 Approach</a></i>: description, excerpts, errata, solutions to exercises.</li>

 <li><i><a href='@(`(:raw (docpath \"acl2-books/acs/index.html\"))`)'>Computer-Aided Reasoning:  ACL2 Case Studies</a></i>: description, list of contributors, excerpts, errata,
 full scripts for case studies, solutions to exercises.</li>

 <li><a href='http://www.cs.utexas.edu/users/moore/acl2/index.html'>ACL2 Home Page</a>: tours of the system, documentation, technical papers,
 source code, installation guide, mailing lists.</li>

 <li><a href='@(`(:raw (docpath \"acl2-books/OrderingInformation.html\"))`)'>Ordering Information</a></li>

 <li><a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-1999/'>1999
 ACL2 Wizard's Workshop</a>: this was the meeting that produced the two books above; it
 was the first in a planned series of workshops for the ACL2 community.</li>

 </ul>

 <h3>Book about logic in computing using ACL2</h3>

 <p><em><a href='http://mitpress.mit.edu/books/essential-logic-computer-science'>Essential
 Logic for Computer Science</a></em>, Rex Page and Ruben Gamboa. ISBN
 978-0262039185. MIT Press, 2019.</p>

 <p>This book is an introduction to the use of predicate logic and ACL2 for
 testing and verifying software and digital circuits. It has been used as a
 textbook in an honors introductory course in computing, and with
 supplementary materials in a course in discrete mathematics.</p>

 <h3>Book about a predecessor of ACL2</h3>

 <p><em><a href='http://www.cs.utexas.edu/users/boyer/acl.pdf'>A Computational Logic</a></em>, R. S. Boyer and J S. Moore.
  Academic Press, New York, 1979.  xiv+397.
  The original Pub source for the book is <a href='@(`(:raw (docpath \"acl.txt\"))`)'>here</a>.
  The translation to TeX and pdf was kindly done by Gary Klimowicz.

 The above book is out of print.
 The copyright has reverted to the authors.</p>

 <p>Boyer and Moore hereby place it in the public domain.</p>

 <h3>Book about customized reasoning tools</h3>

 <p><a
 href='https://link.springer.com/book/10.1007/978-1-4419-5998-0'>Scalable
 Techniques for Formal Verification</a>, Sandip Ray.  ISBN
 978-4419-5997-3.  <a href='http://www.springer.com'>Springer</a>,
 2010.</p>

 <p>This book explains how to develop customized reasoning tools on
 top of ACL2.  The customized reasoning tools extend ACL2 by
 significantly automating formal proofs on their target domains,
 but without requiring any modification to the theorem prover
 source code.</p>

 <h3>Book about high-assurance microprocessors</h3>

 <p><a
 href='http://www.springer.com/engineering/circuits+&amp;+systems/book/978-1-4419-1538-2'>Design
 and Verification of Microprocessor Systems for High-Assurance
 Applications</a>, David S. Hardin, ed.  <a
 href='http://www.springer.com'>Springer</a>, 2010.
 Quoting from the abstract:

 <blockquote>
 This book examines several leading-edge design and verification
 technologies that have been successfully applied to microprocessor
 systems  for high-assurance applications at various levels -- from
 arithmetic circuits to microcode to instruction sets to operating
 systems to applications. We focus on recent hardware, software, and
 system designs that have actually been built and deployed, and feature
 systems that have been certified at high Evaluation Assurance Levels,
 namely the Rockwell Collins AAMP7G microprocessor (EAL7) and the Green
 Hills INTEGRITY-178B separation kernel (EAL6+). The contributing
 authors to this book have endeavored to bring forth truly new material
 on significant, modern design and verification efforts; many of the
 results described herein were obtained only within the past year.
 </blockquote>

 </p>

 <p>Several chapters in this book describe ACL2 proof developments.</p>

 <ul>

 <li>ACL2 and Its Applications to Digital System
 Verification, Kaufmann and Moore, pp 1-22</li>

 <li>A Mechanically Verified Commercial SRT Divider,
 David M. Russinoff, pp 23-64</li>

 <li>Use of Formal Verification at Centaur Technology,
 Warren A. Hunt, Jr., Sol Swords, Jared Davis, and
 Anna Slobodova, pp 65-88</li>

 <li>Formal Verification of Partition Management for
 the AAMP7G Microprocessor, Matthew M. Wilding,
 David A. Greve, Raymond J. Richards, and David
 S. Hardin, pp 175-192</li>

 <li>Modeling and Security Analysis of a Commercial
 Real-Time Operating System Kernel, Raymond
 J. Richards, pp 301-322</li>

 </ul>

 <h3>Book about formal floating-point hardware verification</h3>

 <p><a href='https://www.springer.com/gp/book/9783319955124'>Formal
   Verification of Floating-Point Hardware Design: A Mathematical
   Approach</a>, David
   M. Russinoff.  <a href='http://www.springer.com'>Springer</a>, 2019.
   In the author's words:

 <blockquote>
  This is the first book to focus on the problem of ensuring the correctness
  of floating-point hardware designs through mathematical methods. It advances
  a verification methodology based on a unified theory of register-transfer
  logic and floating-point arithmetic that has been developed and applied to
  the formal verification of commercial floating-point units over the course
  of more than two decades, during which the author was employed by several
  major microprocessor design companies. The entire theory and all
  applications reported have been formalized and mechanically verified with
  ACL2.
 </blockquote>

 </p>")

(defxdoc pub-papers
  :parents (publications)
  :short "Papers Involving ACL2"
  :long "<p>The best introduction to ACL2 is <i><a href='@(`(:raw (docpath
 \"acl2-books/car/index.html\"))`)'>Computer-Aided Reasoning: An
 Approach</a></i>; see @(see pub-books).  But if you prefer to read papers on
 the Web, see the papers listed in the subtopics of this @(see documentation)
 topic.  In particular, we recommend the first two papers in @(see
 pub-overviews).</p>

 <p>Typical formalization problems raise many issues that are not yet adequately
 addressed in ACL2 (or any other mechanized formal system).  If you are trying
 to formalize a problem in ACL2, you may well have to formalize some ideas for
 the first time, while extending the work of others.  It is often helpful to
 separate the issues involved in your problem and to try to find papers below
 that seem likely to touch upon some of those same issues.  Then look at those
 papers for ideas about how to deal with your problems.  A comprehensive
 set of case studies is presented in <i><a href='@(`(:raw (docpath
 \"acl2-books/acs/index.html\"))`)'>Computer-Aided Reasoning:  ACL2 Case
 Studies\"</a></i>; see @(see pub-books).</p>

 <p>Several of the papers listed contain links to ACL2 scripts.</p>

 ")

(xdoc::order-subtopics pub-papers nil t)

(defxdoc pub-overviews
  :parents (pub-papers)
  :short "Overviews"
  :long "
 <ul>
 <li><a href='http://www.cs.utexas.edu/users/moore/publications/how-to-prove-thms/index.html'>About ACL2</a></li>

 <li><a href='@(`(:raw (docpath \"bkm96.pdf\"))`)'>
 ACL2 Theorems about Commercial Microprocessors</a>, Bishop Brock, Matt
 Kaufmann and J Moore, in M. Srivas and A. Camilleri (eds.)  <i>Proceedings of
 Formal Methods in Computer-Aided Design (FMCAD'96)</i>, Springer-Verlag,
 pp. 275-293, 1996.  The paper sketches the system and two industrial
 applications: the AMD5K86 floating-point division proof and the Motorola CAP
 DSP model.</li>

 <li><a href='@(`(:raw (docpath \"km97.pdf\"))`)'>An
 Industrial Strength Theorem Prover for a Logic Based on Common Lisp</a>
 Matt Kaufmann and J Moore, <i>IEEE Transactions on Software Engineering</i>
 <b>23</b>(4), April 1997, pp. 203-213.  We discuss how we scaled up the Nqthm
 (&ldquo;Boyer-Moore&rdquo;) logic to Common Lisp, preserving the use of total functions
 within the logic but achieving Common Lisp execution speeds, via the
 introduction of &ldquo;guards.&rdquo;</li>

 <li><a href='http://www.cs.utexas.edu/users/moore/publications/hyper-card.html'>Hyper-Card for ACL2 Programming</a>
 by Matt Kaufmann and J Moore.  This is a quick reference sheet with lots of hyper-text links to the
 online documentation.  It also contains a gentle introduction to Lisp programming.</li>

 <li>A Computational Logic for Applicative Common Lisp, Matt Kaufmann and J Moore.  In: A
 Companion to Philosophical Logic, D. Jacquette (ed.), Blackwell Publishers,
 pp. 724-741, 2002.</li>

 <li><a
 href='@(`(:raw (docpath \"km94.pdf\"))`)'>Design
 Goals of ACL2</a>, Matt Kaufmann and J Moore, CLI Technical Report 101,
 Computational Logic, Inc., 1717 West Sixth Street, Suite 290, Austin, TX
 78703, 1994.  This is an early report identifying aspects of Nqthm of special
 concern during the design of ACL2.</li>

 <li><a
 href='http://sunsite.informatik.rwth-aachen.de/Publications/CEUR-WS//Vol-192/paper01.pdf'>Maintaining
 the ACL2 Theorem Proving System</a>, Matt Kaufmann and J Strother Moore.  Invited
 talk.  <i><a href='http://CEUR-WS.org/Vol-192/'>Proceedings of the FLoC'06 Workshop on Empirically Successful
 Computerized Reasoning, 3rd International Joint Conference on Automated
 Reasoning</a></i> (G. Sutcliffe, R. Schmidt, and S. Schulz, eds.), CEUR Worksho
 Proceedings Vol. 192, Seattle, Washington, August 2006.</li>

 <li><a href='http://www.rac.es/ficheros/doc/00156.pdf'>Some Key Research Problems in Automated Theorem Proving for Hardware and
 Software Verification</a>, Matt Kaufmann and J Strother Moore.
 <i>Revista de la Real Academia de Ciencias (RACSAM)</i>, Vol. 98, No. 1, pp. 181--196, 2004.
 Spanish Royal Academy of Science.</li>

 <li>ACL2 Support for Verification Projects, Matt Kaufmann.  Invited talk, Proc. 15th
 Intl. Conf. on Automated Deduction, ed.  C. Kirchner and H. Kirchner,
 Lec. Notes Artif. Intelligence 1421, Springer-Verlag, Berlin, 1998,
 pp. 220--238.</li>

 <li>An Industrial Strength Theorem Prover for a Logic Based on Common Lisp,
 Matt Kaufmann and J
 Moore).  IEEE Transactions on Software Engineering 23, no. 4, April 1997,
 203--213.</li>

 <li>Design Goals for ACL2, Matt Kaufmann and J Strother Moore.  In proceedings of:  Third
 International School and Symposium on Formal Techniques in Real Time and Fault
 Tolerant Systems, Kiel, Germany (1994), pp. 92-117.  Published by
 Christian-Albrechts-Universitat.</li>

 <li><a href='https://www.cs.utexas.edu/~kaufmann/talks/acl2-workshop-2014/acl2-14-kaufmann-moore.pdf'>Enhancements
     to ACL2 in Versions 6.2, 6.3, and 6.4</a>, Matt Kaufmann and J
     Strother Moore.  Here is a <a href='http://cs.ru.nl/~freekver/acl2_14_slides/talk.pdf'>link to the slides</a> from that talk
     at <a href='http://vsl2014.at/acl2/'>ACL2 Workshop 2014</a>.</li>

 <li><a href='http://www.cs.utexas.edu/users/kaufmann/talks/acl2-workshop-2013/index.html'>Enhancements
     to ACL2 in Versions 5.0, 6.0, and 6.1</a>, Matt Kaufmann and J
     Strother Moore.  Talk given
     at <a href='http://www.cs.uwyo.edu/~ruben/acl2-13'>ACL2 Workshop 2013</a>.</li>
 </ul>")

(defxdoc pub-foundations
  :parents (pub-papers)
  :short "Foundations"
  :long "
 <ul>

 <li><i><a
 href='@(`(:raw (docpath \"cs313k.pdf\"))`)'>CS313K Notes</a></i>, J Strother Moore, University of Texas at Austin, 2024</li>

 <li><a
 href='http://www.cs.utexas.edu/users/sandip/publications/clauseprocessors/main.html'>
 Integrating External Deduction Tools with ACL2</a>, Matt Kaufmann, J S. Moore,
 Sandip Ray, and Erik Reeber.
 <i>Journal of Applied Logic</i> (Special Issue: Empirically Successful
 Computerized Reasoning), Volume 7, Issue 1, March 2009, pp. 3--25.
 Published <a
 href='http://dx.doi.org/10.1016/j.jal.2007.07.002'>online</a>, DOI
 10.1016/j.jal.2007.07.002.
 <a href='http://www.cs.utexas.edu/users/sandip/publications/external/main.html'>Preliminary version</a> in C. Benzmueller,
 B. Fischer, and G. Sutcliffe (eds.), Proceedings of the 6th
 International Workshop on the Implementation of Logics (IWIL 2006),
 Phnom Penh, Cambodia, November 2006, pages 7-26.  Volume 212 of <a
 href='http://ceur-ws.org'>CEUR Workshop Proceedings</a>.</li>

 <li>An Integration of HOL and ACL2, Michael J.C. Gordon, Warren
 A. Hunt, Jr., Matt Kaufmann, and James Reynolds.  In <i>Proceedings of <a href='http://www.cs.utexas.edu/users/hunt/FMCAD/FMCAD06/'>Formal Methods in
 Computer-Aided Design (FMCAD'06)</a></i> (A. Gupta and P. Manolios, eds.).
 IEEE Computer Society Press, pp. 153-160, November, 2006.  Slides are available
 <a
 href='http://www.cs.utexas.edu/users/hunt/FMCAD/FMCAD06/presentations/FMCAD-2006-Wednesday/Session2-Hunt.pdf'>here</a>.<br/>
 See also:  An Embedding of the ACL2 Logic in HOL, Michael J.C. Gordon, Warren
 A. Hunt, Jr., Matt Kaufmann, and James Reynolds.  In P. Manolios and M. Wilding
 (eds.), <a href='http://www.lulu.com/content/380599'>Proceedings</a> of the <a
 href='http://www.ccs.neu.edu/home/pete/acl206/'>6th International
 Workshop on the ACL2 Theorem Prover and Its Applications (ACL2 2006)</a>,
 Seattle, WA, August 2006, pages 40-46.  Proceeding have also been <a
 href='https://dl.acm.org/doi/proceedings/10.1145/1217975'>published in the ACM
 Digital Library</a>.  Copyright ACL2 Steering Committee.</li>

 <li>Integrating CCG analysis into ACL2, Matt Kaufmann, Panagiotis Manolios, J Moore, and
 Daron Vroon).  <i>Proceedings of <a href='http://www.easychair.org/FLoC-06/WST.html'>The Eighth International Workshop on
 Termination (WST 2006)</a></i>,
 August, 2006.</li>

 <li><a href='http://www.cs.utexas.edu/users/sandip/publications/tail/main.html'>Quantification
 in Tail-recursive Function Definitions</a>, Sandip Ray.  In P. Manolios and M. Wilding
 (eds.), <a href='http://www.lulu.com/content/380599'>Proceedings</a> of the <a
 href='http://www.ccs.neu.edu/home/pete/acl206/'>6th International Workshop on
 the ACL2 Theorem Prover and Its Applications (ACL2 2006)</a>, Seattle, WA,
 August 2006, pages 95-98.  Proceeding have also been <a
 href='https://dl.acm.org/doi/proceedings/10.1145/1217975'>published in the ACM
 Digital Library</a>.  Copyright ACL2 Steering Committee.</li>

 <li><a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2002/contrib/manolios-kaufmann/total-order.pdf'>Adding a Total Order to ACL2</a>, M. Kaufmann and P. Manolios.  In
 <a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2002/'>Proceedings of ACL2 Workshop 2002</a>.</li>

 <li><a href='@(`(:raw (docpath \"stobj/main.pdf\"))`)'>Single-Threaded Objects in ACL2</a>, Robert
 Boyer and J Moore.  Single-threaded objects in ACL2 are structures that have
 the normal &ldquo;copy-on-write&rdquo; applicative semantics one expects in a
 functional programming language but which are implemented by destructive
 modification.  The axiomatic &ldquo;story&rdquo; is consistent with the implementation
 because syntactic restrictions are enforced which insure that only the
 modified structure is subsequently referenced.  Single-threaded objects (or
 &ldquo;@(see stobj)s&rdquo;) are particularly useful in modeling microprocessors, where the
 state of the processor is modeled as a stobj.</li>

 <li><a href='@(`(:raw (docpath \"encap-story.pdf\"))`)'>Structured Theory Development for a Mechanized
 Logic</a>, M. Kaufmann and J Moore, <i>Journal of Automated Reasoning</i>
 <b>26</b>, no. 2 (2001), pp. 161-203.  This paper
 presents a precise development of the <tt>encapsulate</tt> and
 <tt>include-book</tt> features of ACL2 and gives careful proofs of the
 high-level correctness properties of these ACL2 structuring mechanisms.</li>

 <li><a href='@(`(:raw (docpath \"km97a.pdf\"))`)'>A
 Precise Description of the ACL2 Logic</a>, Matt Kaufmann and J Moore, April,
 1998. This paper is a working draft of a precise description of the base
 logic.  The draft does not describe the theorem prover or the system; it is a
 dry mathematical document describing the logic from first principles.  At the
 moment the description omits encapsulation, multiple values, property lists,
 arrays, state, and macros.</li>

 <li><see topic='ACL2____TOP'>The ACL2 User's Manual</see>.  Originally written
 by Matt Kaufmann and J Moore, it now includes contributions from ACL2 users,
 in particular to document many ACL2 @(see books).  The user's manual is
 a vast hypertext document.</li>

 </ul>")

(defxdoc pub-capabilities
  :parents (pub-papers)
  :short "ACL2 Capabilities"
  :long "
 <ul>

 <li><a href='http://www.cs.utexas.edu/users/kaufmann/papers/patterned-congruences-itp.pdf'>Rough Diamond: An Extension of Equivalence-based Rewriting</a>, Matt
 Kaufmann and J Strother Moore.  Proceedings of ITP 2014,
 5th Conference on Interactive Theorem Proving, Gerwin Klein and Ruben Gamboa, editors.
 LNCS 8558 pp. 537-542, Springer International Publishing, 2014.  Also see
 <a href='http://dx.doi.org/10.1007/978-3-319-08970-6_35'>http://dx.doi.org/10.1007/978-3-319-08970-6_35</a>.</li>

 <li>A Futures Library and Parallelism Abstractions for a Functional
 Subset of Lisp, David L. Rager, Warren A. Hunt, Jr. and Matt Kaufmann.
 In <a href='http://www.european-lisp-symposium.org/ELS2011.pdf'>Proceedings
 of ELS 2011 (4th European Lisp Symposium)</a>, pp. 13--16, March 31 -- April 1,
 2011, Hamburg, Germany.  This paper is relevant to ACL2(p), the
   experimental extension of ACL2 supporting parallel evaluation and
   proof (see @(see parallelism)).</li>

 <li><a href='http://link.springer.com/article/10.1007/s10817-007-9095-9'>Rewriting with Equivalence Relations in ACL2</a>,
 Bishop Brock, Matt Kaufmann, and J Strother Moore.
 Journal of Automated Reasoning 40 (2008), pp. 293-306.</li>

 <li><a href='http://www.cs.utexas.edu/users/kaufmann/papers/kaufmann-moore-proof-debugging.pdf'>Proof Search Debugging Tools in ACL2</a>, Matt Kaufmann
   and J Strother Moore.  Unpublished, but presented in a talk at
   <i>Tools and Techniques for Verification
   of System Infrastructure, A Festschrift in honour of Prof. Michael
   J. C. Gordon FRS</i> (Richard Boulton, Joe Hurd, and Konrad Slind,
   organizers).  March 25-26, 2008, Royal Society, London.</li>

 <li><a href='http://www.cs.utexas.edu/users/kaufmann/papers/defexec/index.html'>Efficient execution in an automated reasoning environment</a>, David A. Greve, Matt
 Kaufmann, Panagiotis Manolios, J Strother Moore, Sandip Ray, Jose' Luis
 Ruiz-Reina, Rob Sumners, Daron Vroon and Matthew Wilding.  <a href='http://journals.cambridge.org/action/displayIssue?jid=JFP&amp;volumeId=18&amp;issueId=01'>Journal
 of Functional Programming, Volume 18, Issue 01, January 2008</a>.  Cambridge
 University Press.</li>

 <li>Double Rewriting for Equivalential Reasoning in ACL2, Matt Kaufmann and J
 Strother Moore.  In P. Manolios and M. Wilding
 (eds.), <a href='http://www.lulu.com/content/380599'>Proceedings</a> of the <a
 href='http://www.ccs.neu.edu/home/pete/acl206/'>6th International
 Workshop on the ACL2 Theorem Prover and Its Applications (ACL2 2006)</a>,
 Seattle, WA, August 2006, pages 103-106.  Proceeding have also been <a
 href='https://dl.acm.org/doi/proceedings/10.1145/1217975'>published in the ACM
 Digital Library</a>.  Copyright ACL2 Steering Committee.</li>

 <li><a href='@(`(:raw (docpath \"non-linear.ps\"))`)'>Linear and Nonlinear Arithmetic in ACL2</a>, Warren A. Hunt Jr.,
 Robert Bellarmine Krug, and J Moore.  In <a href='http://www.di.univaq.it/charme2003/'>CHARME 2003</a>,
 D. Geist (ed.), Springer Verlag LNCS 2860, pp. 319-333, 2003.
 This paper describes the mechanization of linear and nonlinear
 arithmetic in ACL2.</li>

 <li><a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2004/contrib/hunt-krug-moore/nonlinear-overview.pdf'>Integrating Nonlinear Arithmetic into ACL2</a>, Warren A. Hunt Jr.,
 Robert Bellarmine Krug, and J Moore.  In <a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2004/'>Proceedings of
 ACL2 Workshop 2004</a>.
 This paper presents an overview of the integration of a
 nonlinear arithmetic reasoning package into ACL2.</li>

 <li><a href='@(`(:raw (docpath \"meta-05.pdf\"))`)'>Meta Reasoning in ACL2</a>, Warren A. Hunt Jr, Matt Kaufmann, Robert
 Bellarmine Krug, J Moore, and Eric W. Smith.  In <a href='https://link.springer.com/book/10.1007/11541868'>18th
 International Conference on Theorem Proving in Higher Order
 Logics: TPHOLs 2005</a>, J. Hurd and T. Melham (eds.), Springer
 Lecture Notes in Computer Science, 3603, pp. 163--178, 2005.
 This paper describes the variety of meta-reasoning facilities
 in ACL2.</li>

 </ul>")

(defxdoc pub-utilities
  :parents (pub-papers)
  :short "Utilities"
  :long "
 <ul>

 <li><a href='http://www.cs.utexas.edu/users/sandip/publications/defpun-exec/main.html'>
 Attaching Efficient Executability to Partial Functions in ACL2</a>,
 Sandip Ray.
 In M. Kaufmann and J S. Moore (eds.), <a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2004/'>5th
 International Workshop on the ACL2 Theorem Prover and Its Applications (ACL2
 2004)</a>, Austin, TX, November 2004.</li>

 <li><a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2003/contrib/kaufmann/paper.pdf'>A Tool for Simplifying Files of ACL2 Definitions</a>, Matt Kaufmann.  In
 <a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2003/'>Proceedings
 of ACL2 Workshop 2003</a>; also see @(see community-books) directory
 <tt>books/workshops/2003/kaufmann/</tt>.</li>

 <li>ACL2 Interaction via Emacs, Bishop Brock, 1998.  This is a collection
 of Emacs programs to speed up interaction between ACL2 and Emacs.  If you
 typically interact with ACL2 via an Emacs buffer, you may be surprised to
 know that up to half of the time you spend waiting for an ACL2 command to
 complete is due to Emacs display overhead.  This package includes freely
 distributable source code for two effective approaches to reducing this
 overhead.  The first approach is very general and provides pretty good
 results.  The other approach is a bit of a hack, but practically eliminates
 display overhead for long ACL2 runs.  To try these out, download the
 following file.  You should name the file <tt>acl2-emacs.tar.gz</tt>.
 After downloading it, decompress and untar it with

 @({% tar -xvzf acl2-emacs.tar.gz})

 and read the enclosed note in <tt>report.ps</tt>.  Here is the file to
 download: <a href='@(`(:raw (docpath
 \"others/acl2-emacs.tar.gz\"))`)'>acl2-emacs.tar.gz</a></li>

 <li>Infix Printing, Mike Smith, 1998.

 An infix syntax for ACL2 has been implemented by Mike Smith.  Two
 capabilities are supported.

 <ul>

 <li><i>IACL2</i> is an infix version of the ACL2
 theorem proving system that performs I/O in infix
 format.  It is intended to make initial
 experiments with ACL2 somewhat simpler for those unfamiliar with or
 opposed to Lisp prefix syntax.  (It is not an interface for experts, as
 some of the more advanced aspects of ACL2 are not supported by the
 infix parser.)  Some examples of the syntax:
 @({
     Function idiv (m : integer, n : integer | n ~~= 0)
      { ifix ( m/n ) };

     /* Idiv takes two integer arguments, the second of which cannot = zero */

     Theorem distributivity-of-minus-over-plus
      {-(x + y) = -x + -y};

     Theorem car-nth-0 { consp(x) -> x.car = x[0] };
 })</li>

 <li>We provide formatting support to help the user publish ACL2 event
 files.  The syntax produced is either standard ACL2 or &ldquo;conventional&rdquo;
 infix mathematical notation with formatted comments and
 doc-strings. For example, in LaTeX mode comments are formatted as
 running text, events are indexed and substitutions are made of LaTeX
 mathematical symbols for various functions.  In HTML mode, cross
 references are created from function usage to definition.  Other ouput
 modes include Scribe and ASCII text. The formatting conventions are
 user extensible.</li>

 </ul>

 For more information, see the
 <a href='http://www.cs.utexas.edu/users/moore/infix/README.html'>README overview</a>.</li>

 </ul>")

(defxdoc pub-data-structures
  :parents (pub-papers)
  :short "Data Structures"
  :long "
 <ul>

 <li><a href='http://www.cs.utexas.edu/users/jared/osets/Web/'>Finite set theory based on fully ordered lists</a>, by Jared Davis,
 describes the set theory implementation in <tt>books/finite-set-theory/osets/</tt>.  In this
 library, set equality is just ACL2's 'equal' and the typical set
 operations (union, intersection, difference, cardinality) are
 linear-time and efficiently implemented.  A fairly complete set of set
 operations and rewrite rules are provided, and 'pick a point' proofs
 can be used to show subset relations.  Macros allow the quick
 introduction of functions to quantify predicates over sets (e.g.,
 'all-less-than'), and map functions over sets (e.g.,
 'cons-onto-each').  More information and
 slides are also available at <a
 href='http://www.cs.utexas.edu/users/jared/osets/Web/'>the above page</a>.</li>

 <li><a href='@(`(:raw (docpath \"finite-set-theory/report.ps\"))`)'>Finite Set Theory in ACL2</a>, by J
 Strother Moore, describes some of the features available in the
 distributed book <tt>books/finite-set-theory/set-theory.lisp</tt>.  The book provides
 hereditarily finite sets built from ACL2 objects.  Sets are represented by
 lists.  Sets may contain sets as elements.  The usual primitives -- including
 those for dealing with functions as sets of ordered pairs -- are defined and
 lemmas are proved providing many algebraic properties of finite set theory.
 Some common proof strategies are codified and macros are provided for
 defining functions that construct certain sets from others.  This book is
 just a start at what could easily turn into a major effort to support finite
 set theory more completely.</li>

 <li><a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2002/contrib/kaufmann-sumners/rcd.pdf'>Efficient
 Rewriting of Data Structures in ACL2</a>, M. Kaufmann and R. Sumners.
 In <a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2002/'>Proceedings of
 ACL2 Workshop 2002</a>  This paper describes the so-called 'records books',
 distributed in <tt>books/misc/records.lisp</tt> and <tt>books/misc/records0.lisp</tt>.</li>

 <li>An Exercise in Graph Theory, J Moore, Chapter 5 of <a
 href='@(`(:raw (docpath \"acl2-books/acs/index.html\"))`)'>Computer-Aided Reasoning: ACL2 Case
 Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer, 2000.
 (ACL2 scripts are available from
   directory <tt>books/workshops/1999/graph/</tt> of the
 community books, hence available at the
 <a href='https://github.com/acl2/acl2'>acl2-books project website</a>.)
 The article formalizes and proves the correctness of several
 simple algorithms for determining whether a path exists between two nodes of
 a finite directed graph.  The ACL2 scripts referenced here provide the full
 details of the results described in the article along with solutions to all
 the exercises in the article.</li>

 <li><a href='http://www.lim.com/~ruben/research/papers/powerlists.html'>
 Defthms About Zip and Tie: Reasoning About Powerlists in ACL2</a>, Ruben
 Gamboa, University of Texas Computer Sciences Technical Report No. TR97-02,
 February, 1998.  This work is based on Jay Misra's &ldquo;powerlist&rdquo; device, a
 data structure well-suited to recursive, data-parallel algorithms.  A
 generalization of powerlists is formalized in ACL2 by Gamboa and used to
 prove a variety of algorithm correct, including several sorting algorithms
 (including bitonic and Batcher), a grey-code sequence generator, and a
 carry-lookahead adder.  ACL2 event lists are linked to the URL above.</li>

 <li><a href='http://www.lim.com/~ruben/research/papers/fft.html'> Mechanically
 Verifying the Correctness of the Fast Fourier Transform in ACL2</a>, Ruben
 Gamboa, in Third International Workshop on Formal Methods for Parallel
 Programming: Theory and Applications (FMPPTA), 1998.  This paper is based on
 Jay Misra's work on &ldquo;powerlists&rdquo; (above) and formalizes Misra's
 stunningly simple proof of the correctness of an FFT algorithm implemented
 with powerlists.  The URL above links to an ACL2 event script as well.</li>

 <li><a
 href='@(`(:raw (docpath \"others/defstructure-brock.ps\"))`)'>Defstructure
 for ACL2</a>, Bishop Brock, December, 1997.  This paper serves as
 documentation for the ACL2 <tt>defstructure</tt> book, which provides a
 &ldquo;record facility&rdquo; similar to Common Lisp's <tt>defstruct</tt> and
 Nqthm's <tt>add-shell</tt>.</li>

 </ul>")

(defxdoc pub-processor-models
  :parents (pub-papers)
  :short "Processor Modeling and Hardware Verification"
  :long "
 <p>See also the previously mentioned book, <i>Design
 and Verification of Microprocessor Systems for High-Assurance
 Applications</i> (see @(see pub-books)), for a variety of papers by various authors on
 processing modeling in ACL2 (and other systems).</p>

 <ul>

 <li><a href='https://www.ncbi.nlm.nih.gov/pmc/articles/PMC5597723/pdf/rsta20150399.pdf'>Industrial
 Hardware and Software Verification with ACL2</a>.  Warren A. Hunt,
 Jr., Matt Kaufmann, J Strother Moore, and Anna Slobodova.
 In <i>Verified Trustworthy Software Systems</i> (Gardner, P., O'Hearn,
 P., Gordon, M., Morrisett, G. and Schneider, F.B., Eds), Philosophical
 Transactions A, vol 374, Royal Society Publishing, September, 2017.</li>

 <li>Using x86isa for Microcode Verification. Shilpi Goel and Rob
 Sumners. In the <a href='https://www.cl.cam.ac.uk/~jrh13/spisa19.html'>Workshop on Instruction Set Architecture
 Specification</a>.</li>

 <li>
 <a
 href='https://repositories.lib.utexas.edu/handle/2152/75087'>A
 Hierarchical Approach to Formal Modeling and Verification of
 Asynchronous Circuits</a>. C. K. Chau. Department of Computer
 Science, The University of Texas at Austin. Ph.D. dissertation, May
 2019.</li>

 <li>
 <a
 href='http://www.cs.utexas.edu/users/ckcuong/Publications/A%20Hierarchical%20Approach%20to%20Self-Timed%20Circuit%20Verification.pdf'>A
 Hierarchical Approach to Self-Timed Circuit Verification</a>.
 C. Chau, W. A. Hunt Jr., M. Kaufmann, M. Roncken, and I. Sutherland. In Proceedings of
 the 25th IEEE International Symposium on Asynchronous Circuits and Systems (<a
 href='http://www.async2019.jp'>ASYNC 2019</a>),
 Hirosaki, Japan, May 2019, pages 105-113. <a
 href='http://www.ieee.org'>IEEE</a>.</li>

 <li>
 <a
 href='https://ieeexplore.ieee.org/document/8589984'>Data-Loop-Free Self-Timed Circuit
 Verification</a>.
 C. Chau, W. A. Hunt Jr., M. Kaufmann, M. Roncken, and I. Sutherland. In Proceedings of
 the 24th IEEE International Symposium on Asynchronous Circuits and Systems (<a
 href='http://asyncsymposium.org/async2018/'>ASYNC 2018</a>),
 Vienna, Austria, May 2018, pages 51-58. <a
 href='http://www.ieee.org'>IEEE</a>.</li>

 <li>
 <a href='https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?ACL22018.6'>Adding
 32-bit Mode to the ACL2 Model of the x86 ISA</a>. Alessandro
 Coglio and Shilpi Goel. In Proceedings of the 15th International
 Workshop on the ACL2 Theorem Prover and Its Applications (ACL2
 2018).
 </li>

 <li>
 <a href='https://arxiv.org/abs/1705.01225v1'>The x86isa Books: Features,
 Usage, and Future Plans</a>. Shilpi Goel. In Proceedings of the 14th
 International Workshop on the ACL2 Theorem Prover and Its Applications
 (ACL2 2017).
 </li>

 <li>
 <a href='https://repositories.lib.utexas.edu/handle/2152/46437'>Formal
 Verification of Application and System Programs Based on a Validation
 x86 ISA Model</a>. Shilpi Goel. Department of Computer Science, The
 University of Texas at Austin. Ph.D. dissertation, December 2016.
 </li>

 <li>
 <a href='https://link.springer.com/chapter/10.1007%2F978-3-319-48628-4_8'>Engineering
 a Formal, Executable x86 ISA Simulator for Software
 Verification</a>. Shilpi Goel, Warren A. Hunt, Jr., and Matt
 Kaufmann. In Provably Correct Systems (ProCoS), 2017.
 </li>

 <li>
 <a href='http://dx.doi.org/10.1109/FMCAD.2014.6987600'>Simulation and
 Formal Verification of x86 Machine-Code Programs That Make System
 Calls</a>. Shilpi Goel, Warren A. Hunt, Jr., Matt Kaufmann, and
 Soumava Ghosh. In Formal Methods in Computer-Aided Design (FMCAD),
 2014.
 </li>

 <li>
 <a href='http://dx.doi.org/10.1007/978-3-642-54108-7_12'>Automated
 Code Proofs on a Formal Model of the x86</a>. Shilpi Goel and Warren
 A. Hunt, Jr. In Verified Software: Theories, Tools, Experiments
 (VSTTE), 2013.
 </li>

 <li> <a href='https://arxiv.org/abs/1304.7858'>Abstract Stobjs and
 Their Application to ISA Modeling</a>. Shilpi Goel, Warren A. Hunt,
 Jr., and Matt Kaufmann. In Proceedings of the 11th International
 Workshop on the ACL2 Theorem Prover and Its Applications (ACL2 2013).
 </li>

 <li>
 <a
 href='http://www.cs.utexas.edu/~sandip/publications/isqed-10/main.html'>Modeling
 and Verification of Industrial Flash Memories</a>.  S. Ray, J. Bhadra,
 T. Portlock, and R. Syzdek.  In P. Chatterjee and K. Gadepally,
 editors, Proceedings of the <a href='http://www.isqed.org'>11th
 International Symposium on Quality Electronic Design (ISQED 2010)</a>,
 San Jose, CA, March 2010, pages 705-712.  <a
 href='http://www.ieee.org'>IEEE</a>.</li>

 <li>
 <a
 href='http://www.cs.utexas.edu/~sandip/publications/date-10/main.html'>Optimizing
 Equivalence Checking for Behavioral Synthesis</a>.  K. Hao, F. Xie,
 S. Ray, and J. Yang.  In <a
 href='http://www.date-conference.org'>Design, Automation &amp; Test in
 Europe (DATE 2010)</a>, Dresden, Germany, March 2010. <a
 href='http://www.ieee.org'>IEEE</a>. </li>

 <li>
 <a href='http://www.cs.utexas.edu/~sandip/publications/fmcad-09/main.html'>Connecting
 Pre-silicon and Post-silicon Verification</a>.
 S. Ray and W. A. Hunt, Jr.
 In <a
 href='http://fmv.jku.at/biere'>A. Biere</a> and <a
 href='http://research.synopsys.com/cgi-bin/bios.cgi?bid=19'>C.
 Pixley</a>, editors, Proceedings of the <a
 href='http://fmv.jku.at/fmcad09'>9th International Conference on
 Formal Methods in Computer-aided Design (FMCAD 2009)</a>, Austin, TX,
 November 2009, pages 160-163.  <a
 href='http://www.computer.org/portal/site/ieeecs'>IEEE Computer
 Society</a>.</li>

 <li>
 <a
 href='http://www.cs.utexas.edu/~sandip/publications/atva-09/main.html'>Formal
 Verification for High-Assurance Behavioral Synthesis</a>.
 S. Ray, K. Hao, Y. Chen, F. Xie, and J. Yang.
 In <a
 href='http://www.iist.unu.edu/~lzm'>Z. Liu</a> and <a
 href='http://www.cs.aau.dk/~apr'>A. P. Ravn</a>, editors, Proceedings
 of the <a href='http://www.iist.unu.edu/atva09'>7th International
 Symposium on Automated Technology for Verification and Analysis (ATVA
 2009)</a>, Macao SAR, China, October 2009, volume 5799 of <a
 href='http://www.springer.de/comp/lncs/index.html'>LNCS</a>, pages
 337-351.  <a href='http://www.springer.com'>Springer</a>.</li>

 <li>
 <a
 href='http://www.cs.utexas.edu/~sandip/publications/flash-nvm-08/main.html'>Abstracting
 and Verifying Flash Memories</a>, Sandip Ray and Jayanta Bhadra.  In K. Campbell, editor,
 Proceedings of the <a href='http://www.nvmts.org'>9th Non-Volatile
 Memory Technology Symposium (NVMTS 2008)</a>, Pacific Grove, CA,
 November 2008, pages 100-104.  <a
 href='http://www.ieee.org'>IEEE</a>.</li>

 <li>
 <a
 href='http://www.cs.utexas.edu/users/sandip/publications/flash-07/main.html'>A
 Mechanized Refinement Framework for Analysis of Custom Memories</a>,
 Sandip Ray and Jayanta Bhadra.
 In J. Baumgartner and <a
 href='http://www.cs.chalmers.se/~ms/'>M. Sheeran</a>, editors,
 Proceedings of the <a href='http://www.fmcad.org/2007'>7th
 International Conference on Formal Methods in Computer-aided Design
 (FMCAD 2007)</a>, Austin, TX, November 2007, pages 239-242. <a
 href='http://www.computer.org/portal/site/ieeecs'>IEEE Computer
 Society</a>.</li>

 <li>
 <a
 href='http://www.cs.utexas.edu/users/sandip/publications/voting-07/main.html'>Mechanized
 Certification of Secure Hardware Designs</a>, Sandip Ray and Warren
 A. Hunt, Jr.  In <a
 href='http://www.cerc.utexas.edu/~jay'>J. Bhadra</a>, <a
 href='http://mtv.ece.ucsb.edu/licwang/'>L. Wang</a>, and M. S. Abadir,
 editors, Proceedings of the <a href='http://mtv.ece.ucsb.edu/MTV/'>8th
 International Workshop on Microprocessor Test and Verification, Common
 Challenges and Solutions (MTV 2007)</a>, Austin, TX, December 2007.
 <a href='http://www.computer.org/portal/site/ieeecs'>IEEE Computer
 Society</a>.</li>

 <li><a href='http://www.russinoff.com/papers/paris.ps'>Formal Verification of Floating-Point RTL at AMD using the ACL2 Theorem Prover</a>,
 David Russinoff, Matt Kaufmann, Eric Smith, Robert Sumners.  17th IMACS World
 Congress: Scientific Computation, Applied Mathematics and Simulation.  July,
 2005.</li>

 <li><a href='http://www.cs.utexas.edu/users/sandip/publications/pipelines/main.html'>
 Deductive Verification of Pipelined Machines Using First-order
 Quantification</a>, Sandip Ray and Warren A. Hunt Jr.
 In R. Alur and D. A. Peled, editors, Proceedings of the
 16th International Conference on Computer-aided Verification (CAV 2004),
 Boston, MA, July 2004, volume 3117 of LNCS, pages 31-43.  Copyright <a
 href='http://www.springer.de/comp/lncs/index.html'>Springer-Verlag</a>.</li>

 <li><a href='http://www.cs.utexas.edu/users/kaufmann/dcc-slides.pdf'>Formal Verification
 of Microprocessors at AMD</a>, Arthur Flatau, Matt Kaufmann, David F. Reed, David Russinoff,
 Eric Smith, and Rob Sumners.  <a href='http://www.cs.chalmers.se/~ms/DCC02/Slides.html'>Proceedings of Designing Correct Circuits 2002</a>.</li>

 <li>High-Speed, Analyzable Simulators, David Greve, Matthew Wilding, and
 David Hardin, Chapter 8 of <a href='@(`(:raw (docpath \"acl2-books/acs/index.html\"))`)'>Computer-Aided
 Reasoning: ACL2 Case Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer,
 2000.
 (ACL2 scripts are available from
   directory <tt>1999/simulator/</tt> in the @(see community-books).)
 High-speed simulation models are routinely developed during the
 design of complex hardware systems in order to predict performance, detect
 design flaws, and allow hardware/software co-design.  Writing such an
 executable model in ACL2 brings the additional benefit of formal analysis;
 however, much care is required to construct an ACL2 model that is both fast
 and analyzable.  In this article, techniques are described for the
 construction of high-speed formally analyzable simulators in ACL2.  Their
 utility is demonstrated on a simple processor model.  The ACL2 scripts
 referenced here provide the full details of the results described in the
 article along with solutions to all the exercises in the article.</li>

 <li>Verification of a Simple Pipelined Machine Model, Jun Sawada, Chapter 9
 of <a href='@(`(:raw (docpath \"acl2-books/acs/index.html\"))`)'>Computer-Aided Reasoning: ACL2 Case
 Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer, 2000.
 (ACL2 scripts are available from
   directory <tt>1999/pipeline/</tt> in the @(see community-books).)
 An ACL2 model of a three-stage pipelined machine is defined,
 along with a model of the corresponding sequential machine.  Then a proof of
 the equivalence between the two machines is presented.  More importantly, the
 method of decomposing the proof applies to much more complicated pipelined
 architectures.  The ACL2 scripts referenced here provide the full details of
 the results described in the article along with solutions to all the
 exercises in the article.  </li>

 <li>Verification of Pipeline Circuits, Matt Kaufmann and David M. Russinoff, in
 <i><a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2000/'>Proceedings of
 ACL2 Workshop 2000</a></i>.</li>

 <li>The DE Language, Warren Hunt, Jr., Chapter 10 of <a
 href='@(`(:raw (docpath \"acl2-books/acs/index.html\"))`)'>Computer-Aided Reasoning: ACL2 Case
 Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer, 2000.
 (ACL2 scripts are available from
   directory <tt>1999/de-hdl/</tt> in the @(see community-books).)
 The DE language is an occurrence-oriented description language
 that permits the hierarchical definition of finite-state machines in the
 style of a hardware description language.  The syntax and semantics of the
 language are formalized and the formalization is used to prove the
 correctness of a simple hardware circuit.  Such formal HDLs have been used to
 prove properties of much more complicated designs.  The ACL2 scripts
 referenced here provide the full details of the results described in the
 article along with solutions to all the exercises in the article.</li>

 <li>Using Macros to Mimic VHDL, Dominique Borrione, Philippe Georgelin, and
 Vanderlei Rodrigues, Chapter 11 of <a
 href='@(`(:raw (docpath \"acl2-books/acs/index.html\"))`)'>Computer-Aided Reasoning: ACL2 Case
 Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer, 2000.
 (ACL2 scripts are available from
   directory <tt>1999/vhdl/</tt> in the @(see community-books).)
 The purpose of this project was to formalize a small
 synthesizable behavioral subset of VHDL, preserving as much as possible the
 syntactic flavor of VHDL and facilitating verification by symbolic simulation
 and theorem proving.  The ACL2 scripts referenced here provide the full
 details of the results described in the article along with solutions to all
 the exercises in the article.</li>

 <li><a href='http://hokiepokie.org/docs/efm.ps'>Efficent
 Simulation of Formal Processor Models</a>, Dave Hardin, Matt
 Wilding, and Dave Greve, Rockwell Collins, Inc., Advanced Technology Center,
 Cedar Rapids, IA, May, 1998.   This paper describes some &ldquo;hacks&rdquo; by which
 ACL2 array processing can be sped up to C speeds.  A simple processor model,
 comparable to the traditional &ldquo;small machine&rdquo; mentioned above, is used as
 the benchmark.  Native ACL2 achieves simulation speeds of about 19,000
 &ldquo;small machine&rdquo; instructions per second when executing this model.  After
 modifying ACL2 as described, the model is executed at slightly over 2 million
 instructions per second, comparable to a C model of the processor.
 Technically, the techniques used in this paper render ACL2 unsound because
 they assume (without the necessary syntactic checking) that ACL2 arrays are
 used in a single-threaded way.  However, the experiments done in this paper
 and the techniques used are extremely illuminating.  They also indicate
 modifications that could be made to ACL2 to provide the efficiency needed in
 industrial-scale modeling, while preserving soundness.  The paper is highly
 recommended.</li>

 <li><a href='http://hokiepokie.org/docs/concept.ps'>Transforming
 the Theorem Prover into a Digital Design Tool: From Concept Car to Off-Road
 Vehicle</a>, Dave Hardin, Matt Wilding and Dave Greve, in A. J. Hu and
 M. Y. Vardi (eds.) <i>Computer Aided Verification: 10th International
 Conference, CAV '98</i>, Springer-Verlag LNCS 1427, 1998.  The paper
 suggests ways to integrate theorem proving into the microprocessor design
 cycle.  The paper was presented at CAV '98.  During the talk, the authors
 demonstrated an ACL2 model of the ALU of the JEM1 (a silicon Java Virtual
 Machine) microprocessor, its transparent use to compute ALU results for a
 C-based simulation tool for the processor and ACL2 proofs about the ALU.
 This demonstration is not discussed in the paper but is indicative of the
 ideas in the paper.</li>

 <li><a href='@(`(:raw (docpath \"symsim.pdf\"))`)'>Symbolic Simulation: An ACL2 Approach</a>, J Moore,
 in G. Gopalakrishnan and P. Windley (eds.)
 <i>Proceedings of the Second International Conference on Formal Methods
 in Computer-Aided Design (FMCAD'98)</i>, Springer-Verlag LNCS 1522,
 pp. 334-350, November, 1998.
 (<a href='@(`(:raw (docpath \"symsim-script/index.html\"))`)'>
 ACL2 Script</a>) This paper advocates the idea of symbolic simulation of
 processor models, as a step from the familiar (namely, traditional simulation
 of C models of designs) to the unfamiliar (namely, proofs about formal
 models).  The papers demonstrates how ACL2 can provide a symbolic simulation
 capability for the &ldquo;small machine&rdquo; model.  Some interesting performance
 measures are also given.</li>

 </ul>")

(defxdoc pub-programming-languages
  :parents (pub-papers)
  :short "Programming Languages and Software Verification"
  :long "
 <ul>

 <li>
 <a
 href='http://www.cs.utexas.edu/~sandip/publications/information-flow-08/main.html'>Mechanized
 Information Flow Analysis through Inductive Assertions</a>, Warren A. Hunt, Jr., Robert Bellarmine Krug, Sandip Ray, and William
 D. Young.  In <a
 href='http://es.fbk.edu/people/cimatti'>A. Cimatti</a> and <a
 href='http://verify.stanford.edu/rjones'>R. B. Jones</a>, editors,
 Proceedings of the <a href='http://www.fmcad.org/2008'>8th
 International Conference on Formal Methods in Computer-aided Design
 (FMCAD 2008)</a>, Portland, OR, November 2008, pages 227-230.  <a
 href='http://www.computer.org/portal/site/ieeecs'>IEEE Computer
 Society</a>.</li>

 <li>
 <a href='http://groups.csail.mit.edu/pag/pubs/pittsfield-usenix2006-abstract.html'>Evaluating SFI for a CISC Architecture</a> by Stephen McCamant and Greg
 Morrisett. In 15th USENIX Security Symposium, (Vancouver, BC, Canada),
 August 2-4, 2006, pp. 209-224.  See also the <a
 href='http://people.csail.mit.edu/smcc/projects/pittsfield/'>project page</a>.</li>

 <li>
 <a href='@(`(:raw (docpath \"talks/marktoberdorf-08/index.html\"))`)'>Mechanized Operational
 Semantics</a> by J Moore (lectures given at Marktoberdorf Summer
 School 2008).  These lectures explain how to formalize an
 &ldquo;operational&rdquo; or &ldquo;state-transition&rdquo; semantics of a von Neumann
 programming language in a functional programming language.
 These lectures illustrate the techniques by formalizing a simple
 programming language called &ldquo;M1,&rdquo; for &ldquo;Machine (or Model) 1.&rdquo; It
 is loosely based on the Java Virtual Machine but has been simplified
 for pedagogical purposes.  They demonstrate the executability of M1
 models. Several styles of code proofs are developed, including direct
 (symbolic simulation) proofs based on Boyer-Moore &ldquo;clock functions&rdquo;
 and Floyd-Hoare inductive assertion proofs. Proofs are constructed
 only for the simplest of programs, namely an iterative factorial
 example.  But to illustrate a more realistic use of the model, the
 correctness proof for an M1 implementation of the Boyer-Moore fast
 string searching algorithm is discussed.</li>

 <li>
 <a
 href='https://www.ece.ufl.edu/wp-content/uploads/sites/119/publications/jar08.pdf'>A
 Mechanical Analysis of Program Verification Strategies</a>, Sandip Ray, Warren
 A. Hunt, Jr.  John Matthews, and J Strother Moore.  <a
 href='https://link.springer.com/journal/10817'>Journal of
 Automated Reasoning</a>. volume 40(4), May 2008, pages 245-269.  <a
 href='http://www.springer.com'>Springer</a>.</li>

 <li><a href='http://www.cs.utexas.edu/users/sandip/publications/symbolic-lpar/main.html'>
 Verification Condition Generation via Theorem Proving</a>, John Matthews, J
 S. Moore, Sandip Ray, and Daron Vroon.  In M. Hermann and
 A. Voronkov, editors, Proceedings of the 13th International Conference on Logic
 for Programming, Artificial Intelligence, and Reasoning (LPAR 2006), Phnom Penh,
 Cambodia, November 2006, volume 4246 of LNCS, pages 362-376.  Copyright <a
 href='http://www.springer.de/comp/lncs/index.html'>Springer-Verlag</a></li>

 <li><a href='http://www.ccs.neu.edu/home/pete/acl206/papers/pike.pdf'>A Verifying Core for a Cryptographic Language Compiler</a>, Lee Pike,
 Mark Shields, and John Matthews.  In P. Manolios and M. Wilding
 (eds.), <a href='http://www.lulu.com/content/380599'>Proceedings</a> of the <a
 href='http://www.ccs.neu.edu/home/pete/acl206/'>6th International
 Workshop on the ACL2 Theorem Prover and Its Applications (ACL2 2006)</a>,
 Seattle, WA, August 2006, pages 95-98.  Proceeding have also been <a
 href='https://dl.acm.org/doi/proceedings/10.1145/1217975'>published in the ACM
 Digital Library</a>.  Copyright ACL2 Steering Committee.
 See also <a
 href='http://www.cs.indiana.edu/~lepike/pub_pages/acl2.html'>the supporting
 materials</a>.</li>

 <li><a href='https://www.ece.ufl.edu/wp-content/uploads/sites/119/publications/fmcad04.pdf'>
 Proof Styles in Operational Semantics</a>, Sandip Ray and J S. Moore.
 In A. J. Hu and A. K. Martin,
 editors, Proceedings of the 5th International Conference on Formal Methods in
 Computer-aided Design (FMCAD 2004), Austin, TX, November 2004, volume 3312
 of LNCS, pages 67-81.  Copyright <a
 href='http://www.springer.de/comp/lncs/index.html'>Springer-Verlag</a>.</li>

 <li>Design Verification of a Safety-Critical Embedded Verifier, Piergiorgio
 Bertoli and Paolo Traverso, Chapter 14 of <a
 href='@(`(:raw (docpath \"acl2-books/acs/index.html\"))`)'>Computer-Aided Reasoning: ACL2 Case
 Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer, 2000.
 (ACL2 scripts are available from
   directory <tt>1999/embedded/</tt> in the @(see community-books).)
 This article shows the use of ACL2 for the design verification of
 a piece of safety-critical software, the Embedded Verifier.  The Embedded
 Verifier checks online that each execution of a safety-critical translator is
 correct. The translator is a component of a software system used by Union
 Switch and Signal to build trainborne control systems.  The ACL2 scripts
 referenced here provide the full details of the results described in the
 article along with solutions to all the exercises in the article.</li>


 <li>Compiler Verification Revisited, Wolfgang Goerigk, Chapter 15 of <a
 href='@(`(:raw (docpath \"acl2-books/acs/index.html\"))`)'>Computer-Aided Reasoning: ACL2 Case
 Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer, 2000.
 (ACL2 scripts are available from
   directory <tt>1999/compiler/</tt> in the @(see community-books).)
 This study illustrates a fact observed by Ken Thompson in his
 Turing Award Lecture: the machine code of a correct compiler can be altered
 to contain a Trojan Horse so that the compiler passes almost every test,
 including the so-called &ldquo;bootstrap test&rdquo; in which it compiles its own
 source code with identical results, and still be capable of generating
 &ldquo;bad&rdquo; code.  The compiler, the object code machine, and the experiments are
 formalized in ACL2.  The ACL2 scripts referenced here provide the full
 details of the results described in the article along with solutions to all
 the exercises in the article.</li>


 <li><a href='@(`(:raw (docpath \"tjvm/main.pdf\"))`)'>Proving Theorems about Java-like Byte Code</a>, J
 Moore, in E.-R. Olderog and B. Steffen (eds.) <i>Correct System Design ---
 Recent Insights and Advances</i>, LNCS: State-of-the-Art-Survey, Volume 1710,
 pp. 139--162, 1999).  This paper describes a formalization of an abstract
 machine very similar to the Java Virtual Machine but far simpler.  Techniques
 are developed for specifying the properties of classes and methods for this
 machine.  The paper illustrates two such proofs, that of a static method
 implementing the factorial function and of an instance method that
 destructively manipulates objects in a way that takes advantage of
 inheritance.  An <a href='@(`(:raw (docpath \"tjvm/index.html\"))`)'>ACL2 Script</a> is also available.</li>

 <li><a href='http://www.cs.utexas.edu/users/boyer/bm96.ps.gz'>Mechanized
 Formal Reasoning about Programs and Computing Machines</a>, Bob Boyer and J
 Moore, in R. Veroff (ed.), <i>Automated Reasoning and Its Applications:
 Essays in Honor of Larry Wos</i>, MIT Press, 1996.  This paper explains a
 formalization style that has been extremely successful in enabling
 mechanized reasoning about programs and machines, illustrated in ACL2.  This
 paper presents the so-called &ldquo;small machine&rdquo; model, an extremely simple
 processor whose state consists of the program counter, a RAM, an execute-only
 program space, a control stack and a flag.  The paper explains how to prove
 theorems about such models.  Accompanying the paper is an
 <a
 href='@(`(:raw (docpath \"small-machine.lisp\"))`)'>
 ACL2 Script</a>: After fetching this script, use @(tsee include-book) to
 load it into your ACL2 and then do @('(in-package \"SMALL-MACHINE\")').</li>

 </ul>")

(defxdoc pub-floating-point-arithmetic

; The following were html comments in
; https://www.cs.utexas.edu/~moore/publications/acl2-papers.html.

;<!--
;<li><a href='others/fp-README.html'>An ACL2 Library of Floating Point
;Arithmetic</a>, David M. Russinoff, Advanced Micro Devices, Inc.  This
;library was developed by David Russinoff at Advanced Micro Devices from 1996
;to 1998 in support of the mechanical verification of a number of floating
;point operations of the AMD-K5 (TM) and Athlon (TM) (aka AMD-K7)
;microprocessors.
;<P> -->

;<!-- This paper was withdrawn after AMD rescinded their permission to publish.
;But I am hoping that a cut down version of the paper will be released.
;<P>
;<li><a href='http://www.onr.com/user/russ/david/fadd.html'> A Case Study in
;Formal Verification of a Register-Transfer Logic with ACL2: The Floating
;Point Adder of the AMD-K7 Processor</a>, David Russinoff, Advanced Micro
;Devices, Inc., July, 1998.  One obstacle to mathematical verification of
;industrial hardware designs is that the commercial hardware description
;languages in which they are usually encoded are too complicated and poorly
;specified to be readily susceptible to formal analysis. As an alternative to
;these commercial languages, AMD has developed an RTL language for
;microprocessor designs that is simple enough to admit a clear semantic
;definition, providing a basis for formal verification. The paper describes a
;mechanical proof system for designs represented in this language, consisting
;of a translator to the ACL2 logical programming language and a methology for
;verifiying properties of the resulting programs using the ACL2 prover. As an
;illustration, the paper presents a proof of IEEE compliance of the floating
;point adder of the AMD-K7 processor.  The paper includes the RTL for a
;simplified version of the AMD-K7 floating-point adder.  -->

  :parents (pub-papers)
  :short "Floating Point Arithmetic"
  :long "
 <ul>

 <li><a href='@(`(:raw (docpath \"double-float.pdf\"))`)'>ACL2 Support for Floating-Point
 Computations</a>, M. Kaufmann and J S. Moore,
 <i>The Practice of Formal Methods: Essays in Honour of Cliff Jones, Part
 I</i> (Cavalcanti, A. and Baxter, J., Eds), Springer Nature Switzerland,
 Cham, pp 251-207, DOI https://doi.org/10.1007/978-3-031-66676-6_13, 2024.</li>

 <li><a href='http://www.russinoff.com/papers/fadd.html'>
 A Case Study in Formal Verification of Register-Transfer Logic with ACL2:
 The Floating Point Adder of the AMD Athlon Processor</a>, David Russinoff.
 Invited paper in Warren A. Hunt Jr. and
 Steven D. Johnson (eds.), <i>Proceedings of the Third International Conference on Formal Methods
 in Computer-Aided Design (FMCAD 2000)</i>, Springer-Verlag LNCS 1954, 2000.
 This is a proof of IEEE-compliance, as an application of a mechanical proof system for RTL designs based
 on ACL2.</li>

 <li>RTL Verification: A Floating-Point Multiplier, David M. Russinoff and
 Arthur Flatau, Chapter 13 of <a
 href='@(`(:raw (docpath \"acl2-books/acs/index.html\"))`)'>Computer-Aided Reasoning: ACL2 Case
 Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer, 2000.
 (ACL2 scripts are available from
   directory <tt>1999/multiplier/</tt> in the @(see community-books).)
 This article describes a mechanical proof system for designs
 represented in the RTL language of Advanced Micro Devices.  The system
 consists of a translator to ACL2 and a methodology for verifying properties
 of the resulting programs using the ACL2 prover.  The correctness of a simple
 floating-point multiplier is proved.  The ACL2 scripts referenced here
 provide the full details of the results described in the article along with
 solutions to all the exercises in the article.</li>

 <li><a href='@(`(:raw (docpath \"div-march-96.ps\"))`)'> A Mechanically Checked Proof of the
 Correctness of the Kernel of the AMD5K86 Floating-Point Division
 Algorithm</a>, J Moore, Tom Lynch, and Matt Kaufmann, <i>IEEE Transactions on
 Computers</i>, <b>47</b>(9), pp. 913-926, Sep., 1998.  This is the original (
 March, 1996) version of our paper describing the mathematical details of the
 proof that the FDIV microcode on the AMD K5 correctly implements IEEE
 floating point division.  The paper underwent extensive revision during the
 reviewing process.</li>

 <li><a href='http://www.onr.com/user/russ/david/k7-div-sqrt.html'> A
 Mechanically Checked Proof of IEEE Compliance of a Register-Transfer-Level
 Specification of the AMD K7 Floating Point Multiplication, Division and
 Square Root Instructions</a>, David Russinoff, Advanced Micro Devices, Inc.,
 January, 1998.  This paper is a <i>tour de force</i> in mechanical
 verification.  The paper describes a mechanically verified proof of
 correctness of the floating-point multiplication, division, and square root
 instructions of The AMD K7 microprocessor. The instructions, which are based
 on Goldschmidt's Algorithm, are implemented in hardware and represented by
 register-transfer level specifications, the primitives of which are logical
 operations on bit vectors. On the other hand, the statements of correctness,
 derived from IEEE Standard 754, are arithmetic in nature and considerably
 more abstract. Therefore, the paper develops a theory of bit vectors and
 their role in floating-point representations and rounding, extending previous
 work (below) in connection with the K5 FPU.  The paper then presents the
 hardware model and a rigorous and detailed proof of its correctness. All of
 the definitions, lemmas, and theorems have been formally encoded in the ACL2
 logic, and every step in the proof has been mechanically checked with the
 ACL2 prover.</li>

 <li><a href='http://www.onr.com/user/russ/david/fsqrt.html'>A Mechanically
 Checked Proof of IEEE Compliance of the AMD K5 Floating-Point Square Root
 Microcode</a>, David Russinoff, <i>Formal Methods in System Design</i>
 Special Issue on Arithmetic Circuits, 1997.  The paper presents a rigorous
 mathematical proof of the correctness of the FSQRT instruction of the AMD K5
 microprocessor. The instruction is represented as a program in a formal
 language that was designed for this purpose, based on the K5 microcode and
 the architecture of its FPU.  The paper proves a statement of its correctness
 that corresponds directly with the IEEE standard.  It also derives an
 equivalent formulation, expressed in terms of rational arithmetic, which has
 been encoded as a formula in the ACL2 logic and mechanically verified with
 the ACL2 prover. Finally, the paper describes a microcode modification that
 was implemented as a result of this analysis in order to ensure the
 correctness of the instruction.</li>

 </ul>")

(defxdoc pub-real-arithmetic
  :parents (pub-papers)
  :short "Real Arithmetic"
  :long "
 <ul>

 <li><a
 href='http://www.cs.uwyo.edu/~ruben/research/pdf/nsa.pdf'>Non-Standard
 Analysis in ACL2</a>, Ruben A. Gamboa and Matt Kaufmann, <i>Journal of Automated
 Reasoning</i> 27(4), 323-351, 2001.
 This paper describes
 ACL2(r), a version of ACL2 with support for the real and complex numbers. The
 modifications are based on non-standard analysis, which interacts better with
 the discrete flavor of ACL2 than does traditional analysis.  See
 below (discussion of a variant of ACL2 called &ldquo;ACL2(r)&rdquo;) or see @(see real)
 for more about ACL2(r).</li>

 <li>Modular Proof: The Fundamental Theorem of Calculus, Matt Kaufmann,
 Chapter 6 of <a href='acl2-books/acs/index.html'>Computer-Aided Reasoning:
 ACL2 Case Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer, 2000.
 (ACL2 scripts are available from
   directory <tt>1999/calculus/</tt> in the @(see community-books).)
 The article presents a modular top-down proof methodology and
 uses it to formalize and prove the Fundamental Theorem of Calculus.  The
 modular strategy works for both ACL2 and &ldquo;ACL2(r)&rdquo; (see above); the
 Fundamental Theorem is proved with ACL2(r).  The ACL2 scripts referenced here
 provide the full details of the results described in the article along with
 solutions to all the exercises in the article.</li>

 <li>Continuity and Differentiability, Ruben Gamboa, Chapter 18 of <a
 href='acl2-books/acs/index.html'>Computer-Aided Reasoning: ACL2 Case
 Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer, 2000.
 (ACL2 scripts are available from
   directory <tt>1999/analysis/</tt> in the @(see community-books).)
 This article shows how an extended version of ACL2 (named
 &ldquo;ACL2(r)&rdquo; and described below) can be used to reason about the real and
 complex numbers, using non-standard analysis.  It describes some
 modifications to ACL2 that introduce the irrational real and complex numbers
 into ACL2's number system.  It then shows how the modified ACL2 can prove
 classic theorems of analysis, such as the intermediate-value and mean-value
 theorems.  The ACL2(r) scripts referenced here provide the full details of
 the results described in the article along with solutions to all the
 exercises in the article.
 </li>

 <li>ACL2 supports the rational numbers but not the reals.  Starting with
 Version  2.5, however, a variant of ACL2 called &ldquo;ACL2(r)&rdquo; supports the real
 numbers by way of non-standard analysis.  ACL2(r) was produced by Ruben
 Gamboa from ACL2.  ACL2(r) can be built from the ACL2 sources (Versions 2.5
 and higher).  See the makefile for instructions for building ACL2(r).  For
 further acknowledgements and some technical details see the documentation
 topic @(see REAL) in the online documentation for ACL2.  ACL2 authors
 Kaufmann and Moore consider ACL2(r) Version  2.5 to be in &ldquo;beta release.&rdquo;
 They have tried to ensure that when ACL2 is built from the integrated source
 files, the result is a sound ACL2.  They are confident that ACL2(r) will
 eventually be sound and behave much as it does in the Version  2.5 release,
 but have not yet checked every detail of the integration.  For the
 foundations of ACL2(r), see Gamboa's Ph.D. dissertation <a
 href='http://www.lim.com/~ruben/research/thesis'> Mechanically Verifying
 Real-Valued Algorithms in ACL2</a> (UT, May, 1999).  The dissertation
 includes ACL2(r)-checked proofs of many fundamental properties of the real
 numbers, including such results as the continuity of <tt>e^x</tt>,
 Euler's identity, the basic identities of trigonometry, the intermediate
 value theorem, and others.</li>

 <li><a href='http://www.lim.com/~ruben/research/papers/sqrt.html'>Square
 Roots in ACL2: A Study in Sonata Form</a>, Ruben Gamboa, UTCS Tech Report
 TR96-34, November, 1996.  This paper describes a proof in ACL2 that <tt>(*
 x x)</tt> is never 2.  This was the beginning of Gamboa's journey into
 the ACL2 mechanization of non-standard analysis.</li>

 </ul>")

(defxdoc pub-concurrency
  :parents (pub-papers)
  :short "Concurrency"
  :long "
 <ul>

 <li><a href='@(`(:raw (docpath \"multi-v-uni.pdf\"))`)'>A Mechanically Checked Proof of a
 Multiprocessor Result via a Uniprocessor View</a>, J Moore, February, 1998.
 This paper presents an ACL2 proof that an n-processor concurrent system
 implements a non-blocking counter.  This paper illustrates one method for
 dealing with concurrency and nondeterminism in ACL2, by formalizing a
 compositional semantics for a shared-memory concurrent system.  (<a
 href='@(`(:raw (docpath \"multi-v-uni.lisp\"))`)'> ACL2 script</a>).</li>

 <li><a href='@(`(:raw (docpath \"wicache.pdf\"))`)'>An ACL2 Proof of Write Invalidate Cache
 Coherence</a>, J Moore, in A. J. Hu and M. Y. Vardi (eds.) <i>Computer Aided
 Verification: 10th International Conference, CAV '98</i>, Springer-Verlag
 LNCS 1427, pp. 29-38, 1998.   This paper presents a pedagogical example of
 the use of ACL2.  An extremely simple cache coherence property is formalized
 and proved.  The intended contribution of the paper is not in the realm of
 cache coherence -- the problem dealt with here is far too simple for that --
 but in demonstrating the ACL2 in a simple modeling project and in one
 approach to concurrency.  (<a href='@(`(:raw (docpath \"write-invalidate-cache/index.html\"))`)'>ACL2
 Scripts</a>)</li>

 <li><a
 href='@(`(:raw (docpath \"others/interactive-consistency-young.ps\"))`)'>Interactive
 Consistency in ACL2</a>, Bill Young, Computational Logic, Inc., March,
 1997.  This paper presents an ACL2 translation of Rushby's PVS improvement
 to Bevier and Young's Nqthm formalization of the Pease, Shostak and Lamport
 Oral Messages (&ldquo;Byzantine Generals&rdquo;) problem.</li>

 </ul>")

(defxdoc pub-model-checking-and-ste
  :parents (pub-papers)
  :short "Model Checking and Symbolic Trajectory Evaluation"
  :long "
 <ul>

 <li><a
 href='http://www.cs.utexas.edu/~sandip/publications/jar-09/main.html'>The
 Right Tools for the Job: Correctness of Cone of Influence Reduction
 Proved Using ACL2 and
 HOL4</a>,
 <a href='http://www.cl.cam.ac.uk/~mjcg'>M. J. C. Gordon</a>,
 <a href='http://www.cs.utexas.edu/~kaufmann'>M. Kaufmann</a>,
 and <a href='http://www.cs.utexas.edu/~sandip'>S. Ray</a>.
 <a href='http://www.springerlink.com/content/100280/'>Journal
 of Automated Reasoning</a>, volume 47(1), June 2011, pages
 1-16.  <a href='http://www.springer.com'>Springer</a>.</li>

 <li>
 <a
 href='http://www.cs.utexas.edu/users/sandip/publications/combination/main.html'>Combining
 Theorem Proving with Model Checking through Predicate Abstraction</a>,
 Sandip Ray and Rob Sumners.
 <a href='http://www.computer.org/dt'>IEEE Design &amp; Test of
 Computers</a>, volume 24(2), March-April 2007 (Special Issue on
 Advances in Functional Validation through Hybrid Techniques), pages
 132-139.</li>

 <li><a href='http://www.cs.utexas.edu/users/sandip/publications/invariants/main.html'>
 Reducing Invariant Proofs to Finite Search via Rewriting</a>,
 Rob Sumners and Sandip Ray.
 In M. Kaufmann
 and J S. Moore, editors, <a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2004/'>5th
 International Workshop on the ACL2 Theorem Prover and Its Applications (ACL2
 2004)</a>, Austin, TX, November 2004.</li>

 <li><a
 href='http://www.cs.utexas.edu/users/sandip/publications/ltl-reductions/main.html'>
 Certifying Compositional Model Checking Algorithms in ACL2</a>,
 Sandip Ray, John Matthews, and Mark Tuttle.
 In W. A. Hunt, Jr, M. Kaufmann, and J S. Moore, editors, <a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2003/'>4th
 International Workshop on the ACL2 Theorem Prover and Its Applications (ACL2
 2003)</a>, Boulder, CO, July 2003.</li>

 <li>Mu-Calculus Model-Checking, Panagiotis Manolios, Chapter 7 of <a
 href='acl2-books/acs/index.html'>Computer-Aided Reasoning: ACL2 Case
 Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer, 2000.
 (ACL2 scripts are available from
   directory <tt>1999/mu-calculus/</tt> in the @(see community-books).)
 The article presents a formal development of the syntax and
 semantics for the Mu-calculus, a model-checker for it in ACL2, and a
 discussion of the translation of other temporal logics into the Mu-calculus.
 The model checker is proved correct.  The ACL2 scripts referenced here
 provide the full details of the results described in the article along with
 solutions to all the exercises in the article.</li>

 <li>Symbolic Trajectory Evaluation, Damir A. Jamsek, Chapter 12 of <a
 href='acl2-books/acs/index.html'>Computer-Aided Reasoning: ACL2 Case
 Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer, 2000.
 (ACL2 scripts are available from
   directory <tt>1999/ste/</tt> in the @(see community-books).)
 Symbolic Trajectory Evaluation (STE) is a form of model checking
 fundamentally based on symbolic simulation.  This article presents a formal
 treatment of STE, including ACL2 proofs of results presented in the Seger and
 Joyce paper &ldquo;A Mathematically Precise Two-Level Formal Hardware Verification
 Methodology.&rdquo;  The ACL2 scripts referenced here provide the full details of
 the results described in the article along with solutions to all the
 exercises in the article.</li>

 </ul>")

(defxdoc pub-logic-and-metamathematics
  :parents (pub-papers)
  :short "Logic and Metamathematics"
  :long "
 <ul>

 <li><a href='http://dx.doi.org/10.1007/s10817-006-9030-5'>
     Formal Correctness of a Quadratic Unification Algorithm</a>,
     J.L. Ruiz-Reina, F.J. Martin-Mateos, J.A. Alonso and M.J. Hidalgo.
     <i>Journal of Automated Reasoning (37):1-2</i>, pp. 67-92, 2006.
     The paper presents the formal verification of a syntactic unification
     algorithm of quadratic time complexity, using a dag representation for
     terms. The use of stobjs and defexec/mbe makes the algorithm efficiently
     executable.</li>

 <li><a href='http://dx.doi.org/10.1007/s10817-010-9178-x'>
     Proof Pearl: A Formal Proof of Higman's Lemma in ACL2</a>,
     F.J. Martin-Mateos, J.L. Ruiz-Reina, J.A. Alonso and M.J. Hidalgo.
     <i>Journal of Automated Reasoning (47):3</i>, pp. 229-250, 2011.
     Highman's Lemma is a property about well quasi-orderings on strings. In
     this paper a formal proof of this result is presented, using a termination
     argument based on well-founded multiset extensions.</li>

 <li>
 <a href='http://www.springerlink.com/content/ydygr1el79p2pg75/fulltext.html'>
     A Formal Proof of Dickson's Lemma in ACL2</a>,
     F.J. Martin-Mateos, J.A. Alonso, M.J. Hidalgo and J.L. Ruiz-Reina.
     <i>LPAR 2003 - LNAI 2850</i>, pp. 49-58, 2003.
     Dickson's Lemma is the main result needed for proving termination of
     Buchberger's algorithm for computing Groebner basis of ideals of
     polynomials. In this paper a formal proof of this result is presented,
     using a termination argument based on well-founded multiset extensions.</li>

 <li><a href='http://www.glc.us.es/fmartin/files/publicaciones/2004-JAR.pdf'>
     Formal verification of a generic framework to synthesize SAT-provers</a>,
     F.J. Martin-Mateos, J.A. Alonso, M.J. Hidalgo and J.L. Ruiz-Reina.
     <i>Journal of Automated Reasoning (32):4</i>, pp. 287-313, 2004.
     A generic framework for SAT checkers is defined and verified. Several
     verified and executable SAT solvers can be obtained instantiating this
     generic framefork.</li>

 <li><a href='http://www.glc.us.es/fmartin/files/publicaciones/2003-als.pdf'>
     Termination in ACL2 Using Multiset Relations</a>,
     J.L. Ruiz-Reina, J.A. Alonso, M.J. Hidalgo and F.J. Martin-Mateos.
     <i>Thirty Five Years of Automating Mathematics</i>, pp. 217-245. 2003.
     A proof in ACL2 of the well-foundedness of multiset extensions of
     well-founded relations and a tool for generating automatically such
     multiset relations.</li>

 <li><a href='http://www.springerlink.com/content/q56uw2rbetj83le9/'>
 A certified polynomial-based decision procedure for  propositional logic </a>,
 I. Medina Bulo, F. Palomo Lozano and J. A. Alonso Jimenez, <i> 4th
 International Conference on Theorem Proving in Higher Order Logics </i>, LNCS
 2152:297-312. Edinburgh (Escocia), 2001. In this paper we present the
 formalization of a decision procedure for Propositional Logic based on
 polynomial normalization. This formalization is suitable for its automatic
 verification in an applicative logic like ACL2. This application of
 polynomials has  been developed by reusing a previous work on polynomial
 rings, showing that a proper formalization leads to a high  level of
 reusability. Two checkers are defined: the first for contradiction formulas
 and the second for tautology formulas. The main theorems state that both
 checkers are sound and complete. Moreover, functions for generating models
 and counterexamples of  formulas are provided. This facility plays also an
 important role in  the main proofs. Finally, it is shown that this allows for
 a highly  automated proof development.</li>

 <li><a href='http://dx.doi.org/10.1023/A:1016003314081'>
     Formal Proofs About Rewriting Using ACL2</a>,
     J.L. Ruiz-Reina, J.A. Alonso, M.J. Hidalgo and F.J. Martin-Mateos.
     <i>Annals of Mathematics and Artificial Intelligence 36(3)</i>,
     pp. 239-262, 2002.
     This paper presents a formalization of term rewriting systems. That is,
     ACL2 is used as the metatheory to formalize results in equational
     reasoning and rewrite systems. Notions such as confluence, local
     confluence, and normal forms are formalized. The main theorems proved are
     Newman's Lemma and Knuth-Bendix critical-pair theorem.</li>

 <li>Ivy: A Preprocessor and Proof Checker for First-Order Logic, William
 McCune and Olga Shumsky, Chapter 16 of <a
 href='@(`(:raw (docpath \"acl2-books/acs/index.html\"))`)'>Computer-Aided Reasoning: ACL2 Case
 Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer, 2000.
 (ACL2 scripts are available from
   directory <tt>1999/ivy/</tt> in the @(see community-books).)
 In this case study, a proof checker for first-order logic is
 proved sound for finite interpretations.  In addition, the study shows how
 non-ACL2 programs can be combined with ACL2 functions in such a way that
 useful properties can be proved about the composite programs.  Nothing is
 proved about the non-ACL2 programs.  Instead, the results of the non-ACL2
 programs are checked at run time by ACL2 functions, and properties of these
 checker functions are proved.  The ACL2 scripts referenced here provide the
 full details of the results described in the article along with solutions to
 all the exercises in the article.</li>

 </ul>")

(defxdoc pub-miscellaneous-applications
  :parents (pub-papers)
  :short "Miscellaneous Applications"
  :long "
 <ul>

 <li><a href='http://dx.doi.org/10.1093/jigpal/jzt034'>Verifying the
 bridge between simplicial topology and algebra: the Eilenberg-Zilber
 algorithm</a>, L. Lamban, J. Rubio, F. J. Martin-Mateos and
 J. L. Ruiz-Reina. <em> Logic Journal of the IGPL 22(1)</em>,
 pp. 39-65, 2014. The Eilenberg-Zilber algorithm is one of the central
 components of the computer algebra system called <i>Kenzo</i>, devoted
 to computing in Algebraic Topology. In this article we report on a
 complete formal proof of the underlying
 Eilenberg-Zilber <i>theorem</i>, using the ACL2 theorem prover. As our
 formalization is executable, we are able to compare the results of the
 certified programme with those of <i>Kenzo</i> on
 some <i>universal</i> examples. Since the results coincide, the
 reliability of <i>Kenzo</i> is reinforced. This is a new step in our
 long-term project towards certified programming for Algebraic
 Topology.</li>

 <li>[Note: This entry extends an earlier version, included just below.]<br/>
     <a href='http://dx.doi.org/10.1007/s10472-011-9274-6'>
     Formalization of a normalization theorem in simplicial
     topology</a>, L. Lamban, F. J. Martin-Mateos,
     J. Rubio and J. L.  Ruiz-Reina. <i>Annals of Mathematics and
     Artificial Intelligence 64(1)</i>, pp. 1-37, 2012.  In this paper
     we present a complete formalization of the Normalization Theorem,
     a result in Algebraic Simplicial Topology stating that there
     exists a homotopy equivalence between the chain complex of a
     simplicial set, and a smaller chain complex for the same
     simplicial set, called the normalized chain complex. Even if the
     Normalization Theorem is usually stated as a higher-order result
     (with a Category Theory flavor) we manage to give a first-order
     proof of it. To this aim it is instrumental the introduction of an
     algebraic data structure called simplicial polynomial.  As a
     demonstration of the validity of our techniques we developed a
     formal proof in the ACL2 theorem prover.</li>

 <li>[Note: See entry just above for an extended version.]<br/>
     <a href='http://dx.doi.org/10.1007/978-3-642-22863-6_16'>
     Applying ACL2 to the Formalization of Algebraic Topology: Simplicial
     Polynomials</a>, L. Lamban, F. J. Martin-Mateos, J. Rubio
     and J. L. Ruiz-Reina. <i>ITP 2011 - LNCS 6898</i>, pp. 200-215, 2011.
     In this paper we present a complete formalization of the Normalization
     Theorem, a result in Algebraic Simplicial Topology stating that there
     exists a homotopy equivalence between the chain complex of a simplicial
     set, and a smaller chain complex for the same simplicial set, called the
     normalized chain complex.</li>

 <li><a href='http://dx.doi.org/10.1007/978-3-642-02614-0_13'>
     ACL2 verification of simplicial degeneracy programs in the Kenzo
     system</a>,
     F.J. Martin-Mateos, J. Rubio and J.L. Ruiz-Reina.
     <i>Calculemus 2009 - LNAI 5625</i>, pp. 106-121, 2009.
     In this paper, we give a complete automated proof of the correctness of
     the encoding of degeneracy lists (a topological object) used in Kenzo,
     a Computer Algebra System devoted to Algebraic Topology.</li>

 <li><a href='http://dx.doi.org/10.1016/j.jsc.2009.07.002'>A verified
 Common Lisp implementation of Buchberger's algorithm in ACL2.</a>
 I. Medina Bulo, F. Palomo Lozano, and J. L. Ruiz Reina. <em>Journal of
 Symbolic Computation</em> 45-1:96-123. 2010.  In this article, we
 present the formal verification of a Common Lisp implementation of
 Buchberger's algorithm for computing Groebner bases of polynomial
 ideals. This work is carried out in ACL2, a system which provides an
 integrated environment where programming (in a pure functional subset
 of Common Lisp) and formal verification of programs, with the
 assistance of a theorem prover, are possible. Our implementation is
 written in a real programming language and it is directly executable
 within the ACL2 system or any compliant Common Lisp system. We provide
 here snippets of real verified code, discuss the formalization details
 in depth, and present quantitative data about the proof effort.</li>

 <li><a href='http://www.springerlink.com/content/036fq6l8fqqjaxq4/fulltext.html'>
     Formal Verification of Molecular Computational Models in ACL2:
     A Case Study</a>,
     F.J. Martin-Mateos, J.A. Alonso, M.J. Hidalgo and J.L. Ruiz-Reina.
     <i>CAEPIA 2003 - LNCS 3040</i>, pp. 344-353, 2004.
     A formalization in ACL2 of Lipton's experiment that uses DNA computation
     for solving SAT.</li>

 <li><a
 href='http://springerlink.metapress.com/content/58acg5q7chw85r4r/?p=387292c2b34a4be5a9e4c3986274efb6&amp;pi=24'>
 Verified Computer Algebra in ACL2 (Groebner Bases Computation)</a>, I.
 Medina Bulo, F. Palomo Lozano, J. A. Alonso Jimenez and J. L. Ruiz
 Reina, <i> Artificial Intelligence and Symbolic Mathematical Computation
 (AISC 2004) </i>, LNAI 3249:171-184. Linz (Austria), 2004. In this paper, we
 present the formal verification of a Common LISP implementation of
 Buchberger's algorithm for computing Groebner bases of polynomial ideals.
 This work is carried out in the ACL2 system and shows how verified Computer
 Algebra can be achieved in an executable logic.</li>

 <li><a href='http://www.cs.utexas.edu/users/sandip/publications/stobj-qsort/main.html'>
 Verification of an In-place Quicksort in ACL2</a>, Sandip Ray and Rob Sumners.
 In D. Borrione, M. Kaufmann,
 and J S. Moore, editors, Proceedings of the <a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2002/'>3rd
 International Workshop on the ACL2 Theorem Prover and Its Applications (ACL2
 2002)</a>, Grenoble, France, April 2002, pages 204-212.</li>

 <li><a href='http://russinoff.com/papers/crt.html'>A Mechanical Proof of the
 Chinese Remainder Theorem</a>, David Russinoff, in <a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2000/'>Proceedings of
 ACL2 Workshop 2000</a>.</li>

 <li>Knuth's Generalization of McCarthy's 91 Function, John Cowles, Chapter 17
 of <a href='@(`(:raw (docpath \"acl2-books/acs/index.html\"))`)'>Computer-Aided Reasoning: ACL2 Case
 Studies</a> (Kaufmann, Manolios, Moore, eds.)  Kluwer, 2000.
 (ACL2 scripts are available from
   directory <tt>1999/knuth-91/</tt> in the @(see community-books).)
 This article deals with a challenge by Donald Knuth for a &ldquo;proof
 by computer&rdquo; of a theorem about his generalization of John McCarthy's famous
 &ldquo;91 function.&rdquo;  The generalization involves real numbers, and the case
 study uses ACL2 to meet Knuth's challenge by mechanically verifying results
 not only about the field of all real numbers, but also about every subfield
 of that field.  The ACL2 scripts referenced here provide the full details of
 the results described in the article along with solutions to all the
 exercises in the article.</li>

 <li><a href='@(`(:raw (docpath \"others/y2k/index.html\"))`)'>
 Verification of Year 2000 Conversion Rules</a>, Matt Kaufmann, March 1999
 (revised from June 1999).  This page links to event files in support
 of the paper <i><a href='https://link.springer.com/article/10.1007/PL00010807'>Verification of Year 2000 Conversion Rules Using the
 ACL2 Theorem Prover'</a></i>, in <a
 href='http://sttt.cs.uni-dortmund.de'><i>Software Tools for
 Technology Transfer</i></a>.  This formal verification of COBOL
 transformation rules was done in support of Y2K remediation performed
 at EDS CIO Services using an in-house proprietary tool, Cogen 2000.</li>

 <li><a href='@(`(:raw (docpath \"csort/main.pdf\"))`)'>A Mechanically Checked Proof of a Comparator Sort Algorithm</a>,
 J Moore and B. Brock,
 in, M. Broy, J. Gruenbauer, D. Harel, and
 C. A. R. Hoare (eds.)
 <i>Engineering Theories of Software Intensive Systems</i>,
 Springer NATO Science Series II, <b>195</b>, pp. 141-175, 2005.
 This paper describes a mechanically checked correctness proof for the
 comparator sort algorithm underlying a microcode program in a commercially
 designed digital signal processing chip.  The abstract algorithm uses an
 unlimited number of systolic comparator modules to sort a stream of data.  In
 addition to proving that the algorithm produces an ordered permutation of its
 input, two theorems are proved that are important to verifying the microcode
 implementation.  These theorems describe how positive and negative
 &ldquo;infinities&rdquo; can be streamed into the array of comparators to achieve
 certain effects.  Interesting generalizations are necessary in order to prove
 these theorems inductively.
 (<a href='@(`(:raw (docpath \"csort/csort.lisp\"))`)'>ACL2 Script</a>)</li>

 <li><a
 href='@(`(:raw (docpath \"others/autopilot-young.ps\"))`)'>The
 Specification of a Simple Autopilot in ACL2</a>, Bill Young, July, 1996.
 This paper presents an ACL2 translation of Butler's PVS formalization of a
 simple autopilot.</li>

 </ul>")

(defxdoc pub-related-web-sites
  :parents (publications)
  :short "Related Web Sites"
  :long "
 <ul>

 <li><a href='http://www-formal.stanford.edu/clt/ARS/ars-db.html'>Mechanized Reasoning Database (USA)</a></li>

 <li><a href='http://www.ags.uni-sb.de/projects/deduktion/deduktion/systems.html'>Mechanized Reasoning Database (Germany)</a></li>

 <li><a href='http://www.comlab.ox.ac.uk/archive/formal-methods.html'>Formal Methods</a></li>

 <li><a href='http://www.ora.on.ca/biblio/biblio-prover-welcome.html'>ORA Canada Bibliography of Automated Deduction</a></li>

 </ul>")

(defxdoc pub-slides
  :parents (publications)
  :short "Slides for talks about ACL2"
  :long"
 <p>See @(see talks) as well as the following pages for many slides for talks
 about ACL2:</p>

 <ul>

 <li>the <a href='http://www.cs.utexas.edu/users/moore/acl2/seminar/'>UT
 ACL2 Seminar page</a>; and</li>

 <li>the <a href='http://www.cs.utexas.edu/users/moore/acl2/workshops.html'>ACL2
 workshops web pages</a>.</li>

 </ul>

 <p>The rest of this topic is a stub.  Please feel free to extend it!</p>")

(defxdoc pub-videos
  :parents (publications)
  :short "Videos about ACL2"
  :long "
 <h3>Videos For Learning ACL2</h3>

 <ul>

 <li>
  The <a href='https://fm.csl.sri.com/SSFT21/'>Tenth Summer School on Formal Techniques</a> (2021) included a series of videos teaching ACL2:
  <ul>
   <li> <a href='https://youtu.be/xcXBOkp_w1s'>Welcome</a></li>
   <li> <a href='https://youtu.be/912RcvJrlk0'>Video 0</a></li>
   <li> <a href='https://youtu.be/pVRfeu8MbgE'>Video 1</a></li>
   <li> <a href='https://youtu.be/dtS4MjaWtgs'>Video 2</a></li>
   <li> <a href='https://youtu.be/81pr9bSVoy4'>Video 3</a></li>
   <li> <a href='https://youtu.be/60PPqrARDLc'>Video 4</a></li>
   <li> <a href='https://youtu.be/rqM7WRXx3qc'>Video 5</a></li>
   <li> <a href='https://youtu.be/dE83qdc7cJc'>Video 6a</a></li>
   <li> <a href='https://youtu.be/xFfZQPPPvjo'>Video 6b</a></li>
   <li> <a href='https://youtu.be/19hdVOLtohA'>Video 7</a></li>
  </ul>
  The <a href='https://fm.csl.sri.com/SSFT21/'>Summer School webpage</a> includes additional supplementary materials.
 </li>

 </ul>

 <h3>Videos About ACL2 and Its Applications</h3>
 <ul>
 <li><a href='https://www.youtube.com/watch?v=wOfHvPjqKaI'>What's New in ACL2, from the ACL2 2018 Workshop (Matt Kaufmann and Holly Bell, 2018)</a></li>
 <li><a href='https://www.youtube.com/watch?v=jtprDAfVtos'>Formal Verification of Cryptographic Code (Eric Smith, 2018)</a></li>
 <li><a href='https://www.youtube.com/watch?v=9JHZKR-gc4w'>Formal Verification of JubJub R1CS Gadgets (Alessandro Coglio, Eric McCarthy, Eric Smith, 2021)</a></li>
 <li><a href='https://www.youtube.com/watch?v=U-y8UNccnIw'>Protocol Analysis Using Real Analysis in ACL2 (Max von Hippel, 2023)</a></li>
 <li><a href='https://youtu.be/43rJSPqDeSM&amp;t=30m30s'>Compositional Formal Verification of Zero-Knowledge Circuits</a> from <a href='https://cbr.stanford.edu/sbc23/'>SBC 2023</a> (Alessandro Coglio, Eric McCarthy, Eric Smith, Collin Chin, Pranav Gaddamadugu, Michel Dellepere)</li>
 <li><a href='https://www.youtube.com/watch?v=PekrHpG1C_s'>An ACL2-based x86-ISA Specification (Warren Hunt, 2024)</a></li>
 <li><a href='http://www.cs.utexas.edu/users/kaufmann/demos/acl2-doc.mov'>Demo of
 the ACL2-Doc Emacs-based documentation browser</a> (also see <see
 topic='ACL2____ACL2-DOC'>its documentation</see>).</li>
 <li>An Integration of Axiomatic Set Theory with ACL2 (Matt Kaufmann):
 <a href='https://www.kestrel.edu/download/An-Integration-of-Axiomatic-Set-Theory-with-ACL2-Part-1.mp4'>Part 1</a>,
 <a
 href='https://www.kestrel.edu/download/An-Integration-of-Axiomatic-Set-Theory-with-ACL2-Part-2.mp4'>Part
 2</a>,
 and <a href='https://www.kestrel.edu/download/An-Integration-of-Axiomatic-Set-Theory-with-ACL2-Part-3.mp4'>Part 3</a>.</li>

 </ul>

")
