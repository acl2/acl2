; ACL2 Version 4.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2011  University of Texas at Austin

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; This document currently has the following form:
;
; :doc ACL2-tutorial
;   introduction
;     OVERVIEW
;     ABOUT THIS TUTORIAL:
;     GETTING STARTED:
;     INTERACTING WITH ACL2:
;   :doc examples
;     EXAMPLE: TOWERS OF HANOI
;     EXAMPLE: EIGHTS PROBLEM
;     A LARGER EXAMPLE: A PHONEBOOK SPECIFICATION
;     DEFUN-SK-EXAMPLE:: example of quantified notions
;     :doc miscellaneous-examples
;       * FILE-READING-EXAMPLE:: example of reading files in ACL2
;       * MUTUAL-RECURSION-PROOF-EXAMPLE:: a small proof about mutually 
;            recursive functions
;       * GUARD-EXAMPLE    a brief transcript illustrating guards in ACL2
;   STARTUP
;   TIDBITS 
;   TIPS

(in-package "ACL2")

(deflabel ACL2-Tutorial
  :doc
  ":Doc-Section ACL2-Tutorial

  tutorial introduction to ACL2~/

  To learn about ACL2, read at least the following two links.
  ~bq[]
  * ~il[interesting-applications Industrial Applications of ACL2] (10 minutes)
  to help you understand what sophisticated users can do;

  * ~il[|A Flying Tour of ACL2| A Flying Tour] (10 minutes) to get an overview
  of the system and what skills the user must have.~eq[]

  If you want to learn ~em[how to use] ACL2, we recommend that you read
  a selection of the materials referenced below, depending on your learning
  style, and do suggested exercises.
  ~bq[]
  * ``~il[|A Walking Tour of ACL2| A Walking Tour]'' (1 hour) provides an
  overview of the theorem prover.

  * ``~il[introduction-to-the-theorem-prover Introduction to the Theorem Prover]''
  (10-40 hours) provides instruction on how to interact with the system.
  Unlike the three documents above, this document expects you to ~em[think]!  It
  cites the necessary background pages on programming in ACL2 and on the logic
  and then instructs you in The Method, which is how expert users use ACL2.  It
  concludes with some challenge problems for the ACL2 beginner (including
  solutions) and an FAQ.  Most users will spend several hours a day for several
  days working through this material.

  * The book ''Computer-Aided Reasoning: An Approach'' (see
  ~url[http://www.cs.utexas.edu/users/moore/publications/acl2-books/car/index.html]
  is worth a careful read, as you work exercises and learn ``The Method.''

  * ``~il[annotated-acl2-scripts Annotated ACL2 Scripts and Demos]'' contains
  relatively elementary proof scripts that have been annotated to help train
  the newcomer.

  * Many files (``books'') in the ~c[books/] directory distributed with ACL2
  are extensively annotated.  See the link to ``Lemma Libraries and Utilities''
  on the ACL2 home page (~url[http://www.cs.utexas.edu/users/moore/acl2]).

  * An ``~il[alternative-introduction Alternative Introduction]'' document,
  while largely subsumed by the topic
  ``~il[introduction-to-the-theorem-prover Introduction to the Theorem Prover]''
  mentioned above, still might be useful because it covers much of the tutorial
  material in a different way.~eq[]

  At this point you are probably ready to use ACL2 on your own ~em[small]
  projects.  A common mistake for beginners is to browse the documentation and
  then try to do something that is too big!  Think of a very small project and
  then simplify it!

  Note that ACL2 has a very supportive user network.  See the link to ``Mailing
  Lists'' on the ACL2 home page
  (~url[http://www.cs.utexas.edu/users/moore/acl2]).

  The topics listed below are a hodge podge, developed over time.  Although
  some of these are not mentioned above, you might find some to be useful as
  well.

  ~/~/")

(deflabel alternative-introduction
  :doc
  ":Doc-Section ACL2-Tutorial

  introduction to ACL2~/

  This section contains introductory material on ACL2 including what
  ACL2 is, how to get started using the system, how to read the
  output, and other introductory topics.  It was written almost
  entirely by Bill Young of Computational Logic, Inc.

  You might also find CLI Technical Report 101 helpful, especially if
  you are familiar with Nqthm.  If you would like more familiarity
  with Nqthm, we suggest CLI Technical Report 100.~/

  ~em[OVERVIEW]

  ACL2 is an automated reasoning system developed (for the first 9 years)
  at Computational Logic, Inc. and (from January, 1997) at the University
  of Texas at Austin.  It is the successor to the Nqthm (or Boyer-Moore)
  logic and proof system and its Pc-Nqthm interactive enhancement.  The
  acronym ACL2 actually stands for ``A Computational Logic for Applicative
  Common Lisp''.  This title suggests several distinct but related aspects
  of ACL2.

  We assume that readers of the ACL2 ~il[documentation] have at least a
  very slight familiarity with some Lisp-like language.  We will
  address the issue of prerequisites further, in ``ABOUT THIS
  TUTORIAL'' below.

  As a ~b[logic], ACL2 is a formal system with rigorously defined
  syntax and semantics.  In mathematical parlance, the ACL2 logic is a
  first-order logic of total recursive functions providing
  mathematical induction on the ordinals up to epsilon-0 and two
  extension principles: one for recursive definition and one for
  constrained introduction of new function symbols, here called
  encapsulation.  The syntax of ACL2 is that of Common Lisp; ACL2
  specifications are ``also'' Common Lisp programs in a way that we
  will make clear later.  In less formal language, the ACL2 logic is
  an integrated collection of rules for defining (or axiomatizing)
  recursive functions, stating properties of those functions, and
  rigorously establishing those properties.  Each of these activities
  is mechanically supported.

  As a ~b[specification language], ACL2 supports modeling of systems
  of various kinds.  An ACL2 function can equally be used to express
  purely formal relationships among mathematical entities, to describe
  algorithms, or to capture the intended behavior of digital systems.
  For digital systems, an ACL2 specification is a mathematical
  ~b[model] that is intended to formalize relevant aspects of system
  behavior.  Just as physics allows us to model the behavior of
  continuous physical systems, ACL2 allows us to model digital
  systems, including many with physical realizations such as computer
  hardware.  As early as the 1930's Church, Kleene, Turing and others
  established that recursive functions provide an expressive formalism
  for modeling digital computation.  Digital computation should be
  understood in a broad sense, covering a wide variety of activities
  including almost any systematic or algorithmic activity, or activity
  that can be reasonably approximated in that way.  This ranges from
  the behavior of a digital circuit to the behavior of a programming
  language compiler to the behavior of a controller for a physical
  system (as long as the system can be adequately modeled discretely).
  All of these have been modeled using ACL2 or its predecessor Nqthm.

  ACL2 is a ~b[computational] logic in at least three distinct
  senses.  First, the theory of recursive functions is often
  considered the mathematics of computation.  Church conjectured that
  any ``effective computation'' can be modeled as a recursive
  function.  Thus, ACL2 provides an expressive language for modeling
  digital systems.  Second, many ACL2 specifications are executable.
  In fact, recursive functions written in ACL2 ~b[are] Common Lisp
  functions that can be submitted to any compliant Common Lisp
  compiler and executed (in an environment where suitable
  ACL2-specific macros and functions are defined).  Third, ACL2 is
  computational in the sense that calculation is heavily integrated
  into the reasoning process.  Thus, an expression with explicit
  constant values but no free variables can be simplified by
  calculation rather than by complex logical manipulations.

  ACL2 is a powerful, automated ~b[theorem prover] or proof checker.
  This means that a competent user can utilize the ACL2 system to
  discover proofs of theorems stated in the ACL2 logic or to check
  previously discovered proofs.  The basic deductive steps in an
  ACL2-checked proof are often quite large, due to the sophisticated
  combination of decision procedures, conditional rewriting,
  mathematical and structural induction, propositional simplification,
  and complex heuristics to orchestrate the interactions of these
  capabilities.  Unlike some automated proof systems, ACL2 does not
  produce a formal proof.  However, we believe that if ACL2 certifies
  the ``theoremhood'' of a given conjecture, then such a formal proof
  exists and, therefore, the theorem is valid.  The ultimate result of
  an ACL2 proof session is a collection of ``~il[events],'' possibly
  grouped into ``~il[books],'' that can be replayed in ACL2.  Therefore, a
  proof can be independently validated by any ACL2 user.

  ACL2 may be used in purely automated mode in the shallow sense that
  conjectures are submitted to the prover and the user does not
  interact with the proof attempt (except possibly to stop it) until
  the proof succeeds or fails.  However, any non-trivial proof attempt
  is actually interactive, since successful proof ``~il[events]''
  influence the subsequent behavior of the prover.  For example,
  proving a lemma may introduce a rule that subsequently is used
  automatically by the prover.  Thus, any realistic proof attempt,
  even in ``automatic'' mode, is really an interactive dialogue with
  the prover to craft a sequence of ~il[events] building an
  appropriate theory and proof rules leading up to the proof of the
  desired result.  Also, ACL2 supports annotating a theorem with
  ``~il[hints]'' designed to guide the proof attempt.  By supplying
  appropriate ~il[hints], the user can suggest proof strategies that
  the prover would not discover automatically.  There is a
  ``~il[proof-tree]'' facility (~pl[proof-tree]) that allows the
  user to ~il[monitor] the progress and structure of a proof attempt
  in real-time.  Exploring failed proof attempts is actually where
  heavy-duty ACL2 users spend most of their time.

  ACL2 can also be used in a more explicitly interactive mode.  The
  ``~il[proof-checker]'' subsystem of ACL2 allows exploration of a proof on
  a fairly low level including expanding calls of selected function
  symbols, invoking specific ~il[rewrite] rules, and selectively navigating
  around the proof.  This facility can be used to gain sufficient
  insight into the proof to construct an automatic version, or to
  generate a detailed interactive-style proof that can be replayed in
  batch mode.

  Because ACL2 is all of these things ~-[] computational logic,
  specification language, ~il[programming] system, and theorem prover ~-[] it
  is more than the sum of its parts.  The careful integration of these
  diverse aspects has produced a versatile automated reasoning system
  suitable for building highly reliable digital systems.  In the
  remainder of this tutorial, we will illustrate some simple uses of
  this automated reasoning system.

  ~em[ABOUT THIS TUTORIAL]

  ACL2 is a complex system with a vast array of features, bells and
  whistles.  However, it is possible to perform productive work with
  the system using only a small portion of the available
  functionality.  The goals of this tutorial are to:
  ~bq[]

  familiarize the new user with the most basic features of and modes
  of interaction with ACL2;

  familiarize her with the form of output of the system; and

  work through a graduated series of examples.
  ~eq[]

  The more knowledge the user brings to this system, the easier it
  will be to become proficient.  On one extreme:  the ~b[ideal] user
  of ACL2 is an expert Common Lisp programmer, has deep understanding
  of automated reasoning, and is intimately familiar with the earlier
  Nqthm system.  Such ideal users are unlikely to need this tutorial.
  However, without some background knowledge, the beginning user is
  likely to become extremely confused and frustrated by this system.
  We suggest that a new user of ACL2 should:
  ~bq[]

  (a) have a little familiarity with Lisp, including basic Lisp
  programming and prefix notation (a Lisp reference manual such as Guy
  Steele's ``Common Lisp:  The Language'' is also helpful);

  (b) be convinced of the utility of formal modeling; and

  (c) be willing to gain familiarity with basic automated theorem
  proving topics such as rewriting and algebraic simplification.
  ~eq[]

  We will not assume any deep familiarity with Nqthm (the so-called
  ``Boyer-Moore Theorem Prover''), though the book ``A Computational
  Logic Handbook'' by Boyer and Moore (Academic Press, 1988) is an
  extremely useful reference for many of the topics required to become
  a competent ACL2 user.  We'll refer to it as ACLH below.

  As we said in the introduction, ACL2 has various facets.  For
  example, it can be used as a Common Lisp ~il[programming] system to
  construct application programs.  In fact, the ACL2 system itself is
  a large Common Lisp program constructed almost entirely within ACL2.
  Another use of ACL2 is as a specification and modeling tool.  That
  is the aspect we will concentrate on in the remainder of this
  tutorial.

  ~em[GETTING STARTED]

  This section is an abridged version of what's available elsewhere;
  feel free to ~pl[startup] for more details.

  How you start ACL2 will be system dependent, but you'll probably
  type something like ``acl2'' at your operating system prompt.
  Consult your system administrator for details.

  When you start up ACL2, you'll probably find yourself inside the
  ACL2 ~il[command] loop, as indicated by the following ~il[prompt].
  ~bv[]

    ACL2 !>

  ~ev[]
  If not, you should type ~c[(LP)].  ~l[lp], which has a lot more
  information about the ACL2 ~il[command] loop.

  There are two ``modes'' for using ACL2, ~c[:]~ilc[logic] and
  ~c[:]~ilc[program].  When you begin ACL2, you will ordinarily be in the
  ~c[:]~ilc[logic] mode.  This means that any new function defined is not
  only executable but also is axiomatically defined in the ACL2 logic.
  (~l[defun-mode] and ~pl[default-defun-mode].)  Roughly
  speaking, ~c[:]~ilc[program] mode is available for using ACL2 as a
  ~il[programming] language without some of the logical burdens
  necessary for formal reasoning.  In this tutorial we will assume
  that we always remain in ~c[:]~ilc[logic] mode and that our purpose is
  to write formal models of digital systems and to reason about them.

  Now, within the ACL2 ~il[command] loop you can carry out various
  kinds of activities, including the folllowing.  (We'll see examples
  later of many of these.)
  ~bq[]

  define new functions (~pl[defun]);

  execute functions on concrete data; 

  pose and attempt to prove conjectures about previously defined
  functions (~pl[defthm]);

  query the ACL2 ``~il[world]'' or database (e.g., ~pl[pe]); and

  numerous other things. 
  ~eq[]

  In addition, there is extensive on-line ~il[documentation], of which this
  tutorial introduction is a part.

  ~em[INTERACTING WITH ACL2]

  The standard means of interacting with ACL2 is to submit a sequence
  of forms for processing by the ACL2 system.  These forms are checked
  for syntactic and semantic acceptability and appropriately processed
  by the system.  These forms can be typed directly at the ACL2
  ~il[prompt].  However, most successful ACL2 users prefer to do their work
  using the Emacs text editor, maintaining an Emacs ``working'' buffer
  in which forms are edited.  Those forms are then copied to the ACL2
  interaction buffer, which is often the ~c[\"*shell*\"] buffer.

  In some cases, processing succeeds and makes some change to the ACL2
  ``logical ~il[world],'' which affects the processing of subsequent forms.
  How can this processing fail?  For example, a proposed theorem will
  be rejected unless all function symbols mentioned have been
  previously defined.  Also the ability of ACL2 to discover the proof
  of a theorem may depend on the user previously having proved other
  theorems.  Thus, the order in which forms are submitted to ACL2 is
  quite important.  Maintaining forms in an appropriate order in your
  working buffer will be helpful for re-playing the proof later.

  One of the most common ~il[events] in constructing a model is
  introducing new functions.  New functions are usually introduced
  using the ~ilc[defun] form; we'll encounter some exceptions later.
  Proposed function definitions are checked to make sure that they are
  syntactically and semantically acceptable (e.g., that all mentioned
  functions have been previously defined) and, for recursive
  functions, that their recursive calls ~b[terminate].  A recursive
  function definition is guaranteed to terminate if there is some some
  ``measure'' of the arguments and a ``well-founded'' ordering such
  that the arguments to the function get smaller in each recursive
  call.  ~l[well-founded-relation].

  For example, suppose that we need a function that will append two
  lists together.  (We already have one in the ACL2 ~ilc[append]
  function; but suppose perversely that we decide to define our own.)
  Suppose we submit the following definition (you should do so as well
  and study the system output):
  ~bv[]

    (defun my-app (x y)
      (if (atom x)
          y
        (cons (car x) (my-app x y))))

  ~ev[]
  The system responds with the following message:
  ~bv[]

    ACL2 Error in ( DEFUN MY-APP ...):  No :MEASURE was supplied with
    the definition of MY-APP.  Our heuristics for guessing one have not
    made any suggestions.  No argument of the function is tested along
    every branch and occurs as a proper subterm at the same argument
    position in every recursive call.  You must specify a :MEASURE.  See
    :DOC defun.

  ~ev[]
  This means that the system could not find an expression involving
  the formal parameters ~c[x] and ~c[y] that decreases under some
  well-founded order in every recursive call (there is only one such
  call).  It should be clear that there is no such measure in this
  case because the only recursive call doesn't change the arguments at
  all.  The definition is obviously flawed; if it were accepted and
  executed it would loop forever.  Notice that a definition that is
  rejected is not stored in the system database; there is no need to
  take any action to have it ``thrown away.''  Let's try again with
  the correct definition.  The interaction now looks like (we're also
  putting in the ACL2 ~il[prompt]; you don't type that):
  ~bv[]

    ACL2 !>(defun my-app (x y)
             (if (atom x)
                 y
               (cons (car x) (my-app (cdr x) y))))

    The admission of MY-APP is trivial, using the relation O<
    (which is known to be well-founded on the domain recognized by
    O-P) and the measure (ACL2-COUNT X).  We observe that the
    type of MY-APP is described by the theorem
    (OR (CONSP (MY-APP X Y)) (EQUAL (MY-APP X Y) Y)).
    We used primitive type reasoning.

    Summary
    Form:  ( DEFUN MY-APP ...)
    Rules: ((:FAKE-RUNE-FOR-TYPE-SET NIL))
    Warnings:  None
    Time:  0.07 seconds (prove: 0.00, print: 0.00, other: 0.07)
    MY-APP

  ~ev[]
  Notice that this time the function definition was accepted.  We
  didn't have to supply a measure explicitly; the system inferred one
  from the form of the definition.  On complex functions it may be
  necessary to supply a measure explicitly.  (~l[xargs].)

  The system output provides several pieces of information.
  ~bq[]

  The revised definition is acceptable.  The system realized that
  there is a particular measure (namely, ~c[(acl2-count x)]) and a
  well-founded relation (~c[o<]) under which the arguments of
  ~c[my-app] get smaller in recursion.  Actually, the theorem prover
  proved several theorems to admit ~c[my-app].  The main one was that
  when ~c[(atom x)] is false the ~c[acl2-count] of ~c[(cdr x)] is less
  than (in the ~c[o<] sense) the ~c[acl2-count] of ~c[x].
  ~ilc[Acl2-count] is the most commonly used measure of the ``size`` of
  an ACL2 object.  ~ilc[o<] is the ordering relation on ordinals
  less than epsilon-0.  On the natural numbers it is just ordinary
  ``<''.

  The observation printed about ``the type of MY-APP'' means that
  calls of the function ~c[my-app] will always return a value that is
  either a ~il[cons] pair or is equal to the second parameter.

  The summary provides information about which previously introduced
  definitions and lemmas were used in this proof, about some notable
  things to watch out for (the Warnings), and about how long this
  event took to process.
  ~eq[]

  Usually, it's not important to read this information.  However, it
  is a good habit to scan it briefly to see if the type information is
  surprising to you or if there are Warnings.  We'll see an example of
  them later.

  After a function is accepted, it is stored in the database and
  available for use in other function definitions or lemmas.  To see
  the definition of any function use the ~c[:]~ilc[pe] command
  (~pl[pe]).  For example,
  ~bv[]

    ACL2 !>:pe my-app
     L       73:x(DEFUN MY-APP (X Y)
                        (IF (ATOM X)
                            Y (CONS (CAR X) (MY-APP (CDR X) Y))))

  ~ev[]
  This displays the definition along with some other relevant
  information.  In this case, we know that this definition was
  processed in ~c[:]~ilc[logic] mode (the ``~c[L]'') and was the 73rd ~il[command]
  processed in the current session.

  We can also try out our newly defined function on some sample data.
  To do that, just submit a form to be evaluated to ACL2.  For
  example,
  ~bv[]

    ACL2 !>(my-app '(0 1 2) '(3 4 5))
    (0 1 2 3 4 5)
    ACL2 !>(my-app nil nil)
    NIL
    ACL2 !>

  ~ev[]

  Now suppose we want to prove something about the function just
  introduced.  We conjecture, for example, that the length of the
  ~il[append] of two lists is the sum of their lengths.  We can formulate
  this conjecture in the form of the following ACL2 ~ilc[defthm] form.
  ~bv[]

    (defthm my-app-length
      (equal (len (my-app x y))
             (+ (len x) (len y))))

  ~ev[]
  First of all, how did we know about the functions ~c[len] and ~ilc[+], etc.?
  The answer to that is somewhat unsatisfying ~-[] we know them from our
  past experience in using Common Lisp and ACL2.  It's hard to know
  that a function such as ~c[len] exists without first knowing some Common
  Lisp.  If we'd guessed that the appropriate function was called
  ~ilc[length] (say, from our knowledge of Lisp) and tried ~c[:pe length], we
  would have seen that ~ilc[length] is defined in terms of ~c[len], and we
  could have explored from there.  Luckily, you can write a lot of
  ACL2 functions without knowing too many of the primitive functions.

  Secondly, why don't we need some ``type'' hypotheses?  Does it make
  sense to append things that are not lists?  Well, yes.  ACL2 and
  Lisp are both quite weakly typed.  For example, inspection of the
  definition of ~c[my-app] shows that if ~c[x] is not a ~il[cons] pair, then
  ~c[(my-app x y)] always returns ~c[y], no matter what ~c[y] is.

  Thirdly, would it matter if we rewrote the lemma with the equality
  reversed, as follows?
  ~bv[]

    (defthm my-app-length2
      (equal (+ (len x) (len y))
             (len (my-app x y)))).

  ~ev[]
  The two are ~b[logically] equivalent, but...yes, it would make a
  big difference.  Recall our remark that a lemma is not only a
  ``fact'' to be proved; it also is used by the system to prove other
  later lemmas.  The current lemma would be stored as a ~il[rewrite] rule.
  (~l[rule-classes].)  For a ~il[rewrite] rule, a conclusion of the
  form ~c[(EQUAL LHS RHS)] means to replace instances of the ~c[LHS] by the
  appropriate instance of the ~c[RHS].  Presumably, it's better to ~il[rewrite]
  ~c[(len (my-app x y))] to ~c[(+ (len x) (len y))] than the other way around.
  The reason is that the system ``knows'' more about ~ilc[+] than it does
  about the new function symbol ~c[my-app].

  So let's see if we can prove this lemma.  Submitting our preferred
  ~ilc[defthm] to ACL2 (do it!), we get the following interaction:
  ~bv[]
            --------------------------------------------------
  ACL2 !>(defthm my-app-length
    (equal (len (my-app x y))
           (+ (len x) (len y))))

  Name the formula above *1.

  Perhaps we can prove *1 by induction.  Three induction schemes are
  suggested by this conjecture.  These merge into two derived
  induction schemes.  However, one of these is flawed and so we are
  left with one viable candidate.

  We will induct according to a scheme suggested by (LEN X), but
  modified to accommodate (MY-APP X Y).  If we let (:P X Y) denote *1
  above then the induction scheme we'll use is
  (AND (IMPLIES (NOT (CONSP X)) (:P X Y))
       (IMPLIES (AND (CONSP X) (:P (CDR X) Y))
                (:P X Y))).
  This induction is justified by the same argument used to admit LEN,
  namely, the measure (ACL2-COUNT X) is decreasing according to the
  relation O< (which is known to be well-founded on the domain
  recognized by O-P).  When applied to the goal at hand the
  above induction scheme produces the following two nontautological
  subgoals.

  Subgoal *1/2
  (IMPLIES (NOT (CONSP X))
           (EQUAL (LEN (MY-APP X Y))
                  (+ (LEN X) (LEN Y)))).

  But simplification reduces this to T, using the :definitions of FIX,
  LEN and MY-APP, the :type-prescription rule LEN, the :rewrite rule
  UNICITY-OF-0 and primitive type reasoning.

  Subgoal *1/1
  (IMPLIES (AND (CONSP X)
                (EQUAL (LEN (MY-APP (CDR X) Y))
                       (+ (LEN (CDR X)) (LEN Y))))
           (EQUAL (LEN (MY-APP X Y))
                  (+ (LEN X) (LEN Y)))).

  This simplifies, using the :definitions of LEN and MY-APP, primitive
  type reasoning and the :rewrite rules COMMUTATIVITY-OF-+ and
  CDR-CONS, to

  Subgoal *1/1'
  (IMPLIES (AND (CONSP X)
                (EQUAL (LEN (MY-APP (CDR X) Y))
                       (+ (LEN Y) (LEN (CDR X)))))
           (EQUAL (+ 1 (LEN (MY-APP (CDR X) Y)))
                  (+ (LEN Y) 1 (LEN (CDR X))))).

  But simplification reduces this to T, using linear arithmetic,
  primitive type reasoning and the :type-prescription rule LEN.

  That completes the proof of *1.

  Q.E.D.

  Summary
  Form:  ( DEFTHM MY-APP-LENGTH ...)
  Rules: ((:REWRITE UNICITY-OF-0)
          (:DEFINITION FIX)
          (:REWRITE COMMUTATIVITY-OF-+)
          (:DEFINITION LEN)
          (:REWRITE CDR-CONS)
          (:DEFINITION MY-APP)
          (:TYPE-PRESCRIPTION LEN)
          (:FAKE-RUNE-FOR-TYPE-SET NIL)
          (:FAKE-RUNE-FOR-LINEAR NIL))
  Warnings:  None
  Time:  0.30 seconds (prove: 0.13, print: 0.05, other: 0.12)
   MY-APP-LENGTH
            --------------------------------------------------
  ~ev[]

  Wow, it worked!  In brief, the system first tried to ~il[rewrite] and
  simplify as much as possible.  Nothing changed; we know that because
  it said ``Name the formula above *1.''  Whenever the system decides
  to name a formula in this way, we know that it has run out of
  techniques to use other than proof by induction.

  The induction performed by ACL2 is structural or ``Noetherian''
  induction.  You don't need to know much about that except that it is
  induction based on the structure of some object.  The heuristics
  infer the structure of the object from the way the object is
  recursively decomposed by the functions used in the conjecture.  The
  heuristics of ACL2 are reasonably good at selecting an induction
  scheme in simple cases.  It is possible to override the heuristic
  choice by providing an ~c[:induction] hint (~pl[hints]).  In the
  case of the theorem above, the system inducts on the structure of
  ~c[x] as suggested by the decomposition of ~c[x] in both ~c[(my-app x y)]
  and ~c[(len x)].  In the base case, we assume that ~c[x] is not a
  ~ilc[consp].  In the inductive case, we assume that it is a ~ilc[consp]
  and assume that the conjecture holds for ~c[(cdr x)].

  There is a close connection between the analysis that goes on when a
  function like ~c[my-app] is accepted and when we try to prove
  something inductively about it.  That connection is spelled out well
  in Boyer and Moore's book ``A Computational Logic,'' if you'd like to
  look it up.  But it's pretty intuitive.  We accepted ~c[my-app]
  because the ``size'' of the first argument ~c[x] decreases in the
  recursive call.  That tells us that when we need to prove something
  inductively about ~c[my-app], it's a good idea to try an induction on
  the size of the first argument.  Of course, when you have a theorem
  involving several functions, it may be necessary to concoct a more
  complicated ~il[induction] schema, taking several of them into account.
  That's what's meant by ``merging'' the induction schemas.

  The proof involves two cases: the base case, and the inductive case.
  You'll notice that the subgoal numbers go ~b[down] rather than up,
  so you always know how many subgoals are left to process.  The base
  case (~c[Subgoal *1/2]) is handled by opening up the function
  definitions, simplifying, doing a little rewriting, and performing
  some reasoning based on the types of the arguments.  You'll often
  encounter references to system defined lemmas (like
  ~c[unicity-of-0]).  You can always look at those with ~c[:]~ilc[pe]; but,
  in general, assume that there's a lot of simplification power under
  the hood that's not too important to understand fully.

  The inductive case (~c[Subgoal *1/1]) is also dispatched pretty
  easily.  Here we assume the conjecture true for the ~ilc[cdr] of the
  list and try to prove it for the entire list.  Notice that the
  prover does some simplification and then prints out an updated
  version of the goal (~c[Subgoal *1/1']).  Examining these gives you a
  pretty good idea of what's going on in the proof.

  Sometimes one goal is split into a number of subgoals, as happened
  with the induction above.  Sometimes after some initial processing
  the prover decides it needs to prove a subgoal by induction; this
  subgoal is given a name and pushed onto a stack of goals.  Some
  steps, like generalization (see ACLH), are not necessarily validity
  preserving; that is, the system may adopt a false subgoal while
  trying to prove a true one.  (Note that this is ok in the sense that
  it is not ``unsound.''  The system will fail in its attempt to
  establish the false subgoal and the main proof attempt will fail.)
  As you gain facility with using the prover, you'll get pretty good
  at recognizing what to look for when reading a proof script.  The
  prover's ~il[proof-tree] utility helps with monitoring an ongoing
  proof and jumping to designated locations in the proof
  (~pl[proof-tree]).  ~l[tips] for a number of useful
  pointers on using the theorem prover effectively.

  When the prover has successfully proved all subgoals, the proof is
  finished.  As with a ~ilc[defun], a summary of the proof is printed.
  This was an extremely simple proof, needing no additional guidance.
  More realistic examples typically require the user to look carefully
  at the failed proof log to find ways to influence the prover to do
  better on its next attempt.  This means either:  proving some rules
  that will then be available to the prover, changing the global state
  in ways that will affect the proof, or providing some ~il[hints]
  locally that will influence the prover's behavior.  Proving this
  lemma (~c[my-app-length]) is an example of the first.  Since this is
  a ~il[rewrite] rule, whenever in a later proof an instance of the
  form ~c[(LEN (MY-APP X Y))] is encountered, it will be rewritten to
  the corresponding instance of ~c[(+ (LEN X) (LEN Y))].  Disabling the
  rule by executing the ~il[command]
  ~bv[]

    (in-theory (disable my-app-length)),

  ~ev[] 
  is an example of a global change to the behavior of the prover
  since this ~il[rewrite] will not be performed subsequently (unless the rule
  is again ~il[enable]d).  Finally, we can add a (local) ~il[disable] ``hint''
  to a ~ilc[defthm], meaning to ~il[disable] the lemma only in the proof of one
  or more subgoals.  For example: 
  ~bv[]
  
    (defthm my-app-length-commutativity
      (equal (len (my-app x y))
             (len (my-app y x)))
      :hints ((\"Goal\" :in-theory (disable my-app-length))))
  
  ~ev[]
  In this case, the hint supplied is a bad idea since the proof is much
  harder with the hint than without it.  Try it both ways.

  By the way, to undo the previous event use ~c[:u] (~pl[u]).  To
  undo back to some earlier event use ~c[:ubt] (~pl[ubt]).  To view
  the current event use ~c[:pe :here].  To list several ~il[events] use
  ~c[:pbt] (~pl[pbt]).

  Notice the form of the hint in the previous example
  (~pl[hints]).  It specifies a goal to which the hint applies.
  ~c[\"Goal\"] refers to the top-level goal of the theorem.  Subgoals
  are given unique names as they are generated.  It may be useful to
  suggest that a function symbol be ~il[disable]d only for Subgoal
  1.3.9, say, and a different function ~il[enable]d only on Subgoal
  5.2.8.  Overuse of such ~il[hints] often suggests a poor global
  proof strategy.

  We now recommend that you visit ~il[documentation] on additional
  examples.  ~l[annotated-acl2-scripts].")

(deflabel annotated-acl2-scripts
  :doc
  ":Doc-Section ACL2-Tutorial

  examples of ACL2 scripts~/

  Beginning users may find these annotated scripts useful.  We suggest that you read
  these in the following order:
  ~bf[]
  ~il[Tutorial1-Towers-of-Hanoi]
  ~il[Tutorial2-Eights-Problem]
  ~il[Tutorial3-Phonebook-Example]
  ~il[Tutorial4-Defun-Sk-Example]
  ~il[Tutorial5-Miscellaneous-Examples]
  ~ef[]

  The page ~url[http://www.cs.utexas.edu/users/moore/publications/tutorial/rev3.html]
  contains a script that illustrates how it feels to use The Method to prove
  an unusual list reverse function correct.  The screen shots of ACL2's proof output
  are outdated -- in the version shown, ACL2 does not print Key Checkpoints, but the
  concept of key checkpoint is clear in the discussion and the behavior of the
  user.  

  See
  ~url[http://www.cs.utexas.edu/users/moore/acl2/contrib/POLISHING-PROOFS-TUTORIAL.html]
  for a tutorial on becoming successful at approaching a formalization and
  proof problem in ACL2.  That tutorial, written by Shilpi Goel and Sandip Ray,
  has two parts: it illustrates how to guide the theorem prover to a successful
  proof, and it shows how to clean up the proof in order to facilitate
  maintenance and extension of the resulting book (~pl[books]).

  At ~url[http://www.cs.utexas.edu/users/moore/publications/tutorial/kaufmann-TPHOLs08/index.html]
  is the demo given by Matt Kaufmann at TPHOLs08, including all the scripts.  There is a gzipped
  tar file containing the entire contents of the demos.

  At ~url[http://www.cs.utexas.edu/users/moore/publications/tutorial/sort-equivalence] is a
  collection of scripts illustrating both high-level strategy and lower-level tactics dealing
  with the functional equivalence of various list sorting algorithms.  Start with the
  ~c[README] on that directory.  There is also a gzipped tar file containing all the
  scripts, at
  ~url[http://www.cs.utexas.edu/users/moore/publications/tutorial/sort-equivalence.tgz].

  When you feel you have read enough examples, you might want to try the
  following very simple example on your own. (~l[solution-to-simple-example]
  for a solution, after you work on this example.)  First define the notion of
  the ``fringe'' of a tree, where we identify trees simply as ~il[cons]
  structures, with ~il[atom]s at the leaves.  For example:
  ~bv[]

    ACL2 !>(fringe '((a . b) c . d))
    (A B C D)

  ~ev[]
  Next, define the notion of a ``leaf'' of a tree, i.e., a predicate
  ~c[leaf-p] that is true of an atom if and only if that atom appears
  at the tip of the tree.  Define this notion without referencing the
  function ~c[fringe].  Finally, prove the following theorem, whose
  proof may well be automatic (i.e., not require any lemmas).
  ~bv[]

    (defthm leaf-p-iff-member-fringe
      (iff (leaf-p atm x)
           (member-equal atm (fringe x))))

  ~ev[]

 ~/~/")

(deflabel Emacs
  :doc
  ":Doc-Section ACL2-Tutorial

  emacs support for ACL2~/

  Many successful ACL2 users run in an shell under the Emacs editor.  If you do
  so, then you may wish to load the distributed file ~c[emacs/emacs-acl2.el].
  The file begins with considerable comments describing what it offers.  It is
  intended to work both with GNU Emacs and XEmacs.

  If you are not comfortable with Emacs, you may prefer to use an Eclipse-based
  interface; ~pl[acl2-sedan].~/~/")

(deflabel ACL2-As-Standalone-Program
  :doc
  ":Doc-Section ACL2-Tutorial

  Calling ACL2 from another program~/

  ACL2 is intended for interactive use.  It is generally unrealistic to expect
  it to prove theorems fully automatically; ~pl[the-method], and
  ~pl[introduction-to-the-theorem-prover] for a more detailed tutorial.

  Nevertheless, here we describe an approach for how to call the ACL2 theorem
  prover noninteractively.  These steps can of course be modified according to
  your needs.  Here, we illustrate how to call ACL2 from another Lisp program
  (or an arbitrary program) to attempt to prove an arithmetic theorem.

  ~b[=== STEP 1: ===]

  Build a suitable ACL2 image by starting ACL2 and then executing the following
  forms.  In particular, these define a macro, ~c[try-thm], that causes ACL2 to
  exit with with an exit status indicating success or failure of a proof
  attempt.

  ~bv[]
  (include-book \"arithmetic-5/top\" :dir :system)
  (defmacro try-thm (&rest args)
    `(mv-let (erp val state)
             (with-prover-time-limit 3 (thm ,@args))
             (declare (ignore val))
             (prog2$ (if erp (exit 1) (exit 0)) state))))
  (reset-prehistory) ; optional
  :q
  (save-exec \"arith-acl2\" \"Included arithmetic-4/top\")
  ~ev[]

  If you prefer, above you can replace 3 by some other number of seconds as a
  time limit for the prover.  Also, you can replace
  ~bv[]
  (with-prover-time-limit 3 (thm ,@args))
  ~ev[]
  by
  ~bv[]
  (with-output :off :all (with-prover-time-limit 3 (thm ,@args)))
  ~ev[]
  if you want to turn off output.  It may be best to leave the output on,
  instead eliminating it in the calling program (see Step 3 below).

  ~b[=== STEP 2: ===]

  Try a little test.  In that same directory try this:

  ~bv[]
  echo '(try-thm (equal x x))' | ./arith-acl2
  echo $?
  ~ev[]

  The exit status should be 0, indicating success.  Now try this:

  ~bv[]
  echo '(try-thm (not (equal x x)))' | ./arith-acl2
  echo $?
  ~ev[]

  The exit status should be 1, indicating failure.

  ~b[=== STEP 3: ===]

  Create a shell script that automates Step 2, for example:

  ~bv[]
  #!/bin/sh
  (echo \"(try-thm $1)\" | ./arith-acl2) >& /dev/null
  exit $?
  ~ev[]

  ~b[=== STEP 4: ===]

  Try your script from a Lisp program, if you like.  Here is how you can do it
  in SBCL, for example.  ( Different Lisps have different ways to do this, as
  summarized in function ~c[system-call] in ACL2 source file
  ~c[acl2-init.lisp].)

  ~bv[]
  (defun provable? (x)
    (let ((status
           (process-exit-code
            (sb-ext:run-program \"./try-thm.sh\" (list (format nil \"~~s\" x))
                                :output t :search t))))
      (eql status 0)))
  ~ev[]

  Then here is a log:

  ~bv[]
    * (provable? '(equal x y))

    NIL
    * (provable? '(equal x x))

    T
    * 
  ~ev[]

  Certainly refinements are possible -- for example the above doesn't
  distinguish between unprovable and ill-formed input.  But it's a
  start.~/~/")

(deflabel acl2-sedan
  :doc
  ":Doc-Section ACL2-Tutorial

  ACL2 Sedan interface~/

  Many successful ACL2 users run in an shell under Emacs; ~pl[emacs].  However,
  those not familiar with Emacs may prefer to start with an Eclipse-based
  interface developed by Peter Dillinger and Pete Manolios called the ``ACL2
  Sedan'', or ``ACL2s''.  As of this writing, the home page for ACL2s is
  ~url[http://acl2s.ccs.neu.edu/acl2s/doc/].~/

  ACL2 sessions in the ACL2 Sedan can utilize non-standard extensions and
  enhancements, especially geared toward new users, termination reasoning, and
  attaching rich user interfaces.  These extensions are generally available as
  certifiable ACL2 books, and can be downloaded from
  ~url[http://acl2s.ccs.neu.edu/acl2s/src/acl2-extensions].  (Some code
  originating from this project has been migrated to the ACL2 system books, but
  only after it was quite stable.)  Thanks to Peter Dillinger, Pete Manolios,
  and Daron Vroon for their work on the ACL2 Sedan and for making their books
  available to ACL2 users.  ~/")

(deflabel solution-to-simple-example
  :doc
  ":Doc-Section Annotated-Acl2-Scripts

  solution to a simple example~/

  To see a statement of the problem solved below,
  ~pl[annotated-acl2-scripts] (in particular the end of that topic).~/

  Here is a sequence of ACL2 ~il[events] that illustrates the use of ACL2
  to make definitions and prove theorems.  We will introduce the
  notion of the fringe of a tree, as well as the notion of a leaf of a
  tree, and then prove that the members of the fringe are exactly the
  leaves.

  We begin by defining the fringe of a tree, where we identify
  trees simply as ~il[cons] structures, with ~il[atom]s at the leaves.  The
  definition is recursive, breaking into two cases.  If ~c[x] is a ~il[cons],
  then the ~c[fringe] of ~c[x] is obtained by appending together the ~c[fringe]s
  of the ~ilc[car] and ~ilc[cdr] (left and right child) of ~c[x].  Otherwise, ~c[x] is an
  ~il[atom] and its ~c[fringe] is the one-element list containing only ~c[x].
  ~bv[]

    (defun fringe (x)
      (if (consp x)
          (append (fringe (car x))
                  (fringe (cdr x)))
        (list x)))

  ~ev[]
  Now that ~c[fringe] has been defined, let us proceed by defining the
  notion of an atom appearing as a ``leaf'', with the goal of proving
  that the leaves of a tree are exactly the members of its ~c[fringe].
  ~bv[]

    (defun leaf-p (atm x)
      (if (consp x)
          (or (leaf-p atm (car x))
              (leaf-p atm (cdr x)))
        (equal atm x)))

  ~ev[]
  The main theorem is now as follows.  Note that the rewrite rule
  below uses the equivalence relation ~ilc[iff] (~pl[equivalence])
  rather than ~ilc[equal], since ~ilc[member] returns the tail of the given
  list that begins with the indicated member, rather than returning a
  Boolean.  (Use ~c[:pe member] to see the definition of ~ilc[member].)
  ~bv[]

    (defthm leaf-p-iff-member-fringe
      (iff (leaf-p atm x)
           (member-equal atm (fringe x))))

  ~ev[]
  ")

(deflabel Tutorial1-Towers-of-Hanoi
  :doc
  ":Doc-Section Annotated-Acl2-Scripts

  The Towers of Hanoi Example~/

  This example was written almost entirely by Bill Young of
  Computational Logic, Inc.~/

  We will formalize and prove a small theorem about the famous
  ``Towers of Hanoi'' problem.  This problem
  is illustrated by the following picture.
  ~bv[]  
  
            |        |        |
            |        |        |
           ---       |        |
          -----      |        |
         -------     |        |
            
            A        B        C
  
  ~ev[] 
  We have three pegs ~-[] ~c[a], ~c[b], and ~c[c] ~-[] and ~c[n] disks of
  different sizes.  The disks are all initially on peg ~c[a].  The goal
  is to move all disks to peg ~c[c] while observing the following two
  rules.

  1. Only one disk may be moved at a time, and it must start and finish
  the move as the topmost disk on some peg;

  2. A disk can never be placed on top of a smaller disk. 

  Let's consider some simple instances of this problem.  If ~c[n] = 1,
  i.e., only one disk is to be moved, simply move it from ~c[a] to
  ~c[c].  If ~c[n] = 2, i.e., two disks are to be moved, the following
  sequence of moves suffices:  move from ~c[a] to ~c[b], move from ~c[a]
  to ~c[c], move from ~c[b] to ~c[c].

  In this doc topic we will show an ACL2 function that generates a suitable
  list of moves for a tower of ~c[n] disks.  Then we will use ACL2 to prove
  that the number of moves is ~c[(- (expt 2 n) 1)].  For an ACL2 script
  that proves the correctness of (a version of) this function, see the
  book ~c[\"misc/hanoi.lisp\"] in the ~c[books] directory of your ACL2
  sources.

  In general, this problem has a straightforward recursive solution.
  Suppose that we desire to move ~c[n] disks from ~c[a] to ~c[c], using
  ~c[b] as the intermediate peg.  For the basis, we saw above that we
  can always move a single disk from ~c[a] to ~c[c].  Now if we have
  ~c[n] disks and assume that we can solve the problem for ~c[n-1]
  disks, we can move ~c[n] disks as follows.  First, move ~c[n-1] disks
  from ~c[a] to ~c[b] using ~c[c] as the intermediate peg; move the
  single disk from ~c[a] to ~c[c]; then move ~c[n-1] disks from ~c[b] to
  ~c[c] using ~c[a] as the intermediate peg.

  In ACL2, we can write a function that will return the sequence of
  moves.  One such function is as follows.  Notice that we have two
  base cases.  If ~c[(zp n)] then ~c[n] is not a positive integer; we
  treat that case as if ~c[n] were 0 and return an empty list of moves.
  If ~c[n] is 1, then we return a list containing the single
  appropriate move.  Otherwise, we return the list containing exactly
  the moves dictated by our recursive analysis above.
  ~bv[]

    (defun move (a b)
      (list 'move a 'to b))

    (defun hanoi (a b c n)
      (if (zp n)
          nil
        (if (equal n 1)
            (list (move a c))
          (append (hanoi a c b (1- n))
                  (cons (move a c)
                        (hanoi b a c (1- n)))))))

  ~ev[]
  Notice that we give ~c[hanoi] four arguments:  the three pegs, and
  the number of disks to move.  It is necessary to supply the pegs
  because, in recursive calls, the roles of the pegs differ.  In any
  execution of the algorithm, a given peg will sometimes be the source
  of a move, sometimes the destination, and sometimes the intermediate
  peg.

  After submitting these functions to ACL2, we can execute the ~c[hanoi]
  function on various specific arguments.  For example:
  ~bv[]

    ACL2 !>(hanoi 'a 'b 'c 1)
    ((MOVE A TO C))

    ACL2 !>(hanoi 'a 'b 'c 2)
    ((MOVE A TO B)
     (MOVE A TO C)
     (MOVE B TO C))

    ACL2 !>(hanoi 'a 'b 'c 3)
    ((MOVE A TO C)
     (MOVE A TO B)
     (MOVE C TO B)
     (MOVE A TO C)
     (MOVE B TO A)
     (MOVE B TO C)
     (MOVE A TO C))

  ~ev[]
  From the algorithm it is clear that if it takes ~c[m] moves to
  transfer ~c[n] disks, it will take ~c[(m + 1 + m) = 2m + 1] moves for
  ~c[n+1] disks.  From some simple calculations, we see that we need
  the following number of moves in specific cases:
  ~bv[]

     Disks   0   1   2   3   4   5   6   7  ...
     Moves   0   1   3   7  15  31  63  127 ...

  ~ev[]
  The pattern is fairly clear.  To move ~c[n] disks requires ~c[(2^n - 1)]
  moves.  Let's attempt to use ACL2 to prove that fact.

  First of all, how do we state our conjecture?  Recall that ~c[hanoi]
  returns a list of moves.  The length of the list (given by the
  function ~c[len]) is the number of moves required.  Thus, we can state
  the following conjecture.
  ~bv[]

    (defthm hanoi-moves-required-first-try
      (equal (len (hanoi a b c n))
             (1- (expt 2 n))))

  ~ev[]
  When we submit this to ACL2, the proof attempt fails.  Along the way
  we notice subgoals such as:
  ~bv[]

    Subgoal *1/1'
    (IMPLIES (NOT (< 0 N))
             (EQUAL 0 (+ -1 (EXPT 2 N)))).

  ~ev[]

  This tells us that the prover is considering cases that are
  uninteresting to us, namely, cases in which ~c[n] might be negative.
  The only cases that are really of interest are those in which ~c[n]
  is a non-negative natural number.  Therefore, we revise our theorem
  as follows:
  ~bv[]

    (defthm hanoi-moves-required
      (implies (and (integerp n) 
                    (<= 0 n))    ;; n is at least 0
               (equal (len (hanoi a b c n))
                      (1- (expt 2 n)))))

  ~ev[]
  and submit it to ACL2 again.  

  Again the proof fails.  Examining the proof script we encounter the
  following text.  (How did we decide to focus on this goal?  Some
  information is provided in ACLH, and the ACL2 documentation on
  ~il[tips] may be helpful.  But the simplest answer is:  this was the
  first goal suggested by the ``~il[proof-tree]'' tool below the start
  of the proof by induction.  ~l[proof-tree].)
  ~bv[]

    Subgoal *1/5''
    (IMPLIES (AND (INTEGERP N)
                  (< 0 N)
                  (NOT (EQUAL N 1))
                  (EQUAL (LEN (HANOI A C B (+ -1 N)))
                         (+ -1 (EXPT 2 (+ -1 N))))
                  (EQUAL (LEN (HANOI B A C (+ -1 N)))
                         (+ -1 (EXPT 2 (+ -1 N)))))
             (EQUAL (LEN (APPEND (HANOI A C B (+ -1 N))
                                 (CONS (LIST 'MOVE A 'TO C)
                                       (HANOI B A C (+ -1 N)))))
                    (+ -1 (* 2 (EXPT 2 (+ -1 N))))))

  ~ev[]
  It is difficult to make much sense of such a complicated goal.
  However, we do notice something interesting.  In the conclusion is
  a ~il[term] of the following shape.
  ~bv[]

     (LEN (APPEND ... ...))

  ~ev[]
  We conjecture that the length of the ~ilc[append] of two lists should
  be the sum of the lengths of the lists.  If the prover knew that, it
  could possibly have simplified this ~il[term] earlier and made more
  progress in the proof.  Therefore, we need a ~il[rewrite] rule that
  will suggest such a simplification to the prover.  The appropriate
  rule is:
  ~bv[]

    (defthm len-append
      (equal (len (append x y))
             (+ (len x) (len y))))

  ~ev[]
  We submit this to the prover, which proves it by a straightforward
  induction.  The prover stores this lemma as a ~il[rewrite] rule and
  will subsequently (unless we ~il[disable] the rule) replace
  ~il[term]s matching the left hand side of the rule with the
  appropriate instance of the ~il[term] on the right hand side.

  We now resubmit our lemma ~c[hanoi-moves-required] to ACL2.  On this
  attempt, the proof succeeds and we are done.   

  One bit of cleaning up is useful.  We needed the hypotheses that:
  ~bv[]

    (and (integerp n) (<= 0 n)).

  ~ev[]
  This is an awkward way of saying that ~c[n] is a natural number;
  natural is not a primitive data type in ACL2.  We could define a
  function ~c[naturalp], but it is somewhat more convenient to define a
  macro as follows:
  ~bv[]

    (defmacro naturalp (x)
      (list 'and (list 'integerp x)
                    (list '<= 0 x)))

  ~ev[]
  Subsequently, we can use ~c[(naturalp n)] wherever we need to note
  that a quantity is a natural number.  ~l[defmacro] for more
  information about ACL2 macros.  With this macro, we can reformulate
  our theorem as follows:
  ~bv[]

    (defthm hanoi-moves-required
      (implies (naturalp n)
               (equal (len (hanoi a b c n))
                      (1- (expt 2 n))))).

  ~ev[]
  Another interesting (but much harder) theorem asserts that the list
  of moves generated by our ~c[hanoi] function actually accomplishes
  the desired goal while following the rules.  When you can state and
  prove that theorem, you'll be a very competent ACL2 user.

  By the way, the name ``Towers of Hanoi'' derives from a legend that
  a group of Vietnamese monks works day and night to move a stack of
  64 gold disks from one diamond peg to another, following the rules
  set out above.  We're told that the world will end when they
  complete this task.  From the theorem above, we know that this
  requires 18,446,744,073,709,551,615 moves:
  ~bv[]

    ACL2 !>(1- (expt 2 64))
    18446744073709551615
    ACL2 !>

  ~ev[]
  We're guessing they won't finish any time soon.")

(deflabel Tutorial2-Eights-Problem
  :doc
  ":Doc-Section Annotated-Acl2-Scripts

  The Eights Problem Example~/

  This example was written almost entirely by Bill Young of
  Computational Logic, Inc.~/

  This simple example was brought to our attention as one that Paul
  Jackson has solved using the NuPrl system.  The challenge is to
  prove the theorem:
  ~bv[]

    for all n > 7, there exist naturals i and j such that: n = 3i + 5j.

  ~ev[]
  In ACL2, we could phrase this theorem using quantification.  However
  we will start with a constructive approach, i.e., we will show that
  values of ~c[i] and ~c[j] exist by writing a function that will
  construct such values for given ~c[n].  Suppose we had a function
  ~c[(split n)] that returns an appropriate pair ~c[(i . j)].  Our
  theorem would be as follows:
  ~bv[]

    (defthm split-splits
      (let ((i (car (split n)))
            (j (cdr (split n))))
        (implies (and (integerp n)
                      (< 7 n))
                 (and (integerp i)
                      (<= 0 i)
                      (integerp j)
                      (<= 0 j)
                      (equal (+ (* 3 i) (* 5 j)) 
                             n)))))

  ~ev[]
  That is, assuming that ~c[n] is a natural number greater than 7,
  ~c[(split n)] returns values ~c[i] and ~c[j] that are in the
  appropriate relation to ~c[n].

  Let's look at a few cases:
  ~bv[]

    8 = 3x1 + 5x1;    11 = 3x2 + 5x1;     14 = 3x3 + 5x1;   ...
    9 = 3x3 + 5x0;    12 = 3x4 + 5x0;     15 = 3x5 + 5x0;   ...
   10 = 3x0 + 5x2;    13 = 3x1 + 5x2;     16 = 3x2 + 5x2;   ...

  ~ev[]
  Maybe you will have observed a pattern here; any natural number larger
  than 10 can be obtained by adding some multiple of 3 to 8, 9, or 10.
  This gives us the clue to constructing a proof.   It is clear that we
  can write split as follows:
  ~bv[]

    (defun bump-i (x)
      ;; Bump the i component of the pair
      ;; (i . j) by 1.
      (cons (1+ (car x)) (cdr x)))

    (defun split (n)
      ;; Find a pair (i . j) such that 
      ;; n = 3i + 5j.
      (if (or (zp n) (< n 8))
          nil ;; any value is really reasonable here
        (if (equal n 8)
            (cons 1 1)
          (if (equal n 9)
              (cons 3 0)
            (if (equal n 10)
                (cons 0 2)
              (bump-i (split (- n 3))))))))

  ~ev[]
  Notice that we explicitly compute the values of ~c[i] and ~c[j] for
  the cases of 8, 9, and 10, and for the degenerate case when ~c[n] is
  not a natural or is less than 8.  For all naturals greater than
  ~c[n], we decrement ~c[n] by 3 and bump the number of 3's (the value
  of i) by 1.  We know that the recursion must terminate because any
  integer value greater than 10 can eventually be reduced to 8, 9, or
  10 by successively subtracting 3.

  Let's try it on some examples:
  ~bv[]

    ACL2 !>(split 28)
    (6 . 2)

    ACL2 !>(split 45)
    (15 . 0)

    ACL2 !>(split 335)
    (110 . 1)

  ~ev[]
  Finally, we submit our theorem ~c[split-splits], and the proof
  succeeds.  In this case, the prover is ``smart'' enough to induct
  according to the pattern indicated by the function split.

  For completeness, we'll note that we can state and prove a quantified
  version of this theorem.  We introduce the notion ~c[split-able] to mean
  that appropriate ~c[i] and ~c[j] exist for ~c[n].
  ~bv[]

    (defun-sk split-able (n)
      (exists (i j)
              (equal n (+ (* 3 i) (* 5 j)))))

  ~ev[]
  Then our theorem is given below.  Notice that we prove it by
  observing that our previous function ~c[split] delivers just such an
  ~c[i] and ~c[j] (as we proved above).
  ~bv[]

    (defthm split-splits2 
      (implies (and (integerp n)
                    (< 7 n))
               (split-able n))
      :hints ((\"Goal\" :use (:instance split-able-suff 
                                      (i (car (split n)))
                                      (j (cdr (split n)))))))

  ~ev[]
  Unfortunately, understanding the mechanics of the proof requires
  knowing something about the way ~ilc[defun-sk] works.
  ~l[defun-sk] or ~pl[Tutorial4-Defun-Sk-Example] for more on
  that subject.")

(deflabel Tutorial3-Phonebook-Example

; Here is another solution to the exercise at the end of this topic.

;  (defun good-phonebookp (bk)
;    (setp (range bk)))
; 
;  (defthm member-equal-strip-cdrs-bind
;    (implies (and (not (member-equal x (strip-cdrs bk)))
;                  (not (equal x num)))
;             (not (member-equal x (strip-cdrs (bind nm num bk))))))
; 
;  (defthm setp-range-bind
;    (implies (and (setp (range bk))
;                  (not (member num (range bk))))
;             (setp (range (bind nm num bk))))
;    :hints (("Goal" :in-theory (enable bind range))))
; 
;  (defthm ADD-PHONE-PRESERVES-NEW-INVARIANT
;    (implies (and (good-phonebookp bk)
;                  (not (member num (range bk))))
;             (good-phonebookp (add-phone nm num bk))))
; 
;  (defthm CHANGE-PHONE-PRESERVES-NEW-INVARIANT
;    (implies (and (good-phonebookp bk)
;                  (not (member num (range bk))))
;             (good-phonebookp (change-phone nm num bk))))
; 
;  (defthm member-equal-strip-cdrs-rembind
;    (implies (not (member-equal x (strip-cdrs bk)))
;             (not (member-equal x (strip-cdrs (rembind nm bk))))))
; 
;  (defthm setp-strip-cdrs-rembind
;    (implies (setp (strip-cdrs bk))
;             (setp (strip-cdrs (rembind nm bk))))
;    :hints (("Goal" :in-theory (enable rembind))))
; 
;  (defthm DEL-PHONE-PRESERVES-NEW-INVARIANT
;    (implies (good-phonebookp bk)
;             (good-phonebookp (del-phone nm bk)))
;    :hints (("Goal" :in-theory (enable range))))

  :doc
  ":Doc-Section Annotated-Acl2-Scripts

  A Phonebook Specification~/

  The other tutorial examples are rather small and entirely self
  contained.  The present example is rather more elaborate, and makes
  use of a feature that really adds great power and versatility to
  ACL2, namely:  the use of previously defined collections of lemmas,
  in the form of ``~il[books].''

  This example was written almost entirely by Bill Young of
  Computational Logic, Inc.~/

  This example is based on one developed by Ricky Butler and Sally
  Johnson of NASA Langley for the PVS system, and subsequently revised
  by Judy Crow, ~i[et al], at SRI.  It is a simple phone book
  specification.  We will not bother to follow their versions closely,
  but will instead present a style of specification natural for ACL2.

  The idea is to model an electronic phone book with the following
  properties.
  ~bq[]

  Our phone book will store the phone numbers of a city.

  It must be possible to retrieve a phone number, given a name.

  It must be possible to add and delete entries. 

  ~eq[]

  Of course, there are numerous ways to construct such a model.  A
  natural approach within the Lisp/ACL2 context is to use
  ``association lists'' or ``alists.''  Briefly, an alist is a list of
  pairs ~c[(key .  value)] associating a value with a key.  A phone
  book could be an alist of pairs ~c[(name . pnum)].  To find the phone
  number associated with a given name, we merely search the alist
  until we find the appropriate pair.  For a large city, such a linear
  list would not be efficient, but at this point we are interested
  only in ~b[modeling] the problem, not in deriving an efficient
  implementation.  We could address that question later by proving our
  alist model equivalent, in some desired sense, to a more efficient
  data structure.

  We could build a theory of alists from scratch, or we can use a
  previously constructed theory (book) of alist definitions and facts.
  By using an existing book, we build upon the work of others, start
  our specification and proof effort from a much richer foundation,
  and hopefully devote more of our time to the problem at hand.
  Unfortunately, it is not completely simple for the new user to know
  what ~il[books] are available and what they contain.  We hope later
  to improve the documentation of the growing collection of ~il[books]
  available with the ACL2 distribution; for now, the reader is
  encouraged to look in the README file in the ~c[books] subdirectory.
  For present purposes, the beginning user can simply take our word
  that a book exists containing useful alist definitions and facts.
  These definitions and lemmas can be introduced
  into the current theory using the ~il[command]:
  ~bv[]

    (include-book \"data-structures/alist-defthms\" :dir :system)

  ~ev[]
  This book has been ``certified,'' which means that the definitions
  and lemmas have been mechanically checked and stored in a safe
  manner.  (~l[books] and ~pl[include-book] for details.)

  Including this book makes available a collection of functions
  including the following:
  ~bv[]

  (ALISTP A)    ; is A an alist (actually a primitive ACL2 function)

  (BIND X V A)  ; associate the key X with value V in alist A

  (BINDING X A) ; return the value associated with key X in alist A

  (BOUND? X A)  ; is key X associated with any value in alist A

  (DOMAIN A)    ; return the list of keys bound in alist A

  (RANGE A)     ; return the list of values bound to keys in alist A

  (REMBIND X A) ; remove the binding of key X in alist A

  ~ev[]
  Along with these function definitions, the book also provides a
  number of proved lemmas that aid in simplifying expressions
  involving these functions.  (~l[rule-classes] for the way in
  which lemmas are used in simplification and rewriting.)  For
  example,
  ~bv[]

    (defthm bound?-bind 
      (equal (bound? x (bind y v a))
             (or (equal x y)
                 (bound? x a))))

  ~ev[]
  asserts that ~c[x] will be bound in ~c[(bind y v a)] if and only if:
  either ~c[x = y] or ~c[x] was already bound in ~c[a].  Also,
  ~bv[]

    (defthm binding-bind
      (equal (binding x (bind y v a))
             (if (equal x y)
                 v
               (binding x a))))

  ~ev[]
  asserts that the resulting binding will be ~c[v], if ~c[x = y], or the
  binding that ~c[x] had in ~c[a] already, if not.

  Thus, the inclusion of this book essentially extends our
  specification and reasoning capabilities by the addition of new
  operations and facts about these operations that allow us to build
  further specifications on a richer and possibly more intuitive
  foundation.

  However, it must be admitted that the use of a book such as this has
  two potential limitations:
  ~bq[]

  the definitions available in a book may not be ideal for your
  particular problem;

  it is (extremely) likely that some useful facts (especially, ~il[rewrite]
  rules) are not available in the book and will have to be proved.

  ~eq[]
  For example, what is the value of ~c[binding] when given a key that
  is not bound in the alist?  We can find out by examining the
  function definition.  Look at the definition of the ~c[binding]
  function (or any other defined function), using the ~c[:]~ilc[pe] command:
  ~bv[]

    ACL2 !>:pe binding
       d     33  (INCLUDE-BOOK
                      \"/slocal/src/acl2/v1-9/books/public/alist-defthms\")
                 \
    >V d          (DEFUN BINDING (X A)
                         \"The value bound to X in alist A.\"
                         (DECLARE (XARGS :GUARD (ALISTP A)))
                         (CDR (ASSOC-EQUAL X A)))

  ~ev[]

  This tells us that ~c[binding] was introduced by the given
  ~ilc[include-book] form, is currently ~il[disable]d in the current
  theory, and has the definition given by the displayed ~ilc[defun] form.
  We see that ~c[binding] is actually defined in terms of the primitive
  ~ilc[assoc-equal] function.  If we look at the definition of
  ~ilc[assoc-equal]:
  ~bv[]

    ACL2 !>:pe assoc-equal
     V     -489  (DEFUN ASSOC-EQUAL (X ALIST)
                        (DECLARE (XARGS :GUARD (ALISTP ALIST)))
                        (COND ((ENDP ALIST) NIL)
                              ((EQUAL X (CAR (CAR ALIST)))
                               (CAR ALIST))
                              (T (ASSOC-EQUAL X (CDR ALIST)))))

  ~ev[]

  we can see that ~ilc[assoc-equal] returns ~c[nil] upon reaching the end
  of an unsuccessful search down the alist.  So ~c[binding] returns
  ~c[(cdr nil)] in that case, which is ~c[nil].  Notice that we could also
  have investigated this question by trying some simple examples.
  ~bv[]

    ACL2 !>(binding 'a nil)
    NIL

    ACL2 !>(binding 'a (list (cons 'b 2)))
    NIL

  ~ev[]

  These definitions aren't ideal for all purposes. For one thing,
  there's nothing that keeps us from having ~c[nil] as a value bound to
  some key in the alist.  Thus, if ~c[binding] returns ~c[nil] we don't
  always know if that is the value associated with the key in the
  alist, or if that key is not bound.  We'll have to keep that
  ambiguity in mind whenever we use ~c[binding] in our specification.
  Suppose instead that we wanted ~c[binding] to return some error
  string on unbound keys.  Well, then we'd just have to write our own
  version of ~c[binding].  But then we'd lose much of the value of
  using a previously defined book.  As with any specification
  technique, certain tradeoffs are necessary.

  Why not take a look at the definitions of other alist functions and
  see how they work together to provide the ability to construct and
  search alists?  We'll be using them rather heavily in what follows
  so it will be good if you understand basically how they work.
  Simply start up ACL2 and execute the form shown earlier, but
  substituting our directory name for the top-level ACL2 directory
  with yours.  Alternatively, just
  ~bv[]

    (include-book \"data-structures/alist-defthms\" :dir :system)

  ~ev[]
  Then, you can use ~c[:]~il[pe] to look at function definitions.
  You'll soon discover that almost all of the definitions are built on
  definitions of other, more primitive functions, as ~c[binding] is
  built on ~ilc[assoc-equal].  You can look at those as well, of course,
  or in many cases visit their documentation.

  The other problem with using a predefined book is that it will
  seldom be ``sufficiently complete,'' in the sense that the
  collection of ~il[rewrite] rules supplied won't be adequate to prove
  everything we'd like to know about the interactions of the various
  functions.  If it were, there'd be no real reason to know that
  ~c[binding] is built on top of ~ilc[assoc-equal], because everything
  we'd need to know about ~c[binding] would be nicely expressed in the
  collection of theorems supplied with the book.  However, that's very
  seldom the case.  Developing such a collection of rules is currently
  more art than science and requires considerable experience.  We'll
  encounter examples later of ``missing'' facts about ~c[binding] and
  our other alist functions.  So, let's get on with the example.

  Notice that alists are mappings of keys to values; but, there is no
  notion of a ``type'' associated with the keys or with the values.
  Our phone book example, however, does have such a notion of types;
  we map names to phone numbers.  We can introduce these ``types'' by
  explicitly defining them, e.g., names are strings and phone numbers
  are integers.  Alternatively, we can ~b[partially define] or
  axiomatize a recognizer for names without giving a full definition.
  A way to safely introduce such ``constrained'' function symbols in
  ACL2 is with the ~ilc[encapsulate] form.  For example, consider the
  following form.
  ~bv[]

    (encapsulate
      ;; Introduce a recognizer for names and give a ``type'' lemma.
      (((namep *) => *))
      ;;
      (local (defun namep (x)
               ;; This declare is needed to tell
               ;; ACL2 that we're aware that the 
               ;; argument x is not used in the body
               ;; of the function.
               (declare (ignore x))
               t))
      ;;
      (defthm namep-booleanp
        (booleanp (namep x))))

  ~ev[] 

  This ~ilc[encapsulate] form introduces the new function ~c[namep] of one
  argument and one result and constrains ~c[(namep x)] to be Boolean,
  for all inputs ~c[x].  More generally, an encapsulation establishes
  an environment in which functions can be defined and theorems and
  rules added without necessarily introducing those functions,
  theorems, and rules into the environment outside the encapsulation.
  To be admissible, all the events in the body of an encapsulate must be
  admissible.  But the effect of an encapsulate is to assume only the
  non-local events.

  The first ``argument'' to ~c[encapsulate], ~c[((namep (x) t))] above,
  declares the intended ~il[signature]s of new function symbols that
  will be ``exported'' from the encapsulation without definition.  The
  ~ilc[local] ~ilc[defun] of ~c[name] defines name within the encapsulation
  always to return ~c[t].  The ~c[defthm] event establishes that
  ~c[namep] is Boolean.  By making the ~c[defun] local but the ~c[defthm]
  non-~c[local] this encapsulate constrains the undefined function
  ~c[namep] to be Boolean; the admissibility of the encapsulation
  establishes that there exists a Boolean function (namely the
  constant function returning ~c[t]).

  We can subsequently use ~c[namep] as we use any other Boolean
  function, with the proviso that we know nothing about it except that
  it always returns either ~c[t] or ~c[nil].  We use ~c[namep] to
  ``recognize'' legal keys for our phonebook alist.

  We wish to do something similar to define what it means to be a legal
  phone number.  We submit the following form to ACL2:
  ~bv[]

    (encapsulate
      ;; Introduce a recognizer for phone numbers.
      (((pnump *) => *))
      ;;
      (local (defun pnump (x)
               (not (equal x nil))))
      ;;
      (defthm pnump-booleanp
        (booleanp (pnump x)))
      ;;
      (defthm nil-not-pnump
        (not (pnump nil)))).

  ~ev[]
  This introduces a Boolean-valued recognizer ~c[pnump], with the
  additional proviso that the constant ~c[nil] is not a ~c[pnump].  We
  impose this restriction to guarantee that we'll never bind a name to
  ~c[nil] in our phone book and thereby introduce the kind of ambiguity
  described above regarding the use of ~c[binding].

  Now a legal phone book is an alist mapping from ~c[namep]s to
  ~c[pnump]s.  We can define this as follows:
  ~bv[]

    (defun name-phonenum-pairp (x)
      ;; Recognizes a pair of (name . pnum).
      (and (consp x)
           (namep (car x))
           (pnump (cdr x))))

    (defun phonebookp (l)
      ;; Recognizes a list of such pairs.
      (if (not (consp l))
          (null l)
        (and (name-phonenum-pairp (car l))
             (phonebookp (cdr l)))))

  ~ev[]
  Thus, a phone book is really a list of pairs ~c[(name . pnum)].
  Notice that we have not assumed that the keys of the phone book are
  distinct.  We'll worry about that question later.  (It is not always
  desirable to insist that the keys of an alist be distinct.  But it
  may be a useful requirement for our specific example.)

  Now we are ready to define some of the functions necessary for our
  phonebook example.  The functions we need are:

  ~bv[]

  (IN-BOOK? NM BK)          ; does NM have a phone number in BK

  (FIND-PHONE NM BK)        ; find NM's phone number in phonebook BK

  (ADD-PHONE NM PNUM BK)    ; give NM the phone number PNUM in BK

  (CHANGE-PHONE NM PNUM BK) ; change NM's phone number to PNUM in BK

  (DEL-PHONE NM PNUM)       ; remove NM's phone number from BK

  ~ev[]

  Given our underlying theory of alists, it is easy to write these
  functions.  But we must take care to specify appropriate
  ``boundary'' behavior.  Thus, what behavior do we want when, say, we
  try to change the phone number of a client who is not currently in
  the book?  As usual, there are numerous possibilities; here we'll
  assume that we return the phone book unchanged if we try anything
  ``illegal.''

  Possible definitions of our phone book functions are as follows.
  (Remember, an ~c[include-book] form such as the ones shown earlier
  must be executed in order to provide definitions for functions such
  as ~c[bound?].)
  ~bv[]

    (defun in-book? (nm bk)
      (bound? nm bk))

    (defun find-phone (nm bk)
      (binding nm bk))

    (defun add-phone (nm pnum bk)
      ;; If nm already in-book?, make no change.
      (if (in-book? nm bk)
          bk
        (bind nm pnum bk)))

    (defun change-phone (nm pnum bk)
      ;; Make a change only if nm already has a phone number.
      (if (in-book? nm bk)
          (bind nm pnum bk)
        bk))

    (defun del-phone (nm bk)
      ;; Remove the binding from bk, if there is one.
      (rembind nm bk))

  ~ev[]
  Notice that we don't have to check whether a name is in the book
  before deleting, because ~c[rembind] is essentially a no-op if ~c[nm]
  is not bound in ~c[bk].

  In some sense, this completes our specification.  But we can't have
  any real confidence in its correctness without validating our
  specification in some way.  One way to do so is by proving some
  properties of our specification.  Some candidate properties are:
  ~bq[]

  1. A name will be in the book after we add it.

  2. We will find the most recently added phone number for a client.

  3. If we change a number, we'll find the change.

  4. Changing and then deleting a number is the same as just deleting.

  5. A name will not be in the book after we delete it.
  ~eq[]

  Let's formulate some of these properties.  The first one, for example, is:
  ~bv[]

    (defthm add-in-book 
      (in-book? nm (add-phone nm pnum bk))).

  ~ev[]
  You may wonder why we didn't need any hypotheses about the ``types''
  of the arguments.  In fact, ~c[add-in-book] is really expressing a
  property that is true of alists in general, not just of the
  particular variety of alists we are dealing with.  Of course, we
  could have added some extraneous hypotheses and proved:
  ~bv[]

    (defthm add-in-book 
      (implies (and (namep nm)
                    (pnump pnum)
                    (phonebookp bk))
               (in-book? nm (add-phone nm pnum bk)))),

  ~ev[]
  but that would have yielded a weaker and less useful lemma because it
  would apply to fewer situations.  In general, it is best to state
  lemmas in the most general form possible and to eliminate unnecessary
  hypotheses whenever possible.  The reason for that is simple: lemmas
  are usually stored as rules and used in later proofs.  For a lemma to
  be used, its hypotheses must be relieved (proved to hold in that
  instance); extra hypotheses require extra work.  So we avoid them
  whenever possible. 

  There is another, more important observation to make about our
  lemma.  Even in its simpler form (without the extraneous
  hypotheses), the lemma ~c[add-in-book] may be useless as a
  ~il[rewrite] rule.  Notice that it is stated in terms of the
  non-recursive functions ~c[in-book?] and ~c[add-phone].  If such
  functions appear in the left hand side of the conclusion of a lemma,
  the lemma may not ever be used.  Suppose in a later proof, the
  theorem prover encountered a ~il[term] of the form:
  ~bv[]

    (in-book? nm (add-phone nm pnum bk)).

  ~ev[]
  Since we've already proved ~c[add-in-book], you'd expect that this
  would be immediately reduced to true.  However, the theorem prover
  will often ``expand'' the non-recursive definitions of ~c[in-book?]
  and ~c[add-phone] using their definitions ~b[before] it attempts
  rewriting with lemmas.  After this expansion, lemma ~c[add-in-book]
  won't ``match'' the ~il[term] and so won't be applied.  Look back at
  the proof script for ~c[add-in-proof] and you'll notice that at the
  very end the prover warned you of this potential difficulty when it
  printed:
  ~bv[]

    Warnings:  Non-rec
    Time:  0.18 seconds (prove: 0.05, print: 0.00, other: 0.13)
    ADD-IN-BOOK

  ~ev[]
  The ``Warnings'' line notifies you that there are non-recursive
  function calls in the left hand side of the conclusion and that this
  problem might arise.  Of course, it may be that you don't ever plan
  to use the lemma for rewriting or that your intention is to
  ~il[disable] these functions.  ~il[Disable]d functions are not
  expanded and the lemma should apply.  However, you should always
  take note of such warnings and consider an appropriate response.  By
  the way, we noted above that ~c[binding] is ~il[disable]d.  If it
  were not, none of the lemmas about ~c[binding] in the book we
  included would likely be of much use for exactly the reason we just
  gave.

  For our current example, let's assume that we're just investigating
  the properties of our specifications and not concerned about using
  our lemmas for rewriting.  So let's go on.  If we really want to
  avoid the warnings, we can add ~c[:rule-classes nil] to each
  ~c[defthm] event; ~pl[rule-classes].

  Property 2 is:  we always find the most recently added phone number
  for a client.  Try the following formalization:
  ~bv[]

    (defthm find-add-first-cut
      (equal (find-phone nm (add-phone nm pnum bk))
             pnum))

  ~ev[]
  and you'll find that the proof attempt fails.  Examining the proof
  attempt and our function definitions, we see that the lemma is false
  if ~c[nm] is already in the book.  We can remedy this situation by
  reformulating our lemma in at least two different ways:
  ~bv[]

    (defthm find-add1
      (implies (not (in-book? nm bk))
               (equal (find-phone nm (add-phone nm pnum bk))
                      pnum)))

    (defthm find-add2
      (equal (find-phone nm (add-phone nm pnum bk))
             (if (in-book? nm bk)
                 (find-phone nm bk)
                 pnum)))

  ~ev[]
  For technical reasons, lemmas such as ~c[find-add2], i.e., which do
  not have hypotheses, are usually slightly preferable.  This lemma is
  stored as an ``unconditional'' ~il[rewrite] rule (i.e., has no
  hypotheses) and, therefore, will apply more often than ~c[find-add1].
  However, for our current purposes either version is all right.

  Property 3 says: If we change a number, we'll find the change.  This
  is very similar to the previous example.  The formalization is as
  follows.
  ~bv[]

    (defthm find-change
      (equal (find-phone nm (change-phone nm pnum bk))
             (if (in-book? nm bk)
                 pnum
               (find-phone nm bk))))

  ~ev[]
  Property 4 says: changing and then deleting a number is the same as
  just deleting.  We can model this as follows.
  ~bv[]

    (defthm del-change
      (equal (del-phone nm (change-phone nm pnum bk))
             (del-phone nm bk)))

  ~ev[]
  Unfortunately, when we try to prove this, we encounter subgoals that
  seem to be true, but for which the prover is stumped.  For example,
  consider the following goal.  (Note:  ~c[endp] holds of lists that
  are empty.)
  ~bv[]

    Subgoal *1/4
    (IMPLIES (AND (NOT (ENDP BK))
                  (NOT (EQUAL NM (CAAR BK)))
                  (NOT (BOUND? NM (CDR BK)))
                  (BOUND? NM BK))
             (EQUAL (REMBIND NM (BIND NM PNUM BK))
                    (REMBIND NM BK))).

  ~ev[]
  Our intuition about ~c[rembind] and ~c[bind] tells us that this goal
  should be true even without the hypotheses.  We attempt to prove the 
  following lemma.
  ~bv[]

    (defthm rembind-bind 
      (equal (rembind nm (bind nm pnum bk))
             (rembind nm bk)))

  ~ev[]
  The prover proves this by induction, and stores it as a rewrite
  rule.  After that, the prover has no difficulty in proving
  ~c[del-change].

  The need to prove lemma ~c[rembind-bind] illustrates a point we made
  early in this example:  the collection of ~il[rewrite] rules
  supplied by a previously certified book will almost never be
  everything you'll need.  It would be nice if we could operate purely
  in the realm of names, phone numbers, and phone books without ever
  having to prove any new facts about alists.  Unfortunately, we
  needed a fact about the relation between ~c[rembind] and ~c[bind] that
  wasn't supplied with the alists theory.  Hopefully, such omissions
  will be rare.

  Finally, let's consider our property 5 above:  a name will not be in
  the book after we delete it.  We formalize this as follows:
  ~bv[]

    (defthm in-book-del
      (not (in-book? nm (del-phone nm bk))))

  ~ev[]
  This proves easily.  But notice that it's only true because
  ~c[del-phone] (actually ~c[rembind]) removes ~b[all] occurrences of a
  name from the phone book.  If it only removed, say, the first one it
  encountered, we'd need a hypothesis that said that ~c[nm] occurs at
  most once in ~c[bk].  Ah, maybe that's a property you hadn't
  considered.  Maybe you want to ensure that ~b[any] name occurs at
  most once in any valid phonebook.

  To complete this example, let's consider adding an ~b[invariant] to
  our specification.  In particular, suppose we want to assure that no
  client has more than one associated phone number.  One way to ensure
  this is to require that the domain of the alist is a ``set'' (has no
  duplicates).
  ~bv[]

    (defun setp (l)
      (if (atom l)
          (null l)
        (and (not (member-equal (car l) (cdr l)))
             (setp (cdr l)))))

    (defun valid-phonebookp (bk)
      (and (phonebookp bk)
           (setp (domain bk))))

  ~ev[]
  Now, we want to show under what conditions our operations preserve
  the property of being a ~c[valid-phonebookp].  The operations
  ~c[in-book?]  and ~c[find-phone] don't return a phone book, so we
  don't really need to worry about them.  Since we're really
  interested in the ``types'' of values preserved by our phonebook
  functions, let's look at the types of those operations as well.
  ~bv[]

    (defthm in-book-booleanp
      (booleanp (in-book? nm bk)))

    (defthm in-book-namep
      (implies (and (phonebookp bk)
                    (in-book? nm bk))
               (namep nm))
      :hints ((\"Goal\" :in-theory (enable bound?))))

    (defthm find-phone-pnump
      (implies (and (phonebookp bk)
                    (in-book? nm bk))
               (pnump (find-phone nm bk)))
      :hints ((\"Goal\" :in-theory (enable bound? binding))))

  ~ev[]
  Note the ``~c[:]~ilc[hints]'' on the last two lemmas.  Neither of these
  would prove without these ~il[hints], because once again there are
  some facts about ~c[bound?] and ~c[binding] not available in our
  current context.  Now, we could figure out what those facts are and
  try to prove them.  Alternatively, we can ~il[enable] ~c[bound?] and
  ~c[binding] and hope that by opening up these functions, the
  conjectures will reduce to versions that the prover does know enough
  about or can prove by induction.  In this case, this strategy works.
  The hints tell the prover to ~il[enable] the functions in question
  when considering the designated goal.

  Below we develop the theorems showing that ~c[add-phone],
  ~c[change-phone], and ~c[del-phone] preserve our proposed invariant.
  Notice that along the way we have to prove some subsidiary facts,
  some of which are pretty ugly.  It would be a good idea for you to
  try, say, ~c[add-phone-preserves-invariant] without introducing the
  following four lemmas first.  See if you can develop the proof and
  only add these lemmas as you need assistance.  Then try
  ~c[change-phone-preserves-invariant] and ~c[del-phone-preserves-invariant].
  They will be easier.  It is illuminating to think about why
  ~c[del-phone-preserves-invariant] does not need any ``type''
  hypotheses.
  ~bv[]

    (defthm bind-preserves-phonebookp
      (implies (and (phonebookp bk)
                    (namep nm)
                    (pnump num))
               (phonebookp (bind nm num bk))))
    
    (defthm member-equal-strip-cars-bind 
      (implies (and (not (equal x y))
                    (not (member-equal x (strip-cars a))))
               (not (member-equal x (strip-cars (bind y z a))))))
    
    (defthm bind-preserves-domain-setp 
      (implies (and (alistp bk)
                    (setp (domain bk)))
               (setp (domain (bind nm num bk))))
      :hints ((\"Goal\" :in-theory (enable domain))))
    
    (defthm phonebookp-alistp
      (implies (phonebookp bk)
               (alistp bk)))
    
    (defthm ADD-PHONE-PRESERVES-INVARIANT
      (implies (and (valid-phonebookp bk)
                    (namep nm)
                    (pnump num))
               (valid-phonebookp (add-phone nm num bk)))
      :hints ((\"Goal\" :in-theory (disable domain-bind))))
    
    (defthm CHANGE-PHONE-PRESERVES-INVARIANT
      (implies (and (valid-phonebookp bk)
                    (namep nm)
                    (pnump num))
               (valid-phonebookp (change-phone nm num bk)))
      :hints ((\"Goal\" :in-theory (disable domain-bind))))
    
    (defthm remove-equal-preserves-setp
      (implies (setp l)
               (setp (remove-equal x l))))
    
    (defthm rembind-preserves-phonebookp 
      (implies (phonebookp bk)
               (phonebookp (rembind nm bk))))
    
    (defthm DEL-PHONE-PRESERVES-INVARIANT
      (implies (valid-phonebookp bk)
               (valid-phonebookp (del-phone nm bk))))
  ~ev[]

  As a final test of your understanding, try to formulate and prove an
  invariant that says that no phone number is assigned to more than
  one name.  The following hints may help.
  ~bq[]

  1. Define the appropriate invariant.  (Hint: remember the function
  ~c[range].)

  2. Do our current definitions of ~c[add-phone] and ~c[change-phone]
  necessarily preserve this property?  If not, consider what
  hypotheses are necessary in order to guarantee that they do preserve
  this property.

  3. Study the definition of the function ~c[range] and notice that it
  is defined in terms of the function ~ilc[strip-cdrs].  Understand how
  this defines the range of an alist.

  4. Formulate the correctness theorems and attempt to prove them.
  You'll probably benefit from studying the invariant proof above.  In
  particular, you may need some fact about the function ~ilc[strip-cdrs]
  analogous to the lemma ~c[member-equal-strip-cars-bind] above.

  ~eq[]

  Below is one solution to this exercise.  Don't look at the solution,
  however, until you've struggled a bit with it.  Notice that we
  didn't actually change the definitions of ~c[add-phone] and
  ~c[change-phone], but added a hypothesis saying that the number is
  ``new.''  We could have changed the definitions to check this and
  return the phonebook unchanged if the number was already in use.
  ~bv[]

    (defun pnums-in-use (bk)
      (range bk))
    
    (defun phonenums-unique (bk)
      (setp (pnums-in-use bk)))
    
    (defun new-pnump (pnum bk)
      (not (member-equal pnum (pnums-in-use bk))))
    
    (defthm member-equal-strip-cdrs-rembind
      (implies (not (member-equal x (strip-cdrs y)))
               (not (member-equal x (strip-cdrs (rembind z y))))))
    
    (defthm DEL-PHONE-PRESERVES-PHONENUMS-UNIQUE
      (implies (phonenums-unique bk)
               (phonenums-unique (del-phone nm bk)))
      :hints ((\"Goal\" :in-theory (enable range))))
    
    (defthm strip-cdrs-bind-non-member
      (implies (and (not (bound? x a))
                    (alistp a))
               (equal (strip-cdrs (bind x y a))
                      (append (strip-cdrs a) (list y))))
      :hints ((\"Goal\" :in-theory (enable bound?))))
    
    (defthm setp-append-list 
      (implies (setp l)
               (equal (setp (append l (list x)))
                      (not (member-equal x l)))))
    
    (defthm ADD-PHONE-PRESERVES-PHONENUMS-UNIQUE
      (implies (and (phonenums-unique bk)
                    (new-pnump pnum bk)
                    (alistp bk))
               (phonenums-unique (add-phone nm pnum bk)))
      :hints ((\"Goal\" :in-theory (enable range))))
    
    (defthm member-equal-strip-cdrs-bind
      (implies (and (not (member-equal z (strip-cdrs a)))
                    (not (equal z y)))
               (not (member-equal z (strip-cdrs (bind x y a))))))
    
    (defthm CHANGE-PHONE-PRESERVES-PHONENUMS-UNIQUE
      (implies (and (phonenums-unique bk)
                    (new-pnump pnum bk)
                    (alistp bk))
               (phonenums-unique (change-phone nm pnum bk)))
      :hints ((\"Goal\" :in-theory (enable range))))
  ~ev[]
  ")

(deflabel Tutorial4-Defun-Sk-Example
  :doc
  ":Doc-Section annotated-acl2-scripts

  example of quantified notions~/

  This example illustrates the use of ~ilc[defun-sk] and ~ilc[defthm]
  ~il[events] to reason about quantifiers.  ~l[defun-sk].  For a more through,
  systematic beginner's introduction to quantification in ACL2,
  ~pl[quantifier-tutorial].

  Many users prefer to avoid the use of quantifiers, since ACL2
  provides only very limited support for reasoning about
  quantifiers.~/

  Here is a list of ~il[events] that proves that if there are arbitrarily
  large numbers satisfying the disjunction ~c[(OR P R)], then either
  there are arbitrarily large numbers satisfying ~c[P] or there are
  arbitrarily large numbers satisfying ~c[R].
  ~bv[]

  ; Introduce undefined predicates p and r.
  (defstub p (x) t)
  (defstub r (x) t)

  ; Define the notion that something bigger than x satisfies p.
  (defun-sk some-bigger-p (x)
    (exists y (and (< x y) (p y))))

  ; Define the notion that something bigger than x satisfies r.
  (defun-sk some-bigger-r (x)
    (exists y (and (< x y) (r y))))

  ; Define the notion that arbitrarily large x satisfy p.
  (defun-sk arb-lg-p ()
    (forall x (some-bigger-p x)))

  ; Define the notion that arbitrarily large x satisfy r.
  (defun-sk arb-lg-r ()
    (forall x (some-bigger-r x)))

  ; Define the notion that something bigger than x satisfies p or r.
  (defun-sk some-bigger-p-or-r (x)
    (exists y (and (< x y) (or (p y) (r y)))))

  ; Define the notion that arbitrarily large x satisfy p or r.
  (defun-sk arb-lg-p-or-r ()
    (forall x (some-bigger-p-or-r x)))

  ; Prove the theorem promised above.  Notice that the functions open
  ; automatically, but that we have to provide help for some rewrite
  ; rules because they have free variables in the hypotheses.  The
  ; ``witness functions'' mentioned below were introduced by DEFUN-SK.

  (thm
   (implies (arb-lg-p-or-r)
            (or (arb-lg-p)
                (arb-lg-r)))
   :hints ((\"Goal\"
            :use
            ((:instance some-bigger-p-suff
                        (x (arb-lg-p-witness))
                        (y (some-bigger-p-or-r-witness 
                            (max (arb-lg-p-witness)
                                 (arb-lg-r-witness)))))
             (:instance some-bigger-r-suff
                        (x (arb-lg-r-witness))
                        (y (some-bigger-p-or-r-witness 
                            (max (arb-lg-p-witness)
                                 (arb-lg-r-witness)))))
             (:instance arb-lg-p-or-r-necc
                        (x (max (arb-lg-p-witness)
                                (arb-lg-r-witness))))))))

  ; And finally, here's a cute little example.  We have already
  ; defined above the notion (some-bigger-p x), which says that
  ; something bigger than x satisfies p.  Let us introduce a notion
  ; that asserts that there exists both y and z bigger than x which
  ; satisfy p.  On first glance this new notion may appear to be
  ; stronger than the old one, but careful inspection shows that y and
  ; z do not have to be distinct.  In fact ACL2 realizes this, and
  ; proves the theorem below automatically.

  (defun-sk two-bigger-p (x)
    (exists (y z) (and (< x y) (p y) (< x z) (p z))))

  (thm (implies (some-bigger-p x) (two-bigger-p x)))

  ; A technical point:  ACL2 fails to prove the theorem above
  ; automatically if we take its contrapositive, unless we disable
  ; two-bigger-p as shown below.  That is because ACL2 needs to expand
  ; some-bigger-p before applying the rewrite rule introduced for
  ; two-bigger-p, which contains free variables.  The moral of the
  ; story is:  Don't expect too much automatic support from ACL2 for
  ; reasoning about quantified notions.

  (thm (implies (not (two-bigger-p x)) (not (some-bigger-p x)))
       :hints ((\"Goal\" :in-theory (disable two-bigger-p))))
  ~ev[]
  ")

(deflabel Tutorial5-Miscellaneous-Examples
  :doc
  ":Doc-Section annotated-acl2-scripts

  miscellaneous ACL2 examples~/

  The following examples are more advanced examples of usage of ACL2.
  They are included largely for reference, in case someone
  finds them useful.~/~/")

(deflabel file-reading-example
  :doc
  ":Doc-Section  Tutorial5-Miscellaneous-Examples

  example of reading files in ACL2~/

  This example illustrates the use of ACL2's ~il[IO] primitives to read the
  forms in a file.  ~l[io].~/

  This example provides a solution to the following problem.  Let's
  say that you have a file that contains s-expressions.  Suppose that
  you want to build a list by starting with ~c[nil], and updating it
  ``appropriately'' upon encountering each successive s-expression in
  the file.  That is, suppose that you have written a function
  ~c[update-list] such that ~c[(update-list obj current-list)] returns
  the list obtained by ``updating'' ~c[current-list] with the next
  object, ~c[obj], encountered in the file.  The top-level function for
  processing such a file, returning the final list, could be defined
  as follows.  Notice that because it opens a channel to the given
  file, this function modifies ~il[state] and hence must return ~il[state].
  Thus it actually returns two values:  the final list and the new
  ~il[state].
  ~bv[]

    (defun process-file (filename state)
      (mv-let
       (channel state)
       (open-input-channel filename :object state)
       (mv-let (result state)
               (process-file1 nil channel state) ;see below
               (let ((state (close-input-channel channel state)))
                 (mv result state)))))

  ~ev[]
  The function ~c[process-file1] referred to above takes the currently
  constructed list (initially, ~c[nil]), together with a channel to the
  file being read and the ~il[state], and returns the final updated
  list.  Notice that this function is tail recursive.  This is
  important because many Lisp compilers will remove tail recursion,
  thus avoiding the potential for stack overflows when the file
  contains a large number of forms.
  ~bv[]

    (defun process-file1 (current-list channel state)
      (mv-let (eofp obj state)
              (read-object channel state)
              (cond
               (eofp (mv current-list state))
               (t (process-file1 (update-list obj current-list)
                                 channel state)))))

  ~ev[]
  ")

(deflabel guard-example
  :doc
  ":Doc-Section Tutorial5-Miscellaneous-Examples

  a brief transcript illustrating ~il[guard]s in ACL2~/

  This note addresses the question:  what is the use of ~il[guard]s in
  ACL2?  Although we recommend that beginners try to avoid ~il[guard]s for
  a while, we hope that the summary here is reasonably self-contained
  and will provide a reasonable introduction to guards in ACL2.  For a
  more systematic discussion, ~pl[guard].  For a summary of that
  topic, ~pl[guard-quick-reference].

  Before we get into the issue of ~il[guard]s, let us note that there are
  two important ``modes'':

  ~il[defun-mode] ~-[] ``Does this ~il[defun] add an axiom (`:logic mode') or not
  (`:program mode')?''  (~l[defun-mode].)  Only ~c[:]~ilc[logic] mode
  functions can have their ``~il[guard]s verified'' via mechanized proof;
  ~pl[verify-guards].

  ~ilc[set-guard-checking] ~-[] ``Should runtime ~il[guard] violations signal an
  error (~c[:all], and usually with ~c[t] or ~c[:nowarn]) or go undetected
  (~c[nil], ~c[:none])?  Equivalently, are expressions evaluated in Common Lisp
  or in the logic?''  (~l[set-guard-checking].)~/

  ~em[Prompt examples]

  Here some examples of the relation between the ACL2 ~il[prompt] and the
  ``modes'' discussed above.  Also ~pl[default-print-prompt].  The
  first examples all have ~c[ld-skip-proofsp nil]; that is, proofs are
  ~em[not] skipped.
  ~bv[]

    ACL2 !>    ; logic mode with guard checking on
    ACL2 >     ; logic mode with guard checking off
    ACL2 p!>   ; program mode with guard checking on
    ACL2 p>    ; program mode with guard checking off

  ~ev[]
  Here are some examples with ~ilc[default-defun-mode] of ~c[:]~ilc[logic].
  ~bv[]

    ACL2 >     ; guard checking off, ld-skip-proofsp nil
    ACL2 s>    ; guard checking off, ld-skip-proofsp t
    ACL2 !>    ; guard checking on, ld-skip-proofsp nil
    ACL2 !s>   ; guard checking on, ld-skip-proofsp t

  ~ev[]

  ~em[Sample session]

  ~bv[]
  ACL2 !>(+ 'abc 3)

  ACL2 Error in TOP-LEVEL: The guard for the function symbol
  BINARY-+, which is (AND (ACL2-NUMBERP X) (ACL2-NUMBERP Y)),
  is violated by the arguments in the call (+ 'ABC 3).

  ACL2 !>:set-guard-checking nil
  ;;;; verbose output omitted here
  ACL2 >(+ 'abc 3)
  3
  ACL2 >(< 'abc 3)
  T
  ACL2 >(< 3 'abc)
  NIL
  ACL2 >(< -3 'abc)
  T
  ACL2 >:set-guard-checking t

  Turning guard checking on, value T.

  ACL2 !>(defun sum-list (x)
          (declare (xargs :guard (integer-listp x)
                          :verify-guards nil))
          (cond ((endp x) 0)
                (t (+ (car x) (sum-list (cdr x))))))

  The admission of SUM-LIST is trivial, using the relation
  O< (which is known to be well-founded on the domain
  recognized by O-P) and the measure (ACL2-COUNT X).
  We observe that the type of SUM-LIST is described by the
  theorem (ACL2-NUMBERP (SUM-LIST X)).  We used primitive type
  reasoning.

  Summary
  Form:  ( DEFUN SUM-LIST ...)
  Rules: ((:FAKE-RUNE-FOR-TYPE-SET NIL))
  Warnings:  None
  Time:  0.03 seconds
     (prove: 0.00, print: 0.00, proof tree: 0.00, other: 0.03)
   SUM-LIST
  ACL2 !>(sum-list '(1 2 3))

  ACL2 Warning [Guards] in TOP-LEVEL:  Guard-checking will be inhibited
  on recursive calls of the executable counterpart (i.e., in the ACL2
  logic) of SUM-LIST.  To check guards on all recursive calls:
    (set-guard-checking :all)
  To leave behavior unchanged except for inhibiting this message:
    (set-guard-checking :nowarn)

  6
  ACL2 !>(sum-list '(1 2 abc 3))

  ACL2 Error in TOP-LEVEL: The guard for the function symbol
  BINARY-+, which is (AND (ACL2-NUMBERP X) (ACL2-NUMBERP Y)),
  is violated by the arguments in the call (+ 'ABC 3).

  ACL2 !>:set-guard-checking nil
  ;;;; verbose output omitted here
  ACL2 >(sum-list '(1 2 abc 3))
  6
  ACL2 >(defthm sum-list-append
         (equal (sum-list (append a b))
                (+ (sum-list a) (sum-list b))))

  << Starting proof tree logging >>

  Name the formula above *1.

  Perhaps we can prove *1 by induction.  Three induction
  schemes are suggested by this conjecture.  Subsumption
  reduces that number to two.  However, one of these is flawed
  and so we are left with one viable candidate.

  ...

  That completes the proof of *1.

  Q.E.D.
  ~ev[]

  ~em[Guard verification vs. defun]

  ~bv[]

        Declare Form                        Guards Verified?

    (declare (xargs :mode :program ...))          no
    (declare (xargs :guard g))                    yes
    (declare (xargs :guard g :verify-guards nil)) no
    (declare (xargs ...<no :guard>...))           no

  ACL2 >:pe sum-list
   l        8  (DEFUN SUM-LIST (X)
                (DECLARE (XARGS :GUARD (INTEGER-LISTP X)
                                :VERIFY-GUARDS NIL))
                (COND ((ENDP X) 0)
                      (T (+ (CAR X) (SUM-LIST (CDR X))))))
  ACL2 >(verify-guards sum-list)
  The non-trivial part of the guard conjecture for SUM-LIST,
  given the :type-prescription rule SUM-LIST, is

  Goal
  (AND (IMPLIES (AND (INTEGER-LISTP X) (NOT (CONSP X)))
                (EQUAL X NIL))
       (IMPLIES (AND (INTEGER-LISTP X) (NOT (ENDP X)))
                (INTEGER-LISTP (CDR X)))
       (IMPLIES (AND (INTEGER-LISTP X) (NOT (ENDP X)))
                (ACL2-NUMBERP (CAR X)))).

  ...

  ACL2 >:pe sum-list
   lv       8  (DEFUN SUM-LIST (X)
                (DECLARE (XARGS :GUARD (INTEGER-LISTP X)
                                :VERIFY-GUARDS NIL))
  ACL2 >:set-guard-checking t
  
  Turning guard checking on, value T.
  
  ACL2 !>(sum-list '(1 2 abc 3))

  ACL2 Error in TOP-LEVEL: The guard for the function symbol
  SUM-LIST, which is (INTEGER-LISTP X), is violated by the
  arguments in the call (SUM-LIST '(1 2 ABC ...)).  See :DOC trace for a useful
  debugging utility.  See :DOC set-guard-checking for information about
  suppressing this check with (set-guard-checking :none), as recommended for
  new users.

  ACL2 !>:set-guard-checking nil
  ;;;; verbose output omitted here
  ACL2 >(sum-list '(1 2 abc 3))
  6
  ACL2 >:comp sum-list
  Compiling gazonk0.lsp.
  End of Pass 1.
  End of Pass 2.
  Finished compiling gazonk0.lsp.
  Loading gazonk0.o
  start address -T 1bbf0b4 Finished loading gazonk0.o
  Compiling gazonk0.lsp.
  End of Pass 1.
  End of Pass 2.
  Finished compiling gazonk0.lsp.
  Loading gazonk0.o
  start address -T 1bc4408 Finished loading gazonk0.o
   SUM-LIST
  ACL2 >:q

  Exiting the ACL2 read-eval-print loop.
  ACL2>(trace sum-list)
  (SUM-LIST)

  ACL2>(lp)

  ACL2 Version 1.8.  Level 1.  Cbd \"/slocal/src/acl2/v1-9/\".
  Type :help for help.
  ACL2 >(sum-list '(1 2 abc 3))
  6
  ACL2 >(sum-list '(1 2 3))
    1> (SUM-LIST (1 2 3))>
      2> (SUM-LIST (2 3))>
        3> (SUM-LIST (3))>
          4> (SUM-LIST NIL)>
          <4 (SUM-LIST 0)>
        <3 (SUM-LIST 3)>
      <2 (SUM-LIST 5)>
    <1 (SUM-LIST 6)>
  6
  ACL2 >:pe sum-list-append
            9  (DEFTHM SUM-LIST-APPEND
                       (EQUAL (SUM-LIST (APPEND A B))
                              (+ (SUM-LIST A) (SUM-LIST B))))
  ACL2 >(verify-guards sum-list-append)

  The non-trivial part of the guard conjecture for
  SUM-LIST-APPEND, given the :type-prescription rule SUM-LIST,
  is

  Goal
  (AND (TRUE-LISTP A)
       (INTEGER-LISTP (APPEND A B))
       (INTEGER-LISTP A)
       (INTEGER-LISTP B)).

  ...

  ****** FAILED ******* See :DOC failure ****** FAILED ******
  ACL2 >(defthm common-lisp-sum-list-append
           (if (and (integer-listp a)
                    (integer-listp b))
               (equal (sum-list (append a b))
                      (+ (sum-list a) (sum-list b)))
               t)
           :rule-classes nil)

  << Starting proof tree logging >>

  By the simple :rewrite rule SUM-LIST-APPEND we reduce the
  conjecture to

  Goal'
  (IMPLIES (AND (INTEGER-LISTP A)
                (INTEGER-LISTP B))
           (EQUAL (+ (SUM-LIST A) (SUM-LIST B))
                  (+ (SUM-LIST A) (SUM-LIST B)))).

  But we reduce the conjecture to T, by primitive type
  reasoning.

  Q.E.D.
  ;;;; summary omitted here
  ACL2 >(verify-guards common-lisp-sum-list-append)

  The non-trivial part of the guard conjecture for
  COMMON-LISP-SUM-LIST-APPEND, given the :type-prescription
  rule SUM-LIST, is

  Goal
  (AND (IMPLIES (AND (INTEGER-LISTP A)
                     (INTEGER-LISTP B))
                (TRUE-LISTP A))
       (IMPLIES (AND (INTEGER-LISTP A)
                     (INTEGER-LISTP B))
                (INTEGER-LISTP (APPEND A B)))).

  ...

  Q.E.D.

  That completes the proof of the guard theorem for
  COMMON-LISP-SUM-LIST-APPEND.  COMMON-LISP-SUM-LIST-APPEND
  is compliant with Common Lisp.
  ;;;; Summary omitted here.
  ACL2 >(defthm foo (consp (mv x y)))

  ...

  Q.E.D.

  ~ev[]
  ~bv[]
  ACL2 >(verify-guards foo)

  ACL2 Error in (VERIFY-GUARDS FOO): The number of values we
  need to return is 1 but the number of values returned by the
  call (MV X Y) is 2.

  > (CONSP (MV X Y))


  ACL2 Error in (VERIFY-GUARDS FOO): The guards for FOO cannot
  be verified because the theorem has the wrong syntactic
  form.  See :DOC verify-guards.
  ~ev[]~/

  :cited-by guard")

(deflabel mutual-recursion-proof-example
  :doc
  ":Doc-Section Tutorial5-Miscellaneous-Examples

  a small proof about mutually recursive functions~/

  Sometimes one wants to reason about mutually recursive functions.
  Although this is possible in ACL2, it can be a bit awkward.  This
  example is intended to give some ideas about how one can go about
  such proofs.

  For an introduction to mutual recursion in ACL2,
  ~pl[mutual-recursion].~/

  We begin by defining two mutually recursive functions:  one that
  collects the variables from a ~il[term], the other that collects the
  variables from a list of ~il[term]s.  We actually imagine the ~il[term]
  argument to be a ~ilc[pseudo-termp]; ~pl[pseudo-termp].
  ~bv[]
  (mutual-recursion

  (defun free-vars1 (term ans)
    (cond ((atom term)
           (add-to-set-eq term ans))
          ((fquotep term) ans)
          (t (free-vars1-lst (fargs term) ans))))

  (defun free-vars1-lst (lst ans)
    (cond ((atom lst) ans)
          (t (free-vars1-lst (cdr lst)
                             (free-vars1 (car lst) ans)))))

  )
  ~ev[]
  The idea of the following function is that it suggests a proof by
  induction in two cases, according to the top-level ~ilc[if] structure of
  the body.  In one case, ~c[(atom x)] is true, and the theorem to be
  proved should be proved under no additional hypotheses except for
  ~c[(atom x)].  In the other case, ~c[(not (atom x))] is assumed together
  with three instances of the theorem to be proved, one for each
  recursive call in this case.  So, one instance substitutes ~c[(car x)]
  for ~c[x]; one substitutes ~c[(cdr x)] for ~c[x]; and the third substitutes
  ~c[(cdr x)] for ~c[x] and ~c[(free-vars1 (car x) ans)] for ~c[ans].  If you think
  about how you would go about a hand proof of the theorem to follow,
  you'll come up with a similar scheme.
  ~bv[]
  (defun symbol-listp-free-vars1-induction (x ans)
    (if (atom x)
  ; then we just make sure x and ans aren't considered irrelevant
        (list x ans)
      (list (symbol-listp-free-vars1-induction (car x) ans)
            (symbol-listp-free-vars1-induction (cdr x) ans)
            (symbol-listp-free-vars1-induction
             (cdr x)
             (free-vars1 (car x) ans)))))
  ~ev[]
  We now prove the two theorems together as a conjunction, because the
  inductive hypotheses for one are sometimes needed in the proof of
  the other (even when you do this proof on paper!).
  ~bv[]
  (defthm symbol-listp-free-vars1
    (and (implies (and (pseudo-termp x)
                       (symbol-listp ans))
                  (symbol-listp (free-vars1 x ans)))
         (implies (and (pseudo-term-listp x)
                       (symbol-listp ans))
                  (symbol-listp (free-vars1-lst x ans))))
    :hints
    ((\"Goal\" :induct (symbol-listp-free-vars1-induction x ans))))
  ~ev[]
  The above works, but let's try for a more efficient proof, which
  avoids cluttering the proof with irrelevant (false) inductive
  hypotheses.
  ~bv[]
  (ubt 'symbol-listp-free-vars1-induction)

  (defun symbol-listp-free-vars1-induction (flg x ans)

  ; Flg is non-nil (or t) if we are ``thinking'' of a single term.

    (if (atom x)
        (list x ans)
      (if flg
          (symbol-listp-free-vars1-induction nil (cdr x) ans)
        (list (symbol-listp-free-vars1-induction t (car x) ans)
              (symbol-listp-free-vars1-induction
               nil
               (cdr x)
               (free-vars1 (car x) ans))))))
  ~ev[]
  We now state the theorem as a conditional, so that it can be proved
  nicely using the ~il[induction] scheme that we have just coded.  The
  prover will not store an ~ilc[if] ~il[term] as a ~il[rewrite] rule, but that's OK
  (as long as we tell it not to try), because we're going to derive
  the corollaries of interest later and make ~b[them] into ~il[rewrite]
  rules.
  ~bv[]
  (defthm symbol-listp-free-vars1-flg
    (if flg
        (implies (and (pseudo-termp x)
                      (symbol-listp ans))
                 (symbol-listp (free-vars1 x ans)))
      (implies (and (pseudo-term-listp x)
                    (symbol-listp ans))
               (symbol-listp (free-vars1-lst x ans))))
    :hints
    ((\"Goal\" :induct (symbol-listp-free-vars1-induction flg x ans)))
    :rule-classes nil)
  ~ev[]
  And finally, we may derive the theorems we are interested in as
  immediate corollaries.
  ~bv[]
  (defthm symbol-listp-free-vars1
    (implies (and (pseudo-termp x)
                  (symbol-listp ans))
             (symbol-listp (free-vars1 x ans)))
    :hints ((\"Goal\" :by (:instance symbol-listp-free-vars1-flg
                                   (flg t)))))

  (defthm symbol-listp-free-vars1-lst
    (implies (and (pseudo-term-listp x)
                  (symbol-listp ans))
             (symbol-listp (free-vars1-lst x ans)))
    :hints ((\"Goal\" :by (:instance symbol-listp-free-vars1-flg
                                   (flg nil)))))
    ~ev[]
  ")

(deflabel functional-instantiation-example
  :doc
  ":Doc-Section Tutorial5-Miscellaneous-Examples

  a small proof demonstrating functional instantiation~/

  The example below demonstrates the use of functional instantiation,
  that is, the use of a generic result in proving a result about
  specific functions.  In this example we constrain a function to be
  associative and commutative, with an identity or ``root,'' on a
  given domain.  Next, we define a corresponding function that applies
  the constrained associative-commutative function to successive
  elements of a list.  We then prove that the latter function gives
  the same value when we first reverse the elements of the list.
  Finally, we use functional instantiation to derive the corresponding
  result for the function that multiplies successive elements of a
  list.

  The details of the proof (such as the ~ilc[in-theory] event and
  particulars of the lemmas) are not the point here.  Rather, the
  point is to demonstrate the interaction of ~ilc[encapsulate]
  ~il[events] and ~c[:functional-instance] ~il[lemma-instance]s.  Of
  course, if you are interested in details then you may find it
  helpful to run these ~il[events] through ACL2.

  Also ~pl[constraint] for more about ~c[:functional-instance] and
  ~pl[lemma-instance] for general information about the use of
  previously-proved lemmas.~/

  ~bv[]
  (in-package \"ACL2\")

  (encapsulate
   (((ac-fn * *) => *)
    ((ac-fn-domain *) => *)
    ((ac-fn-root) => *))
   (local (defun ac-fn (x y) (+ x y)))
   (local (defun ac-fn-root () 0))
   (local (defun ac-fn-domain (x) (acl2-numberp x)))
   (defthm ac-fn-comm
     (equal (ac-fn x y)
            (ac-fn y x)))
   (defthm ac-fn-assoc
     (equal (ac-fn (ac-fn x y) z)
            (ac-fn x (ac-fn y z))))
   (defthm ac-fn-id
     (implies (ac-fn-domain x)
              (equal (ac-fn (ac-fn-root) x)
                     x)))
   (defthm ac-fn-closed
     (and (ac-fn-domain (ac-fn x y))
          (ac-fn-domain (ac-fn-root)))))

  ;;;;;;;;;;;;;;;;;;;;;;;
  ; End of encapsulate. ;
  ;;;;;;;;;;;;;;;;;;;;;;;

  ; Define a ``fold'' function that iteratively applies ac-fn over a list.
  (defun ac-fn-list (x)
    (if (atom x)
        (ac-fn-root)
      (ac-fn (car x)
             (ac-fn-list (cdr x)))))

  ; Recognize lists all of whose elements are in the intended domain.
  (defun ac-fn-domain-list (x)
    (if (atom x)
        t
      (and (ac-fn-domain (car x))
           (ac-fn-domain-list (cdr x)))))

  ; Define a list reverse function.
  (defun rev (x)
    (if (atom x)
        nil
      (append (rev (cdr x))
              (list (car x)))))

  ; The following is needed for proving ac-fn-list-append, which is
  ; needed for proving ac-fn-list-rev.
  (defthm ac-fn-list-closed
     (ac-fn-domain (ac-fn-list x)))

  ; Needed for proving ac-fn-list-rev:
  (defthm ac-fn-list-append
    (implies (and (ac-fn-domain-list x)
                  (ac-fn-domain-list y))
             (equal (ac-fn-list (append x y))
                    (ac-fn (ac-fn-list x)
                           (ac-fn-list y)))))

  ; Needed for proving ac-fn-list-rev:
  (defthm ac-fn-domain-list-rev
    (equal (ac-fn-domain-list (rev x))
           (ac-fn-domain-list x)))

  ; The following is a good idea because without it, the proof attempt
  ; for ac-fn-list-rev (see just below) fails with the term (HIDE
  ; (AC-FN-LIST NIL)).  It is often a good idea to disable
  ; executable-counterparts of functions that call constrained
  ; functions.
  (in-theory (disable (:executable-counterpart ac-fn-list)))

  (defthm ac-fn-list-rev
    (implies (ac-fn-domain-list x)
             (equal (ac-fn-list (rev x))
                    (ac-fn-list x))))

  ; Our goal now is to apply functional instantiation to ac-fn-list-rev
  ; in order to prove the corresponding theorem, times-list-rev, based
  ; on * instead of ac-fn.

  (defun times-list (x)
    (if (atom x)
        1
      (* (car x)
         (times-list (cdr x)))))

  (defun acl2-number-listp (x)
    (if (atom x)
        t
      (and (acl2-numberp (car x))
           (acl2-number-listp (cdr x)))))

  ; The following relies on the following built-in rules for * (whose
  ; statements correspond directly to their names): commutativity-of-*,
  ; associativity-of-*, and unicity-of-1.

  (defthm times-list-rev
    (implies (acl2-number-listp x)
             (equal (times-list (rev x))
                    (times-list x)))
    :hints ((\"Goal\"
             :use
             ((:functional-instance
               ac-fn-list-rev
               ;; Instantiate the generic functions:
               (ac-fn *)
               (ac-fn-root (lambda () 1))
               (ac-fn-domain acl2-numberp)
               ;; Instantiate the other relevant functions:
               (ac-fn-list times-list)
               (ac-fn-domain-list acl2-number-listp))))))
  ~ev[]~/")

(deflabel Startup
  :doc
  ":Doc-Section ACL2-Tutorial

  How to start using ACL2; the ACL2 ~il[command] loop~/~/

  When you start up ACL2, you'll probably find yourself inside the
  ACL2 ~il[command] loop, as indicated by the following ~il[prompt].
  ~bv[]

    ACL2 !>

  ~ev[]
  If not, you should type ~c[(LP)].  ~l[lp], which has a lot more
  information about the ACL2 ~il[command] loop.

  You should now be in ACL2.  The current ``~il[default-defun-mode]'' is
  ~c[:]~ilc[logic]; the other mode is ~c[:]~ilc[program], which would cause the letter ~c[p]
  to be printed in the ~il[prompt].  ~c[:]~ilc[Logic] means that any function we
  define is not only executable but also is axiomatically defined in
  the ACL2 logic.  ~l[defun-mode] and
  ~pl[default-defun-mode].  For example we can define a function
  ~c[my-cons] as follows.  (You may find it useful to start up ACL2 and
  submit this and other ~il[command]s below to the ACL2 ~il[command] loop, as we
  won't include output below.)
  ~bv[]

    ACL2 !>(defun my-cons (x y) (cons x y))

  ~ev[]
  An easy theorem may then be proved:  the ~ilc[car] of ~c[(my-cons a b)] is
  A.
  ~bv[]

    ACL2 !>(defthm car-my-cons (equal (car (my-cons a b)) a))

  ~ev[]

  You can place raw Lisp forms to evaluate at start-up into file
  ~c[acl2-init.lsp] in your home directory, except on Windows systems.  For
  example, if you put the following into ~c[acl2-init.lsp], then ACL2 will
  print \"HI\" when it starts up.
  ~bv[]
  (print \"HI\")
  ~ev[]
  But be careful; all bets are off when you submit forms to raw Lisp, so this
  capability should only be used when you are hacking or when you are setting
  some Lisp parameters (e.g., ~c[(setq si::*notify-gbc* nil)] to turn off
  garbage collection notices in GCL).

  Notice that unlike Nqthm, the theorem ~il[command] is ~ilc[defthm] rather than
  ~c[prove-lemma].  ~l[defthm], which explains (among other things)
  that the default is to turn theorems into ~il[rewrite] rules.

  Various keyword commands are available to query the ACL2 ``~il[world]'',
  or database.  For example, we may view the definition of ~c[my-cons] by
  invoking a command to print ~il[events], as follows.
  ~bv[]

    ACL2 !>:pe my-cons

  ~ev[]
  Also ~pl[pe].  We may also view all the lemmas that ~il[rewrite]
  ~il[term]s whose top function symbol is ~ilc[car] by using the following
  command, whose output will refer to the lemma ~c[car-my-cons] proved
  above.
  ~bv[]

    ACL2 !>:pl car

  ~ev[]
  Also ~pl[pl].  Finally, we may print all the ~il[command]s back
  through the initial ~il[world] as follows.
  ~bv[]

    ACL2 !>:pbt 0

  ~ev[]
  ~l[history] for a list of commands, including these, for
  viewing the current ACL2 ~il[world].

  Continue with the ~il[documentation] for ~il[annotated-acl2-scripts] to
  see a simple but illustrative example in the use of ACL2 for
  reasoning about functions.~/")

(deflabel Tidbits
  :doc
  ":Doc-Section ACL2-Tutorial

  some basic hints for using ACL2~/~/

  ~l[books] for a discussion of books.  Briefly, a book is a file
  whose name ends in ``.lisp'' that contains ACL2 ~il[events];
  ~pl[events].

  ~l[history] for a list of useful commands.  Some examples:
  ~bv[]

    :pbt :here      ; print the current event
    :pbt (:here -3) ; print the last four events
    :u              ; undo the last event
    :pe append      ; print the definition of append

  ~ev[]
  ~l[documentation] to learn how to print documentation to the
  terminal.  There are also versions of the ~il[documentation] for Mosaic,
  Emacs Info, and hardcopy.

  There are quite a few kinds of rules allowed in ACL2 besides
  ~c[:]~ilc[rewrite] rules, though we hope that beginners won't usually need
  to be aware of them.  ~l[rule-classes] for details.  In
  particular, there is support for ~il[congruence] rewriting.
  ~l[rune] (``RUle NamE'') for a description of the various kinds
  of rules in the system.  Also ~pl[theories] for a description of
  how to build ~il[theories] of ~il[rune]s, which are often used in hints;
  ~pl[hints].

  A ``~il[programming] mode'' is supported; ~pl[program],
  ~pl[defun-mode], and ~pl[default-defun-mode].  It can be
  useful to prototype functions after executing the command ~c[:]~ilc[program],
  which will cause definitions to be syntaxed-checked only.

  ACL2 supports mutual recursion, though this feature is not tied into
  the automatic discovery of ~il[induction] schemas and is often not the
  best way to proceed when you expect to be reasoning about the
  functions.  ~l[defuns]; also ~pl[mutual-recursion].

  ~l[ld] for discussion of how to load files of ~il[events].  There
  are many options to ~ilc[ld], including ones to suppress proofs and to
  control output.

  The ~c[:]~ilc[otf-flg] (Onward Thru the Fog FLaG) is a useful feature that
  Nqthm users have often wished for.  It prevents the prover from
  aborting a proof attempt and inducting on the original conjecture.
  ~l[otf-flg].

  ACL2 supports redefinition and redundancy in ~il[events];
  ~pl[ld-redefinition-action] and ~pl[redundant-events].

  A ~il[proof-tree] display feature is available for use with Emacs.  This
  feature provides a view of ACL2 proofs that can be much more useful
  than reading the stream of ~il[characters] output by the theorem prover
  as its ``proof.''  ~l[proof-tree].

  An interactive feature similar to Pc-Nqthm is supported in ACL2.
  ~l[verify] and ~pl[proof-checker].

  ACL2 allows you to ~il[monitor] the use of ~il[rewrite] rules.
  ~l[break-rewrite].

  ~l[arrays] to read about applicative, fast ~il[arrays] in ACL2.

  To quit the ACL2 ~il[command] loop, or (in akcl) to return to the ACL2
  ~il[command] loop after an interrupt, type ~c[:]~ilc[q].  To continue (resume)
  after an interrupt (in akcl), type ~c[:r].  To cause an interrupt (in
  akcl under Unix (trademark of AT&T)), hit control-C (twice, if
  inside Emacs).  To exit ACL2 altogether, first type ~c[:]~ilc[q] to exit
  the ACL2 ~il[command] loop, and then exit Lisp (by typing
  ~c[(user::bye)] in akcl).

  ~l[state] to read about the von Neumannesque ACL2 ~il[state] object that
  records the ``current state'' of the ACL2 session.
  Also ~pl[@], and ~pl[assign], to learn about reading and
  setting global ~il[state] variables.

  If you want your own von Neumannesque object, e.g., a structure that
  can be ``destructively modified'' but which must be used with some
  syntactic restrictions, ~pl[stobj].~/")

(deflabel Tips
  :doc
  ":Doc-Section ACL2-Tutorial

  some hints for using the ACL2 prover~/

  We present here some tips for using ACL2 effectively.  Though this
  collection is somewhat ~em[ad hoc], we try to provide some
  organization, albeit somewhat artificial:  for example, the sections
  overlap, and no particular order is intended.  This material has
  been adapted by Bill Young from a very similar list for Nqthm that
  appeared in the conclusion of:  ``Interaction with the Boyer-Moore
  Theorem Prover: A Tutorial Study Using the Arithmetic-Geometric Mean
  Theorem,'' by Matt Kaufmann and Paolo Pecchiari, CLI Technical
  Report 100, June, 1995.  We also draw from a similar list in Chapter
  13 of ``A Computational Logic Handbook'' by R.S. Boyer and J
  S. Moore (Academic Press, 1988).  We'll refer to this as ``ACLH''
  below.

  These tips are organized roughly as follows.

  ~bq[]
  A. ACL2 Basics

  B. Strategies for creating events

  C. Dealing with failed proofs 

  D. Performance tips 

  E. Miscellaneous tips and knowledge 

  F. Some things you DON'T need to know
  ~eq[]~/

  ~em[ACL2 BASICS]

  ~b[A1. The ACL2 logic.]~nl[]
  This is a logic of total functions.  For example, if ~c[A] and ~c[B]
  are less than or equal to each other, then we need to know something
  more in order to conclude that they are equal (e.g., that they are
  numbers).  This kind of twist is important in writing definitions;
  for example, if you expect a function to return a number, you may
  want to apply the function ~ilc[fix] or some variant (e.g., ~ilc[nfix] or
  ~ilc[ifix]) in case one of the formals is to be returned as the value.

  ACL2's notion of ordinals is important on occasion in supplying
  ``measure ~il[hints]'' for the acceptance of recursive definitions.  Be
  sure that your measure is really an ordinal.  Consider the following
  example, which ACL2 fails to admit (as explained below).
  ~bv[]

    (defun cnt (name a i x)
      (declare (xargs :measure (+ 1 i)))
      (cond ((zp (+ 1 i))
             0)
            ((equal x (aref1 name a i))
             (1+ (cnt name a (1- i) x)))
            (t (cnt name a (1- i) x))))

  ~ev[]
  One might think that ~c[(+ 1 i)] is a reasonable measure, since we
  know that ~c[(+ 1 i)] is a positive integer in any recursive call of
  ~c[cnt], and positive integers are ACL2 ordinals
  (~pl[o-p]).  However, the ACL2 logic requires that the
  measure be an ordinal unconditionally, not just under the governing
  assumptions that lead to recursive calls.  An appropriate fix is to
  apply ~ilc[nfix] to ~c[(+ 1 i)], i.e., to use
  ~bv[]

    (declare (xargs :measure (nfix (+ 1 i))))

  ~ev[]
  in order to guarantee that the measure will always be an ordinal (in
  fact, a positive integer).

  For more about admissibility of recursive definitions, ~pl[defun], in
  particular the discussion of termination.

  ~b[A2. Simplification.]~nl[]
  The ACL2 simplifier is basically a rewriter, with some ``~il[linear]
  arithmetic'' thrown in.  One needs to understand the notion of
  conditional rewriting.  ~l[rewrite].

  ~b[A3. Parsing of rewrite rules.]~nl[]

  ACL2 parses ~il[rewrite] rules roughly as explained in ACLH, ~em[except]
  that it never creates ``unusual'' rule classes.  In ACL2, if you
  want a ~c[:]~ilc[linear] rule, for example, you must specify ~c[:]~ilc[linear] in
  the ~c[:]~ilc[rule-classes].  ~l[rule-classes], and also
  ~pl[rewrite] and ~pl[linear].

  ~b[A4. Linear arithmetic.]~nl[]
  On this subject, it should suffice to know that the prover can
  handle truths about ~ilc[+] and ~ilc[-], and that ~il[linear] rules (see above)
  are somehow ``thrown in the pot'' when the prover is doing such
  reasoning.  Perhaps it's also useful to know that ~il[linear] rules can
  have hypotheses, and that conditional rewriting is used to relieve
  those hypotheses.

  ~b[A5. Events.]~nl[]
  Over time, the expert ACL2 user will know some subtleties of its
  ~il[events].  For example, ~ilc[in-theory] ~il[events] and ~il[hints] are
  important, and they distinguish between a function and its
  executable counterpart.

  ~em[B. STRATEGIES FOR CREATING EVENTS]

  In this section, we concentrate on the use of definitions and
  ~il[rewrite] rules.  There are quite a few kinds of rules allowed in ACL2
  besides ~il[rewrite] rules, though most beginning users probably won't
  usually need to be aware of them.  ~l[rule-classes] for
  details.  In particular, there is support for ~il[congruence] rewriting.
  Also ~pl[rune] (``RUle NamE'') for a description of the various
  kinds of rules in the system.

  ~b[B1. Use high-level strategy.]~nl[]
  Decompose theorems into ``manageable'' lemmas (admittedly,
  experience helps here) that yield the main result ``easily.''  It's
  important to be able to outline non-trivial proofs by hand (or in
  your head).  In particular, avoid submitting goals to the prover
  when there's no reason to believe that the goal will be proved and
  there's no ``sense'' of how an induction argument would apply.  It
  is often a good idea to avoid induction in complicated theorems
  unless you have a reason to believe that it is appropriate.

  ~b[B2. Write elegant definitions.]~nl[]
  Try to write definitions in a reasonably modular style, especially
  recursive ones.  Think of ACL2 as a ~il[programming] language whose
  procedures are definitions and lemmas, hence we are really
  suggesting that one follow good ~il[programming] style (in order to avoid
  duplication of ``code,'' for example).

  When possible, complex functions are best written as compositions of
  simpler functions.  The theorem prover generally performs better on
  primitive recursive functions than on more complicated recursions
  (such as those using accumulating parameters).

  Avoid large non-recursive definitions which tend to lead to large
  case explosions.  If such definitions are necessary, try to prove
  all relevant facts about the definitions and then ~il[disable] them.

  Whenever possible, avoid mutual recursion if you care to prove
  anything about your functions.  The induction heuristics provide
  essentially no help with reasoning about mutually defined functions.
  Mutually recursive functions can usually be combined into a single
  function with a ``flag'' argument.  (However,
  ~pl[mutual-recursion-proof-example] for a small example of proof
  involving mutually recursive functions.)

  ~b[B3. Look for analogies.]~nl[]
  Sometimes you can easily edit sequences of lemmas into sequences of
  lemmas about analogous functions.

  ~b[B4. Write useful rewrite rules.]~nl[]
  As explained in A3 above, every ~il[rewrite] rule is a directive to the
  theorem prover, usually to replace one ~il[term] by another.  The
  directive generated is determined by the syntax of the ~ilc[defthm]
  submitted.  Never submit a ~il[rewrite] rule unless you have considered
  its interpretation as a proof directive.

  ~b[B4a.  Rewrite rules should simplify.]~nl[]
  Try to write ~il[rewrite] rules whose right-hand sides are in some sense
  ``simpler than'' (or at worst, are variants of) the left-hand sides.
  This will help to avoid infinite loops in the rewriter.

  ~b[B4b.  Avoid needlessly expensive rules.]~nl[]
  Consider a rule whose conclusion's left-hand side (or, the entire
  conclusion) is a ~il[term] such as ~c[(consp x)] that matches many ~il[term]s
  encountered by the prover.  If in addition the rule has complicated
  hypotheses, this rule could slow down the prover greatly.  Consider
  switching the conclusion and a complicated hypothesis (negating
  each) in that case.

  ~b[B4c. The ``Knuth-Bendix problem''.]~nl[]
  Be aware that left sides of ~il[rewrite] rules should match the
  ``normalized forms'', where ``normalization'' (rewriting) is inside
  out.  Be sure to avoid the use of nonrecursive function symbols on
  left sides of ~il[rewrite] rules, except when those function symbols are
  ~il[disable]d, because they tend to be expanded away before the rewriter
  would encounter an instance of the left side of the rule.  Also
  assure that subexpressions on the left hand side of a rule are in
  simplified form.

  ~b[B4d. Avoid proving useless rules.]~nl[]
  Sometimes it's tempting to prove a ~il[rewrite] rule even before you see
  how it might find application.  If the rule seems clean and
  important, and not unduly expensive, that's probably fine,
  especially if it's not too hard to prove.  But unless it's either
  part of the high-level strategy or, on the other hand, intended to
  get the prover past a particular unproved goal, it may simply waste
  your time to prove the rule, and then clutter the database of rules
  if you are successful.

  ~b[B4e. State rules as strongly as possible, usually.]~nl[]
  It's usually a good idea to state a rule in the strongest way
  possible, both by eliminating unnecessary hypotheses and by
  generalizing subexpressions to variables.

  Advanced users may choose to violate this policy on occasion, for
  example in order to avoid slowing down the prover by excessive
  attempted application of the rule.  However, it's a good rule of
  thumb to make the strongest rule possible, not only because it will
  then apply more often, but also because the rule will often be
  easier to prove (see also B6 below).  New users are sometimes
  tempted to put in extra hypotheses that have a ``type restriction''
  appearance, without realizing that the way ACL2 handles (total)
  functions generally lets it handle trivial cases easily.

  ~b[B4f. Avoid circularity.]~nl[]
  A stack overflow in a proof attempt almost always results from
  circular rewriting.  Use ~ilc[brr] to investigate the stack;
  ~pl[break-lemma].  Because of the complex heuristics, it is not
  always easy to define just when a ~il[rewrite] will cause circularity.
  See the very good discussion of this topic in ACLH.

  ~l[break-lemma] for a trick involving use of the forms ~c[brr t]
  and ~c[(cw-gstack)] for inspecting loops in the rewriter.

  ~b[B4g. Remember restrictions on permutative rules.]~nl[]
  Any rule that permutes the variables in its left hand side could
  cause circularity.  For example, the following axiom is
  automatically supplied by the system:
  ~bv[]

    (defaxiom commutativity-of-+
              (equal (+ x y) (+ y x))).

  ~ev[] 
  This would obviously lead to dangerous circular rewriting if such
  ``permutative'' rules were not governed by a further restriction.
  The restriction is that such rules will not produce a ~il[term] that
  is ``lexicographically larger than'' the original ~il[term]
  (~pl[loop-stopper]).  However, this sometimes prevents intended
  rewrites.  See Chapter 13 of ACLH for a discussion of this problem.

  ~b[B5. Conditional vs. unconditional rewrite rules.]~nl[]
  It's generally preferable to form unconditional ~il[rewrite] rules unless
  there is a danger of case explosion.  That is, rather than pairs of
  rules such as
  ~bv[]

  (implies p
           (equal term1 term2))
  ~ev[]
  and
  ~bv[]

  (implies (not p)
           (equal term1 term3))

  ~ev[]
  consider:
  ~bv[]

  (equal term1
         (if p term2 term3))

  ~ev[]
  However, sometimes this strategy can lead to case explosions: ~ilc[IF]
  ~il[term]s introduce cases in ACL2.  Use your judgment.  (On the subject
  of ~ilc[IF]: ~ilc[COND], ~ilc[CASE], ~ilc[AND], and ~ilc[OR] are macros that
  abbreviate ~ilc[IF] forms, and propositional functions such as
  ~ilc[IMPLIES] quickly expand into ~ilc[IF] ~il[term]s.)

  ~b[B6. Create elegant theorems.]~nl[]
  Try to formulate lemmas that are as simple and general as possible.
  For example, sometimes properties about several functions can be
  ``factored'' into lemmas about one function at a time.  Sometimes
  the elimination of unnecessary hypotheses makes the theorem easier
  to prove, as does generalizing first by hand.

  ~b[B7. Use] ~ilc[defaxiom]s ~b[temporarily to explore possibilities.]~nl[]
  When there is a difficult goal that seems to follow immediately (by
  a ~c[:use] hint or by rewriting) from some other lemmas, you can
  create those lemmas as ~ilc[defaxiom] ~il[events] (or, the application of
  ~ilc[skip-proofs] to ~ilc[defthm] ~il[events]) and then double-check that the
  difficult goal really does follow from them.  Then you can go back
  and try to turn each ~ilc[defaxiom] into a ~ilc[defthm].  When you do
  that, it's often useful to ~il[disable] any additional ~il[rewrite] rules that
  you prove in the process, so that the ``difficult goal'' will still
  be proved from its lemmas when the process is complete.

  Better yet, rather than disabling ~il[rewrite] rules, use the ~ilc[local]
  mechanism offered by ~ilc[encapsulate] to make temporary rules
  completely ~ilc[local] to the problem at hand.  ~l[encapsulate] and
  ~pl[local].

  ~b[B9. Use books.]~nl[]
  Consider using previously certified ~il[books], especially for arithmetic
  reasoning.  This cuts down the duplication of effort and starts your
  specification and proof effort from a richer foundation.  See the
  file ~c[\"doc/README\"] in the ACL2 distribution for information on ~il[books]
  that come with the system.

  ~em[C. DEALING WITH FAILED PROOFS]

  ~b[C1. Look in proof output for goals that can't be further simplified.]~nl[]
  Use the ``~il[proof-tree]'' utility to explore the proof space.
  However, you don't need to use that tool to use the ``checkpoint''
  strategy.  The idea is to think of ACL2 as a ``simplifier'' that
  either proves the theorem or generates some goal to consider.  That
  goal is the first ``checkpoint,'' i.e., the first goal that does not
  further simplify.  Exception:  it's also important to look at the
  induction scheme in a proof by induction, and if induction seems
  appropriate, then look at the first checkpoint ~em[after] the
  induction has begun.

  Consider whether the goal on which you focus is even a theorem.
  Sometimes you can execute it for particular values to find a
  counterexample.

  When looking at checkpoints, remember that you are looking for any
  reason at all to believe the goal is a theorem.  So for example,
  sometimes there may be a contradiction in the hypotheses.

  Don't be afraid to skip the first checkpoint if it doesn't seem very
  helpful.  Also, be willing to look a few lines up or down from the
  checkpoint if you are stuck, bearing in mind however that this
  practice can be more distracting than helpful.

  ~b[C2. Use the ``break rewrite'' facility.]~nl[]
  ~ilc[Brr] and related utilities let you inspect the ``rewrite stack.''
  These can be valuable tools in large proof efforts.
  ~l[break-lemma] for an introduction to these tools, and
  ~pl[break-rewrite] for more complete information.

  The break facility is especially helpful in showing you why a
  particular rewrite rule is not being applied.

  ~b[C3. Use induction hints when necessary.]
  Of course, if you can define your functions so that they suggest the
  correct inductions to ACL2, so much the better!  But for complicated
  inductions, induction ~il[hints] are crucial.  ~l[hints] for a
  description of ~c[:induct] ~il[hints].

  ~b[C4. Use the ``Proof Checker'' to explore.]~nl[]
  The ~ilc[verify] command supplied by ACL2 allows one to explore problem
  areas ``by hand.''  However, even if you succeed in proving a
  conjecture with ~ilc[verify], it is useful to prove it without using
  it, an activity that will often require the discovery of ~il[rewrite]
  rules that will be useful in later proofs as well.

  ~b[C5. Don't have too much patience.]~nl[]
  Interrupt the prover fairly quickly when simplification isn't
  succeeding.

  ~b[C6. Simplify rewrite rules.]~nl[]
  When it looks difficult to relieve the hypotheses of an existing
  ~il[rewrite] rule that ``should'' apply in a given setting, ask yourself
  if you can eliminate a hypothesis from the existing ~il[rewrite] rule.
  If so, it may be easier to prove the new version from the old
  version (and some additional lemmas), rather than to start from
  scratch.

  ~b[C7. Deal with base cases first.]~nl[]
  Try getting past the base case(s) first in a difficult proof by
  induction.  Usually they're easier than the inductive step(s), and
  rules developed in proving them can be useful in the inductive
  step(s) too.  Moreover, it's pretty common that mistakes in the
  statement of a theorem show up in the base case(s) of its proof by
  induction.

  ~b[C8. Use] ~c[:expand] ~b[hints.]
  Consider giving ~c[:expand] ~il[hints].  These are especially useful when a
  proof by induction is failing.  It's almost always helpful to open
  up a recursively defined function that is supplying the induction
  scheme, but sometimes ACL2 is too timid to do so; or perhaps the
  function in question is ~il[disable]d.

  ~em[D. PERFORMANCE TIPS]

  ~b[D1. Disable rules.]~nl[]
  There are a number of instances when it is crucial to ~il[disable] rules,
  including (often) those named explicitly in ~c[:use] ~il[hints].  Also,
  ~il[disable] recursively defined functions for which you can prove what
  seem to be all the relevant properties.  The prover can spend
  significant time ``behind the scenes'' trying to open up recursively
  defined functions, where the only visible effect is slowness.

  ~b[D2. Turn off the ``break rewrite'' facility.]
  Remember to execute ~c[:brr nil] after you've finished with the
  ``break rewrite'' utility (~pl[break-rewrite]), in order to
  bring the prover back up to full speed.

  ~em[E. MISCELLANEOUS TIPS AND KNOWLEDGE]

  ~b[E1. Order of application of rewrite rules.]~nl[]
  Keep in mind that the most recent ~il[rewrite] rules in the ~il[history]
  are tried first.

  ~b[E2. Relieving hypotheses is not full-blown theorem proving.]~nl[]
  Relieving hypotheses on ~il[rewrite] rules is done by rewriting and ~il[linear]
  arithmetic alone, not by case splitting or by other prover processes
  ``below'' simplification.

  ~b[E3. ``Free variables'' in rewrite rules.]~nl[] The set of ``free
  variables'' of a ~il[rewrite] rule is defined to contain those
  variables occurring in the rule that do not occur in the left-hand
  side of the rule.  It's often a good idea to avoid rules containing
  free variables because they are ``weak,'' in the sense that
  hypotheses containing such variables can generally only be proved
  when they are ``obviously'' present in the current context.  This
  weakness suggests that it's important to put the most
  ``interesting'' (specific) hypotheses about free variables first, so
  that the right instances are considered.  For example, suppose you
  put a very general hypothesis such as ~c[(consp x)] first.  If the
  context has several ~il[term]s around that are known to be
  ~ilc[consp]s, then ~c[x] may be bound to the wrong one of them.  For much
  more information on free variables, ~pl[free-variables].

  ~b[E4. Obtaining information]
  Use ~c[:]~ilc[pl] ~c[foo] to inspect ~il[rewrite] rules whose left hand sides are
  applications of the function ~c[foo].  Another approach to seeing
  which ~il[rewrite] rules apply is to enter the ~il[proof-checker] with
  ~ilc[verify], and use the ~c[show-rewrites] or ~c[sr] command.

  ~b[E5. Consider esoteric rules with care.]~nl[]
  If you care to ~pl[rule-classes] and peruse the list of
  subtopics (which will be listed right there in most versions of this
  ~il[documentation]), you'll see that ACL2 supports a wide variety of
  rules in addition to ~c[:]~il[rewrite] rules.  Should you use them?
  This is a complex question that we are not ready to answer with any
  generality.  Our general advice is to avoid relying on such rules as
  long as you doubt their utility.  More specifically:  be careful not
  to use conditional type prescription rules, as these have been known
  to bring ACL2 to its knees, unless you are conscious that you are
  doing so and have reason to believe that they are working well.

  ~em[F. SOME THINGS YOU DON'T NEED TO KNOW]

  Most generally:  you shouldn't usually need to be able to predict
  too much about ACL2's behavior.  You should mainly just need to be
  able to react to it.

  ~b[F1. Induction heuristics.]~nl[]
  Although it is often important to read the part of the prover's
  output that gives the induction scheme chosen by the prover, it is
  not necessary to understand how the prover made that choice.
  (Granted, advanced users may occasionally gain minor insight from
  such knowledge.  But it's truly minor in many cases.)  What ~em[is]
  important is to be able to tell it an appropriate induction when it
  doesn't pick the right one (after noticing that it doesn't).  See C3
  above.

  ~b[F2. Heuristics for expanding calls of recursively defined functions.]~nl[]
  As with the previous topic, the important thing isn't to understand
  these heuristics but, rather, to deal with cases where they don't
  seem to be working.  That amounts to supplying ~c[:expand] ~il[hints] for
  those calls that you want opened up, which aren't.  See also C8
  above.

  ~b[F3. The ``waterfall''.]~nl[]
  As discussed many times already, a good strategy for using ACL2 is
  to look for checkpoints (goals stable under simplification) when a
  proof fails, perhaps using the ~il[proof-tree] facility.  Thus, it
  is reasonable to ignore almost all the prover output, and to avoid
  pondering the meaning of the other ``processes'' that ACL2 uses
  besides simplification (such as elimination, cross-fertilization,
  generalization, and elimination of irrelevance).  For example, you
  don't need to worry about prover output that mentions ``type
  reasoning'' or ``abbreviations,'' for example.")

(deflabel introduction-to-the-theorem-prover
  :doc
  ":Doc-Section acl2-tutorial

   how the theorem prover works -- level 0~/

   Software is complex, and ACL2 is a piece of software that is used to analyze
   software -- adding another layer of complexity.
   Furthermore, instead of being limited to static analysis for
   certain fixed properties, ACL2 allows you -- indeed, forces you -- to
   formalize the problem and the questions.  It ``knows'' nothing inherent
   about your problem before you start to interact with it.  But it can be used
   to help answer the most complicated questions you can ask about software.

   All this is to say that it is not the kind of tool that you just install and
   then start to use effectively.  So OK, you've installed it or confirmed that
   you can invoke it.  Good for you.  Now you have to learn how to use it!
   Your success ultimately comes down to your understanding of your problem
   domain and your appropriate exploitation of ACL2's strengths and avoidance
   of its weaknesses.  So put aside the idea of sitting down and interacting
   with it.  Instead, learn about it.

   We assume you know some of the ~il[interesting-applications industrial applications]
   of ACL2.  Realizing that such things can be done may sustain you during the
   long learning curve!  We also assume you have taken both the
   ~il[|A Flying Tour of ACL2| Flying Tour] and the ~il[|A Walking Tour of ACL2| Walking Tour].
   The tours give you a good overview of the whole system where this tutorial
   focuses on how to use the prover itself.

   If you haven't visited these links, please do so now.  

   This tutorial will take you several hours -- maybe several days -- to work
   through.  Do not breeze through it as you might a blog.  ~i[Think] your way
   through it.  ~i[Remember] what you read.  Do not take short cuts.  If you
   start to use ACL2 before you really know how, it will only frustrate you.

   We recommend that you read this tutorial with an HTML browser so that you
   can see which links you've followed and which you have not.  To give you a
   sense of what is in store, here is a map of this document.  But don't
   navigate through it from here! Read it linearly, following the links when
   the text directs you to.

   ~bv[]
    ~il[INTRODUCTION-TO-THE-THEOREM-PROVER]
        ~il[INTRODUCTION-TO-REWRITE-RULES-PART-1]
            ~il[SPECIAL-CASES-FOR-REWRITE-RULES]
            ~il[EQUIVALENT-FORMULAS-DIFFERENT-REWRITE-RULES]
        ~il[INTRODUCTION-TO-KEY-CHECKPOINTS]
            ~il[DEALING-WITH-KEY-COMBINATIONS-OF-FUNCTION-SYMBOLS]
            ~il[GENERALIZING-KEY-CHECKPOINTS]
            ~il[POST-INDUCTION-KEY-CHECKPOINTS]
        ~il[INTRODUCTION-TO-REWRITE-RULES-PART-2]
            ~il[STRONG-REWRITE-RULES]
                ~il[PRACTICE-FORMULATING-STRONG-RULES]
                    ~il[PRACTICE-FORMULATING-STRONG-RULES-1]
                    ~il[PRACTICE-FORMULATING-STRONG-RULES-2]
                    ~il[PRACTICE-FORMULATING-STRONG-RULES-3]
                    ~il[PRACTICE-FORMULATING-STRONG-RULES-4]
                    ~il[PRACTICE-FORMULATING-STRONG-RULES-5]
                    ~il[PRACTICE-FORMULATING-STRONG-RULES-6]
            ~il[SPECIFIC-KINDS-OF-FORMULAS-AS-REWRITE-RULES]
            ~il[FURTHER-INFORMATION-ON-REWRITING]
        ~il[INTRODUCTION-TO-THE-DATABASE]
        ~il[INTRODUCTION-TO-HINTS]
        ~IL[INTRODUCTION-TO-A-FEW-SYSTEM-CONSIDERATIONS]
        ~il[INTRODUCTORY-CHALLENGES]
            ~il[INTRODUCTORY-CHALLENGE-PROBLEM-1]
            ~il[INTRODUCTORY-CHALLENGE-PROBLEM-2]
            ~il[INTRODUCTORY-CHALLENGE-PROBLEM-3]
            ~i[(there are others but at least do a few)]
        ~il[FREQUENTLY-ASKED-QUESTIONS-BY-NEWCOMERS]
   ~ev[]

   If any of the links above are marked as ``visited'' by your browser, use
   your browser's tools menu to mark all links as unvisited.  As you can see,
   we really think you'll get the most out of this document if you take it
   seriously.  As you read, you will see some links to ``advanced'' topics.
   These are marked with a tiny warning sign, ``~warn[]''.  They lead out of
   this linear tutorial and into ACL2's hypertext reference manual.  We
   recommend that you ~i[not] visit any of these advanced links until you have
   read the entire tutorial at least once.

   After you finish this tutorial material, we recommend that you look at the
   ACL2 Demos, at the ``Demos'' link of the ACL2 home page,
   ~url[http://www.cs.utexas.edu/users/moore/acl2].

   Most users of ACL2 have bought the book 

   ~i[Computer-Aided Reasoning: An Approach], Kaufmann, Manolios, and Moore,
   Kluwer Academic Publishers, June, 2000

   which is available in paperback from Lulu for approximately $20 (as of
   2010).  See ~url[http://www.lulu.com/content/1746161].  That book contains
   hundreds of exercises in programming, proof, and using The Method described
   here to prove theorems.  Solutions to the exercises are online.  For more
   information about the book and a companion one (also available on Lulu)
   about industrial applications of ACL2, see

   ~url[http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html#Books]

   Using ACL2 is akin to having a partner in the theorem proving enterprise.
   It will do some of the work and you will do some of the work.  It can't
   really be any other way because theorem proving is undecidable.  You bring a
   quirkly, error-prone, creative insight to the problem, and ACL2 brings
   accuracy, logic, and perserverance.

   Here we describe a ``model'' of how the system works and introduce some
   of the ideas and terminology you'll use repeatedly when interacting with it.

   This article is about the ~i[theorem prover] itself, not the programming
   language and not the logic.  We assume you know enough about the ACL2
   programming language that you can define simple functions, run them, and
   read and write ACL2 constants and terms.  For some examples of what we'll
   take for granted about ACL2 programming,
   ~pl[programming-knowledge-taken-for-granted].

   We also assume you know enough about logic to understand, for
   example, the words we use to talk about formulas and proofs.  To see
   some examples of what we'll take for granted about your knowledge of
   logic terminology, ~pl[logic-knowledge-taken-for-granted].

   When you give the theorem prover a goal formula to prove, it tries to prove
   it by breaking it down into subgoals, each of which must be proved in order
   to prove the original goal.  This breaking apart of the goal is done by
   various ~i[proof techniques] built into ACL2.  Different proof techniques
   break the formula apart in different ways.  For example, the ~i[simplifier] rips
   apart the propositional structure to isolate the various cases and applies
   rewrite rules to simplify the subterms of the formula, while the ~i[induction]
   ~i[engine] will attempt to break the goal into some base cases and some
   induction steps.

   The theorem prover's behavior is affected by a ~i[database] of ~i[rules]
   derived from axioms, definitions, and previously proved theorems.  The
   database also records the ~i[enabled status] of each rule; only enabled
   rules are seen by the prover and you can set the status of a rule.  There
   are many other user-settable switches and parameters affecting the behavior
   of the prover; you'll learn about some of them later.

   You guide the theorem prover most of the time simply by identifying lemmas
   for it to prove.  (A ~i[lemma] is just a theorem that you think is useful in
   the proofs of other theorems.)

   Why does this guide the theorem prover?  Because every time you get the
   system to prove a theorem, it turns the theorem into a rule (unless you tell
   it not to) and stores the rule in the database.  That changes how the prover
   behaves subsequently.  But ~i[you] determine the kind of rule ACL2 stores.

   To learn to ``drive'' the theorem prover you have to learn how various rules
   affect the system's behavior and how it turns proved formulas into rules.
   But before we discuss this, we discuss a more mathematical activity: how do
   you figure out the lemmas ACL2 will need in order for it to prove
   interesting theorems?  ACL2 can often help you in this activity, if you use
   it in the right way.

   Here is the way we recommend you use ACL2.

   ~b[The Method].

   (1) you present ACL2 with the goal conjecture to prove

   (2) typically, it fails to prove it (or you abort its attempt), but it
   prints some ~i[Key Checkpoints]

   (3) you look at the Key Checkpoints and decide that you know a fact that
   will help; this tutorial will present some helpful questions to keep in mind

   (4) you formalize your knowledge as a formula, along with directions for how
   ACL2 should turn the formula into a rule; this tutorial will tell you about the most
   commonly used rule, the ~i[rewrite] rule

   (5) you recursively apply The Method to get ACL2 to prove your formula and
   to store it as the kind of rule you specified

   (6) go to step (1)

   Caveat: This approach simply won't work on some theorems!  Basically, this
   is a ``troubleshooting'' approach, where you're letting ACL2 determine the
   basic strategy and you're just helping with the subgoals.  But for some
   theorems, ACL2's approach will be misguided and no amount of troubleshooting
   will salvage its strategy.  You'll have a sense that this is happening when
   it happens because the formulas ACL2 presents to you will raise issues that
   feel irrelevant to you.  The basic truth is that if you think a formula is
   always true there are usually strong intuitive reasons behind your belief.
   If you were asked to defend your belief, you'd start to explain your reasons
   and with training you can turn that into a proof.  So when ACL2's formulas
   present you with things you haven't thought of either (a) you'll have an
   ``Ah ha!''  moment when you realize you hadn't considered that case or (b)
   you'll realize that ACL2's approach is different from your intuitive
   ``proof.''

   But, surprisingly often, the troubleshooting approach to finding proofs
   works quite well, especially as you rein in your expectations and develop a
   sense of what ACL2 can handle on its own.  Of course, if you can decompose
   the proof into a couple of main lemmas before you start, so much the better:
   write down your sequence of lemmas, thinking about the rules you want them
   to generate, and get ACL2 to prove each of them before giving it the main
   theorem.  This ~i[proof planning] approach will gradually become an integral
   part of your use of The Method.

   The only mechanized help we can offer with The Method, aside from the
   theorem prover itself, are tools to help you manage the stack of subgoals it
   generates when, in step (5) you recursively apply The Method to a lemma.
   There are both Emacs and Eclipse tools available.

   To use The Method you have to read the Key Checkpoints printed at the very
   end of ~i[failed] proof attempts, just after the line that reads:
   ~bv[]
   The key checkpoint goals, below, may help you to debug this failure.
   ~ev[]
   Most users do not read the output from successful proofs and do not read the
   output ~i[during] a proof -- they just let it stream by as a sort of gestalt
   meter on the theorem prover's progress or lack thereof.  For example, you'll
   be able to tell it is in a loop and needs to be interrupted.

   You will respond to most Key Checkpoints by formulating new lemmas for the
   system to prove and store as rules designed by you to alter ACL2's behavior
   so that it proves the Key Checkpoints.  You will give each lemma a ~i[name] and
   write some ~i[formula] to express the mathematical idea.  You'll command
   ACL2 to prove it by typing:
   ~bv[]
   (defthm ~i[name]
           ~i[formula]
           ...)
   ~ev[]
   In the ``...'' you may provide two other kinds of information:
   ~i[hints] for how to prove ~i[formula] and directives, called
   ~i[rule-classes], for how to convert ~i[formula] into a rule after it has
   proved ~i[formula].  Note that ~i[you] are in charge of determining
   what kind of rule ACL2 generates!  There are over a dozen different
   types of rules with many opportunities to specialize each type.
   But the most common kind of rule you'll want to generate is a ~i[rewrite]
   rule.

   We recommend that you read the following topics in the following
   order, without skipping anything but links into the reference
   manual, which are marked by the little warning sign, ``~warn[]''.   

   (1) ~l[introduction-to-rewrite-rules-part-1] to read about the use and design of
   rewrite rules.

   (2) ~l[introduction-to-key-checkpoints] to see how to use The Method to help you
   design rules.

   (3) ~l[introduction-to-rewrite-rules-part-2] for general guidance on how to
   turn formulas into effective rules.

   (4) ~l[introduction-to-the-database] to see how to issue commands that
   build different kinds of rules and that affect the enabled status of
   existing rules.

   (5) ~l[introduction-to-hints] to see how to give the prover hints for how to
   prove specific theorems or even subgoals of specific proof attempts.

   (6) ~l[introduction-to-a-few-system-considerations] for a few words about
   system aspects of interacting with ACL2.

   (7) ~l[introductory-challenges] for a graduated sequence of good challenge
   problems for the new user to tackle.  ~b[Do not skip this section!]
   It is here that you ~i[really] learn how to use ACL2 -- by using it.

   (8) ~l[frequently-asked-questions-by-newcomers] for a list of questions
   that new users frequently ask, answered mainly by providing links into
   the reference manual.  We recommend that you skim through these questions
   and remember that you can find the answers here later.  We are very
   interested in receiving suggestions for how to improve this FAQ
   and this tutorial.  See the ACL2 home page, specifically the link
   ``Mailing Lists''.

   Please read all of the material cited above (skipping only the
   reference-manual links (``~warn[]'')) before you try to use ACL2 on
   problems of your own.

   By this point you should have read, at least, the following topics from
   this tutorial introduction to the theorem prover:

   ~bv[]
    ~il[INTRODUCTION-TO-THE-THEOREM-PROVER]
        ~il[INTRODUCTION-TO-REWRITE-RULES-PART-1]
            ~il[SPECIAL-CASES-FOR-REWRITE-RULES]
            ~il[EQUIVALENT-FORMULAS-DIFFERENT-REWRITE-RULES]
        ~il[INTRODUCTION-TO-KEY-CHECKPOINTS]
            ~il[DEALING-WITH-KEY-COMBINATIONS-OF-FUNCTION-SYMBOLS]
            ~il[GENERALIZING-KEY-CHECKPOINTS]
            ~il[POST-INDUCTION-KEY-CHECKPOINTS]
        ~il[INTRODUCTION-TO-REWRITE-RULES-PART-2]
            ~il[STRONG-REWRITE-RULES]
                ~il[PRACTICE-FORMULATING-STRONG-RULES]
                    ~il[PRACTICE-FORMULATING-STRONG-RULES-1]
                    ~il[PRACTICE-FORMULATING-STRONG-RULES-2]
                    ~il[PRACTICE-FORMULATING-STRONG-RULES-3]
                    ~il[PRACTICE-FORMULATING-STRONG-RULES-4]
                    ~il[PRACTICE-FORMULATING-STRONG-RULES-5]
                    ~il[PRACTICE-FORMULATING-STRONG-RULES-6]
            ~il[SPECIFIC-KINDS-OF-FORMULAS-AS-REWRITE-RULES]
            ~il[FURTHER-INFORMATION-ON-REWRITING]
        ~il[INTRODUCTION-TO-THE-DATABASE]
        ~il[INTRODUCTION-TO-HINTS]
        ~IL[INTRODUCTION-TO-A-FEW-SYSTEM-CONSIDERATIONS]
        ~il[INTRODUCTORY-CHALLENGES]
            ~il[INTRODUCTORY-CHALLENGE-PROBLEM-1]
            ~il[INTRODUCTORY-CHALLENGE-PROBLEM-2]
            ~il[INTRODUCTORY-CHALLENGE-PROBLEM-3]
            ~i[(there are others but at least do a few)]
        ~il[FREQUENTLY-ASKED-QUESTIONS-BY-NEWCOMERS]
   ~ev[]

   We also recommend that you look at the ACL2 Demos, at the ``demos'' link of 
   the ACL2 home page ~url[http://www.cs.utexas.edu/users/moore/acl2].

   Most users of ACL2 have bought the book 

   ~i[Computer-Aided Reasoning: An Approach], Kaufmann, Manolios, and Moore,
   Kluwer Academic Publishers, June, 2000

   which is available in paperback from Lulu for approximately $20 (as of 2010).
   See ~url[http://www.lulu.com/content/1746161].  That book contains hundreds
   of exercises in programming, proof, and using The Method to prove theorems.
   Solutions to the exercises are online.  For more information about the
   book and a companion one (also available on Lulu) about industrial applications
   of ACL2, see

   ~url[http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html#Books]

   Thank you for spending the time to get acquainted with the basics of the
   ACL2 theorem prover.  Don't hesitate to send further questions to the
   ACL2 Help address on the ``Mailing Lists'' link of the ACL2 home page.

   ~b[End of Tutorial Introduction to the Theorem Prover]

   Below is a list of all of the topics cited on this page.

   ~/~/")

(deflabel dealing-with-key-combinations-of-function-symbols
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   how to get rid of key combinations of function symbols~/

   Suppose ~c[REV] reverses a list, ~c[MEMBER] checks that its first argument
   is an element of its second, and ~c[SQUARES-PLUS-3P] is some complicated
   predicate.  Suppose you're proving some Main Theorem that involves those
   concepts and the theorem prover presents you with the following hideous
   formula as a key checkpoint.  What action should you take?

   Hint: Don't read the formula ``for sense,'' i.e., don't try to understand
   what this formula is saying!  Just look at every subterm involving a nest of
   two function symbols and ask if you know something about those two symbols
   that allows you to ~i[simplify] that one subterm.

  ~bv[]
   (IMPLIES (AND (CONSP X)
                 (MEMBER (+ 3 (* I I)) (REV X))
                 (LIST-OF-INTEGERS X)
                 (INTEGERP I)
                 (<= 0 I)
                 (INTEGERP K)
                 (<= 0 K)
                 (< I K)
                 (SQUARES-PLUS-3P K X)
                 (NOT (EQUAL (CAR X) (+ 3 (* I I))))
                 (NOT (MEMBER (+ 3 (* I I)) X)))
            (SQUARES-PLUS-3P K (REV X)))?
   ~ev[]

   The experienced ACL2 user will stop reading at the second hypothesis!
   ~bv[]
                 (MEMBER (+ 3 (* I I)) (REV X))
   ~ev[]

   The combination of ~c[MEMBER] and ~c[REV] can be simplified.  The question
   ``is ~c[e] a member of ~c[(REV x)]'' can be answered by asking ``is ~c[e] a
   member of ~c[x]''.  The two questions are equivalent.  This insight comes from
   your intuition about the ~i[semantics] of ~c[REV] -- it just reorders the
   elements but doesn't add or delete any.  The second question is simpler
   since it doesn't mention ~c[REV], so this is a good transformation to make.
   And the theorem that they are equivalent is simpler than the key checkpoint
   above because it involves fewer functions and smaller expressions.

   You might formalize this insight as
   ~bv[]
   (equal (member e (rev x))
          (member e x))
   ~ev[]
   But this conjecture is ~i[not] a theorem, because ~c[(member e x)] returns the
   ~c[cdr] of ~c[x] that begins with ~c[e], not just a Boolean (~c[t] or
   ~c[nil]) indicating whether ~c[e] is an element of ~c[x].  The location
   of the first ~c[e] in ~c[(rev x)] is generally different than the
   location in ~c[x].  So when we say the two questions are ``equivalent''
   we don't mean they are equal.  We mean that they're propositionally equivalent:
   both ~c[nil] or both non-~c[nil].  This sense of equivalence is called
   ``if and only if'' and is checked by the function ~c[iff].

   So our intuitive insight can be phrased as this theorem:
   ~bv[]
   (iff (member e (rev x))
        (member e x))
   ~ev[]

   Suggesting that this formulation of the insight is ``obvious'' begs many questions.
   Mathematically, we could have avoided ~c[iff] and just written two implications:
   ~bv[]
   (and (implies (member e x) (member e (rev x)))
        (implies (member e (rev x)) (member e x))).
   ~ev[]
   or
   ~bv[]
   (and (implies (member e x) (member e (rev x)))
        (implies (not (member e x))  (not (member e (rev x))))).
   ~ev[]
   Or we could have used ~c[iff] but ``oriented'' it the other way:
   ~bv[]
   (iff (member e x)
        (member e (rev x)))
   ~ev[]
   We choose to write
   ~bv[]
   (iff (member e (rev x))
        (member e x))
   ~ev[]
   because of ~i[our knowledge of how ACL2 turns formulas into rules!]

   We deal with this at greater length later.  But just to drive the point home,
   if we issue the command:
   ~bv[]
   (defthm member-rev
     (iff (member e (rev x))
          (member e x)))
   ~ev[]
   ACL2 will build in a rule that causes every propositional occurrence of
   ~c[(MEMBER e (REV x))] to be replaced by ~c[(MEMBER e x)].  (By
   ``propositional occurrence'' we mean an occurrence in which the value is
   tested, as by ~c[IF] or the propositional connectives.  Remember, one
   might use ~c[member] to determine the location of an element too.)

   Note carefully: ~i[if you do not tell ACL2 how to make a rule] from a
   theorem, it makes a rewrite rule.  Rewrite rules always replace instances of
   the left-hand side by the corresponding instances of the right-hand side.
   That is, when interpreted as a rewrite rule, ~c[(iff ]~i[alpha]
   ~i[beta]~c[)] makes ACL2 replace ~i[alpha] by ~i[beta].

   Probably the biggest mistake new users make is forgetting that every theorem
   they prove creates a very specific rule.  You must remember that you are
   ~i[programming] ACL2 with these rules.  Being careless in your statement of
   theorems is tantamount to being careless in your programming.  What you get
   is a mess.

   Had we proved the same equivalence, but with the ~c[iff] commuted, we would
   be giving ACL2 ~i[bad advice].  We would be telling it ``replace instances
   of ~c[(MEMBER e x)] by the corresponding instances of ~c[(MEMBER e (REV x))]''!
   If ACL2 had that rule and ever tried to simplify any ~c[member]
   expression, e.g., ~c[(MEMBER A B)], it would get into an infinite loop,
   e.g., producing the following sequence of transformations:

   ~bv[]
   (MEMBER A B)
   (MEMBER A (REV B))
   (MEMBER A (REV (REV B)))
   ...
   ~ev[]
   until it eventually exhausted some resource.

   Recall that we entertained the idea of phrasing our insight about ~c[member]
   and ~c[rev] with implications rather than ~c[iff].  Generally speaking,
   implications produce weaker rules -- rules that apply less often.  We
   discuss that later.

   Now suppose we've proved ~c[member-rev], oriented so as to rewrite
   ~c[(member e (rev x))] to ~c[(member e x)], and built it in as a rewrite
   rule.  Then suppose we repeated the attempt to prove our Main Theorem.
   This time, when the prover is processing the hideous Key Checkpoint printed above,
   our new lemma, ~c[member-rev], will hit it.  It will transform the formula to:

  ~bv[]
   (IMPLIES (AND (CONSP X)
                 (MEMBER (+ 3 (* I I)) X)   ; <-- the hyp has simplified
                 (LIST-OF-INTEGERS X)
                 (INTEGERP I)
                 (<= 0 I)
                 (INTEGERP K)
                 (<= 0 K)
                 (< I K)
                 (SQUARES-PLUS-3P K X)
                 (NOT (EQUAL (CAR X) (+ 3 (* I I))))
                 (NOT (MEMBER (+ 3 (* I I)) X)))
            (SQUARES-PLUS-3P K (REV X)))?
   ~ev[]

   and then that will collapse to ~c[T], since the ~c[IMPLIES] has
   contradictory hypotheses (note the last hypothesis above).

   By proving ~c[member-rev] we proved the hideous checkpoint.  We never had to look
   at the rest of the formula or think about why it is a theorem.  Furthermore,
   attacking the main theorem again, from scratch, with ~c[member-rev] in
   the database, may eliminate other checkpoints that came up the last time we
   tried to prove our main goal.  So we recommend addressing one checkpoint at
   a time.

   This example illustrates that purely ~i[local] thinking -- looking for
   simplifiable combinations of function symbols -- can sometimes lead to
   proofs and should always be your first reaction to a key checkpoint: what
   local fact do you know that would clean up the formula?  Don't think about
   deep questions like ``why is this true?''  until you can't see any way to
   make it simpler.

   It is important to train yourself to see combinations of function symbols
   and to create strong rules for eliminating them.  We will give you opportunities
   to practice this later in the tutorial.

   If you have been reading the tutorial introduction to the theorem prover,
   use your browser's ~b[Back Button] now to return to
   ~il[INTRODUCTION-TO-KEY-CHECKPOINTS].

   ~/~/")

(deflabel post-induction-key-checkpoints
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   reading post-induction key checkpoints~/

   Each post-induction key checkpoint is a theorem if and only if the original
   conjecture was a theorem.  The reason is that each subgoal produced by
   induction concludes with the original formula and simplification preserves
   equivalence.

   So if you see a post-induction key checkpoint that is not a theorem, stop
   looking at the checkpoints!  Your original conjecture is not a theorem!  Fix
   it.

   If you're convinced all the post-induction conjectures are theorems, ask
   whether each has the hypotheses you'd need to prove it.  If the case
   analysis feels inappropriate or induction hypotheses seem to be missing,
   then ACL2 might have done the wrong induction.  Find the induction scheme it
   did by reading the first induction message printed after the conjecture was
   submitted.  If it is wrong, then extend ACL2's induction analysis or tell
   ACL2 what induction to do, as explained shortly.

   But before you decide the induction hypothesis is missing, look closely for
   contradictions among the hypotheses of the checkpoint formula.  For example,
   perhaps one of the hypotheses is ~c[(MEMBER e x)] and another is
   ~c[(NOT (MEMBER e' x'))] where ~c[e], ~c[x], ~c[e'], and ~c[x'] are 
   possibly complicated expressions.

   Is it possible that ~c[e] and ~c[e'] are equal and ~c[x] and ~c[x'] are
   equal?  If so, then the two hypotheses are contradictory and the checkpoint
   would be proved if you could find rules that would simplify those expressions
   to their common forms.  So look for theorems about those subexpressions.

   Or maybe you can get ~c[e] and ~c[e'] to reduce to some common ~c[d] but
   but find that ~c[x] and ~c[x'] are really different.  Then ask
   whether
   ~bv[]
   (implies (member d x) (member d x'))
   ~ev[]
   If you could prove that, the key checkpoint would be proved.  Of course,
   you may need other hypotheses from the checkpoint to state your theorems.

   If you have been working your way through the tutorial introduction to the
   theorem prover, use your browser's ~b[Back Button] now to
   ~il[introduction-to-key-checkpoints].

   ~/~/")

(deflabel generalizing-key-checkpoints
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   getting rid of unnecessary specificity~/

   Suppose ~c[MEMBER] determines whether its first argument is a member of its
   second, and ~c[SUBSETP] determines whether every element of its first
   argument is a member of its second.  Suppose that you're trying to prove
   some Main Theorem and are told the formula below is a key checkpoint.  What
   should you do?
   ~bv[]

   Key Checkpoint:
   (IMPLIES (AND (CONSP A)
                 (INTEGERP (CAR A))
                 (MEMBER (CAR A) B)
                 (SUBSETP (CDR A) B)
                 (NOT (SUBSETP (CDR A) (APPEND B C))))
            (MEMBER (CAR A) C))
   ~ev[]

   The key observation is that the third hypothesis implies the negation of the
   fourth.  Writing it in the contrapositive:
   ~bv[]
   (IMPLIES (AND ...
                 (SUBSETP (CDR A) B)
                 ...)
            (SUBSETP (CDR A) (APPEND B C)))
   ~ev[]
   In fact, that is more complicated than it needs to be.
   A ``correct'' response to the key checkpoint above is to prove
   ~bv[]
   (defthm subsetp-append
     (implies (subsetp a b)
              (subsetp a (append b c)))).
   ~ev[]

   A still better response is to prove this:
   ~bv[]
   (defthm subsetp-append-2
     (implies (or (subsetp a b)
                  (subsetp a c))
              (subsetp a (append b c)))).
   ~ev[]
 
   This version is better because it handles both of the possibilities regarding whether
   ~c[a] is a subset of the arguments of the ~c[append].  

   It would be nice if we could think of a ``strong'' version, one in which
   ~c[(SUBSETP a (APPEND b c))] is rewritten to some clearly simpler term, but
   nothing comes to mind.

   In any case, if you cannot see any obvious simplification of the individual
   terms in the Key Checkpoint, you should ask yourself whether there are
   connections beween the various propositional parts (as here, with the third
   and fourth hypotheses).  It is a good heuristic to look for relations
   between parts with the same top-level function symbol (as here, with
   ~c[SUBSETP]).  It is also a good heuristic to throw out parts of the formula
   that seem disconnected (as here, with the terms involving ~c[(CAR A)]).

   This discussion suggests several ``modes'' of looking at key checkpoints and
   the idea of trying the modes in sequence:

   (1) look for simplifiable combinations of function symbols within
   propositional components,

   (2) look for relations between propositional components, and

   (3) throw out irrelevant or weakly connected components.

   In all cases you are bringing to bear your intuitions about the
   ~i[semantics] of the terms.  That is, you're not just slinging symbols.  You
   should be looking out for obvious truths about individual parts of the
   checkpoints...  truths that are obvious to you but not to ACL2!

   Ultimately the three ``modes'' are the same and we do not really recommend
   adhering to the given sequence.  You're just looking for simpler theorems that,
   in combination, imply the checkpoint.  Keeping the ``modes'' in mind may
   help focus your attention so you consider all the plausible possibilities.
   After a little experience you'll find yourself looking for all these things
   simultaneously as part ``cleaning up'' the checkpoints.

   When your main goal theorems are harder than these, your main concern will
   be looking at a Key Checkpoint and asking yourself ``why is this true?''
   But you don't want to do that until you've cleaned it up ``locally'' as much
   as possible and sometimes -- more often than you might think -- local
   considerations can prove many of your checkpoints.

   If you have been working your way through the tutorial introduction to the
   theorem prover, use your browser's ~b[Back Button] now to return to
   ~il[introduction-to-key-checkpoints].

   ~/~/")

(deflabel strong-rewrite-rules
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   formulating good rewrite rules~/

   Suppose you notice the following term in a Key Checkpoint:
   ~bv[]
   (MEMBER (CAR A) (REV B)).
   ~ev[]
   You might think of two theorems for handling this term, which we'll call the
   ``weak'' and ``strong'' version of ~c[member-rev].

   ~bv[]
   (defthm member-rev-weak
     (implies (member e b)
              (member e (rev b)))).

   (defthm member-rev-strong
     (iff (member e (rev b))
          (member e b))).
   ~ev[]

   The ``strong'' version logically implies the ``weak'' version and so deserves
   the adjective.  (Recall that ``~i[p] <---> ~i[q]'' is just ``~i[p] ---> ~i[q]''
   and ``~i[q] ---> ~i[p].''  So the strong version quite literally says
   everything the weak version does and then some.)

   But the ``strong'' version also produces a ~i[better] rewrite rule.  Here 
   are the rules generated from these two formulas, phrased as directives to
   ACL2's simplifier:

  ~c[member-rev-weak]: If you ever see an instance of ~c[(MEMBER e (REV b))],
   backchain to ~c[(MEMBER e b)] (i.e., turn your attention to that term) 
   and if you can show that it is true, replace ~c[(MEMBER e (REV b))] by ~c[T].

   ~c[member-rev-strong]:  If you ever see an instance of ~c[(MEMBER e (REV b))],
   replace it by ~c[(MEMBER e b)]. 

   Technical Note: Actually, both rules concern ~i[propositional] occurrences
   of the ``target'' expression, ~c[(MEMBER e (REV b))], i.e., occurrences of
   the target in which its truthvalue is the only thing of relevance.  (Recall
   that ~c[(MEMBER x y)] returns the tail of ~c[y] starting with ~c[x]!
   Evaluate some simple ~c[MEMBER] expressions, like ~c[(MEMBER 3 '(1 2 3 4 5))]
   to see what we mean.)  Both theorems tell us about circumstances in which
   the target is non-~c[NIL] (i.e., ``true'') without telling us its identity.
   But ACL2 keeps track of when the target is in a propositional occurrence and
   can use such rules to rewrite the target to propositionally equivalent
   terms.

   So the strong version is better because it will always eliminate
   ~c[(MEMBER e (REV b))] in favor of ~c[(MEMBER e b)].  That simpler
   expression may be further reduced if the context allows it.  But in
   any case, the strong version eliminates ~c[REV] from the problem.  The weak
   version only eliminates ~c[REV] when a side-condition can be proved.

   While either version may permit us to prove the Key Checkpoint that
   ``suggested'' the rule, the strong version is a better rule to have in the
   database going forward.

   For example, suppose ~c[NATS-BELOW] returns the list of natural numbers below its
   argument.  Imagine two alternative scenarios in which a key checkpoint
   is about to arise involving this term:
   ~bv[]
   (MEMBER K (REV (NATS-BELOW J)))
   ~ev[]

   ~b[Scenario 1] is when you've got the strong version in your database: it will
   rewrite the key checkpoint term to
   ~bv[]
   (MEMBER K (NATS-BELOW J))
   ~ev[]
   and that's what you'll see in the printed checkpoint unless other rules
   reduce it further.

   ~b[Scenario 2] is when you have only the weak version in your database: the weak
   rule will attempt to reduce the term above to ~c[T] and will, if there are
   sufficient rules and hypotheses about ~c[K]'s membership in ~c[(NATS-BELOW J)].  But if no
   such rules or hypotheses are available, you'll be confronted with a key checkpoint
   involving
   ~bv[]
   (MEMBER K (REV (NATS-BELOW J)))
   ~ev[]
   and ~i[it will not be obvious] that the problem would go away if you could establish
   that ~c[K] is in ~c[(NATS-BELOW J)].  Clearly, Scenario 1 is better.

   We recommend that you now practice formulating strong versions of rules
   suggested by terms you might see.  ~l[practice-formulating-strong-rules].

   When you are finished with that, use your browser's ~b[Back Button] to
   return to ~il[introduction-to-key-checkpoints].

   ~/~/")

(deflabel practice-formulating-strong-rules
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   a few simple checkpoints suggesting strong rules~/

   Consider these definitions:
   ~bv[]
   (defun rev (x)
     (if (endp x)
         nil
         (append (rev (cdr x)) (list (car x)))))

   (defun nats-below (j)
     (if (zp j)
         '(0)
         (cons j (nats-below (- j 1)))))
   ~ev[]
   We assume you are familiar with such ACL2 built-ins as ~c[append],
   ~c[member], ~c[subsetp] and ~c[true-listp].  When we use throw-away names
   like ~c[FOO], ~c[BAR], and ~c[MUM] below we mean to suggest some arbitrary function you
   shouldn't think about!  We're just trying to train your eye to ignore
   irrelevant things.

   Below are some terms that should suggest rewrite rules to you.  Imagine that
   each of these terms occurs in some Key Checkpoint.  What rules come to mind?
   Try to think of the strongest rules you can.

   Term 1:~nl[]
   ~c[(TRUE-LISTP (APPEND (FOO A) (BAR B)))]

   Answers:  ~l[practice-formulating-strong-rules-1]

   Term 2:~nl[]
   ~c[(TRUE-LISTP (REV (FOO A)))]

   Answers:  ~l[practice-formulating-strong-rules-2]

   Term 3:~nl[]
   ~c[(MEMBER (FOO A) (APPEND (BAR B) (MUM C)))]

   Answers:  ~l[practice-formulating-strong-rules-3]

   Term 4:~nl[]
   ~c[(SUBSETP (APPEND (FOO A) (BAR B)) (MUM C))]

   Answers:  ~l[practice-formulating-strong-rules-4]

   Term 5:~nl[]
   ~c[(SUBSETP (FOO A) (APPEND (BAR B) (MUM C)))]

   Answers:  ~l[practice-formulating-strong-rules-5]

   Term 6:~nl[]
   ~c[(MEMBER (FOO A) (NATS-BELOW (BAR B)))]

   Answers:  ~l[practice-formulating-strong-rules-6]

   We recommend doing all of these little exercises.  When you're finished, use
   your browser's ~b[Back Button] to return to ~il[strong-rewrite-rules].

   ~/~/")


(deflabel practice-formulating-strong-rules-1
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   rules suggested by ~c[(TRUE-LISTP (APPEND (FOO A) (BAR B)))]~/

   What rules come to mind when looking at the following subterm of a Key
   Checkpoint?  Think of ~i[strong] rules (~pl[strong-rewrite-rules]).
   ~bv[]
   (TRUE-LISTP (APPEND (FOO A) (BAR B)))
   ~ev[]

   Obviously, you must think about the conditions under which ~c[(APPEND x y)]
   returns a true-list.  Recall that ~c[APPEND] concatentates ~c[x] and ~c[y],
   with ~c[y] being the terminal sublist.  Its definition is equivalent
   to
   ~bv[]
   (defun append (x y)
     (if (endp x)
         y
         (cons (car x)
               (append (cdr x) y))))
   ~ev[]
   Technical Note:  ~c[Append] is really a macro that permits you to
   write calls of ~c[append] with more than two arguments.

   In a sense, ~c[append] ``expects'' its arguments to be lists ending in ~c[nil], so-called
   ~c[true-listp]s.  (Such expectations are formalized in ACL2 by the notion of
   the ``~il[guard]'' ~warn[] of the function, but we strongly recommend not investigating
   guards until you're good at using the system.)

   New users frequently start every new theorem by listing all their
   expectations on the arguments of functions in the problem.  For example, if
   the new user wants to make some statement about when ~c[(append x y)] is a
   ~c[true-listp], it is not uncommon for him or her first to write:
   ~bv[]
   (implies (and (true-listp x)
                 (true-listp y))
            ...)
   ~ev[]
   to get ``comfortable.''  Then, thinking about when ~c[(append x y)] is a
   ~c[true-listp] is easy:  it always returns a ~c[true-listp].
   It's always a ~c[true-listp].''  This thinking produces the theorem:
   ~bv[]
   (defthm true-listp-append-really-weak
     (implies (and (true-listp x)
                   (true-listp y))
              (true-listp (append x y))))
   ~ev[]
   You'll note we gave it a name suggesting it is ``really weak.''

   One sense in which it is weak is that it has an unnecessary hypothesis.
   If ~c[y] is a ~c[true-listp], then ~c[(append x y)] is too, whether
   ~c[x] is a ~c[true-listp] or not.  In ACL2, all functions are total.
   Logically speaking, it doesn't matter whether ~c[endp] expects its argument
   to be a ~c[true-listp] or not, it behaves.  ~c[(Append x y)] either returns
   ~c[y] or a ~c[cons] whose second argument is generated by ~c[append].  Thus,
   if ~c[y] is a ~c[true-listp], the answer is too.  So here is an improved
   version of the rule:
   ~bv[]
   (defthm true-listp-append-weak
     (implies (true-listp y)
              (true-listp (append x y))))
   ~ev[]
   We still think of it as ``weak'' because it has a hypothesis that limits
   its applicability.

   The strong version of the rule is
   ~bv[]
   (defthm true-listp-append-strong
     (equal (true-listp (append x y))
            (true-listp y))).
   ~ev[]
   That is, ~c[append] returns a ~c[true-listp] ~i[precisely] when its second
   argument is a ~c[true-listp].  We recommend that the strong version be made
   a :~ilc[rewrite] ~warn[] rule.

   The weak version of the rule allows us to reduce ~c[(TRUE-LISTP (APPEND x y))] to true if
   we can show that ~c[(TRUE-LISTP y)] is true.  But suppose ~c[(TRUE-LISTP y)] is actually
   false.  Then ~c[(TRUE-LISTP (APPEND x y))] would not simplify under the weak version of
   the rule.  But under the strong version it would simplify to ~c[NIL].

   Technical Note: The weak version of the rule is a
   useful :~ilc[type-prescription] ~warn[] rule.  The type mechanism cannot
   currently exploit the strong version of the rule.

   The strategy of ``getting comfortable'' by adding a bunch of hypotheses
   before you know you need them is not conducive to creating strong rules.  We
   tend to state the main relationship that we intuit about some function and
   then add the hypotheses we need to make it true.  In this case, there were no
   necessary hypotheses.  But if there are, we first identify them and then we
   ask ``what can I say about the function if these hypotheses aren't true?''
   and try to strengthen the statement still further.  

   Use your browser's ~b[Back Button] now to return to
   ~il[practice-formulating-strong-rules].~/~/")

(deflabel practice-formulating-strong-rules-2
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   rules suggested by ~c[(TRUE-LISTP (REV (FOO A)))]~/

   What rules come to mind when looking at the following subterm of a Key
   Checkpoint?  Think of ~i[strong] rules (~pl[strong-rewrite-rules]).
   ~bv[]
   (TRUE-LISTP (REV (FOO A)))
   ~ev[]

   The definition of ~c[rev] in this problem is
   ~bv[]
   (defun rev (x)
     (if (endp x)
         nil
         (append (rev (cdr x)) (list (car x)))))
   ~ev[]

   Since the definition terminates with an ~c[endp] test and otherwise ~c[cdr]s
   the argument, the author of ~c[rev] was clearly expecting ~c[x] to be a
   ~c[true-listp].  (Indeed, the ``~il[guard]'' ~warn[] for ~c[rev] must require include
   ~c[(true-listp x)] since that is ~c[endp]'s guard.)  So you're naturally
   justified in limiting your thoughts about ~c[(rev x)] to ~c[x] that are
   true-lists.  This gives rise to the theorem:

   ~bv[]
   (defthm true-listp-rev-weak
     (implies (true-listp x)
              (true-listp (rev x))))
   ~ev[]
   This is the kind of thinking illustrated in the earlier ~c[append] example
   (~pl[practice-formulating-strong-rules-1]) and, to paraphrase Z in ~i[Men in Black],
   it exemplifies ``everything we've come to expect from years of training with
   typed languages.''

   But logically speaking, the definition of ~c[rev] does not require ~c[x] to
   be a ~c[true-listp].  It can be any object at all: ACL2 functions are total.
   ~c[Rev] either returns ~c[nil] or the result of appending a singleton list
   onto the right end of its recursive result.  That ~c[append] always returns
   a ~c[true-listp] since the singleton list is a true
   list.  (~l[practice-formulating-strong-rules-1].)

   So this is a theorem and a very useful :~ilc[rewrite] ~warn[] rule:

   ~bv[]
   (defthm true-listp-rev-strong
     (true-listp (rev x))).
   ~ev[]

   Use your browser's ~b[Back Button] now to return to
   ~il[practice-formulating-strong-rules].

   ~/~/")

(deflabel practice-formulating-strong-rules-3
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   rules suggested by ~c[(MEMBER (FOO A) (APPEND (BAR B) (MUM C)))]~/

   What rules come to mind when looking at the following subterm of a Key
   Checkpoint?  Think of ~i[strong] rules (~pl[strong-rewrite-rules]).
   ~bv[]
   (MEMBER (FOO A) (APPEND (BAR B) (MUM C)))
   ~ev[]

   Since ~c[(append x y)] contains all the members of ~c[x] and all the members
   of ~c[y], ~c[e] is a member of ~c[(append x y)] precisely when ~c[e] is a
   member of ~c[x] or of ~c[y].  So a strong statement of this is:
   ~bv[]
   (defthm member-append-strong-false
     (equal (member e (append x y))
            (or (member e x)
                (member e y))))
   ~ev[]

   However, this is not a theorem because ~c[member] is not Boolean.
   ~c[(Member e x)], for example, returns the first tail of ~c[x] that starts
   with ~c[e], or else ~c[nil].  To see an example of this formula that
   evaluates to ~c[nil], let
   ~bv[]
   e = 3
   x = '(1 2 3)
   y = '(4 5 6).
   ~ev[]
   Then the left-hand side, ~c[(member e (append x y))] evaluates to ~c[(3 4 5 6)] while
   the right-hand side evaluates to ~c[(3)].

   However, the two sides are propositionally equivalent (both either ~c[nil]
   or non-~c[nil] together).  So this is a useful :~ilc[rewrite] ~warn[] rule:
   ~bv[]
   (defthm member-append-strong
     (iff (member e (append x y))
          (or (member e x)
              (member e y)))).
   ~ev[]
   It tells the system that whenever it encounters an instance of
   ~c[(MEMBER e (APPEND x y))] in a propositional occurrence (where only
   its truthvalue is relevant), it should be replaced by this
   disjunction of ~c[(MEMBER e x)] and ~c[(MEMBER e y)].

   The following two formulas are true but provide much weaker rules and
   we would not add them:
   ~bv[]
   (implies (member e x) (member e (append x y)))

   (implies (member e y) (member e (append x y)))
   ~ev[]
   because they each cause the system to backchain upon seeing ~c[(MEMBER e (APPEND x y))]
   expressions and will not apply unless one of the two side-conditions can be established.

   There is a rewrite rule that is even stronger than ~c[member-append-strong].
   It is suggested by the counterexample, above, for the ~c[EQUAL] version of the rule.
   ~bv[]
   (defthm member-append-really-strong
     (equal (member e (append x y))
            (if (member e x)
                (append (member e x) y)
                (member e y))))
   ~ev[]
   While ~c[member-append-strong] only rewrites ~c[member-append] expressions
   occurring propositionally, the ~c[-really-strong] version rewrites ~i[every]
   occurrence.

   However, this rule will be more useful than ~c[member-append-strong] only
   if you have occurrences of ~c[member] in non-propositional places.  For example,
   suppose you encountered a term like:
   ~bv[]
   (CONS (MEMBER e (APPEND x y)) z).
   ~ev[]
   Then the ~c[-strong] rule does not apply but the ~c[-really-strong] rule does.

   Furthermore, the ~c[-really-strong] rule, by itself, is not quite as good as
   the ~c[-strong] rule in propositional settings!  For example, if you have proved
   the ~c[-really-strong] rule, you'll notice that the system still has to use
   induction to prove
   ~bv[]
   (IMPLIES (MEMBER E A)
            (MEMBER E (APPEND B A))).
   ~ev[]
   The ~c[-really-strong] rule would rewrite it to
   ~bv[]
   (IMPLIES (MEMBER E A)
            (IF (MEMBER E A)
                (APPEND (MEMBER E A) B)
                (MEMBER E B)))
   ~ev[]
   which would further simplify to
   ~bv[]
   (IMPLIES (MEMBER E A)
            (APPEND (MEMBER E A) B))
   ~ev[]
   What lemma does this suggest?  The answer is the rather odd:
   ~bv[]
   (implies x (append x y))
   ~ev[]
   which rewrites propositional occurrences of ~c[(APPEND x y)] to ~c[T] if
   ~c[x] is non-~c[nil].  This is an inductive fact about ~c[append].  

   A problem with the ~c[-really-strong] rule is that it transforms even
   propositional occurrences of ~c[member] into mixed propositional and
   non-propositional occurrences.
   ~bv[]
   (defthm member-append-really-strong
     (equal (member e (append x y))      ; <-- even if this is a propositional occurrence
            (if (member e x)
                (append (member e x) y)  ; <-- the member in here is not!
                (member e y))))
   ~ev[]
   So if you are using the ~c[-really-strong] lemma in a situation in which
   all your ~c[member] expressions are used propositionally, you'll suddenly
   find yourself confronted with non-propositional uses of ~c[member].

   Our advice is not to use the ~c[-really-strong] version unless your application is
   inherently using ~c[member] in a non-propositional way.

   Use your browser's ~b[Back Button] now to return to
   ~il[practice-formulating-strong-rules].

   ~/~/")

(deflabel practice-formulating-strong-rules-4
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   rules suggested by ~c[(SUBSETP (APPEND (FOO A) (BAR B)) (MUM C))]~/

   What rules come to mind when looking at the following subterm of a Key
   Checkpoint?  Think of ~i[strong] rules (~pl[strong-rewrite-rules]).
   ~bv[]
   (SUBSETP (APPEND (FOO A) (BAR B)) (MUM C))
   ~ev[]

   When is ~c[(append x y)] a subset of ~c[z]?  When everything in
   ~c[x] is in ~c[z] and everything in ~c[y] is in ~c[z].  We would
   make it a rewrite rule:
   ~bv[]
   (defthm subsetp-append-1-strong
     (equal (subsetp (append x y) z)
            (and (subsetp x z)
                 (subsetp y z))))
   ~ev[]

   We put the ``~c[-1-]'' in the name because there is a comparable
   theorem for when the ~c[append] is in the second argument of the ~c[subsetp];
   ~pl[practice-formulating-strong-rules-5].

   This strong rule is better than the conditional rule;
   ~bv[]
   (defthm subsetp-append-1-weak
     (implies (and (subsetp x z)
                   (subsetp y z))
              (subsetp (append x y) z)))
   ~ev[]
   for all the usual reasons.

   Use your browser's ~b[Back Button] now to return to
   ~il[practice-formulating-strong-rules].

   ~/~/")

(deflabel practice-formulating-strong-rules-5
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   rules suggested by ~c[(SUBSETP (FOO A) (APPEND (BAR B) (MUM C)))]~/

   What rules come to mind when looking at the following subterm of a Key
   Checkpoint?  Think of ~i[strong] rules (~pl[strong-rewrite-rules]).
   ~bv[]
   (SUBSETP (FOO A) (APPEND (BAR B) (MUM C)))
   ~ev[]

   When is ~c[x] a subset of ~c[(append y z)]?  Clearly it is if ~c[x] is a subset of ~c[y]
   or ~c[x] is a subset of ~c[z].  We could write that:
   ~bv[]
   (defthm subsetp-append-2-weak
     (implies (or (subsetp x y)
                  (subsetp x z))
              (subsetp x (append y z))))
   ~ev[]
   The rule generated from this is:  ``if you ever encounter (an instance of)
   ~c[(SUBSETP x (APPEND y z))], backchain to the ~c[or] above and try to
   establish it.  If you can establish it, replace the target by ~c[T].''

   This does not fully characterize the situation though.  For example,
   ~c['(1 2 3 4)] is a subset of ~c[(append '(1 3) '(2 4))] without being
   a subset of either argument of the ~c[append].  

   However, no obvious equivalence comes to mind -- indeed, to express any of
   the ideas floating around here requires defining and introducing more
   functions, which is not recommended unless those functions are already in
   the problem.  

   For example, if you defined the concept of ``~c[set-minus]'' so that
   ~c[(set-minus x y)] consists of those elements of ~c[x] not in ~c[y], then
   you could prove:
   ~bv[]
   (defthm subset-append-2-strong-but-messy
     (equal (subsetp x (append y z))
            (and (subsetp (set-minus x z) y)
                 (subsetp (set-minus x y) z))))
   ~ev[]
   But this rewrite rule would ``trade'' ~c[append] away and introduce ~c[set-minus].
   That might be a good strategy if ~c[set-minus] were already in the problem.
   But if it were not, it might not be.  We wouldn't recommend this rule
   unless it were helpful in normalizing the expressions in the problem.

   We recommend sticking with the weak version of the rule,
   ~bv[]
   (defthm subsetp-append-2-weak
     (implies (or (subsetp x y)
                  (subsetp x z))
              (subsetp x (append y z)))).
   ~ev[]
   This illustrates the fact that sometimes there is no strong version of a rule!

   Use your browser's ~b[Back Button] now to return to
   ~il[practice-formulating-strong-rules].

   ~/~/")


(deflabel practice-formulating-strong-rules-6
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   rules suggested by ~c[(MEMBER (FOO A) (NATS-BELOW (BAR B)))]~/

   What rules come to mind when looking at the following subterm of a Key
   Checkpoint?  Think of ~i[strong] rules (~pl[strong-rewrite-rules]).
   ~bv[]
   (MEMBER (FOO A) (NATS-BELOW (BAR B)))
   ~ev[]
   The definition of ~c[NATS-BELOW] is
   ~bv[]
   (defun nats-below (j)
     (if (zp j)
         '(0)
         (cons j (nats-below (- j 1)))))
   ~ev[]
   Thus, ~c[(nats-below 7)] is ~c[(7 6 5 4 3 2 1 0)].  So when is ~c[k] a member
   of ~c[(nats-below j)]?

   The weakest version is
   ~bv[]
   (defthm member-nats-below-weak
     (implies (and (natp k)
                   (natp j)
                   (<= k j))
              (member k (nats-below j))))
   ~ev[]
   But clearly we could improve this to:
   ~bv[]
   (defthm member-nats-below-weak-better
     (implies (and (natp k)
                   (natp j))
              (iff (member k (nats-below j))
                   (<= k j))))
   ~ev[]
   or even
   ~bv[]
   (defthm member-nats-below-weak-better
     (implies (natp j)
              (iff (member k (nats-below j))
                   (and (natp k)
                        (<= k j)))))
   ~ev[]
   Clearly though, we'd like to get rid of the ~c[(natp j)] hypothesis and the 
   neatest plausible version is:
   ~bv[]
   (defthm member-nats-below-weak-neatest
     (iff (member k (nats-below j))
          (and (natp j)
               (natp k)
               (<= k j))))

   ~ev[]
   But it is not a theorem!  For example, if ~c[j] is ~c[-1] and ~c[k] is 0,
   then the left-hand side above returns ~c[t], because ~c[(nats-below j)] is ~c[(0)],
   but the right-hand side is ~c[nil].  

   But this suggests a strategy for dealing with necessary hypotheses, like ~c[(natp j)].
   We can move them into an ~c[IF] on the right-hand side!  Something like this
   might be a useful rewrite rule:
   ~bv[]
   (iff (member k (nats-below j))
        (if (natp j)
            (and (natp k)
                 (<= k j))
            ...)).
   ~ev[]
   We know, from ~c[member-nats-below-weak-better], that if ~c[(natp j)] is true,
   the ~c[member] is equivalent to ~c[(and (natp k) (<= k j))].  So now consider
   what we know if ~c[(natp j)] is false.  If we can think of some term it's equivalent
   to nd that term is simpler than the ~c[member] expression, we have a strong rule.

   But by inspection of the definition of ~c[nats-below], we see that when
   ~c[(natp j)] is false, ~c[(nats-below j)] is the list ~c[(0)] because ~c[(zp j)]
   is t.  That is, ~c[nats-below] treats all non-natural arguments like
   they were ~c[0].  Thus, when ~c[(natp j)] is false, ~c[(member k (nats-below j))] 
   is ~c[(member k '(0))], which is ~c[(equal k 0)].

   So the strong version is
   ~bv[]
   (defthm member-nats-below-strong
      (iff (member k (nats-below j))
           (if (natp j)
               (and (natp k)
                    (<= k j))
               (equal k 0))))
   ~ev[]
   This is a great :~ilc[rewrite] ~warn[] rule.  It gets rid of the ~c[member] and ~c[nats-below] and
   introduces arithmetic.   

   This example illustrates the idea of putting an ~c[if] on the right-hand-side of the 
   equivalence.  Many users tend to limit themselves to propositional forms inside
   ~c[iff] or to simple expressions inside of ~c[equal].  But it is quite natural to
   use ~c[if] to express what the answer is:  if ~c[j] is a natural, then ~c[k] is
   in ~c[(nats-below j)] precisely if ~c[k] is a natural less than or equal to ~c[j];
   if ~c[j] is not a natural, then ~c[k] is in ~c[(nats-below j)] precisely if ~c[k] is
   ~c[0].

   Use ~c[if] to lay out the cases you must consider, if you can think of a simpler, equivalent
   expression for every possible case.

   Use your browser's ~b[Back Button] now to return to
   ~il[practice-formulating-strong-rules].

   ~/~/")

(deflabel introduction-to-key-checkpoints
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   What questions to ask at key checkpoints~/

   We assume you've read about rewrite rules; ~pl[introduction-to-rewrite-rules-part-1].

   When a proof attempt fails, ACL2 prints some ~i[key checkpoints].  These are
   formulas that we think you should look at.  There are two kinds printed: key
   checkpoints ~i[before an induction], and key checkpoints ~i[under a top-level induction].
   (Key checkpoints under deeper inductions and checkpoints that aren't
   considered ``key'' may exist in the proof attempt, but ACL2 doesn't print
   them at the end of failed proofs because you shouldn't be distracted by
   them.)

   Below is a list of questions to ask yourself about the key checkpoints.
   Initially, we recommend just picking one key checkpoint ~i[before] an
   induction (perhaps the simplest looking one) and asking these questions.
   These questions may lead you to look at other key checkpoints.
   As you gain more experience you'll elaborate and generalize this advice.

   ~b[(1) Do you believe this formula is a theorem?]  If you don't think it is,
   it's pointless to try to prove it!  You should reconsider your top-level
   formula in light of the special case suggested by this key checkpoint.

   ~b[(2) Can it be simplified?]  Is there some combination of function
   symbols in it that could be eliminated or simplified by exploiting some
   simpler fact?  By a ``simpler fact'' we mean a theorem about a few of the
   symbols in this formula.  For an example of this
   ~pl[dealing-with-key-combinations-of-function-symbols].  Don't think about
   the deep question ``how can I prove the checkpoint?'' until you've got it
   into its simplest form.

   ~b[(3) Is the simpler fact already in the database?]  If there is some
   simpler fact that would help clean up the checkpoint but you believe the
   simpler fact is already in the database, you can use ~c[:]~ilc[pl] ~warn[],
   ~c[:]~ilc[pc] ~warn[], ~c[:]~ilc[pbt] ~warn[], and other ~i[history]
   commands to inspect the database; (~pl[history] ~warn[]).  But if you find
   the allegedly relevant simpler fact in the database, you must ask:
   ~b[why wasn't it used?]  There are four principal reasons:

   (3a) it is disabled -- so enable it; you'll learn how when you read
   the coming sections on ~il[introduction-to-the-database] and
   ~il[introduction-to-hints].

   (3b) its left-hand side doesn't match the target -- so improve the rule by
   generalizing its left-hand side or prove a new rule for this situation; if you
   decide to remove the old rule from the database, see ~i[undo] commands in
   ~il[history] ~warn[].

   (3c) it is an ~c[IFF] rule but the target doesn't occur propositionally --
   so see if you you can strengthen the rule to an ~c[EQUAL] rule or weaken the
   context of the target by changing the conjecture to use the target
   propositionally; if you decide to remove the old rule from the database, see
   ~i[undo] commands in ~il[history] ~warn[].

   (3d) the hypotheses of the rule cannot be relieved for this occurrence of
   the target; this can be caused by the rule's hypotheses being too
   strong (requiring more than they should), or by the hypotheses of the
   current conjecture being too weak (you forgot some key hypothesis), or by
   ACL2 not having the rules it needs to prove that the conjecture's hypotheses
   really do imply the rule's.  Tools are available (~c[:]~pl[brr] ~warn[])
   help you figure out why the rule failed, so use them and improve the rule,
   or the current conjecture, or the database as appropriate.

   ~b[(4) If the simpler fact is not already known, prove it.]  This means you
   must create a new ~c[defthm] event with appropriate ~i[rule-classes] to
   store your new theorem so that it will be used.
   ~l[dealing-with-key-combinations-of-function-symbols].  Then you must
   start using The Method recursively to prove your new lemma.

   ~b[(5) Otherwise, is this formula something you'd prove by induction?]  If
   you can't simplify it, it may be because you ``need this fact to prove this
   fact,'' in which case, induction is the right thing to do.  But first,
   remember that in order for a formulas to be provable by induction, it must
   be very general.  Why must it be general?  Because in an inductive proof,
   the main thing you have to work with is the induction hypothesis, which is
   an instance of the theorem you're proving.  If the theorem is not general
   enough, you won't be able to assume an instance that will help you.  ACL2
   may try induction even on formulas that are not general enough.  Don't
   assume that the formula is ripe for induction just because ACL2 found an
   induction to do!  Before you ``approve'' a formula for induction, ask
   whether it is perhaps a special case of some more general theorem.
   ~l[generalizing-key-checkpoints] now and then come back here.  If you found
   a generalization, you should probably be proving that formula instead of
   this one.  So formulate the appropriate ~c[defthm] and use The Method
   recursively to prove it.

   ~b[(6) If the formula is right for induction, did ACL2 do an induction for it?]
   You can answer that without looking at the proof.  Just see if there are any
   key checkpoints after induction.  If not, why didn't ACL2 induct?  Perhaps
   you told ACL2 not to induct!  Perhaps no term in the conjecture suggests an
   appropriate induction?  You could remedy this by extending ACL2's induction
   analysis by adding to the database.  Or you could just tell ACL2 what
   induction to do for this formula.  You'll learn about both later (when you
   read coming sections of the tutorial).

   ~b[(7) If ACL2 did do an induction, was it the right one?]  You can find
   the induction scheme used by reading the first induction message in the
   output log after you submitted the conjecture to ACL2.  But most often you
   will realize the ``wrong'' induction was done just by looking at the
   post-induction key checkpoints, keeping in mind that each is supposed to be
   a natural special case of the theorem you're proving.  Is the case analysis
   inappropriate?  Are induction hypotheses missing?  If so, you should look at
   the induction scheme.  If you determine the wrong induction was done, extend
   ACL2's induction analysis or tell it which induction to do, which you'll
   learn about in the coming sections of the tutorial.  For more advice about
   looking at post-induction key checkpoints,
   ~pl[post-induction-key-checkpoints] now and then come back here.

   ~b[(8) If the post-induction key checkpoints seems plausible,]
   ~b[then repeat the questions above for each one of them,]
   ~b[perhaps starting with the simplest.]

   In any case, after successfully taking whatever action you've decided on, e.g.,
   proving some new lemma and adding it as a rule:

   ~b[Start over trying to prove your main conjecture.]  This is important!
   Do not just scroll back to the key checkpoints generated the last time you
   tried to prove it.  Instead, re-generate them in the context of your new,
   improved database and hints.

   You will be following this general outline almost all of the time that you're
   interacting with ACL2.  You will not often be asking ``Why is ACL2 making me
   think about this subgoal?  What did ACL2 do to get here?  How does ACL2
   work?''

   Two other ideas are helpful to keep in mind.  

   ~b[Is a key checkpoint unexpectedly complicated?]  Pay special attention to
   the case where the complication seems to be the introduction of low-level
   details you thought you'd dealt with or by the introduction of symbols you
   didn't expect to see in this proof.  These can be signs that you ought to
   disable some rules in the database (e.g., a definition of a complicated
   function about which you've proved all the necessary lemmas or some lemma
   that transforms the problem as was appropriate for some other proof).

   ~b[Does the theorem prover just hang up, printing nothing?]  If this happens,
   you must interrupt it.  How you interrupt the prover is dependent on which
   Common Lisp and which interface you're using.  But most Common Lisps treat
   control-c as a console interrupt.  If you're in Emacs running ACL2 as a
   shell process, you must type control-c control-c.  If you're in ACL2s, hit the
   ~i[Interrupt Session] button.  Interrupting ACL2 can leave you in an interactive
   loop similar in appearance but different from ACL2's top-level!  So pay careful
   attention to the prompt and ~pl[breaks] ~warn[].

   Once you've regained control from the ``runaway'' theorem prover, there are
   several tools you can use to find out what it is doing in real-time.
   Generally speaking, when the theorem prover goes silent for a very long time
   it is either in some kind of rewrite loop caused by rules that cause it to
   flip back and forth between various supposedly normal forms, or else it has
   split the problem into a huge number of cases and suffering a combinatoric
   explosion.  ~l[DMR] ~warn[] and, perhaps, ~pl[accumulated-persistence]
   ~warn[].

   If you are reading this as part of the tutorial introduction to the theorem
   prover, use your browser's ~b[Back Button] now to return to
   ~il[introduction-to-the-theorem-prover].  ~/~/")

(deflabel programming-knowledge-taken-for-granted
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   background knowledge in ACL2 programming for theorem prover tutorial~/

   This brief review of the programming language is presented as a sequence of
   questions and answers meant to test your knowledge of the ACL2 programming
   language.  If you want a gentle introduction to the programming language,
   see
   ~url[http://www.cs.utexas.edu/users/moore/publications/gentle-intro-to-acl2-programming.html].

   Before we get started with the programming drill, let us remind you that all we're
   interested in here is the language, not the ``program development environment.''
   It's impossible to program in ACL2 or any other language without a decent
   environment, one that at the very least includes a way to prepare and edit
   files of programs.  The two most popular program development environments among
   ACL2 users are ~il[Emacs] ~warn[] and the Eclipse-based ~il[ACL2-Sedan] ~warn[].
   The Sedan provides the most support for the new user, including real-time syntax
   checking and a facility for testing among many other features.  But in this
   drill we're not interested in the program development environment, we're interested
   in your understanding of the ACL2 language.

   ~b[Q]: What do you think this command does?
   ~bv[]
   (defun rev (x)
     (if (endp x)
         nil
         (append (rev (cdr x)) (list (car x)))))
   ~ev[]
   ~b[A]:  It defines a function named ~c[rev] that takes one argument, treats
   it like a list, and reverses the order of the elements in
   that list.  To figure this out from the definition, you have to know that
   ~c[append] concatenates two lists.  Logically speaking, the ~c[defun] of
   ~c[rev] adds the axiom:
   ~bv[]
   (rev x)
   =
   (if (endp x)
       nil
       (append (rev (cdr x)) (list (car x)))),
   ~ev[]
   implicitly quantified for all ~c[x].

   ~b[Q]:  Given the ~c[defun] of ~c[rev] above, what are the ~i[formal parameters]?
   What is the ~i[body] of the definition?  Write down a ~i[call] of ~i[append]
   that occurs in the body of ~c[rev].  What are the ~i[actuals] of that call?
   ~b[A]:  The ~i[formals] of ~c[rev] is the list of variables after the first ~c[rev]
   in the ~c[defun], namely ~c[(x)].  We say ~c[x] is the first (and only) ~i[formal] here.
   The ~i[body] of ~c[rev] is the entire ~c[if]-expression.  The only ~i[call] of
   ~c[append] in the body is
   ~bv[]
   (append (rev (cdr x)) (list (car x)))
   ~ev[]
   and the ~i[actuals] of that call are, respectively, ~c[(rev (cdr x))] and
   ~c[(list (car x))].   

   ~b[Q]: What do you get if you evaluate ~c[(rev '(a b c d))]?  ~b[A]:
   ~c[(D C B A)].

   ~b[Q]: How did ~c[rev] change the case of the elements, e.g., lowercase ~c[a] 
   was in the input list but uppercase ~c[A] was in the output?  ~b[A]:
   This is a trick question.  ~c[Rev] doesn't change the case of the elements.
   ACL2 is case-insensitive when dealing with symbols.  The symbol ~c[a] is
   read in as the symbol ~c[A].  Thus, when writing function names, for 
   example, we can write ~c[rev], ~c[Rev], ~c[REV], or even ~c[ReV]
   and always be referring to the function ~c[REV].  By default, ACL2
   prints symbols in uppercase.

   ~b[Q]: What does ~c[(rev '((a b c) \"Abc\" \"a\" b #\\c))] return?  ~b[A]:
   ~c[(#\\c B \"a\" \"Abc\" (A B C))].  If you thought the answer was any of
   these, then you need to think or read more carefully:
   ~bv[]
   (#\\C B \"A\" \"ABC\" (A B C))

   (#\\C B \"A\" \"ABC\" (C B A))
   ~ev[]
   The first wrong answer above is wrong because Lisp is ``case insensitive'' only
   for symbols, not for character objects like ~c[#\\c] (the lowercase character c)
   or for strings.   Furthermore, ~c[\"A\"] is a string, not a symbol; it is different
   from ~c[A].  The second wrong answer above is wrong because ~c[rev] does not 
   go into the individual elements of the list, it just reverses the order of the
   elements.  So it doesn't change the element ~c[(A B C)] to ~c[(C B A)].

   ~b[Q]: In the question about what ~c[(rev '(a b c d))] returns, we put a quote
   mark before the ~c[(a b c d)] but not before the answer, ~c[(D C B A)].
   Why?  ~b[A]:  The phrase ``~i[x] evaluates to ~i[y]'' treats
   ~i[x] as a ~i[term] to be evaluated and ~i[y] as an ~i[object].
   ~c[(Rev '(a b c d))] is a term to be evaluated and denotes
   a call of the function ~c[rev] on the value of the argument term
   ~c['(a b c d)].  The value of that argument term is the object ~c[(a b c d)].
   The value of the call of ~c[rev] is the object ~c[(d c b a)].
   If you have an object, ~i[obj], and you wish to create a term whose
   value is ~i[obj], then you put a quote mark in front of it, ~i['obj].

   ~b[Q]: Can ~c[rev] be applied to something other than a list?  ~b[A]:  Yes,
   every ACL2 function can be applied to any object.  ACL2 is an untyped
   programming language:  every variable ranges over the entire universe of
   objects.  In normal usage, ~c[rev] is applied to lists but there is nothing
   about the syntax of the language that prevents it being applied to
   non-lists.

   ~b[Q]: So what does ~c[(rev 23)] evaluate to?  ~b[A]:  ~c[Nil].  

   ~b[Q]: Why?  ~b[A]:  Because ~c[(endp 23)] is ~c[t], because ~c[endp] is
   defined:
   ~bv[]
   (defun endp (x) (not (consp x)))
   ~ev[]
   Thus, if ~c[rev] is applied to anything that is not a cons, it returns
   ~c[nil].

   ~b[Q]: So what does ~c[(rev '(a b c . d))] evaluate to?  ~b[A]:  ~c[(c b a)].
   To explain why requires demonstrating that you know what ~c[(a b c . d)]
   means.  It is the object computed by evaluating:
   ~bv[]
   (cons 'a
         (cons 'b
               (cons 'c
                     'd))).
   ~ev[]
   That is, it is a list whose ``terminal marker'' is the atom ~c[D].
   ~c[Rev] treats that list exactly as it treats the ~c[nil]-terminated
   list of the same elements, ~c[(a b c)], because ~c[(endp 'D)] = 
   ~c[(endp nil)] = ~c[t].

   ~b[Q]: What does ~c[(rev 1 2 3)] evaluate to?  ~b[A]: That's a trick question.
   ~c[Rev] takes one argument, not three.  So ~c[(rev 1 2 3)] is an ill-formed term.

   ~b[Q]: What does ~c[(rev '(a b c . d . nil))] evaluate to?  ~b[A]:  That is
   a trick question.  There is no such object.  In Lisp's ``dot notation''
   every dot must be followed by a well-formed object and then a close
   parenthesis.  Usually that ``well-formed object'' is an atom.  If it is
   not an atom, i.e., if it is a cons, then the entire expression could have
   been written without that dot.  For example, ~c[(a b c . (d e))] is
   an object, but it could be written ~c[(a b c d e)].

   ~b[Q]: Do ~c[(rev (rev x))] and ~c[x] always evaluate to the same object?  ~b[A]:
   No.  ~c[(Rev (rev 23))] evaluates to ~c[nil], not ~c[23].

   ~b[Q]: Do ~c[(rev (rev x))] and ~c[x] always evaluate to the same object when
   ~c[x] is a cons?  ~b[A]:  No.
   ~c[(rev (rev '(a b c . d)))] evaluates to ~c[(a b c)], not ~c[(a b c . d)].

   ~b[Q]: When are ~c[(rev (rev x))] and ~c[x] equal?  ~b[A]: When the terminal
   marker of ~c[x] is ~c[nil].

   ~b[Q]: Can you define a Lisp function that recognizes ~c[nil]-terminated lists?
   ~b[A]:  Yes, but it is not necessary for the user to define that
   concept because Common Lisp provides such a
   function which is logically defined as follows:
   ~bv[]
   (defun true-listp (x)
     (if (consp x)
         (true-listp (cdr x))
         (equal x nil))).
   ~ev[]
   This can be paraphrased: ~c[(true-listp x)] means that if ~c[x] is a
   ~c[cons], its ~c[cdr] is a ~c[true-listp] and if ~c[x] is not a ~c[cons], it
   must be ~c[nil].  Thus, ~c[(true-listp '(a b c))] is ~c[t] and
   ~c[(true-listp '(a b c . d))] is ~c[nil].

   ~b[Q]: Can you write a Lisp formula that says ``If ~c[z] is a ~c[nil]-terminated
   list then reversing the result of reversing ~c[z] is ~c[z]''?

   ~b[A]:  Yes:
   ~bv[]
   (implies (true-listp z)
            (equal (rev (rev z)) z)).
   ~ev[]

   ~b[Q]:  Is this all there is to ACL2 programming?  ~b[A]:  No!  ACL2 provides
   many other features.  For a full list of all the primitive functions in ACL2
   ~pl[programming] ~warn[].  Some highlights for the beginner are mentioned below,
   but all of the links below ought to be tagged with the ~warn[] sign.

   * ~ilc[list]:  build a ~c[nil]-terminated list from the values of ~i[n] terms, e.g.,
   ~c[(list x (+ 1 x) (+ 2 x))] returns ~c[(3 4 5)] if ~c[x] is ~c[3].

   * ~il[list*]: build a non-~c[nil] terminated list of ~i[n] objects from the
   values of ~i[n+1] terms, e.g., ~c[(list* x (+ 1 x) (+ 2 x) (* -1 x))] returns
   the list ~c[(3 4 5 . -3)] if ~c[x] is ~c[3].

   * ~ilc[and], ~ilc[or], ~ilc[not], ~ilc[implies], ~ilc[iff]:  The propositional
   connectives.  ~c[And] and ~c[or] are allowed to take a varying number of arguments, e.g.,
   ~c[(and p q r)] is just an abbreviation for ~c[(and p (and q r))].  
   In Lisp, ~c[and] returns ~c[nil] if any of its arguments evaluates to ~c[nil]; otherwise
   it returns the value of the last argument!  Thus, ~c[(and t t 3)] returns ~c[3]!  If you
   object to the idea that ~c[and] is not Boolean, don't give it non-Boolean arguments!
   Similarly, ~c[or] returns the value of the first argument that evaluates to
   non-~c[nil], or ~c[nil] if they all evaluate to ~c[nil].  Both ~c[and] and ~c[or] can
   be thought of as ``lazy'' in that they don't always have to evaluate all their arguments.
   This is really accomplished by treating ~c[and] and ~c[or] as abbrevations for ~c[if]
   nests.

   * ~ilc[+], ~ilc[*], ~ilc[-], ~ilc[/], ~ilc[floor], ~ilc[mod], ~ilc[<], ~ilc[<=], ~ilc[>=], ~ilc[>]:
   the Lisp elementary arithmetic operators.  Both ~c[+] and ~c[*] allow varying numbers of
   arguments.  All the arithmetic operators default non-numeric arguments to ~c[0].  If you
   don't like the idea that ~c[(+ 1 2 t)] is ~c[3], don't ask ~c[+] to add ~c[t] to something!

   * ~ilc[natp], ~ilc[integerp], ~ilc[rationalp], ~ilc[characterp], ~ilc[stringp], ~ilc[symbolp],
   ~ilc[consp]:  the recognizers for the primitive data types.  The first three recognize subsets of
   the ACL2 numeric universe.  The naturals are a subset of the integers, the integers are a
   subset of the rationals, and the rationals are a subset of the objects recognized by
   ~ilc[acl2-numberp], which also includes the ~ilc[complex-rationalp]s.  The other
   recognizers listed above recognize characters, strings, symbols, and conses.

   * ~ilc[cond]:  a convenient way to write a cascading nest of ~c[if]s, e.g.,
   ~bv[]
   (cond ((not (natp x)) 'non-natural)
         ((equal x 0) 'zero)
         ((evenp x) 'positive-even)
         (t 'positive-odd))
   ~ev[]
   abbreviates
   ~bv[]
   (if (not (natp x))
       'non-natural
       (if (equal x 0)
           'zero
           (if (evenp x)
               'positive-even
               'positive-odd))).
   ~ev[]

   * ~ilc[case]:  a convenient way to case split on the identity of an object.
   ~bv[]
   (case key
     (non-natural -1)
     (zero 0)
     ((positive-even positive-odd) 'positive-natural)
     (otherwise 'unknown))
   ~ev[]
   abbreviates
   ~bv[]
   (cond ((eql key 'non-natural) -1)
         ((eql key 'zero) 0)
         ((member key '(positive-even positive-odd))
          'positive-natural)
         (t 'unknown)).
   ~ev[]

   * user defined macros:  using ~ilc[defmacro] ~warn[] you can introduce your own
   abbreviations.  We recommend you not do this until you're good at list processing
   since macros are functions that build objects representing terms.

   * ~ilc[mutual-recursion]:  allows you to define mutually-recursive functions.

   * ~ilc[mv] and ~ilc[mv-let]:  allow functions to return ``multiple-values''.
   In Lisp, such functions return vectors of values, the vectors are represented as
   lists of values, but the implementations are generally more efficient.  For example,
   ~c[(mv x y z)] returns a ``vector'' consisting of the values of ~c[x], ~c[y], and ~c[z].
   ~bv[]
   (mv-let (a b c)
           (foo x)
           (bar a b c x))
   ~ev[]
   evaluates ~c[(foo x)], treats the result as a vector of three values, binds the variables
   ~c[a], ~c[b], and ~c[c] to those three values, and evaluates and returns ~c[(bar a b c x)].

   ACL2 also provides many other features, such as single-threaded objects which may be
   ``destructively modified'' (~pl[stobj] ~warn[], including a very special single-threaded
   object that records the ~ilc[state] ~warn[] of the ACL2 system), file input and output (~pl[io] ~warn[]),
   applicative arrays (~pl[arrays] ~warn[]) and property lists (~pl[getprop] ~warn[]) and other
   facilities necessary for it to be a practical programming language.  
   However, we ~b[strongly] recommend that as a new user you stay away from these features until
   you are good at proving theorems about elementary list processing!

   If this little drill made sense to you, you know enough of the programming
   language to get started. Use your browser's ~b[Back Button] now to return to
   ~il[introduction-to-the-theorem-prover].

   If you are uncomfortable with ACL2 programming, we recommend that you study
   ~url[http://www.cs.utexas.edu/users/moore/publications/gentle-intro-to-acl2-programming.html]
   and 
   ~url[http://www.cs.utexas.edu/users/moore/publications/acl2-programming-exercises1.html].

   However, we strongly recommend that you first invest in learning either
   the ~il[Emacs] or Eclipse-based ~il[ACL2-Sedan] program development environments,
   since it is foolish to try to learn how to program in a stand-alone read-eval-print
   loop!

   While getting started, many users find the Hyper-Card a handy index into the
   documentation for the ACL2 language:

   ~url[http://www.cs.utexas.edu/users/moore/publications/hyper-card.html]

   Once you are comfortable with the ACL2 programming language, use your
   browser's ~b[Back Button] to return to
   ~il[introduction-to-the-theorem-prover]. ~/~/")

(deflabel example-induction-scheme-nat-recursion
   :doc
   ":Doc-Section introduction-to-the-theorem-prover

   induction on natural numbers~/
   
   ~l[logic-knowledge-taken-for-granted-inductive-proof] for an explanation of
   what we mean by the induction ~i[suggested] by a recursive function or a
   term.

   ~b[Classical Induction on Natural Numbers]: Induction is familiar in the
   arithmetic setting.  To prove ~c[(p n)], for all ~c[n], by classical
   induction on the construction of the natural numbers, prove each of the
   following:
   
   ~bv[]
   ~i[Base Case]:
   (implies (zp n) (p n))
   ~ev[]
   
   ~bv[]
   ~i[Induction Step]:
   (implies (and (not (zp n))
                 (p (- n 1)))
            (p n))
   ~ev[]
   The Base Case establishes that ~c[p] holds for ~c[0].  In fact, because of
   the definition of ~ilc[zp] ~warn[], it establishes that ~c[(p n)] holds when
   ~c[n] is ~c[0] and it holds when ~c[n] is not a natural number.

   The Induction Step establishes that if ~c[n] is a natural number other than ~c[0],
   and if ~c[p] holds for ~c[n]-1, then ~c[p] holds for ~c[n].  The hypothesis
   ~c[(p (- n 1))] above is called the ~i[induction hypothesis].

   A function that suggests this induction is
   ~bv[]   
   (defun nat-recursion (n)
     (if (zp n)
         n
         (nat-recursion (- n 1))))
   ~ev[]
   Similarly, the term ~c[(fact n)] suggests this induction if ~c[fact]
   is defined:
   ~bv[]
    (defun fact (k)
     (if (zp k)
         1
         (* k (fact (- k 1))))).
   ~ev[]
   even though the formal parameter of this definition of ~c[fact] is ~c[k], not ~c[n].

   ~/~/")

(deflabel example-induction-scheme-down-by-2
   :doc
   ":Doc-Section introduction-to-the-theorem-prover

   induction downwards 2 steps at a time~/

   ~l[logic-knowledge-taken-for-granted-inductive-proof] for an explanation of
   what we mean by the induction ~i[suggested] by a recursive function or a
   term.

   ~b[Classical Induction on Natural Numbers Preserving Parity]: Here is
   another way to decompose natural numbers.  To prove ~c[(p n)], for all
   ~c[n], prove each of the following:
   
   ~bv[]
   ~i[Base Case 1]:
   (implies (zp n) (p n))
   ~ev[]
   
   ~bv[]
   ~i[Base Case 2]:
   (implies (equal n 1) (p n))
   ~ev[]

   ~bv[]
   ~i[Induction Step]:
   (implies (and (not (zp n))
                 (not (equal n 1))
                 (p (- n 2)))
            (p n))
   ~ev[]
   Base Case 1 establishes that ~c[p] holds for ~c[0] (and all objects other
   than positive naturals).

   Base Case 2 establishes that ~c[p] holds for ~c[1].

   The Induction Step establishes that if ~c[n] is a natural number greater than ~c[1],
   and if ~c[p] holds for ~c[n]-2, then ~c[p] holds for ~c[n].

   Note that we have thus proved that ~c[(p n)] holds, for all ~c[n].  For example,
   ~c[(p -7)], ~c[(p 'abc)], and ~c[(p 0)] are all established by Base Case 1.
   ~c[(p 1)] is established by Base Case 2.  ~c[(p 2)] is established from ~c[(p 0)]
   and the Induction Step.  Think about it!  ~c[(p 3)] is established form ~c[(p 1)]
   and the Induction Step, etc.

   A function that suggests this induction is:
   ~bv[]
   (defun parity (n)
     (if (zp n)
         'even
         (if (equal n 1)
             'odd
             (parity (- n 2))))).
   ~ev[]

   ~/~/")


(deflabel example-induction-scheme-on-lists
   :doc
   ":Doc-Section introduction-to-the-theorem-prover

   induction on lists~/

   ~l[logic-knowledge-taken-for-granted-inductive-proof] for an explanation of
   what we mean by the induction ~i[suggested] by a recursive function or a
   term.

   ~b[Classical Induction on Lists]: To prove ~c[(p x)], for all ~c[x], by
   classical induction on the linear list structure, prove each of the
   following:

   ~bv[]
   ~i[Base Case]:
   (implies (endp x) (p x))
   ~ev[]
   
   ~bv[]
   ~i[Induction Step]:
   (implies (and (not (endp x))
                 (p (cdr x)))
            (p x))
   ~ev[]

   An argument analogous to that given for natural numbers,
   ~il[example-induction-scheme-nat-recursion], establishes ~c[(p x)] for every
   ~c[x].  For example, ~c[(p -7)], ~c[(p 'abc)], and ~c[(p nil)] are all
   established by the Base Case.  ~c[(p '(Friday))] follows from ~c[(p nil)],
   given the Induction Step.  That sentence bears thinking about!  Think about
   it!  Similarly, ~c[(p '(Yellow))] holds for the same reason.
   ~c[(p '(Thursday Friday))] follows from ~c[(p '(Friday))] and the Induction Step,
   etc.

   A function that suggests this induction is
   ~bv[]
   (defun app (x y)
     (if (endp x)
         y
         (cons (car x) 
               (app (cdr x) y)))).
   ~ev[]

   ~/~/")


(deflabel example-induction-scheme-binary-trees
   :doc
   ":Doc-Section introduction-to-the-theorem-prover

   induction on binary trees~/

   ~l[logic-knowledge-taken-for-granted-inductive-proof] for an explanation of
   what we mean by the induction ~i[suggested] by a recursive function or a
   term.

   ~b[Classical Induction on Binary Trees]: To prove ~c[(p x)], for all ~c[x],
   by classical induction on binary tree structures, prove each of the
   following:

   ~bv[]
   ~i[Base Case]:
   (implies (atom x) (p x))
   ~ev[]
   
   ~bv[]
   ~i[Induction Step]:
   (implies (and (not (atom x))
                 (p (car x))
                 (p (cdr x)))
            (p x))
   ~ev[]

   An argument analogous to that given in ~il[example-induction-scheme-on-lists]
   should convince you that ~c[(p x)] holds for every object.

   A function that suggests this induction is:
   ~bv[]
   (defun flatten (x)
     (if (atom x)
         (list x)
         (app (flatten (car x))
              (flatten (cdr x))))).
   ~ev[]

   ~/~/")


(deflabel example-induction-scheme-on-several-variables
   :doc
   ":Doc-Section introduction-to-the-theorem-prover

   induction on several variables~/

   ~l[logic-knowledge-taken-for-granted-inductive-proof] for an explanation of
   what we mean by the induction ~i[suggested] by a recursive function or a
   term.

   ~b[Induction on Several Variables]  To ~c[(p n x)] for all ~c[n] and all ~c[x],
   prove each of the following:

   ~bv[]
   ~i[Base Case 1]:
   (implies (endp x)
            (p n x))
   ~ev[]

   ~bv[]
   ~i[Base Case 2]:
   (implies (and (not (endp x))
                 (zp n))
            (p n x))
   ~ev[]

   ~bv[]
   ~i[Induction Step]:
   (implies (and (not (endp x))
                 (not (zp n))
                 (p (- n 1) (cdr x)))
            (p n x))
   ~ev[]

   A function that suggests this induction is
   ~bv[]
   (defun nth (n x)
     (if (endp x)
         nil
         (if (zp n)
             (car x)
             (nth (- n 1) (cdr x))))).
   ~ev[]

   ~/~/")

(deflabel example-induction-scheme-upwards
   :doc
   ":Doc-Section introduction-to-the-theorem-prover

   induction upwards~/

   ~l[logic-knowledge-taken-for-granted-inductive-proof] for an explanation of
   what we mean by the induction ~i[suggested] by a recursive function or a
   term.

   ~b[Induction Upwards]:  To ~c[(p i max)] for all ~c[i] and all ~c[max],
   prove each of the following:

   ~bv[]
   ~i[Base Case]:
   (implies (not (and (natp i)
                      (natp max)
                      (< i max)))
            (p i max))
   ~ev[]

   ~bv[]
   ~i[Induction Step]:
   (implies (and  (natp i)
                  (natp max)
                  (< i max)
                  (p (+ i 1) max))
            (p i max))
   ~ev[]
   Note that the induction hypothesis is about an ~c[i] that is ~i[bigger] than
   the ~c[i] in in the conclusion.  In induction, as in recursion, the sense of
   one thing being ``smaller'' than another is determined by an arbitrary
   measure of all the variables, not the magnitude or extent of some particular
   variable.

   A function that suggests this induction is shown below.  ACL2 has to be told
   the measure, namely the difference between ~c[max] and ~c[i] (coerced to a natural
   number to insure that the measure is an ordinal).
   ~bv[]
   (defun count-up (i max)
     (declare (xargs :measure (nfix (- max i))))
     (if (and (natp i)
              (natp max)
              (< i max))
         (cons i (count-up (+ 1 i) max))
         nil)).
   ~ev[]

   ~/~/")


(deflabel example-induction-scheme-with-accumulators
   :doc
   ":Doc-Section introduction-to-the-theorem-prover

   induction scheme with accumulators~/

   ~l[logic-knowledge-taken-for-granted-inductive-proof] for an explanation of
   what we mean by the induction ~i[suggested] by a recursive function or a
   term.

   To prove ~c[(p x a)] for all ~c[x] and all ~c[a], prove each of the following:

   ~bv[]
   ~i[Base Case]:
   (implies (endp x)
            (p x a))
   ~ev[]
   
   ~bv[]
   ~i[Induction Step]:
   (implies (and (not (endp x))
                 (p (cdr x) (cons (car x) a)))
            (p x a))
   ~ev[]
   Note that in the induction hypothesis we assume ~c[p] for a smaller ~c[x] but
   a larger ~c[a].  In fact, we could include as many induction hypotheses as we
   want and use any terms we want in the ~c[a] position as long as the ~c[x]
   position is occupied by a smaller term.

   A function that suggests this particular induction is shown below.
   ~bv[]
   (defun rev1 (x a)
     (if (endp x)
         a
         (rev1 (cdr x) (cons (car x) a)))).
   ~ev[]

   A function that suggests a similar induction in which three induction hypotheses are
   provided, one in which the ~c[a] position is occupied by ~c[(cons (car x) a)],
   another in which the ~c[a] position is occupied by some arbitrary term ~c[b],
   and a third in which the ~c[a] position is occupied by ~c[a], is suggested by
   the term ~c[(rev1-modified x a b)] where
   ~bv[]
   (defun rev1-modified (x a b)
     (if (endp x)
         (list x a b)
         (list (rev1-modified (cdr x) (cons (car x) a) b)
               (rev1-modified (cdr x) b b)
               (rev1-modified (cdr x) a b))))
   ~ev[]
   Remember that the value of this term or function is irrelevant to the induction
   suggested.  Because ACL2's definitional principle insists that all the formal
   parameters play a role in the computation (at least syntactically), it is common
   practice when defining functions for their induction schemes to return the
   ~c[list] of all the formals (to insure all variables are involved) and to combine
   recursive calls on a given branch with ~c[list] (to avoid introducing additional
   case analysis as would happen if ~c[and] or ~c[or] or other propositional functions
   are used).

   If you tried to prove ~c[(p x a)] and suggested the induct hint 
   ~c[(rev1-modified x a (fact k))], as by
   ~bv[]
   (thm (p x a)
        :hints ((\"Goal\" :induct (rev1-modified x a (fact k)))))
   ~ev[]
   the inductive argument would be:
   ~bv[]
   ~i[Base Case]:
   (implies (endp x)
            (p x a))
   ~ev[]

    ~bv[]
    ~i[Inductive Step]:
    (implies (and (not (endp x))
                  (p (cdr x) (cons (car x) a))
                  (p (cdr x) (fact k))
                  (p (cdr x) a))
             (p x a))
    ~ev[]

    ~/~/")

(deflabel example-induction-scheme-with-multiple-induction-steps
   :doc
   ":Doc-Section introduction-to-the-theorem-prover

   induction scheme with more than one induction step~/

   ~l[logic-knowledge-taken-for-granted-inductive-proof] for an explanation of
   what we mean by the induction ~i[suggested] by a recursive function or a
   term.

   ~b[Several Induction Steps]:  To ~c[(p x i a)] for all
   ~c[x], ~c[i], and ~c[a], prove each of the following:

   ~bv[]
   ~i[Base Case 1]:
   (implies (zp i)
            (p x i a))
   ~ev[]

   ~bv[]
   ~i[Induction Step 1]:
   (implies (and (not (zp i))
                 (equal (parity i) 'even)
                 (p (* x x)
                    (floor i 2)
                    a))
            (p x i a))
   ~ev[]

   ~bv[]
   ~i[Induction Step 2]:
   (implies (and (not (zp i))
                 (not (equal (parity i) 'even))
                 (p x
                    (- i 1)
                    (* x a)))
            (p x i a))
   ~ev[]

   A function that suggests this induction is the binary
   exponentiation function for natural numbers.
   ~bv[]
   (defun bexpt (x i a)
     (cond ((zp i) a)
           ((equal (parity i) 'even)
            (bexpt (* x x)
                   (floor i 2)
                   a))
           (t (bexpt x
                     (- i 1)
                     (* x a)
                     )))).
   ~ev[]
   In order to admit this function it is necessary to know that
   ~c[(floor i 2)] is smaller than ~c[i] in the case above.  This can be
   proved if the book ~c[\"arithmetic-5/top\"] has been included from
   the ACL2 system directory, i.e.,
   ~bv[]
   (include-book \"arithmetic-5/top\" :dir :system)
   ~ev[]
   should be executed before defining ~c[bexpt].

   ~/~/")

(deflabel example-inductions
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   some examples of induction schemes in ACL2~/

   Here are some pages illustrating various induction
   schemes suggested by recursive functions.

   ~b[Classical Induction on Natural Numbers]:
   ~pl[example-induction-scheme-nat-recursion].

   ~b[Induction Preserving Even/Odd Parity] or~nl[]
   ~b[Induction Downwards by 2] or ~nl[]
   ~b[Induction with Multiple Base Cases]:
   ~pl[example-induction-scheme-down-by-2] for an induction in which the
   induction hypothesis decreases the induction variable by an amount other
   than 1.  This illustrates that the induction hypothesis can be about
   whatever term or terms are needed to explain how the formula recurs.  The
   example also illustrates an induction with more than one Base Case.

   ~b[Classical Induction on Lists]:
   ~pl[example-induction-scheme-on-lists] for an induction over linear lists,
   in which we inductively assume the conjecture for ~c[(cdr x)] and prove it
   for ~c[x].  It doesn't matter whether the list is ~c[nil]-terminated or not;
   the Base Case addresses all the possibilities.

   ~b[Classical Induction on Binary (Cons) Trees]:
   ~pl[example-induction-scheme-binary-trees] for an induction over the simplest
   form of binary tree.  Here the Induction Step provides two hypotheses, one
   about the left subtree and one about the right subtree.

   ~b[Induction on Several Variables]:
   ~pl[example-induction-scheme-on-several-variables] for an induction in which
   several variables participate in the case analysis and induction hypotheses.

   ~b[Induction Upwards]:
   ~pl[example-induction-scheme-upwards] for an induction scheme in which
   the induction hypothesis is about something ``bigger than'' the induction conclusion.
   This illustrates that the sense in which the hypothesis is about something ``smaller''
   than the conclusion is determined by a measure of all the variables, not the magnitude
   or extent of some single variable.

   ~b[Induction with Auxiliary Variables] or~nl[]
   ~b[Induction with Accumulators]:
   ~pl[example-induction-scheme-with-accumulators] for an induction scheme in which
   one variable ``gets smaller'' but another is completely arbitrary.  Such schemes
   are common when dealing with tail-recursive functions that accumulate partial
   results in auxiliary variables.  This example also shows how to provide
   several arbitrary terms in a non-inductive variable of a scheme.

   ~b[Induction with Multiple Induction Steps]:
   ~pl[example-induction-scheme-with-multiple-induction-steps] for an induction in
   which we make different inductive hypotheses depending on which case we're in.
   This example also illustrates the handling of auxiliary variables or
   accumulators.

   ~/~/")

(deflabel logic-knowledge-taken-for-granted-inductive-proof
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   a brief explanation of induction~/

   We start by showing classical induction on the natural numbers in an ACL2
   setting before turning to a more general treatment of induction.

   ~b[Classical Induction on Natural Numbers]: Induction is familiar in the
   arithmetic setting.  Let ~c[(p n)] denote some formula involving the variable ~c[n]
   (and perhaps some other variables which we don't exhibit).  Then to prove
   ~c[(p n)], for all ~c[n], by classical induction on the construction of the
   natural numbers, prove each of the following:
   
   ~bv[]
   ~i[Base Case]:
   (implies (zp n) (p n))
   ~ev[]
   
   ~bv[]
   ~i[Induction Step]:
   (implies (and (not (zp n))
                 (p (- n 1)))
            (p n))
   ~ev[]
   The Base Case establishes that ~c[p] holds for ~c[0].  In fact, because of
   the definition of ~ilc[zp] ~warn[], it establishes that ~c[(p n)] holds when
   ~c[n] is ~c[0] and it holds when ~c[n] is not a natural number.

   The Induction Step establishes that if ~c[n] is a natural number other than ~c[0],
   and if ~c[p] holds for ~c[n]-1, then ~c[p] holds for ~c[n].  The hypothesis
   ~c[(p (- n 1))] above is called the ~i[induction hypothesis].

   Note that if the Base Case and Induction Step are valid, then we know ~c[(p n)],
   for all ~c[n].  You can convince yourself of this by picking any object
   and asking ``how do I know ~c[p] holds for this object?''  For example,
   ~c[(p -7)], ~c[(p 'abc)], and ~c[(p 0)] are all established by the Base
   Case.  What about ~c[(p 1)]?  That follows from ~c[(p 0)], given the
   Induction Step.  Why?  To prove ~c[(p 1)] using the Induction Step, you have
   to establish ~c[(not (zp 1))], which is true, and ~c[(p (- 1 1))], which is
   ~c[(p 0)], which is true by the Base Case.  So ~c[(p 1)] is true.  Similar
   reasoning proves ~c[(p 2)] from from ~c[(p 1)], etc.  Clearly, for every
   natural number other than ~c[0] we could reason like this to show that ~c[p]
   holds.  Since the Base Case handled all the objects that are not natural
   numbers, and handled ~c[0], we know ~c[(p n)], for all ~c[n].

   There is a duality between recursion and induction that ACL2 exploits.  The fact
   that the Base and Induction steps above are sufficient to prove ~c[p] for all
   objects is related to the fact that the following recursion defines a total,
   terminating function:
   ~bv[]   
   (defun nat-recursion (n)
     (if (zp n)
         n
         (nat-recursion (- n 1))))
   ~ev[]
   
   When this function is admitted we have to prove that if ~c[(zp n)] does not
   hold, then ~c[(- n 1)] is smaller, in some sense, than ~c[n].  This sense of ``smaller''
   is determined by some ~i[measure] of the arguments.  That measure must return an
   ordinal (~il[ordinals] ~warn[]), but the most common measures return natural numbers,
   which are among the ordinals.  Furthermore, that measure should insure that the
   terms in the recursive calls are smaller than the formals, i.e., the measure of ~c[(- n 1)] must be
   smaller than the measure of ~c[n], when the recursive branches are taken.  This sense of
   ``smaller'' must be ~i[well-founded]:  it must be impossible to have an infinitely
   descending chain of smaller things.  This is true of the less-than relation on
   the ordinals (see ~ilc[o<] ~warn[]).  Well-foundedness means that eventually any
   recursion must ``bottom out'' because things can't keep getting smaller forever.

   The recursion in ~c[nat-recursion] ~b[suggests] the induction shown above:
   the Base Case is defined by the ~c[if] branch that does not lead to a
   recursive call.  The Induction Step is defined by the other branch.  The
   induction hypothesis is defined by what we recur on, i.e., ~c[(- n 1)].  The
   theorems proved when ~c[nat-recursion] is introduced ~i[justify] the
   classical induction scheme noted above.

   Every recursively defined ACL2 function suggests a legal induction and vice versa.

   Furthermore, every call of a recursively defined function on distinct variable symbols
   also suggests a legal induction:  just take the induction suggested by the function's
   recursive definition after renaming the formal parameters to be the variables in the call.

   For example, it should be clear that ~c[(nat-recursion a)] suggests a Base
   Case defined by ~c[(zp a)], and induction step defined by ~c[(not (zp a))]
   and an induction hypothesis about ~c[(- a 1)].

   Note that the term ~c[(fact n)] suggests the same classical induction on
   natural numbers shown above, where ~c[fact] is defined as follows (even though
   we've used the formal parameter ~c[k] below).
   ~bv[]
   (defun fact (k)
     (if (zp k)
         1
         (* k (fact (- k 1)))))
   ~ev[]
   The induction suggested by a term like ~c[(fact n)] is insensitive to the
   name of the formal parameter used in the ~c[defun].

   The induction suggested by a function or term is insensitive to the value
   returned by the function or term.

   It doesn't matter what the function returns in its ``base case'' (e.g.,
   ~c[1] in ~c[fact]) or what the function ``does'' to its recursive
   call (e.g., multiply by ~c[k] in the ~c[defun] of ~c[fact]).

   All that matters is (i) how the ~c[if] structure breaks down the cases on
   ~c[k], (ii) which branches lead to recursion, and (iii) what arguments are
   passed to the recursive calls.  Those things determine (i) the case analysis
   of the induction scheme, (ii) which cases are Base Cases and which are
   Induction Steps, and (iii) what the induction hypotheses are.

   For a selection of common inductions schemes in ACL2 (e.g., on the structure of
   natural numbers, lists, and trees and on several variables at once, multiple
   base cases, multiple induction hypotheses, multiple induction steps, etc.)
   ~il[example-inductions check this link].

   Every legal ACL2 induction corresponds to an admissible recursive function
   and vice versa.  Similarly, every legal ACL2 induction corresponds to a
   call of a recursively defined function on distinct variables.

   ACL2 chooses which induction to do by looking at the terms that occur in the
   conjecture.  For many elementary theorems, ACL2 chooses the right induction
   by itself.

   You may occasionally need to tell it what induction to do.  You do that by
   showing it a term that suggests the induction you want.  We'll explain how
   you communicate this to ACL2 later.  If you understand how recursive
   functions suggest inductions, then you know what you need to know to use
   ACL2.

   The main point of this discussion of induction is familiarize you with the
   basic terms:  ~i[Base Case] (of which there may be several), ~i[Induction Step]
   (of which there may be several), ~i[Induction Hypothesis] (of which there
   may be several in each Induction Step), ~i[measure] and ~i[well-founded relation]
   ~i[justifying] an induction, and the induction ~i[suggested] by a
   term or recursive function definition.  Furthermore, every Induction
   Hypothesis is always an
   ~il[logic-knowledge-taken-for-granted-instance instance]
   of the conjecture being proved: each induction hypothesis is obtained
   from the conjecture being proved by applying a ~i[substitution] replacing
   variables by terms.

   If you are reviewing the material taken for granted about logic while
   working your way through the introduction to the theorem prover, please use
   your browser's ~b[Back Button] to return to the example proof in
   ~il[logic-knowledge-taken-for-granted].

   ~/~/")

(deflabel logic-knowledge-taken-for-granted-base-case
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   a brief explanation of base cases~/

   According to the sentence, the conjecture being proved is
   ``reversing the reverse of a ~c[true-listp] yields the original list.''
   The formula corresponding to this conjecture is:
   ~bv[]
   (implies (true-listp z)
            (equal (rev (rev z)) z)).
   ~ev[]
   We're also told that this is an inductive proof.  Evidently we're doing an
   induction on the structure of the list ~c[z].  Then the
   ~i[Base Case] is the formula:
   ~bv[]
   (implies (endp z)
            (implies (true-listp z)
                     (equal (rev (rev z)) z))).
   ~ev[]

   Now use your browser's ~b[Back Button] to return to the example proof
   in ~il[logic-knowledge-taken-for-granted].

   ~/~/")

(deflabel logic-knowledge-taken-for-granted-q1-answer
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   the inductive step of the ~c[rev-rev] proof -- Answer to Question 1~/

   The correct answer to Question 1 in
   ~il[logic-knowledge-taken-for-granted] is ~i[Choice (iv)].

   The Induction Step of the inductive proof of
   ~bv[]
   (implies (true-listp z)
            (equal (rev (rev z)) z))
   ~ev[]
   for an induction on the linear list ~c[z] is:
   ~bv[]
   ~i[Induction Step]:
   (implies (and (not (endp z))
                 (implies (true-listp (cdr z))
                          (equal (rev (rev (cdr z))) (cdr z))))
            (implies (true-listp z)
                     (equal (rev (rev z)) z)))
   ~ev[]
   The second hypothesis above is the the ~i[induction hypothesis].  The
   conclusion above is the formula we are trying to prove.  Each induction
   hypothesis is ~i[always] an ~il[logic-knowledge-taken-for-granted-instance instance]
   of the formula being proved, i.e., it is obtained from the formula
   being proved by uniformly replacing the variables in the formula with terms.
   Notice how the induction hypothesis above is the same as the induction
   conclusion, except that all the ~c[z]s have been replaced by ~c[(cdr z)].

   If you thought the right answer was
   ~bv[]
   ~i[Induction Step -- Choice (i)]:
   (implies (not (endp z))
            (implies (true-listp z)
                     (equal (rev (rev z)) z)))
   ~ev[]
   then perhaps you didn't understand that we're doing an inductive proof.
   Certainly if you prove the Base Case already discussed and you prove
   ~i[Choice (i)] above, then you will have proved the goal conjecture, but you
   would have done it by simple case analysis:  prove it when ~c[(endp z)] and
   prove it when ~c[(not (endp z))].  While logically valid, you probably can't
   prove ~i[Choice (i)] directly because you have no induction hypothesis to work 
   with.

   If you thought the right answer was:
   ~bv[]
   ~i[Induction Step -- Choice (ii)]:   
   (implies (true-listp (cdr z))
            (equal (rev (rev (cdr z))) (cdr z)))
   ~ev[]
   then perhaps you misunderstand the difference between the ~i[Induction Step]
   and the ~i[Induction Hypothesis].  The Induction ~i[Step] is the ``other half''
   of the main proof, balancing the Base Case.  The Induction ~i[Hypothesis] is
   just a hypothesis you get to use during the Induction Step.  The question Q1 asked
   what is the Induction Step.

   If you thought the right answer was:
   ~bv[]
   ~i[Induction Step -- Choice (iii)]:   
   (implies (and (not (endp z))
                 (equal (rev (rev (cdr x))) (cdr x))) ; ~i[``induction hyp'']
            (implies (true-listp z)
                     (equal (rev (rev z)) z)))
   ~ev[]
   then you are making the most common mistake newcomers make to induction.  You
   are giving yourself an ``induction hypothesis'' that is not an instance of the
   conjecture you're proving.  This alleged induction hypothesis says that ~c[(rev (rev (cdr x)))]
   is ~c[(cdr x)], whereas the correct induction hypothesis says those two terms are
   equal ~i[if] ~c[(true-listp (cdr x))].  This alleged induction hypothesis is a stronger
   claim than we're trying to prove.  It turns out that by making this mistake you can
   ``prove'' conjectures that are not always true!  Remember:  the induction hypothesis
   is always an instance of the conjecture you're proving, not just some piece of it.
   Of course, ACL2 ``knows'' this and will never make this mistake.  But we remind you of
   it because there may be times when you intuit a different hypothesis and don't understand
   why ACL2 doesn't use it.

   If this doesn't make sense, perhaps you should read about
   ~il[logic-knowledge-taken-for-granted-inductive-proof induction] again.

   When you understand why ~i[Choice (iv)] is the correct answer, 
   use your browser's ~b[Back Button] to return to
   ~il[logic-knowledge-taken-for-granted] and go to question Q2.
   ~/~/")

(deflabel logic-knowledge-taken-for-granted-q2-answer
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   the inductive step of the ~c[rev-rev] proof -- Answer to Question 2~/

   The correct answer to Question 2 in
   ~il[logic-knowledge-taken-for-granted] is ~i[Subgoal (i)]
   plus any one of the other other three.  For your reference, the
   four choices were:
   ~bv[]
   ~i[Subgoal (i)]:
   (implies (and (not (endp z))
                 (true-listp z))
            (true-listp (cdr z)))

   ~i[Subgoal (ii)]:
   (implies (and (not (endp z))
                 (true-listp z)
                 (equal (rev (rev (cdr z))) (cdr z)))
            (equal (rev (rev z)) z))

   ~i[Subgoal (iii)]:
   (implies (and (not (endp z))
                 (equal (rev (rev (cdr z))) (cdr z)))
            (equal (rev (rev z)) z))

   ~i[Subgoal (iv)]:
   (implies (and (not (endp z))
                 (true-listp (cdr z))
                 (equal (rev (rev (cdr z))) (cdr z)))
            (equal (rev (rev z)) z))
   ~ev[]

   In particular, it is wrong to think the Induction Step of
   the proof of
   ~bv[]
   (implies (true-listp z)
            (equal (rev (rev z)) z))
   ~ev[]
   can be established by proving just ~i[Subgoal (ii)],
   ~i[Subgoal (iii)], ~i[Subgoal (iv)], or combinations of
   those three.  You must also prove ~i[Subgoal (i)] or something
   like it!

   The Inductive Step for the conjecture above is
   ~bv[]
   ~i[Induction Step]:
   (implies (and (not (endp z))
                 ; ~i[Induction Hypothesis]:
                 (implies (true-listp (cdr z))
                          (equal (rev (rev (cdr z))) (cdr z))))
            ; ~i[Induction Conclusion]:
            (implies (true-listp z)
                     (equal (rev (rev z)) z)))
   ~ev[]
   Note that the Inductive Hypothesis is an implication:
   ~bv[]
   (implies (true-listp (cdr z))
            (equal (rev (rev (cdr z))) (cdr z)))
   ~ev[]
   This hypothesis can be true two different ways.  The ``normal'' way -- the
   way everybody remembers -- is that ~c[(true-listp (cdr z))] is true and thus
   ~c[(equal (rev (rev (cdr z))) (cdr z))] is true.  But the way many people
   forget is that ~c[(true-listp (cdr z))] is false.  You must prove the
   Induction Step even in this ``forgetable'' case.

   In this case, the Induction Step simplifies to
   ~bv[]
   ~i[Induction Step]:
   (implies (and (not (endp z))
                 (not (true-listp (cdr z))))
            (implies (true-listp z)
                     (equal (rev (rev z)) z)))
   ~ev[]
   By Promotion (see the list of tautologies in our discussion of
   ~il[logic-knowledge-taken-for-granted-propositional-calculus propositional calculus])
   this is
   ~bv[]
   ~i[Induction Step']:
   (implies (and (not (endp z))
                 (not (true-listp (cdr z)))
                 (true-listp z))
            (equal (rev (rev z)) z))
   ~ev[]
   Using the Contrapositive and rearranging the order of the hypotheses (see 
   ~il[logic-knowledge-taken-for-granted-propositional-calculus propositional calculus]
   again), this is
   ~bv[]
   ~i[Induction Step'']:
   (implies (and (not (endp z))
                 (true-listp z)
                 (not (equal (rev (rev z)) z)))
            (true-listp (cdr z)))
   ~ev[]
   Notice that ~i[Subgoal (i)] implies ~i[Induction Step'']:
   ~bv[]
   ~i[Subgoal (i)]:
   (implies (and (not (endp z))
                 (truelistp z))
            (truelistp (cdr z)))
   ~ev[]

   Every inductive proof of an implication raises a case like this.
   If we denote the conjecture ~c[(implies p q)] as ~c[p ---> q], then
   the Induction Step will look like this:
   ~bv[]
     ( c  &  (p'  --->  q')) 
   --->
     (p ---> q)
   ~ev[]
   where ~c[c] is the test that determines the inductive step, (e.g., ~c[(not (endp z))])
   and ~c[p'] and ~c[q'] are inductive instances of ~c[p] and ~c[q].  Promotion produces
   ~bv[]
     ( c  & p & (p'  --->  q')) 
   --->
     q
   ~ev[]
   It is then very common to prove that ~c[p] implies ~c[p'],
   ~bv[]
   ~i[(i)]:
   (c & p) ---> p'
   ~ev[]
   and then prove that ~c[q'] implies ~c[q],
   ~bv[]
   ~i[(ii)]:
   (c & p & q') ---> q
   ~ev[]
   These correspond exactly to our choices ~i[Subgoal (i)] and ~i[Subgoal (ii)].

   It is sometimes helpful to remember this diagram:
   ~bv[]
   (c  &  (p'  --->  q')
           ^         |
           |         |
           |         v
    -->   (p   --->  q )
   ~ev[]
   
   When you understand why ~i[Subgoals (i)] and ~i[(ii)] are sufficient,
   use your browser's ~b[Back Button] to return to
   ~il[logic-knowledge-taken-for-granted] and go to question Q3.
   ~/~/")

(deflabel logic-knowledge-taken-for-granted-q3-answer
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   the inductive step of the ~c[rev-rev] proof -- Answer to Question 2~/

   The correct answer to Question 3 in
   ~il[logic-knowledge-taken-for-granted] is that you need to prove
   ~bv[]
   ~i[Subgoal to Relieve Hyp 1]:
   (implies (and (q (f a))
                 (r a))
            (p (f a)))
   ~ev[]
   in order to use
   ~bv[]
   ~i[Theorem]:
   (implies (p (f x))
            (equal (g (h x))
                   x))
   ~ev[]
   to rewrite the target ~c[(g (h a))] to ~c[a] in
   ~bv[]
   ~i[Goal Conjecture]:
   (implies (and (q (f a))
                 (r a))
            (s (g (h a))))
   ~ev[]

   If you don't see why, re-read the discussion of 
   ~il[logic-knowledge-taken-for-granted-rewriting rewriting]
   again.  Forgetting about the need to relieve hypotheses is a
   common mistake in informal proofs.  ACL2 won't forget to relieve
   them.  But if you forget about the need to do it, you may be
   confused when ACL2 doesn't see the ``proof'' you see!

   Now use your browser's ~b[Back Button] to return to the end of quiz in
   ~il[logic-knowledge-taken-for-granted].
   ~/~/")


(deflabel logic-knowledge-taken-for-granted-instance
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   a brief explanation of substitution instances~/

   Let ~i[p] and ~i[q] be terms or formulas (there is no difference in ACL2).
   Then we say ~i[p] is an ~i[instance] or ~i[substitution instance]
   of ~i[q] if and only if ~i[p] can be obtained from ~i[q] by uniformly
   replacing the variables of ~i[q] by terms.  Sometimes we call ~i[p] the
   ~i[target] and ~i[q]
   the ~i[pattern] because by choosing appropriate replacements we can make
   the pattern ~i[match] many different targets.

   For example, the following ~i[target] is an instance of the given ~i[pattern]:
   ~bv[]
   ~i[target]:      (APP (APP (REV A) (REV B)) (REV C))
   ~i[pattern]:     (APP (APP   x       y    ) (REV z))
   ~ev[]

   The replacement or ~i[substitution] used in this match of the pattern to the
   target is:
   ~bv[]
   ~i[variable in pattern]          ~i[replacement term]
   x                              (REV A) 
   y                              (REV B)
   z                              C
   ~ev[]
   Such substitutions are usually written this way in ACL2:
   ~bv[]
   ((x  (REV A))
    (y  (REV B))
    (z  C)).
   ~ev[]

   Please use your browser's ~b[Back Button] to return to the page that mentioned
   ``instance.''

   ~/~/")

(deflabel logic-knowledge-taken-for-granted-propositional-calculus
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   a brief explanation of propositional calculus~/

   It is impossible in this short introduction to teach you propositional
   calculus if you don't already know it!

   A typical use of propositional calculus is to observe that
   ~bv[]
   (implies (endp z)
            (implies (true-listp z)
                     (equal (rev (rev z)) z)))   
   ~ev[]
   is equivalent to:
   ~bv[]
    (implies (and (endp z)
                  (true-listp z))
             (equal (rev (rev z)) z))
   ~ev[]
 
   If this is surprising and you know propositional calculus, then the
   problem might be our notation.  We're exploiting the tautology
   ~bv[]
   ~i[(p ---> (q ---> r)) <---> ((p & q) ---> r)]
   ~ev[]
   where ~i[--->] and ~i[<--->] are meant to be the traditional arrows
   denoting logical implication and logical equivalence.

   If you don't know propositional calculus, we'll say just a few things
   to help ease your journey.

   A ~i[propositional formula], in ACL2, is any formula
   written entirely in terms of variable symbols, ~c[T], ~c[NIL], and
   the propositional functions ~c[AND], ~c[OR], ~c[NOT], ~c[IMPLIES], and
   ~c[IFF].  The ``tautology'' above in traditional notation is this
   propositional formula in ACL2:
   ~bv[]
   (IFF (IMPLIES P (IMPLIES Q R))
        (IMPLIES (AND P Q) R)).
   ~ev[]

   If you have a formula like
   ~bv[]
   (implies ~i[hyp]
            ~i[concl])
   ~ev[]
   then we say that formula is an ~i[implication], that ~i[hyp] is the ~i[hypothesis], and
   that ~i[concl] is the conclusion.  If the hypothesis is an ~c[and] expression, as in
   ~bv[]   
   (implies (and ~i[hyp1]
                 ~i[hyp2]
                 ...)
            ~i[concl])
   ~ev[]
   then we call ~i[hyp1] is the ~i[first hypothesis],
   ~i[hyp2] is the ~i[second hypothesis], etc.

   If a term is of the form
   ~bv[]
   (and ~i[term1] ~i[term2] ...)
   ~ev[]
   we say it is a ~i[conjunction] and that ~i[term1] is the ~i[first conjunct], ~i[term2] is
   the ~i[second conjunct], etc.  We treat an ~c[or]-term analogously but call it a
   ~i[disjunction] and its arguments are ~i[disjuncts].

   A ~i[tautology] is any propositional formula that can be proved by testing it
   under all combinations of Boolean assignments to its variables.  We give an
   example of such a ~i[truth-table proof] below, but hasten to add that ACL2
   does not generally use truth tables to recognize tautologies.  It primarily uses
   ~c[IF]-normalization and BDDs to recognize tautologies, which can be seen as a
   mix of symbolic manipulation and case analysis.

   Many tautologies have names, but ACL2 doesn't refer to them by name because it
   derives them from first principles.  We list a few here because we sometimes use
   the names in our documentation; more importantly, you should look at these
   formulas and convince yourself that they're always true for all Boolean values
   of the variables:
   ~bv[]
   ~i[Double Negation]:
   (iff (not (not p)) p)

   ~i[DeMorgan]:
   (iff (not (and p q))
        (or (not p) (not q)))

   ~i[Distributivity]:
   (iff (and p (or q r))
        (or (and p q)
            (and p r)))   

   ~i[Promotion]:
   (iff (implies p (implies q r))
        (implies (and p q) r))

   ~i[Implicative Disjunction]:
   (iff (implies p q)
        (or (not p) q))

   ~i[Contrapositive]:
   (iff (implies p q)
        (implies (not q) (not p)))

   ~i[Generalized Contrapositive]:
   (iff (implies (and p r) q)
        (implies (and p (not q)) (not r)))

   ~ev[]
   There are, of course, many others, even with these same names!  For example, there is a
   dual version of DeMorgan showing how ~c[not] distributes over ~c[or], a dual version of
   Distributivity for ~c[or] over ~c[and], etc.  

   Dealing with propositional calculus will not generally be a problem for you because
   it is decidable and ACL2 has procedures that decide propositional formulas.  However,
   propositional calculus can lead to exponential explosion and can thus explain why
   ACL2 has ``gone out to lunch.''  In addition, sometimes if you are curious as to
   ~i[why] ACL2 is working on a certain subgoal the reason can be traced back to 
   propositional calculus.

   The most common example of this is that to prove a formula of the form
   ~bv[]
   (implies (implies p1 q1)
            (implies p2 q2))
   ~ev[]
   propositional calculus will convert it to
   ~bv[]
   (and (implies (and p2 (not p1)) q2)
        (implies (and p2 q1) q2))
   ~ev[]
   Many users are surprised that the first conjunct above does not have ~c[q1] as a
   hypothesis.  If you ever stare at an ACL2 goal and say to yourself ``A hypothesis is
   missing!'' the chances are that propositional calculus is ``to blame.''
   In particular, if you are trying to prove that ~c[(implies p1 q1)] implies something,
   you must deal with the case that ~c[(implies p1 q1)] is true because ~c[p1] is false.
   Think about it.

   Now we illustrate the truth table method for deciding tautologies, even though that
   is not what ACL2 generally uses.
   Consider the formula called Promotion above:
   ~bv[]
   (IFF (IMPLIES P (IMPLIES Q R))
        (IMPLIES (AND P Q) R))
   ~ev[]

   The formula above is a tautology.  It contains three variables, ~c[P], ~c[Q],
   and ~c[R], and so there are 8 combinations of Boolean assignments to them.
   If we let
   ~bv[]
   ~i[formula1]:  (IMPLIES P (IMPLIES Q R))
   ~i[formula2]:  (IMPLIES (AND P Q) R)
   ~ev[]
   then we wish to test the formula ~c[(IFF ]~i[formula1 formula2]~c[)]:
   ~bv[]
   P   Q   R       ~i[formula1]   ~i[formula2]   (IFF ~i[formula1] ~i[formula2])
   ---------
   T   T   T            T         T       T
   T   T   NIL          NIL       NIL     T
   T   NIL T            T         T       T
   T   NIL NIL          T         T       T
   NIL T   T            T         T       T
   NIL T   NIL          T         T       T
   NIL NIL T            T         T       T
   NIL NIL NIL          T         T       T
   ~ev[]
   So we see that the formula always returns ~c[T] and is thus a tautology.

   Recall that in the original example at the top of this page we were trying
   to prove the formula
   ~bv[]
   (implies (endp z)
            (implies (true-listp z)
                     (equal (rev (rev z)) z)))   
   ~ev[]
   This formula is an ~il[logic-knowledge-taken-for-granted-instance instance] of
   ~bv[]
   (implies p (implies q r)).
   ~ev[]
   The substitution required by the match is
   ~bv[]
   ~i[sigma]:
   ((p    (endp z))
    (q    (true-listp z))
    (r    (equal (rev (rev z)) z)))
   ~ev[]

   Since we know the tautology:
   ~bv[]
   (iff (implies p (implies q r))
        (implies (and p q) r)).
   ~ev[]
   is always true no matter what Boolean values ~c[p], ~c[q], and ~c[r] have,
   then we know this instance of it (obtained by applying the substitution ~i[sigma] above)
   is always true:
   ~bv[]
   (iff (implies (endp z)                            ~i[formula1']
                 (implies (true-listp z)
                          (equal (rev (rev z)) z)))
        (implies (and (endp z)                       ~i[formula2']
                      (true-listp z))
                 (equal (rev (rev z)) z))).
   ~ev[]
   Thus, if we're trying to prove ~i[formula1'] it is permitted to try to
   to prove ~i[formula2'] instead, because they return the same truthvalue.

   This sketch of propositional reasoning in ACL2 is a little suspect because
   we didn't address the possibility that the substitution might replace the
   propositional variables by non-propositional terms.  But the tautology was
   verified only on Boolean values for those variables.  This actually 
   works out because in ACL2 all propositional testing is done against ~c[nil]
   and any non-~c[nil] value, including ~c[t], is as good as another.  However,
   the tautology allows us to replace one formula by the other only in contexts
   in which we just care about propositional truth, i.e., whether the formula
   is ~c[nil] or not.  When we prove a formula in ACL2 we are really
   establishing that it never returns ~c[nil], i.e., no matter what the values
   of the variables, the value of the formula is non-~c[nil].

   A very simple example of this is with Double Negation.  
   ~bv[]
   (iff (not (not p)) p)
   ~ev[]
   is a tautology.  This means that if we were trying to prove
   ~bv[]
   (implies (not (not p)) ...)
   ~ev[]
   we could transform it to
   ~bv[]
   (implies p ...).
   ~ev[]
   But if we were trying to prove:
   ~bv[]
   (equal (not (not p)) p)
   ~ev[]
   we could not prove it by using Double Negation!  The formula above
   claims that ~c[(not (not p))] and ~c[p] have identical values.  
   They do not!  For example, ~c[(not (not 3))] is ~c[t], not ~c[3].
   However, ~c[(not (not 3))] and ~c[t] are propositionally equivalent (i.e.,
   satisfy ~c[iff]) because one is as good as the other in a test.
   ~i[That] is what Double Negation says.

   As long as you only use propositional formulas in propositional places
   this aspect of ACL2 should not affect you.

   Now please use your browser's ~b[Back Button] to return to the 
   example proof in ~il[logic-knowledge-taken-for-granted].

   ~/~/")

(deflabel logic-knowledge-taken-for-granted-rewriting
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   a brief explanation of rewriting from the logical perspective~/

   First we give two examples of rewriting.  Then we give a rather detailed
   description.  We recommend you read the description, even if you understand
   the two examples, just so that you learn our terminology.

   ~b[Example 1]:  Suppose your goal conjecture is:
   ~bv[]
   ~i[Goal Conjecture]:
   (implies (and (endp z)
                 (true-listp z))
            (equal (rev (rev z)) z))
   ~ev[]
   Then you can use the following theorem (actually the definitional axiom introduced
   by the ~c[defun] of ~c[endp]):
   ~bv[]
   ~i[Definitional Axiom]: endp
   (equal (endp x)
          (not (consp x))).
   ~ev[]
   to ~i[rewrite] the ~i[Goal Conjecture] to
   ~bv[]
   ~i[Rewritten Goal Conjecture]:
   (implies (and (not (consp z))
                 (true-listp z))
            (equal (rev (rev z)) z))
   ~ev[]
   Note that in this example, rewriting replaced the call of ~c[endp] by its
   body after instantiating its body with the actuals from the call.  This is
   sometimes just called ~i[expanding] the definition of ~c[endp].
   (The notions of ~i[formal], ~i[body], ~i[call], and ~i[actuals] are
   discussed in ~il[programming-knowledge-taken-for-granted].)

   Expanding a definition is an example of ~i[unconditional] rewriting.
   All definitions in ACL2 are just bare equalities relating a call of the
   function on its formals to its body.  Any time you use an equality
   theorem, whether a definitional equality or something more general like
   ~bv[]
   (equal (append (append x y) z)
          (append x (append y z)))
   ~ev[]
   to replace an instance of one side by the corresponding instance of the
   other in a goal conjecture, we call that ~i[unconditional] rewriting
   with the equality.   

   ~b[Example 2]:  Suppose your goal conjecture is:
   ~bv[]
   ~i[Goal Conjecture]:
   (implies (and (subsetp a b)
                 (true-listp b)
                 (member e a))
            (< (len (rm e b)) (len b))).
   ~ev[]
   This conjecture may be read ``if ~c[a] is a subset of the ~c[true-listp] ~c[b] and ~c[e] is
   a member of ~c[a], then the result of removing ~c[e] from ~c[b] has a shorter length
   than ~c[b].''

   You can use the following theorem:
   ~bv[]
   ~i[Theorem]:
   (implies (member u v)
            (equal (len (rm u v))
                   (- (len v) 1)))
   ~ev[]
   to ~i[rewrite] the ~i[Goal Conjecture] to
   ~bv[]
   ~i[Rewritten Goal Conjecture]:
   (implies (and (subsetp a b)
                 (true-listp b)
                 (member e a))
            (< (- (len b) 1) (len b))).
   ~ev[]
   To do this you must know that the following subgoal is provable:
   ~bv[]   
   ~i[Subgoal to Relieve Hyp 1]:
   (implies (and (subsetp a b)
                 (true-listp b)
                 (member e a))
            (member e b)).
   ~ev[]   

   This is an example of ~i[conditional] rewriting.  In order to use the
   ~i[Theorem] we had to establish that its hypotheses are satisfied.  That is
   called ~i[relieving the hypotheses] and was done by proving the ~i[Subgoal to Relieve Hyp 1].
   Conditional rewriting is the most commonly used proof technique in ACL2.  

   Unconditional rewriting is just a special case, where there are no
   hypotheses to relieve.

   Expanding a definition is just another special case, where there are no
   hypotheses to relieve and the pattern is easy to match because it is a
   call of a function on distinct variables.

   This page discusses ~i[rewriting] from the logical perspective.  It is
   important that you are familiar with the notions of a ~i[pattern] term being
   an ~il[logic-knowledge-taken-for-granted-instance instance] of a ~i[target]
   term.  We often say the pattern ~i[matches] the target.  These notions
   involve a corresponding ~i[substitution] of terms for variables.  All these
   notions are discussed in the link for
   ``~il[logic-knowledge-taken-for-granted-instance instance]'' above and we
   recommend you read it before continuing.  Then use your browser's ~b[Back Button]
   to come back here.
   
   You should also be aware of the terms introduced in our discussion of
   ~il[logic-knowledge-taken-for-granted-propositional-calculus propositional calculus].

   ~i[Rewriting] is a fundamental rule of inference in our system.  The rule
   allows you to use a theorem, i.e., an axiom, lemma, or definition, to
   replace one term by another in the goal conjecture you're trying to prove.

   Suppose you have a theorem that is of the form (or can be put into the
   form):
   ~bv[]
   ~i[Theorem]:
   (implies (and ~i[hyp1]
                 ...
                 ~i[hypk])
            (equal ~i[pattern]
                   ~i[replacement]))
   ~ev[]

   From the logical perspective we don't care how the theorem was actually written
   when it was proved.  It might have no hypotheses (in which case the ~i[hypi] could just
   be ~c[t]), or it could have been written in
   a different but equivalent propositional style, ~c[(or (not] ~i[hyp1]~c[) ...)],
   or the equality could have been written the other way around,
   ~c[(equal ]~i[replacement] ~i[pattern]~c[)].  Such syntactic details don't matter.
   Just take a theorem and use propositional calculus to rearrange it equivalently
   into this form for the purposes of this one rewrite step.

   Suppose ~i[pattern] is an instance of some target term, ~i[target] that
   occurs in your goal conjecture.  Let the corresponding substitution be
   ~i[sigma].  If ~i[sigma] does not contain a binding for every variable that
   occurs in ~i[Theorem], then extend ~i[sigma] to ~i[sigma'] by adding one
   binding for each such variable.  (This is necessary only if ~i[pattern]
   does not contain every variable in ~i[Theorem].)

   Let ~i[replacement'] be the result of instantiating ~i[replacement] with ~i[sigma'].
   Let ~i[hypi'] be the result of instantiating ~i[hypi] with ~i[sigma'].

   Then the ~b[Rewrite Rule of Inference] tells us it is permitted to replace
   that occurrence of ~i[target] in the goal by ~i[replacement'] -- ~b[if you can prove]
   each ~i[hypi'] in this context.  We make this last condition clear
   in a moment.

   The justification for this is that ~i[Theorem] is true for all values of the
   variables.  Hence, it is true for the values specified by ~i[sigma'].  If
   the ~i[hypi'] are true, then the target is really equal to ~i[replacement'].
   But it is always permitted to replace something by something it's equal to.
   
   Rewriting thus involves several steps:

   (1) Finding a ~i[target] and a ~i[theorem] to use to rewrite it to some more
   desirable ~i[replacement].

   (2) Instantiating ~i[pattern] in the (rearranged) theorem to match ~i[target].

   (3) Extending ~i[sigma] to ~i[sigma'] to bind all the variables in ~i[Theorem].

   (4) Establishing that the ~i[sigma'] instances of each of the ~i[hypi] hold.
   This is called ~i[relieving the hypotheses] of the theorem and is discussed in
   greater detail below.

   (5) Replacing the occurrence of ~i[target] in the goal conjecture by
   the ~i[sigma'] instance of ~i[replacement], provided all the hypotheses
   are relieved.

   Step (4) above, ~i[relieving the hypotheses], requires first identifying the
   ``context'' of the target in the goal conjecture.  To do this, use
   propositional calculus to rearrange the goal conjecture so the occurrence of
   ~i[target] is in the conclusion and let ~i[context] be the hypothesis.
   ~bv[]
   ~i[Rearranged Conjecture]:
   (implies ~i[context]
            (... ~i[target] ...))
   ~ev[]

   To relieve the hypotheses you must then prove each of the following
   subgoals:
   ~bv[]
   ~i[Subgoal to Relieve Hyp i]:
   (implies ~i[context] ~i[hypi']).
   ~ev[]

   It is important to note that this description of rewriting with ~i[Theorem] 
   describes the process from a strictly logical perspective.  The syntax of
   the theorem and the goal don't matter.  You're free to use propositional
   calculus to rearrange them to put them into the appropriate forms to 
   fit the descriptions given.  Clearly, if you have a candidate Theorem
   in the ``wrong'' form and but it can be rearranged with propositional
   calculus into the ``right'' form, then that rearranged theorem is also
   a ~i[Theorem] and can be used as described.  But in the actual implementation
   of ACL2, the syntactic form of a proved ~i[Theorem] affects how it is
   used by rewriting.  If a proved theorem takes the form of an implication
   concluding with an equality, ACL2 treats the left-hand side of the
   equality as ~i[pattern] and the right-hand side as ~i[replacement], unless
   you tell it otherwise.  We'll discuss this later.

   Furthermore, being from the logical perspective this discussion of
   rewriting does not address (a) how you extend ~i[simga] to ~i[sigma']
   -- any extension will do provided it allows you to relieve the hypotheses.
   The ACL2 theorem prover uses certain heuristics which we'll discuss later,
   including methods by which you can guide the system in the selection.

   Crucially, it does not discuss whether it is a ~i[good idea] to do a
   particular rewrite!  For example, the definitional equality:
   ~bv[]
   (equal (len x)
          (if (endp x)
              0
              (+ 1 (len (cdr x)))))
   ~ev[]
   may be used repeatedly, endlessly, to replace ~c[(len a)] by an
   ever growing sequence of terms:
   ~bv[]
   (len a)
   =
   (if (endp a)
       0
       (+ 1 (len (cdr a))))
   =
   (if (endp a)
       0
       (+ 1 (if (endp (cdr a))
                0
                (+ 1 (len (cdr (cdr a)))))))
   = ...
   ~ev[]

   The ACL2 implmentation of rewriting uses certain heuristics and the
   you can guide the system in its choices.  We'll discuss this later.

   Now use your browser's ~b[Back Button] to return to the example proof in
   ~il[logic-knowledge-taken-for-granted].~/~/")
   
(deflabel logic-knowledge-taken-for-granted-rewriting-repeatedly
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   further information on expanding definitions via rewriting~/

   We assume you've read about
   ``~il[logic-knowledge-taken-for-granted-instance instances]'' and picked up
   our basic terminology including the ideas of ~i[matching] a ~i[pattern] term to a
   ~i[target] term, obtaining a ~i[substitution] and how to ~i[instantiate] a term
   with a substitution.  We use these notions below without further citation.

   In addition, we assume you've read about
   ``~il[logic-knowledge-taken-for-granted-rewriting rewriting]'' where we
   introduced the idea of treating a theorem (axiom, definition, or lemma)
   as a ~i[conditional rewrite] rule and replaced one term by an equivalent one
   provided we can ~i[relieve the hypotheses].

   Suppose you're trying to prove ~i[formula1] and you transform it
   to ~i[formula2] by rewriting.
   What happened?
   ~bv[]
   ~i[formula1]:
   (implies (and (not (consp z))
                 (true-listp z))
            (equal (rev (rev z)) z))

   ~i[formula2]:
   (implies (and (not (consp z))
                 (equal z nil))
            (equal (rev (rev z)) z))
   ~ev[]
   Evidently we replaced ~c[(true-listp z)] by ~c[(equal z nil)].
   But how did that happen?  What really happened was the sequential
   application of several unconditional rewrites and the use of replacement of
   equals by equals.

   The definition of ~c[true-listp] is:
   ~bv[]
   (defun true-listp (x)
     (if (consp x)
         (true-listp (cdr x))
         (equal x nil))).
   ~ev[]
   By rewriting once with the definition of ~c[true-listp],
   we transform ~i[formula1] to:
   ~bv[]
   ~i[formula1']:
   (implies (and (not (consp z))
                 (if (consp z)
                     (true-listp (cdr z))
                     (equal z nil)))
            (equal (rev (rev z)) z)).
   ~ev[]
   Note how the call of ~c[true-listp] has been replaced by the entire body
   of ~c[true-listp].

   Next, note that the first hypothesis above is that ~c[(consp z)] is false.
   That is, ~c[(not (consp z))] is the same as ~c[(equal (consp z) nil)].
   Thus, replacement of equals by equals means we can transform ~i[formula1'] to   
   ~bv[]
   ~i[formula1'']:
   (implies (and (not (consp z))
                 (if nil
                     (true-listp (cdr z))
                     (equal z nil)))
            (equal (rev (rev z)) z)).
   ~ev[]
   (We will explore replacement of equals by equals later.)

   Furthermore, we know the basic axiom about ~c[if]:
   ~bv[]
   ~i[Axiom] if-nil:
   (if nil x y) = y.
   ~ev[]

   Rewriting with this particular axiom, using ~c[(if nil x y)] as the pattern
   and ~c[y] as the replacement, will transform ~i[formula1''] to
   ~bv[]
   ~i[formula2]:
   (implies (and (not (consp z))
                 (equal z nil))
            (equal (rev (rev z)) z)).
   ~ev[]

   Often when we say we derived one formula from another by ``expansion'' and or
   by ``rewriting'' we take many rewrite steps, as here.  We typically use hypotheses of the
   formula without noting ``replacement of equals by equals'' as when we replaced
   ~c[(consp z)] by ~c[nil], and we typically omit to mention the use of basic
   axioms like ~c[if-nil] above.

   Now use your browser's ~b[Back Button] to return to the example proof in
   ~il[logic-knowledge-taken-for-granted].~/~/")

(deflabel logic-knowledge-taken-for-granted-equals-for-equals
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   substitution of equals for equals~/

   Anytime you have an equality hypothesis relating two terms, e.g.,
   ~bv[]
   (equal ~i[lhs] ~i[rhs])
   ~ev[]
   it is legal to substitute one for the other anyplace else in the formula.
   Doing so does not change the truthvalue of the formula.

   You can use a ~i[negated equality] this way ~i[provided] it appears in the
   conclusion.  For example, it is ok to transform
   ~bv[]
   (implies (true-listp x)
            (not (equal x 23)))
   ~ev[]
   to
   ~bv[]
   (implies (true-listp 23)
            (not (equal x 23)))
   ~ev[]
   by substitutions of equals for equals.  That is because, by 
   ~il[logic-knowledge-taken-for-granted-propositional-calculus propositional calculus],
   we could rearrange the formulas into their ~i[contrapositive] forms:
   ~bv[]
   (implies (equal x 23)
            (not (true-listp x)))
   ~ev[]
   and
   ~bv[]
   (implies (equal x 23)
            (not (true-listp 23)))
   ~ev[]
   and see the equality as a hypothesis and the substitution of ~c[23] for ~c[x] as
   sensible.

   Sometimes people speak loosely and say ``substitution of equals for equals''
   when they really mean ``substitutions of equivalents for equivalents.''
   Equality, as tested by ~c[EQUAL], is only one example of an equivalence
   relation.  The next most common is propositional equivalence, as tested by
   ~c[IFF].  You can use propositional equivalence hypotheses to substitute
   one side for the other ~i[provided] the target term occurs in a propositional
   place, as discussed at the bottom of
   ~il[logic-knowledge-taken-for-granted-propositional-calculus propositional calculus].   

   Now use your browser's ~b[Back Button] to return to the example proof in
   ~il[logic-knowledge-taken-for-granted].~/~/")

(deflabel logic-knowledge-taken-for-granted-evaluation
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   evaluation during proofs~/

   Any time you are proving a formula and see a subterm in the formula
   that contains no variables, you can just evaluate the subterm.

   This is familiar from algebra:  It is not uncommon to
   rearrange a polynominal to collect all the constants and
   then add them up:
   ~bv[]
   (3x + 2 + 7y + 2)
   =
   (3x + 7y + (2 + 2))
   =
   (3x + 7y + 4).
   ~ev[]
   That last step is just evaluation.  

   It happens often in ACL2 proofs because theorems involve constants
   and defined functions and when those constants ``drift into the maw''
   of a function, the function call can be eliminated and replaced by
   a new constant.  ACL2 does this automatically; you don't have to tell it.
   In fact, there are a few occasions where you might prefer it ~i[not]
   evaluate and those are the ones you have to look out for!  They'll be
   obvious when they happen because you'll see a mysterious constant crop
   up in the proof.

   Evaluation is legal because it is just the repeated use of
   unconditional rewriting to replace definitions by their instantiated
   bodies until no function calls remain.

   Now use your browser's ~b[Back Button] to return to the example proof in
   ~il[logic-knowledge-taken-for-granted].~/~/")


(deflabel logic-knowledge-taken-for-granted
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   background knowledge in ACL2 logic for theorem prover tutorial~/

   You might think that in order to use the theorem prover you have to know
   the mathematical logic supported by ACL2.  But you need to know a lot less
   about it than you might think.

   Technically, a theorem is a formula that can be derived from axioms by using
   rules of inference.  Thus, to do a proof you have to know (a) the syntax of
   formulas, (b) the axioms, and (c) the rules of inference.  Traditionally,
   these things are spelled out in excruciating detail in treatments of
   mathematical logic -- and for good reason.

   The whole point of proving theorems is that it is a way to determine that a
   formula is ``always true'' (under some model of the axioms).  By ``always
   true'' we actually mean what logicians mean when they say the formula is
   ~i[valid]: true in the model, for all possible values of the variables.
   Here by ``model of the axioms'' we mean an understanding of the meaning of
   the various function symbols so that the axioms are true for all values of
   the variables.  If the variables in your conjecture can take on an infinite
   number of values, proof is often the ~b[only] way to determine that a
   conjecture is ``always true.''  So if proof is being used to determine that
   a questionable formula is always true the proof must be carried out
   flawlessly.  Thus, the (a) syntax, (b) axioms, and (c) rules of inference
   must be described precisely and followed to the letter.

   But formal mathematical logic was invented to explain how people reason.  To
   the extent that logic mimics human reasoning, proofs can be seen as just
   extremely carefully crafted arguments.  Given that ACL2 is responsible for
   following the rules ``to the letter,'' your main job is ``explain'' the
   big leaps.  

   To use the theorem prover you must understand (a) the syntax, because
   you must be able to write formulas flawlessly.  But you don't have to know
   (b) the axioms and (c) the rules of inference at nearly the same level of
   precision, as long as you understand the basic structure and language of
   proofs.
   
   Below is part of a proof of a certain theorem.  You ought to be able to
   understand the following.  Since what we describe is a proof of one case of
   the formula, we hope that you're ~i[convinced] that the formula holds for
   that case.
    
   Read this and follow the links to confirm that you understand what happens.
   Be sure to then use your browser's ~b[Back Button] to return to this page
   and continue.

   ~b[An Annotated Proof of]
   ~bv[]
   (implies (true-listp z)
            (equal (rev (rev z)) z))
   ~ev[]

   ``We will prove that reversing the reverse of a ~c[true-listp] yields the
   original list.  The formula stating this is above.  We will prove it by
   ~il[logic-knowledge-taken-for-granted-inductive-proof induction] on the
   list structure of ~c[z].

   The ~il[logic-knowledge-taken-for-granted-base-case base case] of the
   induction is:
   ~bv[]
   (implies (endp z)
            (implies (true-listp z)
                     (equal (rev (rev z)) z))).
   ~ev[]
   This formula is equivalent, by
   ~il[logic-knowledge-taken-for-granted-propositional-calculus propositional calculus],
   to
   ~bv[]
   (implies (and (endp z)
                 (true-listp z))
            (equal (rev (rev z)) z))
   ~ev[]

   ~il[logic-knowledge-taken-for-granted-rewriting Rewriting]
   with the definition of ~c[endp] produces:
   ~bv[]
   (implies (and (not (consp z))
                 (true-listp z))
            (equal (rev (rev z)) z))
   ~ev[]

   ~il[logic-knowledge-taken-for-granted-rewriting-repeatedly Rewriting repeatedly] 
   starting with the definition of ~c[true-listp] produces:
   ~bv[]
   (implies (and (not (consp z))
                 (equal z nil))
            (equal (rev (rev z)) z))
   ~ev[]
   Then using the second ~i[hypothesis], just 
   ~il[logic-knowledge-taken-for-granted-equals-for-equals substituting equals for equals],
   we get
   ~bv[]
   (implies (and (not (consp z))
                 (equal z nil))
            (equal (rev (rev nil)) nil))
   ~ev[]
   Since the ~i[conclusion] involves no variables, we can
   ~il[logic-knowledge-taken-for-granted-evaluation evaluate] it,
   getting
   ~bv[]
   (implies (and (not (consp z))
                 (equal z nil))
            T)
   ~ev[]
   But this is an ~il[logic-knowledge-taken-for-granted-instance instance] of
   the ~il[logic-knowledge-taken-for-granted-propositional-calculus tautology]
   ~c[(implies p T)].  Thus, the base case is proved.''

   Now it is time for a little quiz.  There are just three questions.

   ~b[Q1]:  The case above was the Base Case of an inductive proof of
   ~bv[]
   (implies (true-listp z)
            (equal (rev (rev z)) z))
   ~ev[]
   in which we did induction on the structure of the linear list ~c[z].  What
   is the Induction Step?  That is, what do you have to prove besides the Base
   Case to complete this inductive proof?

   Below are four commonly given answers; choose one.  Then look
   ~il[logic-knowledge-taken-for-granted-q1-answer here] to find
   out if you're right.
   ~bv[]
   ~i[Induction Step -- Choice (i)]:
   (implies (not (endp z))
            (implies (true-listp z)
                     (equal (rev (rev z)) z)))

   ~i[Induction Step -- Choice (ii)]:   
   (implies (true-listp (cdr z))
            (equal (rev (rev (cdr z))) (cdr z)))

   ~i[Induction Step -- Choice (iii)]:   
   (implies (and (not (endp z))
                 (equal (rev (rev (cdr x))) (cdr x)))
            (implies (true-listp z)
                     (equal (rev (rev z)) z)))

   ~i[Induction Step -- Choice (iv)]:   
   (implies (and (not (endp z))
                 (implies (true-listp (cdr z))
                          (equal (rev (rev (cdr z))) (cdr z))))
            (implies (true-listp z)
                     (equal (rev (rev z)) z)))
   ~ev[]

   ~b[Q2]: To prove the Induction Step we must prove one or more of the goals below.

   Which combinations are sufficient to imply the Induction Step?  Decide what
   is required and then look ~il[logic-knowledge-taken-for-granted-q2-answer here]
   to find out if you're right.  To help you, the Induction Step is of
   the form:
   ~bv[]
   ~i[Induction Step]:
   (implies (and ~i[c]
                 (implies ~i[p'] ~i[q']))
            (implies ~i[p] ~i[q]))
   ~ev[]
   and beside each candidate subgoal we show its structure in those terms. 

   ~bv[]
   ~i[Subgoal (i)]:
   (implies (and (not (endp z))                        ; (implies (and ~i[c]
                 (true-listp z))                       ;               ~i[p])
            (true-listp (cdr z)))                      ;          ~i[p'])

   ~i[Subgoal (ii)]:
   (implies (and (not (endp z))                        ; (implies (and ~i[c]
                 (true-listp z)                        ;               ~i[p]
                 (equal (rev (rev (cdr z))) (cdr z)))  ;               ~i[q'])
            (equal (rev (rev z)) z))                   ;          ~i[q])

   ~i[Subgoal (iii)]:
   (implies (and (not (endp z))                        ; (implies (and ~i[c]
                 (equal (rev (rev (cdr z))) (cdr z)))  ;               ~i[q'])
            (equal (rev (rev z)) z))                   ;          ~i[q])

   ~i[Subgoal (iv)]:
   (implies (and (not (endp z))                        ; (implies (and ~i[c]
                 (true-listp (cdr z))                  ;               ~i[p']
                 (equal (rev (rev (cdr z))) (cdr z)))  ;               ~i[q'])
            (equal (rev (rev z)) z))                   ;          ~i[q])
   ~ev[]

   ~b[Q3]: Suppose you know the theorem
   ~bv[]
   ~i[Theorem]:
   (implies (p (f x))
            (equal (g (h x))
                   x))
   ~ev[]
   and you wish to rewrite the target ~c[(g (h a))] to ~c[a] in
   ~bv[]
   ~i[Goal Conjecture]:
   (implies (and (q (f a))
                 (r a))
            (s (g (h a))))
   ~ev[]
   What must you prove to relieve the hypothesis of ~i[Theorem]?

   After you've thought about it, look 
   ~il[logic-knowledge-taken-for-granted-q3-answer here] for our answer.

   ~b[End of the Quiz]

   If this page made sense, you're ready to read the introduction to the
   theorem prover.

   If you are reading this as part of the tutorial introduction to the theorem
   prover, use your browser's ~b[Back Button] now to return to
   ~il[introduction-to-the-theorem-prover].~/~/")

(deflabel special-cases-for-rewrite-rules
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   convenient short forms for rewrite rule formulas~/

   In principle, every rewrite rule is made from a formula of this shape:
   ~bv[]
   (IMPLIES (AND ~i[hyp1] ... ~i[hypk])
            (~i[eqv] ~i[lhs] ~i[rhs]))
   ~ev[]
   where ~i[eqv] is either ~c[EQUAL] or ~c[IFF] and the result of expanding any
   abbreviations in ~i[lhs] is the application of some function symbol other
   than ~c[IF].

   * In the special case where there is only one ~i[hyp] term, i.e., ~i[k]=1,
   the ~c[(AND ]~i[hyp1]~c[)] can be written ~i[hyp1].

   * In the special case where there are no ~i[hyp] terms, ~i[k]=0, the ~c[(AND)]
   term is logically just ~c[T] and the whole ~c[IMPLIES] can be dropped; such
   a formula may be written as an unconditional ~c[EQUAL] or ~c[IFF] term.

   * If you build a rewrite rule from a formula that concludes with ~c[(NOT ]~i[x]~c[)],
   it is treated as though it were ~c[(EQUAL ]~i[x]~c[ NIL)], which
   is logically equivalent to what you typed.

   * If you build a rewrite rule from a formula that concludes with an ~c[AND], ACL2
   will build a rewrite rule for each conjunct of the ~c[AND].  This is because
   ~bv[]
   (IMPLIES hyp (AND concl1 concl2))
   ~ev[]
   is propositionally equivalent to
   ~bv[]
   (AND (IMPLIES hyp concl1)
        (IMPLIES hyp concl2)).
   ~ev[]
   However, if you use an ~c[OR]-expression as a hypothesis, ACL2 does ~i[not] do the
   dual transformation.  Thus, ~c[(IMPLIES (OR hyp1 hyp2) concl)] generates one rewrite
   rule.

   * Finally, if you build a rewrite rule from a formula that does not conclude
   with an ~c[EQUAL], an ~c[IFF], a ~c[NOT], or an ~c[AND,] but with some other
   term, say, ~i[lhs], then ACL2 acts like you typed ~c[(IFF ]~i[lhs]~c[ T)],
   which is logically equivalent to what you typed.

   Thus, regardless of what you type, every rule has ~i[k] hypotheses.  For
   unconditional rules, ~i[k] is 0 and the hypotheses are vacuously true.
   Whether or not you write an ~c[EQUAL] or an ~c[IFF] in the conclusion, every
   rule is either an equality or a propositional equivalence, every rule has a
   left-hand side, and every rule has a right-hand side.

   Use your browser's ~b[Back Button] now to return to
   ~il[introduction-to-rewrite-rules-part-1].~/~/")

(deflabel equivalent-formulas-different-rewrite-rules
   :doc
   ":Doc-Section introduction-to-the-theorem-prover

   logically equivalent formulas can generate radically different rules~/

   Consider the rewrite rules that would be generated from the three
   commands below.  In all three cases, the fact being stated relates the
   ~c[n]th element of the reverse of ~c[x] to the ~c[n]th element of ~c[x].  In
   fact, the three formulas are simple rearrangements of each other and are all
   equivalent.  The theorem prover treats all three formulas equivalently
   when proving them.  But the rules generated from them are very different.

   ~bv[]
   (defthm nth-rev-1
     (implies (and (natp n)
                   (< n (len x)))
              (equal (nth n (rev x))
                     (nth (- (len x) (+ 1 n)) x))))

   (defthm nth-rev-2
     (implies (and (natp n)
                   (< n (len x)))
              (equal (nth (- (len x) (+ 1 n)) x)
                     (nth n (rev x)))))

   (defthm nth-rev-3
     (implies (and (natp n)
                   (not (equal (nth n (rev x))
                               (nth (- (len x) (+ 1 n)) x))))
              (not (< n (len x)))))
   ~ev[]

   Here are the three rewrite rules:

   ~b[nth-rev-1]:~nl[]
   Replace instances of ~c[(NTH n (REV x))]~nl[]
   by ~c[(NTH (- (LEN x) (+ 1 n)) x)],~nl[]
   if you can establish that ~c[n] is a natural
   number less than the length of ~c[x].

   ~b[nth-rev-2]:~nl[]
   Replace instances of ~c[(NTH (- (LEN x) (+ 1 n)) x)]~nl[]
   by ~c[(NTH n (REV x))],~nl[]
   if you can establish that ~c[n] is a natural
   number less than the length of ~c[x].

   ~b[nth-rev-3]:~nl[]
   Replace instances of ~c[(< n (LEN x))]~nl[] 
   by ~c[NIL]~nl[]
   if you can establish that ~c[n] is a natural
   number and that ~c[(NTH n (REV x))] is different from
   ~c[(NTH (- (LEN x) (+ 1 n)) x)].

   As the driver of ACL2, you have to decide which rule you want
   ~i[when you give the command to prove it].

   If you tell the theorem prover to use both ~c[nth-rev-1] and ~c[nth-rev-2],
   ACL2 will enter an infinite loop when it sees any term matching either ~c[NTH] expression.

   Most users would choose form ~c[nth-rev-1] of the rule.  It eliminates
   ~c[rev] from the problem -- at the expense of introducing some arithmetic.  But
   arithmetic is so fundamental it is rarely possible to avoid it and it is
   likely to be in the problem already since you're indexing into ~c[(rev x)].  The
   ~c[nth-rev-2] form of the rule is ``bad'' because it introduces ~c[rev] into a
   problem where it might not have appeared.  The ~c[nth-rev-3] version is
   ``bad'' because it makes the theorem prover shift its attention from a
   simple arithmetic inequality to a complicated property of ~c[nth] and
   ~c[rev], which might not be in the problem.

   Use your browser's ~b[Back Button] now to return to
   ~il[introduction-to-rewrite-rules-part-1].~/~/")

(deflabel introduction-to-rewrite-rules-part-2
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   how to arrange rewrite rules~/

   You should design your rewrite rules to canonicalize the terms in your
   problem, that is, your rules should drive terms into some normal form so
   that different but equivalent terms are rewritten into the preferred shape,
   making equivalent terms identical.  You are very familiar with this idea
   from algebra, where you learned to normalize polynomials.  Thus, when you
   see ~i[(2x + 6)(3x - 9)] you automaticaly normalize it, by ``multiplying out
   and collecting like terms,'' to get ~i[(6x^2 - 54)].  This normalization
   strategy allows you to recognize equivalent terms presented differently,
   such as ~i[6(x^2 - 9)].  

   The ACL2 user is responsible for making up the rules.  (Standard ``books''
   -- files of ACL2 definitions and theorems -- can often provide rules for
   some sets of functions, e.g., arithmetic.)  This is a heavy burden on you
   but it means you are in charge of your own normal forms.  For example, if you
   use the function ~c[nthcdr], which returns the ~c[n]th ~c[cdr] of a list,
   you might see both ~c[(cdr (nthcdr i x))] and ~c[(nthcdr i (cdr x))].
   These two expressions are equivalent but not identical.  You will want to
   decide which you want to see and prove the rewrite rule that converts the
   other to that preferred form.

   Most good users develop an implicit ordering on terms and rewrite ``heavy''
   terms to ``lighter'' ones.  This insures that there are no loops in their
   rewrite rules.  But this ordering changes according to the user and the
   problem.

   Generally, the lightest terms are primitives such as ~c[IF], ~c[EQUAL],
   arithmetic, etc.  Functions defined without explicit recursion tend to
   be ignored because they are just expanded away (but see below).  Recursively
   defined functions tend to be heavier than any other recursive function used
   in their definitions, so, for example, if ~c[rev] is defined in terms of ~c[append],
   ~c[rev] is heavier than ~c[append].  But the size and subtlety of recursively
   defined functions also affects their place in the ordering.

   But rewrite rules are surprisingly subtle.  Recall that a rewrite rule
   can be made from a formula of this form:
   ~bv[]
   (IMPLIES (AND ~i[hyp1] ... ~i[hypk])
            (~i[eqv] ~i[lhs] ~i[rhs]))
   ~ev[]
   where ~i[eqv] is either ~c[EQUAL] or ~c[IFF], and ~i[lhs] is a call of a
   function other than ~c[IF].  In such a rule, ~i[lhs] is the pattern
   responsible for triggering the rule, the ~i[hypi] are conditions which must
   be satisfied by the context of the target being rewritten, and ~i[rhs] is
   the replacement.  The replacement only happens if the rule is enabled, the
   pattern matches, the conditions are satisfied, and (in the case of an
   ~c[IFF] rule) the target occurs propositionally.  There are other heuristic
   restrictions that we won't discuss here.

   So how should you phrase a theorem in order to make it an effective rule?

   General Principles:

   * ~b[Strengthen the Formula]: The fewer hypotheses a formula has the better
   the rewrite rule formed from it.  The more general the left-hand side the
   better the rule.  The fewer free variables in the hypothesis, the better.
   The idea is to form a rule that fires predictably.  Later in this tutorial
   you'll get some practice formulating strong rules.

   * ~b[Choosing the Conclusion]: If a lemma is an implication, you have to
   choose what the conclusion will be. (You'll also have to ``orient'' that
   conclusion by choosing a left-hand side and a right-hand side, but we
   discuss that below).  You can swap the conclusion and any hypothesis by
   negating both, producing a different conclusion.  There are generally
   two (possibly conflicting) heuristics for deciding which part of the formula
   should be the conclusion:

   ~i[Choosing the Conclusion Heuristic 1]: Can you make the conclusion be an
   ~c[EQUAL] or ~c[IFF] expression that has a ``heavy term'' on one side?  That
   will make a rule that replaces the heavy term with a lighter one.  We
   discuss this situation more below.

   ~i[Choosing the Conclusion Heuristic 2]: Can you make the conclusion be a
   non-propositional term that contains all the variables mentioned in the
   hypotheses?  By ``non-propositional'' we mean a term that is not just the
   propositional combination (e.g., with ~c[AND] or ~c[OR]) of other terms but
   instead some call of some ``heavy'' function?  If your conclusion contains
   all the variables mentioned in the hypotheses, matching it will instantiate
   all the variables in the hypotheses.  That way ACL2 will not have to guess
   instantiations of unbound variables when it tries to relieve the hypotheses.
   It is not very good at guessing.

   * ~b[Orienting the Conclusion]: If the conclusion is an ~c[EQUAL] or an
   ~c[IFF], you have to decide which is the left-hand side and which is the
   right.  If the conclusion is ~c[(NOT ]~i[lhs]~c[)], then the left-hand side
   is ~i[lhs] and the right-hand side is ~c[NIL].  If the conclusion is not an
   ~c[EQUAL], an ~c[IFF], or a ~c[NOT] then the conclusion itself will be the
   left-hand side and the right-hand side will be ~c[T].  If your lemma was
   created by looking a Key Checkpoints while using The Method, the left-hand
   side should match some term in that checkpoint.

   Remember, the left-hand side is the ``trigger'' that will make the rule
   fire.  It is the pattern that ACL2 will be looking for.

   * ~b[Pay attention to the free variables]: Look at the variables that occur
   in the pattern (the left-hand side) and compare them to the variables that
   occur in the hypotheses.  Does some hypothesis contain a variable, say
   ~i[v], that is not in the pattern?  We call ~i[v] a ~i[free variable]
   because it will not be assigned a value (``bound'') by the process of
   pattern matching.  ACL2 will have to guess a value for ~i[v].  If some
   hypothesis contains ~i[v] as a free variable, ask whether more than one
   hypothesis contains ~i[v]?  ACL2 uses the first hypothesis containing a free
   ~i[v] to guide its guess for ~i[v].  To ``guess'' a value for ~i[v], ACL2
   uses that hypothesis as a pattern and tries to match it against the
   assumptions in the checkpoint formula being proved.  This means that key
   hypothesis must be in normal form, to match the rewritten assumptions of the
   goal.  It also means that you should reorder the hypotheses to put the most
   unusual hypothesis containing a free ~i[v] first in the list of conjuncts.
   For example, if ~c[v] is free in two hypotheses, ~c[(natp v)] and
   ~c[(member (nthcdr v a) b)], then we recommend putting the ~c[member] term
   first.  There are likely to be many terms in the goal satisfying the ~c[natp]
   hypothesis -- or none if ~c[natp] has expanded to an integer inequality -- while
   there are likely to be few terms satisfying the ~c[member] hypothesis, especially
   if ~c[a] and ~c[b] are bound by the left-hand side of the rule.

   Here are some (possibly conflicting) heuristics for choosing the left-hand
   side:

   ~i[Choose a Left-Hand Side that Occurs in a Key Checkpoint]: If you use the
   Method you will tend to do this anyway, because you'll see terms in the Key
   Checkpoints that you want to get rid of.  But many moderately experienced
   users ``look ahead'' to how the proof will go and formulate a few
   anticipatory rules with the idea of guiding ACL2 down the preferred path to
   the proof.  When you do that, you risk choosing left-hand sides that won't
   actually arise in the problem.  So when you formulate anticipatory rules,
   pay special attention to the functions and terms you put in the left-hand
   sides.  The next few paragraphs deal with specific cases.

   ~i[Avoid Non-Recursive Functions in the Left-Hand Side]: If the left-hand
   side contains a call of a defined function whose definition is not
   recursive, then it will almost never match any target in the formula being
   rewritten unless the function is disabled.  Suppose for example you have
   defined ~c[SQ] so that ~c[(SQ x)] is ~c[(* x x)].  Suppose you considered
   choosing a left-hand side like ~c[(+ (SQ x) (SQ y))].  Suppose you hoped it
   would hit the target ~c[(+ (SQ A) (SQ B))] in some formula.  But when ACL2
   simplifies the formula, it will first rewrite that target to ~bv[]
   (+ (* A A) (* B B))
   ~ev[]
   by expanding the definition of ~c[SQ], since it could do so without
   introducing any recursive calls.  But now the target won't match your rule.
   By choosing a left-hand side that occurs in a Key Checkpoint (and is not one
   of a handful of abbreviations ACL2 uses in its output like ~c[AND],
   ~c[NOT]), you'll avoid this problem since ~c[SQ] will have already been
   expanded before the Key Checkpoint is printed.

   ~i[Disable Non-Recursive Functions]: If you insist on a left-hand side that
   contains calls of non-recursive functions, remember to disable those
   non-recursive functions after you've proved all the rules you want about them.  By
   disabling ~c[SQ] you can prevent ACL2 from expanding the definition as it
   did above.  Sometimes you will define a function non-recursively to
   formalize some concept that is common in your application and you will want
   to create a sort of algebra of rules about the function.  By all means do
   so, so you can conduct your formal reasoning in terms of the concepts you're
   informally manipulating.  But after proving the required laws, disable the
   non-recursive concept so that ACL2 just uses your laws and not the messy
   definition.

   ~i[Choose a Left-Hand Side Already in Simplest Form]: This is a
   generalization of the advice above.  If any rule will rewrite your left-hand
   side, it will prevent your rule from matching any target.  For example, if
   you write a left-hand side like ~c[(foo (car (cons x y)))] then it would
   never match any target!  The reason is that even if ~c[(FOO (CAR (CONS A B)))]
   did occur in some goal formula, before ACL2 would try your rule about
   ~c[foo] it will use the obvious rule about ~c[CAR] and ~c[CONS] to transform
   your imagined target to ~c[(FOO A)].  Thus, your rule would not match.
   So you have to keep in mind ~i[all your other rules] when you choose
   a left-hand side (and when you choose the hypotheses to guide free variable
   selection).  If you always choose a pattern that matches a term in a
   Key Checkpoint, you avoid this problem.

   ~i[Make Sure the Left-Hand Side is ``Heavier'' than the Right]: Sometimes
   this is obvious, as when you choose ~c[(REV (REV x))] for the left-hand side
   and ~c[x] for the right.  But what do you about ~c[(REV (APPEND x y))]
   versus ~c[(APPEND (REV y) (REV x))]?  Most of the time we choose to drive
   the heaviest function (in this case ~c[REV]) down toward the variables,
   lifting the lighter function (~c[APPEND]) up so that we can reason about the
   lighter function's interaction with the surrounding ``matrix'' of the
   formula.  So we'd rewrite ~c[(REV (APPEND x y))] to ~c[(APPEND (REV y) (REV x))],
   not vice versa.

   ~i[Alternative Ways to Talk About the Same Thing]: If your problem and
   specification use two different ways to talk about the same thing, choose
   one form and rewrite the other into that form.  For example, the ACL2
   built-in ~c[nth] returns the nth element of a list, and the built-in
   function ~c[nthcdr] returns the nth ~c[cdr] of a list.  They are defined
   independently.  But ~c[(nth n x)] is the same thing as ~c[(car (nthcdr n x))].
   Since ~c[nth] can be expressed in terms of ~c[nthcdr] but not vice
   versa, it is clear we should prove ~c[(equal (nth n x) (car (nthcdr n x)))]
   as a rewrite rule if both ~c[nth] and ~c[nthcdr] are involved in the
   problem.

   ~i[Don't Let Computational Efficiency Dictate the Terms]: If you have two
   functions that are equivalent (perhaps one was defined to be computationally
   more efficient), prove their equivalence as a rewrite rule that eliminates
   the more complicated function.  An extreme example would be a model that
   uses a sophisticated data structure (like a balanced binary tree, red-black
   tree, ordered array, or hash table) to implement something simple like an
   association of keys to values.  By proving the equivalence as stated you can
   eliminate the messy function early and do the bulk of your reasoning in
   terms of its simple specification.

   The best ACL2 users become very good at keeping all these things in mind
   when designing their rewrite rules.  Practice makes perfect.  Don't be
   afraid during your learning of ACL2 to undo the rules you first invented and
   try to make better ones.

   Finally, be patient!  There will be times when you think to yourself ``Why
   should I spend my time thinking of rules that guide ACL2?  I know the
   proof!''  There are two reasons.  First, you may ``know'' the proof but you
   may well be wrong and part-way through this whole exercise you may realize
   that you're missing a major hypothesis or special case that breaks your
   whole conception of the problem.  The proof is in the details.  Second, most
   of the time the library of rules you develop in this process will be used
   over and over again on variants of the main problem in the months and years
   ahead.  This is sometimes called the ~i[proof maintenance] problem.
   Theorems don't suffer bit rot!  But the artifacts you're modeling change and
   you will need to prove new versions of old theorems.  A good general purpose
   library makes this much easier.

   We now recommend that you practice inventing strong rules;
   ~pl[strong-rewrite-rules].

   For advice on handling specific kinds of formulas and definitions,
   ~pl[specific-kinds-of-formulas-as-rewrite-rules].

   For more information about the rewriter works and how rules are
   created, ~pl[further-information-on-rewriting].

   If you are working your way through the tutorial introduction to the theorem
   prover, use your browser's ~b[Back Button] to return to
   ~il[introduction-to-the-theorem-prover].

   ~/~/")

(deflabel specific-kinds-of-formulas-as-rewrite-rules
   :doc
   ":Doc-Section introduction-to-the-theorem-prover

   advice about how to handle commonly occurring formulas as rewrite rules~/

   Below we give you some guidelines for handling specific, commonly occurring situations.

   * ~b[Associativity]:  If a function ~c[f] is associative, prove
   ~bv[]
   (equal (f (f x y) z) (f x (f y z)))
   ~ev[]
   ACL2 will use this to flatten ~c[f]-nests ``to the right.''

   * ~b[Commutativity]:  If a function ~c[f] is commutative, prove both
   ~bv[]
   (equal (f x y) (f y x))
   ~ev[]
   and
   ~bv[]
   (equal (f x (f y z)) (f y (f x z)))
   ~ev[]
   ACL2's heuristics will use these rules to order the arguments
   alphabetically, so that ~c[(f B (f D (f A C)))] becomes
   ~c[(f A (f B (f C D)))].

   * ~b[Distributivity]:  If you have a pair of functions ~c[f] and ~c[g]
   so that ~c[(f x (g y z))] is ~c[(g (f x y) (f x z))] or some other
   form of distributivity is provable, arrange your rules to move the
   lighter function symbol up and the heavier one toward the variable symbols.
   For example, our arithmetic libraries drive multiplication through
   addition, producing sums of products rather than products of sums.

   * ~b[Identity and Other Laws]: Prove the obvious identity and zero laws (or
   at least anticipate that you might need them down the road) so as to
   eliminate operators.

   * ~b[Get Rid of Tail Recursive Functions]: A corollary to the above advice
   concerns tail recursive functions that use auxiliary variables.  New users
   often define concepts using tail recursions, accumulating partial results in
   auxiliary variables, because creating such functions is similar to
   programming with ~c[while] loops.  Expert users will use tail recursion when
   necessary for execution efficiency.  But tail recursive functions are messy
   to reason about: their auxiliary variables have to be properly initialized
   to make the functions compute the expected results, but to state inductively
   provable properties of tail recursive functions you must identify the
   invariants on those auxiliary variables.  This problem tends not to happen
   with ~i[primitive recursive functions].  A primitive recursive function is
   one that recurs down one variable and holds all the other variables constant
   in recursion.  Most tail-recursive functions can be written elegantly as
   primitive recursive functions, though one might have to ignore the
   programmer's desire to make things efficient and define auxiliary functions
   to appropriately transform the value returned by the recursive call.  The
   classic example is reverse defined in terms of the auxiliary function
   ~c[append] versus reverse defined tail recursively with an accumulator.  By
   introducing ~c[append] you introduce a concept about which you can state
   lemmas and decompose the proofs of properties of reverse.  So if your
   problem involves tail recursive functions with auxiliary variables, define
   the primitive recursive version, prove that the tail recursive function is
   equivalent to the primitive recursive one, and arrange the rewrite rule to
   eliminate the tail recursive function.

   * ~b[Get Rid of Mutually Recursive Functions]: Similarly, if you have used
   ~c[mutual-recursion] to introduce a clique of mutually recursive functions,
   ~c[f1], ~c[f2], ..., you will find that to reason about any one function in
   the nest you have to reason about all of them.  Any mutually recursive
   function can be defined in a singly recursive way.  So do that and then
   prove a rewrite rule that
   gets rid of all the mutually recursive functions by proving
   ~bv[]
   (and (equal (f1 ...) (g1 ...))
        (equal (f2 ...) (g2 ...))
        ...)
   ~ev[]

   where the ~c[gi] are singly recursive.  You may need to appeal to a trick to
   define the ~c[gi]: define a singly recursive function that takes a flag
   argument and mimics whichever mutually recursive function the flag
   specifies.  ~l[mutual-recursion] ~warn[] and
   ~pl[mutual-recursion-proof-example] ~warn[].

   If you got to this documentation page from the tutorial discussion of
   rewrite rules, use your browser's ~b[Back Button] now to return to
   ~il[introduction-to-rewrite-rules-part-2].

   ~/~/")

(deflabel further-information-on-rewriting
   :doc
   ":Doc-Section introduction-to-the-theorem-prover

   a grab bag of advice and information on rewriting~/

   In the following paragraphs we give some links to advanced topics, marked
   with ``~warn[]''.  If you are reading this topic as part of the tutorial on
   the theorem prover, do not follow these links upon your first reading.  Just
   take note of the existence of the facilities and ideas mentioned.

   ~b[Arithmetic]:  If your goal theorem involves even trivial arithmetic,
   such as adding or subtracting ~c[1], we recommend that you do
   ~bv[]
   (include-book \"arithmetic/top-with-meta\" :dir :system)
   ~ev[]
   which loads into ACL2 all the rules in one of the books distributed with
   ACL2.  (~i[Books] are certified files of definitions, lemmas, etc., usually
   prepared by other ACL2 users and explicitly shared with the community.)  The
   book \"top-with-meta\" is the most elementary and most widely used
   arithmetic book.  Others that come with the ACL2 distribution include
   \"arithmetic-5/top\" and various hardware and floating-point arithmetic books.

   ~b[Rules Concluding with Arithmetic Inequalities]:  If you are tempted to
   create a rewrite rule with an arithmetic inequality as its conclusion or
   left-hand side, think again.  Inequalities such as
   ~bv[]
   (<= (len (delete e x)) (len x))
   ~ev[]
   make poor left-hand sides for rewrite rules.  For example, the inequality above
   does not match the target
   ~bv[]
   (<= (LEN (DELETE E X)) (+ 1 (LEN X)))
   ~ev[]
   even though it is sufficient to prove the target (given some simple arithmetic).
   We recommend that if you have a theorem that establishes an arithmetic
   inequality, you make it a ~i[linear] rule.  ~l[linear] ~warn[].

   ~b[Rearranging Formulas Before Making Rules]: It is possible to rearrange
   the propositional structure of a proved formula before processing it as a
   rule.  This allows you to state a theorem one way ``for publication'' and
   rearrange it to be stored as a more effective rule.
   ~l[introduction-to-the-database] (a tutorial topic you'll come to later) and
   its discussion of the concept of ~c[corollary].  Also, see the discussion of
   ~c[corollary] in ~ilc[rule-classes] ~warn[].

   ~b[Rewriting with New Equivalence Relations]:
   You may introduce new ~i[equivalence] relations, like ``set-equal'' or
   ``is-a-permutation'' and cause the rewriter to replace equivalents by
   equivalents in suitable contexts, where you use ~i[congruence] rules to
   inform ACL2 of where these more relaxed notions of equivalence may be used;
   ~pl[equivalence] ~warn[] and ~pl[congruence] ~warn[].

   ~b[Pragmatic Advice to Control Rules]:  You may attach various ~i[pragmas]
   to a rule that allow you rather fine heuristic control over whether and how the
   rule is applied.  For example, you may mark a hypothesis to be
   ~i[forced] (~pl[force] ~warn[]) meaning that the rule is to be applied even if that
   hypothesis is not relieved -- but if the proof is successful the system will
   turn its attention to all forced subgoals.  You may similarly mark a
   hypothesis so as to cause a case split, allowing the relief of the
   hypothesis on one branch and spawning another branch explicitly denying the
   hypothesis; ~pl[case-split] ~warn[].  You may add a bogus hypothesis that looks at
   the intended application of the rule and decides whether to apply the rule
   or not, performing an arbitrary computation on the syntactic context of the
   application; ~pl[syntaxp] ~warn[].  By providing a ~c[:match-free] modifier to the 
   ~c[:rewrite] rule declaration in your rule-classes, you may tell ACL2 to try all
   or only the first free variable value it guesses (~pl[rule-classes]
   ~warn[]).  You may provide a bogus hypothesis that computes from the
   syntactic environment the values to guess for the free variables in a rule;
   ~pl[bind-free] ~warn[].  You may mark a term so that the rewriter does not
   dive into it; ~pl[hide] ~warn[].

   ~b[Programming Your Own Rewriter]:
   If you cannot find a way to use rewrite rules to make the transformations
   you desire, you might investigate the use of ~i[metafunctions].  A
   metafunction is just a little theorem prover of your own design.  It takes
   as input a list structure representing a term and returns a list structure
   representing a term.  If you can prove that the meaning of the input and
   output terms are equivalent, you can extend the ACL2 simplifier to call your
   metafunction.  ~l[meta] ~warn[].

   ~b[The Order in which Targets are Rewritten]: 
   The rewriter sweeps through terms ``inside-out'' otherwise known as
   ``left-most innermost first''.  Thus, before trying to apply rewrite
   rules to ~c[(]~i[f a1 ... an]~c[)], rules are applied to the ~i[ai].
   This has the good effect of normalizing the ~i[ai].

   This fact might help you understand why sometimes your rules ``don't
   seem to fire.''  For example, suppose you have a rule for rewriting
   ~c[(len (rev x))] to ~c[(len x)] and suppose you wish to prove a theorem
   about ~c[(LEN (REV (CONS A B)))].  Suppose ~c[rev] is defined in terms of
   ~c[append], as shown in ~il[programming-knowledge-taken-for-granted].  Then
   you might see a checkpoint in which the ~c[(LEN (REV ...))] above has been
   simplified to ~c[(LEN (APPEND (REV B) (LIST A)))] instead of to
   ~c[(LEN (CONS A B))].  Why wasn't your rule about ~c[(len (rev x))] applied?
   The reason is that ~c[(REV (CONS A B))] rewrote to ~c[(APPEND (REV B) (LIST A))]
   before rules were applied to ~c[(LEN (REV ...))].  You need a rule about
   ~c[(len (append x y))], as you will see from the checkpoint.

   ~b[The Order in which Rules are Tried]: The rewriter tries the most
   recently proved rules first.  For example, suppose ~c[f], ~c[g], and ~c[h]
   are functions defined so that the following two theorems are provable and
   suppose you executed the following two events in the order shown:
   ~bv[]
   (defthm rule1 (equal (f (g x)) (h 1 x)))
   (defthm rule2 (equal (f (g x)) (h 2 X)))   
   ~ev[]
   Then if rewrite rules are applied to ~c[(F (G A))], the result
   will be ~c[(H 2 A)], because the latter rule, ~c[rule2], is applied
   first.  It is generally best not to have conflicting rules or, at least,
   to understand how such conflicts are resolved.  The system will warn you
   when you propose a rule that conflicts with an existing one.

   If you were reading this topic as part of the tutorial introduction to the
   theorem prover, use your browser's ~b[Back Button] now to return to
   ~il[introduction-to-rewrite-rules-part-2].~/~/")

(deflabel introduction-to-rewrite-rules-part-1
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   introduction to ACL2's notion of rewrite rules~/

   Rewrite rules make ACL2 replace one term by another.  This is done
   by the rewriter, which is part of ACL2's simplifier.  The rewriter
   sweeps through the goal formula trying all the rewrite rules it knows.
   Here's an example.  Just pretend that you have made a rewrite rule
   from the formula below.
   ~bv[]
   (implies (and (natp i)
                 (< i (len a)))
            (equal (put i v (append a b))
                   (append (put i v a) b)))
   ~ev[]
   Then every time the rewriter sees a target term that ~i[matches]
   ~bv[]
   (put i v (append a b))
   ~ev[]
   it considers the rule, with the variables ~c[i], ~c[v], ~c[a], and ~c[b]
   of the rule ~i[bound] to whatever terms matched them in the target, say 
   the terms ~i[i], ~i[v], ~i[a], and ~i[b].  To consider the rule, the 
   rewriter first tries to establish (``relieve'') the hypotheses.  In 
   particular, it rewrites:
   ~bv[]
   (natp ~i[i])           ; ~i[hyp 1]
   ~ev[]
   and
   ~bv[]
   (< ~i[i] (len ~i[a])). ; ~i[hyp 2]
   ~ev[]
   If both hyptheses rewrite to true, then the rule ~i[fires] and replaces
   the target by:   
   ~bv[]
   (append (put ~i[i] ~i[v] ~i[a]) ~i[b]).
   ~ev[]
   In short, rewrite rules direct ACL2 to rearrange the terms in the goal
   formulas.

   We are more precise later, but for now we turn to the question of how do you
   make a rewrite rule from a formula?  The answer is, you prove the formula
   with the ~c[defthm] command.  Recall that
   ~bv[]
   (defthm ~i[name]
           ~i[formula]
           ...)
   ~ev[]
   commands ACL2 to try to prove ~i[formula] and, if successful, build it
   into the database as a rule according to your specification in the ~i[rule-classes]
   argument of the ... part of the command.

   To make it easy for you to generate rewrite rules, ~c[defthm] has a simple heuristic:
   if you don't tell it what kind of rule to generate from ~i[formula], it
   generates a rewrite rule!  Thus, if this command
   ~bv[]
   (defthm ~i[name]
           ~i[formula])
   ~ev[]
   is successful, ACL2 will have a new rewrite rule in the database, even though you
   did not ~i[explicitly] tell it to add a rule.

   A common mistake for the new users is to forget that the above command adds
   a rewrite rule.  This often results in a tangle of rules that lead nowhere
   or to infinite rewriting that you will have to interrupt.  It is also good
   to remember that the command ~i[only] adds a rule.  It does not magically
   make ACL2 aware of all the mathematical consequences of the formula: it just
   makes a rewrite rule.

   When you prove a theorem with ~c[defthm] you are ~i[programming] ACL2.
   Being careless in your statement of lemmas is tantamount to being careless
   in your programming.

   ACL2 can generate rewrite rules from formulas that
   look like this:
   ~bv[]
   (IMPLIES (AND ~i[hyp1] ... ~i[hypk])
            (~i[eqv] ~i[lhs] ~i[rhs]))
   ~ev[]
   where ~i[eqv] is either ~c[EQUAL] or ~c[IFF], and ~i[lhs] is not a variable
   symbol, not a constant, and not a call of the function ~c[IF], and not
   a call of an abbreviation (``macro'') that expands to any of these.  So illegal
   ~i[lhs] include ~c[X], ~c[0], ~c[(IF X Y Y)], and ~c[(OR p q)].  The last
   is illegal because ~c[OR] is just an abbreviation for a certain ~c[IF]-expression.

   Technical Note: This tutorial introduction to the theorem prover takes
   liberties with the truth!  We are trying to give you a useful predictive
   model of the system without burdening you with all the details, which are
   discussed in the reference manual.  For example, using directives in the
   rule-classes you can rearrange the proved formula into the form you want
   your rule to take, and you can make ACL2 take advantage of equivalence
   relations ~i[eqv] other than just ~c[EQUAL] and ~c[IFF].  But we'll ignore
   these fine points for now.

   We call the ~i[hyp] terms the ~i[hypotheses] of the rule.  We call ~i[lhs]
   the ~i[left-hand side] of the rule, and we call ~i[rhs] the ~i[right-hand side]
   of the rule.  If the conclusion of the rule is an ~c[EQUAL] term we
   call it an ~i[equality] rule.  Otherwise, it is a ~i[propositional equivalence]
   rule.  If there are no hypotheses, ~i[k]=0, we say the rule is
   an ~i[unconditional] rewrite rule; otherwise it is ~i[conditional].

   ACL2 allows several special cases of the shapes above.
   ~l[special-cases-for-rewrite-rules], but come back here and continue.

   A rewrite rule makes ACL2 seek out occurrences of terms that match the
   left-hand side of the rule and replace those occurrences using the
   right-hand side, provided all the hypotheses rewrite to true in the context
   of the application of the rule.

   That is, the left-hand side is treated as a ~i[pattern] that triggers the
   rule.  The hypotheses are ~i[conditions] that have to be proved in order for
   the rule to fire.  The right-hand side is the ~i[replacement] and is put
   into the formula where the pattern occurred.

   Now for some clarifications. ACL2 only considers enabled rules.  And ACL2
   will use a propositional rule to replace a target only if the target occurs
   in a propositional place in the formula.  Generally that means it occurs in
   the argument of a propositional connective, like ~c[AND], ~c[OR], ~c[NOT],
   ~c[IMPLIES], and ~c[IFF], or in the test of an ~c[IF].  When we say that the
   left-hand side of the rule must ~i[match] the target we mean that we can
   instantiate the variables in the rule to make the left-hand side identical
   to the target.  To ~i[relieve] or establish the hypotheses of the rule, ACL2
   just applies other rewrite rules to try to prove the instantiated hypotheses
   from the assumptions governing the occurrence of the target.  When ACL2
   replaces the target, it replaces it with the instantiated right-hand side of
   the rule and then applies rewrite rules to that.

   If a hypothesis has variables that do not occur in the left-hand side of the
   rule, then the pattern matching process won't find values for those variables.  We
   call those ~i[free variables].  They must be instantiated before ACL2 can
   relieve that hypothesis.  To instantiate them, ACL2 has to guess values that
   would make the hypothesis true in this context, i.e., true given the assumptions of
   the goal theorem.  So if you're trying to prove
   ~bv[]
   (IMPLIES (AND (TRUE-LISTP A)
                 (MEMBER (CAR P) A)
                 (MEMBER (CDR P) A))
            ...)
   ~ev[]
   and the target you're rewriting is in the ``...'' part of the formula,
   the rewriter knows that ~c[(TRUE-LISTP A)] ~c[(MEMBER (CAR P) A)] and
   ~c[(MEMBER (CDR P) A)] are true.  So if a rewrite rule is considered
   and the rule has ~c[(member e x)] as a hypothesis, where ~c[e] is a free
   variable but ~c[x] was bound to ~c[A] in the pattern matching, then
   it will guess that ~c[e] must be ~c[(CAR P)] or ~c[(CDR P)], even though
   there are many other possibilities that would make ~c[(MEMBER e A)] true.
   Of course, whatever guess it makes must also satisfy all the other hypotheses that
   mention ~c[e] in the rule.  It simply isn't very imaginative at guessing!

   The most predictable rewrite rules have no free variables.  You can add
   pragmatic advice to help ACL2 with free variables, telling it to try all
   the possibilities it finds, to try just the first, or even to compute
   a ``creative'' guess.  

   It is possible to make the rewriting process loop forever, e.g., by
   rewriting ~i[alpha] to ~i[beta] with one set of rules and rewriting ~i[beta]
   to ~i[alpha] with another.  Even a single rule can make the process loop;
   we'll show you an example of that later in the tutorial.  ACL2 can handle
   commutativity rules without looping.  It uses ~c[(equal (+ x y) (+ y x))] to
   replace ~c[(+ B A)] by ~c[(+ A B)], but not vice versa.  (It is sensitive 
   to alphabetic ordering when dealing with ~i[permutative] rules.)

   Logically equivalent formulas can generate radically different rewrite
   rules!  Rearranging the propositional structure of the formula or swapping
   the left and right sides of an equality -- while having no effect on the
   mathematical meaning of a formula -- can have a drastic impact on the
   pragmatic meaning as a rule.  To see an illustration of this,
   ~pl[equivalent-formulas-different-rewrite-rules].

   Developing an effective set of rewrite rules is key to success at using
   ACL2.  We'll look more at this later in the tutorial.

   If you are working your way through the tutorial for the theorem prover, use
   your browser's ~b[Back Button] now to return to
   ~il[introduction-to-the-theorem-prover].  If you are reading just about how
   to make effective rewrite rules, go on to
   ~il[introduction-to-rewrite-rules-part-2].~/~/")

(deflabel introduction-to-the-database
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   how to update the database~/

   We assume you've read ~il[introduction-to-rewrite-rules-part-1] and
   ~il[introduction-to-key-checkpoints].
   
   The theorem prover's heuristics are influenced by the database of rules and
   the enabled/disabled status of the rules.  You can think of the database as
   a ~i[global] hint, potentially affecting all parts of a proof attempt.

   However, in addition to the ``global hint,'' it is possible to give ~i[local]
   hints that affect the theorem prover's behavior on specific subgoals.  We
   discuss the database here and discuss local hints later in the tutorial.

   The theorem prover's ``database'' is called the ~i[ACL2 world].  You change
   the world by issuing commands called ~i[events].  The most common events are
   ~c[defun] for defining new functions (and predicates) and ~c[defthm] for
   proving new theorems.  Both add rules to the database.  Here are some
   commonly used events.

   We recommend that upon the first reading of this tutorial you do not follow
   the links shown below!  The links take you into the hypertext reference
   manual, where it is easy to get lost unless you're looking for detail about
   one specific feature.

   ~l[defun] ~warn[] to define a new function or predicate symbol.  Definitional axioms
   are just a kind of ~c[rewrite] rule, but ~c[defun] may also add rules
   affecting the determination of the type of a term and rules affecting the
   induction analysis.  When you issue a ~c[defun] command you will always supply
   the ~i[name] of the function or predicate, the list of ~i[formal parameters], ~i[v1,...vn], and
   the ~i[body]:
   ~bv[]
   (defun ~i[name] (~i[v1 ... vn])
      ~i[body])
   ~ev[]
   If the event is accepted, a ~i[definitional axiom] is added to the world,
   ~c[(]~i[name] ~i[v1...vn]~c[)]=~i[body], stored as a special kind of
   unconditional rewrite rule.  However, the ~c[defun] event may require
   theorems to be proved.  Specifically, ~i[measure theorems] must be proved to
   establish that recursively defined functions always terminate, by proving
   that an ~i[ordinal] measure of the formal parameters decreases in a
   ~i[well-founded] way in every recursive call.  In addition, if ~i[guards]
   are being used to declare the ~i[expected domain] of the newly defined
   function, ~i[guard theorems] might be proved to establish that all functions
   stay within their expected domains.  In any case, you may provide additional
   information to the ~c[defun] event, coded as part of the ~c[declaration] that
   Common Lisp allows:
   ~bv[]
   (defun ~i[name] (~i[v1 ... vn])
      (declare (xargs ...))
      ~i[body])
   ~ev[]
   The ~c[xargs] (``extra arguments to ~c[defun]'') entry may specify, among
   other things, the measure to use in the termination proof, hints for use by
   the prover during the termination proof, the guard of the new function, and
   hints for use by the prover during the guard verification step.

   ~l[defthm] ~warn[] to prove a theorem and to add it as a rule of one or more
   specified rule-classes.  When you issue a ~c[defthm] command you always
   specify a ~i[name] for the theorem you're trying to prove and a ~i[formula]
   stating the theorem.  You may optionally supply some local hints as we
   describe later in the tutorial.  You may also optionally supply some ~i[rule classes]
   indicating how you want your formula stored as a rule, after it is
   proved.  We discuss the ~c[defthm] ~i[rule classes] below.

   ~l[in-theory] ~warn[] to enable or disable rules.  Rules have names derived from the
   names you give to functions and theorems, e.g., ~c[(:REWRITE LEFT-IDENTITY-OF-FOO . 2)]
   for the second rewrite rule you created from the
   theorem named ~c[LEFT-IDENTITY-OF-FOO].  Rule names are called ~i[runes].  A
   ~i[theory] is just a set (list) of runes.  The ~i[current theory] is the
   list of enabled runes and the ~c[in-theory] event can add runes to or delete
   runes from the current theory.

   ~l[include-book] ~warn[] to change the world by loading a certified file of other events.
   The most common use of ~c[include-book] is to load ``system'' books -- books written by
   other ACL2 users who have released them for distribution to the community.
   The most common books loaded are probably the arithmetic books:
   ~bv[]
   ; * for the most elementary arithmetic, needed for any problem 
   ;   that involves even simple addition and multiplication like
   ;   ~c[(+ x (* 2 y) -3)]:

       (include-book \"arithmetic/top-with-meta\" :dir :system)

   ; * for more complicated arithmetic involving non-linear terms like
   ;   ~c[(* x y)], ~c[(expt x (+ i j))], and ~c[floor] and ~c[mod]

       (include-book \"arithmetic-5/top\" :dir :system)
   ~ev[]
   But for a complete list of system books, ~pl[books] ~warn[].

   ~l[certify-book] ~warn[] to certify a file of events for reuse later.

   ~l[defconst] ~warn[] to define a new constant, allowing you to write a
   symbol, e.g., ~c[*weekdays*] in place of some object, e.g.,
   ~c['(MON TUE WED THU FRI)] in formulas.

   ~l[defmacro] ~warn[] to define a new syntactic abbreviation.  The macro facility in
   Lisp is quite powerful, allowing you to ~i[compute] the form to which some
   type-in expands.  For example, the primitive macro ~c[COND] is defined so
   that ~c[(COND ((P X) 1)((Q X) 2)(T 3))] expands to
   ~c[(IF (P X) 1 (IF (Q X) 2 3))].

   ~l[defstobj] ~warn[] to introduce a ~i[single-threaded object] that your functions may
   modify ``destructively'' provided they follow strict syntactic rules.

   ~l[events] ~warn[] for a complete list of the ACL2 events.  There are events to
   allow mutually recursive definitions, to introduce some new function symbols
   constrained to satisfy given axioms, to allow the temporary introduction of
   a ``local'' event to help prove some goal theorem and then disappear, to
   provide the power of first-order quantification and a choice operator, and
   many other features.

   There are also commands that allow you to inspect the world, e.g., to print the
   command that introduced a given name, to show all the commands back to a certain
   one, undo the last command or more generally roll-back to an earlier command.
   ~l[history] ~warn[].

   ~b[The Defthm Rule-Classes]

   We've already discussed the key role that rules play in controlling the
   behavior of the system.  New rules are introduced primiarily with the
   ~c[defthm] event, though ~c[defun] and other events may introduce rules.

   To prove ~i[formula] and generate, say a ~c[:rewrite] rule and a ~c[:generalize]
   rule from it, you would write
   ~bv[]
   (defthm ~i[name]
           ~i[formula]
           :rule-classes (:rewrite :generalize))
   ~ev[]
   If you wanted to rearrange the shape of the formula before generating the ~c[:rewrite] rule
   you could provide a ~c[:corollary] modifier to the ~c[:rewrite] rule class:
   ~bv[]
   (defthm ~i[name]
           ~i[formula]
           :rule-classes ((:rewrite :corollary ...)
                          :generalize)).
   ~ev[]

   There are many classes of rules, affecting different parts of the system.
   Each class is denoted by a keyword, e.g., ~c[:REWRITE], ~c[:LINEAR], etc.
   You are responsible for specifying the class(es) of rules to be generated
   from a given formula and several different rules (possibly of different
   classes) may be derived from a single formula.  Each class admits optional
   modifiers that allow you finer control over each rule.  Each class admits
   the ~c[:corollary] modifier with which you can rearrange the formula before
   a rule of that class is generated.  This allows you to state a theorem in
   its most elegant form for publication purposes but store it as a rule with
   the most appropriate hypotheses and conclusion.  Other modifiers tend to
   be specific to certain rule classes, but for example, ~c[:rewrite] rule
   modifiers include an optional limit on the depth of backchaining and
   options for handling free variables.

   We give some links below to other classes of rules.  However, we recommend
   that you not follow these links upon your first reading of this tutorial!

   ~l[REWRITE] ~warn[] for a description of how to create a rewrite rule.

   ~l[LINEAR] ~warn[]  for a description of how to store theorems concluding with
   arithmetic inequalities.  The trouble with storing
   ~bv[]
   (<= (len (delete e x)) (len x))
   ~ev[]
   as a rewrite rule is that it only matches instances of that inequality and
   thus fails to match 
   ~bv[]
   (<= (LEN (DELETE E X)) (+ 1 (LEN X)))
   ~ev[]
   ACL2 contains an extensible linear arithmetic decision procedure and by storing
   inequalities as ~c[:linear] rules you can make that decision procedure aware of
   the basic inequalities between non-primitive numerically valued terms.

   ~l[EQUIVALENCE] ~warn[], ~pl[CONGRUENCE] ~warn[], and ~pl[REFINEMENT]
   ~warn[] to learn how to introduce a new equivalence relation to the
   rewriter.  For example, suppose you define ~c[set-equal] so that it returns
   t precisely if its two arguments are lists containing the same elements,
   regardless of order or number of occurrences.  Note that under this sense of
   ``equivalence'', ~c[(rev x)] is the identity function and ~c[append] is
   commutative, for example.
   ~bv[]
   (set-equal (rev x) x)

   (set-equal (append x y) (append y x))
   ~ev[]
   You can make ACL2 use these two theorems as ~c[:rewrite] rules to replace
   instances of ~c[(REV x)] and ~c[(APPEND x y)] by ~c[set-equal] terms, even
   though the results are not actually ~c[EQUAL].  This is possible provided the
   target occurs in a context admitting ~c[set-equal] as a congruence relation.
   For example, the ~c[:congruence] rule:
   ~bv[]
   (implies (set-equal a b)
            (iff (member e a)
                 (member e b)))
   ~ev[]
   gives the rewriter permission to use the above ~c[set-equal] rules as
   rewrite rules in the second argument of any ~c[member] expression being used
   in a propositional way.

   ~l[ELIM] ~warn[] for a description of how to make the system adopt a
   ``change of variable'' tactic that can trade in ~i[destructor] functions for
   ~i[constructor] functions.  In analogy with how ACL2 eliminates ~c[(CAR X)]
   and ~c[(CDR X)] by replacing ~c[X] with ~c[(CONS A B)], you can make it
   eliminate other destructors.  For example, the system book
   ~c[\"arithmetic-5/top\"] provides an ~c[elim] rule that eliminates ~c[(floor x y)]
   and ~c[(mod x y)] by replacing ~c[x] by ~c[(+ r (* y q))], so that the
   ~c[floor] expression becomes ~c[q] and the ~c[mod] expression becomes ~c[r].
   When introducing your own ~c[elim] rules you will probably also need to
   introduce ~c[generalize] rules (see below) so that the new variables are
   appropriately constrained.

   ~l[GENERALIZE] ~warn[] for a description of how you can make ACL2 restrict the new
   variables it introduces when generalizing.  ACL2 will sometimes replace a
   term by a new variable and with ~c[generalize] rules you can insure that the
   new variable symbol has certain properties of the term it replaces.

   ~l[INDUCTION] ~warn[] for a description of how to tailor the inductions suggested by
   a term.  Most of the time when ACL2 chooses the ``wrong'' induction, the
   easiest fix is with a local ~c[:induct] hint (see below).  But if the same
   problem arises repeatedly in several theorems, you might want to ``educate''
   ACL2's induction heuristic.

   For a complete list of rule-classes, ~l[rule-classes] ~warn[].

   If you are reading this as part of the tutorial introduction to the theorem
   prover, use your browser's ~b[Back Button] now to return to
   ~il[introduction-to-the-theorem-prover].~/~/")

(deflabel introduction-to-hints
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   how to provide hints to the theorem prover~/

   We assume you've read ~il[introduction-to-rewrite-rules-part-1],
   ~il[introduction-to-key-checkpoints], and ~il[introduction-to-the-database].

   You may give the theorem prover a hint that is specific to a particular
   subgoal generated during a proof attempt.  Of course, you learn the name of the
   subgoal by inspecting the key checkpoints or other proof output.  You are not
   expected to anticipate the need for hints at specific subgoals; instead, you
   usually deduce that a hint is required because the subgoals is not proved but
   you see that existing rules and context make it provable.

   The most common hint is to enable and/or disable a particular rule on some
   particular subgoal.
   ~bv[]
   (defthm ~i[name]
           ~i[formula]
           :hints ((\"Subgoal *1/3.2''\" :in-theory (disable nth-nthcdr))))
   ~ev[]
   The hint above tells the rewriter that just before it begins to work on
   ~c[Subgoal *1/3.2''] it should switch to a local theory in which all of the
   rules generated from the event ~c[nth-nthcdr] are disabled.  That local
   theory remains the one in use for all descendent subgoals generated from the
   one named, until and unless one of those descendent subgoals has an
   ~c[:in-theory] hint associated with it.  There are many kinds of hints
   besides ~c[:in-theory] and in general, after each subgoal name, you can give
   various forms of advice and list various adjustments you wish to make to the
   context in which the prover is operating when it begins addressing the subgoal
   named.
   
   The top-level goal is always named ~c[Goal].  Thus
   ~bv[]
   (defthm ~i[name]
           ~i[formula]
           :hints ((\"Goal\" ...~i[hints1]...)
                   (\"Subgoal *1/3.2''\" ...~i[hints2]...)))
   ~ev[]
   has the effect of using ~i[hints1] for the top-level goal and all of its
   children throughout the entire proof, except for ~c[Subgoal *1/3.2''] and
   its children, where ~i[hints2] is used instead.  

   There are a few hints which ``take effect'' exactly on the subgoal to which
   they are attached and are not inherited by their descendents.

   Here is an incomplete list of some of the more common hints; we note the
   ones that do not pass on their effects to their descendents.  We recommend
   that you not follow the advanced links (marked ``~warn[]'') below until you
   have read the entire tutorial.

   ~l[in-theory] ~warn[]  for how to enable and/or disable rules.  The new theory is
   computed by a ``theory expression'' (~pl[theories] ~warn[]) such as
   ~c[(disable nth-nthcdr)] and typically makes adjustments such as additions
   or deletions to the global current theory.  All the relevant new theories
   are computed before the proof begins.  Thus, in
   ~bv[]
   (defthm ~i[name]
           ~i[formula]
           :hints ((\"Goal\" :in-theory (disable rule1))
                   (\"Subgoal *1/3.2''\" (disable rule2))))
   ~ev[]
   the theory mentioned for ~c[Goal] is the global current theory minus ~c[rule1],
   while the theory mentioned for its descendent, ~c[Subgoal *1/3.2''], is the global
   current theory minus ~c[rule2].  In particular, if both ~c[rule1] and ~c[rule2] are
   enabled in the global current theory, then ~c[rule1] is enabled during the 
   processing of ~c[Subgoal *1/3.2''] because it was not removed explicitly there.

   ~l[use] ~warn[] for how to force the theorem prover to take note of
   particular instances of particular theorems; in particular, the instances
   are created and added as hypotheses to the subgoal in question.  The hint is
   not inherited by the descendents of the subgoal
   (since the formula being proved has been modified by the hint).  If the rule
   you are using (with a ~c[:use] hint) is an enabled rewrite rule, it might interfere
   with the added hypothesis -- by rewriting itself to ~c[T] -- and thus often you will
   both ~c[:use ...] and ~c[:in-theory (disable ...)].

   ~l[expand] ~warn[] for how to tell the theorem prover to expand one or more
   function calls whenever encountered.

   ~l[cases] ~warn[] for how to force the theorem prover to do a case split to
   prove the subgoal under each of an exhaustive list of cases given in the
   hint.  This hint takes action specifically at the named subgoal and is not
   passed down to its children. 

   ~l[induct] ~warn[] for how to tell the theorem prover to go immediately into
   induction for the subgoal in question, and to use the induction scheme
   suggested by the hint rather than the one suggested by the terms in the
   subgoal itself.  This hint is not inherited by its descendents.

   ~l[hints] ~warn[] for a complete list of all hints, and
   ~pl[hints-and-the-waterfall] ~warn[] for a more thorough description of how
   the effects of hints at a subgoal are inherited by the descendents.

   If you are reading this as part of the tutorial introduction to the theorem
   prover, use your browser's ~b[Back Button] now to return to
   ~il[introduction-to-the-theorem-prover].~/~/")

(deflabel introduction-to-a-few-system-considerations
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   the mechanics of interaction with the theorem prover~/

   ACL2 is implemented in Common Lisp.  There are many different Common Lisps
   and they differ in details relating to interacting with the system.  We
   sometimes refer to the host Common Lisp as ``raw Lisp.''  The new user is
   advised not to operate in raw Lisp as it is possible to, say, redefine ACL2
   system faclities like ~c[defthm].

   Most people use Emacs (~pl[Emacs] ~warn[]) or the ACL2 Sedan (Eclipse) interface
   (~pl[ACL2-Sedan] ~warn[]).  They provide protection against certain common
   mistakes, e.g., trying to edit a block of input text after the operating
   system has buffered it up and sent it to the Lisp reader which is parsing it
   as you type.  More on this below.  In addition, the Sedan provides helpful
   syntax checking and a disciplined approach to the stack of lemmas generated
   by The Method.  But the variety of interfaces to the variety of Lisps mean
   that there is great variation in what one must type to interact with ACL2.

   The best example is perhaps trying to interrupt a running proof.  If your
   host Common Lisp is GCL or Allegro and you are typing directly to the Common
   Lisp process, then you can interrupt a computation by typing
   ``ctrl-c'' (hold down the Control key and hit the ``c'' key once).  But
   other Lisps may require some other control sequence.  If you are typing to
   an Emacs process which is running the GCL or Allegro Common Lisp process in
   a shell buffer, you should type ctrl-c ctrl-c.  If you are running the ACL2
   Sedan, you can use the ~i[Interrupt Session] button on the tool bar.  The
   environment you enter when you interrupt depends on various factors and
   basically you should endeavor to get back to the top level ACL2 command
   loop, perhaps by typing some kind of Lisp depenent ``abort'' command like
   ~c[A] or ~c[:q], or ~c[:abort!].  You can usually determine what environment
   you're in by paying attention to the prompt, which we discuss below.

   The ACL2 ``interactive loop'' is called ~ilc[LP] (~warn[]) and is generally
   invoked automatically from your Common Lisp when you start up the ACL2
   process.  ~c[LP] is just a special case of an ACL2 function called ~ilc[LD]
   ~warn[], which the user can call from within the ACL2 interactive loop to
   enter the loop recursively.  New users don't have to know this except that
   it helps explain why some commands have the string ``~c[-ld-]'' in their
   names!

   ACL2 presents itself as a ``read-eval-print'' loop: you're repeatedly
   prompted for some type-in, which is read, evaluated, and may cause some
   printing.  The prompt tells you something about ACL2's state.  In the
   standard environment, the prompt is
   ~bv[]
   ACL2 !>
   ~ev[]
   The ``~c[ACL2]'' tells you that the symbols you use in your command are
   those defined in the standard ACL2 namespace (or, in the jargon of Lisp, the
   ``current package,'' ~pl[current-package] ~warn[]).  You could create a new
   namespace (~pl[defpkg] ~warn[]) and set the current package to
   it (~pl[in-package] ~warn[]).  The next part of the prompt
   above (``~c[!]''), the exclamation mark) tells you that before ACL2
   evaluates your type-in it will check to see whether ~ilc[guard]s (~warn[])
   are respected, i.e., whether the functions used in your command are being
   supplied arguments in their ``expected domains.''  If evaluation is allowed
   by the guards, it proceeds exactly according to the ACL2 axioms; if
   evaluation is not allowed, an error is signaled.  ACL2 event commands check
   their arguments thoroughly at run-time, regardless of Lisp's notion of
   ``expected domains.''

   If the exclamation mark is missing from the prompt,
   ~bv[]
   ACL2 >
   ~ev[]
   then evaluation occurs strictly according to the ACL2 axioms, without regard for
   any declared guards.  

   You can switch between these two prompts by typing
   ~bv[]
   ACL2 !>:set-guard-checking nil
   ~ev[]
   to turn guard checking off and
   ~bv[]
   ACL2 >:set-guard-checking t
   ~ev[]
   to turn it on.  Try typing ~c[(car 7)] to each prompt.

   If there is a ``~c[p]'' in the prompt, 
   ~bv[]
   ACL2 p!>
   ~ev[]
   with or without the exclamation mark:
   ~bv[]
   ACL2 p>
   ~ev[]
   it means you are in ~c[:]~ilc[program] (~warn[]) mode rather than
   ~c[:]~ilc[logic] (~warn[]) mode.  In ~c[:program] mode, ~c[defun] just
   defines Common Lisp programs that you can evaluation but it adds no axioms
   and you cannot use such defined functions in theorems or invoke ~c[defthm].
   ~c[:Program] mode is often used to prototype a model.

   Most commands are just typical parenthesized Lisp expressions, like
   ~bv[]
   ACL2 !>(defthm rev-rev
            (implies (true-listp x)
                     (equal (rev (rev x)) x)))
   ~ev[]
   but some are typed as keywords followed by a certain number of arguments.

   For example, to undo the last event you may type
   ~bv[]
   ACL2 !>:u
   ~ev[]
   or to undo back through the introduction of ~c[rev] you may type
   ~bv[]
   ACL2 !>:ubt rev
   ~ev[]
   The first is equivalent to evaluating ~c[(u)] and the second is equivalent to
   evaluating ~c[(ubt 'rev)].  ~l[keyword-commands] ~warn[].  So if you see a sentence
   like ``to turn on the break rewrite facility, execute ~c[:brr t],'' we mean type
   ~bv[]
   ACL2 !>:brr t
   ~ev[]
   or equivalently
   ~bv[]
   ACL2 !>(brr t)
   ~ev[]

   If you see a prompt that doesn't look like those above you are probably not
   typing commands to the standard ACL2 read-eval-print loop!  If you've
   somehow called ~c[LD] recursively, the prompt ``gets deeper,'' e.g.,
   ~bv[]
   ACL2 !>>
   ~ev[]
   and you can pop out one level with ~c[:]~ilc[q] ~warn[] (for ``quit'') or
   pop to the outermost ACL2 loop with ~c[:]~c[abort!] ~warn[].  If you are in
   the outermost call of the ACL2 interactive loop and you type ~c[:q], you
   pop out into raw lisp.  The prompt there is generally different from the
   ACL2 prompt but that is outside our our control and varies from Lisp to
   Lisp.  We have arranged for many (but not all) Lisps to use a raw lisp
   prompt involving the string ~c[\"~[RAW LISP~]\"].  To get back into the
   ACL2 interactive loop from raw lisp, evaluate ~c[(LP)].

   If you see a prompt that looks like an ACL2 prompt but has a number in front
   of it, e.g.,
   ~bv[]
   1 ACL2 >
   ~ev[]
   then you're talking to the break rewrite facility (and you are 1 level deep
   in the example above).  Presumably at earlier time in this session you enabled
   that facility, with ~c[:brr t], installed a monitor on some rule, invoked the
   prover, entered the break, and forgot.  Everything you have done (e.g.,
   lemmas you might have proved with ~c[defthm]) inside that break will be lost
   when you exit the break.

   Since the break rewrite facility is ``ours'' we can tell you how to exit it!
   To exit our breaks and return to the top-level ACL2 loop, execute ~c[:abort!].

   If you discover you've been working in a ~c[brr] break, exit, turn off the
   break facility wih ~c[:brr nil], and redo whatever ~c[defun]s and
   ~c[defthm]s you did while in that break.

   Users of the Emacs interface may occasionally type commands directly in the ~c[*shell*]
   buffer running ACL2.  This can be ``dangerous'' for two reasons.  One is that
   if you type an event, like a ~c[defun] or ~c[defthm], directly to the shell,
   it will not be recorded in your ``script'' buffer and you may forget it in your
   final script.  The other is that if you attempt to edit a multi-line command on any
   but the most recent line, e.g., to correct the spelling of ~c[defthm] below
   after you've typed the ``~c[(implies (true-listp x)]'' you will confuse the
   Lisp parser because it has already read ``~c[(defth rev-rev]''.
   ~bv[]
   ACL2 !>(defth rev-rev
            (implies (true-listp x)
   ~ev[]
   This usually provokes the raw Lisp to enter a low level error break from which
   you must abort, possibly reenter the ACL2 loop, and re-type the corrected command
   from scratch.

   Another common mistake when using interfaces other than the ACL2 Sedan is to
   type an ill-formed ACL2 expression containing dots or commas, which also
   often provokes a break into the raw Lisp's error handler.

   The fundamental lesson is that you should pay attention to the prompt and learn what
   the different prompts mean -- or use the ACL2 Sedan.
   
   If you have been working your way through the tutorial introduction to the
   theorem prover, use your browser's ~b[Back Button] now to return to
   ~il[introduction-to-the-theorem-prover].~/~/")

(deflabel architecture-of-the-prover
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

  a simple overview of how the prover works~/

   Six built-in proof techniques are used by ACL2 to decompose the goal formula
   into subgoals.

   ~i[simplification] -- decision procedures and rewriting with previously
   proved rules, but actually including a host of other techniques under your
   control.  Simplification is the only proof technique that can reduce a
   formula to 0 subgoals (i.e., prove it) rather than just transform it to other
   formulas.  The predominant activity in most proofs is simplification.  There
   are many ways you can affect what the simplifier does to your formulas.
   Good users spend most of their time thinking about how to control the
   simplifier.

   ~i[destructor elimination] -- getting rid of ``destructor terms'' like
   ~c[(CAR X)] and ~c[(CDR X)] by replacing a variable, e.g., ~c[X], by a
   ``constructor'' term, e.g., ~c[(CONS A B)].  But you can tell ACL2 about new
   destructor/constructor combinations.

   ~i[cross-fertilization] -- using an equivalence hypothesis by substituting
   one side for the other into the conclusion
   ~i[and then throwing the hypothesis away].
   This is a heuristic that helps use an inductive hypothesis and prepare for
   another induction.

   ~i[generalization] -- replacing a term by a new variable and restricting
   the new variable to have some of the properties of the term.  You can
   control the restrictions imposed on the new variable.  This is a heuristic
   that prepares the goal for another induction.

   ~i[elimination of irrelevance] -- throwing away unnecessary hypotheses.
   This is a heuristic that prepares the goal for another induction.

   ~i[induction] -- selecting an induction scheme to prove a formula.  Inductions
   are ``suggested'' by the recursive functions appearing in the formula.  But you
   can control what inductions are suggested by terms.

   But you can add additional techniques, called ~i[clause processors].

   The various techniques are tried in turn, with simplification first and
   induction last.  Each technique reports one of three outcomes: it found
   nothing to change (i.e., the technique doesn't ~i[apply] to that subgoal),
   it decided to abort the proof attempt (typically because there is reason to
   believe the proof is failing), or it decomposed the goal into ~i[k]
   subgoals.

   The last outcome has a special case: if ~i[k] is 0 then the technique proved
   the goal.  Whenever ~i[k] is non-0, the process starts over again with
   simplification on each of the ~i[k] subgoals.  However, it saves up all the
   subgoals for which induction is the only proof technique left to try. That
   way you see how it performs on every base case and induction step of one
   induction before it launches into another induction.

   It runs until you or one of the proof techniques aborts the proof attempt or
   until all subgoals have been proved.

   Note that if simplification produces a subgoal, that subgoal is
   re-simplified.  This process continues until the subgoal cannot be
   simplified further.  Only then is the next proof technique is tried.  Such
   suboals are said to be ~i[stable under simplification].

   While this is happening, the prover prints an English narrative describing
   the process.  Basically, after each goal is printed, the system prints an
   English paragraph that names the next applicable proof technique, gives a
   brief description of what that technique does to the subgoal, and says how
   many new subgoals are produced.  Then each subgoal is dealt with in turn.

   If the proof is successful, you could read this log as a proof of the
   conjecture.  But output from successful proofs is generally never read
   because it is not important to The Method described in
   ~il[introduction-to-the-theorem-prover].

   The output of an unsuccessful proof attempt concludes with some ~i[key]
   ~i[checkpoints] which usually bear looking at.

   ~/~/")

(deflabel frequently-asked-questions-by-newcomers
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   some questions newcomers frequently ask~/

   This FAQ is for people who've read through all the other sections of the
   tutorial introduction to the theorem
   prover (~pl[introduction-to-the-theorem-prover] and all the links from it
   that are not marked with the little warning sign (``~warn[]'').  Do not
   expect to understand our answers if you haven't taken the time to read
   through the tutorial.  In the answers below you will see more links into the
   hypertext reference manual.  While such links were marked ``~warn[]'' in the
   tutorial, they are not marked that way here.  When you enter the reference
   manual be prepared to explore and assemble a mini-course on the topic of
   interest, not a quick fix.

   ~b[Q].  How do I find something in the ~b[ACL2 documentation]?
   ~b[A].  Try going to the Search link on the ACL2 home page.

   ~b[Q].  How does the theorem prover work?  ~b[A].  We really don't think you
   need to know much about the inner workings of the prover to become an effective
   user.  That doesn't mean the system is self-explanatory!  It means that stuff you
   need to learn is not how the theorem prover works but how to interact with it!
   That is what ~il[introduction-to-the-theorem-prover] is about.
   However, if you want the most basic overview of the prover, ~pl[architecture-of-the-prover].

   ~b[Q]. How do I ~b[define a new function]?  
   ~b[A]. ~l[defun].

   ~b[Q]. How do I ~b[define a new predicate]?  ~b[A]. ~l[defun].

   ~b[Q]. How do I ~b[define a new relation]?  ~b[A]. ~l[defun].

   ~b[Q]. How do I define a ~b[function or predicate that takes a varying number of arguments]?
   ~b[A]. You can't.  However, ~pl[defmacro] to learn
   how to define a macro that takes a varying number of arguments and expands
   into an arbitrary term that you compute.

   ~b[Q]. How do I define a ~b[macro that is sensitive to the state]?  ~b[A].
   You can't.  However, advanced users should consider ~ilc[make-event].

   ~b[Q]. How do I define ~b[mutually recursive] functions?  ~b[A].
   ~l[mutual-recursion].  However, you should realize that when two functions,
   say ~c[f] and ~c[g], are mutually recursive, properties of ~c[f] generally
   have to be stated simultaneously with properties of ~c[g], since inductive
   proofs about one function require inductive hypotheses about the other.
   Furthermore, ACL2 does not know how to do inductions for mutually recursive
   functions and must be told.  ~l[mutual-recursion-proof-example].

   ~b[Q]. How do I declare the ~b[type signature of a function]?  ~b[A].
   You can't.  ACL2 is a syntactically untyped language and all functions are
   defined on all objects in the ACL2 universe.  We recommend that the new user
   get used to this and only then explore the use of ACL2 to express and
   enforce a type regime.  In ACL2, the ~i[guard] of a function is akin to the
   type signature of a function in typed languages.  However, ACL2 guards may
   be arbitrary terms, not just type conditions, they only concern the inputs
   to the function (not its result), and do not affect the axiom defining the
   function -- all functions are defined on every combination of objects.  You
   may, of course, prove theorems that establish that every function called in
   a definition or theorem is supplied with input satisfying its guards (which
   necessarily involves describe the outputs too).  These formulas are called
   ~i[guard conjectures] and the process of proving them is called ~i[guard verification].
   Since guards are arbitrary ACL2 formulas, the ``type
   regimes'' one tends to enforce in ACL2 can be much for flexible and
   expressive than those in most programming languages.  However, that
   expressibility also means guard verification can be challenging
   (indeed undecidable).  On the other hand, if one limits oneself to simple
   type-like guards, lemmas can be proved that make most guard verification
   fully automatic and one can configure ACL2 to do guard verification
   automatically at ~c[defun]-time.  One may also delay guard verification
   until ``the right'' lemmas have been proved.  By doing guard verification
   one can make functions execute faster by allowing the code to avoid runtime
   checks.  This is especially valuable to industrial users who have large
   models used both in verification and as simulation engines for designed
   artifacts.  In addition, guard verification can give you the assurance that
   you are using your functions within their intended domains and hence is a
   form of functional specification and verification.  However, all these
   advantages aside, it is remarkably easy to drift away from the simplest type
   regimes and write a guard that raises deep mathematical problems.  New users
   should not try to confront these problems until they are comfortable with
   the theorem prover and with lemma development.  Therefore, we ~b[strongly]
   recommend that you forget about types and guards and get used to reasoning
   about total functions.  When you do decide to learn about them, be prepared
   for a complex story involving specification, execution efficiency,
   and proof management.  ~l[guard].

   ~b[Q]. How do I tell ~c[defun] ~b[what measure to use]?
   ~b[A]. ~l[xargs], specifically ~c[:measure].

   ~b[Q].  I specified a measure that always returns a natural number but ACL2
   is acting like it's not a natural number.  ~b[A].  There are two likely problems.
   The most likely one is that your measure isn't really always a natural!
   Suppose the formals of your ~c[defun] are ~c[x] and ~c[y] and your measure
   is ~c[(m x y)].  Suppose the recursive calls of your function are protected
   by tests that insure that ~c[x] and ~c[y] are naturals.  Then you might
   assume ~c[x] and ~c[y] are naturals in the measure.  But
   ACL2 has to prove ~c[(o-p (m x y))], where ~ilc[o-p] is the
   predicate that recognizes ordinals (and naturals are ordinals).  Note that the
   theorem doesn't have any hypotheses!  You might intuitively think that your measure
   has to be an ordinal just under the conditions that lead to recursive calls.  That's not
   what ACL2 enforces.  It has to be an ordinal, always.  So you must change your
   specified measure.  For example, consider wrapping ~ilc[nfix] around it or around
   its uses of ~c[x] and ~c[y] to coerce those quantities to naturals.  The second most likely
   explanation is that your measure returns a natural, always, but ACL2 doesn't know that and it
   takes induction to prove.  This might happen if ~c[m] involves some recursive functions.
   In this case, prove ~c[(natp (m x y))] before your ~c[defun].  Perhaps you should
   consider making the ~c[natp] lemma a ~c[:]~ilc[type-prescription] lemma to make ACL2's
   typing algorithm aware of it.

   ~b[Q]. How do I tell ~c[defun] ~b[what well-founded relation to use]?
   ~b[A]. ~l[xargs], specifically ~c[:well-founded-relation].

   ~b[Q]. How do I show that a ~b[relation is well-founded]?
   ~b[A]. Prove a theorem establishing that there is an order preserving embedding into the
   ordinals and store it with ~c[:rule-classes] ~c[:]~ilc[well-founded-relation].

   ~b[Q].  What is an ~b[ordinal]?  What does it mean to be
   ~b[well-founded]?  ~b[A].  Ordinals are an extension of the natural
   numbers used to insure that a process can't go on forever.  Like naturals,
   they can be added, multiplied, and exponentiated.  There is a sense of one
   ordinal being less than another.  Unlike the naturals, each of which is
   finite, the ordinals include infinite objects.  Now imagine ``standing'' on
   an ordinal and ``stepping'' to a smaller one.  Like the naturals, this
   ``walk down the ordinals'' can't go on forever, even if you start on an
   infinite ordinal.  That is because the ordinals are ~i[well-founded].  See
   ~ilc[o-p] for more information about ordinals in ACL2 and about
   well-foundedness.  ~l[ordinals] for a deeper discussion and a discussion of
   books that can help configure ACL2 to reason about ordinals.

   ~b[Q]. How can provide ~b[hints for the termination proofs] in ~c[defun]?
   ~b[A]. ~l[xargs], specifically ~c[:hints] (for the termination proofs) and
   ~c[:guard-hints] (for the guard verification proofs).

   ~b[Q]. How do I define a ~b[constant] (something like a ~b[global variable])?
   ~b[A]. ~l[defconst].  But remember that as an applicative
   programming language, ACL2 does not have global variables!  You can define a
   symbol to have a fixed value and use the symbol sort of like a global
   variable in function definitions: you may refer to the value of the symbol
   in your functions without passing the variable in as formal parameter.  But
   you may not ever change the value of the symbol!

   ~b[Q]. How do I save the value of a top-level computation for future use?
   ~b[A]. ~l[assign] and ~pl[@].

   ~b[Q]. How do I introduce ~b[new syntactic form] or ~b[abbreviation]?
   ~b[A]. ~l[defmacro].

   ~b[Q].  How can create and modify an array?  ~b[A].  ACL2 is a functional
   language, so it is impossible to destructively modify an existing object;
   technically, all ``updates'' to objects must be implemented by ``copy-on-write''
   semantics.  That said, ACL2 provides support for ~il[arrays], provided you
   use them in a restricted way.  They give you constant-time access and
   change under the use restrictions.

   ~b[Q].  How do I read from or write to a file?  How do I do IO?  ~b[A].
   To manipulate files, your function must have ~ilc[state] as an argument, so
   you should read about the restrictions that imposes.  For input/output
   facilities, ~pl[io].

   ~b[Q]. How do I define a ~b[structure that can be destructively modified]?
   ~b[A]. ACL2 is an ~i[applicative programming language].  You can't modify
   objects arbitrarily!  You basically have to ``copy on write,'' which means
   you construct new objects from old ones, making the changes you want in the
   new one.  If the ~c[car] of some object is ~c[1] at one moment and ~c[2]
   later, then the basic logical axiom ~c[(car x)] = ~c[(car x)] is violated!
   However, if the only reference to the old object, e.g., ~i[x], was to pass
   it to the code that copied and ``changed'' it, then ACL2 can re-use the old
   object to produce the new one and the axioms would not object.  Such
   syntactic restrictions can make ~i[x] a modifiable structure but they will
   impose a heavy burden on you as a programmer: if pass such an ~i[x] to a
   function and the function modifies it, then you must pass ~i[x] only to that
   function and you must return the modified value and use it henceforth.  Such
   objects are said to be ~i[single threaded].  ~l[defstobj].

   ~b[Q].  How do I write a universal quantifier?  An existential quantifier?
   How can I say ``for all'' or ``there exists''?  ~b[A]  You can't literally
   write quantifiers.  But ACL2 has the power of full first order logic with
   quantification.  ~l[quantifiers].

   ~b[Q].  How do I introduce an undefined or uninterpreted function symbol?
   Can I constrain it to have certain properties?  ~b[A].  ~l[encapsulate].

   ~b[Q].  How can I hide a lemma?  I want to prove a lemma temporarily
   to use in another proof but I don't want the lemma around thereafter.
   ~b[A].  One way to get a similar effect is to prove the lemma and then
   disable it with an ~c[(in-theory (disable ...))] event; ~pl[in-theory].
   Another way is to put the lemma and the theorem that needs it into an
   ~ilc[encapsulate] and wrap a ~ilc[local] around the lemma.

   ~b[Q]. What is an ~b[event]?  ~b[A]. An ~i[event] is a command that adds
   information to the ACL2 database (the ``logical world''), like ~c[defun] or
   ~c[defthm].  ~l[events].

   ~b[Q]. How do I say that I ~b[do not want a rewrite rule] generated from a
   theorem?  ~b[A]. The command
   ~bv[]
   (defthm ~i[name] ~i[formula]
           :rule-classes nil)
   ~ev[]
   will attempt to prove ~i[formula] and, if successful,
   give ~i[formula] the name ~i[name], which you may use in hints as a
   theorem, but it will build no rules from the formula.

   ~b[Q]. How do I say that I want a formula to be ~b[stored as a rewrite rule]?
   ~b[A]. The command
   ~bv[]
   (defthm ~i[name] ~i[formula])
   ~ev[]
   will attempt to prove ~i[formula] and, if successful, it will give ~i[formula] the
   name ~i[name] and generate a rewrite rule from it, with the runic name
   ~c[(:rewrite ]~i[name])].  It could happen that ~i[formula] generates more
   than one rewrite rule, e.g., this happens if the conclusion is an ~c[AND].  In
   this case, each conjunctive branch through the conclusion generates a rule
   named ~c[(:rewrite ]~i[name]~c[ . i)], for ~i[i]=1,2,...  For more details,
   ~pl[rewrite].

   ~b[Q]. How do I say that I want a formula to be ~b[stored as a rewrite rule]
   ~b[and some other kinds of rules]?  ~b[A]. The command
   ~bv[]
   (defthm ~i[name] ~i[formula]
           :rule-classes (~i[:class1] ... ~i[classk]))
   ~ev[]
   will attempt to prove ~i[formula] and, if successful, it
   will give ~i[formula] the name ~i[name] and generate a rule of each
   ~i[:classi] specified.  Each ~i[:classi] should either be a keyword, like
   ~c[:REWRITE] or ~c[:GENERALIZE], naming a rule class (~pl[rule-classes]), or
   else should be a list that starts with a rule class and then lists the
   relevant modifiers.  Be sure to include ~c[:REWRITE] among the rule classes
   if you want the formula to generate a rewrite rule.  It doesn't do that
   automatically if you explicitly specify ~c[:rule-classes]!

   ~b[Q]. How do I ~b[rearrange] the shape of a formula before generating a
   rule from it?  ~b[A]. ~l[rule-classes] and read about the ~c[:corollary]
   modifier.

   ~b[Q]. What is a ~b[type-prescription]?  ~b[A]. ACL2 has an algorithm for
   determining the type of object returned by a term, where a type is one of the Common Lisp
   primitive datatypes such as natural, integer, Boolean, cons, true-listp, etc.
   Rules provided by you can influence this algorithm.  ~l[type-prescription].

   ~b[Q]. How do ~b[rewrite rules work]?  ~b[A]. Re-read the tutorial
   sections: ~il[introduction-to-rewrite-rules-part-1] and
   ~il[introduction-to-rewrite-rules-part-2].

   ~b[Q]. How do I ~b[see what's in the database]?  ~b[A]. You can't look at
   the entire database with user-friendly tools.  You can print the command
   that introduced a particular name, print the entire sequence of user
   commands, print the commands in the region between two commands, print all
   the rewrite rules that apply to a given term or function symbol, and many
   other options.  ~l[history].  If you have loaded a book from another user,
   you might wish to read the source file.  For example, the source file for
   ~c[(include-book \"arithmetic-5/top\" :dir :system)] is the file named
   ~c[arithmetic-5/top.lisp] on the ~c[acl2-sources/books/] directory where
   ever your ACL2 sources are installed.  Often, books are well-documented by
   comments by their authors.  Some books have ~c[Readme] or ~c[README] files
   on the same directory.

   ~b[Q]. How do I ~b[undo] a command?  ~b[A]. ~l[history], especially
   ~pl[u] (``undo'') and ~pl[ubt] (``undo back through''). ~b[Q]. What
   ~b[rewrite rules match] a given term?  ~b[A]. ~l[pl].

   ~b[Q].  What were those ~b[questions to ask when looking at key checkpoints]?
   ~b[A].  ~l[introduction-to-key-checkpoints].

   ~b[Q]. How do I figure out ~b[why a rewrite rule won't fire]?  ~b[A]. If you
   activate rewrite rule monitoring (~pl[brr]) and then install a
   monitor (~pl[monitor]) on the rule in question, ACL2 will enter an
   interactive break whenever the pattern of the rule is matched against a
   target in a proof.  So after installing the monitor, re-try the proof and
   then interact with the rewriter via break commands (~pl[brr-commands]).
   Like all trace and break packages, you have to know what you're doing to use
   the break rewrite facility, so read the material in the reference manual.
   If no interactive break happens after you've installed the monitor on your
   rule and re-tried the proof, it means no suitable target ever arose.  Don't
   forget to turn off monitoring when you're done as it slows down the system.

   ~b[Q]. ~b[Why is a proof taking so long?]  ~b[A]. Unexpectedly poor
   performance on simple problems is usually a sign of cyclic rewriting or
   combinatoric explosion.  ~l[dmr] and ~pl[accumulated-persistence].

   ~b[Q]. How do I tell ACL2 ~b[what induction to do] for a particular
   formula?  ~b[A]. When issuing the ~c[defthm] command for the formula, supply
   an ~c[:induct] hint:
    ~bv[]
   (defthm ~i[name]
           ~i[formula]
           :hints ((\"Goal\" :induct (f x1 ... xn))))
   ~ev[]
   where ~c[f] is a function that recurs the way you want the induction to
   unfold and ~c[x1 ... xn] are the relevant variables in ~i[formula].  You
   usually have to define ~c[f] appropriately for each formula that needs an
   induct hint, though sometimes you can re-use an earlier ~c[f] or one of the
   functions in the formula itself.  It doesn't matter what value ~c[(f x1 ... xn)]
   returns.  All that matters is how it recurs.  The termination
   analysis for ~c[f] justifies the induction done.  ~l[hints], especially the
   section on ~c[:induct] hints; also ~pl[induction].

   ~b[Q]. ACL2 doesn't know ~b[simple arithmetic] that can simplify the term
   ~c[(+ 1 -1 x)].  ~b[A]. You should load an arithmetic book whenever you're dealing
   with an arithmetic problem.  The simplest arithmetic book is loaded with the
   event ~c[(include-book \"arithmetic/top-with-meta\" :dir :system)].  If
   you're using ~c[floor] and ~c[mod] or non-linear arithmetic like ~c[(* x y)]
   you should use ~c[(include-book \"arithmetic-5/top\" :dir :system)].  See
      also the discussion of arithmetic books under the ``Lemma Libraries and
   Utilities'' link of the ACL2 home page.

   ~b[Q]. ACL2 is not using an ~b[arithmetic lemma] that I proved.
   ~b[A]. Lemmas concluding with arithmetic inequalities, like
   ~bv[]
   (implies (member e x)
            (< (len (delete e x)) (len x)))
   ~ev[]
   are not good rewrite rules because they rarely match targets because of intervening
   arithmetic operators.  For example, the above conclusion doesn't match
   ~c[(< (LEN (DELETE E X)) (+ 1 (LEN X)))].  You should store such lemmas as
   ~c[:linear] rules by using the command:
   ~bv[]
   (defthm len-delete
     (implies (member e x)
              (< (len (delete e x)) (len x)))
     :rule-classes :linear)
   ~ev[]
   ~l[linear].

   ~b[Q].  What is a ~b[linear rule]?
   ~b[A].  ~l[linear].

   ~b[Q]. How do I make ACL2 ~b[treat a relation as an equality]?  ~b[A]. We
   assume you mean to treat the relation as an equivalence, i.e., replace one
   term by another when they are equivalent under your relation.
   ~l[equivalence], ~pl[congruence], and ~pl[refinement].

   ~b[Q]. One of my rewrite rules has a ~b[hypothesis that doesn't rewrite]
   to true.  What do I do?  ~b[A]. Prove a rewrite rule that establishes that
   hypothesis under the relevant assumptions from the context of the intended
   target.  Alternatively, undo the rule and restate it with a ~ilc[force]
   around the problematic hypothesis, making ACL2 assume the hypothesis when
   the rule is applied and raising the truth of the hypothesis as an explicit
   subgoal of the proof.  See also ~ilc[case-split].  Of course, you should
   always state the strongest rewrite rules you can think of, eliminating hypotheses
   or shifting them to the right-hand side inside of ~c[IF]s; ~pl[strong-rewrite-rules].

   ~b[Q]. How do I make ACL2 ``guess'' the ~b[right instantiation of a free variable]?
   ~b[A]. You can provide a ~c[:restrict] hint that names the problematic
   lemma and provides an instantiation of the free variable.  ~l[hints],
   specifically ~c[:restrict].  You could alternatively give a hint that
   ~c[:uses] the rule and provides the appropriate instantiation in full.
   ~l[hints], specifically ~c[:use].  Recall that ACL2 guesses free variable
   instantiations by matching the problematic hypothesis to the assumptions in
   the context of the target.  If the appropriate assumption is present but
   ACL2 is finding another one, try undoing the problematic rule and proving it
   again, specifying the ~c[:match-free :all] modifier of the ~c[:rewrite] or
   ~c[:linear] rule class.  ~l[rule-classes].  Alternatively, undo and prove the
   problematic rule again and use a ~ilc[bind-free] form to compute the
   appropriate instantiation.

      ~b[Q]. How can I make ACL2 do a ~b[case split] to prove a certain subgoal?
   ~b[A]. ~l[hints], specifically ~c[:cases].

   ~b[Q]. How can I ~b[prevent ACL2 from using a rewrite rule]?  ~b[A].
   ~l[hints], specifically ~c[:in-theory (disable ...)].  If the use of the
   rule is problematic in only one subgoal and the lemma is needed in other subgoals,
   disable the lemma only in the problematic subgoal by specifying the subgoal name (e.g.,
   ~c[\"Subgoal 1/3.2.1\"]) as the goal specifier in the hint.  If the rule
   isn't needed anywhere in the proof, you could use the specifier
   ~c[\"Goal\"].  If you don't think the rule will ever be needed for a while,
   you could globally disable it with the event ~c[(in-theory (disable ...))]
   (~pl[in-theory]) executed before the first problematic proof.  If the
   rule has never been used or must always be disabled, undo it and prove it
   again with ~c[:]~ilc[rule-classes] ~c[nil].

   ~b[Q].  How can I prevent ACL2 from running a definition on constants?
   I tried disabling the function but that didn't work.  ~b[A].
   If you have a function named ~c[f] then disabling ~c[f] will disable the
   definitional axiom about ~c[f].  But ACL2 has another kind of rule about
   ~c[f], telling it how to evaluate ~c[f].  The ~il[rune] of this rule is
   ~c[(:executable-counterpart f)].  Try disabling that, as in the ~c[:]~ilc[hints] ~c[((]...
   ~c[:in-theory (disable  (:executable-counterpart f)) ...~c[))].

   ~b[Q]. How can I make ACL2 ~b[use a rule] in a proof?  
   ~b[A]. ~l[hints], specifically ~c[:use].

   ~b[Q].  How can I make ACL2 expand a function call in a proof?
   ~b[A].  You can give an ~c[:]~l[expand] hint.

   ~b[Q].  ACL2 sometimes aborts the proof attempt before showing me all of the
   subgoals.  How can I make it just keep going instead of aborting early?
   ~b[A]. ~l[otf-flg], which stands for Onward Thru the Fog FLaG.

   ~b[Q]. How can I ~b[compute when I want a rule to fire]?  ~b[A].
   ~l[syntaxp].

   ~b[Q].  How can I add ~b[pragmatic advice to a lemma after it has been proved]?
   For example, how can add a forced hypothesis, a backchain limit, or a
   ~c[syntaxp] test?  ~b[A].  You can't.  You can undo the lemma, restate it
   appropriately, and prove it again.  This produces the cleanest database.
   Alternatively, you can prove the restated lemma under a new name -- a
   task that should be easy since the old version is in the database and will
   presumably make the proof trivial -- and then disable the old name.

   ~b[Q]. How can I ~b[stop ACL2 from rewriting a term]?  ~b[A]. If you need
   rewriting done but want to prevent some particular terms from being
   rewritten, ~pl[hints], specifically ~c[:hands-off].  Alternatively, consider
   embedding the problematic term in a ~ilc[hide].  Users sometime develop
   special theories (~pl[theory]) containing just the rules they want and
   then use hints to switch to those theories on the appropriate subgoals.

   ~b[Q].  Can I ~b[compute which subgoals a hint refers to]?
   ~b[A].  Yes, ~pl[computed-hints].  This topic is for advanced users but knowing
   that it is possible might come in handy someday.

   ~b[Q].  I want the rewriter to ~b[always use one theory and then switch to another] so that
   it doesn't use my most complicated before until doing the simple things.
   ~b[A].  This is possible but is something for the advanced user.  It can be done
   using a form of ~il[computed-hints].  ~l[using-computed-hints-7].

   ~b[Q].  Is there a way to attach ~b[the same hint to every defthm]?
   ~b[A].  ~l[default-hints].

   ~b[Q].  How can I just tell ACL2 the proof steps?  ~b[A].  ~l[verify] and 
   ~pl[proof-checker].

   ~b[Q]. How can I write ~b[my own simplifier]?
   ~b[A].  ~l[meta].

   ~b[Q]. How can I add an axiom or just assume some lemma without proof?
   ~b[A]. This is very dangerous but is a good strategy for exploring whether or
   not a certain set of lemmas (and their rules) is sufficient to prove your goal.
   ~l[defaxiom] and ~pl[skip-proofs].

   ~b[Q]. How can redefine a user-defined function?  ~b[A].  This is tricky.  What if
   you've already proved theorems about the old definition and then wish to change it?
   There are several options.  ~l[ld-redefinition-action] (and note specifically the
   discussion of updater function for it, ~c[set-ld-redefinition-action]); also 
   ~pl[redef], ~pl[redef!], ~pl[redef+],  and ~pl[redef-].

   ~b[Q]. How do I ~b[change a function from] ~c[:program] ~b[mode to]
   ~c[:logic] ~b[mode]?  ~b[A]. ~l[verify-termination].

   ~b[Q]. How do I ~b[change the guards] on a function?  ~b[A]. You can't.
   Undo it and redefine it.

   ~b[Q]. What is ~b[program mode]?
   ~b[A]. ~l[program].

   ~b[Q]. What does the ACL2 ~b[prompt] mean?  ~b[A].
   ~l[introduction-to-a-few-system-considerations] or, specifically, ~pl[prompt].

   ~b[Q]. What is ~b[logic mode]?
   ~b[A]. ~l[logic].

   ~b[Q]. How do I ~b[get into or out of] ~c[:program] ~b[mode?]  ~c[:Logic]
   ~b[mode?]  ~b[A]. ~l[program] and ~pl[logic].  You can enter these modes
   temporarily for a particular ~ilc[defun] by using
   ~c[(declare (xargs :mode :program))] or ~c[(declare (xargs :mode :logic))]
   after the list of formal parameters to the definition.

   ~b[Q].  How do I quit from ACL2?  ~b[A].  This varies depending on the
   interface you're using.  ~l[introduction-to-a-few-system-considerations].

   ~b[Q]. How do I ~b[load a file] of definitions and theorems created by
   someone else?  ~b[A]. ~l[include-book].

   ~b[Q]. How do I ~b[create my own book] of definitions and theorems?
   ~b[A]. ~l[books].

   ~b[Q]. Where are the ``distributed books'' referenced by ~b[:dir :system]
   on my machine?  ~b[A]. If your ACL2 is installed on the directory
   ~i[dir]~c[/acl2-sources], then the distributed books are the files under the
   directory ~i[dir]~c[/acl2-sources/books/].

   ~b[Q]. How can I find out ~b[what books are available]?  ~b[A]. Go to the
   ACL2 home page, ~c[http://www.cs.utexas.edu/u/moore/acl2/] and look at the
   link labeled ``Lemma Libraries and Utilities.''

   ~b[Q]. How do I ~b[produce my own book]?
   ~b[A]. ~l[books].

   ~b[Q]. What is a ~b[decision procedure]?  What ~b[decision procedures does ACL2 have]?
   ~b[A]. A ~i[decision procedure] is an algorithm that given
   enough time and space can determine, for all the formulas in a certain
   syntactic class of formulas, whether the formula is a theorem or not.  The
   most well-known decision procedure is for propositional calculus: by testing
   a formula under all the combinations Boolean assignments to the variables,
   one can decide if a propositional formula is a theorem.  The syntactic class
   consists of all formulas you can write using just variables, constants, and
   compositions of the functions ~c[and], ~c[or], ~c[not], ~c[implies],
   ~c[iff], and ~c[if].  There are, of course, an exponential number of
   different assignments so the algorithm can be slow.  ACL2 contains a
   propositional decision procedure based on symbolic normalization that can be
   faster than trying all the combinations of truthvalues -- but is not
   guaranteed to be faster.  ACL2 also contains an optional ~il[bdd] procedure.
   ACL2 also contains a decision procedure for rational arithmetic involving
   variables, rational constants, addition, multiplication by rational
   constants, equality, and the various versions of arithmetic
   inequality (~c[<], ~c[<=], ~c[>=], and ~c[>]).  It can be extended with
   ~c[:]~ilc[linear] lemmas.  ACL2 is complete for equality over
   uninterpreted (e.g., undefined and unconstrained) function symbols using an
   algorithm based on transitive closure of equivalence classes under
   functional substitutivity.  Finally, you can make ACL2 use other decision
   procedures, even ones implemented outside of ACL2; ~pl[clause-processor].

   ~b[Q]. ACL2 has the ~b[change of variable] trick (~b[destructor elimination])
   that it does to get rid of ~c[(CAR X)] and ~c[(CDR X)] by
   replacing ~c[x] by ~c[(CONS A B)].  Is there a way to make ACL2 do that for
   other terms?  ~b[A]. Yes.  ~l[elim].

   ~b[Q]. How can I ~b[prevent destructor elimination]?
   ~b[A]. ~l[hints], specifically ~c[:do-not '(eliminate-destructors)].

   ~b[Q]. How can I ~b[prevent cross-fertilization]?
   ~b[A]. ~l[hints], specifically ~c[:do-not '(fertilize)].

   ~b[Q]. How can I ~b[prevent generalization]?
   ~b[A]. ~l[hints], specifically ~c[:do-not '(generalize)].

   ~b[Q]. How can I make ACL2 ~b[impose a restriction on a new variable]
   introduced by destructor elimination or generalization?  ~b[A].
   ~l[generalize].

   ~b[Q]. What ~b[rule classes] are there?
   ~b[A]. ~l[rule-classes].

   ~b[Q]. What is a ~b[theory]?
   ~b[A]. ~l[theories].

   ~b[Q]. How are ~b[hints inherited by the children of a subgoal]?
   ~b[A]. ~l[hints-and-the-waterfall].

   ~b[Q].  How do I use ACL2 under ~b[Emacs]?  ~b[A]. ~l[emacs].

   ~b[Q].  How do I use ACL2 under ~b[Eclipse]?  ~b[A]. ~l[ACL2-Sedan].

   ~b[Q].  How do I interrupt the prover?  
   ~b[A].  The keyboard sequence for interrupting a running process depends your
   operating system, host Common Lisp, and user interface (e.g., Emacs, Eclipse, etc.).
   But perhaps a few examples will help you discover what you need to know.
   If your host Common Lisp is GCL or Allegro and you are typing
   directly to the Common Lisp process, then you can interrupt a computation by
   typing ``ctrl-c'' (hold down the Control key and hit the ``c'' key once).
   But other Lisps may require some other control sequence.  If you are typing
   to an Emacs process which is running the GCL or Allegro Common Lisp process
   in a shell buffer, you should type ctrl-c ctrl-c -- that is, you have to type the
   previously mentioned sequence twice in succession.  If you are running the
   ACL2 Sedan, you can use the ~i[Interrupt Session] button on the tool bar.
   The environment you enter when you interrupt depends on various factors and
   basically you should endeavor to get back to the top level ACL2 command
   loop, perhaps by typing some kind of Lisp depenent ``abort'' command like
   ~c[A] or ~c[:q], or ~c[:abort!].  You can usually determine what environment
   you're in by paying attention to the prompt.

   ~b[Q].  What is the ~b[ACL2 loop]?  ~b[A].  That is the name given to the
   interactive environment ACL2 provides, a ``read-eval-print loop'' in which
   the user submits successive commands by typing ACL2 expressions and keyword
   commands.  ~l[introduction-to-a-few-system-considerations].

   ~b[Q].  What is ~b[raw lisp]?  ~b[A].  That is our name for the host
   Common Lisp in which ACL2 is implemented.
   ~l[introduction-to-a-few-system-considerations].  There is an ACL2 mode
   named ~i[raw mode] which is different from ``raw lisp.''  ~l[set-raw-mode].

   ~b[Q].  Can I get a tree-like view of a proof?  ~b[A].  ~l[proof-tree] for an
   Emacs utility that displays proof trees and allows you to navigate through a proof
   from the proof tree.  The ACL2 Sedan also supports proof trees and you should see
   the ACL2s documention on that topic.

   ~b[Q].  I used the earlier Boyer-Moore theorem prover, Nqthm.  How is
   ACL2 different?  ~b[A]. ~l[nqthm-to-acl2].

   If you are reading this as part of the tutorial introduction to the theorem
   prover, use your browser's ~b[Back Button] now to return to
   ~il[introduction-to-the-theorem-prover].~/~/")



(deflabel introductory-challenges
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   challenge problems for the new ACL2 user~/

   Do each of the problems.  In each case, start with a fresh ACL2 (or undo all effects of
   previous events with ~c[:ubt! 1]).  This may require that you ``re-discover'' the same
   lemma more than once in different problems, but recognizing the need for something you
   used in some previous project is part of the training.

   We recommend that you follow The Method and consult the documentation as
   needed -- but that you not look at our answers until you're well and truly
   baffled!

   ~l[introductory-challenge-problem-1]  (Answer: ~il[introductory-challenge-problem-1-answer])

   ~l[introductory-challenge-problem-2]  (Answer: ~il[introductory-challenge-problem-2-answer])

   ~l[introductory-challenge-problem-3]  (Answer: ~il[introductory-challenge-problem-3-answer])

   ~l[introductory-challenge-problem-4]  (Answer: ~il[introductory-challenge-problem-4-answer])

   In addition to these explicit challenge problems designed for beginners, the ACL2
   documentation has many example solutions to problems (not always phrased in the
   question/answer format here).  If you are looking for other examples, you should
   consider

   ~il[annotated-acl2-scripts] (Answer:  the answers are given in the examples)

   When you've done the problems and compared your solutions to ours, use your
   browser's ~b[Back Button] now to return to
   ~il[introduction-to-the-theorem-prover].

   ~/~/")

(deflabel introductory-challenge-problem-1
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   challenge problem 1 for the new user of ACL2~/

   Start in a fresh ACL2, either by restarting your ACL2 image from scratch or
   executing
   ~bv[]
   :ubt! 1
   ~ev[]
   which will undo everything since the first user event.

   Then define this function:
   ~bv[]
   (defun rev (x)
     (if (endp x)
         nil
         (append (rev (cdr x)) (list (car x)))))
   ~ev[]
   Then use The Method to prove:
   ~bv[]
   (defthm triple-rev
     (equal (rev (rev (rev x))) (rev x)))
   ~ev[]

   When you've solved this problem, compare your answer to ours;
   ~pl[introductory-challenge-problem-1-answer].

   Then, use your browser's ~b[Back Button] to return to 
   ~il[introductory-challenges].
   ~/~/")

(deflabel introductory-challenge-problem-1-answer
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   answer to challenge problem 1 for the new user of ACL2~/

   This answer is in the form of an ACL2 script sufficient to lead ACL2 to a
   proof.

   ~bv[]
   (defun rev (x)
     (if (endp x)
         nil
         (append (rev (cdr x)) (list (car x)))))

   ; Trying ~c[triple-rev] at this point produces a key checkpoint containing
   ; ~c[(REV (APPEND (REV (CDR X)) (LIST (CAR X))))], which suggests:

   (defthm rev-append
     (equal (rev (append a b))
            (append (rev b) (rev a))))

   ; And now ~c[triple-rev] succeeds.

   (defthm triple-rev
     (equal (rev (rev (rev x))) (rev x)))

   ; An alternative, and more elegant, solution is to prove the ~c[rev-rev]
   ; instead of ~c[rev-append]:

   ; (defthm rev-rev
   ;   (implies (true-listp x)
   ;            (equal (rev (rev x)) x)))

   ; ~c[Rev-rev] is also discoverable by The Method because it is
   ; suggested by the statement of ~c[triple-rev] itself:  ~c[rev-rev]
   ; simplifies a simpler composition of the functions in ~c[triple-rev].

   ; Both solutions produce lemmas likely to be of use in future proofs
   ; about ~c[rev].

   ~ev[]

   Use your browser's ~b[Back Button] now to return to
   ~il[introductory-challenge-problem-1].

   ~/~/")

(deflabel introductory-challenge-problem-2
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   challenge problem 2 for the new user of ACL2~/

   Start in a fresh ACL2, either by restarting your ACL2 image from scratch or
   executing ~c[:ubt! 1].

   Use The Method to prove 
   ~bv[]
   (defthm subsetp-reflexive
     (subsetp x x))
   ~ev[]

   When you've solved this problem, compare your answer to ours;
   ~pl[introductory-challenge-problem-2-answer].

   Then, use your browser's ~b[Back Button] to return to 
   ~il[introductory-challenges].

   ~/~/")

(deflabel introductory-challenge-problem-2-answer
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   answer to challenge problem 2 for the new user of ACL2~/

   This answer is in the form of a script sufficient to lead ACL2 to a
   proof.

   ~bv[]
   ; Trying ~c[subsetp-reflexive] at this point produces the key checkpoint:

   ; (IMPLIES (AND (CONSP X)
   ;               (SUBSETP (CDR X) (CDR X)))
   ;          (SUBSETP (CDR X) X))

   ; which suggests the generalization:

   (defthm subsetp-cdr
     (implies (subsetp a (cdr b))
              (subsetp a b)))

   ; And now ~c[subsetp-reflexive] succeeds.

   (defthm subsetp-reflexive
     (subsetp x x))   

   ; A weaker version of the lemma, namely the one in which we
   ; add the hypothesis that ~c[b] is a ~c[cons], is also sufficient.

   ;    (defthm subsetp-cdr-weak
   ;      (implies (and (consp b)
   ;                    (subsetp a (cdr b)))
   ;               (subsetp a b)))   

   ; But the ~c[(consp b)] hypothesis is not really necessary in
   ; ACL2's type-free logic because ~c[(cdr b)] is ~c[nil] if ~c[b] is
   ; not a ~c[cons].  For the reasons explained in the tutorial, we
   ; prefer the strong version.

   ~ev[]

      Use your browser's ~b[Back Button] now to return to
   ~il[introductory-challenge-problem-2].

   ~/~/")

(deflabel introductory-challenge-problem-3
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   challenge problem 3 for the new user of ACL2~/

   Start in a fresh ACL2, either by restarting your ACL2 image from scratch or
   executing ~c[:ubt! 1].

   Define the following functions and use The Method to prove the theorem
   at the bottom:
   ~bv[]
   (defun rev (x)
     (if (endp x)
         nil
         (append (rev (cdr x)) (list (car x)))))   

   (defun dupsp (x)  ; does x contain duplicate elements?
     (if (endp x)
         nil
         (if (member (car x) (cdr x))
             t
             (dupsp (cdr x)))))

   (defthm dupsp-rev
     (equal (dupsp (rev x)) (dupsp x)))
   ~ev[]

     When you've solved this problem, compare your answer to ours;
   ~pl[introductory-challenge-problem-3-answer].

   Then, use your browser's ~b[Back Button] to return to 
   ~il[introductory-challenges].

   ~/~/")

(deflabel introductory-challenge-problem-3-answer
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   answer to challenge problem 3 for the new user of ACL2~/

   This answer is in the form of a script sufficient to lead ACL2 to a
   proof.

   ~bv[]
   ; Trying ~c[dupsp-rev] at this point produces the key checkpoint:

   ; (IMPLIES (AND (CONSP X)
   ;               (NOT (MEMBER (CAR X) (CDR X)))
   ;               (EQUAL (DUPSP (REV (CDR X)))
   ;                      (DUPSP (CDR X))))
   ;          (EQUAL (DUPSP (APPEND (REV (CDR X)) (LIST (CAR X))))
   ;                 (DUPSP (CDR X))))

   ; which suggests the lemma

   ; (defthm dupsp-append
   ;   (implies (not (member e x))
   ;            (equal (dupsp (append x (list e)))
   ;                   (dupsp x))))

   ; However, attempting to prove that, produces a key checkpoint
   ; containing ~c[(MEMBER (CAR X) (APPEND (CDR X) (LIST E)))].
   ; So we prove the lemma:

   (defthm member-append
     (iff (member e (append a b))
          (or (member e a)
              (member e b))))

   ; Note that we had to use ~c[iff] instead of ~c[equal] since ~c[member] is not a
   ; Boolean function.

   ; Having proved this lemma, we return to ~c[dupsp-append] and succeed:

   (defthm dupsp-append
     (implies (not (member e x))
              (equal (dupsp (append x (list e)))
                     (dupsp x))))

   ; So now we return to ~c[dups-rev], expecting success.  But it fails
   ; with the same key checkpoint:

   ; (IMPLIES (AND (CONSP X)
   ;               (NOT (MEMBER (CAR X) (CDR X)))
   ;               (EQUAL (DUPSP (REV (CDR X)))
   ;                      (DUPSP (CDR X))))
   ;          (EQUAL (DUPSP (APPEND (REV (CDR X)) (LIST (CAR X))))
   ;                 (DUPSP (CDR X))))

   ; Why wasn't our ~c[dupsp-append] lemma applied?  We have two choices here:
   ; (1) Think.  (2) Use tools.

   ; Think:  When an enabled rewrite rule doesn't fire even though the left-hand
   ; side matches the target, the hypothesis couldn't be relieved.  The ~c[dups-append]
   ; rule has the hypothesis ~c[(not (member e x))] and after the match with the left-hand side,
   ; ~c[e] is ~c[(CAR X)] and ~c[x] is ~c[(REV (CDR X))].  So the system couldn't rewrite
   ; ~c[(NOT (MEMBER (CAR X) (REV (CDR X))))] to true, even though it knows that
   ; ~c[(NOT (MEMBER (CAR X) (CDR X)))] from the second hypothesis of the checkpoint.
   ; Obviously, we need to prove ~c[member-rev] below.

   ; Use tools:  We could enable the ``break rewrite'' facility, with

   ; ACL2 !>:brr t

   ; and then install an unconditional monitor on the rewrite rule
   ; ~c[dupsp-append], whose rune is (:REWRITE DUPSP-APPEND), with:

   ; :monitor (:rewrite dupsp-append) t

   ; Then we could re-try our main theorem, dupsp-rev.  At the resulting
   ; interactive break we type :eval to evaluate the attempt to relieve the
   ; hypotheses of the rule.

   ; (1 Breaking (:REWRITE DUPSP-APPEND) on 
   ; (DUPSP (BINARY-APPEND (REV #) (CONS # #))):
   ; 1 ACL2 >:eval

   ; 1x (:REWRITE DUPSP-APPEND) failed because :HYP 1 rewrote to 
   ; (NOT (MEMBER (CAR X) (REV #))).

   ; Note that the report above shows that hypothesis 1 of the rule
   ; did not rewrite to T but instead rewrote to an expression
   ; involving ~c[(member ... (rev ...))].  Thus, we're led to the
   ; same conclusion that Thinking produced.  To get out of the
   ; interactive break we type:

   ; 1 ACL2 >:a!
   ; Abort to ACL2 top-level

   ; and then turn off the break rewrite tool since we won't need it
   ; again right now, with:

   ; ACL2 !>:brr nil

   ; In either case, by thinking or using tools, we decide to prove:

   (defthm member-rev
     (iff (member e (rev x)) 
          (member e x)))

   ; which succeeds.  Now when we try to prove dups-rev, it succeeds.

   (defthm dupsp-rev
     (equal (dupsp (rev x))
            (dupsp x)))

   ~ev[]

      Use your browser's ~b[Back Button] now to return to
   ~il[introductory-challenge-problem-3].

   ~/~/")

(deflabel introductory-challenge-problem-4
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   challenge problem 4 for the new user of ACL2~/

   Start in a fresh ACL2, either by restarting your ACL2 image from scratch or
   executing ~c[:ubt! 1].

   This problem is much more open ended than the preceding ones.  The challenge
   is to define a function that collects exactly one copy of each element of a list
   and to prove that it returns a subset of the list with no duplications.

   ~b[Hint]:  We recommend that you read this hint to align your function names
   with our solution, to make comparisons easier.  Our answer is shown in 
   ~pl[introductory-challenge-problem-4-answer].  In that page you'll see a definition of
   a function ~c[collect-once] and the proofs of two theorems:
   ~bv[]
   (defthm main-theorem-1-about-collect-once
     (subsetp (collect-once x) x))

   (defthm main-theorem-2-about-collect-once
     (not (dupsp (collect-once x))))
   ~ev[]
   The function ~c[dupsp] is as defined in ~pl[introductory-challenge-problem-3].
   This is quite easy.

   Then, we define a tail-recursive version of the method based on the pseudo-code:
   ~bv[]
    a = nil;
    while (x not empty) {
     a = if (member (car x) a) then a else (cons (car x) a);
     x = (cdr x);
     }
    return a;
   ~ev[]
   We formalize this with the function ~c[while-loop-version], where
   ~c[(while-loop-version x nil)] is the ``semantics'' of the code above.
   I.e., the function ~c[while-loop-version] captures the while loop in the
   pseudo-code above and returns the final value of ~c[a], and it should be
   invoked with the initial value of ~c[a] being ~c[nil].

   We prove ~c[(while-loop-version x nil)] returns a subset of ~c[x] that
   contains no duplications.  Furthermore, we do it two ways: first
   ``indirectly'' by relating ~c[while-loop-version] to ~c[collect-once], and
   second (``directly'') without using ~c[collect-once].  Both of these proofs
   are much harder than the ~c[collect-once] approach, involving about a dozen
   lemmas each.

   Compare your solutions to ours at 
   ~pl[introductory-challenge-problem-4-answer].  

   Then, use your browser's ~b[Back Button] to return to 
   ~il[introductory-challenges].

   ~/~/")

(deflabel introductory-challenge-problem-4-answer
  :doc
  ":Doc-Section introduction-to-the-theorem-prover

   answer to challenge problem 4 for the new user of ACL2~/

   This answer is in the form of a script sufficient to lead ACL2 to a
   proof, with a brief prologue.

   We wish to collect one copy of each element in x.  We'll actually define the
   method two ways, primitive recursively and tail-recursively, the latter
   method being analogous to the program:
   ~bv[]
   a = nil;
   while (x not empty) {
     a = if (member (car x) a) then a else (cons (car x) a);
     x = (cdr x);
     }
   return a;
   ~ev[]

   We'll prove the two ``equivalent'' and we'll prove that they return a subset
   of ~c[x] that contains no duplications.

   This page is organized into four sections.  (A) We will start by proving that
   the primitive recursive version correct: it returns a subset of its argument
   that is duplication free.  This will be straightforward.  (B) Then we'll
   define the ~c[while]-loop version and we will prove it ``equivalent'' to the
   primitive recursive version.  This will be challenging primarily because the
   two methods collect their answers in different orders; even stating the
   relationship between the two is interesting.  Proving it will involve a few
   lemmas.  But once we prove their ``equivalence'' the correctness of the
   ~c[while]-loop version will be straightforward from the correctness of the
   primitive recursive version.  (C) We will disable the rules we prove about
   the ~c[while]-loop version and prove it correct directly, without exploiting the
   primitive recursive version.  This requires leading the theorem prover more
   carefully because reasoning about tail-recursive functions that accumulate
   results is sometimes delicate.  (D) Lessons learned -- a narrative that
   summarizes what we learn from these examples.

   We follow The Method, which, recall, involves us in recursive attempts to
   prove lemmas.  We use a notation to indicate our sequence of proof attempts.
   Here is an example (although in actual use we print things across multiple
   lines).  The number in bracket indicates our ``stack depth''.  The ``key
   term'' is some term from a Key Checkpoint in the failed proof which is
   responsible for our subsequent action.  Sometimes instead of a Key Term we
   just give an English explanation of what we're thinking.
   ~bv[]
   [0] (defthm main ...)     Failed!    Key Term: ...
   [1] (defthm lemma-1 ...)  Succeeded!
   [0] (defthm main ...)     Failed!    Key Term: ...
   [1] (defthm lemma-2 ...)  Failed!    Key Term: ...
   [2] (defthm lemma-2a ...) Succeeded!
   [2] (defthm lemma-2b ...) Succeeded!
   [1] (defthm lemma-2 ...)  Succeeded!
   [0] (defthm main ...)     Succeeded!
   ~ev[]

   The rest of this page is just a re-playable script.

   ~bv[]
   ; -----------------------------------------------------------------
   ; Section A:  The Primitive Recursive Version and Its Correctness

   ; The property of having duplications is defined as:

   (defun dupsp (x)
     (if (endp x)
         nil
         (if (member (car x) (cdr x))
             t
             (dupsp (cdr x)))))

   ; The primitive recursive method of collecting one copy of each element is:

   (defun collect-once (x)
     (if (endp x)
         nil
         (if (member (car x) (cdr x))
             (collect-once (cdr x))
             (cons (car x) (collect-once (cdr x))))))

   ; [0] 
   (defthm main-theorem-1-about-collect-once
     (subsetp (collect-once x) x))
   ; Succeeded!

   ; [0]
   ; (defthm main-theorem-2-about-collect-once
   ;   (not (dupsp (collect-once x))))
   ; Failed!
   ; Key Term:  (MEMBER (CAR X) (COLLECT-ONCE (CDR X)))

   ; [1]
   (defthm member-collect-once
     (iff (member e (collect-once a))
          (member e a)))
   ; Succeeded!

   ; [0]
   (defthm main-theorem-2-about-collect-once
     (not (dupsp (collect-once x))))
   ; Succeeded!

   ; That was really easy!

   ;-----------------------------------------------------------------
   ; Section B:  The While-Loop Version and Its Correctness --
   ;  presented in two parts:  its equivalence to the primitive recursive
   ;  version and then its correctness proved via that equivalence

   ; The tail-recursive, or while-loop version, is defined as follows.  The
   ; function below is the loop itself and it ought to be called with a = nil to
   ; implement the initialization of a in the pseudo-code above.

   (defun while-loop-version (x a)
     (if (endp x)
         a
         (while-loop-version (cdr x)
                             (if (member (car x) a)
                                 a
                                 (cons (car x) a)))))

   ; We wish to prove that the two are equivalent.  But they are actually
   ; very different.  For example,

   ; (collect-once '(2 4 1 3 1 2 3 4))           = (1 2 3 4)
   ; (while-loop-version '(2 4 1 3 1 2 3 4) nil) = (3 1 4 2)

   ; Things get a little more complicated if a is non-nil:
   ; (while-loop-version '(2 4 1 3 1 2 3 4) '(2 2 4 4)) = (3 1 2 2 4 4)

   ; Several observations help explain what is happening.  (1) Collect-once
   ; collects the last occurrence of each element, in the order of their last
   ; occurrences.  So, for example, since the last occurrence of 2 preceeds the
   ; last occurrence of 3 in '(2 4 1 3 1 2 3 4)), then the collected 2 preceeds
   ; the collected 3 in the answer.  But while-loop-version collects the first
   ; occurrence of each element, in the reverse order of that occurrence.  So it
   ; adds 2 to its accumulator first and adds 3 last, making 3 preceed 2 in the
   ; answer.

   ; (2) The while-loop-version does not collect anything already in a and indeed
   ; just adds stuff to the front of a, returning everything initially in a plus
   ; one occurrence of everything in x not in a.

   ; To state the relationship that holds between these two we have to define two
   ; other functions.

   ; This is our familiar list reverse function...
   (defun rev (x)
     (if (endp x)
         nil
         (append (rev (cdr x))
                 (list (car x)))))

   ; And this function ``removes'' from x all the elements in y, i.e., copies x
   ; while dropping the elements of y.

   (defun list-minus (x y)
     (if (endp x)
         nil
         (if (member (car x) y)
             (list-minus (cdr x) y)
             (cons (car x) (list-minus (cdr x) y)))))

   ; The specific equivalence we're really interested in is
   ; (equal (while-loop-version x nil)
   ;        (collect-once (rev x)))

   ; But we will not be able to prove that by induction because it has the
   ; constant nil where we need a variable, a, in order to admit an appropriate
   ; inductive instance.  So we will attack the most general problem.  What is
   ; (while-loop-version x a) equal to, in terms of collect-once?

   ; The most general relationship between the two collection functions is:

   ; (equal (while-loop-version x a)
   ;        (append (collect-once (list-minus (rev x) a)) a))

   ; This formula bears thinking about!  If you're like us, you won't believe it
   ; until it is proved!

   ; [0]
   ; (defthm general-equivalence
   ;   (equal (while-loop-version x a)
   ;          (append (collect-once (list-minus (rev x) a)) a)))
   ; Failed!
   ; Key term in checkpoint:
   ; (LIST-MINUS (APPEND (REV (CDR X)) (LIST (CAR X))) A)

   ; [1]
   (defthm list-minus-append
     (equal (list-minus (append a b) c)
            (append (list-minus a c)
                    (list-minus b c))))
   ; Succeeded!

   ; [0]
   ; (defthm general-equivalence
   ;   (equal (while-loop-version x a)
   ;          (append (collect-once (list-minus (rev x) a)) a)))
   ; Failed!
   ; Key term in checkpoint:
   ; (COLLECT-ONCE (APPEND (LIST-MINUS (REV (CDR X)) A) (LIST (CAR X))))

   ; [1]
   ; (defthm collect-once-append
   ;   (equal (collect-once (append a b))
   ;          (append (list-minus (collect-once a) b)
   ;                  (collect-once b))))
   ; Failed!
   ; Key term:
   ; (MEMBER (CAR A) (APPEND (CDR A) B))

   ; [2]
   (defthm member-append
     (iff (member e (append a b))
          (or (member e a)
              (member e b))))
   ; Succeeded!

   ; [1]
   (defthm collect-once-append
     (equal (collect-once (append a b))
            (append (list-minus (collect-once a)
                                b)
                    (collect-once b))))
   ; Succeeded!

   ; [0]
   ; (defthm general-equivalence
   ;   (equal (while-loop-version x a)
   ;          (append (collect-once (list-minus (rev x) a)) a)))
   ; Failed!
   ; Key term:
   ; (APPEND (APPEND (LIST-MINUS (COLLECT-ONCE (LIST-MINUS (REV (CDR X)) A))

   ; [1]
   (defthm assoc-append
     (equal (append (append a b) c)
            (append a (append b c))))
   ; Succeeded!

   ; [0]
   ; (defthm general-equivalence
   ;   (equal (while-loop-version x a)
   ;          (append (collect-once (list-minus (rev x) a)) a)))
   ; Failed!
   ; Key term:
   ; (LIST-MINUS (COLLECT-ONCE (LIST-MINUS (REV (CDR X)) A)) ...)

   ; This key term makes us think of the lemma to move the LIST-MINUS inside the
   ; COLLECT-ONCE.  But when that's done, we will have two LIST-MINUS terms
   ; nestled together and we will want to combine them into one.  Call these two
   ; lemmas (a) and (b).

   ; [1] (a)
   ; (defthm list-minus-collect-once
   ;   (equal (list-minus (collect-once x) a)
   ;          (collect-once (list-minus x a))))
   ; Failed!
   ; Key term:
   ; (MEMBER (CAR X) (LIST-MINUS (CDR X) A))

   ; [2] (A pretty fact)
   (defthm member-list-minus
     (iff (member e (list-minus x a))
          (and (member e x)
               (not (member e a)))))
   ; Succeeded!

   ; [1] (a)
   (defthm list-minus-collect-once
     (equal (list-minus (collect-once x) a)
            (collect-once (list-minus x a))))
   ; Succeeded!

   ; [1] (b)
   (defthm list-minus-list-minus
     (equal (list-minus (list-minus x a) b)
            (list-minus x (append b a))))
   ; Succeeded!

   ; [0]
   (defthm general-equivalence
     (equal (while-loop-version x a)
            (append (collect-once (list-minus (rev x) a)) a)))
   ; Succeeded!

   ; That completes the proof of the ``equivalence'' of the two methods.

   ; Now we prove (1) that the result of while-loop-version is a subset, and (2)
   ; that it contains no duplications.  We prove the two conjuncts separately.

   ; [0]
   (defthm main-theorem-1-about-while-loop
     (subsetp (while-loop-version x nil) x))
   ; Succeeded!

   ; But the theorem prover works harder to do the proof above than one might have
   ; expected because it doesn't turn into an instance of
   ; main-theorem-1-about-collect-once because of the presence of the rev term.
   ; However, we're content that ACL2 managed to do the proof on its own.

   ; [0]
   (defthm main-theorem-2-about-while-loop
     (not (dupsp (while-loop-version x nil))))

   ; So we see that the proof of correctness of while-loop-version isn't hard,
   ; after we establish the relationship with the primitive recursive version.
   ; But finding and proving the relationship is fairly challenging.

   ; -----------------------------------------------------------------
   ; Section C:  A Direct Proof of the Correctness of the While-Loop Version

   ; Some would consider the proof in Section B ``indirect'' because we first showed
   ; how while-loop-version could be expressed as a collect-once and then proved
   ; our main theorems about while-loop-version, which means those main proofs
   ; were conducted in terms of collect-once, not while-loop-version.

   ; It is interesting to compare this proof with the ``direct'' one in which
   ; we don't use collect-once at all and reason only about while-loop-version.

   ; So to do that comparison, let's disable all the lemmas we've proved about
   ; while-loop-version and try to prove the two main theorems above about
   ; while-loop-version.

   (in-theory (disable general-equivalence
                       main-theorem-1-about-while-loop
                       main-theorem-2-about-while-loop))

   
   ; [0]
   ; (defthm main-theorem-1-about-while-loop-redux
   ;   (subsetp (while-loop-version x nil) x))
   ; Failed!  [Well, the truth is below...]

   ; We don't even submit this event above because we recognize that it is not
   ; general enough to permit proof by induction.  We need to deal with the nil in
   ; the second argument of while-loop-version.  Experience with induction tells
   ; us this should be a variable, so we can assume an appropriate inductive
   ; instance.  Therefore, we adopt this subgoal immediately:

   ; [1]
   ; (defthm main-lemma-1-about-while-loop-version
   ;   (subsetp (while-loop-version x a) (append x a)))
   ; Failed!
   ; Key Term:  Does the wrong induction.  

   ; [1]
   ; (defthm main-lemma-1-about-while-loop-version
   ;   (subsetp (while-loop-version x a) (append x a))
   ;   :hints ((\"Goal\" :induct (while-loop-version x a))))
   ; Failed!  Two key terms are suggested
   ; Key term: (IMPLIES (AND ... (SUBSETP (WHILE-LOOP-VERSION (CDR X) A) (APPEND (CDR X) A)))
   ;                    (SUBSETP (WHILE-LOOP-VERSION (CDR X) A) (CONS ... (APPEND (CDR X) A))))
   ; Key term: (SUBSETP A A)
   ; So we'll prove both before trying again.
   ; [2]
   (defthm subsetp-cons
     (implies (subsetp a b)
              (subsetp a (cons e b))))
   ; Succeeded!

   ; [2]
   (defthm subsetp-reflexive
     (subsetp a a))
   ; Succeeded!

   ; [1]
   ; (defthm main-lemma-1-about-while-loop-version
   ;   (subsetp (while-loop-version x a) (append x a))
   ;   :hints ((\"Goal\" :induct (while-loop-version x a))))
   ; Failed!
   ; Key Term:
   ; (IMPLIES (AND ...
   ;               (SUBSETP (WHILE-LOOP-VERSION (CDR X) (CONS (CAR X) A))
   ;                        (APPEND (CDR X) (CONS (CAR X) A))))
   ;          (SUBSETP (WHILE-LOOP-VERSION (CDR X) (CONS (CAR X) A))
   ;                   (CONS (CAR X) (APPEND (CDR X) A))))

   ; We'd be done if we could rewrite the
   ; (APPEND (CDR X) (CONS (CAR X) A)) 
   ; to
   ; (CONS (CAR X) (APPEND (CDR X) A))
   ; These two terms are not equal!  But they are ``set-equal'' and this kind of
   ; rewriting is possible using user-defined equivalences and congruence rules.
   ; But the new user should not dive into congruences yet.  So we will do this
   ; with ordinary lemmas:

   ; The plan then is to prove
   ; (iff (subsetp a (append b (cons e c)))
   ;      (subsetp a (cons e (append b c)))) 

   ; Consider the first half of this bi-implication:
   ; (implies (subsetp a (append b (cons e c)))            ; hyp1
   ;          (subsetp a (cons e (append b c))))           ; concl
   ; Notice that if we knew
   ; (subsetp (append b (cons e c)) (cons e (append b c))) ; hyp2
   ; then we could use hyp1 and hyp2 together with the transitivity of
   ; subsetp to get concl.

   ; The proof in the other direction is comparable but requires the
   ; (subsetp (cons e (append b c)) (append b (cons e c)))

   ; Thus, our plan is prove 
   ; (a) transitivity of subsetp
   ; (b) (subsetp (append b (cons e c)) (cons e (append b c)))
   ; (c) (subsetp (cons e (append b c)) (append b (cons e c)))

   ; in order to prove
   ; (d) (iff (subsetp a (append b (cons e c)))
   ;         (subsetp a (cons e (append b c)))) 

   ; [2] (a)
   (defthm trans-subsetp
     (implies (and (subsetp a b)
                   (subsetp b c))
              (subsetp a c)))
   ; Succeeded!

   ; [2] (b)
   (defthm append-cons-v-cons-append-1
     (subsetp (append b (cons e c))
              (cons e (append b c))))
   ; Succeeded!

   ; [2] (c)
   (defthm append-cons-v-cons-append-2
     (subsetp (cons e (append b c))
              (append b (cons e c))))
   ; Succeeded!

   ; [2] (d)
   (defthm subsetp-append-cons-cons-append
     (iff (subsetp a (append b (cons e c)))
          (subsetp a (cons e (append b c)))))
   ; Succeeded!

   ; [1]
   (defthm main-lemma-1-about-while-loop-version
     (subsetp (while-loop-version x a) (append x a))
     :hints ((\"Goal\" :induct (while-loop-version x a))))
   ; Succeeded!

   ; [0]
   ; (defthm main-theorem-1-about-while-loop-version
   ;   (subsetp (while-loop-version x nil) x))
   ; Failed!  [But the truth is below...]

   ; But we don't submit this because we don't expect it to be proved
   ; from the main lemma just proved:  they don't match!  But
   ; note that if we instantiated the main lemma, replacing a by nil,
   ; we get:

   ; (subsetp (while-loop-version x nil) (append x nil))

   ; and we could simplify the (append x nil) to x in this context, with
   ; another congruence rule -- if we were using them.  So let's prove
   ; first that we can simplify (append x nil) inside a subsetp:

   ; [1]
   (defthm subsetp-append-nil
     (iff (subsetp x (append y nil))
          (subsetp x y)))
   ; Succeeded!

   ; and then just tell ACL2 how to use the lemma to get the main theorem.  Note
   ; that we give a hint to instantiate main-lemma-1... but we also disable
   ; main-lemma-1... because otherwise it will rewrite itself away!  Once the
   ; instance of main-lemma-1... is sitting around as a hypothesis,
   ; subsetp-append-nil will rewrite the (append x nil) to x for us and finish the
   ; proof.

   ; [0]
   (defthm main-theorem-1-about-while-loop-version
     (subsetp (while-loop-version x nil) x)
     :hints ((\"Goal\"
              :use (:instance main-lemma-1-about-while-loop-version
                              (x x)
                              (a nil))
              :in-theory (disable main-lemma-1-about-while-loop-version))))
   ; Succeeded!

   ; Recall that the main-theorem-1... just proved is just half of what we want.
   ; We also want:

   ; [0]
   ; (defthm main-theorem-2-about-while-loop-version
   ;   (not (dupsp (while-loop-version x nil))))
   ; Failed!  [But the truth is below...]

   ; But, again, we don't submit that because the nil makes it not general enough for
   ; induction.  Instead we go immediately to:

   ; [1]
   (defthm main-lemma-2-about-while-loop-version
     (implies (not (dupsp a))
              (not (dupsp (while-loop-version x a)))))
   ; Succeeded!

   ; This time we know our main-lemma-2... will match (there's no (append x nil)
   ; in there to mess things up) and so we can complete the proof with:

   ; [0]
   (defthm main-theorem-2-about-while-loop-version
     (not (dupsp (while-loop-version x nil))))
   ; Succeeded!

   ;-----------------------------------------------------------------
   ; Section D:  Lessons Learned

   ; The most obvious lesson is that it is easier to reason about the primitive
   ; recursive collect-once than about the while-loop-version.  Thus, if your only
   ; need is for a function that collects one occurrence of each element of a list
   ; and you don't care about the order in which you collect them and you don't
   ; need it to be very sparing of stack space when it executes, then use the
   ; primitive recursive definition and don't even think about while loops!

   ; So why might you be driven to while-loop-version?  One possibility is that
   ; the list you wish to process is very long and the primitive recursive version
   ; would produce a stack overflow.  In ACL2, that would mean the list would have
   ; to be several thousand long.  Is your application really so demanding?

   ; Another possibility is that you are modeling in Lisp a while loop expressed
   ; in some other programming language.  In that case, the fidelity of your model to
   ; the artifact being modeled is important and you should use while-loop-version.

   ; Another possibility is that for some reason order matters and you really are
   ; interested in collecting the first occurrence rather than the last.  Of
   ; course this is most likely to be relevant in more interesting applications
   ; where the occurrences are somehow distinguishable.

   ; If you are forced to deal with the while-loop-version the question is do you
   ; do an indirect proof as in Section B or a direct proof as in Section C?
   ; The indirect proof involved 10 theorems and the direct proof involved 11.
   ; That is not a significant difference.

   ; But our sense is that the indirect proof is easier to find, once you figure
   ; out the basic shape of the relation between while-loop-version collect-once.
   ; In particular, we had to give the theorem prover two hints in the direct
   ; proof (versus no hints in the indirect proof).  One of our hints was about
   ; what induction to do and the other was about how to use a previously proved
   ; instance of a lemma involving an accumulator.  Furthermore, we had to think
   ; carefully about the use of the transitivity of subsetp and we had to hack our
   ; way around rewriting (append a (cons e b)) to (cons e (append a b)) in a
   ; subsetp-expression.

   ; Some of these ``set'' problems could have been handled a lot more elegantly by
   ; defining set-equal as an equivalence relation and proving the congruence
   ; rules to allow the rewriting of set-equal terms to set-equal terms inside
   ; certain expressions like subsetp and member.  However, that involves a lot of
   ; overhead in the form of congruence rules showing that set-equality is
   ; maintained by replacement of set-equals by set-equals in various argument
   ; positions of the various functions.  See :doc congruence.  In general, we
   ; find congruence-based reasoning extremely neat and powerful when the
   ; appropriate infrastructure has been built up.  But because the infrastructure
   ; is ``heavy'' we tend not to invest in it for small projects.

   ; In summary, different users might take home different lessons about whether a
   ; direct or indirect proof is better here.  This is in part due to the
   ; complexity of the functional relationship between collect-once and
   ; while-loop-version, which additionall involved append, list-minus, and rev.
   ; Had the relationship been simpler, the indirect proof would have been
   ; preferred.

   ; An undeniable lesson, however, is that it is helpful to know both styles of
   ; proof and to be able to explore both as needed in your applications.
   ~ev[]

   Use your browser's ~b[Back Button] now to return to
   ~il[introductory-challenge-problem-4].

   ~/~/")

; text below was generated quite tediously:  I modified an existing
; tex file to produce:
; /v/filer4b/v11q001/text/onr/beige-paper.tex
; then processed it with latex and bibtex, then displayed the pdf and copied
; it to text, and then formatted it as a doc string, eliminating odd characters
; etc.  

(deflabel interesting-applications
  :doc
  ":Doc-Section acl2-tutorial

  some industrial examples of ACL2 use~/

  ACL2 is an interactive system in which you can model digital artifacts and
  guide the system to mathematical proofs about the behavior of those
  models.  It has been used at such places as AMD, Centaur, IBM, and Rockwell
  Collins to verify interesting properties of commercial designs.  It has been
  used to verify properties of models of microprocessors, microcode, the Sun Java
  Virtual Machine, operating system kernels, other verifiers, and interesting
  algorithms.  

  Here we list just a few of the industrially-relevant results obtained with
  ACL2.  Reading the list may help you decide you want to learn how to use
  ACL2.  If you do decide you want to learn more, we recommend that you take
  ~il[|The Tours| The Tours] after you leave this page.

  ACL2 was used at ~b[Motorola Government Systems] to certify several microcode
  programs for the ~b[Motorola CAP digital signal processor], including a
  comparator sort program that is particularly subtle. In the same project,
  ACL2 was used to model the CAP at both the pipelined architectural level and
  the instruction set level.  The architectural model was bit- and
  cycle-accurate: it could be used to predict every bit of memory on every
  cycle.  The models were proved equivalent under certain hypotheses, the most
  important being a predicate that analyzed the microcode for certain pipeline
  hazards. This predicate defined what the hazards were, syntactically, and the
  equivalence of the two models established the correctness of this syntactic
  characterization of hazards.  Because ACL2 is a functional programming
  language, the ACL2 models and the hazard predicate could be executed.  ACL2
  executed microcode interpretr several times faster than the hardware
  simulator could execute it -- with assurance that the answers were
  equivalent.  In addition, the ACL2 hazard predicate was executed on over
  fifty microcode programs written by Motorola engineers and extracted from the
  ROM mechanically. Hazards were found in some of these.  (See, for example,
  Bishop Brock and Warren. A. Hunt, Jr. ``Formal analysis of the motorola CAP
  DSP.'' In ~i[Industrial-Strength Formal Methods]. Springer-Verlag, 1999.)

  ACL2 was used at ~b[Advanced Micro Devices] (AMD) to verify the compliance of
  the ~b[AMD Athon]'s (TM) elementary floating point operations with their IEEE
  754 specifications. This followed ground-breaking work in 1995 when ACL2 was
  used to prove the correctness of the microcode for floating-point division on
  the ~b[AMD K5]. The AMD Athlon work proved addition, subtraction,
  multiplication, division, and square root compliant with the IEEE
  standard. Bugs were found in RTL designs. These bugs had survived undetected
  in hundreds of millions of tests but were uncovered by ACL2 proof
  attempts. The RTL in the fabricated Athlon FPU has been mechanically verified
  by ACL2.  Similar ACL2 proofs have been carried out for every major AMD FPU design
  fabricated since the Athlon.  (See for example,
  David Russinoff. ``A mechanically checked proof of correctness of the
  AMD5K86 floating-point square root microcode''.
  ~i[Formal Methods in System Design] Special Issue on Arithmetic Circuits, 1997.)

  ACL2 was used at ~b[IBM] to verify the floating point divide and square root
  on the ~b[IBM Power 4].  (See Jun Sawada. ``Formal verification of divide and square root algorithms
  using series calculation''. In ~i[Proceedings of the ACL2 Workshop 2002],
  Grenoble, April 2002.)

  ACL2 was used to verify floating-point addition/subtraction instructions for
  the ~b[media unit] from ~b[Centaur Technology]'s 64-bit, X86-compatible
  microprocessor. This unit implements over one hundred instructions, with the
  most complex being floating-point addition/subtraction. The media unit can
  add/subtract four pairs of floating-point numbers every clock cycle with an
  industry-leading two-cycle latency. The media unit was modeled by translating
  its Verilog design into an HDL deeply embedded in the ACL2 logic. The proofs
  used a combination of AIG- and BDD-based symbolic simulation, case splitting,
  and theorem proving.  (See Warren A. Hunt, Jr. and Sol Swords. ``Centaur Technology Media Unit
  Verification''. In ~i[CAV '09: Proceedings of the 21st International]
  ~b[Conference on Computer Aided Verification], pages 353--367, Berlin,
  Heidelberg, 2009. Springer-Verlag.)

  ~b[Rockwell Collins] used ACL2 to prove information flow properties about its
  ~b[Advanced Architecture MicroProcessor 7 Government Version (AAMP7G)], a
  Multiple Independent Levels of Security (MILS) device for use in
  cryptographic applications. The AAMP7G provides MILS capability via a verified
  secure hardware-based separation kernel. The AAMP7G's design was proved to
  achieve MILS using ACL2, in accordance with the standards set by EAL-7 of
  the Common Criteria and Rockwell Collins has received National Security
  Agency (NSA) certification for the device based on this work.
  (See David S. Hardin, Eric W. Smith, and William. D. Young. ``A robust machine
  code proof framework for highly secure applications''. In
  ~i[Proceedings of the sixth international workshop on the ACL2 theorem prover]
  ~i[and its applications], pages 11--20, New York, NY, USA, 2006. ACM.)

  Key properties of the ~b[Sun Java Virtual Machine] and its ~b[bytecode verifier] were
  verified in ACL2. Among the properties proved were that certain invariants
  are maintained by ~b[class loading] and that the bytecode verifier insures that
  execution is safe. In addition, various ~b[JVM bytecode programs] have been
  verified using this model of the JVM.  (See Hanbing Liu. ~i[Formal Specification and]
  ~i[Verification of a JVM and its Bytecode Verifier]. PhD thesis,
  University of Texas at Austin, 2006.)

  The ~b[Boyer-Moore fast string searching algorithm] was verified with ACL2,
  including a model of the JVM bytecode for the search algorithm itself (but
  not the preprocessing).  (See J S. Moore and Matt Martinez. ``A mechanically
  checked proof of the correctness of the Boyer-Moore fast string searching
  algorithm.'' In ~i[Engineering Methods and Tools for Software Safety and Security] 
  pages 267--284. IOS Press, 2009.)

  ACL2 was used to verify the fidelity between an ~b[ACL2-like theorem prover]
  and a simple (``trusted by inspection'') ~b[proof checker], thereby
  establishing (up to the soundness of ACL2) the soundness of the ACL2-like
  theorem prover.  This project was only part of a much larger project in
  which the resulting ACL2 proof script was then hand-massaged into a script
  suitable for the ACL2-like theorem prover to process, generating a formal
  proof of its fidelity that has been checked by the trusted proof checker.
  (See Jared Davis.  ~i[Milawa: A Self-Verifying Theorem Prover].  Ph.D. Thesis, University of
  Texas at Austin, December, 2009.)

  These are but a few of the interesting projects carried out with ACL2.  Many
  of the authors mentioned above have versions of the papers on their web
  pages.  In addition, see the link to ``Books and Papers about ACL2 and Its
  Applications'' on the ACL2 home
  page (~url[http://www.cs.utexas.edu/users/moore/acl2]).  Also see the
  presentations in each of the workshops listed in the link to ``ACL2
  Workshops'' on the ACL2 home page.

  ~/~/")
