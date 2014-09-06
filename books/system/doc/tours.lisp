; -*- fill-column: 79 -*-
;
; tours.lisp - The Tours
;
; ACL2 Version 6.5 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2014, Regents of the University of Texas
;
; This documentation was derived from the ACL2 system in October 2013, which
; was a descendent of ACL2 Version 1.9, Copyright (C) 1997 Computational Logic,
; Inc.  See the documentation topic NOTE-2-0.
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the LICENSE file distributed with ACL2.
;
; This program is distributed in the hope that it will be useful, but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the LICENSE file distributed with ACL2 for
; more details.
;
; Here are the original authors of this book.
;
; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; Jared split this out of acl2-doc.lisp to put it into a package.

(in-package "TOURS")
(include-book "xdoc/top" :dir :system)

(defxdoc |The Tours|
  :parents (acl2-tutorial)
  :short "The tours give an introduction to ACL2.  They describe what ACL2 is
for, and explain a bit about the ACL2 logic, the theorem prover, and the user
interface."

  :long "<p>@(see ACL2) is a very large, multipurpose system.  You can use it
 as a programming language, a specification language, a modeling language, a
 formal mathematical logic, or a semi-automatic theorem prover, just to name
 its most common uses.  It has been used on a number of <see topic='@(url
 INTERESTING-APPLICATIONS)'>industrial applications</see>.  If you're uncertain
 as to whether your project is appropriate for ACL2 we urge you to look over
 this list or contact the ACL2 developers.</p>

 <p>ACL2's documentation is quite extensive (over 4 megabytes)!  To help ease
 your introduction to ACL2, we have built two tours through this documentation.
 If you are familiar with at least some of ACL2's industrial applications, then
 you will understand the distance between the simple examples we talk about in
 these tours and the kinds of things ACL2 users do with the system.</p>

 <p>Newcomers to ACL2 should first take:</p>

 <blockquote><sf><see topic='@(url |A Flying Tour of ACL2|)'><icon
 src='flying.gif'></icon> The Flying Tour</see></sf></blockquote>

 <p>Then, if you want to know more, take:</p>

 <blockquote><sf><see topic='@(url |A Walking Tour of ACL2|)'><icon
 src='walking.gif'></icon> The Walking Tour</see></sf></blockquote>

 <p>On your first reading, follow the two tours linearly, clicking only on the
 icon of the tour you're on.  Beware of other links, which might jump you from
 one tour to the other or into the ACL2 User's Manual!  Once you have a
 coherent overview of the system, you might quickly repeat both Tours to see if
 there are unvisited links you're interested in.</p>

 <p>After the tours, if you want to learn how to use the theorem prover, see
 @(see acl2-tutorial).</p>"

 ;; I think this isn't really necessary.  What new user would know how to use
 ;; :doc or the Emacs documentation without having ever even seen the tours?
  ;;
 ;;<p>If you take the tours in a text-based format (such as using the :DOC
 ;;command in Emacs), they will probably be unsatisfying because we use gif files
 ;;and assume you can navigate ``back.''</p>

 )

(defxdoc |Pages Written Especially for the Tours|
  :parents (|The Tours|)
  :short "Placeholder parent for topics within @(see |The Tours|)."
  ;; BOZO it might be better to use parents and order-subtopics to provide
  ;; actual table-of-contents style navigation of the tours.  But for now
  ;; I'll just leave this as a small placeholder.
  )

(defxdoc |A Flying Tour of ACL2|
  :parents (|Pages Written Especially for the Tours|)
  :short "A Flying Tour of ACL2"
  :long "<p><see topic='@(url |About the ACL2 Home Page|)'><img
 src='large-flying.gif'></img></see></p>

 <p>On this tour you will learn a little about what ACL2 is for rather than how
 ACL2 works.  At the top and bottom bottom of the ``page'' there are ``flying
 tour'' icons.  Click on either icon to go to the next page of the tour.</p>

 <p>The tour visits the following topics sequentially.  But on your first
 reading, don't navigate through the tour by clicking on these links; they are
 shown as live links only so that later you can determine what you've visited.
 Instead, just use the flying tour icons.</p>

 <code>
 <b>The Flight Plan</b>
 * <see topic='@(url |About the ACL2 Home Page|)'>This Documentation</see>
 * <see topic='@(url |What Is ACL2(Q)|)'>What is ACL2?</see>
 * <see topic='@(url |What is a Mathematical Logic(Q)|)'>Mathematical Logic</see>
 * <see topic='@(url |What is a Mechanical Theorem Prover(Q)|)'>Mechanical Theorem Proving</see>
 * <see topic='@(url |About Models|)'>Mathematical Models in General</see>
 * <see topic='@(url |Models of Computer Hardware and Software|)'>Mathematical Models of Computing Machines</see>
      <see topic='@(url |A Typical State|)'>Formalizing Models</see>
      <see topic='@(url |Running Models|)'>Running Models</see>
      <see topic='@(url |Symbolic Execution of Models|)'>Symbolic Execution of Models</see>
      <see topic='@(url |Proving Theorems about Models|)'>Proving Theorems about Models</see>
 * Requirements of ACL2
      <see topic='@(url |What is Required of the User(Q)|)'>The User's Skills</see>
      <see topic='@(url |How Long Does It Take to Become an Effective User(Q)|)'>Training</see>
      <see topic='@(url |Other Requirements|)'>Host System</see>
 </code>

 <p>On your first reading, don't explore other links you see in the tour.  Some
 of them lead to the Walking Tour, which you can take coherently when you
 finish this tour.  Others lead into the extensive hyptertext documentation and
 you are liable to get lost there unless you're trying to answer a specific
 question.  We intend the tour to take about 10 minutes of your time.</p>

 <p><see topic='@(url |About the ACL2 Home Page|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |A Walking Tour of ACL2|
  :parents (|Pages Written Especially for the Tours|)
  :short "A Walking Tour of ACL2"
  :long "<p><see topic='@(url |Common Lisp|)'><img
 src='large-walking.gif'></img></see></p>

 <p>On this tour you will learn a little more about the ACL2 logic, the theorem
 prover, and the user interface.</p>

 <p>This time we will stick with really simple things, such as the
 associativity of list concatenation.</p>

 <p>We assume you have taken the Flying Tour but that you did not necessarily
 follow all the ``off-tour'' links because we encouraged you not to.  With the
 Walking Tour we encourage you to visit off-tour links &mdash; provided they
 are not marked with the tiny warning sign (<see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>).
 But they are ``branches'' in the tour that lead to ``dead ends.''  When you
 reach a dead end, remember to use your browser's Back Button to return to the
 Walking Tour to continue.</p>

 <p>When you get to the end of the tour we'll give you a chance to repeat
 quickly both the Flying and the Walking Tours to visit any off-tour links
 still of interest.</p>

 <p><see topic='@(url |Common Lisp|)'><img src='walking.gif'></img></see></p>")

(defxdoc |A Sketch of How the Rewriter Works|
  :parents (|Pages Written Especially for the Tours|)
  :short "A Sketch of How the Rewriter Works"
  :long "<p>Below we show the first target term, extracted from the current
 conjecture.  Below it we show the associativity rule.</p>

 <p><img src='uaa-rewrite.gif'></img></p>

 <p>The variables of the rewrite rule are <b>instantiated</b> so that the
 <b>left-hand side</b> of the rule matches the target:</p>

 @({
       variable          term from target
         a                     x1
         b                     x2
         c                     (app x3 x4)
 })

 <p>Then the target is <b>replaced</b> by the instantiated <b>right-hand
 side</b> of the rule.</p>

 <p>Sometimes rules have <b>hypotheses</b>.  To make a long story short, if the
 rule has hypotheses, then after matching the left-hand side, the rewriter
 instantiates the hypotheses and rewrites them recursively.  This is called
 <b>backchaining</b>.  If they all rewrite to true, then the target is replaced
 as above.</p>

 <p>We discuss the rewriter in more detail in the extended introduction to how
 to use the theorem prover, see @(see introduction-to-the-theorem-prover),
 which we will recommend you work through <b>after</b> you have finished the
 two tours.</p>")

(defxdoc |A Tiny Warning Sign|
  :parents (|Pages Written Especially for the Tours|)
  :short "A Tiny Warning Sign"
  :long "<p><img src='warning.gif'></img></p>

 <p>This warning sign, which usually appears as ``<icon src='twarning.gif'/>'',
 indicates that the link it marks takes you into ACL2's online
 documentation.</p>

 <p>The documentation is a vast graph of documented topics intended to help the
 <i>user</i> of ACL2 rather than the <i>potential user</i>.  If you are
 exploring ACL2's home page to learn about the system, perhaps you should go
 back rather than follow the link marked with this sign.  But you are welcome
 to explore the online documentation as well.  Good luck.</p>")

(defxdoc |A Trivial Proof|
  :parents (|Pages Written Especially for the Tours|)
  :short "A Trivial Proof"
  :long "<p><img src='concrete-proof.gif'></img></p>")

(defxdoc |A Typical State|
  :parents (|Pages Written Especially for the Tours|)
  :short "A Typical State"
  :long "<p><see topic='@(url |Functions for Manipulating these Objects|)'><img
 src='flying.gif'></img></see></p>

 <p><img src='state-object.gif'></img></p>

 <p>Observe that the states in typical models talk about</p>

 <code>
 <b>booleans</b>    <b>integers</b>   <b>vectors</b>     <b>records</b>   <b>caches</b>
 <b>bits</b>        <b>symbols</b>    <b>arrays</b>      <b>stacks</b>    <b>files</b>
 <b>characters</b>  <b>strings</b>    <b>sequences</b>   <b>tables</b>    <b>directories</b>
 </code>

 <p>These objects are <b>discrete</b> rather than <b>continuous</b>;
 furthermore they are built incrementally or <b>inductively</b> by repeatedly
 using primitive operations to put together smaller pieces.</p>

 <p>The functions we need to manipulate these objects do things like
 <b>concatenate</b>, <b>reverse</b>, <b>sort</b>, <b>search</b>, <b>count</b>,
 etc.</p>

 <p><see topic='@(url |Functions for Manipulating these Objects|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |ACL2 Characters|
  :parents (|Pages Written Especially for the Tours|)
  :short "ACL2 Characters"
  :long "<p>ACL2 accepts 256 distinct characters, which are the characters
 obtained by applying the function @(tsee code-char) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 to each integer from 0 to 255.  Among these, Common Lisp designates certain
 ones as @('*standard-characters*'), namely those of the form @('(code-char
 n)') where n is from 33 to 126, together with @('#\\Newline') and
 @('#\\Space').  The actual standard characters may be viewed by evaluating the
 constant expression @('*standard-chars*').</p>

 <p>The standard character constants are written by writing a hash mark
 followed by a backslash (#\\) followed by the character.</p>

 <p>The function @(tsee characterp) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 recognizes characters.  For more details, See @(see characters) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>.</p>")

(defxdoc |ACL2 Conses or Ordered Pairs|
  :parents (|Pages Written Especially for the Tours|)
  :short "ACL2 Conses or Ordered Pairs"
  :long "<p>The function @(tsee cons) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 creates an ordered pair.  @(tsee Car) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see> and
 @(tsee cdr) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> return the first and second components,
 respectively, of an ordered pair.  The function @(tsee consp) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 recognizes ordered pairs.</p>

 <p>Ordered pairs are used to represent lists and trees.  See any Common Lisp
 documentation for a discussion of how list constants are written and for the
 many list processing functions available.  Also, see @(see programming) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 where we list all the ACL2 primitive functions.</p>

 <p>Here are some examples of list constants to suggest their syntax.</p>

 @({
  '(a . b)                ; a pair whose car is 'a and cdr is 'b
  '(a . nil)              ; a pair whose car is 'a and cdr is nil
  '(a)                    ; another way to write the same thing
  '(a b)                  ; a pair whose car is 'a and cdr is '(b)
  '(a b c)                ; a pair whose car is 'a and cdr is '(b c)
                          ;  i.e., a list of three symbols, a, b, and c.
  '((a . 1) (b . 2))      ; a list of two pairs
 })

 <p>It is useful to distinguish ``proper'' conses from ``improper'' ones, the
 former being those cons trees whose right-most branch terminates with
 @('nil').  A ``true list'' (see @(see true-listp) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>) is
 either @('nil') or a proper cons.  @('(A b c . 7)') is an improper cons and
 hence not a true list.</p>")

(defxdoc |ACL2 Strings|
  :parents (|Pages Written Especially for the Tours|)
  :short "ACL2 Strings"
  :long "<p>Strings of ACL2 <see topic='@(url
 |ACL2 Characters|)'>characters</see> are written as sequences of characters
 delimited by ``double quotation marks''
 (\").  To put a double quotation mark in a string (or, any other character
 such as backslash or newline that seems to cause problems), escape it by
 preceding it with a backslash (\\).</p>

 <p>The function @(tsee stringp) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 recognizes strings and @(tsee char) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 will fetch the nth character of a string.  There are many other primitives for
 handling strings, such as @(tsee string<) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see> for
 comparing two strings lexicographically.  We suggest you See @(see
 programming) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> where we list all of the primitive ACL2 functions.
 Alternatively, see any Common Lisp language documentation.</p>")

(defxdoc |ACL2 Symbols|
  :parents (|Pages Written Especially for the Tours|)
  :short "ACL2 Symbols"
  :long "<p>Common Lisp's symbols are a data type representing words.  They are
 frequently regarded as atomic objects in the sense that they are not
 frequently broken down into their constituents.  Often the only important
 properties of symbols is that they are not numbers, characters, strings, or
 lists and that two symbols are not equal if they look different (!).  Examples
 of symbols include @('PLUS') and @('SMITH::ABC').  All function and variable
 names in ACL2 are symbols.  When symbols are used as constants they must be
 quoted, as in @(''PLUS').</p>

 <p>The symbol @('T') is commonly used as the Boolean ``true.''  The symbol
 @('NIL') is commonly used both as the Boolean ``false'' and as the ``empty
 list.''  Despite sometimes being called the ``empty list'' @('NIL') is a
 <b>symbol</b> not an ``empty cons.''  Unlike other symbols, @('T') and
 @('NIL') may be used as constants without quoting them.</p>

 <p>Usually, symbols are written as sequences of alphanumeric characters other
 than those denoting numbers.  Thus, @('A12'), @('+1A') and @('1+') are symbols
 but @('+12') is a number.  Roughly speaking, when symbols are read lower case
 characters are converted to upper case, so we frequently do not distinguish
 @('ABC') from @('Abc') or @('abc').  Click <see topic='@(url
 |Conversion|)'>here</see> for information about case conversion when symbols
 are read.  However, any character can be used in a symbol, but some characters
 must be ``escaped'' to allow the Lisp reader to parse the sequence as a
 symbol.  For example, @('|Abc|') is a symbol whose first character is
 capitalized and whose remaining characters are in lower case.  @('|An odd
 duck|') is a symbol containing two #\\Space characters.  See any Common Lisp
 documentation for the syntactic rules for symbols.</p>

 <p>Technically, a symbol is a special kind of pair consisting of a package
 name (which is a string) and a symbol name (which is also a string).  (See
 @(see symbol-package-name) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see> and
 see @(see symbol-name) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>.)  The symbol SMITH::ABC is said to be in package
 \"SMITH\" and to have the symbol name \"ABC\".  The symbol @('ABC') in package
 \"SMITH\" is generally not equal to the symbol @('ABC') in package \"JONES\".
 However, it is possible to ``import'' symbols from one package into another
 one, but in ACL2 this can only be done when the package is created.  (See
 @(see defpkg) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>.)  If the @(tsee current-package) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see> is
 \"SMITH\" then @('SMITH::ABC') may be more briefly written as just @('ABC').
 @(tsee Intern) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> ``creates'' a symbol of a given name in a given
 package.</p>")

(defxdoc |ACL2 System Architecture|
  :parents (|Pages Written Especially for the Tours|)
  :short "ACL2 System Architecture"
  :long "<p><see topic='@(url
 |Rewrite Rules are Generated from DEFTHM Events|)'><img
 src='walking.gif'></img></see></p>

 <p><img src='acl2-system-architecture.gif'></img></p>

 <p>The user interacts with the theorem prover by giving it definitions,
 theorems and advice.  Most often the advice is about how to store each proved
 theorem as a rule.  Sometimes the advice is about how to prove a specific
 theorem.</p>

 <p>The database consists of all the rules ACL2 ``knows.''  It is possible to
 include in the database all of the rules in some certified file of other
 events.  Such certified files are called @(see books) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>.</p>

 <p>Interesting proofs are usually built on top of many books, some of which
 are written especially for that problem domain and others of which are about
 oft-used domains, like arithmetic or list processing.  ACL2's distribution
 includes many books written by users.  See the ``books'' link under the
 <b>Lemma Libraries and Utilities</b> <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 link of the ACL2 home page.</p>

 <p><see topic='@(url |Rewrite Rules are Generated from DEFTHM Events|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |ACL2 as an Interactive Theorem Prover|
  :parents (|Pages Written Especially for the Tours|)
  :short "ACL2 as an Interactive Theorem Prover"
  :long "<p>The ACL2 theorem prover finds proofs in the ACL2 logic.  It can be
 automatic.  But most often the user must help it.</p>

 <p><img src='interactive-theorem-prover.gif'></img></p>

 <p>The user usually guides ACL2 by suggesting that it first prove key
 <b>lemmas</b>.  Lemmas are just theorems used in the proofs of other
 theorems.</p>")

(defxdoc |ACL2 as an Interactive Theorem Prover (cont)|
  :parents (|Pages Written Especially for the Tours|)
  :short "ACL2 as an Interactive Theorem Prover (cont)"
  :long "<p><see topic='@(url |ACL2 System Architecture|)'><img
 src='walking.gif'></img></see></p>

 <p>When ACL2 proves a lemma, it is converted into one or more <b>rules</b> and
 stored in a <b>database</b>.  The theorem prover is <b>rule-driven</b>.  By
 proving lemmas you can configure ACL2 to behave in certain ways when it is
 trying to prove formulas in a certain problem domain.  The expert user can
 make ACL2 do amazingly ``smart'' looking things.</p>

 <p>But it would be wrong to think that ACL2 <i>knows</i> the mathematical
 content of a formula just because it has proved it.  What ACL2 knows &mdash;
 all ACL2 knows &mdash; is what is encoded in its rules.  There are many types
 of rules (see @(see rule-classes) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>).</p>

 <p>Many formulas can be effectively coded as rules.  But by the same token, it
 is possible to encode a formula as a rule that is so ineffective it cannot
 even prove itself!</p>

 <p>The way a formula is stored as a rule is entirely up to the user.  That is,
 <b>you</b> determine how ACL2 should use each formula that it proves.</p>

 <p>The most common kind of rule is the <b>rewrite rule</b>.  It is so common
 that if you don't tell ACL2 how to store a formula, it stores it as a rewrite
 rule.</p>

 <p><see topic='@(url |ACL2 System Architecture|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |ACL2 is an Untyped Language|
  :parents (|Pages Written Especially for the Tours|)
  :short "ACL2 is an Untyped Language"
  :long "<p>The example</p>

 <code>
 ACL2 !&gt;<b>(app '(a b c) 27)</b>
 (A B C . 27)
 </code>

 <p>illustrates the fact that ACL2's logic is untyped (click <see topic='@(url
 |About Types|)'>here</see> for a brief discussion of the typed versus untyped
 nature of the logic).</p>

 <p>The definition of @('app') makes no restriction of the arguments to lists.
 The definition says that if the first argument satisfies @(tsee endp) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 then return the second argument.  In this example, when @('app') has recursed
 three times down the @('cdr') of its first argument, @(''(a b c)'), it reaches
 the final @('nil'), which satisfies @('endp'), and so 27 is returned.  It is
 naturally consed into the emerging list as the function returns from
 successive recursive calls (since @('cons') does not require its arguments to
 be lists, either).  The result is an ``improper'' list, @('(a b c . 27)').</p>

 <p>You can think of @('(app x y)') as building a binary tree by replacing the
 right-most tip of the tree @('x') with the tree @('y').</p>")

(defxdoc |About Models|
  :parents (|Pages Written Especially for the Tours|)
  :short "About Models"
  :long "<p><see topic='@(url |Models of Computer Hardware and Software|)'><img
 src='flying.gif'></img></see></p>

 <p>ACL2 is used to construct mathematical models of computer hardware and
 software (i.e., ``digital systems'').</p>

 <p><img src='computing-machine.gif'></img></p>

 <p>A <b>mathematical model</b> is a set of mathematical formulas used to
 predict the behavior of some artifact.</p>

 <p>The use of mathematical models allows <b>faster</b> and <b>cheaper</b>
 delivery of <b>better</b> systems.</p>

 <p>Models need not be <b>complete</b> or <b>perfectly accurate</b> to be
 useful to the trained engineer.</p>

 <p>Click <see topic='@(url |Models in Engineering|)'>here</see> for more
 discussion of these assertions in an engineering context.</p>

 <p><see topic='@(url |Models of Computer Hardware and Software|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |About Types|
  :parents (|Pages Written Especially for the Tours|)
  :short "About Types"
  :long "<p>The universe of ACL2 objects includes objects of many different
 types.  For example, @('t') is a ``symbol'' and 3 is an ``integer.''  Roughly
 speaking the objects of ACL2 can be partitioned into the following types:</p>

 <code> <see topic='@(url |Numbers in ACL2|)'>Numbers</see> @('3, -22/7, #c(3
 5/2)') <see topic='@(url |ACL2 Characters|)'>Characters</see> @('#\\A, #\\a,
 #\\Space') <see topic='@(url |ACL2 Strings|)'>Strings</see> @('\"This is a
 string.\"') <see topic='@(url |ACL2 Symbols|)'>Symbols</see> @(''abc,
 'smith::abc') <see topic='@(url |ACL2 Conses or Ordered Pairs|)'>Conses (or
 Ordered Pairs)</see> @(''((a . 1) (b . 2))') </code>

 <p>When proving theorems it is important to know the types of object returned
 by a term.  ACL2 uses a complicated heuristic algorithm, called @(tsee
 type-set) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>, to determine what types of objects a term may
 produce.  The user can more or less program the @('type-set') algorithm by
 proving @(tsee type-prescription) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 rules.</p>

 <p>ACL2 is an ``untyped'' logic in the sense that the syntax is not typed: It
 is legal to apply a function symbol of n arguments to any n terms, regardless
 of the types of the argument terms.  Thus, it is permitted to write such odd
 expressions as @('(+ t 3)') which sums the symbol @('t') and the integer 3.
 Common Lisp does not prohibit such expressions.  We like untyped languages
 because they are simple to describe, though proving theorems about them can be
 awkward because, unless one is careful in the way one defines or states
 things, unusual cases (like @('(+ t 3)')) can arise.</p>

 <p>To make theorem proving easier in ACL2, the axioms actually define a value
 for such terms.  The value of @('(+ t 3)') is 3; under the ACL2 axioms,
 non-numeric arguments to @('+') are treated as though they were 0.</p>

 <p>You might immediately wonder about our claim that ACL2 is Common Lisp,
 since @('(+ t 3)') is ``an error'' (and will sometimes even ``signal an
 error'') in Common Lisp.  It is to handle this problem that ACL2 has
 <b>guards</b>.  We will discuss guards later in the Walking Tour.  However,
 many new users simply ignore the issue of guards entirely and that is what we
 recommend for now.</p>

 <p>You should now return to <see topic='@(url
 |Revisiting the Admission of App|)'>the Walking Tour</see>.</p>")

(defxdoc |About the ACL2 Home Page|
  :parents (|Pages Written Especially for the Tours|)
  :short "About the ACL2 Home Page"
  :long "<p><see topic='@(url |What Is ACL2(Q)|)'><img
 src='flying.gif'></img></see></p>

 <p>The ACL2 Home Page is integrated into the ACL2 online documentation.  Over
 4 megabytes of hypertext is available here.</p>

 <p>The vast majority of the text is user-level documentation.  For example, to
 find out about @(see rewrite) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 rules you could click on the link.  (If you do that, remember to use your
 browser's <b>Back Button</b> to come back here.)</p>

 <p>The tiny warning signs <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> mark links that lead out of the introductory-level
 material and into the user documentation.  We advise against following such
 links upon your first reading of the documentation.</p>

 <p>At the end of the tours you will have a chance to revisit them quickly to
 explore alternative paths more fully.</p>

 <p>Finally, every page contains two icons at the bottom.  The ACL2 icon leads
 you back to the ACL2 Home Page.  The Index icon allows you to browse an
 alphabetical listing of all the topics in ACL2's online documentation.  But
 both icons take you off the main route of the tour.</p>

 <p><see topic='@(url |What Is ACL2(Q)|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |About the Admission of Recursive Definitions|
  :parents (|Pages Written Especially for the Tours|)
  :short "About the Admission of Recursive Definitions"
  :long "<p>You can't just add any formula as an axiom or definition and expect
 the logic to stay sound!  For example, if we were permitted to define @('(APP
 X Y)') so that it was equal to @('(NOT (APP X Y))') then we could prove
 anything.  The purported ``definition'' of @('APP') must have several
 properties to be admitted to the logic as a new axiom.</p>

 <p>The key property a recursive definition must have is that the recursion
 terminate.  This, along with some syntactic criteria, ensures us that there
 exists a function satisfying the definition.</p>

 <p>Termination must be proved before the definition is admitted.  This is done
 in general by finding a measure of the arguments of the function and a
 well-founded relation such that the arguments ``get smaller'' every time a
 recursive branch is taken.</p>

 <p>For @('app') the measure is the ``size'' of the first argument, @('x'), as
 determined by the primitive function @(tsee acl2-count) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>.
 The well-founded relation used in this example is @(tsee o-p) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>,
 which is the standard ordering on the ordinals less than ``epsilon naught.''
 These particular choices for @('app') were made ``automatically'' by ACL2.
 But they are in fact determined by various ``default'' settings.  The user of
 ACL2 can change the defaults or specify a ``hint'' to the @(tsee defun) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 command to specify the measure and relation.</p>

 <p>You should now return to <see topic='@(url
 |Revisiting the Admission of App|)'>the Walking Tour</see>.</p>")

(defxdoc |About the Prompt|
  :parents (|Pages Written Especially for the Tours|)
  :short "About the Prompt"
  :long "<p>The string ``@('ACL2 !>')'' is the ACL2 prompt.</p>

 <p>The prompt tells the user that an ACL2 @(see command) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>is
 expected.  In addition, the prompt tells us a little about the current state
 of the ACL2 command interpreter.  We explain the prompt briefly below.  But
 first we talk about the command interpreter.</p>

 <p>An ACL2 command is generally a Lisp expression to be evaluated.  There are
 some unusual commands (such as :@(see q) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see> for
 <b>quitting</b> ACL2) which cause other behavior.  But most commands are read,
 evaluated, and then have their results printed.  Thus, we call the command
 interpreter a ``read-eval-print loop.''  The ACL2 command interpreter is named
 @(tsee LD) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> (after Lisp's ``load'').</p>

 <p>When a command is read, all the symbols in it are converted to uppercase.
 Thus, typing @('(defun app ...)') is the same as typing @('(DEFUN APP ...)')
 or @('(defun App ...)').  There are ways to force lowercase case characters
 into symbols but we won't discuss them here.  A consequence of Common Lisp's
 default uppercasing is that you'll see a general lack of concern over the case
 used when symbols are displayed in this documentation.</p>

 <p>In addition, symbols ``belong'' to ``packages'' which give the user a way
 to control namespaces.  The prompt tells us which package is the default one,
 namely @('\"ACL2\"').  That means when we call @('car'), for example, we are
 invoking the standard definition of that symbol.  If the packager were
 @('\"JONES\"') then @('car') would refer to the definition of that symbol in
 that package (which may or may not be different depending on what symbols were
 imported into that package.</p>

 <p>A command like <b>(defun app (x y) ...)</b> causes ACL2 to evaluate the
 @(see defun) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> function on <b>app</b>, <b>(x y)</b> and
 <b>...</b>.  When that command is evaluated it prints some information to the
 terminal explaining the processing of the proposed definition.  It returns the
 symbol @('APP') as its value, which is printed by the command interpreter.
 (Actually, @('defun') is not a function but a <see topic='@(url
 DEFMACRO)'>macro</see> <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> which expands to a form that involves @(tsee state)
 <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>, a necessary precondition to printing output to the
 terminal and to ``changing'' the set of axioms.  But we do not discuss this
 further here.)</p>

 <p>The @('defun') command is an example of a special kind of command called an
 ``event.''  @(see Events) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> are those commands that change the ``logical
 world'' by adding such things as axioms or theorems to ACL2's database.  See
 @(see world) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>.  But not every command is an event command.</p>

 <p>A command like <b>(app '(1 2 3) '(4 5 6 7))</b> is an example of a
 non-event.  It is processed the same general way: the function <b>app</b> is
 applied to the indicated arguments and the result is printed.  The function
 <b>app</b> does not print anything and does not change the ``world.''</p>

 <p>A third kind of command is one that display information about the current
 logical world or that ``roll back'' to previous versions of the world.  Such
 commands are called ``@(see history)'' <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 commands.</p>

 <p>What does the ACL2 prompt tell us about the read-eval-print loop?  The
 prompt ``@('ACL2 !>')'' tells us that the command will be read with @(tsee
 current-package) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> set to @('\"ACL2\"'), that guard checking (see
 @(see set-guard-checking) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>) is on (``@('!')''), and that we are at the
 top-level (there is only one ``@('>')'').  For more about the prompt, see
 @(see default-print-prompt) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>.</p>

 <p>You should now return to <see topic='@(url
 |Revisiting the Admission of App|)'>the Walking Tour</see>.</p>")

(defxdoc |An Example Common Lisp Function Definition|
  :parents (|Pages Written Especially for the Tours|)
  :short "An Example Common Lisp Function Definition"
  :long "<p><see topic='@(url |An Example of ACL2 in Use|)'><img
 src='walking.gif'></img></see></p>

 <p>Consider the binary trees @('x') and @('y') below.</p>

 <p><img src='binary-trees-x-y.gif'></img></p>

 <p>In Lisp, @('x') is written as the list @(''(A B)') or, equivalently, as
 @(''(A B . NIL)').  Similarly, @('y') may be written @(''(C D E)').  Suppose
 we wish to replace the right-most tip of @('x') by the entire tree @('y').
 This is denoted @('(app x y)'), where @('app') stands for ``append''.</p>

 <p><img src='binary-trees-app.gif'></img></p>

 <p>We can define @('app') with:</p>

 <code>
 <b>(defun app (x y)</b>                           <i>; Concatenate x and y.</i>
   <b>(declare (type (satisfies true-listp) x))</b><i>; We expect x to end in NIL.</i>
   <b>(cond ((endp x) y)</b>                       <i>; If x is empty, return y.</i>
         <b>(t (cons (car x)</b>                   <i>; Else, copy first node</i>
                  <b>(app (cdr x) y)))))</b>       <i>;  and recur into next.</i>
 </code>

 <p>If you defined this function in some Common Lisp, then to run @('app') on
 the @('x') and @('y') above you could then type</p>

 @({
  (app '(A B) '(C D E))
 })

 <p>and Common Lisp will print the result @('(A B C D E)').</p>

 <p><see topic='@(url |An Example of ACL2 in Use|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |An Example of ACL2 in Use|
  :parents (|Pages Written Especially for the Tours|)
  :short "An Example of ACL2 in Use"
  :long "<p><see topic='@(url |How To Find Out about ACL2 Functions|)'><img
 src='walking.gif'></img></see></p>

 <p>To introduce you to ACL2 we will consider the @('app') function discussed
 in the <see topic='@(url |Common Lisp|)'>Common Lisp</see> page, <b>except</b>
 we will omit for the moment the <b>declare</b> form, which in ACL2 is called a
 <b>guard</b>.</p>

 <p>Guards are arbitrary ACL2 terms that express the ``intended domain'' of
 functions.  In that sense, guards are akin to type signatures.  However,
 Common Lisp and ACL2 are untyped programming languages: while the language
 supports several different data types and the types of objects can be
 determined by predicates at runtime, any type of object may be passed to any
 function.  Thus, guards are ``extra-logical.''  Recognizing both the practical
 and intellectual value of knowing that your functions are applied to the kinds
 of objects you intend, ACL2 imposes guards on Common Lisp and provides a means
 of proving that functions are used as intended.  But the story is necessarily
 complicated and we do not recommend it to the new user.  Get used to the fact
 that any ACL2 function may be applied to any objects and program accordingly.
 Read about guards later.</p>

 <p>Here is the definition again</p>

 <code>
 <b>(defun app (x y)</b>
   <b>(cond ((endp x) y)</b>
         <b>(t (cons (car x) </b>
                  <b>(app (cdr x) y)))))</b>
 </code>

 <p>The next few stops along the Walking Tour will show you</p>

 <code> * how to use the ACL2 documentation, * what happens when the above
 definition is submitted to ACL2, * what happens when you evaluate calls of
 @('app'), * what one simple theorem about @('app') looks like, * how ACL2
 proves the theorem, and * how that theorem can be used in another proof.
 </code>

 <p>Along the way we will talk about the <b>definitional principle</b>,
 <b>types</b>, the ACL2 <b>read-eval-print loop</b>, and how the <b>theorem
 prover</b> works.</p>

 <p>When we complete this part of the tour we will return briefly to the notion
 of <b>guards</b> and revisit several of the topics above in that context.</p>

 <p><see topic='@(url |How To Find Out about ACL2 Functions|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |Analyzing Common Lisp Models|
  :parents (|Pages Written Especially for the Tours|)
  :short "Analyzing Common Lisp Models"
  :long "<p>To analyze a model you must be able to reason about the operations
 and relations involved.  Perhaps, for example, some aspect of the model
 depends upon the fact that the concatenation operation is associative.</p>

 <p>In any Common Lisp you can confirm that</p>

 @({
  (app '(A B) (app '(C D) '(E F)))
 })

 <p>and</p>

 @({
  (app (app '(A B) '(C D)) '(E F)))
 })

 <p>both evaluate to the same thing, @('(A B C D E F)').</p>

 <p>But what distinguishes ACL2 (the logic) from applicative Common Lisp (the
 language) is that in ACL2 you can <b>prove</b> that the concatenation function
 @('app') is associative when its arguments are true-lists, whereas in Common
 Lisp all you can do is test that proposition.</p>

 <p>That is, in ACL2 it makes sense to say that the following formula is a
 ``theorem.''</p>

 <code>
 <b>Theorem</b> Associativity of App
 (implies (and (true-listp a)
               (true-listp b))
          (equal (app (app a b) c)
                 (app a (app b c))))
 </code>

 <p>Theorems about the properties of models are proved by symbolically
 manipulating the operations and relations involved.  If the concatenation of
 sequences is involved in your model, then you may well need the theorem above
 in order to that your model has some particular property.</p>")

(defxdoc |Common Lisp|
  :parents (|Pages Written Especially for the Tours|)
  :short "Common Lisp"
  :long "<p><see topic='@(url
 |An Example Common Lisp Function Definition|)'><img
 src='walking.gif'></img></see></p>

 <p><img src='common-lisp.gif'></img></p>

 <p>The logic of ACL2 is based on Common Lisp.</p>

 <p>Common Lisp is the standard list processing programming language.  It is
 documented in: Guy L. Steele, <a
 href='https://www.cs.cmu.edu/Groups/AI/html/cltl/cltl2.html'><b>Common Lisp
 The Language</b></a>, Digital Press, 12 Crosby Drive, Bedford, MA 01730,
 1990.</p>

 <p>ACL2 formalizes only a subset of Common Lisp.  It includes such familiar
 Lisp functions as @('cons'), @('car') and @('cdr') for creating and
 manipulating list structures, various arithmetic primitives such as @('+'),
 @('*'), @('expt') and @('<='), and @('intern') and @('symbol-name') for
 creating and manipulating symbols.  Control primitives include @('cond'),
 @('case') and @('if'), as well as function call, including recursion.  New
 functions are defined with @('defun') and macros with @('defmacro').  See
 @(see programming) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> for a list of the Common Lisp primitives supported
 by ACL2.</p>

 <p>ACL2 supports five of Common Lisp's datatypes:</p>

 <p>* the precisely represented, unbounded numbers (integers, rationals, and
 the complex numbers with rational components, called the ``complex rationals''
 here),</p>

 <p>* the characters with ASCII codes between 0 and 255</p>

 <p>* strings of such characters</p>

 <p>* symbols (including packages)</p>

 <p>* conses</p>

 <p>ACL2 is a very small subset of full Common Lisp.  ACL2 does not include the
 Common Lisp Object System (CLOS), higher order functions, circular structures,
 and other aspects of Common Lisp that are <b>non-applicative</b>.  Roughly
 speaking, a language is applicative if it follows the rules of function
 application.  For example, @('f(x)') must be equal to @('f(x)'), which means,
 among other things, that the value of @('f') must not be affected by ``global
 variables'' and the object @('x') must not change over time.</p>

 <p><see topic='@(url |An Example Common Lisp Function Definition|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |Common Lisp as a Modeling Language|
  :parents (|Pages Written Especially for the Tours|)
  :short "Common Lisp as a Modeling Language"
  :long "<p><img src='common-lisp.gif'></img></p>

 <p>In ACL2 we have adopted Common Lisp as the basis of our modeling language.
 If you have already read our brief note on Common Lisp and recall the example
 of @('app'), please proceed.  Otherwise click <see topic='@(url
 |Common Lisp|)'>here</see> for an exceedingly brief introduction to Common
 Lisp and then come <b>back</b> here.</p>

 <p>In Common Lisp it is very easy to write systems of formulas that manipulate
 discrete, inductively constructed data objects.  In building a model you might
 need to formalize the notion of sequences and define such operations as
 concatenation, length, whether one is a permutation of the other, etc.  It is
 easy to do this in Common Lisp.  Furthermore, if you have a Common Lisp
 ``theory of sequences'' you can <b>run</b> the operations and relations you
 define.  That is, you can execute the functions on concrete data to see what
 results your formulas produce.</p>

 <p>If you define the function @('app') as shown above and then type</p>

 @({
  (app '(A B) '(C D E))
 })

 <p>in any Common Lisp, the answer will be computed and will be @('(A B C D
 E)').</p>

 <p>The <b>executable</b> nature of Common Lisp and thus of ACL2 is very handy
 when producing models.</p>

 <p>But executability is not enough for a modeling language because the purpose
 of models is to permit analysis.</p>

 <p>Click <see topic='@(url |Analyzing Common Lisp Models|)'>here</see> to
 continue.</p>")

(defxdoc |Conversion|
  :parents (|Pages Written Especially for the Tours|)
  :short "Conversion to Uppercase"
  :long "<p>When symbols are read by Common Lisp they are converted to upper
 case.  Note carefully that this remark applies to the characters in
 <i>symbols</i>.  The characters in strings are not converted upper case.</p>

 <p>To type a symbol containing lower case characters you can enclose the
 symbol in vertical bars, as in @('|AbC|') or you can put a ``backslash''
 before each lower case character you wish to preserve, as in @('A\\bC').
 @('|AbC|') and @('A\\bC') are two different ways of writing the same symbol
 (just like 2/4 and 1/2 are two different ways of writing the same rational and
 123 and 0123 are two different ways to write the same natural number).  The
 symbol has three characters in its name, the middle one of which is a lower
 case b.</p>")

(defxdoc |Corroborating Models|
  :parents (|Pages Written Especially for the Tours|)
  :short "Corroborating Models"
  :long "<p><see topic='@(url |Models of Computer Hardware and Software|)'><img
 src='flying.gif'></img></see></p>

 <p>After producing a model, it must be <b>corroborated</b> against reality.
 The Falling Body Model has been corroborated by a vast number of experiments
 in which the time and distance were measured and compared according to the
 formula.  In general all models must be corroborated by experiment.</p>

 <p>The Falling Body Model can be derived from deeper models, namely Newton's
 laws of motion and the assertion that, over the limited distances concerned,
 graviation exerts a constant acceleration on the object.  When the model in
 question can be derived from other models, it is the other models that are
 being corroborated by our experiments.</p>

 <p>Because nature is not formal, we cannot <b>prove</b> that our models of it
 are correct.  All we can do is test our models against nature's behavior.</p>

 <p>Such testing often exposes restrictions on the applicability of our models.
 For example, the Falling Body Model is inaccurate if air resistance is
 significant.  Thus, we learn not to use that model to predict how long it
 takes a feather to fall from a 200 foot tower in the earth's atmosphere.</p>

 <p>In addition, attempts at corroboration might reveal that the model is
 actually incorrect.  Careful measurements might expose the fact that the
 gravitational force increases as the body falls closer to earth.  Very careful
 measurements might reveal relativistic effects.  Technically, the familiar
 Falling Body Model is just wrong, even under excessive restrictions such as
 ``in a perfect vacuum'' and ``over small distances.''  But it is an incredibly
 useful model nonetheless.</p>

 <p>There are several morals here.</p>

 <p><b>Models need not be complete to be useful.</b></p>

 <p><b>Models need not be perfectly accurate to be useful.</b></p>

 <p><b>The user of a model must understand its limitations.</b></p>

 <p><see topic='@(url |Models of Computer Hardware and Software|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |Evaluating App on Sample Input|
  :parents (|Pages Written Especially for the Tours|)
  :short "Evaluating App on Sample Input"
  :long "<p><see topic='@(url |The Associativity of App|)'><img
 src='walking.gif'></img></see></p>

 <p><img src='green-line.gif'></img></p>

 <code>
 ACL2 !&gt;<b>(app nil '(x y z))</b>
 (X Y Z)

 ACL2 !&gt;<b>(app '(1 2 3) '(4 5 6 7))</b>
 (1 2 3 4 5 6 7)

 ACL2 !&gt;<b>(app '(a b c d e f g) '(x y z))</b>   ; click <see topic='@(url |Conversion|)'>here</see> for an explanation
 (A B C D E F G X Y Z)

 ACL2 !&gt;<b>(app (app '(1 2) '(3 4)) '(5 6))</b>
 (1 2 3 4 5 6)

 ACL2 !&gt;<b>(app '(1 2) (app '(3 4) '(5 6)))</b>
 (1 2 3 4 5 6)

 ACL2!&gt;<b>(let ((a '(1 2))</b>
             <b>(b '(3 4))</b>
             <b>(c '(5 6)))</b>
         <b>(equal (app (app a b) c)</b>
                <b>(app a (app b c))))</b>
 T
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>As we can see from these examples, ACL2 functions can be executed more or
 less as Common Lisp.</p>

 <p>The last three examples suggest an interesting property of @('app').</p>

 <p><see topic='@(url |The Associativity of App|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |Flawed Induction Candidates in App Example|
  :parents (|Pages Written Especially for the Tours|)
  :short "Flawed Induction Candidates in App Example"
  :long "<p>Induction on <b>a</b> is unflawed: every occurrence of <b>a</b> in
 the conjecture</p>

 <code>
 (equal (app (app <b>a</b> b) c)
        (app <b>a</b> (app b c)))
 </code>

 <p>is in a position being recursively decomposed!</p>

 <p>Now look at the occurrences of @('b').  The first (shown in <b>bold</b>
 below) is in a position that is held constant in the recursion of @('(app a
 b)').  It would be ``bad'' to induct on @('b') here.</p>

 <code>
 (equal (app (app a <b>b</b>) c)
        (app a (app b c)))
 </code>")

(defxdoc |Free Variables in Top-Level Input|
  :parents (|Pages Written Especially for the Tours|)
  :short "Free Variables in Top-Level Input"
  :long "<code>
 ACL2 !&gt;<b>(equal (app (app a b) c)</b>
               <b>(app a (app b c))))</b>

 ACL2 Error in TOP-LEVEL:  Global variables, such as C, B, and A, are
 not allowed. See :DOC ASSIGN and :DOC @@.

 </code>

 <p>ACL2 does not allow ``global variables'' in top-level input.  There is no
 ``top-level binding environment'' to give meaning to these variables.</p>

 <p>Thus, expressions involving no variables can generally be evaluated,</p>

 <code>
 ACL2 !&gt;<b>(equal (app (app '(1 2) '(3 4)) '(5 6))</b>
               <b>(app '(1 2) (app '(3 4) '(5 6))))</b>
 (1 2 3 4 5 6)
 </code>

 <p>but expressions containing variables cannot.</p>

 <p>There is an exception to this rule.  References to ``single-threaded
 objects'' may appear in top-level forms.  See @(see stobj) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>.  A
 single-threaded object is an ACL2 object, usually containing many fields,
 whose use is syntactically restricted so that it may be given as input only to
 certain functions and must be returned as output by certain functions.  These
 restrictions allow single- threaded objects to be efficiently manipulated.
 For example, only a single copy of the object actually exists, even though
 from a logical perspective one might expect the object to be ``copied on
 write.''</p>

 <p>The most commonly used single-threaded object in ACL2 is the ACL2 system
 state, whose current value is always held in the variable @(tsee state) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>.</p>

 <p>ACL2 provides a way for you to use @('state') to save values of
 computations at the top-level and refer to them later.  See @(see assign) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see> and
 @(see @) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>.</p>")

(defxdoc |Functions for Manipulating these Objects|
  :parents (|Pages Written Especially for the Tours|)
  :short "Functions for Manipulating these Objects"
  :long "<p><see topic='@(url |Modeling in ACL2|)'><img
 src='flying.gif'></img></see></p>

 <p>Consider a typical ``stack'' of control frames.</p>

 <p><img src='stack.gif'></img></p>

 <p>Suppose the model required that we express the idea of ``the most recent
 frame whose return program counter points into @('MAIN').''</p>

 <p>The natural expression of this notion involves</p>

 <p><b>function application</b> &mdash; ``fetch the @('return-pc') of this
 frame''</p>

 <p><b>case analysis</b> &mdash; ``<b>if</b> the pc is @('MAIN'), <b>then</b>
 ...''</p>

 <p><b>iteration</b> or <b>recursion</b> &mdash; ``pop this frame off and
 repeat.''</p>

 <p>The designers of ACL2 have taken the position that a <b>programming</b>
 <b>language</b> is the natural language in which to define such notions,
 <b>provided</b> the language has a mathematical foundation so that models can
 be analyzed and properties derived logically.</p>

 <p>Common Lisp is the language supported by ACL2.  To be precise, a small
 applicative subset of Common Lisp is the language supported by ACL2.</p>

 <p><see topic='@(url |Modeling in ACL2|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |Guards|
  :parents (|Pages Written Especially for the Tours|)
  :short "Guards"
  :long "<p>Common Lisp functions are partial; they are not defined for all
 possible inputs.  But ACL2 functions are total.  Roughly speaking, the logical
 function of a given name in ACL2 is a <b>completion</b> of the Common Lisp
 function of the same name obtained by adding some arbitrary but ``natural''
 values on arguments outside the ``intended domain'' of the Common Lisp
 function.</p>

 <p>ACL2 requires that every ACL2 function symbol have a ``guard,'' which may
 be thought of as a predicate on the formals of the function describing the
 intended domain.  The guard on the primitive function @(tsee car) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>,
 for example, is @('(or (consp x) (equal x nil))'), which requires the argument
 to be either an ordered pair or @('nil').  We will discuss later how to
 specify a guard for a defined function; when one is not specified, the guard
 is @('t') which is just to say all arguments are allowed.</p>

 <p><b>But guards are entirely extra-logical</b>: they are not involved in the
 axioms defining functions.  If you put a guard on a defined function, the
 defining axiom added to the logic defines the function on <b>all</b>
 arguments, not just on the guarded domain.</p>

 <p>So what is the purpose of guards?</p>

 <p>The key to the utility of guards is that we provide a mechanism, called
 ``guard verification,'' for checking that all the guards in a formula are
 true.  See @(see verify-guards).  This mechanism will attempt to prove that
 all the guards encountered in the evaluation of a guarded function are true
 every time they are encountered.</p>

 <p>For a thorough discussion of guards, see the paper [km97] in the ACL2 @(see
 bibliography).</p>")

(defxdoc |Guessing the Type of a Newly Admitted Function|
  :parents (|Pages Written Especially for the Tours|)
  :short "Guessing the Type of a Newly Admitted Function"
  :long "<p>When a function is admitted to the logic, ACL2 tries to ``guess''
 what type of object it returns.  This guess is codified as a term that
 expresses a property of the value of the function.  For @('app') the term
 is</p>

 @({
  (OR (CONSP (APP X Y))
      (EQUAL (APP X Y) Y))
 })

 <p>which says that @('app') returns either a cons or its second argument.
 This formula is added to ACL2's rule base as a @(tsee type-prescription) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 rule.  Later we will discuss how rules are used by the ACL2 theorem prover.
 The point here is just that when you add a definition, the database of rules
 is updated, not just by the addition of the definitional axiom, but by several
 new rules.</p>

 <p>You should now return to <see topic='@(url
 |Revisiting the Admission of App|)'>the Walking Tour</see>.</p>")

(defxdoc |Guiding the ACL2 Theorem Prover|
  :parents (|Pages Written Especially for the Tours|)
  :short "Guiding the ACL2 Theorem Prover"
  :long "<p><see topic='@(url
 |ACL2 as an Interactive Theorem Prover (cont)|)'><img
 src='walking.gif'></img></see></p>

 <p>Now that you have seen the theorem prover in action you might be curious as
 to how you guide it.</p>

 <p><img src='interactive-theorem-prover.gif'></img></p>

 <p>Look at the picture above.  It is meant to suggest that <i>Q</i> is an
 important lemma needed for the proof of <i>P</i>.  Note that to lead the
 prover to the proof of <i>P</i> the user first proves <i>Q</i>.  In a way, the
 formulation and proof of <i>Q</i> is a hint to the prover about how to prove
 <i>P</i>.</p>

 <p>The user usually doesn't think of <i>Q</i> or recognize the need to prove
 it separately until he or she sees the theorem prover <b>fail</b> to prove
 <i>P</i> without it ``knowing'' <i>Q</i>.</p>

 <p>The way the user typically discovers the need for <i>Q</i> is to look at
 failed proofs.</p>

 <p><see topic='@(url |ACL2 as an Interactive Theorem Prover (cont)|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |Hey Wait!  Is ACL2 Typed or Untyped(Q)|
  :parents (|Pages Written Especially for the Tours|)
  :short "Hey Wait!  Is ACL2 Typed or Untyped?"
  :long "<p>The example</p>

 <code>
 ACL2 !&gt;<b>(app 7 27)</b>

 ACL2 Error in TOP-LEVEL:  The guard for the function symbol ENDP, which
 is (OR (CONSP X) (EQUAL X NIL)), is violated by the arguments in the
 call (ENDP 7).
 </code>

 <p>illustrates the fact that while ACL2 is an untyped language the ACL2
 evaluator can be configured so as to check ``types'' at runtime.  We should
 not say ``types'' here but ``guards.''  Click <see topic='@(url
 |Undocumented Topic|)'>here</see> for a discussion of guards.</p>

 <p>The guard on @(tsee endp) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 requires its argument to be a true list.  Since 7 is not a true list, and
 since ACL2 is checking guards in this example, an error is signaled by ACL2.
 How do you know ACL2 is checking guards?  Because the prompt tells us (click
 <see topic='@(url |About the Prompt|)'>here</see>) with its ``!''.</p>")

(defxdoc |How Long Does It Take to Become an Effective User(Q)|
  :parents (|Pages Written Especially for the Tours|)
  :short "How Long Does It Take to Become an Effective User?"
  :long "<p><see topic='@(url |Other Requirements|)'><img
 src='flying.gif'></img></see></p>

 <p>We expect that a talented undergraduate majoring in computer science (or
 perhaps mathematics) will probably take several weeks to become an effective
 ACL2 user.  The time will depend, of course, on that student's familiarity
 with logic (or formal methods) and Lisp programming, as well as willingness to
 read and study the ACL2 User's Manual.</p>

 <p>Of course, it is critical to do some projects in order to gain proficiency.
 (Hence access to an ACL2 implementation is also a requirement, for example by
 downloading and installing following links from the ACL2 home page.)  But it
 is critical to start with ``toy'' projects before tackling a ``grand
 challenge.''</p>

 <p><see topic='@(url |Other Requirements|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |How To Find Out about ACL2 Functions|
  :parents (|Pages Written Especially for the Tours|)
  :short "How To Find Out about ACL2 Functions"
  :long "<p><see topic='@(url
 |How To Find Out about ACL2 Functions (cont)|)'><img
 src='walking.gif'></img></see></p>

 <p>Most ACL2 primitives are documented.  Here is the definition of @('app')
 again, with the documented topics highlighted.  <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 All of the links below lead into the ACL2 User's Manual.  So follow these
 links if you wish, but use your <b>Back Button</b> to return here!</p>

 <code>
 (@(see defun) app (x y)
   (@(see cond) ((@(see endp) x) y)
         (t (@(see cons) (@(see car) x)
                  (app (@(see cdr) x) y)))))
 </code>

 <p>By following the link on @(see endp) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see> we
 see that it is a Common Lisp function and is defined to be the same as @(see
 atom) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>, which recognizes non-conses.  But @('endp') has a
 guard.  Since we are ignorning guards for now, we'll ignore the guard issue on
 @('endp').</p>

 <p>So this definition reads ``to @('app') @('x') and @('y'): if @('x') is an
 atom, return @('y'); otherwise, @('app') @('(cdr x)') and @('y') and then cons
 @('(car x)') onto that.''</p>

 <p><see topic='@(url |How To Find Out about ACL2 Functions (cont)|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |How To Find Out about ACL2 Functions (cont)|
  :parents (|Pages Written Especially for the Tours|)
  :short "How To Find Out about ACL2 Functions (cont)"
  :long "<p><see topic='@(url |The Admission of App|)'><img
 src='walking.gif'></img></see></p>

 <p>You can always use the Index <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 icon below to find the documentation of functions.  Try it.  Click on the
 Index icon below.  Then use the Find command of your browser to find ``endp''
 in that document and follow the link.  But remember to come back here.</p>

 <p>The ACL2 documentation is also available in Emacs, via the ACL2-Doc
 browser (see @(see ACL2-Doc)) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>,
 allowing you to explore the hyperlinked documentation in the comfort of a text
 editor that can also interact with ACL2.</p>

 <p>In addition, runtime images of ACL2 have the hyperlinked text as a large
 ACL2 data structure that can be explored with ACL2's <b>:doc</b> command.  If
 you have ACL2 running, try the command <b>:doc endp</b>.</p>

 <p>Another way to find out about ACL2 functions, if you have an ACL2 image
 available, is to use the command :@(tsee args) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 which prints the formals, type, and guard of a function symbol.</p>

 <p>Of course, the ACL2 documentation can also be printed out as a very long
 book but we do not recommend that!  See the ACL2 Home Page to download the
 Postscript.</p>

 <p>Now let's continue with @('app').</p>

 <p><see topic='@(url |The Admission of App|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |Modeling in ACL2|
  :parents (|Pages Written Especially for the Tours|)
  :short "Modeling in ACL2"
  :long "<p><see topic='@(url |Running Models|)'><img
  src='flying.gif'></img></see></p>

 <p><img src='computing-machine-a.gif'></img></p>

 <p>Below we define <b>mc(s,n)</b> to be the function that <b>single-step</b>s
 <b>n</b> times from a given starting state, <b>s</b>.  In Common Lisp,
 ``mc(s,n)'' is written @('(mc s n)').</p>

 <code>
 <b>(defun mc (s n)</b>                     ; To step <b>s</b> <b>n</b> times:
  <b>(if (zp n)</b>                         ; If <b>n</b> is 0
      <b>s</b>                              ;    then return <b>s</b>
      <b>(mc (single-step s) (- n 1))))</b> ;    else step <b>single-step(s)</b>
                                                       <b>n-1</b> times.
 </code>

 <p>This is an example of a formal model in ACL2.</p>

 <p><see topic='@(url |Running Models|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |Models in Engineering|
  :parents (|Pages Written Especially for the Tours|)
  :short "Models in Engineering"
  :long "<p><img src='bridge.gif'></img></p>

 <p>Frequently, engineers use mathematical models.  Use of such models
 frequently lead to</p>

 <p><b>better designs</b>,</p>

 <p><b>faster completion of acceptable products</b>, and</p>

 <p><b>reduced overall cost</b>,</p>

 <p>because models allow the trained user to study the design before it is
 built and analyze its properties.  Usually, testing and analyzing a model is
 cheaper and faster than fabricating and refabricating the product.</p>

 <p><img src='bridge-analysis.gif'></img></p>")

(defxdoc |Models of Computer Hardware and Software|
  :parents (|Pages Written Especially for the Tours|)
  :short "Models of Computer Hardware and Software"
  :long "<p><see topic='@(url |A Typical State|)'><img
 src='flying.gif'></img></see></p>

 <p><img src='computing-machine.gif'></img></p>

 <p>Computing machines, whether hardware or software or some combintation, are
 frequently modeled as ``state machines.''</p>

 <p>To so model a computing machine we must represent its <b>states</b> as
 objects in our mathematical framework.</p>

 <p><b>Transitions</b> are functions or relations on state objects.</p>

 <p>In what language shall we define these objects, functions, and
 relations?</p>

 <p>The mathematical languages we were taught in high school</p>

 <p><b>algebra</b>,</p>

 <p><b>geometry</b>,</p>

 <p><b>trignometry</b>, and</p>

 <p><b>calculus</b></p>

 <p>are often inappropriate for modeling digital systems.  They primarily let
 us talk about numbers and continuous functions.</p>

 <p>To see what kind of expressive power we need, take a closer look at what a
 typical state contains.</p>

 <p><see topic='@(url |A Typical State|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |Name the Formula Above|
  :parents (|Pages Written Especially for the Tours|)
  :short "Name the Formula Above"
  :long "<p>When the theorem prover explicitly assigns a name, like @('*1'), to
 a formula, it has decided to prove the formula by induction.</p>")

(defxdoc |Nontautological Subgoals|
  :parents (|Pages Written Especially for the Tours|)
  :short "Prover output omits some details"
  :long "<p>The theorem prover's proof output is intended to suggest an outline
 of the reasoning process employed by its proof engine, which is virtually
 always more than is necessary for the ACL2 user.  In particular, the output
 often omits subgoals that are sufficiently trivial, including
 tautologies.</p>")

(defxdoc |Numbers in ACL2|
  :parents (|Pages Written Especially for the Tours|)
  :short "Numbers in ACL2"
  :long "<p>ACL2 numbers are precisely represented and unbounded.  They can be
 partitioned into the following subtypes:</p>

 @({
  ACL2 Numbers
   |
   |- Rationals
   |  |
   |  |- Integers
   |  |  |- Positive integers                 3
   |  |  |- Zero                              0
   |  |  |- Negative Integers                 -3
   |  |
   |  |- Non-Integral Rationals
   |  |  |
   |  |  |- Positive Non-Integral Rationals   19/3
   |  |  |- Negative Non-Integral Rationals   -22/7
   |
   |- Complex Rational Numbers                 #c(3 5/2) ; i.e., 3 + (5/2)i
 })

 <p>Signed integer constants are usually written (as illustrated above) as
 sequences of decimal digits, possibly preceded by @('+') or @('-').  Decimal
 points are not allowed.  Integers may be written in binary, as in @('#b1011')
 (= 23) and @('#b-111') (= -7).  Octal may also be used, @('#o-777') = -511.
 Non-integral rationals are written as a signed decimal integer and an unsigned
 decimal integer, separated by a slash.  Complex rationals are written as
 #c(rpart ipart) where rpart and ipart are rationals.</p>

 <p>Of course, 4/2 = 2/1 = 2 (i.e., not every rational written with a slash is
 a non-integer).  Similarly, #c(4/2 0) = #c(2 0) = 2.</p>

 <p>The common arithmetic functions and relations are denoted by @('+'),
 @('-'), @('*'), @('/'), @('='), @('<'), @('<='), @('>') and @('>=').  However
 there are many others, e.g., @('floor'), @('ceiling'), and @('lognot').  We
 suggest you see @(see programming) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 where we list all of the primitive ACL2 functions.  Alternatively, see any
 Common Lisp language documentation.</p>

 <p>The primitive predicates for recognizing numbers are illustrated below.
 The following ACL2 function will classify an object, x, according to its
 numeric subtype, or else return 'NaN (not a number).  We show it this way just
 to illustrate programming in ACL2.</p>

 @({
  (defun classify-number (x)
    (cond ((rationalp x)
           (cond ((integerp x)
                  (cond ((< 0 x) 'positive-integer)
                        ((= 0 x) 'zero)
                        (t 'negative-integer)))
                 ((< 0 x) 'positive-non-integral-rational)
                 (t 'negative-non-integral-rational)))
          ((complex-rationalp x) 'complex-rational)
          (t 'NaN)))
 })")

(defxdoc |On the Naming of Subgoals|
  :parents (|Pages Written Especially for the Tours|)
  :short "On the Naming of Subgoals"
  :long "<p>@('Subgoal *1/2') is the <b>induction step</b> from the scheme,
 obtained by instantiating the scheme with our conjecture.</p>

 <p>We number the cases ``backward'', so this is case ``2'' of the proof of
 ``*1''.  We number them backward so you can look at a subgoal number and get
 an estimate for how close you are to the end.</p>")

(defxdoc |Other Requirements|
  :parents (|Pages Written Especially for the Tours|)
  :short "Other Requirements"
  :long "<p><see topic='@(url |The End of the Flying Tour|)'><img
 src='flying.gif'></img></see></p>

 <p>ACL2 is distributed on the Web without fee.</p>

 <p>There is a <b>license</b> agreement based on the 3-clause BSD license.  See
 the file LICENSE in the ACL2 distribution.</p>

 <p>ACL2 currently runs on <b>Unix</b>, <b>Linux</b>, <b>Windows</b>, and
 <b>Macintosh OS X</b> operating systems.</p>

 <p>It can be built in any of the following Common Lisps:</p>

 <code>
   * <b>Allegro Common Lisp</b>,
   * <b>CCL</b> (formerly OpenMCL)
   * <b>CLISP</b>,
   * <b>CMU Common Lisp</b>,
   * <b>GCL</b> (Gnu Common Lisp),
   * <b>LispWorks</b>, and
   * <b>SBCL</b> (Steel Bank Common Lisp)
 </code>

 <p><see topic='@(url |The End of the Flying Tour|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |Overview of the Expansion of ENDP in the Base Case|
  :parents (|Pages Written Especially for the Tours|)
  :short "Overview of the Expansion of ENDP in the Base Case"
  :long "<p>@('Subgoal *1/1') is the <b>Base Case</b> of our induction.  It
 simplifies to @('Subgoal *1/1'') by expanding the <b>ENDP</b> term in the
 hypothesis, just as we saw in the earlier proof of @('Subgoal *1/2').</p>")

(defxdoc |Overview of the Expansion of ENDP in the Induction Step|
  :parents (|Pages Written Especially for the Tours|)
  :short "Overview of the Expansion of ENDP in the Induction Step"
  :long "<p>In this message the system is saying that @('Subgoal *1/2') has
 been rewritten to the @('Subgoal *1/2''), by expanding the definition of
 <b>endp</b>.  This is an example of <b>simplification</b>, one of the main
 proof techniques used by the theorem prover.</p>

 <p>Click <see topic='@(url
 |The Expansion of ENDP in the Induction Step (Step 0)|)'>here</see> if you
 would like to step through the simplification of @('Subgoal *1/2').</p>")

(defxdoc |Overview of the Final Simplification in the Base Case|
  :parents (|Pages Written Especially for the Tours|)
  :short "Overview of the Final Simplification in the Base Case"
  :long "<p>The <b>But</b> is our signal that the goal is proved.</p>

 <p>Click <see topic='@(url
 |The Final Simplification in the Base Case (Step 0)|)'>here</see> to step
 through the proof.  It is very simple.</p>")

(defxdoc |Overview of the Proof of a Trivial Consequence|
  :parents (|Pages Written Especially for the Tours|)
  :short "Overview of the Proof of a Trivial Consequence"
  :long "<p><see topic='@(url |The End of the Walking Tour|)'><img
 src='walking.gif'></img></see></p>

 <p><img src='green-line.gif'></img></p>

 <code>
 ACL2 !&gt;<b>(defthm trivial-consequence</b>
          <b>(equal (app (app (app (app x1 x2) (app x3 x4)) (app x5 x6)) x7)</b>
                 <b>(app x1 (app (app x2 x3) (app (app x4 x5) (app x6 x7))))))</b>

 <see topic='@(url |The WARNING about the Trivial Consequence|)'>ACL2 Warning</see> [Subsume] in ( DEFTHM TRIVIAL-CONSEQUENCE ...):  The previously
 added rule ASSOCIATIVITY-OF-APP subsumes the newly proposed :REWRITE
 rule TRIVIAL-CONSEQUENCE, in the sense that the old rule rewrites a
 more general target.  Because the new rule will be tried first, it
 may nonetheless find application.

 By the simple :rewrite rule <see topic='@(url |The First Application of the Associativity Rule|)'>ASSOCIATIVITY-OF-APP</see> we reduce the conjecture
 to

 Goal'
 (EQUAL (APP X1
             (APP X2
                  (APP X3 (APP X4 (APP X5 (APP X6 X7))))))
        (APP X1
             (APP X2
                  (APP X3 (APP X4 (APP X5 (APP X6 X7))))))).

 But we reduce the conjecture to T, by primitive type reasoning.

 Q.E.D.

 Summary
 Form:  ( DEFTHM TRIVIAL-CONSEQUENCE ...)
 Rules: ((:REWRITE ASSOCIATIVITY-OF-APP)
         (:FAKE-RUNE-FOR-TYPE-SET NIL))
 Warnings:  <see topic='@(url |The Summary of the Proof of the Trivial Consequence|)'>Subsume</see>
 Time:  0.20 seconds (prove: 0.02, print: 0.00, other: 0.18)
  TRIVIAL-CONSEQUENCE
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>You might explore the links before moving on.</p>

 <p><see topic='@(url |The End of the Walking Tour|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |Overview of the Simplification of the Base Case to T|
  :parents (|Pages Written Especially for the Tours|)
  :short "Overview of the Simplification of the Base Case to T"
  :long "<p><see topic='@(url
 |The End of the Proof of the Associativity of App|)'><img
 src='walking.gif'></img></see></p>

 <code>
 <see topic='@(url |Overview of the Expansion of ENDP in the Base Case|)'>Subgoal *1/1</see>
 (IMPLIES (ENDP A)
          (EQUAL (APP (APP A B) C)
                 (APP A (APP B C)))).

 By the simple :definition ENDP we reduce the conjecture to

 Subgoal *1/1'
 (IMPLIES (NOT (CONSP A))
          (EQUAL (APP (APP A B) C)
                 (APP A (APP B C)))).

 <see topic='@(url |Overview of the Final Simplification in the Base Case|)'>But</see> simplification reduces this to T, using the :definition APP and
 primitive type reasoning.

 </code>

 <p><see topic='@(url |The End of the Proof of the Associativity of App|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |Overview of the Simplification of the Induction Conclusion|
  :parents (|Pages Written Especially for the Tours|)
  :short "Overview of the Simplification of the Induction Conclusion"
  :long "<p>In this message the system is saying that @('Subgoal *1/2'') has
 been rewritten to T using the rules noted.  The word ``<b>But</b>'' at the
 beginning of the sentence is a signal that the goal has been proved.</p>

 <p>Click <see topic='@(url
 |The Simplification of the Induction Conclusion (Step 0)|)'>here</see> to step
 through the proof of @('Subgoal *1/2'').</p>")

(defxdoc |Overview of the Simplification of the Induction Step to T|
  :parents (|Pages Written Especially for the Tours|)
  :short "Overview of the Simplification of the Induction Step to T"
  :long "<p><see topic='@(url
 |Overview of the Simplification of the Base Case to T|)'><img
 src='walking.gif'></img></see></p>

 <code>
 <see topic='@(url |On the Naming of Subgoals|)'>Subgoal *1/2</see>
 (IMPLIES (AND (NOT (ENDP A))
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL (APP (APP A B) C)
                 (APP A (APP B C)))).

 By the simple :definition <see topic='@(url |Overview of the Expansion of ENDP in the Induction Step|)'>ENDP</see> we reduce the conjecture to

 Subgoal *1/2'
 (IMPLIES (AND (CONSP A)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL (APP (APP A B) C)
                 (APP A (APP B C)))).

 <see topic='@(url |Overview of the Simplification of the Induction Conclusion|)'>But</see> simplification reduces this to T, using the :definition APP, the
 :rewrite rules CDR-CONS and CAR-CONS and primitive type reasoning.
 </code>

 <p><see topic='@(url
 |Overview of the Simplification of the Base Case to T|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |Perhaps|
  :parents (|Pages Written Especially for the Tours|)
  :short "Perhaps"
  :long "<p>The theorem prover's proof is printed in real time.  At the time it
 prints ``Perhaps'' it does not know the proof will succeed.</p>")

(defxdoc |Popping out of an Inductive Proof|
  :parents (|Pages Written Especially for the Tours|)
  :short "Popping out of an Inductive Proof"
  :long "<p>Recall that our induction scheme (click <see topic='@(url
 |The Proof of the Associativity of App|)'>here</see> to revisit it) had two
 cases, the induction step (@('Subgoal *1/2')) and the base case (@('Subgoal
 *1/1')).  Both have been proved!</p>")

(defxdoc |Proving Theorems about Models|
  :parents (|Pages Written Especially for the Tours|)
  :short "Proving Theorems about Models"
  :long "<p><see topic='@(url |What is Required of the User(Q)|)'><img
 src='flying.gif'></img></see></p>

 <p>But ACL2 is a <b>logic</b>.  We can <b>prove theorems about the
 model</b>.</p>

 <p><img src='computing-machine-xxy.gif'></img></p>

 <code>
 <b>Theorem.  MC 'mult is a multiplier</b>
 (implies (and (natp x)
               (natp y))
          (equal (lookup 'z (mc (s 'mult x y) (mclk x)))
                 (* x y))).
 </code>

 <p>This theorem says that a certain program running on the <b>mc</b> machine
 will correctly multiply <b>any two natural numbers</b>.</p>

 <p>It is a statement about an <b>infinite</b> number of test cases!</p>

 <p>We know it is true about the model because we <b>proved</b> it.</p>

 <p>Of course, models of actual machines usually only accept a finite number of
 different inputs.  For example, engineers at Advanced Micro Devices (AMD),
 Centaur, and IBM have ACL2 models of floating point units that operate on
 double precision IEEE floating point numbers.  These are finite models.  But
 the size of their inputs is sufficiently large that they are verified by the
 same mathematical methods used to prove theorems about infinite state systems
 like our little @('mc').</p>

 <p><see topic='@(url |What is Required of the User(Q)|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |Revisiting the Admission of App|
  :parents (|Pages Written Especially for the Tours|)
  :short "Revisiting the Admission of App"
  :long "<p><see topic='@(url |Evaluating App on Sample Input|)'><img
 src='walking.gif'></img></see></p>

 <p>Here is the definition of @('app') again with certain parts highlighted.
 If you are taking the Walking Tour, please read the text carefully and click
 on each of the links below, <b>except those marked</b> <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>.
 Then come <b>back</b> here.</p>

 <p><img src='green-line.gif'></img></p>

 <code>
 <see topic='@(url |About the Prompt|)'>ACL2 !&gt;</see><b>(defun app (x y)</b>
   <b>(cond ((endp x) y)</b>
         <b>(t (cons (car x) </b>
                  <b>(app (cdr x) y)))))</b>

 The <see topic='@(url |About the Admission of Recursive Definitions|)'>admission</see> of APP is trivial, using the
 relation @(see O<) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see> (which is known to be well-founded on
 the domain recognized by @(see O-P) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>) and the measure
 (@(see ACL2-COUNT) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see> X).  We <see topic='@(url |Guessing the Type of a Newly Admitted Function|)'>observe</see> that the
 <see topic='@(url |About Types|)'>type</see> of APP is described by the theorem (OR
 (CONSP (APP X Y)) (EQUAL (APP X Y) Y)).  We used primitive type
 reasoning.

 <see topic='@(url |The Event Summary|)'>Summary</see>
 Form:  ( DEFUN APP ...)
 Rules: ((:FAKE-RUNE-FOR-TYPE-SET NIL))
 Warnings:  None
 Time:  0.03 seconds (prove: 0.00, print: 0.00, other: 0.03)
  APP
 </code>

 <p><img src='green-line.gif'></img></p>

 <p><see topic='@(url |Evaluating App on Sample Input|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |Rewrite Rules are Generated from DEFTHM Events|
  :parents (|Pages Written Especially for the Tours|)
  :short "Rewrite Rules are Generated from DEFTHM Events"
  :long "<p><see topic='@(url
 |You Must Think about the Use of a Formula as a Rule|)'><img
 src='walking.gif'></img></see></p>

 <p>By reading the documentation of @(tsee defthm) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 (and especially of its :@(see rule-classes) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 argument) you would learn that when we submitted the command</p>

 <code>
 <b>(defthm associativity-of-app</b>
   <b>(equal (app (app a b) c)</b>
          <b>(app a (app b c))))</b>

 </code>

 <p>we not only command the system to prove that @('app') is an associative
 function but</p>

 <code>
   * <b>we commanded it to use that fact as a rewrite rule</b>.
 </code>

 <p>That means that every time the system encounters a term of the form</p>

 <code>
 (app (app <b>x</b> <b>y</b>) <b>z</b>)
 </code>

 <p>it will replace it with</p>

 <code>
 (app <b>x</b> (app <b>y</b> <b>z</b>))!
 </code>

 <p><see topic='@(url
 |You Must Think about the Use of a Formula as a Rule|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |Running Models|
  :parents (|Pages Written Especially for the Tours|)
  :short "Running Models"
  :long "<p><see topic='@(url |Symbolic Execution of Models|)'><img
 src='flying.gif'></img></see></p>

 <p>Suppose the machine being modeled is some kind of arithmetic unit.  Suppose
 the model can be initialized so as to <b>multiply</b> <b>x</b> times <b>y</b>
 and leave the answer in <b>z</b>.  Then if we initialize <b>s</b> to
 <b>multiply</b> with <b>x=5</b> and <b>y=7</b> and run the machine long
 enough, we can read the answer <b>35</b> in the final state.

  <img src='computing-machine-5x7.gif'></img></p>

 <p>Because ACL2 is a programming language, our model can be <b>run</b> or
 <b>executed</b>.</p>

 <p>If you defined the model in ACL2 and then typed</p>

 @({
  (lookup 'z (mc (s 'mult 5 7) 29))
 })

 <p>then ACL2 would compute 35.  (Here we assume that the function @('s')
 creates a state ready to run a given application on given inputs @('x') and
 @('y').)  You can <b>emulate</b> or <b>test</b> the model of your machine.</p>

 <p>This is <b>obvious</b> because ACL2 is Common Lisp; and Common Lisp is a
 <b>programming language</b>.</p>

 <p><see topic='@(url |Symbolic Execution of Models|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |Subsumption of Induction Candidates in App Example|
  :parents (|Pages Written Especially for the Tours|)
  :short "Subsumption of Induction Candidates in App Example"
  :long "<p>After collecting induction suggestions from these three terms</p>

 <code>
 (app <b>a</b> b)

 (app <b>b</b> c)

 (app <b>a</b> (app b c))
 </code>

 <p>the system notices that the first and last suggest the same decomposition
 of @('a'): case split on whether @('a') is empty (i.e., @('(endp a)')), and in
 the case where it is not empty, recursively process @('(cdr a)').  So we are
 left with two ideas about how to induct:</p>

 <p>Decompose <b>a</b> as we would to unwind (app <b>a</b> b).</p>

 <p>Decompose <b>b</b> as we would to unwind (app <b>b</b> c).</p>")

(defxdoc |Suggested Inductions in the Associativity of App Example|
  :parents (|Pages Written Especially for the Tours|)
  :short "Suggested Inductions in the Associativity of App Example"
  :long "<p>To find a plausible induction argument, the system studies the
 recursions exhibited by the terms in the conjecture.</p>

 <p>Roughly speaking, a call of a recursive function ``suggests'' an induction
 if the argument position decomposed in recursion is occupied by a
 variable.</p>

 <p>In this conjecture, three terms suggest inductions:</p>

 <code>
 (app <b>a</b> b)

 (app <b>b</b> c)

 (app <b>a</b> (app b c))
 </code>

 <p>The variable recursively decomposed is indicated in <b>bold</b>.</p>")

(defxdoc |Symbolic Execution of Models|
  :parents (|Pages Written Especially for the Tours|)
  :short "Symbolic Execution of Models"
  :long "<p><see topic='@(url |Proving Theorems about Models|)'><img
 src='flying.gif'></img></see></p>

 <p>But ACL2 is more than a programming language.</p>

 <p>Initialize <b>x</b> to 5 and let <b>y</b> be <b>any legal value</b>.</p>

 <p><img src='computing-machine-5xy.gif'></img></p>

 <p>Because ACL2 is a mathematical language, we can simplify the expression</p>

 @({
  (lookup 'z (mc (s 'mult 5 y) 29))
 })

 <p>and get (+ y y y y y).  This is <b>symbolic execution</b> because not all
 of the parameters are known.</p>

 <p><see topic='@(url |Proving Theorems about Models|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |The Admission of App|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Admission of App"
  :long "<p><see topic='@(url |Revisiting the Admission of App|)'><img
 src='walking.gif'></img></see></p>

 <p>Here is what it looks like to submit the definition of @('app') to
 ACL2:</p>

 <p><img src='green-line.gif'></img></p>

 <code>
 ACL2 !&gt;<b>(defun app (x y)</b>
   <b>(cond ((endp x) y)</b>
         <b>(t (cons (car x) </b>
                  <b>(app (cdr x) y)))))</b>

 The admission of APP is trivial, using the relation O&lt; (which
 is known to be well-founded on the domain recognized by O-P)
 and the measure (ACL2-COUNT X).  We observe that the type of APP is
 described by the theorem (OR (CONSP (APP X Y)) (EQUAL (APP X Y) Y)).
 We used primitive type reasoning.

 Summary
 Form:  ( DEFUN APP ...)
 Rules: ((:FAKE-RUNE-FOR-TYPE-SET NIL))
 Warnings:  None
 Time:  0.03 seconds (prove: 0.00, print: 0.00, other: 0.03)
  APP
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>The text between the lines above is one interaction with the ACL2 command
 loop.  Interacting with the latest version of ACL2 may not produce the very
 same output, but we trust you'll recognize the basics.</p>

 <p>Above you see the user's <b>input</b> and how the system responds.  This
 little example shows you what the syntax looks like and is a very typical
 <b>successful</b> interaction with the definitional principle.</p>

 <p>Let's look at it a little more closely.</p>

 <p><see topic='@(url |Revisiting the Admission of App|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |The Associativity of App|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Associativity of App"
  :long "<p><see topic='@(url |The Theorem that App is Associative|)'><img
 src='walking.gif'></img></see></p>

 <p><img src='green-line.gif'></img></p>

 <code>
 ACL2!&gt;<b>(let ((a '(1 2))</b>
             <b>(b '(3 4))</b>
             <b>(c '(5 6)))</b>
         <b>(equal (app (app a b) c)</b>
                <b>(app a (app b c))))</b>
 T
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Observe that, for the particular @('a'), @('b'), and @('c') above, @('(app
 (app a b) c)') returns the same thing as @('(app a (app b c))').  Perhaps
 @('app') is <b>associative</b>.  Of course, to be associative means that the
 above property must hold for all values of @('a'), @('b'), and @('c'), not
 just the ones <b>tested</b> above.</p>

 <p>Wouldn't it be cool if you could type</p>

 <code>
 ACL2!&gt;<b>(equal (app (app a b) c)</b>
              <b>(app a (app b c)))</b>

 </code>

 <p>and have ACL2 compute the value @('T')?  Well, <b>you can't!</b> If you try
 it, you'll get an error message!  The message says we can't evaluate that form
 because it contains <b>free</b> variables, i.e., variables not given values.
 Click <see topic='@(url |Free Variables in Top-Level Input|)'>here</see> to
 see the message.</p>

 <p>We cannot evaluate a form on an infinite number of cases.  But we can prove
 that a form is a theorem and hence know that it will always evaluate to
 true.</p>

 <p><see topic='@(url |The Theorem that App is Associative|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |The Base Case in the App Example|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Base Case in the App Example"
  :long "<p>This formula is the <b>Base Case</b>.  It consists of two parts, a
 test identifying the non-inductive case and the conjecture to prove.</p>

 <code>
 (IMPLIES (ENDP A)                 <b>; Test</b>
          (:P A B C))              <b>; Conjecture</b>
 </code>

 <p>When we prove this we can assume</p>

 <code> * @('A') is empty </code>

 <p>and we have to prove the conjecture for @('A').</p>")

(defxdoc |The End of the Flying Tour|
  :parents (|Pages Written Especially for the Tours|)
  :short "The End of the Flying Tour"
  :long "<p><img src='landing.gif'></img></p>

 <p>This completes the Flying Tour.</p>

 <p>We recommend that you now take <see topic='@(url
 |A Walking Tour of ACL2|)'>A Walking Tour of ACL2</see>.</p>

 <p>Thanks.<br></br>

 Matt Kaufmann and J Moore</p>

 <p><see topic='@(url |A Walking Tour of ACL2|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |The End of the Proof of the Associativity of App|
  :parents (|Pages Written Especially for the Tours|)
  :short "The End of the Proof of the Associativity of App"
  :long "<p><see topic='@(url |Guiding the ACL2 Theorem Prover|)'><img
 src='walking.gif'></img></see></p>

 <code>
 That <see topic='@(url |Popping out of an Inductive Proof|)'>completes</see> the proof of *1.

 <see topic='@(url |The Q.E.D. Message|)'>Q.E.D.</see>

 Summary
 Form:  ( DEFTHM ASSOCIATIVITY-OF-APP ...)
 <see topic='@(url |The Rules used in the Associativity of App Proof|)'>Rules</see>: ((:REWRITE CDR-CONS)
         (:REWRITE CAR-CONS)
         (:DEFINITION NOT)
         (:DEFINITION ENDP)
         (:FAKE-RUNE-FOR-TYPE-SET NIL)
         (:DEFINITION APP))
 Warnings:  None
 Time:  0.27 seconds (prove: <see topic='@(url |The Time Taken to do the Associativity of App Proof|)'>0.10</see>, print: 0.05, other: 0.12)
  ASSOCIATIVITY-OF-APP
 </code>

 <p><img src='green-line.gif'></img></p>

 <p><see topic='@(url |Guiding the ACL2 Theorem Prover|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |The End of the Walking Tour|
  :parents (|Pages Written Especially for the Tours|)
  :short "The End of the Walking Tour"
  :long "<p><img src='sitting.gif'></img></p>

 <p>This completes the Walking Tour.</p>

 <p>We intend to document many other parts of the system this way, but we just
 haven't gotten around to it.</p>

 <p>To start the two tours over again from the beginning, click on the icons
 below.  If you are really interested in learning how to use ACL2, we recommend
 that you repeat each tour at least once more to explore branches of the tour
 that you might have missed.</p>

 <p>If you want to learn how to use the theorem prover, we now recommend that
 you devote the time necessary to work your way through the extended
 introduction to how to use the prover.</p>

 <p>See @(see introduction-to-the-theorem-prover).</p>

 <p>This will explain how to interact with ACL2 and has some sample problems
 for you to solve including some challenge proofs to make ACL2 find.</p>

 <p>We hope you enjoy ACL2.  We do.</p>

 <p>Matt Kaufmann and J Strother Moore</p>

 <p><see topic='@(url |A Flying Tour of ACL2|)'><img
 src='flying.gif'></img></see> <see topic='@(url
 |A Walking Tour of ACL2|)'><img src='walking.gif'></img></see></p>")

(defxdoc |The Event Summary|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Event Summary"
  :long "<p>At the conclusion of most events (click <see
 topic='@(url |About the Prompt|)'>here</see> for a brief discussion of events or
 see @(see events) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>), ACL2 prints a summary.  The summary for @('app')
 is:</p>

 @({
  Summary
  Form:  ( DEFUN APP ...)
  Rules: ((:FAKE-RUNE-FOR-TYPE-SET NIL))
  Warnings:  None
  Time:  0.03 seconds (prove: 0.00, print: 0.00, other: 0.03)
   APP
 })

 <p>The ``rules'' listed are those used in function admission or proof
 summarized.  What is actually listed are ``runes'' (see @(see rune)) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>)
 which are list-structured names for rules in the ACL2 database or ``@(see
 world)'' <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see>.  Using @(see theories) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see> you
 can ``enable'' and ``disable'' rules so as to make them available (or not) to
 the ACL2 theorem prover.</p>

 <p>The ``warnings'' mentioned (none are listed for @('app')) remind the reader
 whether the event provoked any warnings.  The warnings themselves would have
 been printed earlier in the processing and this part of the summary just names
 the earlier warnings printed.</p>

 <p>The ``time'' indicates how much processing time was used and is divided
 into three parts: the time devoted to proof, to printing, and to syntactic
 checks, pre-processing and database updates.  Despite the fact that ACL2 is an
 applicative language it is possible to measure time with ACL2 programs.  The
 @(tsee state) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> contains a clock.  The times are printed in decimal
 notation but are actually counted in integral units.  Note that by default,
 each time is a runtime, also known as a cpu time, as opposed to being a real
 time, also known as a wall clock time.</p>

 <p>The final @('APP') is the value of the @('defun') command and was printed
 by the read-eval-print loop.  The fact that it is indented one space is a
 subtle reminder that the command actually returned an ``error triple'',
 consisting of a flag indicating (in this case) that no error occurred, a value
 (in this case the symbol @('APP')), and the final @(tsee state) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>).
 See @(see ld-post-eval-print) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see> for
 some details.  If you really want to follow that link, however, you might see
 @(see ld) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> first.</p>

 <p>You should now return to <see topic='@(url
 |Revisiting the Admission of App|)'>the Walking Tour</see>.</p>")

(defxdoc |The Expansion of ENDP in the Induction Step (Step 0)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Expansion of ENDP in the Induction Step (Step 0)"
  :long "<code>
 Subgoal *1/2
 (IMPLIES (AND (NOT <see topic='@(url |The Expansion of ENDP in the Induction Step (Step 1)|)'>(</see>ENDP A))
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL (APP (APP A B) C)
                 (APP A (APP B C)))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above (the open parenthesis before @('ENDP')) to replace
 @('(ENDP A)') by its definition.</p>")

(defxdoc |The Expansion of ENDP in the Induction Step (Step 1)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Expansion of ENDP in the Induction Step (Step 1)"
  :long "<code>
 Subgoal *1/2
 (IMPLIES (AND <see topic='@(url |The Expansion of ENDP in the Induction Step (Step 2)|)'>(</see>NOT <b>(NOT (CONSP A))</b>)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL (APP (APP A B) C)
                 (APP A (APP B C)))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>The <b>bold</b> text is the instantiated definition of @('ENDP').</p>

 <p>Now click on the link above to simplify (NOT (NOT (CONSP A)))</p>")

(defxdoc |The Expansion of ENDP in the Induction Step (Step 2)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Expansion of ENDP in the Induction Step (Step 2)"
  :long "<code>
 Subgoal *1/2'
 (IMPLIES (AND <b>(CONSP A)</b>
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL (APP (APP A B) C)
                 (APP A (APP B C)))).

 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Note that this is @('Subgoal *1/2'.')</p>

 <p>You may click <see topic='@(url
 |Overview of the Simplification of the Induction Step to T|)'>here</see> to
 return to the main proof.</p>")

(defxdoc |The Falling Body Model|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Falling Body Model"
  :long "<p><img src='pisa.gif'></img></p>

 <p>One particularly famous and very simple model is the equation of a falling
 body: the distance d an object falls is proportional to the square of the time
 t.  If the time is measured in seconds and the distance in feet, the equation
 relating these two is</p>

 @({
         2
  d = 16t
 })

 <p>This equation is a <b>model</b> of falling objects.  It can be used to
 predict how long it takes a cannonball to fall from the top of a 200 foot
 tower (3.5 seconds).  This might be important if your product is designed to
 drop cannonballs on moving targets.</p>")

(defxdoc |The Final Simplification in the Base Case (Step 0)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Final Simplification in the Base Case (Step 0)"
  :long "<code>
 Subgoal *1/1'
 (IMPLIES (NOT (CONSP A))
          (EQUAL (APP <see topic='@(url |The Final Simplification in the Base Case (Step 1)|)'>(</see>APP A B) C)
                 (APP A (APP B C)))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to replace @('(APP A B)') by its definition.  Note
 that the hypothesis @('(NOT (CONSP A))') allows us to simplify the @('IF') in
 @('APP') to its <b>false branch</b> this time.</p>")

(defxdoc |The Final Simplification in the Base Case (Step 1)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Final Simplification in the Base Case (Step 1)"
  :long "<code>
 Subgoal *1/1'
 (IMPLIES (NOT (CONSP A))
          (EQUAL (APP <b>B</b> C)
                 <see topic='@(url |The Final Simplification in the Base Case (Step 2)|)' use-tsee='yes'>(</see>APP A (APP B C)))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to expand the definition of @('APP').  Again, we
 come out through the false branch because of the hypothesis.</p>")

(defxdoc |The Final Simplification in the Base Case (Step 2)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Final Simplification in the Base Case (Step 2)"
  :long "<code>
 Subgoal *1/1'
 (IMPLIES (NOT (CONSP A))
          <see topic='@(url |The Final Simplification in the Base Case (Step 3)|)'>(</see>EQUAL (APP B C)
                 <b>(APP B C)</b>)).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to use the Axiom @('(EQUAL x x) = t')</p>")

(defxdoc |The Final Simplification in the Base Case (Step 3)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Final Simplification in the Base Case (Step 3)"
  :long "<code>
 Subgoal *1/1'
 (IMPLIES (NOT (CONSP A))
          <b>T</b>)
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Now that its conclusion is identically @('T') the @('IMPLIES') will
 simplify to @('T') (not shown) and we are done with @('Subgoal *1/1'').</p>

 <p>You may click <see topic='@(url
 |Overview of the Simplification of the Base Case to T|)'>here</see> to return
 to the main proof.</p>")

(defxdoc |The First Application of the Associativity Rule|
  :parents (|Pages Written Especially for the Tours|)
  :short "The First Application of the Associativity Rule"
  :long "<p>So here we see our associativity rule being used!</p>

 <p>The rewriter sweeps the conjecture in a <b>leftmost innermost</b> fashion,
 applying rewrite rules as it goes.</p>

 <p>The associativity rule is used many times in this sweep.  The first
 ``target'' is highlighted below.  Click on it to see what happens:</p>

 <code>
 <b>Current Conjecture</b>:
 (equal (app (app <see topic='@(url |A Sketch of How the Rewriter Works|)'>(app (app x1 x2) (app x3 x4))</see> (app x5 x6)) x7)
        (app x1 (app (app x2 x3) (app (app x4 x5) (app x6 x7)))))
 </code>")

(defxdoc |The Induction Scheme Selected for the App Example|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Induction Scheme Selected for the App Example"
  :long "@({
  (AND
     (IMPLIES (AND (NOT (ENDP A))         ; Induction Step: test
                   (:P (CDR A) B C))      ;  and induction hypothesis
              (:P A B C))                 ;  implies induction conclusion.
     (IMPLIES (ENDP A) (:P A B C)))       ; Base Case
 })

 <p>The formula beginning with this parenthesis is the induction scheme
 suggested by @('(APP A B)') applied to @('(P A B C)').</p>

 <p>It is a <b>conjunction</b> (@(tsee AND) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>) of
 two formulas.</p>

 <p>The first is the <b>induction step</b> and the second is the <b>base
 case</b>.</p>")

(defxdoc |The Induction Step in the App Example|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Induction Step in the App Example"
  :long "<p>This formula is the <b>Induction Step</b>.  It basically consists
 of three parts, a test identifying the inductive case, an induction hypothesis
 and an induction conclusion.</p>

 <code>
 (IMPLIES (AND (NOT (ENDP A))      <b>; Test</b>
               (:P (CDR A) B C))   <b>; Induction Hypothesis</b>
          (:P A B C))              <b>; Induction Conclusion</b>
 </code>

 <p>When we prove this we can assume</p>

 <code> * @('A') is not empty, and that

   * the associativity conjecture holds for a ``smaller'' version of @('A'),
     namely, @('(CDR A)').

 </code>

 <p>Under those hypotheses we have to prove the associativity conjecture for
 @('A') itself.</p>")

(defxdoc |The Instantiation of the Induction Scheme|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Instantiation of the Induction Scheme"
  :long "<p>The induction scheme just shown is just an abbreviation for our
 real goal.</p>

 <p>To obtain our actual goals we have to replace the schema @(':P') by the
 associativity conjecture (instantiated as shown in the scheme).</p>

 <p>This produces two actual goals, the induction step and the base case.</p>")

(defxdoc |The Justification of the Induction Scheme|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Justification of the Induction Scheme"
  :long "<p>This paragraph explains why the induction selected is legal.  The
 explanation is basically the same as the explanation for why the recursion in
 @('(APP A B)') terminates.</p>")

(defxdoc |The Proof of the Associativity of App|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Proof of the Associativity of App"
  :long "<p><see topic='@(url
 |Overview of the Simplification of the Induction Step to T|)'><img
 src='walking.gif'></img></see></p>

 <p>Here is the theorem prover's output when it processes the <b>defthm</b>
 command for the associativity of @('app').  We have highlighted text for which
 we offer some explanation, and broken the presentation into several pages.
 (The most recent version of ACL2 may print slightly different output but the
 basics are the same.)  Just follow the Walking Tour after exploring the
 explanations.</p>

 <p>However, before exploring this output you should understand that ACL2 users
 rarely read successful proofs!  Instead, they look at certain subgoals printed
 in failed proofs, figure whether and how those subgoals can be proved, and
 give ACL2 directions for proving them, usually by simply proving other lemmas.
 Furthermore, to be a good user of ACL2 you do not have to understand how the
 theorem prover works.  You just have to understand how to interact with it.
 We explain this in great detail later.  But basically all new users are
 curious to know how ACL2 works and this little tour attempts to give some
 answers, just to satisfy your curiosity.</p>

 <p><img src='green-line.gif'></img></p>

 <code>
 ACL2!&gt;<b>(defthm associativity-of-app</b>
         <b>(equal (app (app a b) c)</b>
                <b>(app a (app b c))))</b>

 Name the formula above <see topic='@(url |Name the Formula Above|)'>*1</see>.

 <see topic='@(url |Perhaps|)'>Perhaps</see> we can prove *1 by induction.  Three induction schemes are
 <see topic='@(url |Suggested Inductions in the Associativity of App Example|)'>suggested</see> by this conjecture.  <see topic='@(url |Subsumption of Induction Candidates in App Example|)'>Subsumption</see> reduces that number to two.
 However, one of these is <see topic='@(url |Flawed Induction Candidates in App Example|)'>flawed</see> and so we are left with one viable
 candidate.

 We will induct according to a scheme suggested by (APP A B).  If we
 let  (:P A B C) denote *1 above then the induction scheme we'll use
 is
 <see topic='@(url |The Induction Scheme Selected for the App Example|)'>(</see>AND
    <see topic='@(url |The Induction Step in the App Example|)'>(</see>IMPLIES (AND (NOT (ENDP A))
                  (:P (CDR A) B C))
             (:P A B C))
    <see topic='@(url |The Base Case in the App Example|)'>(</see>IMPLIES (ENDP A) (:P A B C))).
 This induction is <see topic='@(url |The Justification of the Induction Scheme|)'>justified</see> by the same argument used to admit APP,
 namely, the measure (ACL2-COUNT A) is decreasing according to the relation
 O&lt; (which is known to be well-founded on the domain recognized
 by O-P).  When <see topic='@(url |The Instantiation of the Induction Scheme|)'>applied</see> to the goal at hand the above induction
 scheme produces the following two <see topic='@(url |Nontautological Subgoals|)'>nontautological subgoals</see>.

 </code>

 <p><see topic='@(url
 |Overview of the Simplification of the Induction Step to T|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |The Q.E.D. Message|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Q.E.D. Message"
  :long "<p><b>Q.E.D.</b> stands for ``quod erat demonstrandum'' which is Latin
 for ``which was to be demonstrated'' and is the signal that a proof is
 completely done.</p>")

(defxdoc |The Rules used in the Associativity of App Proof|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Rules used in the Associativity of App Proof"
  :long "<p>Note that under <b>Rules</b> we list the <see topic='@(url
 RUNE)'>runes</see> <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> of all the rules used in the proof.  This list says
 that we used the rewrite rules @('CAR-CONS') and @('CDR-CONS'), the
 definitions of the functions @('NOT'), @('ENDP') and @('APP'), and primitive
 type reasoning (which is how we simplified the @('IF') and @('EQUAL')
 terms).</p>

 <p>For what it is worth, @('IMPLIES') and @('AND') are actually <see
 topic='@(url DEFMACRO)'>macros</see> <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 that are expanded into @('IF') expressions before the proof ever begins.  The
 use of macros is not reported among the rules.</p>")

(defxdoc |The Simplification of the Induction Conclusion (Step 0)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Simplification of the Induction Conclusion (Step 0)"
  :long "<code>
 Subgoal *1/2'
 (IMPLIES (AND (CONSP A)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL (APP <see topic='@(url |The Simplification of the Induction Conclusion (Step 1)|)'>(</see>APP A B) C)
                 (APP A (APP B C)))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to replace @('(APP A B)') by its definition.</p>")

(defxdoc |The Simplification of the Induction Conclusion (Step 1)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Simplification of the Induction Conclusion (Step 1)"
  :long "<code>
 Subgoal *1/2'
 (IMPLIES (AND (CONSP A)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL (APP <b>(IF </b><see topic='@(url |The Simplification of the Induction Conclusion (Step 2)|)'>(</see><b>CONSP A)</b>
                          <b>(CONS (CAR A) (APP (CDR A) B))</b>
                          <b>B)</b>
                      C)
                 (APP A (APP B C)))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Note that the @('IF') expression above is the simplified body of @('APP').
 But we know the test @('(CONSP A)') is true, by the first hypothesis.  Click
 on the link above to replace the test by @('T').  Actually this step and
 several subsequent ones are done during the simplification of the body of
 @('APP') but we want to illustrate the basic principles of simplification
 without bothering with every detail.</p>")

(defxdoc |The Simplification of the Induction Conclusion (Step 10)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Simplification of the Induction Conclusion (Step 10)"
  :long "<code>
 Subgoal *1/2'
 (IMPLIES (AND (CONSP A)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          <see topic='@(url |The Simplification of the Induction Conclusion (Step 11)|)'>(</see><b>EQUAL (APP (APP (CDR A) B) C)</b>
                 <b>(APP (CDR A) (APP B C)))</b>).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to use the Induction Hypothesis (which is the
 second of the two hypotheses above and which is identical to the rewritten
 conclusion).</p>")

(defxdoc |The Simplification of the Induction Conclusion (Step 11)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Simplification of the Induction Conclusion (Step 11)"
  :long "<code>
 Subgoal *1/2'
 <see topic='@(url |The Simplification of the Induction Conclusion (Step 12)|)'>(</see>IMPLIES (AND (CONSP A)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          <b>T</b>)
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to use the definition of @('IMPLIES').  Since the
 conclusion of the implication is now identically @('T'), the implication
 simplifies to @('T').</p>")

(defxdoc |The Simplification of the Induction Conclusion (Step 12)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Simplification of the Induction Conclusion (Step 12)"
  :long "<code>
 Subgoal *1/2'
 <b>T</b>
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>So, indeed, @('Subgoal *1/2'') <b>does</b> simplify to T!</p>

 <p>You can see that even in an example as simple as this one, quite a lot
 happens in simplification.</p>

 <p>You may click <see topic='@(url
 |Overview of the Simplification of the Induction Step to T|)'>here</see> to
 return to the main proof.</p>")

(defxdoc |The Simplification of the Induction Conclusion (Step 2)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Simplification of the Induction Conclusion (Step 2)"
  :long "<code>
 Subgoal *1/2'
 (IMPLIES (AND (CONSP A)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL (APP <see topic='@(url |The Simplification of the Induction Conclusion (Step 3)|)'>(</see>IF <b>T</b>
                          (CONS (CAR A) (APP (CDR A) B))
                          B)
                      C)
                 (APP A (APP B C)))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to apply the Axiom @('(IF T x y) = x').</p>")

(defxdoc |The Simplification of the Induction Conclusion (Step 3)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Simplification of the Induction Conclusion (Step 3)"
  :long "<code>
 Subgoal *1/2'
 (IMPLIES (AND (CONSP A)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL <see topic='@(url |The Simplification of the Induction Conclusion (Step 4)|)'>(</see>APP <b>(CONS (CAR A) (APP (CDR A) B))</b>
                      C)
                 (APP A (APP B C)))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to expand the definition of @('APP') here.</p>")

(defxdoc |The Simplification of the Induction Conclusion (Step 4)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Simplification of the Induction Conclusion (Step 4)"
  :long "<code>
 Subgoal *1/2'
 (IMPLIES (AND (CONSP A)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL (IF <see topic='@(url |The Simplification of the Induction Conclusion (Step 5)|)'>(</see><b>CONSP (CONS (CAR A) (APP (CDR A) B)))</b>
                     <b>(CONS (CAR (CONS (CAR A) (APP (CDR A) B)))</b>
                           <b>(APP (CDR (CONS (CAR A) (APP (CDR A) B)))</b>
                                <b>C))</b>
                     <b>C)</b>
                 (APP A (APP B C)))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to apply the Axiom @('(CONSP (CONS x y)) =
 T').</p>")

(defxdoc |The Simplification of the Induction Conclusion (Step 5)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Simplification of the Induction Conclusion (Step 5)"
  :long "<code>
 Subgoal *1/2'
 (IMPLIES (AND (CONSP A)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL (IF <b>T</b>
                     (CONS <see topic='@(url |The Simplification of the Induction Conclusion (Step 6)|)'>(</see>CAR (CONS (CAR A) (APP (CDR A) B)))
                           (APP (CDR (CONS (CAR A) (APP (CDR A) B)))
                                C))
                     C)
                 (APP A (APP B C)))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to apply the Axiom @('(CAR (CONS x y)) = x').</p>")

(defxdoc |The Simplification of the Induction Conclusion (Step 6)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Simplification of the Induction Conclusion (Step 6)"
  :long "<code>
 Subgoal *1/2'
 (IMPLIES (AND (CONSP A)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL (IF T
                     (CONS <b>(CAR A)</b>
                           (APP <see topic='@(url |The Simplification of the Induction Conclusion (Step 7)|)'>(</see>CDR (CONS (CAR A) (APP (CDR A) B)))
                                C))
                     C)
                 (APP A (APP B C)))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to apply the Axiom @('(CDR (CONS x y)) = y').</p>")

(defxdoc |The Simplification of the Induction Conclusion (Step 7)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Simplification of the Induction Conclusion (Step 7)"
  :long "<code>
 Subgoal *1/2'
 (IMPLIES (AND (CONSP A)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL <see topic='@(url |The Simplification of the Induction Conclusion (Step 8)|)'>(</see>IF T
                     (CONS (CAR A)
                           (APP <b>(APP (CDR A) B)</b>
                                C))
                     C)
                 (APP A (APP B C)))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to apply the Axiom @('(IF T x y) = x').</p>")

(defxdoc |The Simplification of the Induction Conclusion (Step 8)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Simplification of the Induction Conclusion (Step 8)"
  :long "<code>
 Subgoal *1/2'
 (IMPLIES (AND (CONSP A)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          (EQUAL <b>(CONS (CAR A)</b>
                       <b>(APP (APP (CDR A) B)</b>
                            <b>C))</b>
                 <see topic='@(url |The Simplification of the Induction Conclusion (Step 9)|)'>(</see>APP A (APP B C)))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to expand the definition of @('APP') here.  This
 time, we'll do the whole expansion at once, including the simplification of
 the resulting @('IF').  This is how ACL2 actually does it.</p>")

(defxdoc |The Simplification of the Induction Conclusion (Step 9)|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Simplification of the Induction Conclusion (Step 9)"
  :long "<code>
 Subgoal *1/2'
 (IMPLIES (AND (CONSP A)
               (EQUAL (APP (APP (CDR A) B) C)
                      (APP (CDR A) (APP B C))))
          <see topic='@(url |The Simplification of the Induction Conclusion (Step 10)|)'>(</see>EQUAL (CONS (CAR A)
                       (APP (APP (CDR A) B)
                            C))
                 <b>(CONS (CAR A)</b>
                       <b>(APP (CDR A) (APP B C))</b>))).
 </code>

 <p><img src='green-line.gif'></img></p>

 <p>Click on the link above to apply the Axiom that @('(EQUAL (CONS x y) (CONS
 u v))') is equal to the conjunction of @('(EQUAL x u)') and @('(EQUAL y v)').
 In this case, @('(EQUAL x u)') is trivial, @('(EQUAL (CAR A) (CAR A))').</p>")

(defxdoc |The Summary of the Proof of the Trivial Consequence|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Summary of the Proof of the Trivial Consequence"
  :long "<p>Note that at the conclusion of the proof, the system reminds you of
 the earlier <b>Warning</b>.</p>

 <p>It is a good idea, when the <b>Q.E.D.</b> flys by, to see if there were any
 Warnings.</p>")

(defxdoc |The Theorem that App is Associative|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Theorem that App is Associative"
  :long "<p><see topic='@(url |The Proof of the Associativity of App|)'><img
 src='walking.gif'></img></see></p>

 <code>
 ACL2!&gt;<b>(defthm associativity-of-app</b>
         <b>(equal (app (app a b) c)</b>
                <b>(app a (app b c))))</b>
 </code>

 <p>The formula above says @('app') is associative.  The @(tsee defthm) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 command instructs ACL2 to prove the formula and to name it
 @('associativity-of-app').  Actually, the @('defthm') command also builds the
 formula into the database as a @(tsee rewrite) <see
 topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>
 rule, but we won't go into that just yet.</p>

 <p>What we will consider is how the ACL2 theorem prover proves this
 formula.</p>

 <p>If you proceed you will find the actual output of ACL2 in response to the
 command above.  Some of the text is highlighted for the purposes of the tour.
 ACL2 does not highlight its output.</p>

 <p>You will note that we sometimes highlight a single open parenthesis.  This
 is our way of drawing your attention to the subformula that begins with that
 parenthesis.  By clicking on the parenthesis you will get an explanation of
 the subformula or its processing.</p>

 <p><see topic='@(url |The Proof of the Associativity of App|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |The Time Taken to do the Associativity of App Proof|
  :parents (|Pages Written Especially for the Tours|)
  :short "The Time Taken to do the Associativity of App Proof"
  :long "<p>The time it took us to explain this proof may leave the impression
 that the proof is complicated.  In a way, it is.  But it happens quickly.</p>

 <p>The time taken to do this proof is about 1/10 second.  The rest of the time
 (about 2/10 seconds) is spent in pre- and post-processing.</p>

 <p>Basically, this proof flashes across your screen before you can read it;
 you see the <b>Q.E.D.</b> and don't bother to scroll back to read it.  You
 have more important things to do than read successful proofs.</p>")



(defxdoc |The WARNING about the Trivial Consequence|
  :parents (|Pages Written Especially for the Tours|)
  :short "The WARNING about the Trivial Consequence"
  :long "<p>This <b>Warning</b> alerts us to the fact that when treated as a
 <b>rewrite</b> rule, the new rule @('TRIVIAL-CONSEQUENCE'), rewrites terms of
 the same form as a rule we have already proved, namely
 @('ASSOCIATIVITY-OF-APP').</p>

 <p>When you see this warning you should <b>think about your rules</b>!</p>

 <p>In the current case, it would be a good idea <b>not</b> to make
 @('TRIVIAL-CONSEQUENCE') a rule at all.  We could do this with @(':')@(tsee
 rule-classes) <see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon
 src='twarning.gif'/></see> nil.</p>

 <p>ACL2 proceeds to try to prove the theorem, even though it printed some
 warnings.  The basic assumption in ACL2 is that the <b>user</b> <b>understands
 what he or she is doing</b> but may need a little reminding just to manage a
 complicated set of facts.</p>")

(defxdoc |Undocumented Topic|
  :parents (|Pages Written Especially for the Tours|)
  :short "Undocumented Topic"
  :long "<p>This topic has not yet been documented.  Sorry</p>")

(defxdoc |Using the Associativity of App to Prove a Trivial Consequence|
  :parents (|Pages Written Especially for the Tours|)
  :short "Using the Associativity of App to Prove a Trivial Consequence"
  :long "<p><see topic='@(url
 |Overview of the Proof of a Trivial Consequence|)'><img
 src='walking.gif'></img></see></p>

 <p>If we have proved the @('associativity-of-app') rule, then the following
 theorem is trivial:</p>

 @({
  (defthm trivial-consequence
    (equal (app (app (app (app x1 x2) (app x3 x4)) (app x5 x6)) x7)
           (app x1 (app (app x2 x3) (app (app x4 x5) (app x6 x7))))))
 })

 <p>Below we show the proof</p>

 <p><see topic='@(url |Overview of the Proof of a Trivial Consequence|)'><img
 src='walking.gif'></img></see></p>")

(defxdoc |What Is ACL2(Q)|
  :parents (|Pages Written Especially for the Tours|)
  :short "What Is ACL2?"
  :long "<p><see topic='@(url |What is a Mathematical Logic(Q)|)'><img
 src='flying.gif'></img></see></p>

 <p>ACL2 is a <b>mathematical logic</b> together with a <b>mechanical theorem
 prover</b> to help you reason in the logic.</p>

 <p>The logic is just a subset of applicative <see topic='@(url
 |Common Lisp|)'>Common Lisp</see>.  (This link takes you off the main route of
 the tour.  You'll see some Common Lisp on the tour, so visit this later!)</p>

 <p>The theorem prover is an ``industrial strength'' version of the Boyer-Moore
 theorem prover, Nqthm.</p>

 <p><b>Models</b> of all kinds of computing systems can be built in ACL2, just
 as in Nqthm, even though the formal logic is Lisp.</p>

 <p>Once you've built an ACL2 model of a system, you can run it.</p>

 <p>You can also use ACL2 to prove theorems about the model.</p>

 <p><see topic='@(url |What is a Mathematical Logic(Q)|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |What is Required of the User(Q)|
  :parents (|Pages Written Especially for the Tours|)
  :short "What is Required of the User?"
  :long "<p><see topic='@(url
 |How Long Does It Take to Become an Effective User(Q)|)'><img
 src='flying.gif'></img></see></p>

 <p>It is not easy to build ACL2 models of complex systems.  To do so, the user
 must <b>understand</b></p>

 @({
    * the system being modeled, and

    * ACL2, at least as a programming language.
 })

 <p>It is not easy to get ACL2 to prove hard theorems.  To do so, the user must
 <b>understand</b></p>

 @({
    * the model,

    * ACL2 as a mathematical logic, and

    * be able to construct a proof (in interaction with ACL2).
 })

 <p>ACL2 will help construct the proof but its primary role is to prevent
 logical mistakes.  The creative burden &mdash; the mathematical insight into
 <b>why the model has the desired property</b> &mdash; is the user's
 responsibility.</p>

 <p><see topic='@(url
 |How Long Does It Take to Become an Effective User(Q)|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |What is a Mathematical Logic(Q)|
  :parents (|Pages Written Especially for the Tours|)
  :short "What is a Mathematical Logic?"
  :long "<p><see topic='@(url |What is a Mechanical Theorem Prover(Q)|)'><img
 src='flying.gif'></img></see></p>

 <p><img src='proof.gif'></img></p>

 <p>A mathematical logic is a formal system of formulas (<b>axioms</b>) and
 <b>rules</b> for deriving other formulas, called <b>theorems</b>.</p>

 <p>A <b>proof</b> is a derivation of a theorem.  To see a concrete proof tree,
 click <see topic='@(url |A Trivial Proof|)'>here</see>.</p>

 <p>Why should you care?  The neat thing about Theorems is that they are
 ``true.''  More precisely, if all the axioms are valid and the rules are
 validity preserving, then anything derived from the axioms via the rules is
 valid.</p>

 <p>So, if you want to determine if some formula is true, <b>prove it</b>.</p>

 <p><see topic='@(url |What is a Mechanical Theorem Prover(Q)|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |What is a Mechanical Theorem Prover(Q)|
  :parents (|Pages Written Especially for the Tours|)
  :short "What is a Mechanical Theorem Prover?"
  :long "<p><see topic='@(url
 |What is a Mechanical Theorem Prover(Q) (cont)|)'><img
 src='flying.gif'></img></see></p>

 <p>A <b>mechanical theorem prover</b> is a computer program that finds proofs
 of theorems.</p>

 <p><img src='automatic-theorem-prover.gif'></img></p>

 <p>The ideal mechanical theorem prover is <b>automatic</b>: you give it a
 formula and it gives you a proof of that formula or tells you there is no
 proof.</p>

 <p>Unfortunately, automatic theorem provers can be built only for very simple
 logics (e.g., <b>propositional calculus</b>) and even then practical
 considerations (e.g., how many centuries you are willing to wait) limit the
 problems they can solve.</p>

 <p><see topic='@(url |What is a Mechanical Theorem Prover(Q) (cont)|)'><img
 src='flying.gif'></img></see></p>")

(defxdoc |What is a Mechanical Theorem Prover(Q) (cont)|
  :parents (|Pages Written Especially for the Tours|)
  :short "What is a Mechanical Theorem Prover? (cont)"
  :long "<p><see topic='@(url |About Models|)'><img
 src='flying.gif'></img></see> To get around this, mechanical theorem provers
 often require help from the <b>user</b>.</p>

 <p><img src='interactive-theorem-prover-a.gif'></img></p>

 <p>Click <see topic='@(url
 |ACL2 as an Interactive Theorem Prover|)'>here</see> to continue downward.</p>

 <p><see topic='@(url |About Models|)'><img src='flying.gif'></img></see></p>")

(defxdoc |You Must Think about the Use of a Formula as a Rule|
  :parents (|Pages Written Especially for the Tours|)
  :short "You Must Think about the Use of a Formula as a Rule"
  :long "<p><see topic='@(url
 |Using the Associativity of App to Prove a Trivial Consequence|)'><img
 src='walking.gif'></img></see></p>

 <p>This is <b>good</b> and <b>bad</b>.</p>

 <p>The good news is that you can <b>program</b> ACL2's simplifier.</p>

 <p>The bad news is that when you command ACL2 to prove a theorem you must give
 some thought to <b>how that theorem is to be used as a rule</b>!</p>

 <p>For example, if after proving @('associativity-of-app') as previously
 shown, you engaged in the mathematically trivial act of proving it again but
 with the equality reversed, you would have programmed ACL2's rewriter to loop
 forever.</p>

 <p>You can avoid adding any rule by using the command:</p>

 <code>
 (defthm associativity-of-app
   (equal (app (app a b) c)
          (app a (app b c)))
   <b>:rule-classes nil</b>)
 </code>

 <p><see topic='@(url
 |Using the Associativity of App to Prove a Trivial Consequence|)'><img
 src='walking.gif'></img></see></p>")
