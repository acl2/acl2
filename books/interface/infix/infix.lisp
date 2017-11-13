; ACL2 Version 1.9

; Copyright (C) 1989-1996 Computational Logic, Inc. (CLI).  All rights reserved.

; Use of this software constitutes agreement with the terms of the
; license agreement, found in the file LICENSE.

; NOTE: we depend on the following externally defined package:

(in-package "USER")

;; MAJOR MODS

;; 1. Added ACL2 ~ formatting conventions in doc strings and comments.
;;    BUT THEY ONLY APPLY IF THIS FILE IS LOADED INTO ACL2.
;;    And the following may be used to disable it.
;;    *acl2-format-comments* => nil,  *acl2-format-doc-strings* => nil.
;;    Ignored in lisp.
;;    We handle doc strings by calling an ACL2 function
;;    that takes a doc string and 2 tables and returns
;;    a doc string, with the ACL2 formatting done.
;;    In order to handle arbitrary formatting within doc strings `~id[x]`
;;    will eventually map to `x`.  Thus, in scribe mode, ~id[@section](Testing)
;;    will come out as @section(Testing).
;;    Whereas @section(Testing) would come out as @@section(Testing)

;; BUGS

;; 1. In comments !p(implies a b) produces different results from !p(IMPLIES a b)
;;    Case is honored when reading comments.  !p may need to adjust case.
;;    We could just store things redundantly under `IMPLIES' and `implies',
;;    but then we would fail on `Implies'
;;
;; 2. "~ID[{\\it foo}]" does not map to "{\\it foo}".  The braces get quoted.
;;    Matt Kaufmann may fix.  Until then, the user can either not use
;;    any special formatting other that that provided by ! and ~, or can
;;    turn off ACL2 formatting, by setting *acl2-format-doc-strings* and
;;    *acl2-format-comments* to nil.  (See keyword args to INFIX-FILE and
;;    INFIX-SETTINGS.)  With this turned off you can still use ! and whatever
;;    native text formatting conventions you wish.
;;
;; 3. "!cfoo" when processed by nqftm2fmt will result in an attempt to
;;    eval foo.  This may break, if the user is not taking advantage of
;;    this !c `feature'.

;; Note the difference between the backslash in comments and the backslash
;; in doc strings.  In doc strings, because they are read as strings, they
;; need to be quoted (e.g. doubled).


;; INTERACTIONS

;; We treat comments and doc strings similarly.  The only difference is that
;; the initial comment characters of a comment line determine the format that
;; the comment text is imbedded in (e.g. running text, verbatim, format, etc.
;; See COMMENT-FORMAT documentation).

;; There are 3 (at least) kinds of imbedded formatting commands
;; that can occur in comments and doc strings.  They are handled
;; in distinct phases of processing.
;;
;;   1. ~ ACL2 doc string formatting commands.
;;   2. ! Infix commands.
;;   3.   Text formatter commands (Scribe or LaTeX)
;;
;; The first two effect the output of this infix processor.

;; To ensure that your text formatter (type 3) commands
;; are preserved during processing steps 1 and 2, the simplest
;; approach is to enclose the commands that you wish
;; to preserve in the ~id[...] form or between ~bid[] .. ~eid[] pairs.
;; SEE BUG 2 ABOVE.

;; Comments and doc strings are preprocessed to translate their ACL2
;; formatting commands to our target formatter.
;; Note that the ACL2 doc formatter goes to great lengths to make sure
;; weird characters in the target dialect are quoted.  So if you want
;; such things preserved, you need to use the ~id forms above.  Because
;; we now pass comment text through the ACL2 doc formatter, you
;; will need to treat comments as you treat doc strings.
;; You also need ;; to be careful of occurences of "~".  If a "~" is
;; not followed by an ACL2 formatting command, we will complain.

;; Load packages and macros we depend on.
;; [The following comment is modified from previous versions, which said
;; "Require must be here.".]
;; Require probably must be here if using other than GCL.

#-gcl
(progn
  (require "sloop" "/acl2/interface/infix/sloop")
  (use-package "SLOOP"))

;; Add space for CFUNs (compiled funs without environment) in GCL.

#+gcl(eval-when (load eval compile)
		(defun pages-allocated (type)
		  (declare (ignore type))
		  (multiple-value-bind
		   (nfree npages maxpage nppage gcs used) (system:allocated 'cfun)
		   (declare (ignore nfree maxpage nppage gcs used))
		   npages)))

#+gcl(eval-when (load)
		(cond
		 ((boundp 'si::*gcl-major-version*) ;GCL 2.0 or greater
		  (if (< (pages-allocated 'cfun) 200)  (sys:allocate 'cfun 200)))
		 ((< (sys::allocated-pages 'cfun) 200) (sys:allocate 'cfun 200))))

;; ACL2 doc string interaction.  First is for ~ directives, second
;; for special characters.

(defvar acl2-markup-table nil)
(defvar acl2-char-subst-table nil)

;; Read-keyword command uses the acl2 read to suck in keyword
;; commands.

(proclaim '(ftype (function (t) t)
		  acl2-parse-string
		  read-keyword-command))

(defvar a-very-rare-cons nil)

(defun read-keyword-form (key n)
  "This function reads the N args for keyword command, KEY,
where we have used ACL2 mechanisms to compute N.  It returns a form.
If KEY cannot be presented in keyword form, N will be NIL."
  (cond ((null n) key)
	((integerp n)
	 (let (args)
	   (sloop for i from 1 to n
		  do (setq args
			   (append
			    args
			    (list (readx *standard-input* nil a-very-rare-cons nil)))))
	   (cons (intern (symbol-name key)) args)))
	(t key)))

(eval-when (load eval compile)

;; Set this to be the directory in which we compile this file.
(defparameter *infix-directory* #.(namestring (truename "./")))

)

(defun load-base (s)
  (load (concatenate 'string *infix-directory* s)))

(eval-when (load eval)

(if (find-package "acl2")
    (progn (load-base "acl2-formatting.lisp"))

    (progn (defun acl2-parse-string (doc) (cons nil doc))
	   (defun acl2-keywordp (key) nil)
	   (defun read-keyword-command (key) key)))

)


#|

		A Conventional Syntax Pretty-Printer for ACL2

		      Originially written by Rober Boyer
                 Modified for Scribe by Michael K. Smith (2/92,8/93)
                 Modified for ACL2   by Michael K. Smith (10/93)


				 INTRODUCTION

The functions in this file implement a pretty-printer for Acl2 events.  The
syntax produced is conventional mathematical notation.

This file is not automatically compiled or loaded when building Acl2.
To use this printer, after compiling and loading Acl2, compile this file and
load it, i.e., (compile-file "infix.lisp") and (load "infix").  For
more information on installation see the README file in the directory
containing this file.

The following text is, currently, the only documentation for this facility.
Criticism of all sorts solicited.


				  BASIC USE

The intent is to take an ACL2 events file and produce a nicely formatted
document.  Knowing what text formatter you are targeting, you can insert text
formatting commands into comments.  You can also request an infix
transformation of prefix forms in comments (see documentation of function
NQFMT2FMT.

ONE NOTE OF CAUTION:  It is important that you know what text formatter you
are targetting, since the bulk of your comments will be copied literally into
the text input file.  It is up to you to ensure that the interaction of
your comments with the formatting convention of choice for the various
comment types results in legal text formatting commands.  That is, if you
are in Scribe mode and a comment contains an email message with net addresss
you should quote occurences of "@" as "@@".  More importantly, if you decide
that ";\" introduces a line to be formatted as raw LaTex (the default in
"latex" mode), you need to ensure that any occurrence of "_" or other LaTeX
special characters on such a line results in a meaningful formatting
command.  For simple transformations of .event files to LaTeX I suggest you
use the default :COMMENT-FORMAT (= 'BOYER).  This causes most comments to be
formatted within verbatim environments, which are not so picky about special
characters.  Scribe is more forgiving of these problems because it only has
the single special character, "@" that needs to be watched out for. (See
`SETTINGS THAT MAY BE MODIFIED IN MODE-THEORY.LISP'.)

There are two basic modes, "latex" and "scribe".  You can then build on top of
these to customize the printing of functions in your theory.  All mode
sensitivity should be contained in the file <mode>-theory.lisp.  Normally this
file also loads a basic file called <mode>-init.lisp.  The idea is that the
`-init' files contain the minimal required information for INFIX to do its job
with respect to a particular text formatter.  The `-theory' file contains the
details of how you want the functions in your theory to be printed.
`Scribe-theory.lisp' and `latex-theory.lisp' load `scribe-init.lisp' and
`latex-init.lisp', respectively.

In order to customize printing for a particular file of events, say
"clock.events", we suggest the following approach.  Each column shows the
procedure for the corresponding text formatter, Latex or Scribe.

First, assume we have a file "clock.events", in proper syntactic form for
acceptance by LD.  That is to say, suppose that the file
"clock.events" contains only legal event commands such as defun's and
defthm's, Lisp style comments, and the few other sorts of miscellaneous
instructions documented as legal instructions to LD.


1. Create clock-theory.lisp.  It should have the following form:

-    Tex                                 Scribe
-    ----------------------------------------------------------------
-    (load-base "latex-theory.lisp")     (load-base "scribe-theory.lisp")
-     ...
-     Your extensions and/or redefinitions.
-     See in particular the documentation on make-infix et.al.
-     under `SIX GENERAL OPERATOR SCHEMAS', and the examples at the
-     end of this file and in scribe-theory.lisp and latex-theory.lisp.
-     ...
-     INFIX-SETTINGS provides some simple control over an assortment of
-     formatting options.  See `SETTINGS THAT MAY BE MODIFIED IN MODE-THEORY.LISP'.
-     ...
-    (infix-settings :mode "clock"       (infix-settings :mode "clock"
-               :extension "tex" ...)               :extension "mss" ...)

2. Save clock-theory.lisp, preferably in the same directory with clock.events.

3. Call infix-file.  The simplest call on infix-file would be just

-    (infix-file "clock").

   which will result in the file "clock.tex" or "clock.mss"

4. Run the appropriate formatter.

5. Special considerations for latex vs. scribe.

-  To get an index in LaTeX.             To avoid an index in Scribe
-  ----------------------------------------------------------------
-  %latex clock                          Insert @disable(Index) in clock.mss.
-  %makeindex clock
-  %latex clock


A full blown call to infix-file includes a file root and keyword arguments.
Below is such a call with keywords supplied with their defaults.

-  (infix-file fl :print-case :downcase :mode nil :chars-wide 77 :comment t)
-
-   :print-case - must be one of :downcase, :upcase, or :capitalize.
-                 DEFAULT: :downcase.
-
-   :mode       - if not provided (thus defaulting to nil) we look for
-                 "fl-theory.lisp" and load it if present.  If not, we use
-                 the mode of the last successfull call to infix-file or
-                 query whether you want to use Scribe or Latex mode.
-                 In this last case you will need to know where the basic
-                 theory files are located.  Simplest is to create a trivial
-                 -theory file in the same directory as the event files that
-                 just loads appropriate scribe or latex -theory file.
-                 DEFAULT: fl root name.  If not found, queries the user.
-
-   :chars-wide - approximate width in characters of the formatted output.
-                 Controls where infix inserts line breaks within expressions.
-                 DEFAULT: 77.
-
-   :comment    - If t, then certain specially marked Acl2 expressions in
-                 comments are replaced with their conventional notation.
-                 See the documentation of the function `nqfmt2fmt' below for
-                 a description of the special syntax for this replacement
-                 process.  We assume you use this feature.  If not,
-                 set *nq-default* to NIL in your mode file.
-                 DEFAULT: T.


			       COMMENT HANDLING

- Jul 28 93 MKS - Extended comment handling.
- Aug  3 93 MKS - Still haven't done anything with internal comments.

Modified Treatment of comments: `infix-file' preserves comments
between events, but skips over comments within events.  We completely
skip comments within events because we have not figured out how to
place them appropriately mechanically.  Documentations strings in
events are handled, normally by pulling them out of the event and
inserting them before the event itself.

Comments are formatted in several ways, depending on the character immediately
following the semi-colon or OPEN-BAR-COMMENT.  A comment may be turned into:

- 1. Running TEXT.  The comment chars (see definition following) are
- eliminated and the text is copied to the output file.
-
- 2. A FORMATted environment.  The comment chars (see definition
- following) are eliminated, line breaks and spaces are preserved, and
- the font is the default document font.
-
- 3. A VERBATIM environment. The comment chars may or may not be preserved,
- line breaks and spaces are PRESERVED and the font is a fixed width font.
-
- 4. An EMPHASIS environment. Like format, but the font is italic.

This set, which is used by the named formats in *comment-format-alist*, can
be extended by modifying the value of *comment-environment-mapping* in your
theory file.

To replace the comment format conventions, use (define-comment-format name
format).

The format argument has two parts, one for semi-colon comments
and the other for #| ... |# comments.  The assignment below corresponds to
Boyer's initial setting.

- (define-comment-format 'boyer
-   '((#\; (("\\"   nil   text)) nil verbatim #\;)
-     (#\# (("\\"   nil   text))   t verbatim )))

The structure of each of these lists is
-  type      ::= (label (substring*) spaces-p format [char])
-  substring ::= (string spaces-p format [char])

LABEL indicates which of the two types of comments we are looking at, either
those that start with a SEMI-COLON or those that start with LB VERTICAL-BAR.
We determine what to do in the various cases (which amounts to choosing
SPACES-P, FORMAT, and CHAR) based on whether the comment type indicated by
LABEL is followed by any of the strings that begin SUBSTRINGS or not.  If it
matches, we use the components of the matching substring, otherwise we use
the default for the comment type, i.e.  the elements of the type list.

-  If SPACES-P, consume one space if there is one.
-  Begin formatting according to FORMAT.
-  Insert CHAR.

So, for the example above, the first sublist, whose car is the semi-colon
character, describes how to format comments that begin with a semi-colon followed
by specific strings.  There are two possibilites.  If the semi-colon is not
followed by a back-slash (\), we don't look for a space, we ensure we are in a
verbatim environment, and print a semi-colon.  If semi-colon is followed by a
back-slash, we don't look for a space and ensure that we are in a text environment.

Thus, if we encounter a comment beginning ";\", the comment should be
inserted as top level text with no special formatting.  The ";\" will not show
up in the output.


- COMMENT TRANSFORMATIONS:

There are three versions.  One reflects MKSmith's preferences, one Boyer's,
and one the Common Lisp defaults.  MKSmiths is the default.  To get Boyer's,
do (setup-comment-format 'boyer).  To get Common Lisp's, do
(setup-comment-format 'cl).  You can insert this form in your theory file.
To create your own conventions, see DEFINE-COMMENT-FORMAT.

- Description:

-  BT begins running text, with no environment modifiers.
-  BF ... EF corresponds  to <begin-format> ... <end-format>
-  BV ... EV corresponds  to <begin-verbatim> ... <end-verbatim>
-  BE ... EE corresponds  to <begin-emphasis> ... <end-emphasis>
-  BS ... ES corresponds  to <begin-section-name> ... <end-section-name>
-  BC ... EC corresponds  to <begin-comment> ... <end-comment>
-
-              MKS           Boyer             CL
-
-  #| ... |#   BT...         BV ... EV         BT...
-  #|\ ... |#  BT...         BT ...            BT...
-  #|- ... |#  BF... EF      BV- ... EV        BF... EF
-  #|; ... |#  BV... EV      BV; ... EV        BV... BV
-
-  ; ...       BT...         BV; ... EV        BE... EE
-  ;; ...      BT...         BV;; ... EV       BF... EF
-  ;;; ...     BV... EV      BV;;; ... EV      BT...
-  ;;;; ...    BV;... EV     BV;;;; ... EV     BS... ES

-  ;# ...      BC... EC
-  ;\ ...      BT...         BT ...            BT...
-  ;- ...      BF... EF      BV;- ... EV       BF... EF
-  ;+ ...      BV... EV      BV;+ ... EV       BV... EV
-  ;! ...      BE... EE      BV;! ... EV       BE... EE

-  ;;- ...     BF; ... EF    BV;;- ... EV      BF; ... EF
-  ;;+ ...     BV; ... EV    BV;;+ ... EV      BV; ... EV
-  ;;! ...     BE; ... EE    BV;;! ... EV      BE; ... EE



				   COVERAGE

The `infix-file' function should handle the entirety of the Acl2 term syntax
checked by ld.  We DO print out the `hint' parts of events.



				  MOTIVATION

We hope this notation will facilitate the communication of work with Acl2 to
those who do not happily read Lisp notation.  But we have no expectation that
this notation will make it easier for the Acl2 user to formulate or to prove
theorems.


			      NO ERROR CHECKING

Warning about the absence of error checking: In general, user-callable
subroutines of Acl2 do extensive syntactic checking on their input and
explicitly report syntactic errors.  But this pretty printer does not do such
syntactic checking.  Rather, we assume the given input is known to be
syntactically correct, namely as though checked by `LD'.  Failure to
provide input in correct syntactic form can result in nasty, brutish, and
short Lisp errors.


			  OTHER USER-LEVEL FUNCTIONS

Besides `infix-file', here are the other user-level functions supported by
this file.

(a) (print-examples) creates a stand-alone, file named
"infix-examples.tex" or "infix-examples.mss", which is a summary of
the syntax we print in terms of the official Acl2 syntax.  This file
will also correctly report any user modifications made to the syntax
by invocation of the make... functions described later.  We hope that
users will want to include this file in reports about Acl2 use to
make clear what syntactic conventions they are using.

(b) (NQFMT2FMT "foo") copies the file "foo.lisp" to the file
"foo.tex" or "foo.mss", but along the way, Acl2 terms preceded by an
exclamation mark and certain alphabetic characters are replaced with
the formatting commands for the conventional notation this printer
generates.  For example, when in latex mode, if nqfmt2fmt encounters
!t(gcd x (difference y x)) in a file, it will replace it with
{\rm{gcd}}\,({\it{x\/}}, {\it{y\/}} $-$ {\it{x\/}}).  We find the
former much easier to read in a file.  nqfmt2fmt thus permits one to
keep Acl2 forms in files to be read and edited by humans, e.g., in
comments in Acl2 event files.  Ordinary uses of !, e.g., uses of it
followed by white space or punctuation characters, are, of course,
unaltered.

Let ev  be an Acl2 event form, e.g., (defun foo (x) 3)
    fm  be an Acl2 term, e.g., (plus x y)
    foo be a symbol

Summary:

!Pfm  - Pretty print.
!Tfm  - Pretty print but without any line breaks.
!Eev  - Format event.
!Ifoo - Identity, handling special chars of formatter.
!Qfn  - `fn'.
!Vfoo - Verbatim.

Begin HACK ALERT

!Cform - [C]ommand evaluate.  This should really be E for EVAL.
         The form is evaled in Lisp.  This allows you to do things
         like dynamically change the margin (*rightmost-char-number*)
         turn indexing on (SETQ *DO-NOT-INDEX* NIL) and off
         (SETQ *DO-NOT-INDEX* T), or even redefine a printer.

End HACK ALERT

!section(text)    - Format text as a section header.
!subsection(text) - Format test as a subsection header.

!B(text) - bold
!S(text) - italic

Detail:

!Eev  - Event. Results in conventional notation for ev.

!Ifoo - Identity. Results in foo, but with with formatting sensitive
        characters quoted.

!Pfm  - Pretty print.  Results in conventional mathematical notation.

!Qfn  - where fn is a symbol, results in fn surrounded by single gritches,
        after formatting sensitive characters have been quoted, e.g., !qfoo results
        in `foo' in TeX.  Useful for distinguishing function symbols from other
        words in a sentence, since function symbols appear in Roman.
        Mnemonic: Q -- think Quoted.

!Tfm  - where fm is an Acl2 term, results in conventional mathematical
        notation for fm, but without any line breaks.
        Mnemonic: T -- think Term.

!Vfoo - foo is printed as is, but in typewriter font, and with special characters quoted.
        Mnemonic: V -- think Verbatim.

! followed by anything else is left alone, along with the exclamation mark.

See the comment at the beginning of the definition of nqfmt2fmt, below, for
details on the syntax and replacements.  There is also an option to nqfmt2fmt
for simply stripping out the !commands.

(c) (infix-form fm) prints (to *standard-output*) the formatting input for the
conventional notation for the Acl2 term fm.  `infix-form' and `infix-event'
can be used to generate Latex or Scribe to be inserted manually into
papers, but we recommend the use of nqfmt2fmt, described above, for this
purpose.

(d) (infix-event ev) prints (to *standard-output*) the Latex or Scribe for the
conventional notation for the Acl2 event ev.


			   USER EXTENSION OF SYNTAX

`infix-file' is table-driven, and it is very easy to extend in certain ways,
e.g., to introduce a new infix operator.  See the very end of this file, at
`USER MODIFIABLE TABLE SETUP', for examples of how to establish new syntax.

Also see `SETTINGS THAT MAY BE MODIFIED IN MODE-THEORY.LISP' to see how to
control additional features of the printing process, e.g. indexing, details of
comment handling, parentheses around expressions, etc.


                          PARENTHESES and PRECEDENCE

This pretty-printer does not provide a facility for the suppression of
parentheses via the declaration of precedence for operators.  An objective in
printing a formula is clarity.  We know of very, very few cases (e.g., + and
*) where precedence is something on which people agree.  As a small
contribution towards the suppression of parentheses , we do drop the outermost
parentheses of a formula when the formula is an argument of a function that is
being printed in the usual f(x,y) notation, with subterms separated by
parentheses and commas.

In addition, the user has two alternatives to fully parenthesized notation.

1. Eliminate them at the top level by setting *TOP-PARENS-ELIMINABLE*
   to T.

2. Eliminate them except where absolutely required (e.g. around
   normal, prefix function arguments) by setting
   *TOP-PARENS-ELIMINABLE-DEFAULT* to T.

See the section `SETTINGS THAT MAY BE MODIFIED IN MODE-THEORY.LISP'.


                               OTHER FORMATTERS

There are some functions in this file that take advantage of similarities
between LaTeX and Scribe.  They are marked with `WARNING: Latex/Scribe
dependency'.  If you want to generate input to some other formatter you may
want to take a look at these.  Not guaranteed to be complete.  In order to
built a -init.lisp file for some other formatter make sure you look at
`SPECIAL VARIABLES THAT MUST BE DEFINED IN MODE-INIT.LISP'.


                            END OF COMMENTS ON USE

|#

#| ---------------------------------------------------------------------------------

                          COMPILATION DEPENDENCIES
|#

;; Check that we are in a compatible Acl2.

;(eval-when (load eval compile)
; (or (boundp 'infix-input-file-type)
;     (error "~%~%infix.lisp is to be compiled and used with acl2 versions 1992 or later,~%~
;      not stand-alone or with older versions of acl2.~%")))

;; Not used.

; (defun untranslate-event (form) (acl2::untranslate form nil))

;; Included from Nqthm.

(defun our-flatc (x)
  (cond ((stringp x) (+ 2 (length x)))
        ((symbolp x) (length (symbol-name x)))
        ((integerp x) (our-flatc-number x))
        (t (let ((*print-base* 10)
                 (*print-pretty* nil)
                 (*print-radix* nil)
                 (*print-level* nil)
                 (*print-length* nil)
                 (*print-case* :upcase))
             (length (format nil "~a" x))))))

(defun our-flatc-number (n)
  (cond ((< n 0) (1+ (our-flatc-number (- n))))
        ((< n 10) 1)
        (t (1+ (our-flatc-number (floor (/ n 10)))))))

(defvar a-very-rare-cons (cons nil nil))


#| ---------------------------------------------------------------------------------

             SETTINGS THAT MAY BE MODIFIED IN MODE-THEORY.LISP.

Use INFIX-SETTINGS to set this first set of properties.
See files latex-mode.lisp and scribe-mode.lisp for examples.

The things you can control with INFIX-SETTINGS are listed below.  The first
choice is the default, so if you are happy with the default you don't need to
fool with the setting.  See examples after the enumeration.  These are
all keyword arguments to INFIX-SETTINGS.

1. MODE: a string naming the theory we are in.  The default is constructed
   the the name of the events file.  If no corresponding -theory file is found,
   query the user.

2. EXTENSION: type of output file ("mss", "tex", ...)

3. OP-LOCATION: ['FRONT, 'BACK]
   Controls where operator is printed when printing on multiple lines
   'FRONT - put operator at beginning of line (Smith's way)
   'BACK  - put operator at end of line (Boyer's way)

4. COMMENT-FORMAT: ['SMITH, 'BOYER, 'CL]
   Chooses from one of the predefined conventions for determining from the character
   following the comment character how to format the comment.  This interacts
   with your use of native-mode formatting commands in comments in the .events file.

   For your own control over this, use (DEFINE-COMMENT-FORMAT name format).
   See the description of comment handling for more information.

5a. FORMAT-!-IN-COMMENTS: [T, nil]
   If true, run nqfmt2fmt over comments.

5b. ACL2-FORMAT-COMMENTS: [T, nil]
   If true, run the acl2 doc string formatting process over comments.

5c. ACL2-FORMAT-DOC-STRINGS: [T, nil]
   If true, run the acl2 doc string formatting process over doc strings.

6. ELIMINATE-TOP-PARENS: boolean [T, nil]
   Indicates whether you wish the outermost parentheses of function bodies suppressed.

7. ELIMINATE-INNER-PARENS: boolean [T, nil]
   Suppresses all precedence related parentheses.  Much cleaner output, though an
   expression printed with this flag=true may reconstruct oddly, depending on the
   reader's precedence model.  The indentation of large expressions helps somewhat.

   Example: Consider the defun,
   (defun foo (l)
     (and (plistp l) (and (bar l) (baz (cdr l)))))

   Below is a table showing how the body (the AND) would be printed.

   TOP  INNER  Printed output of body of foo
   t    t      plistp(l) & bar(l) & baz(cdr(l))
   t    nil    plistp(l) & (bar(l) & baz(cdr(l)))
   nil  t      (plistp(l) & bar(l) & baz(cdr(l)))
   nil  nil    (plistp(l) & (bar(l) & baz(cdr(l))))

8. NO-INDEX: boolean [NIL, t]. If T, then no index is generated.

9. NO-INDEX-CALLS: boolean [NIL, T] or list
   If you want all function calls indexed, NIL. you do not want any function use indexed, T.
   If you want to exclude certain function calls, provide a list of function
   names to be ignored.

If you do not provide a keyword value pair, the settings remains unchanged.
Thus, you really don't have to call this function.  Though typically you want
to change the :mode if you have created a special theory extension on top of
Scribe or Latex.

The minimal call on INFIX-SETTINGS requires a mode and extension.

(INFIX-SETTINGS :MODE                   "scribe"
		:EXTENSION              "mss"   )

The maximal call, setting everything explicitly.
The following shows infix-settings with all of the default settings as
arguments.  The comments indicate required types of values.  `...' indicates
settings that the user may extend with more work.

(INFIX-SETTINGS :MODE                   "scribe" ; string ["scribe","latex",...]
		:EXTENSION              "mss"    ; string ["mss","tex"]
		:OP-LOCATION            'FRONT   ; ['FRONT,'BACK]
		:COMMENT-FORMAT         'SMITH   ; ['SMITH,'BOYER,'CL,...]
		:FORMAT-!-IN-COMMENTS   NIL      ; [t,nil]
		:ACL2-FORMAT-COMMENTS   T        ; [t,nil]
		:ACL2-FORMAT-DOC-STRINGS T       ; [t,nil]
		:ELIMINATE-TOP-PARENS   T        ; [t,nil]
		:ELIMINATE-INNER-PARENS T        ; [t,nil]
		:NO-INDEX               NIL      ; [t,nil]
		:NO-INDEX-CALLS         NIL      ; [t,nil,l]
		)

|#


; Variable controlling handling of special formatting within comments.  See `NQFMT2FMT'.

(defparameter *nq-default* t)

; If *INFIX-OP-LOCATION* (:OP-LOCATION arg to INFIX-SETTINGS) is 'BACK
; then you get Boyer's style of printing a list of infix operators and
; arguments.  If 'FRONT, you get Smiths.  Smiths is the default.
; You can tell who last editted this file.

;- BACK form is      e.g
;-  arg1 op               foo(a,b,c) &
;-  arg2 op               bar(a,1) &
;-  argn                  some-long-function-name(a,b,1)

;- FRONT form is       e.g
;-     arg1                 foo(a,b,c)
;-  op arg2               & bar(a,1)
;-  op argn               & some-long-function-name(a,b,1)


; Either FRONT or BACK.
(defparameter *infix-op-location* 'front)

; Extension of input file.
(defparameter infix-input-file-type "lisp")


#|
             SETTINGS THAT MAY BE RESET IN MODE-THEORY.LISP. (2)

The following variables do not NEED to be reset in your mode file, but they may be.

|#

(defparameter *top-parens-eliminable* nil)

; *TOP-PARENS-ELIMINABLE-DEFAULT* is a global.  If t, then it is ALWAYS
; assumed to be ok to omit the outermost parentheses of the expressions
; we are about to print.  This may procudes output that cannot
; unambiguously be parsed back into its original sexpr format.

(defparameter *top-parens-eliminable-default* nil)

#|\

INDEXING

If you do not any index (SETQ *DO-NOT-INDEX* T).
If you do not want occurences of functions indexed (SETQ *DO-NOT-INDEX-CALLS* T).
If you want to exclude certain functions, add them to the list *DO-NOT-INDEX-CALLS-OF*.
If you want no index, see comments at beginning of file.


DEBUGGING

Setting *INFIX-TRACE* to T will provide some debugging help when testing new mode files.


                     END OF SETTINGS FOR MODE-INIT.LISP.

---------------------------------------------------------------------------------
|#


; ---------------------------------------------------------------------------------
;
;             SPECIAL VARIABLES THAT MUST BE DEFINED IN MODE-INIT.LISP.
;
; Use INFIX-SETTINGS to set this variable.  See Introduction.

; One of NIL, "latex", "scribe", or another string.
(defparameter *infix-mode* nil)


;; STRINGS BASED ON THE TARGET FORMATTER (LaTeX, Scribe, ...)

;; Default extension of created files.
(defvar *mode-extension* nil)

(defparameter *standard-prelude* nil)
(defparameter *standard-postlude* nil)

(defparameter *example-prelude* nil)
(defparameter *begin-example-table*  nil)
(defparameter *end-example-table*  nil)
(defparameter *example-table-size*  nil)
(defparameter *example-postlude*  nil)

;; BASIC BRACKETS AND THEIR QUOTED VERSION.

(defparameter *begin*  "")
(defparameter *end*    "")
(defparameter *lbrace*  "")
(defparameter *rbrace*  "")

;; ENVIRONMENT BEGIN-END PAIRS

(defparameter *begin-index*  "")
(defparameter *end-index*  "")

(defparameter *begin-text-env* "")
(defparameter *end-text-env* "")

(defparameter *begin-verbatim-env* "")
(defparameter *end-verbatim-env* "")

(defparameter *begin-format-env* "")
(defparameter *end-format-env* "")

(defparameter *begin-emphasis-env*  "")
(defparameter *end-emphasis-env*  "")

(defparameter *begin-comment-env*  "")
(defparameter *end-comment-env*  "")

(defparameter *begin-section-env*  "")
(defparameter *end-section-env*  "")

(defparameter *begin-subsection-env*  "")
(defparameter *end-subsection-env*  "")

(defparameter *begin-tt-env*  "")
(defparameter *end-tt-env*    "")

(defparameter *begin-string-env*  "")
(defparameter *end-string-env*    "")

(defparameter *begin-bold-env*  "")
(defparameter *end-bold-env*    "")

(defparameter *begin-italic-env*  "")
(defparameter *end-italic-env*    "")

(defparameter *begin-sc-env*  "")
(defparameter *end-sc-env*    "")

(defparameter *begin-enumerate-env*  "")
(defparameter *end-enumerate-env*  "")
(defparameter *begin-item*  "")
(defparameter *end-item*  "")

(defparameter *forall* "")
(defparameter *exists* "")

;; TABBING AND INDENTING ENVIRONMENT AND TAB OPERATIONS

(defparameter *begin-tabbing-env*  nil)
(defparameter *end-tabbing-env*  nil)
(defparameter *new-tab-row*  nil)

;; Needs to be redefined in <mode>-init.lisp
;; No longer used. A LIE!
(defmacro new-tab-row (&optional followed-by-infix-print-term)
  (declare (ignore followed-by-infix-print-term))
  '(pprinc *new-tab-row*))

(defparameter *tab*  nil)

(defparameter *column-separator* nil)

; *tabs-list* is a text-formatter specific variable.  Typically of the form of a
; list of pairs, either (tab . n) or (lm . n), where n is the value of
; *infix-loc* when we set tabs and margins.

(defparameter *tab-list* nil)
(defparameter *tab-stack* nil)

(defparameter *set-margin* nil)
(defparameter *pop-margin*  nil)
(defparameter *set-tab* nil)

(defparameter *default-op-tab-space* "")

(defparameter *adjust-tab-before-margin* nil)

;; FONTS

(defparameter *function-font*  nil)
(defparameter *neg-str* nil)

;; MATH ENV AND OPERATORS

(defparameter *math-format*  nil)
(defparameter *math-begin*  nil)
(defparameter *math-end*  nil)

(defparameter *math-thick-space*  nil)
(defparameter *math-thin-space*  nil)

(defparameter *subscript*  nil)

(defparameter *begin-subscript* nil)
(defparameter *end-subscript* nil)

;; MISC.

(defparameter *newpage*  nil)

(defparameter *comma-atsign*  nil)
(defparameter *caret*  nil)

(defparameter *dotted-pair-separator* " . ")
(defparameter *dotted-pair-separator-newline* ". ")

(defparameter *no-tab-event-trailer*  nil)
(defparameter *print-default-event-header*  nil)
(defparameter *print-default-lisp-header*  nil)

(defparameter *print-default-command-header*  nil)
(defparameter *no-tab-command-trailer*  nil)


;; ACL2 RELATED.

;; We conditionally apply the ACL2 formatting conventions.

(defvar *acl2-format-comments* t)
(defvar *acl2-format-doc-strings* t)


#|\---------------------------------------------------------------------------------

              FUNCTIONS THAT MUST BE DEFINED IN MODE-INIT.LISP.

Signatures as passed to (proclaim '(ftype ...) ..)

() -> t : function of no args, returning arbitrary type

            begin-tabbing                end-tabbing
            begin-normal-text            end-normal-text
            increase-margin
            set-margin                   pop-margin
            get-margin                   pop-tab
            do-tab
            begin-flushright             end-flushright

            ;; to-current-margin            ;; newline-to-current-margin
            ;; force-newline

(t) -> t : function of one arbitray arg, returning arbitrary type

            flushright


(t) -> t : function of one optional arg, returning arbitrary type

            set-tab

(character) -> t : function of one character arg, returning arbitrary type

            handle-special-chars
            handle-special-chars-in-string
            char                         { Why is this in this list? }


---------------------------------------------------------------------------------

                           IMPLEMENTATION COMMENTS

The three `tables' that govern the printing are the variables:

1. *atom-alist*, which governs printing of variables, numbers, T, F, and NIL.

2. *fn-alist*, which governs the printing of any term that starts with a
function symbol, including LET, COND, CASE, LIST, LIST*, and FOR.

3. *event-printer-alist*, which governs the printing of events.

4. *special-quoted-forms-alist*, which governs the special printing of selected
quoted symbols.

Each table is an alist.  Each member of any of these alists is a list (symbol
fn), where symbol is the car of a form (or in the case of a non-consp form,
the form itself) which is about to be printed.  fn is a Common Lisp function
of one argument which is called on the form in question to do the printing.
For each alist, there is a default function that is returned if a symbol is
not explicitly represented.  One such default is the function
default-fn-printer, which is a good function to study before contemplating
serious modifications to this file.

Although adding new members to these alists, and defining corresponding
special purpose functions, is certainly sensible and easy, there are several
points to be made.

1.  It is unlikely that there will be any call to edit `*atom-alist*' until
and unless TRANSLATE is changed.

2.  *fn-alist* can be most easily modified by the use of the macros
make-infix-op, make-unary-prefix-op, make-unary-suffix-op,
make-infix-multiple-op, and make-prefix-multiple-op.  See the very end of the
file for many examples of how syntax operators can be easily established.

We really do assume throughout this code that the input file has passed
through LD, e.g., we assume that the last test in a `cond' is on T,
the last test in a case is an `otherwise', and that the third argument to
`defthm' is something that translate can accept.


STANDARD OUTPUT USED

Printing.  We do *all* of our printing of formulas to *standard-output*, so we
call princ and write-char on just one argument, the thing to be printed.

|#

;                                   PRINTING

; The setting of the *left-margin* causes only the stuff within tabbing
; environments to be moved over.  Acl2 event forms that do not use that
; tabbing environment should be adjusted by other means by the user if desired.
; *left-margin* may be set before invoking infix-form or infix-event.

(defparameter *left-margin* 0)

; *rightmost-char-number* is bound sometimes to alter subsidiary printing
; operations that more text needs to be printed on the same line after they
; finish.

(defparameter *rightmost-char-number* 77)

; *infix-loc* is a good estimate of how far in from the left margin we
; currently are, counting as 1 any character, or any symbol not wired in.

(defparameter *infix-loc* 0)

; If *testing* is t, then we are not really printing but only counting the
; characters we would print, trying to see if a line break is necessary.

(defparameter *testing* nil)

(defparameter *latex-indent-number-limit* 13)

; In *tabs-in* we keep track of how deep into tabs we are so that we can punt
; if necessary.

(defparameter *tabs-in* 0)

(defparameter *do-not-use-tabs* nil)

; We cannot place defparameters for the following three special symbols at this
; place in the file because their initial values contain `functions' of
; functions to be defined later.

(proclaim '(special *atom-alist* *fn-alist*))

(defparameter *event-printer-alist* nil)

(defparameter *index-entry-max* 100)

(defparameter *negative-constant-table* nil)

(defparameter *negative-infix-table* nil)

(defparameter *constant-ops* nil)

(defparameter *infix-ops* nil)

(defparameter *infix-multiple-ops* nil)

(defparameter *prefix-multiple-ops* nil)

(defparameter *suffix-multiple-ops* nil)

(defparameter *unary-prefix-ops* nil)

(defparameter *negative-unary-prefix-table* nil)

(defparameter *unary-suffix-ops* nil)

(defparameter *negative-unary-suffix-table* nil)

(defparameter *unary-abs-ops* nil)

(defparameter *tracing-advise-break* nil)

(defparameter *white-space* '(#\Space #\Newline #\Tab #\Page))

(defparameter *started-a-verbatim* nil)

(defparameter *started-a-format* nil)

(defparameter *reported-tabs* nil)

;  This `secret' function symbol is used to print out integers generated by
; readins #b, #o, or #x syntax.

(defparameter *infix-radix* (make-symbol "*infix-radix*"))

; One should add to this list if any other special forms are hard wired into
; this printer.

(defparameter *wired-in-infix-examples*
  '((if x y z)
    (cond (test1 value1) (test2 value2) (t value3))
    (case x (key1 answer1) (key2 answer2) (otherwise default))
;    (for x in l when (test x) collect (fn x))
    (let ((var1 val1) (var2 val2)) form)
    (let* ((var1 val1) (var2 val2)) form)
    (forall (x y) (p x))
    (exists (x y) (p x))
    (not x)))

; Severe warning on printing.  It is illegal for any function in this
; file to do any printing except via these four printing macros:
; pprinc, pprin1, pformat, and pwrite-char.  This may be true
; transitively, e.g., pprinci calls pprinc.

; This rule is imposed so that the `hack' of printing invisibly (see
; *testing*) will work.  The point is that any printing operation may
; be called many times!  But we do not want to print unless the
; special *testing* is bound to nil!  Key fact: if *testing* is t, we
; DO NOT print.

; A very sloppy fudge factor to account for the fact that in \tt mode,
; characters are fatter.

(defparameter *tt-size* 1.3)

(defparameter *do-not-index* nil)

(defparameter *do-not-index-calls* nil)

(defparameter *infix-comma* (make-symbol "comma"))

(defparameter *infix-comma-atsign* (make-symbol "comma-atsign"))

(defparameter *infix-backquote* (make-symbol "backquote"))

(defparameter *do-not-index-calls-of*
  (list *infix-radix* *infix-comma* *infix-comma-atsign* *infix-backquote*))

(defvar *user-package* (find-package "user"))

(eval-when (load compile eval)

(defmacro pprinc (x)
  `(or *testing* (let ((*package* *user-package*))
		   (princ ,x))))

(defmacro pprin1 (x)
  `(or *testing* (let ((*package* *user-package*))
		   (prin1 ,x))))

(defmacro pformat (&rest x)
  `(or *testing* (let ((*package* *user-package*))
		   (format ,@x))))

(defmacro ppformat (&rest x)
  `(or *testing* (let ((*package* *user-package*))
		   (format *standard-output* ,@x))))

(defmacro pwrite-char (x)
  `(or *testing* (write-char ,x)))

)

; It is absolutely desireable that any printing done by any function inside this
; file, within the scope of a tabbing environment, be done with with pprinci,
; pprin1, or print-atom IF the printing is to contribute `real', i.e.,
; non-formatting, characters to the final output.  The optional second argument
; specifies how many characters are being contributed, with default 1.  If
; *testing* is t, not only do we not want to print, but we want to throw out to
; advise-break if we have exceeded the *rightmost-char-number*.

(defvar *newline-in-text* "")
(defvar *newline-in-env*  "")

(defvar *force-newline-in-text* "")
(defvar *force-newline-in-env*  "")

(defvar *prev-line-loc* nil)

(defun line-return ()
  (setq *prev-line-loc* *infix-loc*)
  (pwrite-char #\Newline)
  (setq *infix-loc* (get-margin)))

(defun newline-in-env (&optional force)
  (if force (pprinc *force-newline-in-env*) (pprinc *newline-in-env*))
  (line-return))

(defun newline-in-text (&optional force)
  (if force (pprinc *force-newline-in-text*) (pprinc *newline-in-text*))
  (line-return))

(eval-when (load compile eval)

(defmacro begin-text () `(begin-normal-text))

(defmacro end-text () '(end-normal-text))

(defun last-line-feed-position (x)
  (if (stringp x) (position #\linefeed x :from-end t)))

(defmacro pprinci (x &optional (i 1))
  `(let ((x ,x)
	 (i ,i)
	 n)
     (pprinc x)
     (setq *prev-line-loc* *infix-loc*)
     (cond ((setq n (last-line-feed-position x))
	    (if (> (- (length x) 1) n)
		(setq *infix-loc* (- (length x) 1 n))
		(setq *infix-loc* (get-margin))))
	   (t (incf *infix-loc* i)))
     (cond ((and *testing*
		 (> *infix-loc* *rightmost-char-number*))
	    (throw 'advise-break t)))))

(defmacro pprin1i (x)
  `(progn (let ((x ,x))
            (pprin1 x)
            (incf *infix-loc* (our-flatc x)))
          (cond ((and *testing*
                      (> *infix-loc* *rightmost-char-number*))
                 (throw 'advise-break t)))))

)

(defun newline (&optional force)
  (cond (*do-not-use-tabs* (pprinci " "))
	((null *tab-stack*) (newline-in-text force))
	(t (newline-in-env force))))

(defun to-current-margin ()
  (cond ((eql *infix-loc* (get-margin)) nil)
	(t (newline))))

(defun blankline (&optional force)
  (cond ((and (eql *infix-loc* (get-margin))
	      (eql *prev-line-loc* *infix-loc*)))
	((eql *infix-loc* (get-margin)) (newline force))
	(t (newline force) (newline force))))

(defvar *default-indent-spaces* 4)


;                    SIX GENERAL OPERATOR SCHEMAS

; The following make-... macros are used to generate functions and entries for
; the *fn-alist*.  See the end of this file for many examples of usage which can
; be easily extended.

(defun clean-up (fn)

; This function is supposed to remove completely all trace of any prior establishment
; of any syntax for the function symbol fn.

  (or (symbolp fn)
      (error (format nil "Illegal function symbol name: ~a." fn)))
  ;; DELTA !!!!
  (setf (get fn 'literalform) nil)
  (sloop for lst in '(*constant-ops* *infix-ops* *unary-prefix-ops* *unary-suffix-ops* *unary-abs-ops*)
           do  (set lst (remove fn (eval lst))))
  (sloop for alist in '(*fn-alist* *negative-constant-table* *negative-infix-table* *negative-unary-prefix-table*
                                     *negative-unary-suffix-table* *prefix-multiple-ops*
				     *suffix-multiple-ops*
                                     *infix-multiple-ops*)
           do  (set alist (sloop for pair in (eval alist)
                                   unless (eq fn (car pair))
                                   collect pair))))

;; Used to reinitialize during clean-up-everything
(defparameter *save-fn-alist* nil)

(defun clean-up-everything ()
  (sloop for alist in '(*fn-alist* *negative-constant-table*
				     *negative-infix-table*
				     *negative-unary-prefix-table*
                                     *negative-unary-suffix-table*
				     *prefix-multiple-ops*
				     *suffix-multiple-ops*
                                     *infix-multiple-ops*)
           do (progn
                (sloop for pair in (eval alist)
                         do (clean-up (car pair)))
                (set alist nil)))
  ;; Reinitialize
  (setq *fn-alist* *save-fn-alist*))

(defmacro make-constant-op (name str &optional neg-str)
  (let ((fn-name (intern (format nil "~s-constant-op-printer" name))))
    `(progn
       (clean-up ',name)
       (setf (get ',name 'literalform) ,(format nil *math-format* str))
       (defun ,fn-name
         (term)
         (declare (ignore term))
	 (pprinci ,(format nil *math-format* str)))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push ',name *constant-ops*)
       ,(cond (neg-str `(push (list ',name ',(format nil *math-format* neg-str))
                              *negative-constant-table*)))
       ',name)))

(defmacro make-infix-op (name str &optional neg-str)
  (let ((fn-name (intern (format nil "~s-infix-op-printer" name))))
    `(progn
       (clean-up ',name)
       (setf (get ',name 'literalform) ,(format nil *math-format* str))
       (defun ,fn-name
         (term)
         (default-infix-printer
           term
           ,(format nil *math-format* str)))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push ',name *infix-ops*)
       ,(cond (neg-str `(push (list ',name ',(format nil *math-format* neg-str))
                              *negative-infix-table*)))
       ',name)))

(defmacro make-infix-multiple-op (name &rest strs)
  (let ((fn-name (intern (format nil "~s-infix-multiple-op-printer" name))))
    `(progn
       (clean-up ',name)
       (defun ,fn-name
         (term)
         (default-infix-multiple-printer
           term
           ',(sloop for str in strs collect
                      (format nil *math-format* str))))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push (cons ',name ,(length strs)) *infix-multiple-ops*)
       ',name)))

(defmacro make-prefix-multiple-op (name &rest strs)
  (let ((fn-name (intern (format nil "~s-prefix-multiple-op-printer" name))))
    `(progn
       (clean-up ',name)
       (defun ,fn-name
         (term)
         (default-prefix-multiple-printer
           term
           ',(sloop for str in strs collect
                      (format nil *math-format* str))))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push (cons ',name ,(length strs)) *prefix-multiple-ops*)
       ',name)))

(defmacro make-suffix-multiple-op (name &rest strs)
  (let ((fn-name (intern (format nil "~s-prefix-multiple-op-printer" name))))
    `(progn
       (clean-up ',name)
       (defun ,fn-name
         (term)
         (default-suffix-multiple-printer
           term
           ',(sloop for str in strs collect
                      (format nil *math-format* str))))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push (cons ',name ,(length strs)) *suffix-multiple-ops*)
       ',name)))

(defmacro make-unary-prefix-op (name str &optional neg-str)
  (let ((fn-name (intern (format nil "~s-unary-prefix-op-printer" name))))
    `(progn
       (clean-up ',name)
       (defun ,fn-name
         (term)
         (default-unary-prefix-printer
           term
           ,(format nil *math-format* str)))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push ',name *unary-prefix-ops*)
       ,(cond (neg-str `(push (list ',name ',(format nil *math-format* neg-str))
                              *negative-unary-prefix-table*)))
       ',name)))

(defmacro make-unary-suffix-op (name str &optional neg-str)
  (let ((fn-name (intern (format nil "~s-unary-suffix-op-printer" name))))
    `(progn
       (clean-up ',name)
       (defun ,fn-name
         (term)
         (default-unary-suffix-printer
           term
           ,(format nil *math-format* str)))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push ',name *unary-suffix-ops*)
       ,(cond (neg-str `(push (list ',name ',(format nil *math-format* neg-str))
                              *negative-unary-suffix-table*)))
       ',name)))

(defmacro make-unary-abs-op (name lhs-str rhs-str)
  (let ((fn-name (intern (format nil "~s-unary-abs-op-printer" name))))
    `(progn
       (clean-up ',name)
       (defun ,fn-name
         (term)
         (default-unary-abs-printer
           term
           ,(concatenate 'string *math-begin* lhs-str)
           ,(concatenate 'string rhs-str *math-end*)))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push ',name *unary-abs-ops*)
       ',name)))

(defmacro declare-atom-printer (x v)
  `(let ((temp (assoc ',x *atom-alist*)))
     (if (null temp)
         (setq *atom-alist* (cons (list ',x ,v) *atom-alist*))
         (rplacd temp (list ,v)))))

(defmacro declare-fn-printer (x v)
  `(let ((temp (assoc ',x *fn-alist*)))
     (if (null temp)
         (setq *fn-alist* (cons (list ',x ,v) *fn-alist*))
         (rplacd temp (list ,v)))))

(defmacro declare-event-printer (x v)
  `(let ((temp (assoc ',x *event-printer-alist*)))
     (if (null temp)
         (setq *event-printer-alist* (cons (list ',x ,v) *event-printer-alist*))
         (rplacd temp (list ,v)))))

(defmacro declare-command-printer (x v)
  `(let ((temp (assoc ',x *event-printer-alist*)))
     (if (null temp)
         (setq *event-printer-alist* (cons (list ',x ,v) *event-printer-alist*))
         (rplacd temp (list ,v)))))

(defmacro def-atom-printer (x args body)
  (let ((printer (intern (concatenate 'string (symbol-pname x) "-atom-printer"))))
    `(let ((temp (assoc ',x *atom-alist*)))
       (defun ,printer ,args ,body)
       (if (null temp)
	   (setq *atom-alist* (cons (list ',x (function ,printer)) *atom-alist*))
         (rplacd temp (list (function ,printer)))))))

(defmacro def-fn-printer (x args body)
  (let ((printer (intern (concatenate 'string (symbol-pname x) "-fn-printer"))))
    `(let ((temp (assoc ',x *fn-alist*)))
       (defun ,printer ,args ,body)
       (if (null temp)
	   (setq *fn-alist* (cons (list ',x (function ,printer)) *fn-alist*))
         (rplacd temp (list (function ,printer)))))))

(defmacro def-event-printer (x args body)
  (let ((printer (intern (concatenate 'string (symbol-pname x) "-event-printer"))))
    `(let ((temp (assoc ',x *event-printer-alist*)))
       (defun ,printer ,args ,body)
       (if (null temp)
	   (setq *event-printer-alist*
		 (cons (list ',x (function ,printer)) *event-printer-alist*))
         (rplacd temp (list (function ,printer)))))))


;                                    TABBING

; Infix-File generates text that uses the Latex `tabbing' or Scribe `format' environment,
; setting a tab for each new level of indentation.  We find this a convenient
; sublanguage to target.

; It appears based upon various experiment that perhaps Latex cannot handle tabs
; more than about 14 deep, or so.

; The parameter, *latex-indent-number-limit*, could perhaps be increased if one
; had a Latex wherein this limit has been raised.  However, it is a relatively rare
; function that needs terms that are more than 13 function calls deep.  When
; infix-file hits this limit in Latex mode, it falls back upon the standard Acl2
; pretty-printer, and puts the result in a verbatim environment.

;; All of the following should be defined in the text-formatting init file,
;; e.g., latex-init.lisp or scribe-init.lisp.

(proclaim '(ftype (function nil t)
                  begin-tabbing		;enter a tabbing environment
		  begin-group-tabbing	;enter a tabbing environment, no page breaks
                  end-tabbing		;exit tabbing env
		  begin-normal-text	;
		  end-normal-text
		  increase-margin	;increment left margin by a fixed amount
                  set-margin		;set margin to current line location
                  pop-margin		;pop to previous margin
                  get-margin		;value
                  set-tab		;set at tab at current line location
                  pop-tab		;remove a tab
                  do-tab		;tab to next tab
		  begin-flushright
		  end-flushright
                  ;; to-current-margin
		  ;; newline-to-current-margin ;
		  ;; force-newline
		  ))

(proclaim '(ftype (function (t) t)
		  flushright))

(proclaim '(ftype (function (&optional t) t)
                  set-tab))

(proclaim '(ftype (function (character) t)
                  handle-special-chars
                  handle-special-chars-in-string char))


;                                  PRINT-ATOM

; We want to slashify special characters in the following three lists in
; case they appear in an Acl2 symbol.  Used only by print-atom and index.

(defparameter doc-special-chars  nil)
(defparameter doc-other-chars    nil)
(defparameter doc-index-specials nil)

; We also to handle the characters in doc-other-chars specially, by going into
; math mode, since slashification with backslash does not work.

(defun print-string (str &optional i)

; Our own printer, which slashifies (or otherwise quotes) the doc-special-chars and
; doc-other-chars in strings.  We print all Acl2 symbols with this
; function and print-atom because we want to avoid generating stuff that will make
; the text formatter barf, e.g., in Latex, a symbol with an unslashified $, <, or { in it.

  (cond ((stringp str)
         (sloop for j below (length (the string str))
                  for char = (char (the string str) (the fixnum j))
                  do  (handle-special-chars-in-string char)
                  finally (incf *infix-loc* (or i (length str)))))
        ((symbolp str)
         (print-atom str i))
	((characterp str) (print-character str i))
        (t (pprin1i str)))
  (cond ((and *testing*
              (> *infix-loc* *rightmost-char-number*))
         (throw 'advise-break t))))

(defun print-atom (atm &optional i)

; Our own atom printer, which slashifies (or otherwise quotes) the doc-special-chars and
; doc-other-chars in symbols and strings.  We print all Acl2 symbols with this
; function because we want to avoid generating stuff that will make the text formatter barf,
; e.g., in Latex, a symbol with an unslashified $, <, or { in it.
; If i is present is is meant to be the actual printed width of the formatted output, e.g.
; stripped of formatting commands.

  (cond ((symbolp atm)
	 (if (keywordp atm)
	     (pprinc ":"))
         (sloop with str = (symbol-name atm)
                  for j below (length (symbol-name (the symbol atm)))
                  for char = (char (the string str) (the fixnum j))
                  do  (handle-special-chars char)
                  finally (incf *infix-loc* (or i (length str)))))
        ((stringp atm)
         (incf *infix-loc* (or i (+ 4 (* 2 (length atm)))))
         (pprinc *begin-string-env*)	;was *begin-tt-env*
         (pprinc "\"")
         (sloop for i below (length atm)
                  for char = (char (the string atm) (the fixnum i))
                  do  (handle-special-chars-in-string char))
         (pprinc "\"")
         (pprinc *end-string-env*))
        (t (pprin1i atm)))
  (cond ((and *testing*
              (> *infix-loc* *rightmost-char-number*))
         (throw 'advise-break t))))

(defun print-character (c &optional i)

; Our own character printer, quotes the doc-special-chars and
; doc-other-chars used to print characters.  We print all Acl2 characters with this
; function because we want to avoid generating stuff that will make the text formatter barf,
; e.g., in Latex, a symbol with an unslashified $, <, or { in it.
; If i is present is is meant to be the actual printed width of the formatted output, e.g.
; stripped of formatting commands.

  (handle-special-chars #\#)
  (handle-special-chars #\\)
  (handle-special-chars c)
  (incf *infix-loc* (or i 3))
  (cond ((and *testing*
              (> *infix-loc* *rightmost-char-number*))
         (throw 'advise-break t))))

(defun print-atoms (l)
  (cond ((cdr l)
	 (sloop for x on l
		do (cond ((cddr x)
			  (print-atom (car x))
			  (pprinc ", "))
			 ((cdr x)
			  (print-atom (car x))
			  (pprinc " and "))
			 (t (print-atom (car x))))))
	(t (print-atom (car l)))))

(defun print-bare-function-name (term)
  (pprinc "`")
  (print-atom term)
  (pprinc "'"))

(defun print-bare-function-names (l)
  (cond ((cdr l)
	 (sloop for x on l
		do (cond ((cddr x)
			  (print-bare-function-name (car x))
			  (pprinc ", "))
			 ((cdr x)
			  (print-bare-function-name (car x))
			  (pprinc " and "))
			 (t (print-bare-function-name (car x))))))
	(t (print-bare-function-name (car l)))))


;                             FONT SYMBOL PRINTERS

(defun bold-sym-printer (x &optional i)         ; Print in bold face.
  (pprinc *begin-bold-env*)
  (cond ((symbolp x) (print-atom x i))
	((characterp x) (print-character x i))
	(t (print-string x i)))
  (pprinc *end-bold-env*))

(defun italic-sym-printer (x &optional i)               ; Print in italic face.
  (pprinc *begin-italic-env*)
  (cond ((symbolp x)    (print-atom x i))
	((characterp x) (print-character x i))
	(t (print-string x i)))
  (pprinc *end-italic-env*))

(defun tt-sym-printer (x &optional i)           ; Print in typewriter font.
  (pprinc *begin-tt-env*)
  (cond ((symbolp x) (print-atom x i))
	((characterp x) (print-character x i))
	(t (print-string x i)))
  ;; We charge more for tt characters.
  (incf *infix-loc* (* (- *tt-size* 1) (our-flatc x)))
  (pprinc *end-tt-env*))

(defun small-caps-sym-printer (x &optional i)           ; Print in small caps.
  (pprinc *begin-sc-env*)
  (cond ((symbolp x) (print-atom x i))
	((characterp x) (print-character x i))
	(t (print-string x i)))
  (pprinc *end-sc-env*))

(defun font-sym-printer (symbol font)
  (case font
    (bold   (bold-sym-printer symbol))
    (italic (italic-sym-printer symbol))
    (tt     (tt-sym-printer symbol))
    (sc     (small-caps-sym-printer symbol))
    (otherwise (format *terminal-io* "Bad font descriptor (~a) passed to subscript printer.~%" font)
               (tt-sym-printer symbol))))

(defun subscript (x)
  (pprinc *begin-subscript*)
  (print-atom x)
  (pprinc *end-subscript*))

;                                   *ATOM-ALIST*

; *atom-alist* is one of the three tables off of which this printer is driven.
; It determines how a variable symbol is printed.  It is unlikely that anyone
; would want to change this unless translate changes because t, f, and nil are
; the only symbols that translate treats specially as constants instead of as
; variable symbols.

; We would like to put this at the beginning of the file but cannot, so we put
; a special declaration up there.

(defparameter *atom-alist*
  (list (list 't   (function bold-sym-printer))
        (list 'f   (function bold-sym-printer))
        (list 'nil (function bold-sym-printer))))

(defun default-atom-printer (var)

; We put variables in italics, strings in typewriter.

  (cond ((keywordp var) (print-atom var))
	((symbolp var)  (italic-sym-printer var))
        ((stringp var)  (print-atom var))
        ((numberp var)  (tt-sym-printer var))
	((characterp var) (print-character var))
        (t (pprin1 var))))

(defun get-atom-printer (sym)
  (let ((a (assoc sym *atom-alist*)))
    (cond (a (cadr a))
          (t (function default-atom-printer)))))


;                                     QUOTE

; The printing of quote terms is intrinsically intertwined with the printing of
; backquoted terms.  The backquoted terms have been read with our
; special-to-infix-file backquote reader.

(defun quote-printer1 (term)

; How we output a quoted term.

  (cond ((stringp term)                       (print-atom term))
	((atom term)
	 (tt-sym-printer term))
        ((eq (car term) 'quote)
         (quote-printer term))
        ((eq (car term) *infix-comma*)
         (comma-printer term))
        ((eq (car term) *infix-comma-atsign*)
         (comma-atsign-printer term))
        ((eq (car term) *infix-backquote*)
         (backquote-printer term))
        ((eq (car term) *infix-radix*)
         (funcall (function *infix-radix*-printer) term))
        ((advise-break (list 'quote term))
         (quote-printer1-advise-break term))
        (t (quote-printer1-tt-form term))))

(defun tt-pprinci (term &optional (size 1))
  (pprinci *begin-tt-env* size)
  (pprinci term size)
  (pprinci *end-tt-env*))

(defun quote-printer1-tt-form (term)
  (tt-pprinci "(" *tt-size*)
  (sloop for tail on term do
           (progn (quote-printer1 (car tail))
                  (cond ((null (cdr tail)) (tt-pprinci ")" *tt-size*))
                        ((or (atom (cdr tail))
                             (eq (car (cdr tail)) *infix-comma*)
                             (eq (car (cdr tail)) *infix-comma-atsign*)
                             (eq (car (cdr tail)) *infix-backquote*))
                         (tt-pprinci *dotted-pair-separator*  4)
                         (quote-printer1 (cdr tail))
                         (tt-pprinci ")" *tt-size*)
                         (line-return))
                        (t (tt-pprinci " " *tt-size*))))
           until (atom (cdr tail))))

(defun quote-printer1-advise-break (term)
  (tt-pprinci "(" *tt-size*)
  (set-margin)
  ;; (let ((*left-margin-tab-context* nil)) )
  (sloop for tail on term
           do (progn (quote-printer1 (car tail))
                     (cond ((null (cdr tail))
                            (tt-pprinci ")" *tt-size*))
                           ((or (atom (cdr tail))
                                (eq (car (cdr tail)) *infix-comma*)
                                (eq (car (cdr tail)) *infix-comma-atsign*)
                                (eq (car (cdr tail)) *infix-backquote*))
                            (to-current-margin)	;newline
                            (tt-pprinci *dotted-pair-separator-newline* 4)
                            (quote-printer1 (cdr tail))
                            (tt-pprinci ")" *tt-size*)
                            (return nil))
                           ((and (or (atom (car tail)) (eq *infix-radix* (car (car tail))))
                                 (cdr tail)
                                 (or (atom (cadr tail)) (eq *infix-radix* (car (cadr tail))))
                                 (not (advise-break (list 'quote (cadr tail)))))
                            (tt-pprinci " " *tt-size*))
                           (t (to-current-margin)))) ;newline
           until (atom (cdr tail)))
  (pop-margin))

(defun pending-printer (term)
  (declare (ignore term))
  (italic-sym-printer "pending"))

(defvar *special-quoted-forms-alist*
  (list (cons 'pending (function pending-printer))))

(defun quote-printer (term)
  (let ((fun (cdr (assoc (cadr term) *special-quoted-forms-alist*))))
    (if fun
	(funcall fun (list (cadr term)))
	(progn (tt-pprinci "'" *tt-size*)
	       (quote-printer1 (cadr term))))))

(defun backquote-printer (term)
  (tt-pprinci "`" *tt-size*)
  (quote-printer1 (cadr term)))

(defun comma-printer (term)
  (tt-pprinci "," *tt-size*)
  (quote-printer1 (cadr term)))

(defun comma-atsign-printer (term)
  (tt-pprinci *comma-atsign* 4)
  (quote-printer1 (cadr term)))


;; NEED to have read, read in the user package, where all of our
;; variables are compiled!.  So use readx.

(defun readx (str a b c)
  (let ((*package* *user-package*))
    (let ((val (read str a b c)))
      (if (acl2-keywordp val)
	  (read-keyword-command val)
	  val))))

(defun read-from-stringx (str)
  (let ((*package* *user-package*))
    (read-from-string str)))


; We arrange to read #b, #o, and #x syntax preserving what was read and to
; print it in the conventional notation whereby #o10 comes out as

;      10
;        8

; We do this by having READ fake numbers into the parse tree looking like
; function calls of the function whose name is the uninterned symbol that is
; the value of *infix-radix*, and by supplying a printer for this symbol.

; The 6 read macros for this syntax:

(defun smash-infix-readtable ()
  (sloop for c in '(#\B #\b #\O #\o #\X #\x)
           as n in '(2 2 8 8 16 16)
           for l = (case n
                         (2 '(#\0 #\1))
                         (8 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7))
                         (16 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9
                               #\A #\B #\C #\D #\E #\F
                               #\a #\b #\c #\d #\e #\f)))
           do
           (set-dispatch-macro-character
            #\#
            c
            (let ((l l)
                  (nn n)
                  (arithmetic-signs '(#\+ #\- #\/)))
              (function (lambda (stream char n)
                          (declare (ignore char n))
                          (list* *infix-radix* nn
                                 (sloop for ch = (read-char stream)
                                          with ll = nil
                                          do
                                          (cond ((or (member ch l)
                                                     (member ch arithmetic-signs))
                                                 (push ch ll))
                                                (t (unread-char ch stream)
                                                   (return (nreverse ll)))))))))))

; Also setup the backquote reader.

  (set-macro-character #\`
    #'(lambda (stream char)
       (declare (ignore char))
       (list *infix-backquote* (readx stream t nil t))))
  (set-macro-character #\,
   #'(lambda (stream char)
       (declare (ignore char))
       (case (peek-char nil stream t nil t)
             ((#\@ #\.)
              (read-char stream)
              (list *infix-comma-atsign* (readx stream t nil t)))
             (t (list *infix-comma* (readx stream t nil t)))))))

(defun *infix-radix*-printer (term)
  (pprinc *math-begin*)
  (pprinc *begin-tt-env*)
  (sloop for ch in (cddr term) do (pprinc ch))
  (pprinc *end*)
  (pprinc *subscript*)                  ; "}_{"
  (pprinc *begin*)
  (pprin1i (cadr term))
  (pprinc *end-tt-env*)
  (pprinc *math-end*))

(defun subscript-printer (symbol subscript &optional (font 'tt))
  ;; Font must be one of bold, italic, tt, sc (small caps)
  (pprinc *math-begin*)
  (font-sym-printer symbol font)
  (pprinc *subscript*)                  ; "_" in latex
  (pprinc *begin*)
  (font-sym-printer subscript font)
  (pprinc *end*)
  (pprinc *math-end*))

;; FROM NQTHM

(eval-when (load compile eval)

(defmacro match (term pattern) (match-macro term pattern))

(defun match-macro (term pat)
  (cond ((atom term)
         (match1-macro term pat))
        (t (let ((sym (gensym "match")))
             `(let ((,sym ,term))
                ,(match1-macro sym pat))))))

(defvar setq-lst nil)
(defvar test-lst nil)

(defun match1-macro (term pat)
  (let (test-lst setq-lst)
    (match2-macro term pat)
    (list (quote cond)
          (cons
           (cond ((null test-lst) t)
                 ((null (cdr test-lst)) (car test-lst))
                 (t (cons (quote and) test-lst)))
           (nconc setq-lst (list t))))))

(defun match2-macro (term pat)
  (cond ((atom pat)
         (cond ((eq pat (quote &)) nil)
               ((or (eq pat t) (eq pat nil))
                (error "attempt to smash t or nil."))
               ((symbolp pat)
                (setq setq-lst (nconc setq-lst (list (list (quote setq) pat term)))))
               (t (setq test-lst
                        (nconc test-lst (list (list (quote equal) pat term)))))))
        ((eq (quote cons) (car pat))
         (setq test-lst (nconc test-lst (list (list (quote consp) term))))
         (match2-macro (list (quote car) term) (cadr pat))
         (match2-macro (list (quote cdr) term) (caddr pat)))
        ((eq (quote quote) (car pat))
         (cond ((symbolp (cadr pat))
                (setq test-lst
                      (nconc test-lst
                              (list (list (quote eq)
                                    (list (quote quote) (cadr pat)) term)))))
               (t (setq test-lst (nconc test-lst
                                         (list (list (quote equal)
                                               (list (quote quote) (cadr pat))
                                               term)))))))
        (t (cond ((not (eq (quote list) (car pat)))
                  (setq pat (cons (quote list)
                                  (cons (list (quote quote) (car pat))
                                        (cdr pat))))))
           (sloop for subpat in (cdr pat) do
                    (progn (setq test-lst
                                 (nconc test-lst (list (list (quote consp) term))))
                           (match2-macro (list (quote car) term) subpat)
                           (setq term (list (quote cdr) term))))
           (setq test-lst (nconc test-lst (list (list (quote eq) term nil)))))))

)

;; END NQTHM importation


; A FEW HAND-CODED FORM PRINTERS:  IF, COND, CASE, LET, FOR, FORALL and EXISTS.

(defun math-space (&optional (n 1))
  (cond (*do-not-use-tabs* (setq n 1)))
  (pprinc *math-begin*)
  (sloop for i from 1 to n do
           (pprinci *math-thick-space*))
  (pprinc *math-end*))

(defun math-thin-space (&optional (n 1))
  (cond (*do-not-use-tabs* (setq n 1)))
  (pprinc *math-begin*)
  (sloop for i from 1 to n do
           (pprinci *math-thin-space*))
  (pprinc *math-end*))

(defun condify (term)
  (let (x u v)
    (sloop with pairs
             while (match term (if x u v))
             do (progn (push (list x u) pairs)         ; ??? I put the push and setq into a PROGN ???
                       (setq term v))
             finally
             (progn (push (list t term) pairs)
                    (return (cons 'cond (reverse pairs)))))))

(defun if-printer (term)
  (cond ((null (cddr term))
         (format *terminal-io* "~%Ill formed if-expression - ~a~%" term)
         (cond-printer (condify (append term '(nil nil)))))
        ((null (cdddr term))
         (format *terminal-io* "~%Ill formed if-expression - ~a~%" term)
         (cond-printer (condify (append term '(nil)))))
        (t (cond-printer (condify term)))))

; We take the attitude that we can print an untranslated term t as we would
; print an untranslated term t' provided that t and t' translate to the same
; term.  This point of view is to be found expressed in our treatment of nested
; if's as though they were conds.

(defun cond-printer (term)
  (let (some-line-broken)
    (advise-break-if-testing)
    (let ((*top-parens-eliminable* t))
      (cond ((null (cddr term))
	     (infix-print-term1 (cadr (cadr term))))
	    (t (let ((cases (cdr term))
		     (first-case (car (cdr term))))
		 (set-margin)
		 ;; (let ((*left-margin-tab-context* nil))  )
		 (bold-sym-printer "if " 3)
		 (infix-print-term1 (car first-case))
		 ;; then
		 (cond ((let ((*rightmost-char-number* (- *rightmost-char-number* 7)))
			  (advise-break (cadr first-case)))
			(setq some-line-broken t)
			(to-current-margin)) ;newline-
		       (t (math-space 1)))
		 (bold-sym-printer " then " 5)
		 (infix-print-term1 (cadr first-case))
		 ;; else
		 (cond ((let ((*rightmost-char-number* (- *rightmost-char-number* 7)))
			  (advise-break (cons 'cond (cdr cases))))
			(setq some-line-broken t)
			(to-current-margin)) ;newline-
		       (t (math-space 1)))
		 ;;
		 (sloop for tail on (cdr cases) do
                        (cond ((null (cdr tail))
                               (bold-sym-printer " else " 5)
                               (let ((*rightmost-char-number* (- *rightmost-char-number* 6)))
                                 (infix-print-term1 (cadr (car tail))))
			       ;; TESTING.  Inserted (math-space 1) and deleted the following
			       ;; Switched back, using to-current-margin.
			       (if some-line-broken
				   (to-current-margin)
				   (math-space 1))
                               (bold-sym-printer "fi" 3)
			       (pop-margin))
                              (t (bold-sym-printer " elseif " 7)
                                 (infix-print-term1 (caar tail))
                                 (cond ((let ((*rightmost-char-number*
					       (- *rightmost-char-number* 7)))
                                          (advise-break (cadar tail)))
					(setq some-line-broken t)
                                        (to-current-margin)) ;newline
                                       (t (math-space 1)))
                                 (bold-sym-printer " then " 5)
                                 (infix-print-term1 (cadar tail))
                                 (to-current-margin)))))))))) ;newline

(defun print-one-case (case term)
  (let ((break (advise-break term)))
    (bold-sym-printer " case = " 7)
    ;; Was (infix-print-term1 case)
    (quote-printer1 case)
    (bold-sym-printer " then " 5)
    (if break
	(progn (to-current-margin) (math-space 5) (set-margin))	;newline
      (math-space 1))
    (infix-print-term1 term)
    (if break (pop-margin))
    (to-current-margin)))		;newline

(defun case-printer (term)
  (advise-break-if-testing)
  (let ((*top-parens-eliminable* t))
    (cond ((null (cdddr term))
           (infix-print-term1 (cadr (caddr term))))
          (t (let ((cases (cddr term))
                   (first-case (car (cddr term))))
               (set-margin)
               ;; (let ((*left-margin-tab-context* nil))   ... )
               (bold-sym-printer "case on " 9)
               (infix-print-term1 (cadr term))
               (pprinci ":")
               (to-current-margin)	;newline
	       (pprinci "  " 2)
               (set-margin)
	       (print-one-case (car first-case) (cadr first-case))
               (sloop for tail on (cdr cases) do
		      (cond ((null (cdr tail))
			     (bold-sym-printer " otherwise " 10)
			     (infix-print-term1 (cadr (car tail)))
			     (to-current-margin)
			     ;; (math-space 1)
			     ;; Was imbedded in
			     ;; (let((*rightmost-char-number* (- *rightmost-char-number* 8)))
			     ;;    <form>)
			     (bold-sym-printer "endcase" 8)
			     (pop-margin))
			    (t (print-one-case (caar tail) (cadar tail)))))
	       (pop-margin))))))

(defun let-printer (term)
  (advise-break-if-testing)
  (let ((*top-parens-eliminable* t))
    (cond ((null (cadr term))
           (infix-print-term1 (caddr term)))
          (t (let ((lets (cadr term)))
               (set-margin)
               ;; (let ((*left-margin-tab-context* nil)) .. )
               (bold-sym-printer "let " 5)
               (set-margin)
	       ;; Symbolp lets => lets = NIL.  Deleted (infix-print-term1 lets))
               (if (consp lets)
		   (sloop for tail on lets
			  for let = (car tail)
			  do (progn (infix-print-term1 (car let))
				    (bold-sym-printer " be " 3)
				    (infix-print-term1 (cadr let))
				    (cond ((cdr tail)
					   (pprinci ", " 1)
					   (to-current-margin))
					  (t (to-current-margin)
					     (bold-sym-printer " in " 3))))))
	       ;; Deleted (to-current-margin) after printing " in "
	       (pop-margin)
	       (to-current-margin)
               (let ((*rightmost-char-number* (- *rightmost-char-number* 7)))
                 (infix-print-term1 (caddr term)))
               (pop-margin))))))

(defun let*-printer (term)
  (advise-break-if-testing)
  (let ((*top-parens-eliminable* t))
    (cond ((null (cadr term))
           (infix-print-term1 (caddr term)))
          (t (let ((lets (cadr term)))
               (set-margin)
               ;; (let ((*left-margin-tab-context* nil)) .. )
               (bold-sym-printer "let* " 5)
               (set-margin)
               (if (consp lets)
		   (sloop for tail on lets
			  for let = (car tail)
			  do (progn (infix-print-term1 (car let))
				    (bold-sym-printer " be " 3)
				    (infix-print-term1 (cadr let))
				    (cond ((cdr tail)
					   (pprinci ", " 1)
					   (to-current-margin)) ;newline
					  (t (to-current-margin)
					     (bold-sym-printer " in " 3)))
				    )))
	       (pop-margin)
	       (to-current-margin)
               (let ((*rightmost-char-number* (- *rightmost-char-number* 7)))
                 (infix-print-term1 (caddr term)))
               (pop-margin))))))

(defun mv-printer (term)
  (mv-printer1 (cdr term)))

(defparameter *mv-bracket-left* "")
(defparameter *mv-bracket-right* "")

(defun mv-printer1 (vars)
  (pprinc *mv-bracket-left*)
  (sloop for tail on vars do
	 (progn
	   (if (symbolp (car tail))
	       (funcall (get-atom-printer (car tail)) (car tail))
	       (infix-print-term1 (car tail)))
	   (if (cdr tail) (pprinci ", " *tt-size*))))
  (pprinc *mv-bracket-right*))

(defun assign-printer (vars term)
  (cond ((atom vars)
	 (funcall (get-atom-printer vars) vars))
	(t (mv-printer1 vars)))
  (math-space 1)
  (pprinc ":=")
  (math-space 1)
  (infix-print-term1 term)
  (pprinc ";"))

(defun mv-let-printer (term)
  ;; (mv-let (arg1 ... argn) form form)
  (advise-break-if-testing)
  (let ((*top-parens-eliminable* t)
	(vars (cadr term))
	(value (caddr term))
	(form (cadddr term)))
    (set-margin)
    (assign-printer vars value)
    ;; newline(to-current-margin)
    (to-current-margin)
    (infix-print-term form)
    (pop-margin)))

(defun make-alist-pairlist (l)
  (if (not (consp l))
      l
      (cons (list (caar l) (cdar l))
            (make-alist-pairlist (cdr l)))))


;                                   *FN-ALIST*

; *fn-alist* is considerably extended via calls to make-... at the end of this
; file.  This initial value given here picks up the very few entries for which
; we have totally ad hoc handling.  Although LIST and LIST* are essentially
; macros, we handle them by the default-fn-printer, since they evaluate all
; their arguments.  We could have handled IF this default way, too.  It was
; essential that we handle QUOTE, COND, CASE, LET, and FOR specially because
; they do not evaluate all their arguments but `parse' them to some extent.

; We would like to put this at the top but have to put it after the functions
; are defined.

(defparameter *fn-alist*
  (list (list 'quote (function quote-printer))
        (list *infix-backquote* (function backquote-printer))
        (list *infix-radix* (function *infix-radix*-printer))
        (list 'if    (function if-printer))
        (list 'let   (function let-printer))
        (list 'let*  (function let*-printer))
        (list 'mv     (function mv-printer))
        (list 'mv-let (function mv-let-printer))
        (list 'cond  (function cond-printer))
        (list 'case  (function case-printer))))

(defun default-fn-printer (term)

; This function is a good function to study if one finds it necessary to define
; by hand a special handler for a function symbol.  We annotate rather
; verbosely as a pedagogical device.

; In general, we know that term is a lisp object on which TRANSLATE does not
; cause an error.

; Binding *top-parens-eliminable* is a sign to the infix, prefix, and suffix
; operators immediately below that we are putting out syntactic noise (e.g.,
; commas) that is so strong that they need not emit an initial outer layer of
; parentheses.

  (let ((*top-parens-eliminable* t)
        (advice (advise-break term)))

    (cond ((atom (car term))

; First put out the function symbol, in roman.
; Functions of no arguments are printed as constants, without parentheses,
; rather than with, e.g., foo().

           (cond ((null (cdr term))
                  (roman-font (car term))
                  (return-from default-fn-printer nil)))

; We want a very tiny space in front of the open parenthesis because otherwise,
; it looks like some function symbols touch the open parenthesis.  In some
; cases, this results in a touch more space than we like, and perhaps there
; exists a more delicate kerning command.

           (roman-font (car term))
           (math-thin-space)
           (pprinci "("))
          (t (pprinci "(")
             (setq term (cons 'foo term))))
    (cond ((null (cdr term))
           (pprinci ")"))
          ((null (cddr term))
           (infix-print-term1 (cadr term))
           (pprinci ")"))

; The coder of the printer for each function should consider whether to print
; flat or not, by calling advise-break.  This is a somewhat aesthetic and
; heuristic decision.

          (advice

; If it is decided not to print flat, one needs somewhere early to set a tab
; stop to which to return.

           (set-margin)
           ;; (let ((*left-margin-tab-context* nil)) .. )
           (sloop for tail on (cdr term)
                    do (progn (infix-print-term1 (car tail))
                              (cond ((cdr tail)
                                     (pprinci ",")
                                     ;; Each call of newline-to-current-magin will
                                     ;; return to the indent we set.
                                     (to-current-margin)) ;newline
                                    (t
                                     (pprinci ")")
                                     ;; Now we get rid of the indent.
                                     (pop-margin))))))
          (t (sloop for tail on (cdr term)
		      do (progn
			   (cond ((keywordp (car tail))
				  (infix-print-keyword-value-pair (car tail) (cadr tail))
				  (setq tail (cdr tail)))
				 (t (infix-print-term1 (car tail))))
			   (cond ((cdr tail)
				  (pprinci ", "))
				 (t (pprinci ")")))))))))

(defun infix-print-keyword-value-pair (key value)
  (infix-print-term1 (list 'assign (symbol-name key) value)))

(defun get-fn-printer (sym)
  (or (symbolp sym)
      (error (format nil "Illegal object where function symbol expected : ~a." sym)))
  (let ((a (assoc sym *fn-alist*)))
    (cond (a (cadr a))
          (t (function default-fn-printer)))))

(defun defun-call-part-printer (term)
  (let ((*top-parens-eliminable* t)
        (advice (advise-break term)))
    (cond ((atom (car term))

; First put out the function symbol, in roman.
; Functions of no arguments are printed as constants, without parentheses,
; rather than with, e.g., foo().

           (cond ((null (cdr term))
                  (roman-font (car term))
                  (return-from defun-call-part-printer nil)))

; We want a very tiny space in front of the open parenthesis because otherwise,
; it looks like some function symbols touch the open parenthesis.  In some
; cases, this results in a touch more space than we like, and perhaps there
; exists a more delicate kerning command.

           (roman-font (car term))
           (math-thin-space)
           (pprinci "("))
          (t (pprinci "(")
             (setq term (cons 'foo term))))
    (cond ((null (cdr term))
           (pprinci ")"))
          ((null (cddr term))
	   ;; infix-print-arg takes a list of args and prints the first.
	   ;; This allows it to handle &optional.
           (infix-print-args (cdr term))
           (pprinci ")"))

; The coder of the printer for each function should consider whether to print
; flat or not, by calling advise-break.  This is a somewhat aesthetic and
; heuristic decision.

          (advice

; If it is decided not to print flat, one needs somewhere early to set a tab
; stop to which to return.

           (set-margin)
	   (infix-print-args (cdr term) t)
	   (pprinci ")")
	   (pop-margin))
          (t (infix-print-args (cdr term))
	     (pprinci ")")))))


;                                    BREAKS

(defun advise-break (term)

; advise-break is the only place that *testing* is bound, and here it is bound
; to t, meaning that we want no printing, just want to know if we can print
; term flat.  We also bind, just to restore, the current *infix-loc* and
; *tab-list*.

; This first cond is only for debugging purposes.  Same for the second value
; of the prog1.

  (cond (*tracing-advise-break*
         (format *terminal-io* "~%Entering *infix-loc* = ~a, *testing* = ~a~%" *infix-loc* *testing*)))
  (prog1
      (let ((*infix-loc* *infix-loc*)
            (*tab-list* *tab-list*))
        (cond (*testing* nil)
	      (t (catch 'advise-break
                   (let ((*testing* t))
                     (infix-print-term1 term)
                     nil)))))
    (cond (*tracing-advise-break*
           (format *terminal-io* "~%Exiting *infix-loc* = ~a~%" *infix-loc*)))))

;; Next 3 from Nqthm.
(defparameter *extra-propertyless-symbols-alist* nil)

(defun propertyless-symbolp (x)
  (or (car-cdrp x)
      (member x (quote (nil quote list let case cond t f
                               list*)))
      (assoc x *extra-propertyless-symbols-alist*)))

(defun car-cdrp (x)
  (let ((str (symbol-name x)))
    (cond ((and (> (length str) 2)
                (eql (aref str 0) #\c)
                (eql (aref str (1- (length str))) #\r)
                (sloop for i from 1 to  (- (length str) 2)
                         always (or (eql (aref str i) #\a)
                                    (eql (aref str i) #\d))))
           (sloop for i downfrom (- (length str) 2) to 1 collect
                    (aref str i)))
          (t nil))))

(defun advise-break-if-testing ()

; A printer function that is sure that it will break should short circuit the
; expense of calculating whether printing flat is ok.

  (cond (*testing*
         (throw 'advise-break t))))

(defun do-not-index-call-of (fn)
  (or *do-not-index*
      *do-not-index-calls*
      (propertyless-symbolp fn)
      ;; (eq 'ground-zero (get fn 'main-event))
      (get fn '*predefined*)		;seems appropriate for Acl2.
      (member fn *do-not-index-calls-of*)))

(defun index-call (fn)
  (cond (*testing* nil)
        ((do-not-index-call-of fn) nil)
        (t (index fn))))

(defun index-event (fn)
  (cond (*testing* nil)
	(*do-not-index* nil)
        ((do-not-index-event-of fn) nil)
        (t (index fn))))

(defun infix-print-term1 (term)
  (cond ((atom term)
         (funcall (get-atom-printer term) term))
	((consp (car term))
	 (sloop for x in term do (infix-print-term1 x)))
	((not (symbolp (car term)))
	 (sloop for x in term do (infix-print-term1 x)))
        (t (funcall (get-fn-printer (car term))
                    term)
           (index-call (car term)))))

(defun infix-print-term (term)
  (newline)
  (infix-print-term1 term)
  (newline)
  nil)

(defun infix-print-list-element-newline (term &optional trailer)
  ;; TRAILER, if present, must be a string.
  (infix-print-term1 term)
  (if trailer (pprinc trailer))
  (newline)
  nil)

(defun infix-print-list-element (term &optional trailer)
  ;; TRAILER, if present, must be a string.
  (infix-print-term1 term)
  (if trailer (pprinc trailer))
  nil)

(defun infix-print-list1 (l)
  (set-margin)
  (sloop for tail on l
	 do (cond ((consp tail)
		   (infix-print-term1 (car tail))
		   (if (cdr tail) (pprinci ", ")))
		  (t (pprinci " . " (infix-print-term1 tail)))))
  ;; Now we get rid of the indent.
  (pop-margin))

(defun infix-print-list-a (l &optional printer)
  (set-margin)
  (sloop for tail on l
	 do (cond ((consp tail)
		   (if printer
		       (funcall printer (car tail))
		       (infix-print-term1 (car tail)))
		   (if (cdr tail) (pprinci ", ")))
		  (t (pprinci " . ")
		     (if printer
			 (funcall printer tail)
			 (infix-print-term1 tail)))))
  ;; Now we get rid of the indent.
  (pop-margin))

(defun infix-print-list (l)
  (set-margin)
  (newline)
  (sloop for tail on l
	 do (cond ((consp tail)
		   ;; Issues newline at end of call.
		   (infix-print-list-element-newline (car tail) (if (cdr tail) ", "))
		   (cond ((and (cdr tail) (not (consp tail)))
			  (pprinci " . ")
			  (infix-print-list-element-newline (cdr tail))
			  (loop-return nil))))
		  ;; Should never get to this.  Sloop doesn't deal with
		  ;; non-consp cdrs.
		  (t (pprinci " . ") (infix-print-list-element-newline tail))))
  ;; Now we get rid of the indent.
  (pop-margin))

(defun infix-print-l (l &optional printer)
  (let ((advice (advise-break l)))
    (if (null printer)
	(if advice
	    (setq printer (function infix-print-list-element-newline))
	    (setq printer (function infix-print-list-element))))
    (set-margin)
    (newline)
    ;; NEED L TO BE A PROPER LIST.
    (sloop for tail on l
	   do (cond ((consp tail)
		     ;; Issues newline at end of call.
		     (funcall printer (car tail)
			      (if (and (cdr tail) (consp (cdr tail)))
				  ", "
				  nil))
		     (if (and (cdr tail) (not (consp (cdr tail))))
			 (progn (pprinci " . ")
				(funcall printer (cdr tail))
				(loop-return nil))))
		    (t nil)))
    ;; Now we get rid of the indent.
    (pop-margin)))

;;   &optional var || &optional (var [literal [varp]])
;;   &rest v
;;   &key foo bar
;;   &whole l
;;   &body l
;;   &allow-other-keys

(defvar infix-lambda-list-keywords '(&optional &rest &key &whole &body &allow-other-keys))

(defun infix-print-args (l &optional terpri-flag)
  ;; Whether the args will fit was decided by the caller.
  ;; If not, terpri-flag is T and we emit a newline between args.
  ;; Margin is set at current position.
  (sloop for tail on l
	 do (let ((arg (car tail)))
	      (cond ((not (member arg infix-lambda-list-keywords))
		     (cond ((symbolp arg) (italic-sym-printer arg))
			   ((and (consp arg) (equal (length arg) 2))
			    (italic-sym-printer (car arg))
			    (math-space 1)
			    (pprinc ":=")
			    (math-space 1)
			    (infix-print-term1 (cadr arg)))
			   ((and (consp arg) (equal (length arg) 3))
			    (italic-sym-printer (car arg))
			    (math-space 1)
			    (pprinc ":=")
			    (math-space 1)
			    (infix-print-term1 (cadr arg))
			    (math-space 1)
			    (pprinc " flag ")
			    (math-space 1)
			    (infix-print-term1 (caddr arg)))
			 (t (format t "Unrecognized argument type ~s" arg)))
		     (if (cdr tail) (pprinci ", ")))
		  (t (small-caps-sym-printer arg) (pprinci " ")))
	      (if terpri-flag (newline)))) ;newline
  )

;; Let set-margin and set-tab know if they are in a context where
;; we are using a left margin followed by a tab.
(defparameter *left-margin-tab-context* nil)

(defun default-infix-printer (term op)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* *top-parens-eliminable-default*)
         (advice (advise-break term)))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))

; We hate to see (member x (foo ...)) broken right after the x, where
; x is an atom.

    (cond ((and advice
                (not (and (<= (length term) 3)
                          (atom (cadr term)))))
	   ;; Note that this INFIX printer expects at least two arguments.
	   (cond ((consp op)
		  (if (eq *infix-op-location* 'FRONT)
		      (smith-infix-print-tail "" term top-parens-were-eliminable)
		      (boyer-infix-print-tail "" term top-parens-were-eliminable)))
		 ((eq *infix-op-location* 'FRONT)
		  (smith-infix-print-tail op (cdr term) top-parens-were-eliminable))
		 (t (boyer-infix-print-tail op (cdr term) top-parens-were-eliminable))))

	  ((consp op)
	   (if (eq *infix-op-location* 'FRONT)
	       (smith-infix-print-tail "" term top-parens-were-eliminable)
	       (boyer-infix-print-tail "" term top-parens-were-eliminable)))
          ((= (length term) 2)
	   ;; We have accidentally captured a unary op.  Since
	   ;; We assume these will behave like +/-, e.g. if
	   ;; (op x y) prints as "x O y" then (op x) prints as "O x".
	   (pprinci op 3)
	   (pprinci " ")
	   (infix-print-term1 (cadr term))
	   (if (null top-parens-were-eliminable) (pprinci ")")))
	  (t
           (sloop for tail on (cdr term)
                    do
                    (progn (infix-print-term1 (car tail))
                           (cond ((cdr tail)
                                  (pprinci " ")
                                  (pprinci op 3)
                                  (pprinci " "))
                                 (t (cond ((null top-parens-were-eliminable)
                                           (pprinci ")")))))))))))

; See `SETTINGS THAT MAY BE MODIFIED IN MODE-THEORY.LISP' for a description
; of the difference between these two modes of printing.

(defun boyer-infix-print-tail (op args top-parens-were-eliminable)
  (set-tab)
  (sloop for tail on args
           do
           (progn (infix-print-term1 (car tail))
                  (cond ((cdr tail)
                         (newline) (do-tab) ;force-newline
                         (math-space 5)
                         (pprinci op 3)
                         (newline) (do-tab)) ;force-newline
                        (t (cond ((null top-parens-were-eliminable)
                                  (pprinci ")")))
                           (pop-tab))))))

(defun smith-infix-print-tail (op args top-parens-were-eliminable)
  ;; Does this assume we are in a tabbing env?
  (set-margin)
  (set-tab op)
  ;; (let ((*left-margin-tab-context* t)) ... )
  (infix-print-term1 (car args))
  (sloop for tail on (cdr args)
           do
           (progn (to-current-margin)
                  (pprinci op 3)
                  (do-tab)
                  (infix-print-term1 (car tail))
                  (cond ((cdr tail)
                         (to-current-margin))
                        (t (cond ((null top-parens-were-eliminable)
                                  (pprinci ")")))
                           (pop-margin)
			   ;; MOD  Nov 30 94 MKS
                           ;; (to-current-margin)  ;newline
			   )))))


(defun default-unary-prefix-printer (term op)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* *top-parens-eliminable-default*))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (pprinci op 3)
    (pprinci " ")
    (infix-print-term1 (cadr term))
    (cond ((null top-parens-were-eliminable)
           (pprinci ")")))))

(defun default-infix-multiple-printer (term strs)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* *top-parens-eliminable-default*)
         (advice (advise-break term)))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (if (eq *infix-op-location* 'FRONT)
        (smith-infix-multiple-printer term strs advice)
        (boyer-infix-multiple-printer term strs advice))
    (cond ((null top-parens-were-eliminable)
           (pprinci ")")))))

(defun boyer-infix-multiple-printer (term strs advice)
    (set-tab)
    (infix-print-term1 (cadr term))
    (sloop for arg in (cddr term)
             as str in strs do
             (cond (advice (newline) (do-tab)) ;force-newline
                   (t (pprinci " ")))
             (pprinci str)
             (cond (advice (newline) (do-tab)) ;force-newline
                   (t (pprinci " ")))
             (infix-print-term1 arg))
    (pop-tab))

(defun smith-infix-multiple-printer (term strs advice)
  (set-margin)
  ;; (let ((*left-margin-tab-context* nil)) .. )
  (infix-print-term1 (cadr term))
  (sloop for arg in (cddr term)
           as str in strs
           do (progn (cond (advice (to-current-margin))	;newline
                           (t (pprinci " ")))
                     (pprinci str)
                     ;;(cond (advice (newline-to-current-margin))
                     ;;      (t (pprinci " ")))
                     (pprinci " ")
                     (infix-print-term1 arg)))
  (pop-margin))

(defun default-prefix-multiple-printer (term strs)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* *top-parens-eliminable-default*)
         (advice (advise-break term)))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (set-margin)
    ;; (let ((*left-margin-tab-context* nil)) .. )
    (sloop for tail on (cdr term)
             as str in strs
             do (progn (pprinci str)
                       ;;(cond (advice (newline-to-current-margin))
                       ;;      (t (pprinci " ")))
                       (pprinci " ")
                       (infix-print-term1 (car tail))
                       (cond ((null tail) nil)
                             (advice (to-current-margin)) ;newline
                             (t (pprinci " ")))))
    (pop-margin)
    (cond ((null top-parens-were-eliminable)
           (pprinci ")")))))

(defun default-suffix-multiple-printer (term strs)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* *top-parens-eliminable-default*)
         (advice (advise-break term)))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (set-margin)
    (sloop for tail on (cdr term)
             as str in strs
             do (progn (infix-print-term1 (car tail))
                       ;;(cond (advice (newline-to-current-margin))
                       ;;      (t (pprinci " ")))
                       (pprinci str)
                       (cond ((null (cdr tail)))
                             (advice (to-current-margin)) ;newline
                             (t nil))))
    (pop-margin)
    (cond ((null top-parens-were-eliminable)
           (pprinci ")")))))

(defun default-unary-suffix-printer (term op)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* *top-parens-eliminable-default*))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (set-margin)
    (infix-print-term1 (cadr term))
    (pprinci " ")
    (pprinci op 3)
    (pop-margin)
    (cond ((null top-parens-were-eliminable)
           (pprinci ")")))))

(defun default-unary-abs-printer (term lhs-str rhs-str)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* *top-parens-eliminable-default*))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (set-margin)
    (pprinci lhs-str)
    (infix-print-term1 (cadr term))
    (pprinci rhs-str)
    (pop-margin)
    (cond ((null top-parens-were-eliminable)
           (pprinci ")")))))


;                            PRINTING INDEX ENTRIES

; Who could ever have guessed that it would take this much code to print out a
; simple \index{foo} command for an arbitrary Acl2 function symbol foo.  There
; are so many special cases one can hardly believe one's eyes.

; Should be re-defined in mode-init.lisp, e.g. latex-init.lisp.

(defparameter index-subitem-length 30)

(defun index (x &optional subkind)
  ;; Subkind must be string or atom.
  (pprinc *begin-index*)
  (cond ((stringp x) (print-string x 0))
	(t (print-atom x 0)))
  ;; WARNING: Latex/Scribe dependency.
  (if subkind
      (cond ((stringp subkind) (pprinc ", ") (print-string subkind 0))
            ((symbolp subkind) (pprinc ", ") (print-atom subkind 0))
            (t nil)))
  (pprinc *end-index*))


;                                EVENT PRINTERS

(defvar *local-context* nil
  "Indicates when we are in a `local' context, e.g. in encapsulate.")

(defvar *local-handlers* nil
  "List of events that are sensitive to *local-context*")
;; Every -printer that calls event-label printer is so sensitive.

(defmacro local-print (x)
  `(or (member ',x  *local-handlers*)
       (setq *local-handlers* (cons ',x *local-handlers*))))

(defun event-doc-string (doc)
  (cond ((or (null doc) (not (stringp doc)) (string= doc "")))
	(t (begin-text)
	   (if *acl2-format-doc-strings*
	       (let ((pair (acl2-parse-string doc)))
		 (if (car pair)		;failed
		     nil
		     (setq doc (cdr pair)))))
	   ;; IS PPRINC THE RIGHT THING?  WHAT ABOUT SPECIAL CHARS?
	   ;; I think so.
	   (pprinci doc)
	   (to-current-margin)
	   (end-text)
	   (blankline))))

(defun print-default-event-header ()
  (ppformat *print-default-event-header*)
  (setq *infix-loc* 0))

(defun no-tab-event-trailer ()
  (ppformat *no-tab-event-trailer*))

(defun print-default-command-header ()
  (ppformat *print-default-command-header*)
  (setq *infix-loc* 0))

(defun no-tab-command-trailer ()
  "May occur in a tabbing env. due to an encapsulate.
In which case we don't want to print *no-tab-command-trailer*."
  (if *tab-stack* (blankline) (ppformat *no-tab-command-trailer*)))

(defun event-label-printer (label &optional lowercase)
  (if *local-context* (small-caps-sym-printer "LOCAL "))
  (small-caps-sym-printer label)
  (if lowercase (pprinc lowercase)))

(eval-when (load compile eval)

(defun begin-event (&optional doc)
  (blankline)
  (event-doc-string doc)
  (begin-tabbing)
  (line-return))

(defmacro end-event ()
  '(progn (end-tabbing)
	  (blankline)))

(defmacro begin-paragraph ()
  `(progn (blankline) (begin-text)))

(defmacro end-paragraph ()
  `(progn (end-text) (blankline)))

)

;; acl2    == segment*
;; segment == text blankline || event blankline
;; event   == [ doc blankline ] begin-event body [ keys ] end-event
;; body    == type header = form || type header acl2

(defun default-event-printer (event)
  (begin-event)
  (if *local-context*
      (event-label-printer "Local Event" " (of unknown type):  ")
      (event-label-printer "Event" " (of unknown type):  "))
  (newline)
  (quote-printer1 event)
  (end-event))

(defun extract-keywords (l keys)
  (cond ((not (consp keys)) nil)
	((member (car keys) l)
	 (cons (cadr (member (car keys) l))
	       (extract-keywords l (cdr keys))))
	(t (cons nil (extract-keywords l (cdr keys))))))


(defun defcor-printer (event)
  (let* ((name (nth 1 event))
	 (old-event (nth 2 event))
	 (keys (extract-keywords event '(:rule-classes :doc)))
	 (rule-classes (car keys))
	 (doc (cadr keys)))
    (begin-event doc)
    (event-label-printer "Corollary: ")
    (print-atom name)
    (pprinci " is a corollary to ")
    (print-atom old-event)
    (pprinci ".")
    (index name)
    (to-current-margin)
    (cond ((and (consp rule-classes)
		(consp (car rule-classes))
		(equal (car (car rule-classes)) :rewrite)
		(consp (cdr (car rule-classes)))
		(equal (car (cdr (car rule-classes))) :corollary))
	   (infix-print-term (cadr (cdr (car rule-classes)))))
	  (t (pprinc "Rule Classes: ")
	     (infix-print-term rule-classes)))
    (end-event)))

(local-print defcor)


(defun defequiv-printer (event)
  (let* ((fn (nth 1 event))
	 (keys (extract-keywords event '(:rule-classes :doc)))
	 (rule-classes (car keys))
	 (doc (cadr keys)))
    (begin-event doc)
    (event-label-printer "Equivalence relation: ")
    (print-atom fn)
    (index fn)
    (flushright-rule-classes rule-classes)
    (end-tabbing)))

(local-print defequiv)

(defun defdoc-printer (term)
  (ppformat "~%New documentation for: ~s.~%" (cadr term))
  (pprinci (caddr term)))

(defun flushright-rule-classes (rules)
  (if rules
      (progn (begin-flushright)
	     (rule-class-printer rules)
	     (end-flushright))))


(defun defaxiom-printer (term)
  ;; name term :rule-clases clases :doc string
  (let* ((name (nth 1 term))
         (subterm (nth 2 term))
         (keys (extract-keywords term '(:rule-classes :doc)))
         (rule-classes (car keys))
         (doc (cadr keys)))
    (begin-event doc)
    (event-label-printer "Axiom: ")
    (print-atom name)
    (index name)
    (flushright-rule-classes rule-classes)
    (infix-print-term subterm)
    (end-event)))

(local-print defaxiom)


(defun defcong-printer (term)
  ;; equiv1 k equiv2 fn :rule-classes :instructions :hints :otf-flg :cheat :doc
  (let* ((equiv1 (nth 1 term))
         (equiv2 (nth 2 term))
         (fn (nth 3 term))
         (arity (nth 4 term))
         (keys (extract-keywords term '(:rule-classes :instructions :hints :otf-flg :doc)))
         (rule-classes (nth 0 keys))
         (doc (nth 4 keys)))
    (begin-event doc)
    (event-label-printer "Equivalence relation: ")
    (print-atom equiv1)
    (small-caps-sym-printer " preserves ")
    (print-atom equiv2)
    (to-current-margin)
    (small-caps-sym-printer " for argument position ")
    (print-atom arity)
    (small-caps-sym-printer " of ")
    (infix-print-term1 fn)
    (index equiv1 "equivalence")
    (index equiv2 "equivalence")
    (if (consp fn) (index (car fn)))
    (flushright-rule-classes rule-classes)
    (newline)
    (end-event)))

(local-print defcong)


(defun defconst-printer (event)
  (let ((name (nth 1 event))
        (term (nth 2 event))
        (doc  (nth 3 event)))
    (begin-event doc)
    (event-label-printer "Constant: ")
    (infix-print-term (list 'equal name term))
    (end-event)))

(local-print defconst)

(defun defevaluator-printer (term)
  ;; ev ev-list signatures
  (let ((ev (nth 1 term))
	(ev-list (nth 2 term))
	(signatures (cadddr term)))
    (begin-event "Define an evaluator.")
    (ppformat "Let `~s' be an evaluator function, with mutually-recursive counterpart
`~s', for the functions" ev ev-list)
    (print-bare-function-names (mapcar (function car) signatures))
    (index ev)
    (index ev-list)
    (end-event)))

(local-print defevaluator)


(defun deflabel-printer (event)
  (let* ((name (nth 1 event))
         (keys (extract-keywords event '(:doc)))
         (doc (nth 0 keys)))
    (begin-event doc)
    (event-label-printer "Label: ")
    (print-atom name)
    (index name)
    (end-event)))

(local-print deflabel)


(defun defrefinement-printer (term)
  ;; equiv1 equiv2 :rule-classes :instructions :hints :otf-flg :doc
  (let* ((eq1 (nth 1 term))
         (eq2 (nth 2 term))
         (keys (extract-keywords term '(:rule-classes :instructions :hints :otf-flg :doc)))
         ;(rule-classes (nth 0 keys))
         (doc (nth 4 keys)))
    (begin-event doc)
    (event-label-printer "Refinement: ")
    (print-atom eq1)
    (small-caps-sym-printer " refines ")
    (print-atom eq2)
    (index eq1)
    (index eq2)
    (end-event)))

(local-print defrefinement)


(defun defpkg-printer (event)
  (let ((name (nth 1 event))
        ; (contents (nth 2 event))
        (doc  (if (> (length event) 3) (nth 3 event))))
    ;;
    ;; We do the following so that we can print and
    ;; read symbols in this package.
    ;;
    (if (not (find-package name)) (make-package name))
    ;;
    (begin-event doc)
    (event-label-printer "Package ")
    (bold-sym-printer name)
    (index name " defined")
    ;; (infix-print-term contents)
    (to-current-margin)
    (end-event)))


(defun in-package-printer (event)
  (let ((name (nth 1 event)))
    ;;
    ;; We do the following so that we can print and
    ;; read symbols in this package.
    ;;
    (if (not (find-package name)) (make-package name))
    ;;
    (begin-event)
    (event-label-printer "Set current package" " to be ")
    (bold-sym-printer name)
    (pprinc ".") (index name "package used")
    (end-event)))

(local-print in-package)

(defun rebuild-printer (event)
  (let ((name (nth 1 event))
	(key  (if (cddr event) (caddr event))))
    (begin-event)
    (event-label-printer "Rebuild ")
    (italic-sym-printer name)
    (cond ((or (null key)
	       (equal key t)
	       (equal key :all)
	       (equal key :query))
	   (pprinc "."))
	  ((symbolp key) (ppformat " through  ~s." (symbol-name key)))
	  ((and (consp key)
		(eq (car key) 'quote)
		(symbolp (cadr key)))
	   (ppformat " through  ~s." (symbol-name (cadr key))))
	  (t (ppformat ".")))
    (end-event)))

(local-print rebuild)

(defun filename-sym-printer (x)
  (italic-sym-printer (acl2-smash-file-name x)))

;; A file (to acl2) may be a string or
;; (:ABSOLUTE . string* )
;; (:RELATIVE . string* )

(defun acl2-file-name-root (file)
  (cond ((not (consp file)) file)
	(t (car (last file)))))

(defun acl2-smash-file-name (file)
  (cond ((not (consp file))
	 (cond ((stringp file) file)
	       ((symbolp file) (symbol-name file))
	       (t "")))
	((equal (car file) :absolute)
	 (concatenate 'string "/" (acl2-smash-file-name (cdr file))))
	((equal (car file) :relative)
	 (acl2-smash-file-name (cdr file)))
	((equal (car file) :back)
	 (concatenate 'string "../" (acl2-smash-file-name (cdr file))))
	((cdr file) (concatenate 'string (car file) "/" (acl2-smash-file-name (cdr file))))
	(t (car file))))


(defun include-book-printer (event)
  (let* ((file (nth 1 event))
	 (root (acl2-file-name-root file))
	 (keys (extract-keywords event '(:doc)))
	 (doc (nth 0 keys)))
    (begin-event doc)
    (event-label-printer "Including" " the book: ")
    (filename-sym-printer file)
    (pprinc ".") (index root "included")
    (end-event)))

(local-print include-book)		;???


(defun certify-book-printer (event)
  (let* ((file (nth 1 event))
	 (root (acl2-file-name-root file)))
    (begin-event)
    (event-label-printer "Certifying" " the book: ")
    (filename-sym-printer file)
    (pprinc ".") (index root "certified")
    (end-event)))

(local-print certify-book)		;???

(defun infix-print-macro-body (body)
  (cond ((not (consp body)) (infix-print-term1 body))
	((equal (car body) 'quote)
	 (pprinc "'") (infix-print-term1 (cadr body)))
	((equal (car body) '*infix-backquote*)
	 (pprinc "`") (infix-print-term1 (cadr body)))
	(t (infix-print-term1 body))))


(defun defmacro-printer (event)
  (let* ((name (nth 1 event))
	 ;; Note that macro args may include &optional or &rest.
         (args (nth 2 event))
         (doc  (nth 3 event))
         (body (car (last event)))
         (form (cons name args)))
    (begin-event doc)
    (event-label-printer "Macro: ")
    (index name "defined")
    (to-current-margin)
    ;; Can we fit the defun on one line?
    (cond ((let ((*rightmost-char-number* (- *rightmost-char-number* 12)))
             (advise-break (list 'equal form body)))
           ;; No.
           (defun-call-part-printer form)
           (to-current-margin)		;newline
           (pprinci (format nil " ~a " (get 'equal 'literalform)))
	   (to-current-margin)		;(new-tab-row t)
           (infix-print-macro-body body))
          (t (defun-call-part-printer form)
             (pprinci (format nil " ~a " (get 'equal 'literalform)))
	     (infix-print-macro-body body)))
    (to-current-margin)
    (end-event)))

(local-print defmacro)


(defun defstub-printer (event)
  (let ((name (nth 1 event))
        (args (nth 2 event))
        (result (nth 3 event)))
    (begin-event)
    (event-label-printer "Function: ")
    (infix-print-term1 (cons name args))
    ;; (if (equal 1 (length args))
    ;;     (pprinc " of one argument.")
    ;;     (ppformat " of ~a arguments." (length args))))
    (cond ((symbolp result))
          (t (ppformat ". Returns ~a results." (length (cdr result)))))
    (end-event)))

(local-print defstub)

(defun rule-class-printer (classes)
  ;; classes is either keyword or a list of keywords or
  ;; lists whose car is a keyword.
  (cond ((consp classes)
	 (rule-class-print (car classes))
	 (mapc (function (lambda (x) (print-string ", ") (rule-class-print x))) (cdr classes)))
	(t (rule-class-print classes))))

(defun rule-class-print (class)
  (cond ((keywordp class) (italic-sym-printer class))
	((keywordp (car class)) (italic-sym-printer (car class)))
	(t nil)))


(defun defthm-printer (term)
  ;; name term :rule-classes :instructions :hints :otf-flg :doc
  (let* ((name (nth 1 term))
         (subterm (nth 2 term))
         (keys (extract-keywords term '(:rule-classes :instructions :hints :otf-flg :doc)))
         (rule-classes (nth 0 keys))
         (doc (nth 4 keys)))
    (begin-event doc)
    (event-label-printer "Theorem: ")
    (print-atom name)
    (index name)
    (flushright-rule-classes rule-classes)
    (infix-print-term subterm)
    (end-event)))

(local-print defthm)

(defparameter *noindent* nil)
(defvar *indent-string* " ")
(defvar *default-indent* 2)

(defun begin-indent (&optional newline (indent *default-indent*))
  (if newline (newline))
  (sloop for i from 1 to indent do (pprinc *indent-string*))
  (set-margin))

(defun end-indent ()
  (pop-margin)
  (line-return))




(defun encapsulate-printer (term)
  (let ((signatures (nth 1 term))
        (events (cddr term)))
    (begin-event)
    (event-label-printer "Begin Encapsulation")
    (if signatures
	(progn (blankline)
	       (event-label-printer "Constrain" " the functions: ")
	       ;; SCRIBE SPECIFIC BRANCH.
	       (if (or (string= *infix-mode* "scribe")
		       (string= *infix-mode* "SCRIBE"))
		   (blankline))
	       (begin-indent)
	       (mapc (function (lambda (x)
				 (defstub-printer (cons 'defstub x))))
		     signatures)
	       (end-indent)
	       ;(blankline)
	       (small-caps-sym-printer "according to the following events:  ")))
    (blankline)
    (begin-indent)
    (mapc (function (lambda (x) (infix-event x))) events)
    (end-indent)
    (blankline)
    (small-caps-sym-printer "End encapsulatation.")
    (end-event)))

(defun skip-proofs-printer (term)
  (let ((event (nth 1 term)))
    (ppformat "~%The proofs normally generated by the following event are being skipped.~%~%")
    (funcall (get-event-printer (car event)) event)))




(defun local-printer (term)
  (let ((event (cadr term))
	(*local-context* t))
    (if (and (consp event) (member (car event) *local-handlers*))
	(infix-event event)
        (progn (event-label-printer "Local event: ")
	       (infix-event event)))))


(defun mutual-recursion-printer (term)
  (let ((events (cdr term)))
    (mapc (function (lambda (x) (infix-event x))) events)))


(defun defuns-printer (term)
  (let ((events (cdr term)))
    (mapc (function (lambda (x) (infix-event (cons 'defun x)))) events)))


(defun ld-printer (term)
  (let ((keys (extract-keywords term '(:standard-co :proofs-co :current-package
				       :ld-skip-proofsp :ld-redefinition-action
				       :ld-prompt :ld-pre-eval-filter
				       :ld-pre-eval-print :ld-post-eval-print :ld-evisc-tuple
				       :ld-error-triples :ld-error-action
				       :ld-query-control-alist :ld-verbose))))
    (begin-event)
    (event-label-printer "Load" " the file: ")
    (filename-sym-printer (cadr term))
    (end-event)
    (if keys
	(let ((pairs (pairlis '(:standard-co :proofs-co :current-package
			        :ld-skip-proofsp :ld-redefinition-action
				:ld-prompt :ld-pre-eval-filter
				:ld-pre-eval-print :ld-post-eval-print :ld-evisc-tuple
				:ld-error-triples :ld-error-action
				:ld-query-control-alist :ld-verbose)
			      keys)))
	  (pprinc "Loaded with the following settings: ")
	  (print-settings-list pairs)))
    (blankline)))

(defun infix-print-setting (a)
  ;; X is pair of form keyword . setting.
  (let ((f (get-keyword-printer (car a))))
    (funcall f a)))

(defun print-settings-list (pairs)
  (sloop for tail on pairs
	 do (cond ((not (consp tail)))
		  ((cddr tail)
		   (infix-print-setting (car tail))
		   (pprinci ", "))
		  ((cdr tail)
		   (infix-print-setting (car tail)))
		  (t
		   (pprinci " and ")
		   (infix-print-setting (car tail)) (pprinci ".")))))

(defun extract-declare-xarg (dcls)
  ;; dcls = ((DECLARE arg*))
  ;; arg  = xarg || other
  ;; xarg = (XARGS key value ...)
  ;; key  = :guard || :measure || :mode
  (cond ((null dcls) nil)
	((consp (car dcls))
	 (let ((dcl (car dcls)))
	   (cond ((and (equal (car dcl) 'declare)
		       (equal (car (cadr dcl)) 'xargs))
		  (append (cdr (cadr dcl))
			  (extract-declare-xarg (cdr dcls))))
		 (t (extract-declare-xarg (cdr dcls))))))
	(t (extract-declare-xarg (cdr dcls)))))

(defun print-decls (dcls)
  (print-decls2 (extract-declare-xarg dcls)))

(defun print-decls2 (dcls)
  (if (null dcls)
      nil
    (let* ((keys (extract-keywords dcls '(:measure :guard :mode)))
	   ;; Left out :well-founded-relation, :hints, :guard-hints, verify-guards, :otf-flag
	   (measure (nth 0 keys))
	   (guard   (nth 1 keys))
	   (mode    (nth 2 keys)))
      (when measure
	(bold-sym-printer "Measure: ")
	(set-margin)
	(infix-print-term1 measure)
	(pop-margin))
      (when mode
	(bold-sym-printer "Mode: ")
	(print-atom mode)
	(to-current-margin))		;newline
      (when guard
	(bold-sym-printer "Guard: ")
	(set-margin)
	(infix-print-term1 guard)
	(pop-margin)
	(to-current-margin)))))		;newline



(defun defun-printer1 (term equiv)
  ;; (defun name args doc-string dcl ... dcl body)
  (let* ((name (nth 1 term))
         (args (nth 2 term))
         (doc (if (stringp (nth 3 term)) (nth 3 term)))
         (form (cons name args))
         (body (car (last term)))
	 (eq (list equiv form body))
         dcls)
    (sloop for x in (cdddr term)
	   do (if (or (stringp x)
		      (equal x body))
		  nil
		  (setq dcls (append dcls (list x)))))
    (begin-event doc)
    (event-label-printer "Definition: ")
    (index name "defined")
    (to-current-margin)
    ;; Can we fit the defun on one line?
    (cond ((let ((*rightmost-char-number* (- *rightmost-char-number* 12)))
            (advise-break eq))
           ;; No.
           (infix-print-term1 form)
           (to-current-margin)		;newline
           (pprinci (format nil " ~a " (get equiv 'literalform)) 3)
           ;; (new-tab-row t)
           (infix-print-term body))
          (t (infix-print-term1 form)
             (pprinci (format nil " ~a " (get equiv 'literalform)) 3)
             (infix-print-term1 body)))
    (to-current-margin)
    (print-decls dcls)
    (end-event)))


(defun defun-printer (term)
  (defun-printer1 term 'equal))

(local-print defun)
(local-print define)

(defun forall-printer (term)
  (let  ((vars (nth 1 term))
	(body (nth 2 term)))
    (pprinci *forall* *tt-size*)
    (cond ((atom vars)
           (funcall (get-atom-printer vars) vars))
          (t (sloop for tail on vars do
                      (funcall (get-atom-printer (car tail)) (car tail))
                      (cond ((cdr tail)
                             (pprinci ", " *tt-size*))))))
    (pprinc ":")
    (math-space 1)
    (infix-print-term1 body)))

(defun exists-printer (term)
  (let ((vars (nth 1 term))
	(body (nth 2 term)))
    (pprinci *exists* *tt-size*)
    (cond ((atom vars)
	   (funcall (get-atom-printer vars) vars))
          (t (sloop for tail on vars do
		    (funcall (get-atom-printer (car tail)) (car tail))
		    (cond ((cdr tail)
			   (pprinci ", " *tt-size*))))))
    (pprinc ":")
    (math-space 1)
    (infix-print-term1 body)))

(declare-fn-printer exists (function exists-printer))
(declare-fn-printer forall (function forall-printer))


;; Rune                           Runic Desig
;;  def = symbolp   :functionp ==  (:DEFINITION symb).
;;  ex  = (symbolp) :functionp ==  (:EXECUTABLE-COUNTERPART symb)
;;  thm = symbolp   :defthm    ==  {...} set introduced
;;  ax  = symbolp   :defaxiom  ==  {...} set introduced
;;  th  = symbolp   :deftheory ==  {...} set introduced

;; runic-desig    = def | ex | thm | ax | theory | ?? string
;; runic-des  ==   sym | (sym)
;; rune       ==   (:DEFINITION sym) | (:EXECUTABLE-COUNTERPART sym)
;;               | (:REWRITE sym)    | (:REWRITE sym)
;;               | (:ELIM sym)       | runic-des



(defun print-rune-string (rune)
  (cond ((eq rune :here)     (pprinc "the current theory"))
	((not (consp rune))  (print-bare-function-name rune))
	((null (cdr rune))
	 (pprinc "the executable counterpart of ")
	 (print-bare-function-name (car rune)))
	((eq (car rune) :executable-counterpart)
	 (pprinc "the executable counterpart of ")
	 (print-bare-function-name (cadr rune)))
	((eq (car rune) :definition)
	 (pprinc "the definition of ")
	 (print-bare-function-name (cadr rune)))
	((eq (car rune) :rewrite)
	 (pprinc "the rewrite rule, ")
	 (print-bare-function-name (cadr rune)))
	((eq (car rune) :elim)
	 (pprinc "the elimination rule, ")
	 (print-bare-function-name (cadr rune)))
	(t (pprinc "the ") (print-atom (car rune))
	   (pprinc " rule, ")
	   (print-bare-function-name (cadr rune)))))

(defun runes-print (runes)
  (cond ((cdr runes)
	 (sloop for x on runes
		do (cond ((cddr x)
			  (print-rune-string (car x))
			  (pprinc ", "))
			 ((cdr x)
			  (print-rune-string (car x))
			  (pprinc " and "))
			 (t (print-rune-string (car x))))))
	(t (print-rune-string (car runes)))))

;; name       ==   sym | string | :here   -- event name
;; theory     ==   (rune*)                -- sets of runes to enable/disable in concert
;; theory-des ==
;;      (DISABLE runic-desig*)            => theory
;;    | (ENABLE  runic-desig*)            => theory
;;
;;    | (CURRENT-THEORY   name)           => theory  -- name is atom, string, or :here
;;    | (UNIVERSAL-THEORY name)           => theory  -- as of logical name
;;    | (THEORY           name)           => theory
;;    | (FUNCTION-THEORY  name)           => theory  -- function symbol rules
;;
;;    | (INTERSECTION-THEORIES th1 th2)   => theory
;;    | (SET-DIFFERENCE-THEORIES th1 th2) => theory
;;    | (UNION-THEORIES th1 th2)          => theory


(defun theory-print (form &optional (tail ""))
  (cond ((not (consp form))
	 (pprinci (format nil "the theory "))
	 (bold-sym-printer form)
	 (pprinci tail))
	((eq (car form) 'quote) (runes-print (cadr form)) (pprinci tail))
	(t (or *do-not-use-tabs* (begin-tabbing))
	   (infix-print-term1 form)(pprinci tail)
	   (or *do-not-use-tabs* (end-tabbing)))))

(defun deftheory-printer (event)
  (let* ((name (nth 1 event))
         (theory (nth 2 event))
         (keys (extract-keywords event '(:doc)))
         (doc (nth 0 keys)))
    (event-doc-string doc)
    (newline)
    (begin-text)
    (line-return)
    (event-label-printer "Define" " the theory ")
    (bold-sym-printer name)
    (index name "theory")
    (pprinc " to be ")
    (theory-print theory ".")
    (end-text)
    (blankline)))

(local-print deftheory)


(defun in-theory-printer (event)
  (let* ((theory (nth 1 event))
         (keys (extract-keywords event '(:doc)))
         (doc (nth 0 keys))
	 *do-not-use-tabs*)
    (event-doc-string doc)
    (newline)
    (begin-text)
    (line-return)
    (event-label-printer "Modify" " the current theory: ")
    (theory-print theory ".")
    (end-text)
    (blankline)))

(local-print in-theory)


(defun boot-strap-printer (term)
  (declare (ignore term))
  (begin-event)
  (event-label-printer "Start" " with the initial Acl2 theory.")
  (end-event))


(defun verify-guards-printer (event)
  (let* ((name (nth 1 event))
	 (keys (extract-keywords event '(:doc)))
	 (doc (nth 0 keys)))
    (begin-event doc)
    (event-label-printer "Verify guards" " for ")
    (print-bare-function-name name)
    (index name "guard verification")
    (end-event)))

(local-print verify-guards)


;;    (verify-termination fn dcl ... dcl)
;; or (verify-termination (fn1 dcl ... dcl) (fn2 dcl ... dcl) ...)

(defun verify-termination-printer (event)
  (begin-event)
  (event-label-printer "Verify termination" " for ")
  (set-margin)
  (let ((events (if (symbolp (cadr event))
		    (list (cdr event))
		    (cdr event))))
    (mapl (function (lambda (x)
		      (progn (print-verify-termination (car x))
			     (to-current-margin))))
	  events))
  (pop-margin)
  (end-event))

(local-print verify-termination)

(defun print-verify-termination (x)
  (cond ((consp x)
	 (pprinc " ")
	 (print-bare-function-name (car x))
	 (pprinc " with ")
	 (print-decls (cdr x)))
	(t (pprinc " ") (print-bare-function-name x))))

(defun disable-printer (form)
  (pprinc "Disable ")
  (runes-print (cdr form)))

(declare-fn-printer disable (function disable-printer))

(defun enable-printer (form)
  (pprinc "Enable ")
  (runes-print (cdr form)))

(declare-fn-printer enable (function enable-printer))

(defun current-theory-printer (form)
  (cond ((eq (cadr form) :here)
	 (pprinci "the current theory "))
	((and (consp (cadr form)) (eq (car (cadr form)) 'quote))
	 (pprinci (format nil "the theory as of ~a" (cadr (cadr form)))))
	(t (pprinci (format nil "the theory as of ~a" (cadr form))))))

(declare-fn-printer current-theory (function current-theory-printer))

(defun universal-theory-printer (form)
  (cond ((eq (cadr form) :here)
	 (pprinci "the current universal theory "))
	((and (consp (cadr form)) (eq (car (cadr form)) 'quote))
	 (pprinci (format nil "the theory as of ~a" (cadr (cadr form)))))
	(t (pprinci (format nil "the universal theory as of ~a" (cadr form))))))

(declare-fn-printer universal-theory (function universal-theory-printer))

(defun theory-printer (form)
  (cond ((eq (cadr form) :here)
	 (pprinci "the current theory "))
	((and (cadr form) (consp (cadr form)) (eq (car (cadr form)) 'quote))
	 (pprinci "the theory ") (bold-sym-printer (cadr (cadr form))))
	(t (pprinci (format nil "the theory ~a" (cadr form))))))

(declare-fn-printer theory (function theory-printer))

(defun function-theory-printer (form)
  (cond ((eq (cadr form) :here)
	 (pprinci "the current function theory "))
	((and (cadr form) (consp (cadr form)) (eq (car (cadr form)) 'quote))
	 (pprinci "the function theory ") (bold-sym-printer (cadr (cadr form))))
	(t (pprinci (format nil "the function theory ~a" (cadr form))))))

(declare-fn-printer function-theory (function function-theory-printer))

;; See scribe or latex init to see how the following are handled.
;;  intersection-theories
;;  set-difference-theories
;;  union-theories

(defun theory-invariant-printer (form)
  (let ((term (cadr form))
	(key  (if (cddr form) (caddr form) nil)))
    (cond ((eq (car term) 'incompatible)
	   (print-rune-string (cadr term))
	   (pprinc " is incompatible with ")
	   (print-rune-string (caddr term))
	   (pprinc " in this theory")
	   (if key (pprinc "Call this invariant ") (print-atom key)))
	  (t (cond (key (pprinc (format nil "Invariant [~a]: " key))
			(infix-print-term1 (term)))
		   (t (pprinc "Invariant : ")
			(infix-print-term1 (term))))))))

(declare-fn-printer theory-invariant (function theory-invariant-printer))

(defun defun-sk-printer (event)
  ;; (defun-sk name args body &key doc quant-ok skolem-name thm-name)
  (let* ((name (nth 1 event))
         (args (nth 2 event))
         (body (nth 3 event))
	 (keys (extract-keywords event '(:doc :quant-ok :skolem-name :thm-name)))
	 (doc (nth 0 keys))
         (form (cons name args))
         (eq (list 'equal form body)))
    (begin-event doc)
    (event-label-printer "Definition w/quantifier: ")
    (index name "defined with quantifier")
    (to-current-margin)
    ;; Can we fit the defun on one line?
    (cond ((let ((*rightmost-char-number* (- *rightmost-char-number* 12)))
            (advise-break eq))
           ;; No.
           (infix-print-term1 form)
           (to-current-margin)		;newline
           (pprinci (format nil " ~a " (get 'equal 'literalform)) 3)
           ;; (new-tab-row t)
           (infix-print-term body))
          (t (infix-print-term1 form)
             (pprinci (format nil " ~a " (get 'equal 'literalform)) 3)
             (infix-print-term1 body)))
    (to-current-margin)
    (end-event)))

;; (  LEFT IN ----------

(defun do-file-printer (term)
  (print-default-event-header)
  (pprinc "Do all forms in the file:
")
  (italic-sym-printer (cadr term))
  (no-tab-event-trailer))

(defun setq-printer (term)
  (print-default-event-header)
  (let (name value)
    (match term (setq name value))
    (ppformat "Give the Acl2 control variable ")
    (tt-sym-printer name)
    (ppformat " the value ")
    (tt-sym-printer value)
    (ppformat "."))
  (no-tab-event-trailer))

(defun comp-printer (term)
  ":comp t          - compile all uncompiled ACL2 functions
:comp foo        - compile the defined function foo
:comp (foo bar)  - compile the defined functions foo and bar"
  (print-default-command-header)
  (cond ((null (cdr term))
         (pprinc "Unknown compile command."))
        ((equal (cadr term) t)
	 (pprinc "Compile all uncompiled ACL2 functions."))
        ((symbolp (cadr term))
	 (pprinc "Compile ")
           (print-bare-function-name (cadr term))
           (pprinc "."))
        (t (pprinc "Compile ")
           (print-bare-function-names (cadr term))
           (pprinc ".")))
  (no-tab-command-trailer))

(defmacro define-command-printer (name string)
  (let ((fn-name (intern (format nil "~s-COMMAND-PRINTER" name))))
    `(progn
       (clean-up ',name)
       (defun ,fn-name
         (term)
	 (declare (ignore term))
	 (print-default-command-header)
	 (pprinc ,string)
	 (no-tab-command-trailer))
       (declare-command-printer ,name (function ,fn-name)))))

(defun checkpoint-forced-goals-printer (term)
  (print-default-command-header)
  (if (cadr term)
      (pprinc "Checkpoint forced goals.")
      (pprinc "Do not checkpoint forced goals."))
  (no-tab-command-trailer))

(define-command-printer disable-forcing "Disable forcing.")
(define-command-printer enable-forcing "Enable forcing.")
(define-command-printer good-bye "Exiting both ACL2 & lisp.")
(define-command-printer oops-printer "Redo last undo.")

(defun puff-printer (term)
  (print-default-command-header)
  (pprinc "Expand command ")
  (print-atom (cadr term))
  (pprinc ".")
  (no-tab-command-trailer))

(defun puff*-printer (term)
  (print-default-command-header)
  (pprinc "Expand command ")
  (print-atom (cadr term))
  (pprinc " recursively.")
  (no-tab-command-trailer))

(define-command-printer q "Quiting ACL2.")
(define-command-printer redef "Allow redefinition without undoing.")
(define-command-printer redef!
 "!!! ACL2 system hacker's redefinition command:
Allow redefinition (even of system functions) without undoing.")

(defun reset-ld-specials-printer (term)
  (print-default-command-header)
  (pprinc "Reset LD specials to their initial value")
  (if (cadr term)
      (pprinc ", including I/O channels.")
      (pprinc "."))
  (no-tab-command-trailer))

(defun set-cbd-printer (term)
  (print-default-command-header)
  (pprinc "Set connected book directory to ")
  (filename-sym-printer (cadr term))
  (pprinc ".")
  (no-tab-command-trailer))

(defun set-guard-checking-printer (term)
  (print-default-command-header)
  (if (cadr term)
      (pprinc "Set guard checking on.")
      (pprinc "Set guard checking off."))
  (no-tab-command-trailer))

(define-command-printer start-proof-tree "Start prooftree logging.")
(define-command-printer stop-proof-tree "Stop prooftree logging.")
(define-command-printer u "Undo last event.")

(defun ubt-printer (term)
  (print-default-command-header)
  (cond ((null (cdr term))
         (pprinc "Undo the last event."))
        (t (pprinc "Undo back through the event named `")
           (print-atom (cadr term))
           (pprinc "'.")))
  (no-tab-command-trailer))

(defun retrieve-printer (term)
  (print-default-command-header)
  (pprinc "Re-enter proof-builder state")
  (if (cadr term)
      (ppformat " named ~s." (cadr term))
      (pprinc "."))
  (no-tab-command-trailer))

(define-command-printer unsave "")
(define-command-printer save "")

(defun verify-printer (event)
  (begin-event "Enter the interactive proof check with:")
  (infix-print (cadr event))
  (end-event))

(defun accumulated-persistence-printer (term)
  (print-default-command-header)
  (if (cadr term)
      (pprinc "Activate statistics gathering.")
      (pprinc "De-activate statistics gathering."))
  (no-tab-command-trailer))

(defun show-accumulated-persistence-printer (term)
  (print-default-command-header)
  (cond ((equal (cadr term) :frames)
	 (pprinc "Display statistics ordered by frames built."))
	((equal (cadr term) :tries)
	 (pprinc "Display statistics ordered by times tried."))
	((equal (cadr term) :ratio)
	 (pprinc "Display statistics ordered by the ratio of frames built to times tried."))
	(t nil))
  (no-tab-command-trailer))

(defun brr-printer (term)
  (print-default-command-header)
  (if (cadr term)
      (pprinc "Enable the breaking of rewrite rules.")
      (pprinc "Disable the breaking of rewrite rules."))
  (no-tab-command-trailer))

(defun monitor-printer (term)
  (let ((form (cadr term))
	(flag (caddr term)))
    (if (and (consp form) (equal (car form) 'quote))
	(setq form (cadr form)))
    (if (and (consp flag) (equal (car flag) 'quote))
	(setq flag (cadr flag)))
    (print-default-command-header)
    (pprinc "Monitor: ")
    (print-rune-string form)
    (cond ((equal flag t))
	  (t (pprinc " when ")
	     (infix-print-term flag)))
    (no-tab-command-trailer)))

(define-command-printer monitored-runes "Print monitored runes.")

(defun unmonitor-printer (term)
  (let ((form (cadr term)))
    (if (and (consp form) (equal (car form) 'quote))
	(setq form (cadr form)))
    (print-default-command-header)
    (pprinc "Un-monitor: ")
    (cond ((equal form :all) (pprinc "all monitored runes."))
	  (t (print-rune-string form)
	     (pprinc ".")))
    (no-tab-command-trailer)))

(defun add-macro-alias-printer (term)
  (print-default-command-header)
  (pprinc "Let the macro name ")
  (print-bare-function-name (cadr term))
  (pprinc " be an alias for the function ")
  (print-bare-function-name (caddr term))
  (pprinc ".")
  (no-tab-command-trailer))

(defun remove-macro-alias-printer (term)
  (print-default-command-header)
  (pprinc "Remove the alias from the macro ")
  (print-bare-function-name (cadr term))
  (pprinc ".")
  (no-tab-command-trailer))

(define-command-printer logic "Enter logic mode.")
(define-command-printer program "Enter program mode.")

(defun set-compile-fns-printer (term)
  (print-default-command-header)
  (if (cadr term)
      (pprinc "New functions will be compiled after their defun.")
      (pprinc "New functions will not be compiled after their defun."))
  (no-tab-command-trailer))

(defun set-ignore-ok-printer (term)
  (print-default-command-header)
  (cond ((null (cadr term))
	 (pprinc "Disallow unused formals and locals."))
	((eq (cadr term) t)
	 (pprinc "Allow unused formals and locals."))
	((eq (cadr term) :warn)
	 (pprinc "Allow unused formals and locals, but print warning.")))
  (no-tab-command-trailer))

(define-command-printer set-invisible-fns-alist "Setting the invisible fns alist.")

(defun set-irrelevant-formals-ok-printer (term)
  (print-default-command-header)
  (cond ((null (cadr term))
	 (pprinc "Disallow irrelevant formals in definitions."))
	((eq (cadr term) t)
	 (pprinc "Allow irrelevant formals in definitions."))
	((eq (cadr term) :warn)
	 (pprinc "Allow irrelevant formals in definitions, but print warning.")))
  (no-tab-command-trailer))

(defun set-measure-function-printer (term)
  (print-default-command-header)
  (pprinc "Set the default measure function to be ")
  (print-bare-function-name (cadr term))
  (pprinc ".")
  (no-tab-command-trailer))

(defun set-verify-guards-eagerness-printer (term)
  (print-default-command-header)
  (cond ((equal (cadr term) 0)
	 (pprinc "No guard verification unless :verify-guards is t."))
	((equal (cadr term) 1)
	 (pprinc "Verify guards, if supplied."))
	((equal (cadr term) 2)
	 (pprinc "Verify guards, unless :verify-guards is NIL.")))
  (no-tab-command-trailer))

(defun set-well-founded-ordering-printer (term)
  (print-default-command-header)
  (pprinc "Set the default well-founded relation to be ")
  (print-bare-function-name (cadr term))
  (pprinc ".")
  (no-tab-command-trailer))

;; TABLE

(defun table-printer (term)
  ;; (table tests 1 '(...))               ; set contents of tests[1] to '(...)
  ;; (table tests 25)                     ; get contents of tests[25]
  ;; (table tests)                        ; return table tests as an alist
  ;; (table tests nil nil :clear)         ; clear table tests
  ;; (table tests nil (foo 7) :clear)     ; set table tests to (foo 7)
  ;; (table tests nil nil :guard)         ; fetch the table guard
  ;; (table tests nil nil :guard term)    ; set the table guard
  (print-default-command-header)
  (let ((table (nth 1 term))
	(i (nth 2 term))
	(value (nth 3 term))
	(op (nth 4 term))
	(guard (nth 5 term)))
    (cond ((null (cddr term))
	   (ppformat "Return table, ")
	   (infix-print-term1 table)
	   (ppformat ", as an alist."))
	  ((null (cdddr term))
	   (infix-print-term1 table)
	   (pprinc "[")
	   (infix-print-term1 i)
	   (pprinc "]"))
	  ((null (cdddr (cdr term)))
	   (infix-print-term1 table)
	   (pprinc "[")
	   (infix-print-term1 i)
	   (pprinc "]")
	   (math-space 1)
	   (pprinc ":=")
	   (math-space 1)
	   (infix-print-term1 value)
	   (pprinc ";"))
	  ((null op)
	   (message (format nil "Unknown table operation ~s" term)))
	  ((equal op :clear)
	   (cond ((null value)
		  (ppformat "Clear table, ")
		  (infix-print-term1 table)
		  (ppformat "."))
		 (t (ppformat "Set elements of table, ")
		    (infix-print-term1 table)
		    (ppformat " to ")
		    (infix-print-term1 value)
		    (pprinc "."))))
	  ((equal op :guard)
	   (cond ((null guard)
		  (ppformat "Fetch guard of table, ")
		  (infix-print-term1  table)
		  (ppformat "."))
		 (t
		  (ppformat "Set guard of table, ")
		  (infix-print-term1 table)
		  (ppformat ", to ")
		  (infix-print-term1 guard)
		  (pprinc "."))))
	  (t (message (format nil "Unknown table operation ~s" term)))))
  (no-tab-command-trailer))

;; We would like to put this at the top, but the functions need to be defined first.

(setq *event-printer-alist*
      (append
       *event-printer-alist*
       (list
	(list 'defaxiom (function defaxiom-printer))
	(list 'defcong (function defcong-printer))
	(list 'defconst (function defconst-printer))
	(list 'defcor (function defcor-printer)) ;gone
	(list 'defequiv (function defequiv-printer))
	(list 'deflabel (function deflabel-printer))
	(list 'defdoc   (function defdoc-printer))
	(list 'defevaluator (function defevaluator-printer))
	(list 'defmacro (function defmacro-printer))
	(list 'defpkg (function defpkg-printer))
	(list 'defrefinement (function defrefinement-printer))
	(list 'defstub (function defstub-printer))
	(list 'deftheory (function deftheory-printer))
	(list 'defthm (function defthm-printer))
	(list 'defun (function defun-printer))
	(list 'defun-sk (function defun-sk-printer))
	(list 'define (function defun-printer)) ;mks&mk specific
	(list 'in-package (function in-package-printer))
	(list 'rebuild (function rebuild-printer))
	(list 'encapsulate (function encapsulate-printer))
	(list 'verify-guards (function verify-guards-printer))
	(list 'verify-termination (function verify-termination-printer))

	;; Books

	(list 'include-book (function include-book-printer))
	(list 'certify-book (function certify-book-printer))
	(list 'certify-book! (function certify-book-printer))

	;; History.

	;; (list 'ubt (function ubt-printer))
	;; (list 'pbt (function ignore-printer))
	;; (list 'pc  (function pc-printer))
	;; (list 'pcb (function pcb-printer))
	;; (list 'pe  (function pe-printer))

	;; OTHER

	(list 'in-theory (function in-theory-printer))
	(list 'local (function local-printer))
	(list 'mutual-recursion (function mutual-recursion-printer))
	(list 'defuns (function defuns-printer))
	(list 'ld (function ld-printer))

	(list 'comp (function comp-printer))
	(list 'checkpoint-forced-goals (function checkpoint-forced-goals-printer))
	(list 'puff (function puff-printer))
	(list 'puff* (function puff*-printer))
	(list 'reset-ld-specials (function reset-ld-specials-printer))
	(list 'set-cbd (function set-cbd-printer))

	(list 'set-guard-checking (function set-guard-checking-printer))
	(list 'ubt (function ubt-printer))
	(list 'ubt! (function ubt-printer))
	(list 'retrieve (function retrieve-printer))
	(list 'skip-proofs (function skip-proofs-printer))
	(list 'accumulated-persistence (function accumulated-persistence-printer))
	(list 'show-accumulated-persistence (function show-accumulated-persistence-printer))
	(list 'brr (function brr-printer))
	(list 'monitor (function monitor-printer))
	(list 'unmonitor (function unmonitor-printer))
	(list 'add-macro-alias (function add-macro-alias-printer))
	(list 'remove-macro-alias (function remove-macro-alias-printer))
	(list 'set-compile-fns (function set-compile-fns-printer))
	(list 'set-ignore-ok (function set-ignore-ok-printer))
	(list 'set-irrelevant-formals-ok (function set-irrelevant-formals-ok-printer))
	(list 'set-measure-function (function set-measure-function-printer))
	(list 'set-verify-guards-eagerness (function set-verify-guards-eagerness-printer))
	(list 'set-well-founded-ordering (function set-well-founded-ordering-printer))

	(list 'table (function table-printer))

	)))

(defparameter *save-event-printer-alist* *event-printer-alist*)

(defun get-event-printer (sym)
  (let ((a (assoc sym *event-printer-alist*)))
    (cond (a (cadr a))
          (t (function default-event-printer)))))

;;                          KEYWORD PRINTERS

(defvar *keyword-printer-alist* nil)

;; Argument to keyword printers is a pair (key . value)

(defun get-keyword-printer (sym)
  (let ((a (assoc sym *keyword-printer-alist*)))
    (cond (a (cadr a))
          (t (function default-keyword-printer)))))

(defun default-keyword-printer (pair)
  (ppformat " ~a is ~a" (car pair) (cdr pair)))

(defun standard-co-keyword-printer (pair)
  ;; "foo.out"
  (ppformat " standard output to ~a" (cdr pair)))

(defun proofs-co-keyword-printer (pair)
  ;; "proofs.out"
  (ppformat " proof output to ~a" (cdr pair)))

(defun current-package-keyword-printer (pair)
  ;; 'acl2
  (let ((name (if (equal (car (cdr pair)) 'quote)
		  (cadr (cdr pair))
		  (cdr pair))))
    (ppformat " in the package ~a" name)))

(defun ld-skip-proofsp-keyword-printer (pair)
  ;; 'include-book
  (cond ((null (cdr pair))
	 (ppformat " doing proofs"))
	((equal (cdr pair) t)
	 (ppformat " skipping termination proofs"))
	((equal (cdr pair) '(quote include-book))
	 (ppformat " assuming proofs in included books"))
	((equal (cdr pair) '(quote include-book-with-locals))
	 (ppformat " assuming proofs in included books and executing local events"))
	((equal (cdr pair) '(quote initialize-acl2))
	 (ppformat " skipping local proofs"))
	(t nil)))

(defun ld-redefinition-action-keyword-printer (pair)
  ;; nil
  (cond ((null (cdr pair))
	 (ppformat " redefinition prohibited"))
	(t (let ((a (car (cdr pair)))
		 (b (cdr (cdr pair))))
	     (cond ((eq a ':query)
		    (ppformat " query on redefinition "))
		   ((eq a ':warn)
		    (ppformat " warn on redefinition"))
		   ((eq a ':doit)
		    (ppformat " redefinition ok"))
		   (t			; :warn! :query!
		    (ppformat " redefinition ~a" a)))
	     (cond ((eq b ':erase)
		    (ppformat " erase properties on redefinition "))
		   ((eq a ':overwrite)
		    (ppformat " overwrite properties on redefinition"))
		   (t
		    (ppformat " redefinition properties ~a" a)))))))

(defun ld-prompt-keyword-printer (pair)
  ;; t
  (cond ((null (cdr pair))
	 (ppformat " no prompt"))
	((eq (cdr pair) t)
	 (ppformat " default prompt"))
	(t
	 (ppformat " prompt function = ~a" (cdr pair)))))

(defun ld-pre-eval-filter-keyword-printer (pair)
  ;; :all
  (cond ((null (cdr pair)))
	((equal (cdr pair) ':all)
	 (ppformat " every form read is evaled"))
	((equal (cdr pair) ':query)
	 (ppformat " user queried whether form read is evaled"))
	(t nil)))

(defun ld-pre-eval-print-keyword-printer (pair)
  ;; nil
  (if (cdr pair)
      (ppformat " forms read are printed")
      (ppformat " forms read are not printed")))

(defun ld-post-eval-print-keyword-printer (pair)
  ;; :all
  (cond ((null (cdr pair))
	 (ppformat " results are not printed"))
	((equal (cdr pair) t)
	 (ppformat " results are printed"))
	((equal (cdr pair) ':command-conventions)
	 (ppformat " conditionally print error triples"))
	(t nil)))

(defun ld-evisc-tuple-keyword-printer (pair)
  ;; '(alist nil nil level length)
  (let (value)
    (cond ((null (cdr pair)) (setq value nil))
	  ((not (consp (cdr pair))) (setq value (cdr pair)))
	  ((equal (car (cdr pair)) 'quote) (setq value (cadr (cdr pair))))
	  (t (setq value (cdr pair))))
    (cond ((null value)
	   (ppformat " print results fully"))
	  (t (let ((alist (cadr value))
		   (level (car (cdddr value)))
		   (length (car (cdr (cdddr value)))))
	       (ppformat " eviscerate results (level = ~d, length = ~d)" level length)
	       (if alist
		   (progn (ppformat "whose cars are in (" )
			  (sloop for tail on alist do
				 (cond ((cddr tail)
					(ppformat"~a, " (car (car tail))))
				       ((cdr tail)
					(ppformat " ~a, and" (car (car tail))))
				       (t (ppformat " ~a)" (car (car tail)))))))))))))

(defun ld-error-triples-keyword-printer (pair)
  ;; t
  (cond ((null (cdr pair))
	 (ppformat " errors printed as triples"))
	((equal (cdr pair) t)
	 (ppformat " errors roll back to state before call"))
	(t nil)))

(defun ld-error-action-keyword-printer (pair)
  ;; :return
  (cond ((null (cdr pair)))
	((equal (cdr pair) ':continue)
	 (ppformat " continue after errors"))
	((equal (cdr pair) ':return)
	 (ppformat " return after errors"))
	((equal (cdr pair) ':error)
	 (ppformat " signal errors"))
	(t nil)))

(defun ld-query-control-alist-keyword-printer (pair)
  ;; nil
  (cond ((null (cdr pair))
	 (ppformat " handle queries interactively"))
	((equal (cdr pair) 't)
	 (ppformat " queries default to first accepted response"))
	(t
	 (ppformat "queries default according to ~s"  (cdr pair)))))

(defun ld-verbose-keyword-printer (pair)
  ;; nil
  (cond ((null (cdr pair))
	 (ppformat"verbose mode off "))
	(t
	 (ppformat " verbose mode on"))))

(defparameter *keyword-printer-alist*
  (list (list ':standard-co (function standard-co-keyword-printer))
	(list ':proofs-co (function proofs-co-keyword-printer))
	(list ':current-package (function current-package-keyword-printer))
	(list ':ld-skip-proofsp (function ld-skip-proofsp-keyword-printer))
	(list ':ld-redefinition-action (function ld-redefinition-action-keyword-printer))
	(list ':ld-prompt (function ld-prompt-keyword-printer))
	(list ':ld-pre-eval-filter (function ld-pre-eval-filter-keyword-printer))
	(list ':ld-pre-eval-print (function ld-pre-eval-print-keyword-printer))
	(list ':ld-post-eval-print (function ld-post-eval-print-keyword-printer))
	(list ':ld-evisc-tuple (function ld-evisc-tuple-keyword-printer))
	(list ':ld-error-triples (function ld-error-triples-keyword-printer))
	(list ':ld-error-action (function ld-error-action-keyword-printer))
	(list ':ld-query-control-alist (function ld-query-control-alist-keyword-printer))
	(list ':ld-verbose (function ld-verbose-keyword-printer))))


;                           COPY COMMENTS

;; MKS Tue Jul 13 1993
;; Make ;- comments and BAR-COMMENTs followed by a dash appear in
;; a formatted (in Latex, verbatim) environment.

(defparameter *comment-environment* nil)

(defparameter *comment-format* 'smith)

(defparameter *comment-semi-net* nil)
(defparameter *comment-lb-net* nil)

;; We use this two stage template/eval kludge so that if the template can
;; be used to reset the variable after the user has defined these variables.

;; Note a problem with this flexibility.  In some contexts we need to format
;; special characters and in others we don't.  Thus in LaTeX, in a Verbatim
;; we don't need to quote `_', but in running text we do need to quote it.

(defparameter *comment-environment-mapping-template*
  (quote `((text     "" "")
	   (format   ,*begin-format-env*   ,*end-format-env*)
           (verbatim ,*begin-verbatim-env* ,*end-verbatim-env*)
           (emphasis ,*begin-emphasis-env* ,*end-emphasis-env*)
	   (comment  ,*begin-comment-env*  ,*end-comment-env*)
	   (section ,*begin-section-env*   ,*end-section-env*))))

(defparameter *comment-environment-mapping*
  (eval *comment-environment-mapping-template*))

(defparameter *saved-whitespace* nil)

(defun print-saved-whitespace ()
  (sloop for c in *saved-whitespace*
	 do (if (stringp c) (pprinc c) (pwrite-char c)))
  (setq *saved-whitespace* nil))

(defun wrap-up-copy-comments ()
  ;; MOD - X
  (end-environment)
  (print-saved-whitespace)
  (throw 'copy-comments nil))

(defun begin-environment (env)
  (setq *comment-environment* env)
  (ppformat
           (or (cadr (assoc env *comment-environment-mapping*)) "")))

(defun end-environment ()
  (if *comment-environment*
      (ppformat (or (caddr (assoc *comment-environment*
				  *comment-environment-mapping*))
		    "")))
  (setq *comment-environment* nil))

(defun end-environment-and-write (c)
  (end-environment)
  (pwrite-char c))

(defun pop-environment-write-and-push (string)
  (let ((saved-env *comment-environment*))
    (if (not saved-env)
        (pprinc string)
        (progn (end-environment)
               (pprinc string)
               (begin-environment saved-env)))))

(defun end-environment-if-not (env)
  (if (not (equal *comment-environment* env))
      (end-environment)))

(defun white-space-string-p (s)
  (let ((x t))
    (sloop for i from 0 to (- (length s) 1)
             do (setq x (and x (member (char s i) *white-space*))))
    x))

(defun insert-newpage ()
  (pop-environment-write-and-push (pformat nil "~%~a~%" *newpage*)))

;; (defparameter *format-tag-char* #\~)

(defun check-environment-and-write (env ch)

  ;; Note: Latex causes an error on an empty VERBATIM environment, so we watch out
  ;; for that as a special case.  Also, Latex forbids control-l in a verbatim
  ;; environment, so we watch out for that, too.

  ;; Thus, we forbid any empty environments, and we always pull a page break
  ;; out of the current environment.

  ;; First, end an existing environment if it is not ENV.

  (end-environment-if-not env)

  (cond ((not *comment-environment*)    ; We are in no environment.  Enter one.
         (cond ((and ch (not (member ch *white-space*)))
		;; Assuming *saved-whitespace* can't intersect
		;; characters handled by (handle-special-chars-in-string ch)
                (print-saved-whitespace)
                (begin-environment env))

;; Does this work? Printing of saved whitespace complicated by the
;; verbatim restrictions of latex.  I.e., can't have an empty verbatim.


               ((and ch (eql ch #\Page)) ;; MOD 1/96 (equal env 'verbatim)
                ;;(setq *saved-whitespace*
                ;;    (append *saved-whitespace*
                ;;            (list (format nil "~%~a~%" *newpage*))))
		(ppformat t "~%~a~%" *newpage*))
               (ch (setq *saved-whitespace*
                        (append *saved-whitespace* (list ch)))))))
  ;; Tabs
  (cond ((and (equal env 'verbatim)
              (eql ch #\Tab)
              (not *reported-tabs*))
         (setq *reported-tabs* t)
         (pformat *terminal-io*
                  "WARNING: about tabs!~%We note the presence of a tab ~
                  in a comment that we are copying~%into a verbatim ~
                  environment.  Tabs will be treated just like ~%single spaces ~
                  by Latex.  Consider removing all tabs, e.g., ~%with the ~
                  Emacs command M-x untabify.~%")))

  ;; Print it or not, checking #\Page.
  (cond (*saved-whitespace*)
        ((and (eql ch #\Page) (equal env 'verbatim))
         (end-environment)
         (ppformat "~%~a~%"  *newpage*)
         (begin-environment env))

        (ch
	 ;; Switched (pwrite-char ch)
	 (handle-special-chars-in-string ch))))

(defun unread-chars (l stream)
  (sloop for c in l do (unread-char c stream)))

(defun read-char-in-comment ()
       (let ((c (read-char *standard-input* nil a-very-rare-cons)))
         (cond ((eq c a-very-rare-cons)
                ;; EOF.  We are no longer in a comment.
                ;; Exit whatever environment we are in, which will be either
                ;; verbatim, format, or none.
                (wrap-up-copy-comments))
               (t c))))

(defun copy-comments-read-net (net)
  ;; Returns (env char), where env is the environment to
  ;; enter and char is nil or a char to unread.
  ;; Net is cdr of a net whose car = #\;
  ;; Have already read a #\;
  ;;
  ;; Test (progn (read-char)(COPY-COMMENTS-READ-NET *comment-semi-net*))
  ;;
  (let* ((subnet (car net))
         (action (cadr net))
	 ;; on EOF does a throw out once it cleans up.
         (c (read-char-in-comment))
         (branch (assoc c subnet)))
    (cond ((null branch)
           (unread-char c *standard-input*)
           (list (car action) (cadr action)))
          (t (copy-comments-read-net (cdr branch))))))

(defvar number-deep nil "Measure of depth of imbedding in \#\| \|\# comments")

(defun normalize-lb-comment-line (str action)
  (let ((beg (search "#|" str))
	(end (search "|#" str)))
    (cond ((and beg end)
	   (cond ((< beg end)
		  (normalize-lb-comment-line
		   (concatenate 'string
				(subseq str 0 beg)
				(subseq str (+ beg 2) end)
				(subseq str (+ end 2)))
		   action))
		 (t (format-comment-string (subseq str 0 end) action)
		    (decf number-deep 1)
		    (cond ((= number-deep 0)
			   (end-environment)
			   (unread-chars (coerce (subseq str (+ end 2)) 'list)
					 str))
			  (t (normalize-lb-comment-line (read-line *standard-input*) action))))))
	  (beg (incf number-deep 1)
	       (format-comment-string (subseq str 0 beg) action)
	       (normalize-lb-comment-line (subseq str (+ beg 2)) action))
	  (end (format-comment-string (subseq str 0 end) action)
	       (decf number-deep 1)
	       (cond ((= number-deep 0)
		      (end-environment)
		      (subseq str (+ end 2)))
		     (t (normalize-lb-comment-line (subseq str (+ end 2)) action))))
	  (t (format-comment-string str action)
	     (normalize-lb-comment-line (read-line *standard-input*) action)))))

(defun format-comment-string (line mode)
  (if (and *acl2-format-comments* (search "~" line))
      (let ((pair (acl2-parse-string line)))
	(if (car pair)			;failed
	    nil
	    (setq line (cdr pair)))))
  (let ((max (- (length line) 1)))
    (sloop for i from 0 to max
	   do (let ((ch (aref line i)))
		(cond ((eql ch #\Page) (insert-newpage))
		      ;; switched (pwrite-char ch)
		      (*comment-environment* (handle-special-chars-in-string ch))
		      (t (check-environment-and-write mode ch)))))
    (if (> max 0)
	(if (not (char-equal (aref line max) #\Newline))
	    (pwrite-char #\Newline)
	    nil)
	(pwrite-char #\Newline))
    nil))

(defun copy-comments ()

; This function tries to sneak up to the next top-level open parenthesis,
; parsing all of the Lisp comments up till there.
; NOTE:  Jul 13 93 MKS
; Random atoms, numbers, strings and characters are treated as if they were in
; comments.  And are printed in a FORMAT environment.
; NOTE:  Nov 30 94 MKS
; This sneaking up doesn't work quite the way we would like. If we have
; a comment line, followed by a blank line, followed by (foo ..) then we
; put out the formatted comment line, followed by a blank line, followed
; by a close-environment, followed by the formatted (foo ..).

  (let (*comment-environment*)
    (catch 'copy-comments
      (sloop
       for ch = (read-char-in-comment)

; The top level loop for simulating the skimming of whitespace and comments
; that READ would perform to get to the next open parenthesis.

       (case ch

; Semicolon starts a comment.
; We use *COMMENT-SEMI-NET* to determine how to format the comment based on the
; immediately following characters.  This is user-setable to produce
; running text, a format environment (honors spaces and newlines, but probably
; does not produce a fixed width font), a verbatim environment (like format, but
; fixed width font), an emphasis environment (typically italics), or a title
; environment (like a section name).

         (#\;
	  ;; Do one line.
          (let ((action (copy-comments-read-net *comment-semi-net*)))
            (check-environment-and-write (car action) (cadr action))
	    (format-comment-string (read-line *standard-input*) (car action))))

; #\| starts a comment.
; As above, we use the *comment-lb-net* to determine what formatting action to take.
; \|# ends one.

         (#\#
          (setq ch (read-char-in-comment))
          (cond ((not (eql ch #\|))
                 (error"Do not know how to handle #~s while copying at the top level." ch)))
          (let ((action (copy-comments-read-net *comment-lb-net*)))

            ;; The following may not put us into an env if (cadr
            ;; action) is whitespace.

            (check-environment-and-write (car action) (cadr action))

            ;; We ignore formatting changes within imbedded #| |# comments.
            ;; They are stuck with whatever the outermost comment
            ;; decreed.

	    (setq number-deep 1)
	    (let* ((line (read-line *standard-input*))
		   (rest (normalize-lb-comment-line line (car action))))
	      (cond ((and rest (not (string-equal rest "")))
		     ;; Sep 22 95 MKS reversed order of the 2 forms below.
		     ;; Wrap-up throws out of copy-comments.
		     (unread-chars (nreverse (coerce rest 'list))
				   *standard-input*)
		     (wrap-up-copy-comments))))))

         ;; A raw ^L at the top level, not in a comment.
         (#\Page (end-environment)
          (ppformat "~%~a~%"  *newpage*))

	 (#\Newline
	  (end-environment)
	  (print-saved-whitespace)
	  (pwrite-char ch))
         (#\(
          (unread-char #\( *standard-input*)
          (wrap-up-copy-comments))
	 ;; Handle keywords like parenthesized forms, because they may
	 ;; need to read their arguments.
         (#\:
          (unread-char #\: *standard-input*)
          (wrap-up-copy-comments))
         (otherwise ;; switched (pwrite-char ch)
	  ;; MOD -  Sep 21 95 MKS
	  ;; Added the following:
	  (print-saved-whitespace)
	  (handle-special-chars-in-string ch)
	  ))))))


;;--------------------------------------------------------------------------------
;
;                       COMMENT FORMATS
;

(defparameter *comment-format-alist* nil)
(defparameter *comment-format* nil)

(defun update-alist (al key value)
  (cond ((not (consp al)) (list (cons key key value)))
        ((eq key (caar al)) (cons (cons key value) (cdr al)))
        (t (cons (car al) (update-alist (cdr al) key value)))))

(defun define-comment-format (n format)
  ;; Last call to this sets *comment-format*.
  ;; Can be overruled by
  ;;  1. assigning directly to *comment-format*,
  ;;  2. calling (setup-comment-format format-name), or
  ;;  3. calling infix-setup with the appropriate arguments.
  (if (not (check-comment-character-net format))
      (format *terminal-io* "~%Ill formed definition for comment format ~a" n)
      (progn
	(setq *comment-format* n)
	(cond ((assoc n *comment-format-alist*)
	       (setq  *comment-format-alist* (update-alist *comment-format-alist* n format)))
	      (t (setq *comment-format-alist*
		       (cons (cons n format) *comment-format-alist*)))))))

(defun setup-comment-format (&optional n)
  (cond ((and n (assoc n *comment-format-alist*))
	 ;; A named format.
	 (setq *comment-format* n))
	((and n *comment-format*)
	 ;; Not defined.  Use existing setting.
	 (format *terminal-io*
		 "~%No comment format named ~a.  Left as ~a." n *comment-format*))
	(n (setq *comment-format* 'smith)
	   (format *terminal-io*
		   "~%No comment format named ~a.  Defaluting to ~a." n *comment-format*))
        ((null *comment-format*)
         (cond ((eq *infix-op-location* 'FRONT)
                (setq *comment-format* 'smith))
               ((eq *infix-op-location* 'BACK)
                (setq *comment-format* 'boyer))
               (t (setq *comment-format* 'smith))))
        ((assoc *comment-format* *comment-format-alist*))
	(*comment-format-alist*
	 (setq *comment-format* (caar *comment-format-alist*))
	 (format *terminal-io* "~%Defaluting to first format in alist, ~a." *comment-format*))
        (t ;; Should never get here.
	 (format *terminal-io* "~%*** No comment formats defined!!! ***")))
  (compute-comment-character-net *comment-format*)
  ;; We have side-effected *comment-semi-net* and *comment-lb-net*
  ;; Update mapping info AFTER users theory file loaded.
  (setq *comment-environment-mapping* (eval *comment-environment-mapping-template*)))

(defun check-comment-character-net (l)
  (if (null l)
      (format *terminal-io* "*COMMENT-FORMAT* is not present in *COMMENT-FORMAT-ALIST*."))
  (if (not (assoc #\; l))
      (format *terminal-io* "Selected comment format should include a list labelled \"\;\"."))
  (if (not (assoc #\# l))
      (format *terminal-io* "Selected comment format  should include a list labelled \"\#\"."))
  ;; Each branch is of the form (string flag environment [echo-character])
  (check-comment-character-net2 l))

(defun check-comment-character-net2 (l)
  (cond ((null l) t)
        ((and (listp l)
              (listp (car l))
              (characterp (caar l))
              (every
	       (function
		(lambda (branch)
		  (if (check-comment-character-branch branch)
		      t
		      (format *terminal-io* "Ill-formed branch in *COMMENT-FORMAT-ALIST*.~
                                                       ~%~a" branch))))
	       (cadr (car l)))
              (let ((top (cddr (car l))))
                (and (or (equal (car top) 't) (null (car top)))
                     ;; Must be known environment.
                     (assoc (cadr top) *comment-environment-mapping*)
                     (or (null (cddr top)) (characterp (caddr top))))))
         ;; Do the other one, if there.
         (check-comment-character-net2 (cdr l)))
        (t nil)))

(defun check-comment-character-branch (b)
  (and (listp b)
       (> (length b) 2)
       (stringp (car b))
       (or (equal (cadr b) 't) (null (cadr b)))
       ;; Must be known environment.
       (assoc (caddr b) *comment-environment-mapping*)
       (or (null (cdddr b))
           (characterp (cadddr b)))))

(defun compute-comment-character-net (name)
  (let ((l (cdr (assoc name  *comment-format-alist*))))
    (let ((net (assoc #\; l)))
      (setq *comment-semi-net*
            (if net
                (cdr (compute-net -1 (car net) (cadr net) (caddr net) (cdddr net)))
                nil)))
    (let ((net (assoc #\# l)))
      (setq *comment-lb-net*
            (if net
                (cdr (compute-net -1 (car net) (cadr net) (caddr net) (cdddr net)))
                nil)))))

(defun compute-net (n char net skip-one-blank-p default)
  (list char
        (append (if skip-one-blank-p
                    `((#\  nil ,default))
                    nil)
                (compute-branches (+ n 1) net))
        default))

(defun compute-branches (n net)
  (cond ((null net) nil)
        (t (merge-net (compute-branch n (car net))
                      (compute-branches n (cdr net))))))

(defun compute-branch (n branch)
  ;; branch is of the form (string flag . default)
  (let ((string (car branch))
        (flag (cadr branch))
        (default (cddr branch)))
  (cond ((> n (length string)) nil)
        ((= n (length string))
         (if flag
             `(#\  nil ,default)
             nil))
        (t (append (list (char string n)
                         (list (compute-branch (+ n 1) branch)))
                   (if (= (+ n 1) (length string)) (list default) nil))))))

(defun merge-net (branch net)
  ;; All branches of net begin with a unique character.
  ;; As does the result.
  (cond ((null net) (list branch))
        ((char= (car branch) (caar net))
         (let ((def1 (caddr branch))
               (def2 (caddr (car net))))
           (cons
	    (list (car branch)
		  (merge-net (caadr branch) (cadr (car net)))
		  (cond ((equal def1 def2) def1)
			((and def1 def2)
			 (format *terminal-io*
				 "Your comment network is in conflict ~a ~a." branch (car net))
			 def1)
			(def1 def1)
			(t def2)))
	    (cdr net))))
        (t (cons (car net) (merge-net branch (cdr net))))))

(define-comment-format 'boyer
  '((#\; (("\\"   t   text))
     nil verbatim #\;)
    (#\# (("\\"   t   text))
     nil verbatim)))

(define-comment-format 'smith
  '((#\; (("\;"   t   text   )
          ("\#"   t   comment )
          ("\;\;" t   verbatim )
          ("\\"   t   text     )
          ("-"    t   format   )
          ("+"    t   verbatim )
          ("!"    t   emphasis )
          ("\;\\" nil   text     #\;)
          ("\;-"  nil   format   #\;)
          ("\;+"  nil   verbatim #\;)
          ("\;!"  nil   emphasis #\;))
     t text)
    (#\# (("\\"   t   text     )
          ("\#"   t   comment  )
          ("-"    t   format   )
          ("\;"   t   verbatim ))
     t text )))


(define-comment-format 'CL
  '((#\; (("\;"   t    format )
          ("\;\;" t    text   )
          ("\;\;\;" t  section)

          ("\\"   t   text     )
          ("-"    t   format   )
          ("+"    t   verbatim )
          ("!"    t   emphasis )
          ("\;\\" nil   text     #\;)
          ("\;-"  nil   format   #\;)
          ("\;+"  nil   verbatim #\;)
          ("\;!"  nil   emphasis #\;))
     t emphasis)
    (#\# (("\\"   t   text     )
          ("-"    t   format   )
          ("\;"   t   verbatim ))
     t text )))

(setup-comment-format 'cl)

;; End of comment stuff.

(defun infix-form (form &key ((:print-case *print-case*) :downcase))
  ;; We cannot recover well from this case since we don't
  ;; know where we are.  All of the I/O that provides that info
  ;; is in the top level loop.  So these inner forms are just out of luck.
  (let ((*top-parens-eliminable* t)
        (*print-pretty* nil)
	;; (*saved-tab-stack* *tab-stack*)
	)
    ;; (cond ((catch 'taboverflow
    ;;              (let ((*tabs-in* 1))
    ;;                (or *do-not-use-tabs* (begin-tabbing))
    ;;                (infix-print-term1 form)
    ;;                (or *do-not-use-tabs* (end-tabbing))
    ;;                nil))
    ;;            (pformat *terminal-io*
    ;; 		    "~%Sorry. Exceeded tabbing limit (1). ~a needs hand massaging.~%"
    ;; 		    (car form))
    ;; 	   (setq *tab-stack* *saved-tab-stack*)
    ;; 	   (newline)))
    (let ((*tabs-in* 1))
      (or *do-not-use-tabs* (begin-tabbing))
      (infix-print-term1 form)
      (or *do-not-use-tabs* (end-tabbing))
      nil)))

(defun infix-event (form &key ((:print-case *print-case*) :downcase))
  ;; We cannot recover well from this case since we don't
  ;; know where we are.  All of the I/O that provides that info
  ;; is in the top level loop.  So these inner forms are just out of luck.
  (let ((*top-parens-eliminable* t)
        (*print-pretty* nil))
    ;; (cond ((catch 'taboverflow
    ;;              (let ((*tabs-in* 1))
    ;;                (funcall (get-event-printer (car form)) form)
    ;;                nil))
    ;;            (pformat *terminal-io*
    ;; 		    "~%Sorry. Exceeded tabbing limit (2). ~a needs hand massaging.~%"
    ;; 		    (car form))
    ;; 	   (newline)))
    (let ((*tabs-in* 1))
      (funcall (get-event-printer (car form)) form)
      nil)))

(defparameter *last-mode* nil)

(defparameter *infix-trace* nil)

(defun current-directory ()
  ;; This is somewhat redundant.
  ;; That is (probe-file file) should equal
  ;; (probe-file (concatenate 'string (current-directory) file))
  ;; But we let *current-directory* also be set by the input file.
  (truename "./"))

;; This may be set by the function above or based on the directory of the input file.
(defparameter *current-directory* nil)

(defun probe-theory (fl)
  (let ((name (concatenate 'string (pathname-name fl) "-theory")))
    (or (probe-file (make-pathname :name name
				   :type "lisp" :defaults fl))
	(probe-file (make-pathname :name name
				   :type "lisp"
				   :directory (pathname-directory *current-directory*)
				   :defaults fl))
	(probe-file (make-pathname :name name
				   :type "lisp"
				   :directory (pathname-directory *infix-directory*)
				   :defaults fl)))))

;; Check that *infix-directory* we can find at least a latex and scribe theory.
(eval-when (load eval)
 (if (not (and (probe-theory "scribe") (probe-theory "latex")))
     (format *terminal-io* "~%Seem to be missing theory of scribe or latex or both.~%")))

(defun type-file-name (file type &optional force)
  ;;if extension = nil, return file.
  ;;if file already has type and force = nil, return file.
  (cond ((null type) file)
	((and (not force) (pathname-type file)) file)
	(t (make-pathname :type type :defaults file))))

(defvar *default-chars-wide* 77)

(defun directory-or-current (fl)
  (let ((dir (directory-namestring fl)))
    (cond ((null dir) (current-directory))
	  ((not (equal dir "")) dir)
	  (t (current-directory)))))

(defun probe-cert-for-packages (fl)
  (let ((cert (probe-file (make-pathname :type "cert" :defaults fl)))
	doit)
    (if cert
	(progn
	  (format t "Checking ~s for defpackage forms.~%" cert)
	  (with-open-file
	   (*standard-input* cert :direction :input)
	   (sloop for form = (read *standard-input* nil a-very-rare-cons nil)
		  until (or (eq form a-very-rare-cons)
			    (eq form :end-portcullis-cmds))
		  do
		  (cond ((eq form :begin-portcullis-cmds)
			 (setq doit t))
			((and doit (consp form) (eq (car form) 'defpkg))
			 (if (not (find-package (cadr form)))
			     (make-package (cadr form))))
			(t nil))))))))

(defun infix-file (fl &key ((:print-case *print-case*) :downcase)
                      (mode nil)
                      (chars-wide *default-chars-wide*)
                      (comment *nq-default*))

  (let ((*current-directory* (directory-or-current fl))
	(fl-root (pathname-name fl))
	*tab-stack*)
    (cond ((and mode (string= mode *infix-mode*))
           (format t "~%Processing in ~a mode.~%" mode))
          ((stringp mode)
           (setq *infix-mode* mode)
           (format t "~%Entering ~a mode.~%" *infix-mode*)
           (load-infix-init-file))
          (mode
           (setq *infix-mode* (string mode))
           (format t "~%Entering ~a mode.~%" *infix-mode*)
           (load-infix-init-file))
          ((probe-theory fl-root)
           (setq *infix-mode* (pathname-name fl-root))
           (format t "~%Entering ~a mode.~%" *infix-mode*)
           (load-infix-init-file))
          ((null *infix-mode*)
           (cond ((y-or-n-p "Enter Latex mode? ")
                  (setq *infix-mode* "latex"))
                 ((y-or-n-p "Enter Scribe mode? ")
                  (setq *infix-mode* "scribe"))
                 (t (setq *infix-mode* nil)))
           (if *infix-mode*
               (progn (format t "~%Entering ~a mode.~%" *infix-mode*)
                      (load-infix-init-file))))
          (t (format t "~%Remaining in ~a mode.~%" *infix-mode*)))

; infix-file takes a root file name, e.g., foo, reads the file foo.lisp,
; which we suppose has been previously checked by LD, and creates the
; file foo.tex, which the user can then run through Latex, etc.  By default, we
; lowercase all variable and function symbols, but the user can override this
; with the keyword parameter.

; If the keyword comment is given as true, then we first generate fl.nqxxx and then
; invoke nqfmt2fmt, generating fl.xxx (.tex or .mss).

    ;; Update comment information AFTER users theory file loaded.
    (setup-comment-format)

    (if *infix-mode*
        (let ((infl  (type-file-name fl infix-input-file-type))  ; ".lisp"
              ;; .mss, .tex, .nqmss, .nqtex
              (outfl (type-file-name fl (fmtfile-extension *infix-mode* comment) t))
              (a-very-rare-cons (cons nil nil))
              (*print-pretty* nil)
              (*top-parens-eliminable* t)
              (*readtable* (copy-readtable nil))
              (*reported-tabs* nil)
              (*infix-loc* 0)
              (*left-margin* 0)
              (*rightmost-char-number* chars-wide)
              (count 1)
              inpos)
	  (probe-cert-for-packages fl)
          (smash-infix-readtable)

          (with-open-file
           (*standard-input* infl :direction :input)
           (with-open-file

; We do *all* of our printing of terms to *standard-output*, giving princ only
; one argument.

            (*standard-output* outfl :direction :output :if-exists :rename-and-delete)

; The formatting system opening.

            (ppformat *standard-prelude*)
            (sloop for form = (progn (copy-comments)
				     ;; Set this here so we don't rewrite preceding comment,
				     ;; if tabs overflow.
				     (setq inpos (file-position *standard-input*))
				     (readx *standard-input* nil a-very-rare-cons nil))

; We remember where we are in the output file as part of our mechanism for
; recovering from the very small finiteness of the Latex tabbing mechanism.  We
; will rewrite to the current position and start printing in verbatim mode with
; PPR if we exceed the Latex tabbing mechanism.

                     for outpos = (file-position *standard-output*)
                     until (eq form a-very-rare-cons)
                     do
                     ; (ppformat "\\filbreak %\\item~%")
                     (cond ((or (eq (car form) 'comment)
                                (cond ((catch 'taboverflow
                                         (let ((*tabs-in* 1))
                                           (if *infix-trace*
                                               (format *terminal-io* "~% ~a " (car form)))
                                           ;; Let the user know we are making some
					   ;; kind of progress, every 10 events.
                                           (if (= count 10)
					       (progn (format *terminal-io* ".")
						      (setq count 1))
                                               (incf count))
                                           (funcall (get-event-printer (car form)) form))
                                         nil)
				       (pformat *terminal-io*
						"~%Warning: Tab limit reached in event ~a~
                                                 ~%Hand massaging required.~%"
					     (or (and (consp form) (cdr form) (cadr form))
						 (car form)))
                                       t)))
                            ;; If taboverflow, go back to where we started printing and
                            ;; print over the previous stuff.  In the 'commment case our
                            ;; position is unchanged.
                            (file-position *standard-output* outpos)
			    (setq *tab-stack* nil)
                            (begin-environment 'verbatim)
                            (let ((stop (file-position *standard-input*)))
                              (file-position *standard-input* inpos)
                              (sloop while (< (file-position *standard-input*) stop)
                                       do (check-environment-and-write 'verbatim
								       (read-char *standard-input*))))
                            (end-environment))
                           (t nil)))
            (ppformat *standard-postlude*)))
          (if comment
              (nqfmt2fmt fl)
              outfl))
        (format t "~%No mode specified (e.g. Latex or Scribe), aborting.~%"))))

(defun load-obj-or-lisp (file)
  (let ((object (make-pathname :type "o" :defaults file)))
    (cond ((and (probe-file object)
		(> (file-write-date object) (file-write-date file)))
	   (load object))
	  ((probe-file file) (load file))
	  (t (error (format nil "~%No theory or init file mathcing ~f~%" file))))))

;; (defun load-obj-or-lisp (file)
;;   (let* ((name2 (if (member 'sparc *features*)
;; 		    (concatenate 'string (pathname-name file) "-sparc")
;; 		    (concatenate 'string (pathname-name file) "-sun")))
;; 	 (file2   (probe-file (make-pathname :name name2 :defaults file)))
;;          (object  (probe-file (make-pathname :type "o" :defaults file)))
;;          (object2 (if file2 (probe-file (make-pathname :type "o" :defaults file2)))))
;;     (cond ((and object2 (> (file-write-date object2) (file-write-date file2)))
;; 	   (load object2))
;; 	  (file2 (load file2))
;; 	  ((and object (> (file-write-date object) (file-write-date file)))
;; 	   (load object))
;; 	  ((probe-file file) (load file))
;; 	  (t (error (format nil "~%No theory or init file mathcing ~f~%" file))))))

(defun load-theory-or-init (dir)
  (let* ((initfile   (make-pathname :name (concatenate 'string *infix-mode* "-init")
				    :type "lisp"
				    :directory (and dir (pathname-directory dir))))
         (theoryfile (make-pathname :name (concatenate 'string *infix-mode* "-theory")
				    :type "lisp"
				    :directory (and dir (pathname-directory dir)))))
    ;; We assume that, if present, the -theory file loads the -init file.
    (cond ((probe-file theoryfile) (load-obj-or-lisp theoryfile) t)
          ((probe-file initfile)   (load-obj-or-lisp initfile) t)
          (t nil))))

(defun load-infix-init-file ()
  (clean-up-everything)
  (cond ((null *infix-mode*)
         (format t "~%Failed to initialize.  *infix-mode* is NIL.~%"))
        ((not (stringp *infix-mode*))
         (format t "~%Failed to initialize.~
                    ~%*infix-mode* (~a) is not a string.~%" *infix-mode*))
        ((load-theory-or-init *current-directory*))
        ((load-theory-or-init *infix-directory*))
        (t (format t "~%Failed to initialize.  No init or theory file in ~a nor ~a.~%"
                   *current-directory* *infix-directory*)
           (setq *infix-mode* nil))))

(defun fmtfile-extension (mode comment)
  (cond ((and *mode-extension* (stringp *mode-extension*))
         (if comment (concatenate 'string "nq" *mode-extension*) *mode-extension*))
        ((string= mode "latex")
         (if comment "nqtex" "tex"))
        ((string= mode "scribe")
         (if comment "nqmss" "mss"))
        (t (if comment "nqnq" "nq"))))

(defun fmt2fmt-extension (remove! mode)
  (cond (remove! "stripped")
        ((and *mode-extension* (stringp *mode-extension*))
         (concatenate 'string "nq" *mode-extension*))
        ((string= mode "latex")  "nqtex")
        ((string= mode "scribe") "nqmss")
        (t "nqnq")))

(defvar nqread-default-white-space '(#\Space #\Newline #\Tab #\Page #\Return))
(defvar nqread-default-normal-clause-enders '(#\. #\! #\? #\, #\; #\:))
(defvar nqread-default-break-chars '(#\( #\) #\` #\' #\" #\; #\,))

(defparameter nqread-white-space nqread-default-white-space)
(defparameter nqread-normal-clause-enders nqread-default-normal-clause-enders)
(defparameter nqread-break-chars nqread-default-break-chars)

(defun acl2-read-preserving-whitespace-error ()
  (error "A character or an integer or an Acl2 symbol was expected at location ~a of input."
         (file-position *standard-input*)))

(defun acl2-read-preserving-whitespace ()

; This function does the READing right after a ! command.  This
; function is almost the same as read-preserving-whitespace.  It is
; different only because of the peculiar problem of trailing
; punctuation marks.  We sometimes stop the reading before Common Lisp
; would.

; In processing ! commands, we call READ on the following text.  If
; the text starts with an open parenthesis or string-quote, it is
; clear where the READing should stop.  However, if a mere symbol or
; number follows a ! command, then when READing the symbol we treat
; an exclamation mark, colon, question mark, or period that is
; followed by whitespace as a punctuation mark, not as part of the
; symbol that is to be READ.  The other ordinary English clause ending
; punctuation characters (comma and semicolon) already naturally
; terminate a READ, as do parentheses, quotation marks, and
; whitespace.

; Example.  When we do a READ while processing a ! command under
; nqtex2tex, we have to decide what to do about text such as

;    !tnil.

; The question is, does the period belong to the token to be read, or
; is it just some user punctuation?  We take the attitude that the
; answer is punctuation.  Now, this attitude is a bit arbitrary.  nil.
; is a legal Common Lisp symbol.  Unfortunately it is ALSO a legal Acl2 symbol.
; But we are just going to assume that it is atypical.  And likewise for
; `foo.bar'.  We also run into problems reading things like
; xxx.@end{text}@begin{format}@tabclear{}.  This is a fine atom as far as
; ACL2 is concerned. Likewise
; xxx.\begin{verbatim}\hfill
; So the text-formatting -init file will need to extend nqread-normal-clause-enders
; to account for this.

; One might ask, who cares?  The reason we care is that nil, and other
; symbols on *atom-alist*, get printed specially.  For example, nil is
; printed in bold, not italics.  If we read nil. as one symbol, it would
; come out in intalics because nil. is not on *atom-alist*.

; The idea of fiddling with READ so that it is `smart' about not
; reading a trailing punctuation character is weird.  But then,
; calling READ in the middle of Tex file is weird, too.  We have found from
; experience that it is very hard to write sentences that have
; whitespace after every symbol.  We want to be able to write things
; like !tnil, and !tnil.  So here is the general procedure for how far
; we READ after a ! command.  When we say READ below, we really mean
; read-preserving-whitespace.

; We peek at the first nonwhitespace character after the ! command,
; and we consider the cases on this character.

; If it is ( or " we simply call READ, knowing that upon encountering
; the closing " or ) READ will not look at any trailing punctuation.

; If it is ' or ` we recursively read further with this function and
; then quote or backquote the result.  This is so that `foo. will come
; out right.

; Otherwise, we call READ on the string consisting of all of the
; characters up to but not including the first (a) whitespace, (b)
; terminating readmacro Common Lisp character, i.e., ()`'"";,, or (c)
; normal English clause ending character, i.e., .!?:, that is followed
; by a whitespace.

; Known ambiguity.  Although periods are permitted at the ends of
; numbers in Acl2 syntax, we treat them as ends of sentences, if they
; are followed by white space.  Thus in reading !t5. , the read
; would not pick up the period.  So the period would appear in the
; final text.  It is hard to see whether this is a bug, a feature, or
; a problem that simply never arises.

; Known ambiguity.  Because the quotation mark is a legal character
; in Acl2 symbols, a minor question arises about the handling of
; a terminal question mark in an Acl2 symbol; we treat it as punctuation.
; Thus !qfoo? will come out as `foo'? rather than `foo?'.

; All this peeking stuff doesn't work really correctly if there are
; comments in the way, so we adopt this rule: don't put comments in
; expressions after ! commands.  Typically, this function is called
; inside of a comment.  If the text to be read extends over a line and
; the next line begins with a ; character, you may not get at all what
; you want because the text on the line after the ; will be skipped.

  (case (peek-char t *standard-input*)
        ((#\( #\") (read-preserving-whitespace *standard-input*))
        (#\'
         (read-char *standard-input*)
         (list 'quote (acl2-read-preserving-whitespace)))
        (#\`
         (read-char *standard-input*)
         (list *infix-backquote* (acl2-read-preserving-whitespace)))
        (otherwise
	 (let ((*package* *user-package*))
         (read-from-string
          (coerce
           (nconc
            (prog (c ans c2)
                  loop
                  (setq c (peek-char nil *standard-input* nil a-very-rare-cons))
                  (cond ((or (eq c a-very-rare-cons)
                             (member c nqread-white-space)
                             (member c nqread-break-chars))
                         (cond ((null ans)
                                (acl2-read-preserving-whitespace-error)))
                         (return (nreverse ans)))
                        ((member c nqread-normal-clause-enders)
                         (read-char *standard-input*)
                         (setq c2 (peek-char nil *standard-input* nil a-very-rare-cons))
                         (cond ((or (member c2 nqread-white-space)
                                    (eq c2 a-very-rare-cons))
                                (unread-char c *standard-input*)
                                (cond ((null ans)
                                       (acl2-read-preserving-whitespace-error)))
                                (return (nreverse ans)))
                               (t (push c ans))))
                        ((member c '(#\| #\; #\\))
                         (acl2-read-preserving-whitespace-error))
                        (t (read-char *standard-input*)
                           (push c ans)))
                  (go loop))

; Sticking on this extra space is not strictly necessary.  We do it to
; work around a bug in AKCL 1-605.

            (list #\Space))
           'string))))))

(defparameter nqtex2tex-chars
  (coerce "eipqtv" 'list))

;             NQFMT2FMT

(defun nqfmt2fmt (fl &key
                  ((:print-case *print-case*) :downcase)
                  ((:left-margin *left-margin*) 5)
                  (just-remove-! nil))

; Copies the file fl.nqxxx file to the file fl.xxx file, replacing Acl2 forms
; preceded by a two character sequence starting with an exclamation mark with
; the results described below.  If an exclamation mark is not followed by one
; of these special characters, then the following form is preserved unchanged,
; and the exclamation mark and the character following it are preserved, too.

; Although we may extend this set of replacement commands, we *promise* to give
; special meanings only to alphabetic characters after !.  Thus we promise
; never to give !!  a replacement effect.

; In every case, for one of the replacement characters, upper or lower case has
; the same effect.

; !Bform, prints form in bold.

; !Eev, where ev is an Acl2 event form, e.g., (defun foo (x) 3), results in
; conventional notation for ev.  We may introduce line breaks via tabbing commands.
; Mnemonic: E -- think Event.

; !Ifoo, where foo is a symbol, results in foo, but with with formatting sensitive
; characters quoted.  For example, in TeX, !Ia$b would result in a\$b.
; Mnemonic: I -- think Identity.

; !Pfm, where fm is an Acl2 term, e.g., (plus x y), results in conventional
; mathematical notation for fm.  May introduce line breaks via tabbing.
; Mnemonic: P -- think Pretty print.

; !Qfn, where fn is a symbol, results in fn surrounded by single gritches,
; after formatting sensitive characters have been quoted, e.g., !qfoo results in
; `foo' in TeX.  Useful for distinguishing function symbols from other words in a
; sentence, since function symbols appear in Roman.
; Mnemonic: Q -- think Quoted.

; !Tfm, where fm is an Acl2 term, results in conventional mathematical
; notation for fm, but without any line breaks.
; Mnemonic: T -- think Term.

; !Vfoo means that foo is printed as is, but in typewriter font, and with
; special characters quoted.
; Mnemonic: V -- think Verbatim.

; ! followed by anything else is left alone, along with the exclamation mark.

; One can certainly use nqfmt2fmt on the result of running infix-file, but one
; must do so deliberately by first running infix-file, then renaming the
; resulting file, say foo.tex, to be foo.nqtex, and then running nqfmt2fmt.
; More convenient is to run infix-file with the :comment keyword parameter set to t,
; which causes infix-file first to generate a .nqtex file and second to run
; nqfmt2fmt on that file.

; If the :just-remove-! keyword is t, then a file named root.stripped is
; created, with all of our special ! commands options removed.

; Implementation note.  In all the cases we treat explicitly, the characters
; after !? are read with the Lisp function READ-PRESERVING-WHITESPACE, which
; is just the same as READ except that it doesn't gratuitously consume whitespace
; at the end of a READ.

; Warning: Because we use a relative of READ to obtain the forms immediately
; after the two character exclamation commands, the user must beware that if a
; form to be read extends for more than a line, and if a semicolon (comment
; character) is encountered on the next line, say at the beginning, READ will
; skip that line from the semicolon on, which may not be what the user intends.
; Thus it can be safer to use the #\| ... \|# construct for comments containing
; !, especially if one is in the habit of using the Emacs command M-x fill
; paragraph to rearrange paragraphs that begin with the comment delimiter
; semicolon.

  (let ((infl (type-file-name fl (fmt2fmt-extension just-remove-! *infix-mode*) t))
        (*print-pretty* nil)
        (orig-readtable (copy-readtable nil))
        (outfl (type-file-name fl (fmtfile-extension *infix-mode* nil) t))
        (a-very-rare-cons (cons nil nil))
        (count 1)
        (*readtable* (copy-readtable nil)))
    (smash-infix-readtable)
    (with-open-file
     (*standard-input* infl :direction :input)
     (with-open-file
      (*standard-output* outfl :direction :output :if-exists :rename-and-delete)
      (sloop for c = (read-char *standard-input* nil a-very-rare-cons)
	     (let (form)
	       (cond ((catch 'taboverflow
			(cond ((eq c a-very-rare-cons) (return-from nqfmt2fmt outfl))
			      ;; The Latex indexing routines may insert new exclamation points!!!
			      ((eql c #\\)
			       (cond ((skip-index-entries) nil)
				     ;; I am inserting a gigantic hack here because
				     ;; I can't figure out a more principled, simple
				     ;; way to get the effect I want in LaTeX.
				     ;; The problem is that at the end of a tabbing
				     ;; environment we often have two lines of the form:
				     ;;   ....  \\
				     ;;   \end{tabbing}
				     ;; which causes the event formatted in the tabbing
				     ;; env to appear to be followed by two blank lines
				     ;; rather than one.
				     ((adjust-tabbing-env) nil)
				     (t (pwrite-char c))))
			      ((eql c #\!)
			       (let ((c (read-char *standard-input* nil a-very-rare-cons)))
				 (cond ((eq c a-very-rare-cons)
					(pwrite-char #\!)
					(return-from nqfmt2fmt outfl)))
				 (case c
				   ((#\B #\b)
				    (or just-remove-!
					(let ((term (acl2-read-preserving-whitespace)))
					  (setq form term)
					  (bold-sym-printer term))))
				   ((#\C #\c)
				    (or just-remove-!
					(let ((term (acl2-read-preserving-whitespace)))
					  ;(handler-case
					  (eval term)
					   ;(error () (pwrite-char #\!)
						;     (pwrite-char c)
						;     (prin1 term)))
					  )))
				   ((#\E #\e)
				    (or just-remove-!
					(let ((term (acl2-read-preserving-whitespace)))
					  (setq form term)
					  (infix-event term))))
				   ((#\I #\i)
				    (or just-remove-!
					(let ((term (acl2-read-preserving-whitespace)))
					  (print-atom term))))
				   ((#\P #\p)
				    (or just-remove-!
					(let ((term (acl2-read-preserving-whitespace)))
					  (setq form term)
					  (infix-form term))))
				   ((#\Q #\q)
				    (or just-remove-!
					(let ((term (acl2-read-preserving-whitespace)))
					  (print-bare-function-name term))))
				   ((#\S #\s)
				    (or just-remove-!
					(let ((rest (acl2-read-preserving-whitespace)))
					  (sectionize rest just-remove-!))))
				   ((#\T #\t)
				    (or just-remove-!
					(let ((term (acl2-read-preserving-whitespace))
					      (*do-not-use-tabs* t))
					  (infix-form term))))
				   ((#\V #\v)
				    (or just-remove-!
					(let* ((*readtable* orig-readtable)
					       (term (acl2-read-preserving-whitespace))
					       (*do-not-use-tabs* t))
					  (quote-printer1 term))))
				   ((#\Space #\Tab #\Newline)
				    (pwrite-char #\!)
				    (pwrite-char c))
				   (otherwise
				    (or just-remove-!
					(pformat *terminal-io*
						 "Surprising character after ! ~a.~%" c))
				    (pwrite-char #\!)
				    (pwrite-char c)))))
			      ;; Let the user know we are making some kind
			      ;; of progress, every 60 lines
			      ((eql c #\Newline)
			       (if (= count 60)
				   (progn (format *terminal-io* "-") (setq count 1))
				   (incf count))
			       (pwrite-char c))
			      (t (pwrite-char c)))
			nil)
			(pformat *terminal-io*
				 "~%Sorry. Exceeded tabbing limit (2).
We can't handle this large a form in running text.  ~a needs hand massaging.~%"
				 (car form))
			(newline))))
		   )))))

(defvar balanced-parens '((#\( . #\))
			  (#\[ . #\])
			  (#\{ . #\})))

(defun sectionize (rest just-remove-!)
  ;; sleazy hack to make sections independent of mode (scribe or tex).
  (let (left right)
    (setq rest (intern (string-upcase rest)))
    (cond ((equal rest 'ection)
	   (setq left (read-char *standard-input* nil a-very-rare-cons))
	   (setq right (cdr (assoc left balanced-parens)))
	   (cond ((null right) (pprinc "section") (pwrite-char left))
		 (t (pprinc *begin-section-env*)
		    (sloop for c = (read-char *standard-input* nil a-very-rare-cons)
			   until (equal c right)
			   do (pwrite-char c))
		    (pprinc *end-section-env*))))
	  ((equal rest 'ubsection)
	   (setq left (read-char *standard-input* nil a-very-rare-cons))
	   (setq right (cdr (assoc left balanced-parens)))
	   (cond ((null right) (pprinc "subsection") (pwrite-char left))
		 (t (pprinc *begin-subsection-env*)
		    (sloop for c = (read-char *standard-input* nil a-very-rare-cons)
			   until (equal c right)
			   do (pwrite-char c))
		    (pprinc *end-subsection-env*))))
	  (t (or just-remove-!
		 (pformat *terminal-io* "Surprising string after !s ~s.~%" rest))
	     (pwrite-char #\!)
	     (pwrite-char #\s)
	     (pprinc rest)))))

(defun skip-index-entries ()
  ;; We are looking at a backslash. In Tex mode we need to skip to the end
  ;; of the entry, because we may add !'s.  In Scribe mode this is just NIL.
  nil)

(defun adjust-tabbing-env ()
  ;; We are looking at a backslash. In Tex mode we may need to replace
  ;;   ....  \\
  ;;   \end{tabbing}
  ;; with
  ;;   ....
  ;;   \end{tabbing}
  ;; NOTE: this will only work if NQFMT2FMT is run.
  ;; In Scribe mode this is just NIL.
  nil)


;                        INFIX SETTINGS

; This function should be called by the <mode>-init file, or may be called by
; the <mode>-theory file to override the <mode>-init settings.

(defun infix-settings
  (&key (mode                   nil p-mode)                  ; string ["SCRIBE","latex",...]
        (extension              nil p-extension)              ; string ["MSS","tex"]
        (op-location            nil p-op-location)            ; ['FRONT,'BACK]
        (comment-format         nil p-comment-format)         ; ['SMITH,'boyer]
        (format-!-in-comments   nil p-format-!-in-comments)   ; [T,nil]
        (acl2-format-comments   nil p-acl2-format-comments)   ; [T,nil]
        (acl2-format-doc-strings nil p-acl2-format-doc-strings) ; [T,nil]
        (eliminate-top-parens   nil p-eliminate-top-parens)   ; [T,nil]
        (eliminate-inner-parens nil p-eliminate-inner-parens) ; [T,nil]
        (no-index               nil p-no-index)               ; [t,NIL]
        (no-index-calls         nil p-no-index-calls))        ; [t,NIL,l]

  (if p-mode           (setq *infix-mode* mode))
  (if p-extension      (setq *mode-extension* extension))
  (if p-op-location    (setq *infix-op-location* op-location))
  (if p-comment-format (setup-comment-format comment-format))
  (if p-format-!-in-comments   (setq *nq-default* format-!-in-comments))
  (if p-acl2-format-comments   (setq *acl2-format-comments* acl2-format-comments))
  (if p-acl2-format-doc-strings (setq *acl2-format-doc-strings* acl2-format-doc-strings))
  (if p-eliminate-top-parens   (setq *top-parens-eliminable* eliminate-top-parens))
  (if p-eliminate-inner-parens (setq *top-parens-eliminable-default* eliminate-inner-parens))
  (if p-no-index
      (setq *do-not-index* no-index))
  (if p-no-index-calls
      (cond ((consp no-index-calls)
             (setq *do-not-index-calls-of* (append no-index-calls *do-not-index-calls-of*))
             (setq *do-not-index-calls* nil))
            (t  (setq *do-not-index-calls* no-index-calls)))))

(defun will-will-not (x)
  (if x "will" "will not"))

(defun show-infix-settings ()
  (format *terminal-io* "~%Expecting a .~a file to be mapped to .~a file to be formatted by ~a."
          infix-input-file-type *mode-extension* *infix-mode*)
  (format *terminal-io* "~%Multiline infix ops will be printed at the ~a of the line." *infix-op-location*)
  (format *terminal-io* "~%Comment format is ~a." *comment-format*)
  (format *terminal-io* "~%!formatting ~a be in effect." (will-will-not *nq-default*))
  (format *terminal-io* "~%Topmost parens ~a be suppressed." (will-will-not *top-parens-eliminable*))
  (format *terminal-io* "~%Inner parens ~a be suppressed." (will-will-not *top-parens-eliminable-default*))
  (format *terminal-io* "~%Index ~a be created." (will-will-not (not *do-not-index*)))
  (format *terminal-io* "~%Calls ~a be indexed." (will-will-not (not *do-not-index-calls*))))

(defun help-infix-settings ()
  (format *terminal-io* "~%To see current settings use (SHOW-INFIX-SETTINGS).
To change settings use INFIX-SETTINGS and supply the keyword arguments
for settings you wish to modify. Defaults in caps.~%")
  (format *terminal-io* "~%:mode           : string - formatting style [\"SCRIBE\",\"latex\",...]")
  (format *terminal-io* "~%:extension      : string - output file extension [\"MSS\",\"tex\"]")
  (format *terminal-io* "~%:op-location    : ['FRONT, 'back]
                - Multiline infix operators will be printed at the front
                - or back of the line according to this setting.")
  (format *terminal-io* "~%:comment-format : ['SMITH, 'boyer, 'cl] - Comment format")
  (format *terminal-io* "~%:no-index: [t,NIL] - Index will/will not be created")
  (format *terminal-io* "~%:no-index-calls : [t,NIL,1ist]
                - Calls will/will not be indexed.  If a list,
                - these functions will not be indexed.")
  (format *terminal-io* "~%:format-!-in-comments    : [T, nil] - !formatting in effect.")
  (format *terminal-io* "~%:acl2-format-comments    : [T, nil] - acl2 comment formatting.")
  (format *terminal-io* "~%:acl2-format-doc-strings : [T, nil] - acl2 formatting doc strings.")
  (format *terminal-io* "~%:eliminate-top-parens    : [T, nil] - Topmost parens suppressed.")
  (format *terminal-io* "~%:eliminate-inner-parens  : [T, nil] - Inner parens suppressed."))


;                             DEFINITION BY EXAMPLES

; Anyone extending the syntax by hand rather than by use of one of the make...
; functions ought also to add something to this list of examples to illustrate
; the new syntax.

(defun functify (l)
  ;; Removes redundant elements from an alist.
  (sloop for tail on l with ans
           do (cond ((null (assoc (car (car tail)) ans))
                     (push (car tail) ans)))
           finally (return (nreverse ans))))

(defvar *infix-test-directory*
  (concatenate 'string *infix-directory* "test/"))

(defun scrunch (l)
  (sloop for tail on l unless (member (car tail) (cdr tail))
	 collect (car tail)))

(defun print-examples (&optional mode)

; Illustrates the current syntax via a brief sample document.

  (cond (mode
	 (cond ((and (stringp mode)
		     (or (equal mode "latex")
			 (equal mode "scribe")))
		(setq *infix-mode* mode)
		(format t "~%Entering ~a mode.~%" *infix-mode*)
		(load-infix-init-file))
	       (t (error (format nil "Unknown mode ~s" mode)))))
	((stringp *infix-mode*)
         (format t "~%Entering ~a mode.~%" *infix-mode*)
         (load-infix-init-file))
        ((null *infix-mode*)
         (cond ((y-or-n-p "Enter Latex mode? ")
                (setq *infix-mode* "latex"))
               ((y-or-n-p "Enter Scribe mode? ")
                (setq *infix-mode* "scribe"))
               (t (setq *infix-mode* nil)))
	 (if *infix-mode*
	     (progn (format t "~%Entering ~a mode.~%" *infix-mode*)
		    (load-infix-init-file))))
        (t (format t "Remaining in ~a mode." *infix-mode*)))



  (let ((*print-pretty* nil)
        (*print-case* :downcase))
    (with-open-file
     (*standard-output* (type-file-name "infix-examples"
					(fmt2fmt-extension nil *infix-mode*) t)
                        :direction :output
                        :if-exists :rename-and-delete)
     (ppformat *example-prelude* *infix-mode*)
     (sloop for form in (functify *wired-in-infix-examples*)
              do (let ((*do-not-use-tabs* t))
                   (pprinc *begin-item*)
                   (quote-printer1 form)
                   (ppformat " is printed as ~%~%")
                   (infix-form form)
                   (ppformat ".~%")
                   (pprinc *end-item*))
              (ppformat "~%"))
     (pprinc *begin-item*)
     (ppformat "The remaining symbols that are printed specially are
described in the following table.")
     (pprinc *end-item*)
     (pprinc *end-enumerate-env*)
     (ppformat "~%~%")
     (let ((*tab-stack* t)
	   (table-number 1)
	   (example-number 1))
       ;; need to set *tab-list* non-nil to ensure (newline) works properly.
       (ppformat *begin-example-table* table-number)
       (sloop for form in
              (append (sloop for pair in (functify *atom-alist*)
			     collect (car pair))
                      (sloop for name in (scrunch *constant-ops*)
			     collect (list name))
                      (sloop for name in (scrunch *infix-ops*)
			     collect (list name 'x 'y))
                      (sloop for pair in (functify *negative-constant-table*)
			     collect (list 'not (list (car pair))))
                      (sloop for pair in (functify *negative-infix-table*)
			     collect (list 'not (list (car pair) 'x 'y)))
                      (sloop for name in (scrunch *unary-prefix-ops*)
			     collect (list name 'x))
                      (sloop for pair in (functify *negative-unary-prefix-table*)
			     collect (list 'not (list (car pair) 'x)))
                      (sloop for name in (scrunch *unary-suffix-ops*)
			     collect (list name 'x))
                      (sloop for pair in (functify *negative-unary-suffix-table*)
			     collect (list 'not (list (car pair) 'x)))
                      (sloop for name in (scrunch *unary-abs-ops*)
			     collect (list name 'x))
                      (sloop for pair in (functify *prefix-multiple-ops*)
			     collect (cons (car pair)
					   (sloop for i from 1 to (cdr pair) collect
						  (intern (format nil "X~a" i)))))
                      (sloop for pair in (functify *suffix-multiple-ops*)
			     collect (cons (car pair)
					   (sloop for i from 1 to (cdr pair) collect
						  (intern (format nil "X~a" i)))))
                      (sloop for pair in (functify *infix-multiple-ops*)
			     collect (cons (car pair)
					   (sloop for i from 1 to (1+ (cdr pair)) collect
						  (intern (format nil "X~a" i))))))
              do (let ((*do-not-use-tabs* t))
		   (cond ((> example-number *example-table-size*)
			  (ppformat *end-example-table*)
			  (ppformat *begin-example-table* table-number)
			  (setq example-number 1)))
                   (quote-printer1 form)
                   (pprinc *column-separator*)
                   (infix-form form)
		   (new-tab-row nil)
		   (line-return)
		   (setq table-number (+ 1 table-number))
		   (setq example-number (+ 1 example-number))
                   (setq *infix-loc* *left-margin*)))
       (ppformat *end-example-table*))
     (pprinc *example-postlude*))
    (nqfmt2fmt "infix-examples")))


; The following should be modified to interact with the vaiables that set
; parens printing.  In particular, this seems to be the piece of precedence that
; is most easily screwed up.

;                                      NOT

; The following code is for the special handling of NOT, which involves diving
; into the term negated to turn a predicate into one that has a slash through
; it.  We advise that the casual user not touch this.

(defun not-printer (term)
  (let (x)
    (cond ((atom (cadr term))
           (default-unary-prefix-printer term *neg-str*))
          ((setq x (assoc (car (cadr term)) *negative-constant-table*))
           (pprinc (cadr x)))
          ((setq x (assoc (car (cadr term)) *negative-infix-table*))
           (default-infix-printer (cadr term) (cadr x)))
          ((setq x (assoc (car (cadr term)) *negative-unary-prefix-table*))
           (default-unary-prefix-printer (cadr term) (cadr x)))
          ((setq x (assoc (car (cadr term)) *negative-unary-suffix-table*))
           (default-unary-suffix-printer (cadr term) (cadr x)))
          (t (default-unary-prefix-printer term *neg-str*)))))

(declare-fn-printer not (function not-printer))

;; REAL INITIALIZATION.  Used to reinitialize during clean-up-everything
(setq *save-fn-alist* *fn-alist*)


;                          USER MODIFIABLE TABLE SETUP

; It is easy to augment, or even to modify, the syntax by calling one of the
; make-... functions illustrated below.  The non-initial arguments to these
; make-...  functions are strings to be printed by Latex to generate operators
; and other noise words when printing a term whose function symbol is the
; intial argument of the call to make-...

; make-infix-op, make-unary-prefix-op, and make-unary-suffix-op take an
; optional second argument, *neg-str*, which indicates how to print an the
; negation of an application of the function symbol in question.

; In TeX or Latex, one can do astonishingly clever things.  But the strings
; that we have in mind should do nothing clever involving motion, they should
; only result in characters being placed at the current location.  While being
; printed, the strings will be passed no arguments or information about the
; context in which printing is to take place. Typically, these strings should
; be nothing more than instructions to print a single symbol. The strings are
; processed in `math mode', and in fact, they are auomatically embedded in
; $...$.

; None of the operators below are built into this printer anywhere else except
; by the code below.  The meaning of `not', defined above, is wired in because
; it gives the meaning to the optional *neg-str* arguments.


;                                     CONSTANT-OPS

; Sometimes you want to print a function as a constant, particularly if it is one.
; (make-constant-op op str) causes (op ..) to print as str.

;                                     INFIX-OPS

; infix-ops (infix operators) should be function symbols of two or more
; arguments for which it is desired that one symbol come out between every
; adjacent pair of arguments.  E.g., invoking (make-infix-op plus "+") causes
; the term (plus a b c d) to be printed as (a $+$ b $+$ c $+$ d).  Invoking
; (make-infix-op equal "=" "\\not=") causes the term (equal x y) to be printed
; as (x $=$ y) and it also causes the term (not (equal x y)) to be printed as
; (x $\not= y).

; Thus, for example, if one introduces a new function, say join, and wants to
; print terms of the form (join x y) as (x \bigtriangledown y), cf. p. 44 of
; the Latex manual, then one should invoke:

;   (make-infix-op join "\\bigtriangledown")

; from Lisp.  That is all that need be done to cause infix-file to subsequently
; print `join' terms this way.

; Note that throughout the following examples, we have used two backslashes to
; get one because, in Common Lisp, backslash is a character for quoting other
; characters.

; Examples of make-infix-op are contained in latex-theory.lisp.  Look for INFIX OPERATORS.


;             UNARY-PREFIX-OPS, UNARY-SUFFIX-OPS, and UNARY-ABS-OPS

; Use make-unary-prefix-op and make-unary-suffix-op only for function symbols
; of one argument.  The string str (or *neg-str*) will be printed before or
; after the argument.

; For more examples, see latex-theory.lisp.

; unary-suffix-ops should be unary function symbols.

; (make-unary-suffix-op foo x str) makes (foo x) print as (x $str$).

; Examples of make-unary-suffix-op.

; unary-prefix-ops should be unary function symbols.

; (make-unary-prefix-op foo str) makes (foo x) print as ($str$ x).

; unary-abs-ops should be unary function symbols.

; To create syntax like that for absolute value, use (make-unary-absolute-op
; lhs-str rhs-str), where lhs-str and rhs-str are the strings to print on the
; left and right of the argument.  (make-unary-abs-op foo str1 str2) makes (foo
; x) print as (str1 x str2).  See the example for abs below.


;                           SOME POSSIBLE EXTENSIONS


;; (simple-extension)           ; see latex-theory.lisp
;; (dmg-syntax)                 ; see latex-theory.lisp

; Undoing.  To cause applications of a function symbol fn to be printed in the
; default way, i.e., fn(x, y), invoke (clean-up 'fn).


;; TESTING

;; Lines in the test file are the following form:

;;    filename
;; or (filename mode)
;; or (filename mode comment)

;; Comment defaults to T.

(defvar *mode-list* '("latex" "scribe"))

(defvar *test-file* "testfile")

;; Better to use test-directory
;; (defun test-infix ()
;;   (let ((files (read-file-list *test-file*)))
;;     (sloop for test in files
;;              do (cond ((or (stringp test)
;;                            (and (consp test) (null (cdr test))))
;;                        ;; "file" or (file)
;;                        (if (consp test) (setq test (car test)))
;;                        (sloop for mode in *mode-list*
;;                                 do (progn
;; 				     (format *terminal-io*
;; 					     "~%Translating ~a in ~a mode.~%" test mode)
;; 				     (infix-file test :mode mode :comment t))))
;;                       ((and (consp test) (eql (length test) 2))
;;                        ;; (file mode)
;;                        (format *terminal-io*
;; 			       "~%Translating ~a in ~a mode.~%" (car test) (cadr test))
;;                        (infix-file (car test) :mode (cadr test) :comment t))
;;                       ((and (consp test) (eql (length test) 3))
;;                        ;; (file mode comment)
;;                        (format *terminal-io*
;;                                "~%Translating ~a in ~a mode, with comment = ~a.~%"
;;                                (car test) (cadr test) (caddr test))
;;                        (infix-file (car test) :mode (cadr test) :comment (caddr test)))
;;                       (t (format *terminal-io* "~%BAD TEST FILE SPEC: ~ad.~%" test))))))

;; (defun read-file-list (file)
;;   (cond ((null (probe-file file))
;;          (format t "~%Failed to find file: ~a~%" file))
;;         (t (with-open-file
;;             (*standard-input* file :direction :input)
;;             (sloop for form = (readx *standard-input* nil a-very-rare-cons nil)
;;                      until (eq form a-very-rare-cons)
;;                      collect form)))))


;; Testing functions

;; MODIFY and USE:
;; mks: script test.log
;; mks:
;; >(load "infix")
;; >(test-directory "scribe")
;; >(bye)
;; mks: foreach f (*.mss)
;; ? scribe $f
;; ? end
;; mks: ^D
;; mks: sed -e s/^V^M// test.log > test-scribe.log

(defun test-directory (mode &optional directory (comment nil comment-p))
  ;; ONLY EXPECTING mode = "latex" or "scribe"
  (let ((type (if (string= mode "latex") "tex" "mss"))
	(dir (or directory *infix-test-directory*))
	;; Default testing excludes nqfmt2fmt translations
	;; for latex, since it is so much more sensitive
	;; to character weirdness.
	(com (if (string= mode "latex") nil t)))
    (if comment-p (setq com comment))
    (setq dir (concatenate 'string dir "*.lisp"))
    (mapc (function (lambda (f)
                      (format *terminal-io* "~%Infixing ~a.lisp." (pathname-name f))
                      (if (probe-file (make-pathname :type type :defaults f))
                          (format *terminal-io* "~%~a.~a already exists. Skipping.~%"
				  (pathname-name f) type)
                          (infix-file f :mode mode))))
          (directory dir))))

(format *terminal-io* "~%~%--- Do (help-infix-settings) for help. ---~%~%")


#| Note on math printing from LSmith.

Bill and I had troubles printing with infix because nesting math modes
is not allowed in latex. Our latex output from infix is filled with

     {\ifmmode <form>\else$<form>$\fi}

with the two <form>s identical and often containing more ifmmodes.

I happened across a solution to this problem in the Latex manual.

     \mbox{$<form>$}

works whether of not we are currently in mathmode. In other words, it
is possible to nest math modes in latex after all. This feature is
documented in section 3.4.1, Defining Commands, in the Latex manual.

|#
