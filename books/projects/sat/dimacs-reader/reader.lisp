;; Copyright (c) 2016, Regents of the University of Texas
;;
;; License: The MIT License (MIT)
;;
;;   Permission is hereby granted, free of charge, to any person
;;   obtaining a copy of this software and associated documentation
;;   files (the "Software"), to deal in the Software without
;;   restriction, including without limitation the rights to use,
;;   copy, modify, merge, publish, distribute, sublicense, and/or sell
;;   copies of the Software, and to permit persons to whom the
;;   Software is furnished to do so, subject to the following
;;   conditions:
;;
;;   The above copyright notice and this permission notice shall be
;;   included in all copies or substantial portions of the Software.
;;
;;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;   EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
;;   OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;   NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;   HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;   WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
;;   OTHER DEALINGS IN THE SOFTWARE.
;;
;; Original author: Nathan Wetzler <nathan.wetzler@gmail.com>

;; Last Modified:  2016-10-16 17:05


;; ============================= PACKAGE =============================
;; Package declaration.
(in-package "DIMACS-READER")


;; ============================ INCLUDES =============================

;; This book defines the b* macro for easy bindings in function definitions.
(include-book "std/util/bstar" :dir :system)

;; This book introduces a macro called "define" that is a more powerful way to
;; define functions (as opposed to "defun").
(include-book "std/util/define" :dir :system)

;; This book is part of the standard I/O books and will introduce a mechanism
;; to read a file as a list of bytes.
(include-book "std/io/read-file-bytes" :dir :system)

;; This book contains various functions and theorems about string operations.
(include-book "std/strings/top" :dir :system)


;; XDOC support
(include-book "xdoc/top" :dir :system)
;; (include-book "xdoc/debug" :dir :system)


;; ===================================================================
;; ============================= READER ==============================
;; ===================================================================

(defxdoc DIMACS-READER
  :parents (acl2::projects)
  :short "A reader and parser for satisfiability instances stored in the DIMACS
  SAT format."
  )

(xdoc::order-subtopics
 DIMACS-READER
 (;Background-And-Description
  ))


;; =================== BACKGROUND AND DESCRIPTION ====================

(defsection Background-And-Description
  :extension DIMACS-READER
  ;; :parents (DIMACS-READER)
  ;; :short ""
  :long
"<h2>Background and Description</h2>

<p>Satisfiability (SAT) instances are typically stored on disk in a format
called the DIMACS SAT/CNF format.  The name DIMACS comes from the Rutgers
University research group Center for Discrete Mathematics and Theoretical
Computer Science (DIMACS).  The DIMACS group hosted several challenges in the
1990s on algorithms and implementations related to graphs and other NP hard
problems (<a href='http://dimacs.rutgers.edu/Challenges/'>
http://dimacs.rutgers.edu/Challenges/</a>).  In 1992, the Second DIMACS
Implementation Challenge included problems on graph cliques, graph coloring,
and satisfiability.  The original DIMACS format for satisfiablity problems
comes from this challenge, although it's hard to find evidence of this
today.  (In fact, there used to be a document online describing the format used
in this challenge, but that has since been removed.  It's quite difficult to
find any mention of the format or challenge in the literature either.  This
makes the reason behind the <i>DIMACS</i> part of the satisfiability format
somewhat mysterious.)</p>

<p>The SAT community has since taken ownership of this format and uses versions
of it for SAT competitions.  The format seems to change at times, but is always
based around the DIMACS CNF format.  Recent competitions use the definition
from the 2009 SAT Competition (<a
href='http://www.satcompetition.org/2009/format-benchmarks2009.html'>
http://www.satcompetition.org/2009/format-benchmarks2009.html</a>).  This
specification is far from complete, however, and it is unfortunate there is no
research paper that defines and evaluates a SAT problem specification.</p>

<p>Here, we define a reader and parser for files in the DIMACS SAT format.  The
general strategy will be to read the entire file into a list of bytes.  This
list will be interpreted as a list of integers (but this could be changed to a
list of bytes or list of signed bytes, etc.).  We then parse this list into
either a list of clauses (which are lists of integers) or a flat list of
integers (where clauses are separated by zeroes).  If the parsing fails, an
error string is generated.  This string contains a call stack of sorts, so the
offending part of the file can be located.  If the string is empty, then
parsing succeeded.</p>

<h3>Related work:</h3>
<p>Jared Davis and Sol Swords have defined a DIMACS writer and a SAT solver
output reader for their SATLINK books.  Additional information can be found
at: books/centaur/satlink/.</p>
")

;; ====================== FORMAT SPECIFICATION =======================

(defsection Format-Specification
  :extension DIMACS-READER
  ;; :parents (DIMACS-READER)
  ;; :short ""
  :long
"<h2>Format Specification</h2>

Here, we define, in English, our interpretation of the most common
specification for the DIMACS CNF format.  A DIMACS CNF file is divided into two
sections: the preamble and the clauses section.

The preamble is divided into two subsections: the comment section and the
problem line.  The comment section is optional and comes before the problem
line, if it exists.  The comment section is composed of comment lines where
each comment line begins with the prefix <tt>c </tt> (that is, the character
<tt>c</tt> followed by a space).  There is no whitespace before the prefix.

The problem line is the second part of the preamble and is mandatory.  The
problem line begins with the prefix <tt>p </tt> (the character <tt>p</tt> followed by a
space).  (As an aside, the <tt>p</tt> is short for <i>problem</i>.)  Again, there is no
whitespace before the prefix.  This prefix is followed by the string <tt>cnf </tt>
indicating the problem is in the conjunctive normal form (CNF) format.
(There are other formats from the DIMACS group with other problem identifiers.)
The problem line then contains a positive integer indicating the highest
variable used in the formula.  Finally, the problem line ends in a positive
integer indicating the number of clauses in the formula.  An example problem
line looks like <tt>p cnf 4 8</tt> which indicated the CNF formula described in
the clauses section uses a maximum of 4 variables and contains exactly 8
clauses.

The clauses section immediately follows the problem line and occupies the
remainder of the file.  A CNF formula consists of a conjunction of clauses
which are disjunctions of literals.  The ANDs and ORs of the formula are
implicit in the DIMACS CNF representation.  The clauses section is a series of
integers separated by any amount of whitespace including spaces, tabs, and
newlines.  Zero is a special integer that indicates the end of a clause.  Each
clause consists of literals, indicated by positive and negative integers,
followed by a zero.  The absolute value of any integer indicates the variable.
Positive integers indicate the positive literal and negative integers indicate
the negative literal, which is the negation of the associated variable.  An
example clause in the DIMACS CNF format is <tt>1 -2 -3 0</tt> which represents
the logical clause <tt>x_1 OR NOT x_2 OR NOT x_3</tt>.

Furthermore, variables cannot exceed the maximum variable provided on the
problem line, and the number of clauses in the clauses section must be exactly
the number provided on the problem line.  Both literals and variables must be
unique in each clause.  Clauses must be unique sets in the formula: no two
clauses may be permuatations of each other.  The empty clause is
permissable (but makes the formula trivially unsatisfiable when
present).  (None of these features are checked in the parser below.  They would
require a formula validator and hashing mechanism to examine the formula
during/after parsing.)
")

;; ====================== SPECIFICATION ISSUES =======================

(defsection Specification-Issues
  :extension DIMACS-READER
  ;; :parents (DIMACS-READER)
  ;; :short ""
  :long
"<h2>Specification Issues</h2>

There are several inconsistencies in documented DIMACS CNF specifications.  It
would be nice to support each of these variations with parser options.

In most representations, the comments subsection is limited to the beginning of
the file.  However, some specifications allow for comments to be interspersed
throughout the clauses sections.  This encourages organizational descriptions
of sets of clauses.

Usually, the components of a problem line are separated by one space.  However,
some specifications allow for multiple spaces (but not newlines) inside the
problem line.

The maximum variable in the problem line exists to indicate the amount of space
to allocate in a solver.  This can be quite inefficient for benchmarks where
many variables are unused in the formula.  These types of benchmarks exist
because some encoding schemes might not be compact.  Some specifications
require each variable from 1 to the maximum variable appear in the clauses
section.  One application of this parser might be to report unused variables or
condense a formula that skips certain variable numberings.

Some specifications require that each clause occupy a single line of the file.
That is, every clause-terminating zero should be followed by a newline and the
whitespace separating literals cannot contain newlines.  This makes parsing a
bit easier and makes the file easier to debug.  This requirement is probably
the most common difference between DIMACS CNF specifications.

While the most common specification disallows tautologies (clauses that contain
both a literal and its negation), many specifications allow these clauses.

Duplicate literals within a single clause could be allowed, but it seems like a
poor idea.

Some specifications disallow the empty clause (a clause with no literals before
the terminating zero).

A specification could allow the number of clauses in the clauses section to be
different from number listed on the problem line.
")

;; ====================== FUTURE SPECIFICATIONS ======================

(defsection Future-Specifications
  :extension DIMACS-READER
  ;; :parents (DIMACS-READER)
  ;; :short ""
  :long
"<h2>Future Specifications</h2>

Donald Knuth proposes a new format/specification for satisfiability instances
in his new volume of The Art of Computer Programming
(<a href='http://www-cs-faculty.stanford.edu/~uno/taocp.html'>
http://www-cs-faculty.stanford.edu/~uno/taocp.html</a>).  The DIMACS format is
not very human-friendly.  Knuth's <tt>SAT</tt> format allows for human-readable
formulas.  In this format, variables can be strings of (up to eight?) ASCII
characters, negation is represented by a tilde character (~), whitespace is
limited to one space character, clauses are limited to one per line, and
clauses are not zero-terminated.
")



;; ========================== ERROR STRINGS ==========================

(define empty-stringp ;emptyp? shorter
  ((string stringp))
  :returns (empty booleanp)
  (null (explode string))

  ///

  (defthm consp-append1
    (implies (consp x)
             (consp (append x y)))
    :rule-classes :type-prescription)

  (defthm consp-append2
    (implies (consp y)
             (consp (append x y)))
    :rule-classes :type-prescription)

  (defthm consp-implies-not-empty-stringp-implode
    (implies (consp x)
             (not (empty-stringp (implode x))))))


(defconst *empty-string* "")
;(defconst *es* "") ;shorter???


(define create-error-string
  ((function-name symbolp)
   (message stringp)
   (old-error stringp))
  :returns (new-error stringp)
  (b* ((new-error (symbol-name function-name))
       (new-error (string-append new-error " :: "))
       (new-error (string-append new-error message))
       (new-error (implode (append (explode new-error)
                                   (list #\Newline))))
       (new-error (string-append new-error old-error)))
      new-error)

  ///
  (defthm not-empty-stringp-create-error-string
    (not (empty-stringp (create-error-string function-name
                                             message
                                             old-error)))))

(defmacro error-string-define (message
                               &optional (old-error '*empty-string*))
  `(create-error-string acl2::__function__ ,message ,old-error))



(define char-list-to-integer-list
  ((char-list character-listp))
  :returns (integer-list integer-listp :hyp :guard)
  (if (atom char-list)
      char-list
    (cons (char-code (car char-list))
          (char-list-to-integer-list (cdr char-list)))))

(define string-to-integer-list
  ((string stringp))
  :returns (integer-list integer-listp :hyp :guard)
  (char-list-to-integer-list (explode string)))


(define read-line1
  ((content integer-listp))
  :returns (mv (err stringp)
               (line integer-listp :hyp :guard)
               (new-content integer-listp :hyp :guard))
  (b* (((if (atom content))
        (mv (error-string-define "End of list.")
            nil
            content))
       ((if (equal (car content) (char-code #\Newline)))
        (mv *empty-string* (list (car content)) (cdr content)))
       ((mv err line new-content)
        (read-line1 (cdr content))))
      (mv err (cons (car content) line) new-content))

  ///
  (defthm read-line1-no-error-implies-smaller-content
    (implies (empty-stringp (mv-nth 0 (read-line1 content)))
             (< (len (mv-nth 2 (read-line1 content)))
                (len content)))
    :rule-classes :linear))

(define skip-line
  ((content integer-listp))
  :returns (mv (err stringp)
               (new-content integer-listp :hyp :guard))
  (b* (((mv err ?line new-content)
        (read-line1 content)))
      (mv err new-content))

  ///
  (defthm skip-line-no-error-implies-smaller-content
    (implies (empty-stringp (mv-nth 0 (skip-line content)))
             (< (len (mv-nth 1 (skip-line content)))
                (len content)))
    :rule-classes :linear))

(define trim-whitespace
  ((content integer-listp))
  :returns (new-content integer-listp :hyp :guard)
  (b* (((if (atom content))
        content)
       ((if (member (car content) (list (char-code #\Space)
                                        (char-code #\Tab)
                                        (char-code #\Newline))))
        (trim-whitespace (cdr content))))
      content)

  ///
  (defthm trim-whitespace-at-least-as-small-content
    (<= (len (trim-whitespace content))
        (len content))
    :rule-classes :linear))


(define char-code-to-digit
  ((char-code integerp))
  :returns (mv (err stringp)
               (digit integerp :hyp :guard))
  (b* ((adjusted-char-code (- char-code 48))
       ((if (and (<= 0 adjusted-char-code)
                 (<= adjusted-char-code 9)))
        (mv *empty-string* adjusted-char-code)))
      (mv (error-string-define "Not a digit.")
          char-code))

  ///
  (defthm char-code-to-digit-no-error-implies-digit
    (implies (and (integerp char-code)
                  (empty-stringp (mv-nth 0 (char-code-to-digit char-code))))
             (and (natp (mv-nth 1 (char-code-to-digit char-code)))
                  (<= 0 (mv-nth 1 (char-code-to-digit char-code)))
                  (<= (mv-nth 1 (char-code-to-digit char-code)) 9)))
    :rule-classes :forward-chaining))


(define parse-natural-my
  ((content integer-listp)
   &optional
   ((base natp) '0))
  :returns (mv (err stringp)
               (num natp :hyp :guard :rule-classes :type-prescription)
               (new-content integer-listp :hyp :guard))
  (b* (((if (atom content))
        (mv (error-string-define "End of list.")
            base
            content))
       ((mv err digit)
        (char-code-to-digit (car content)))
       ((if (not (empty-stringp err)))
        (mv (error-string-define "Bad char." err)
            base
            content))
       ((mv ?err num new-content)
        (parse-natural-my (cdr content) (+ (* base 10) digit))))
      (mv *empty-string* num new-content))

  ///
  (defthm parse-natural-my-fn-at-least-as-small-content
    (<= (len (mv-nth 2 (parse-natural-my-fn content base)))
        (len content))
    :rule-classes :linear)

  (defthm parse-natural-my-at-least-as-small-content
    (<= (len (mv-nth 2 (parse-natural-my content)))
        (len content))
    :rule-classes :linear)

  (defthm parse-natural-my-fn-no-error-implies-smaller-content
    (implies (empty-stringp (mv-nth 0 (parse-natural-my-fn content base)))
             (< (len (mv-nth 2 (parse-natural-my-fn content base)))
                (len content)))
    :rule-classes :linear)

  (defthm parse-natural-my-no-error-implies-smaller-content
    (implies (empty-stringp (mv-nth 0 (parse-natural-my content)))
             (< (len (mv-nth 2 (parse-natural-my content)))
                (len content)))
    :rule-classes :linear))



(define parse-integer-my
  ((content integer-listp))
  :returns (mv (err stringp)
               (num integerp :hyp :guard)
               (new-content integer-listp :hyp :guard))
  (b* (((if (atom content))
        (mv (error-string-define "End of list.")
            0
            content))
       (signed (equal (car content) (char-code #\-)))
       (sign-mult (if signed -1 1))
       (content (if signed (cdr content) content))
       ((mv err num new-content)
        (parse-natural-my content)))
      (mv err (* sign-mult num) new-content))

  ///
  (defthm parse-integer-my-at-least-as-small-content
    (<= (len (mv-nth 2 (parse-integer-my content)))
        (len content))
    :rule-classes :linear)

  (defthm parse-integer-my-no-error-implies-smaller-content
    (implies (empty-stringp (mv-nth 0 (parse-integer-my content)))
             (< (len (mv-nth 2 (parse-integer-my content)))
                (len content)))
    :rule-classes :linear))


(define parse-char
  ((content integer-listp)
   (char characterp))
  :returns (mv (success symbolp)
               (new-content integer-listp :hyp :guard))
  (b* (((if (atom content))
        (mv nil content))
       ((if (equal (car content) (char-code char)))
        (mv t (cdr content))))
      (mv nil content))

  ///
  (defthm parse-char-success-implies-smaller-content
    (implies (mv-nth 0 (parse-char content char))
             (< (len (mv-nth 1 (parse-char content char)))
                (len content)))
    :rule-classes :linear))

(define parse-char-list
  ((content integer-listp)
   (char-list character-listp))
  :returns (mv (success symbolp)
               (new-content integer-listp :hyp :guard))
  (b* (((if (atom char-list))
        (mv t content))
       ((if (atom content))
        (mv nil content))
       ((if (equal (car content) (char-code (car char-list))))
        (parse-char-list (cdr content) (cdr char-list))))
      (mv nil content))

  ///
  (defthm parse-char-list-success-implies-smaller-content
    (implies (and (consp char-list)
                  (mv-nth 0 (parse-char-list content char-list)))
             (< (len (mv-nth 1 (parse-char-list content char-list)))
                (len content)))
    :rule-classes :linear))


(define parse-string
  ((content integer-listp)
   (string stringp))
  :returns (mv (success symbolp)
               (new-content integer-listp :hyp :guard))
  (parse-char-list content (explode string))

  ///
  (defthm parse-string-success-implies-smaller-content
    (implies (and (stringp string)
                  (not (equal string ""))
                  (mv-nth 0 (parse-string content string)))
             (< (len (mv-nth 1 (parse-string content string)))
                (len content)))
    :rule-classes :linear))


(define parse-comments
  ((content integer-listp))
  :returns (mv (err stringp)
               (new-content integer-listp :hyp :guard))
  :measure (len content)
  (b* (((if (atom content))
        (mv (error-string-define "End of list.")
            nil))
       ((mv success new-content)
        (parse-string content "c "))
       ((if (not success))
        (mv *empty-string* content))
       ((mv err new-content)
        (skip-line new-content))
       ((if (not (empty-stringp err)))
        (mv err new-content)))
      (parse-comments new-content)))

(define parse-spaces
  ((content integer-listp))
  :returns (mv (success symbolp)
               (new-content integer-listp :hyp :guard))
  (b* (((if (atom content))
        (mv nil content))
       ((unless (member (car content) (list (char-code #\Space)
                                            (char-code #\Tab))))
        (mv nil content))
       ((mv ?success new-content)
        (parse-spaces (cdr content))))
      (mv t new-content))

  ///
  (defthm parse-spaces-at-least-as-small-content
    (<= (len (mv-nth 1 (parse-spaces content)))
        (len content))
    :rule-classes :linear)

  (defthm parse-spaces-success-implies-smaller-content
    (implies (mv-nth 0 (parse-spaces content))
             (< (len (mv-nth 1 (parse-spaces content)))
                (len content)))
    :rule-classes :linear))


(define parse-whitespace
  ((content integer-listp))
  :returns (mv (success symbolp)
               (new-content integer-listp :hyp :guard))
  (b* (((if (atom content))
        (mv nil content))
       ((unless (member (car content) (list (char-code #\Space)
                                            (char-code #\Tab)
                                            (char-code #\Newline))))
        (mv nil content))
       ((mv ?success new-content)
        (parse-whitespace (cdr content))))
      (mv t new-content))

  ///
  (defthm parse-whitespace-at-least-as-small-content
    (<= (len (mv-nth 1 (parse-whitespace content)))
        (len content))
    :rule-classes :linear)

  (defthm parse-whitespace-success-implies-smaller-content
    (implies (mv-nth 0 (parse-whitespace content))
             (< (len (mv-nth 1 (parse-whitespace content)))
                (len content)))
    :rule-classes :linear))




(define parse-problem-line
  ((content integer-listp))
  :returns (mv (err stringp)
               (num-vars natp :hyp :guard)
               (num-clauses natp :hyp :guard)
               (new-content integer-listp :hyp :guard))
  (b* (((if (atom content))
        (mv (error-string-define "End of list.")
            0 0 nil))
       ((mv success new-content)
        (parse-string content "p cnf"))
       ((if (not success))
        (mv (error-string-define "No problem statement.")
            0 0 content))
       ((mv success new-content)
        (parse-spaces new-content))
       ((if (not success))
        (mv (error-string-define "Malformed statement.")
            0 0 content))
       ((mv err num-vars new-content)
        (parse-natural-my new-content))
       ((if (not (empty-stringp err)))
        (mv (error-string-define "Bad vars." err)
            0 0 content))
       ((mv success new-content)
        (parse-spaces new-content))
       ((if (not success))
        (mv (error-string-define "Malformed statement.")
            0 0 content))
       ((mv err num-clauses new-content)
        (parse-natural-my new-content))
       ((if (not (empty-stringp err)))
        (mv (error-string-define "Bad clauses." err)
            0 0 content))
       ((mv err new-content)
        (skip-line new-content))
       ((if (not (empty-stringp err)))
        (mv err 0 0 content)))
      (mv *empty-string* num-vars num-clauses new-content)))

(define parse-preamble
  ((content integer-listp))
  :returns (mv (err stringp)
               (num-vars natp :hyp :guard)
               (num-clauses natp :hyp :guard)
               (new-content integer-listp :hyp :guard))
  (b* (((mv err new-content)
        (parse-comments content))
       ((if (not (empty-stringp err)))
        (mv err 0 0 new-content)))
      (parse-problem-line new-content)))

(define encode
  ((n integerp))
  :returns (val integerp :hyp :guard)
  (if (< n 0)
      (1+ (* -2 n))
    (* 2 n)))

(define parse-clause
  ((content integer-listp))
  :returns (mv (err stringp)
               (clause integer-listp :hyp :guard)
               (new-content integer-listp :hyp :guard))
  :measure (len content)
  (b* (((if (atom content))
        (mv (error-string-define "End of list.")
            nil nil))
       ((mv err num new-content1)
        (parse-integer-my content))
       ((if (not (empty-stringp err)))
        (mv (error-string-define "Bad integer." err)
            nil content))
       ((if (equal num 0))
        (mv *empty-string* nil new-content1))
       ((mv success new-content2)
        (parse-whitespace new-content1))
       ((if (not success))
        (mv (error-string-define "No separator.")
            nil new-content1))
       ((mv err clause new-content3)
        (parse-clause new-content2)))
      (mv err (cons (encode num) clause) new-content3))

  ///
  (defthm parse-clause-at-least-as-small-content
    (<= (len (mv-nth 2 (parse-clause content)))
        (len content))
    :rule-classes :linear)

  (defthm parse-clause-no-error-implies-smaller-content
    (implies (empty-stringp (mv-nth 0 (parse-clause content)))
             (< (len (mv-nth 2 (parse-clause content)))
                (len content)))
    :rule-classes :linear))


(define integer-list-listp
  ((x))
  :returns (result booleanp)
  (if (atom x)
      (null x)
    (and (integer-listp (car x))
         (integer-list-listp (cdr x))))

  ///
  (defthm integer-list-listp-cons
    (implies (and (integer-listp x)
                  (integer-list-listp y))
             (integer-list-listp (cons x y)))))


(define parse-formula
  ((content integer-listp))
  :returns (mv (err stringp)
               (formula integer-list-listp :hyp :guard)
               (new-content integer-listp :hyp :guard))
  :measure (len content)
  (b* (((if (atom content))
        (mv (error-string-define "End of list.")
            nil nil))
       (new-content (trim-whitespace content))
       ((mv err clause new-content)
        (parse-clause new-content))
       ((if (not (empty-stringp err)))
        (mv (error-string-define "Bad clause." err)
            nil content))
       ((if (atom new-content))
        (mv *empty-string* (list clause) new-content))
       ((mv success new-content)
        (parse-whitespace new-content))
       ((if (not success))
        (mv (error-string-define "No trailing whitespace after clause.")
            nil new-content))
       ((if (atom new-content))
        (mv *empty-string* (list clause) new-content))
       ((mv err formula new-content)
        (parse-formula new-content)))
      (mv err (cons clause formula) new-content)))




(define parse-dimacs
  ((content integer-listp))
  :returns (mv (err stringp)
               (num-vars natp :hyp :guard)
               (num-clauses natp :hyp :guard)
               (formula integer-list-listp :hyp :guard))
  (b* (((mv err num-vars num-clauses new-content)
        (parse-preamble content))
       ((if (not (empty-stringp err)))
        (mv (error-string-define "Preamble error.")
            num-vars num-clauses nil))
       ((mv err formula ?new-content)
        (parse-formula new-content)))
      (mv err num-vars num-clauses formula)))




(set-state-ok t)

(define read-dimacs
  ((filename stringp)
   (state state-p))
  :returns (mv (contents integer-listp)
               (state state-p :hyp :guard))
  (b* (((mv contents state)
        (acl2::read-file-bytes filename state))
       ((if (stringp contents))
        (mv nil state)))
      (mv contents state)))

(define read-and-parse-with-state
  ((filename stringp)
   (state state-p))
  :returns (mv (err stringp)
               (num-vars natp)
               (num-clauses natp)
               (formula integer-list-listp)
               (state state-p :hyp :guard))
  (b* (((mv contents state)
        (read-dimacs filename state))
       ((mv err num-vars num-clauses formula)
        (parse-dimacs contents)))
      (mv err num-vars num-clauses formula state)))

(defmacro read-and-parse (filename)
  `(read-and-parse-with-state ,filename state))

(set-state-ok nil)


; Post processing for unique, tautology, etc


;; ===================================================================


(defthm integer-listp-append
  (implies (and (integer-listp x)
                (integer-listp y))
           (integer-listp (append x y))))

(defthm integer-listp-rev
  (implies (integer-listp x)
           (integer-listp (rev x))))

;; (defthm integer-listp-append
;;   (equal (integer-listp (append x y))
;;          (and (integer-listp x)
;;               (integer-listp y))))

(define parse-formula-flat
  ((content integer-listp))
  :returns (mv (err stringp)
               (formula integer-listp :hyp :guard)
               (new-content integer-listp :hyp :guard))
  :measure (len content)
  (b* (((if (atom content))
        (mv (error-string-define "End of list.")
            nil nil))
       (new-content (trim-whitespace content))
       ((mv err clause new-content)
        (parse-clause new-content))
       ((if (not (empty-stringp err)))
        (mv (error-string-define "Bad clause." err)
            nil content))
       ((if (atom new-content))
        (mv *empty-string* (append clause (list 0)) new-content))
       ((mv success new-content)
        (parse-whitespace new-content))
       ((if (not success))
        (mv (error-string-define "No trailing whitespace after clause.")
            nil new-content))
       ((if (atom new-content))
        (mv *empty-string* (append clause (list 0)) new-content))
       ((mv err formula new-content)
        (parse-formula-flat new-content)))
      (mv err (append (append clause (list 0)) formula) new-content)))




(define parse-dimacs-flat
  ((content integer-listp))
  :returns (mv (err stringp)
               (num-vars natp :hyp :guard)
               (num-clauses natp :hyp :guard)
               (formula integer-listp :hyp :guard))
  (b* (((mv err num-vars num-clauses new-content)
        (parse-preamble content))
       ((if (not (empty-stringp err)))
        (mv (error-string-define "Preamble error.")
            num-vars num-clauses nil))
       ((mv err formula ?new-content)
        (parse-formula-flat new-content)))
      (mv err num-vars num-clauses formula)))


(set-state-ok t)  ;; The use of STATE is OK.

(define read-dimacs-flat
  ((filename stringp)
   (state state-p))
  :returns (mv (contents integer-listp)
               (state state-p :hyp :guard))
  (b* (((mv contents state)
        (acl2::read-file-bytes filename state))
       ((if (stringp contents))
        (mv nil state)))
      (mv contents state)))

(define read-and-parse-with-state-flat
  ((filename stringp)
   (state state-p))
  :returns (mv (err stringp)
               (num-vars natp)
               (num-clauses natp)
               (formula integer-listp)
               (state state-p :hyp :guard))
  (b* (((mv contents state)
        (read-dimacs-flat filename state))
       ((mv err num-vars num-clauses formula)
        (parse-dimacs-flat contents)))
      (mv err num-vars num-clauses formula state)))

(defmacro read-and-parse-flat (filename)
  `(read-and-parse-with-state-flat ,filename state))

(set-state-ok nil)


;; ===================================================================

(defthm integer-list-listp-rev
  (implies (integer-list-listp x)
           (integer-list-listp (rev x)))
  :hints (("Goal" :in-theory (enable integer-list-listp))))


(define parse-formula-count-clauses1
  ((err stringp)
   (num-clauses natp)
   (formula integer-list-listp)
   (content integer-listp))
  :returns (mv (err stringp)
               (num-clauses natp :hyp :guard)
               (formula integer-list-listp :hyp :guard)
               (new-content integer-listp :hyp :guard))
  :measure (len content)
  (b* (((if (atom content))
        (mv (error-string-define "End of list.")
            num-clauses formula nil))
       (new-content (trim-whitespace content))
       ((mv clause-err clause new-content)
        (parse-clause new-content))
       ((if (not (empty-stringp clause-err)))
        (mv (error-string-define "Bad clause." clause-err)
            num-clauses formula content))
       ((if (atom new-content))
        (mv *empty-string*
            (1+ num-clauses)
            (cons clause formula)
            new-content))
       ((mv success new-content)
        (parse-whitespace new-content))
       ((if (not success))
        (mv (error-string-define "No trailing whitespace after clause.")
            num-clauses formula new-content))
       ((if (atom new-content))
        (mv *empty-string*
            (1+ num-clauses)
            (cons clause formula)
            new-content)))
      (parse-formula-count-clauses1 err
                                    (1+ num-clauses)
                                    (cons clause formula)
                                    new-content)))

(define parse-formula-count-clauses
  ((content integer-listp))
  :returns (mv (err stringp)
               (num-clauses natp :hyp :guard)
               (formula integer-list-listp :hyp :guard)
               (new-content integer-listp :hyp :guard))
  (b* (((mv err num-clauses formula new-content)
        (parse-formula-count-clauses1 *empty-string* 0 nil content)))
      (mv err num-clauses (rev formula) new-content)))

(define parse-proof
  ((content integer-listp))
  :returns (mv (err stringp)
               (num-clauses natp :hyp :guard)
               (formula integer-list-listp :hyp :guard))
  (b* (((mv err num-clauses formula ?new-content)
        (parse-formula-count-clauses content)))
      (mv err num-clauses formula)))


(set-state-ok t)  ;; The use of STATE is OK.

(define read-proof
  ((filename stringp)
   (state state-p))
  :returns (mv (contents integer-listp)
               (state state-p :hyp :guard))
  (b* (((mv contents state)
        (acl2::read-file-bytes filename state))
       ((if (stringp contents))
        (mv nil state)))
      (mv contents state)))

(define read-and-parse-proof-with-state
  ((filename stringp)
   (state state-p))
  :returns (mv (err stringp)
               (num-clauses natp)
               (formula integer-list-listp)
               (state state-p :hyp :guard))
  (b* (((mv contents state)
        (time$ (read-proof filename state)))
       ((mv err num-clauses formula)
        (time$ (parse-proof contents))))
      (mv err num-clauses formula state)))

(defmacro read-and-parse-proof (filename)
  `(read-and-parse-proof-with-state ,filename state))

(set-state-ok nil)


;; ===================================================================

(define parse-formula-flat-count-clauses1
  ((err stringp)
   (num-clauses natp)
   (formula integer-listp)
   (content integer-listp))
  :returns (mv (err stringp)
               (num-clauses natp :hyp :guard)
               (formula integer-listp :hyp :guard)
               (new-content integer-listp :hyp :guard))
  :measure (len content)
  (b* (((if (atom content))
        (mv (error-string-define "End of list.")
            num-clauses formula nil))
       (new-content (trim-whitespace content))
       ((mv clause-err clause new-content)
        (parse-clause new-content))
       ((if (not (empty-stringp clause-err)))
        (mv (error-string-define "Bad clause." clause-err)
            num-clauses formula content))
       ((if (atom new-content))
        (mv *empty-string*
            (1+ num-clauses)
            (append (append (list 0) (rev clause))
                    formula)
            new-content))
       ((mv success new-content)
        (parse-whitespace new-content))
       ((if (not success))
        (mv (error-string-define "No trailing whitespace after clause.")
            num-clauses formula new-content))
       ((if (atom new-content))
        (mv *empty-string*
            (1+ num-clauses)
            (append (append (list 0) (rev clause))
                    formula)
            new-content)))
      (parse-formula-flat-count-clauses1 err
                                         (1+ num-clauses)
                                         (append (append (list 0) (rev clause))
                                                 formula)
                                         new-content)))

(define parse-formula-flat-count-clauses
  ((content integer-listp))
  :returns (mv (err stringp)
               (num-clauses natp :hyp :guard)
               (formula integer-listp :hyp :guard)
               (new-content integer-listp :hyp :guard))
  (b* (((mv err num-clauses formula new-content)
        (parse-formula-flat-count-clauses1 *empty-string* 0 nil content)))
      (mv err num-clauses (rev formula) new-content)))

(define parse-proof-flat
  ((content integer-listp))
  :returns (mv (err stringp)
               (num-clauses natp :hyp :guard)
               (formula integer-listp :hyp :guard))
  (b* (((mv err num-clauses formula ?new-content)
        (parse-formula-flat-count-clauses content)))
      (mv err num-clauses formula)))


(set-state-ok t)  ;; The use of STATE is OK.

(define read-proof-flat
  ((filename stringp)
   (state state-p))
  :returns (mv (contents integer-listp)
               (state state-p :hyp :guard))
  (b* (((mv contents state)
        (acl2::read-file-bytes filename state))
       ((if (stringp contents))
        (mv nil state)))
      (mv contents state)))

(define read-and-parse-proof-with-state-flat
  ((filename stringp)
   (state state-p))
  :returns (mv (err stringp)
               (num-clauses natp)
               (formula integer-listp)
               (state state-p :hyp :guard))
  (b* (((mv contents state)
        (time$ (read-proof-flat filename state)))
       ((mv err num-clauses formula)
        (time$ (parse-proof-flat contents))))
      (mv err num-clauses formula state)))

(defmacro read-and-parse-proof-flat (filename)
  `(read-and-parse-proof-with-state-flat ,filename state))

(set-state-ok nil)

;; ===================================================================

;; (defttag t)

;; (remove-untouchable acl2::create-state t)

;; (defun read-and-parse-local-state (filename)
;;   ;; This function requires the STATE, so we use the next form
;;   (with-local-state
;;    ;; "Powerful" macro that provides access to the state, but
;;    ;; requires the two events above.
;;    (mv-let (err num-vars num-clauses formula state)
;;            (read-and-parse filename)
;;            (mv err num-vars num-clauses formula))))

;; Example Read -- filename can be changed.

;; (defconst *f*
;;   (mv-let (err num-vars num-clauses formula)
;;           (read-and-parse-local-state "rbcl_xits_07_UNSAT.cnf")
;;           (list err num-vars num-clauses formula)))
