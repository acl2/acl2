; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "lexstate")
(include-book "utils")
(include-book "chartypes")
(include-book "../../util/warnings")
(include-book "../../util/commentmap")
(local (include-book "../../util/arithmetic"))

(local (defthm true-listp-of-cdr
           (implies (consp x)
                    (equal (true-listp (cdr x))
                           (true-listp x)))))

(defxdoc lexer
  :parents (loader)
  :short "Verilog Lexer."

  :long "<p>Lexers are often implemented as a @('get-token') routine, the idea
being that, at the parser's request, the lexer should read just enough from the
input stream to provide the next token.</p>

<p>In contrast, our top-level lexer function, @(see vl-lex), processes the
whole list of input characters that are produced by the @(see preprocessor),
and generates a whole list of @(see tokens) as output.  (It also generates a
list of @(see warnings), e.g., when integer constants are truncated.)</p>

<p>This is obviously inefficient.  On the other hand, memory is abundant and
lexing is almost intrinsically @('O(n)').  Meanwhile, our approach allows our
parser to be state-free, with arbitrary lookahead, and also gives us the
convenience of list-based (rather than file-based) debugging and unit testing
throughout the whole process.</p>

<p>A basic correctness result for our lexer is:</p>

@(thm vl-tokenlist->etext-of-vl-lex-tokens)

<p>That is, whenever the lexer successfully tokenizes its input @('echars'),
you could flatten the resulting tokens to recover exactly the input text.</p>

<p>To make the above theorem possible, our lexer produces tokens even for
whitespace and comments.  These tokens are not suitable as input for the @(see
parser), and should be removed using @(see vl-kill-whitespace-and-comments)
before parsing begins.</p>

<p>Since we often want to use VL to transform or simplify Verilog source code,
we don't throw away comments&mdash;instead, we collect them up into a @(see
vl-commentmap-p).  We that later use comment maps to re-attach the comments to
the right parts of the tree; see for instance @(see vl-ppc-module).</p>")

(defmacro def-token/remainder-thms (fn &key
                                       (formals '(echars))
                                       (extra-tokenhyp 't)
                                       (extra-appendhyp 't)
                                       (extra-strongcounthyp 't)
                                       (token-n '0)
                                       (remainder-n '1))
  (let ((mksym-package-symbol (pkg-witness "VL")))
    `(defsection ,(mksym fn '-token/remainder-thms)
       :parents (,fn)
       :short "Basic token/remainder theorems automatically added with
               @(see vl::def-token/remainder-thms)."

       (local (in-theory (enable ,fn)))

       (defthm ,(mksym 'vl-token-p-of- fn)
         (implies (and (force (vl-echarlist-p echars))
                       ,extra-tokenhyp)
                  (equal (vl-token-p (mv-nth ,token-n (,fn . ,formals)))
                         (if (mv-nth ,token-n (,fn . ,formals))
                             t
                           nil))))

       (defthm ,(mksym 'true-listp-of- fn)
         (equal (true-listp (mv-nth ,remainder-n (,fn . ,formals)))
                (true-listp echars))
         :rule-classes ((:rewrite)
                        (:type-prescription
                         :corollary
                         (implies (true-listp echars)
                                  (true-listp (mv-nth ,remainder-n (,fn . ,formals))))))
         :hints(("Goal" :in-theory (disable (force)))))

       (defthm ,(mksym 'vl-echarlist-p-of- fn)
         (implies (force (vl-echarlist-p echars))
                  (equal (vl-echarlist-p (mv-nth ,remainder-n (,fn . ,formals)))
                         t)))

       (defthm ,(mksym 'append-of- fn)
         (implies (and (mv-nth ,token-n (,fn . ,formals))
                       (force (vl-echarlist-p echars))
                       ,extra-appendhyp)
                  (equal (append (vl-token->etext (mv-nth ,token-n (,fn . ,formals)))
                                 (mv-nth ,remainder-n (,fn . ,formals)))
                         echars)))

       (defthm ,(mksym 'no-change-loser-of- fn)
         (implies (not (mv-nth ,token-n (,fn . ,formals)))
                  (equal (mv-nth ,remainder-n (,fn . ,formals))
                         echars)))

       (defthm ,(mksym 'acl2-count-of- fn '-weak)
         (<= (acl2-count (mv-nth ,remainder-n (,fn . ,formals)))
             (acl2-count echars))
         :rule-classes ((:rewrite) (:linear))
         :hints(("Goal" :in-theory (disable (force)))))

       (defthm ,(mksym 'acl2-count-of- fn '-strong)
         (implies (and (mv-nth ,token-n (,fn . ,formals))
                       ,extra-strongcounthyp)
                  (< (acl2-count (mv-nth ,remainder-n (,fn . ,formals)))
                     (acl2-count echars)))
         :rule-classes ((:rewrite) (:linear))
         :hints(("Goal" :in-theory (disable (force))))))))


(defsection comments
  :parents (lexer)
  :short "Support for Verilog comments."

  :long "<p>Both Verilog-2005 and SystemVerilog-2012 support two forms of
comments.  Single-line comments that start with @('//') and end with a newline.
Multi-line comments start with @('/*') and end with @('*/').</p>

<p>Many lexers would skip past comments (and whitespace).  We instead create
@(':vl-comment') tokens.  This is generally meant to allow us to preserve
comments as we process and pretty-print the source code.</p>

<p>BOZO things to check:</p>

<ul>

<li>How do other Verilog tools handle @('// foo [carriage-return] bar
[newline]')?  Do they consider the carriage return to be a newline?
Both standards present the grammar rule as:
@({
     one_line_comment ::= // comment_text \\n
})
which perhaps suggests that maybe we're doing it right.
</li>

<li>How do other Verilog tools react to a single-line comment that ends with a
backslash before the newline?  Is that regarded as a line continuation?</li>

</ul>")

(define vl-lex-oneline-comment
  :parents (comments)
  :short "Try to match a @('// ...') style comment."
  ((echars (and (vl-echarlist-p echars)
                (true-listp echars))))
  :returns (mv token/nil remainder)
  (b* (((unless (vl-matches-string-p "//" echars))
        (mv nil echars))
       ((mv & prefix remainder)
        (vl-read-through-literal *nls* (cddr echars)))
       (etext
        (list* (first echars) (second echars) prefix))
       (token (make-vl-plaintoken :etext etext :type :vl-comment)))
      (mv token remainder)))

(def-token/remainder-thms vl-lex-oneline-comment)


(define vl-lex-block-comment
  :parents (comments)
  :short "Try to match a @('/* ... */') style comment."
  ((echars (and (vl-echarlist-p echars)
                (true-listp echars))))
  :returns (mv token/nil remainder)
  (b* (((unless (vl-matches-string-p "/*" echars))
        (mv nil echars))
       ((mv successp prefix remainder)
        (vl-read-through-literal "*/" (cddr echars)))
       ((unless successp)
        (mv (cw "Lexer error (~s0): block comment is never closed.~%"
                (vl-location-string (vl-echar->loc (car echars))))
            echars))
       (etext
        (list* (first echars) (second echars) prefix))
       (token (make-vl-plaintoken :etext etext :type :vl-comment)))
      (mv token remainder)))

(def-token/remainder-thms vl-lex-block-comment)


(defsection identifiers
  :parents (lexer)
  :short "Handling of identifiers."

  :long "<p>The grammars of Verilog-2005 and SystemVerilog-2012 agree on:</p>

@({
    identifier ::= simple_identifier
                 | escaped_identifier

    simple_identifier ::= [ a-zA-Z_ ] { [a-zA-Z0-9_$ ] }
      (no embedded spaces)
})

<p>The Verilog-2005 grammar presents the rule for escaped identifiers as:</p>

@({
    escaped_identifier ::= \ { any non-whitespace character } white_space
})

<p>However, Section 3.7.1 of the Verilog-2005 standard appears to contradict
the above definition.  It says that escaped identifiers \"provide a means of
including any of the <i>printable ASCII characters</i> in an identifier (the
decimal values 33 through 126...).  Section 5.6.1 of the SystemVerilog-2012
standard says the same thing, and its grammar has been updated with this
clarification:</p>

@({
    escaped_identifier ::= \ { any printable non-whitespace character } white_space
})

<p>We therefore restrict the name characters in escaped identifiers to the
printable ascii characters, i.e., characters whose codes are 33-126.</p>


<h5>Whitespace Minutia</h5>

<p>Per Section 3.7.1 of Verilog-2005, the leading backslash character and the
terminating whitespace character are not \"considered to be part of the
identifier\", i.e., @('\\cpu3') is treated the same as @('cpu3').  Section
5.6.1 of the SystemVerilog-2012 standard says the same thing.  Note that the
Verilog grammar treats EOF as a whitespace, so we allow an escaped identifier
to be closed with EOF -- there just isn't a whitespace character at the end of
the PREFIX in that case.</p>

<p>Perhaps a reason for including this whitespace is found on page 351 of the
Verilog-2005 standard.  A macro with arguments is introduced like @('`define
max(a,b) ...') with no whitespace between its name (an identifier) and the
first paren of the argument list.  So if you wanted to have an escaped
identifier as the name of a macro with arguments, how would you know when the
identifier ended and the argument list began?  Making the escaped identifier
include a whitespace seems like a dirty trick to accomplish this.  In any
event, we don't support macros with arguments anyway, but we go ahead and
include the whitespace in case such support is ever added.</p>


<h5>Empty Identifiers</h5>

<p>I have not found anything in the spec which explicitly prohibits the empty
escaped identifier, i.e., @('\\<whitespace>'), from being used.  Nevertheless,
I exclude it on the grounds that is suspicious and Cadence does not permit it
either.  Allowing it would make end-of-define even more complicated to properly
support in the @(see preprocessor).</p>


<h3>Notes about Honsing Identifiers</h3>

<p>We are always careful to @(see hons) the names of the identifier tokens we
create.  One reason it's a good idea is that identifiers are often repeated
many times, so making the actual string part a hons lets us use only one copy
of the string.  The other big reason is that identifier names are often used in
fast-alist lookups, and if the string isn't a hons, then @(see hons-get) will
have to hons it first anyway.  So, by honsing as we create the identifier
token, we potentially avoid a lot of repeated, redundant honsing later
on.</p>")

(define vl-read-simple-identifier
  :parents (identifiers)
  :short "Try to match a simple identifier (or any keyword!)."
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)
  (if (or (not (consp echars))
          (not (vl-simple-id-head-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-simple-id-tail echars))
  ///
  (local (defrule lemma
           (b* (((mv prefix ?remainder)
                 (vl-read-while-simple-id-tail echars)))
             (implies (vl-simple-id-head-p (vl-echar->char (first echars)))
                      prefix))
           :enable vl-read-while-simple-id-tail))

  (defrule vl-read-simple-identifier-when-vl-simple-id-head-p
    (b* (((mv prefix ?remainder)
          (vl-read-simple-identifier echars)))
      (implies (vl-simple-id-head-p (vl-echar->char (first echars)))
               prefix))
    :enable vl-simple-id-head-p
    :disable ((force))))

(def-prefix/remainder-thms vl-read-simple-identifier)


(define vl-read-escaped-identifier
  :parents (identifiers)
  ((echars vl-echarlist-p))
  :returns (mv (name/nil "On success, a string with the interpreted name
                          (similar to prefix, but without the leading
                          backslash or trailing whitespace character.)"
                         (equal (stringp name/nil)
                                (if name/nil t nil))
                         :hyp :fguard)
               prefix remainder)
  (b* (((when (or (not (consp echars))
                  (not (eql (vl-echar->char (car echars)) #\\))))
        (mv nil nil echars))
       ((mv tail remainder)
        (vl-read-while-printable-not-whitespace (cdr echars)))
       ((unless tail)
        ;; Attempt to use the empty identifier?
        (mv nil nil echars))
       ((unless (consp remainder))
        ;; EOF-terminated identifier -- we allow this since the grammar
        ;; says that EOF is a whitespace character
        (mv (hons-copy (vl-echarlist->string tail))
            (cons (car echars) tail)
            remainder)))
    ;; Regular whitespace-terminated identifier
    (mv (hons-copy (vl-echarlist->string tail))
        (cons (car echars) (append tail (list (car remainder))))
        (cdr remainder)))
  ///
  (defthm vl-read-escaped-identifier-under-iff
    (b* (((mv name prefix ?remainder)
          (vl-read-escaped-identifier echars)))
      (iff prefix name))))

(def-prefix/remainder-thms vl-read-escaped-identifier
  :prefix-n 1
  :remainder-n 2)


(define vl-lex-escaped-identifier
  :parents (identifiers)
  ((echars vl-echarlist-p))
  :returns (mv token/nil remainder)
  :long "<p>Per 3.7.2, escaped identifiers cannot be keywords.  So we do not
 need to consult the keyword table.</p>"
  (b* (((unless (and (consp echars)
                     (eql (vl-echar->char (car echars)) #\\)))
        (mv nil echars))
       ((mv name prefix remainder)
        (vl-read-escaped-identifier echars))
       ((unless name)
        (mv (cw "Lexer error (~s0): stray backslash?~%"
                (vl-location-string (vl-echar->loc (car echars))))
            echars))
       (token (make-vl-idtoken :etext prefix :name name)))
    (mv token remainder))
  ///
  (def-token/remainder-thms vl-lex-escaped-identifier))


(define vl-lex-simple-identifier-or-keyword
  :parents (lexer)
  :short "Match either a keyword or an ordinary, simple identifier."
  ((echars vl-echarlist-p     "The characters we're lexing.")
   (table  vl-keyword-table-p "The table of keywords we're currently using."))
  :returns (mv token/nil remainder)
  (b* (((unless (and (consp echars)
                     (vl-simple-id-head-echar-p (car echars))))
        (mv nil echars))
       ((mv prefix remainder)
        (vl-read-simple-identifier echars))
       (str     (hons-copy (vl-echarlist->string prefix)))
       (lookup  (vl-keyword-lookup str table))
       (token   (if lookup
                    (make-vl-plaintoken :etext prefix :type lookup)
                  (make-vl-idtoken :etext prefix :name str))))
      (mv token remainder)))

(def-token/remainder-thms vl-lex-simple-identifier-or-keyword
  :formals (echars table)
  :extra-tokenhyp (vl-keyword-table-p table)
  :extra-appendhyp (vl-keyword-table-p table))



;; --------------------------- I AM HERE ------------------------------

;; system_function_identifier ::= $[ a-zA-Z0-9_$ ] { [ a-zA-Z0-9_$ ] }
;; system_task_identifier     ::= $[ a-zA-Z0-9_$ ] { [ a-zA-Z0-9_$ ] }


(define vl-lex-system-identifier ((echars vl-echarlist-p))
  :returns (mv token/nil remainder)
  (b* (((unless (and (consp echars)
                     (eql (vl-echar->char (car echars)) #\$)))
        (mv nil echars))
       ((mv tail remainder)
        (vl-read-while-simple-id-tail (cdr echars)))
       ((unless tail)
        (mv (cw "Lexer error (~s0): stray dollar sign?~%"
                (vl-location-string (vl-echar->loc (car echars))))
            echars))
       (etext (cons (car echars) tail))
       (name  (hons-copy (vl-echarlist->string etext)))
       (token (make-vl-sysidtoken :etext etext :name name)))
    (mv token remainder))
  ///
  (def-token/remainder-thms vl-lex-system-identifier))





(define vl-read-string-escape-sequence
  :parents (vl-lex-string)
  :long "<p>We assume we are reading a string literal from ECHARS and have just
found a backslash at (CAR ECHARS).  We try to read and interpret the escape
sequence which follows.  The CHAR we return is the ACL2 characterp indicated by
this escape sequence on success, or nil otherwise.</p>"

  ((echars (and (vl-echarlist-p echars)
                (consp echars)
                (equal (vl-echar->char (car echars)) #\\))))

  :returns (mv char/nil prefix remainder)

  :prepwork
  ((local (defthm vl-echar-digit-value-upper-bound
            (implies (force (vl-echar-p echar))
                     (< (vl-echar-digit-value echar 8)
                        8))
            :rule-classes :linear
            :hints(("Goal" :in-theory (enable vl-echar-digit-value)))))

   (local (in-theory (enable vl-echarlist-unsigned-value
                             vl-echarlist-unsigned-value-aux))))

  (b* (((unless (consp (cdr echars)))
        (mv nil nil echars))
       (echar1 (first echars))
       (echar2 (second echars)))
    (case (vl-echar->char echar2)
      (#\n (mv #\Newline (list echar1 echar2) (cddr echars)))
      (#\t (mv #\Tab     (list echar1 echar2) (cddr echars)))
      (#\\ (mv #\\       (list echar1 echar2) (cddr echars)))
      (#\" (mv #\"       (list echar1 echar2) (cddr echars)))
      (t
       (b* ((echar3 (and (consp (cddr echars))
                         (third echars)))
            (echar4 (and (consp (cddr echars))
                         (consp (cdddr echars))
                         (fourth echars)))
            ((unless (vl-echar-digit-value echar2 8))
             (mv (cw "Lexer error (~s0): invalid escape sequence: ~s1.~%"
                     (vl-location-string (vl-echar->loc (car echars)))
                     (vl-echarlist->string (list echar1 echar2)))
                 nil echars))
            ((when (or (not echar3)
                       (not (vl-echar-digit-value echar3 8))))
             ;; One octal digit.  Cannot overflow.
             (mv (code-char (vl-echar-digit-value echar2 8))
                 (list echar1 echar2)
                 (cddr echars)))
            ((when (or (not echar4)
                       (not (vl-echar-digit-value echar4 8))))
             ;; Two octal digits.  Cannot overflow.
             (mv (code-char (vl-echarlist-unsigned-value (list echar2 echar3) 8))
                 (list echar1 echar2 echar3)
                 (cdddr echars)))
            ;; Three octal digits.  We must check for overflow.
            (value (vl-echarlist-unsigned-value (list echar2 echar3 echar4) 8))
            ((when (< 255 value))
             (mv (cw "Lexer error (~s0): invalid escape sequence: ~s1.~%"
                     (vl-location-string (vl-echar->loc (car echars)))
                     (vl-echarlist->string (list echar1 echar2 echar3 echar4)))
                 nil echars)))
         (mv (code-char value)
             (list echar1 echar2 echar3 echar4)
             (cddddr echars))))))

  ///

  (def-prefix/remainder-thms vl-read-string-escape-sequence
    :prefix-n 1
    :remainder-n 2)

  (local (in-theory (enable vl-read-string-escape-sequence)))

  (defthm characterp-of-vl-read-string-escape-sequence
    (equal (characterp (mv-nth 0 (vl-read-string-escape-sequence echars)))
           (if (mv-nth 0 (vl-read-string-escape-sequence echars))
               t
             nil)))

  (defthm second-of-vl-read-string-escape-sequence-under-iff
    (iff (mv-nth 1 (vl-read-string-escape-sequence echars))
         (mv-nth 0 (vl-read-string-escape-sequence echars)))))



(define vl-read-string-aux
  :parents (vl-lex-string)
  :short "Main loop for reading string literals."
  ((echars vl-echarlist-p "Characters we're reading")
   (eacc "Accumulator for actual characters read (e.g., #\\n),
          as extended characters")
   (vacc "Accumulator for interpreted characters read (e.g., a newline),
          as ordinary characters"))
  :returns (mv (error "nil on success, stringp error message on failure."
                      (equal (stringp error)
                             (if error t nil)))
               eacc vacc remainder)
  (b* (((unless (consp echars))
        (mv "the file ends before the string is closed." eacc vacc echars))
       (echar1 (first echars))
       (char1  (vl-echar->char echar1)))
    (case char1
      (#\Newline
       (mv "the line ends before the string is closed." eacc vacc echars))
      (#\"
       (mv nil (cons echar1 eacc) vacc (rest echars)))
      (#\\
       (mv-let (char prefix remainder)
         (vl-read-string-escape-sequence echars)
         (if (not char)
             (mv "the string contains an invalid escape sequence."
                 eacc vacc echars)
           (vl-read-string-aux remainder
                               (revappend prefix eacc)
                               (cons char vacc)))))
      (t
       (vl-read-string-aux (cdr echars)
                           (cons echar1 eacc)
                           (cons char1 vacc)))))
  ///
  (defthm vl-echarlist-p-of-vl-read-string-aux
    (implies (and (force (vl-echarlist-p echars))
                  (force (vl-echarlist-p eacc)))
             (vl-echarlist-p (mv-nth 1 (vl-read-string-aux echars eacc vacc)))))

  (defthm true-listp-of-vl-read-string-aux-vacc
    (equal (true-listp (mv-nth 1 (vl-read-string-aux echars eacc vacc)))
           (true-listp eacc)))

  (defthm character-listp-of-vl-read-string-aux-eacc
    (implies (and (force (vl-echarlist-p echars))
                  (force (character-listp vacc)))
             (character-listp (mv-nth 2 (vl-read-string-aux echars eacc vacc)))))

  (defthm vl-echarlist-p-of-vl-read-string-aux-remadiner
    (implies (force (vl-echarlist-p echars))
             (vl-echarlist-p (mv-nth 3 (vl-read-string-aux echars eacc vacc)))))

  (defthm true-listp-of-vl-read-string-aux-remainder
    (equal (true-listp (mv-nth 3 (vl-read-string-aux echars eacc vacc)))
           (true-listp echars)))

  (defthm revappend-of-vl-read-string-aux
    (equal (append (rev (mv-nth 1 (vl-read-string-aux echars eacc vacc)))
                   (mv-nth 3 (vl-read-string-aux echars eacc vacc)))
           (append (rev eacc)
                   echars)))

  (defthm acl2-count-of-vl-read-string-aux-weak
    (<= (acl2-count (mv-nth 3 (vl-read-string-aux echars eacc vacc)))
        (acl2-count echars))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-vl-read-string-aux-strong
    (implies (not (mv-nth 0 (vl-read-string-aux echars eacc vacc)))
             (< (acl2-count (mv-nth 3 (vl-read-string-aux echars eacc vacc)))
                (acl2-count echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force))))))


(define vl-read-string
  :parents (vl-lex-string)
  ((echars "Characters we're reading, which we assume begin with a double-quote."
           (and (vl-echarlist-p echars)
                (consp echars)
                (equal (vl-echar->char (car echars)) #\"))))
  :returns (mv (str? "NIL on failure.  A stringp with the interpreted
                      characters from the string literal otherwise.
                      That is, we'll have already expanded things like
                      @('\\n') into proper newline characters."
                      (equal (stringp str?)
                             (if str? t nil)))
               prefix remainder)
  (b* (((mv err eacc vacc remainder)
        (vl-read-string-aux (cdr echars) nil nil))
       ((when err)
        (mv (cw "Lexer error (~s0) while reading string: ~s1.~%"
                (vl-location-string (vl-echar->loc (car echars)))
                err)
            nil echars)))
    (mv (str::rchars-to-string vacc)
        (cons (car echars) (reverse eacc))
        remainder))
  ///
  (encapsulate
   ()
   (local (in-theory (disable character-listp-of-vl-read-string-aux-eacc)))
   (def-prefix/remainder-thms vl-read-string
     :prefix-n 1
     :remainder-n 2))

  (local (in-theory (enable vl-read-string)))

  (defthm second-of-vl-read-string-under-iff
    (iff (mv-nth 1 (vl-read-string echars))
         (mv-nth 0 (vl-read-string echars)))))



(define vl-lex-string
  :parents (lexer)
  :short "Lexing of string literals."

  ((echars vl-echarlist-p))
  :returns (mv token/nil remainder)

  :long "<p>Strings literals in Verilog are enclosed in \"double quotes\" and
cannot span multiple lines.  They may contain the following escape sequences,
outlined in Section 3.6.</p>

@({
   \n          Newline
   \t          Tab
   \\          Backslash
   \"          Quote
   \ddd        Character by octal code of 1-3 digits
})

<p>The characters referenced by the \ddd format must be between 0 and 377,
since 377 is octal for 255.  Any larger values are an error since they do not
refer to a valid ASCII character.</p>"

  (b* (((unless (and (consp echars)
                     (eql (vl-echar->char (car echars)) #\")))
        (mv nil echars))
       ((mv string prefix remainder)
        (vl-read-string echars))
       ((unless string)
        (mv nil echars))
       (token (make-vl-stringtoken :etext prefix :expansion string)))
      (mv token remainder))
  ///
  (def-token/remainder-thms vl-lex-string))


(defxdoc numbers
  :parents (lexer)
  :short "Handling of numbers."
  :long "<p>Verilog's numbers are quite complicated.  We begin working through
  the grammar for them \"from the bottom up.\"</p>

@({
    z_digit ::= z | Z | ?

    x_digit ::= x | X

    hex_digit ::=
        x_digit | z_digit | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
      | a | b | c | d | e | f | A | B | C | D | E | F

    octal_digit ::= x_digit | z_digit | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7

    binary_digit ::= x_digit | z_digit | 0 | 1

    decimal_digit ::= 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9

    non_zero_decimal_digit ::= 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
})")



; Embedded spaces are prohibited in the following productions.
;
; hex_base ::= '[s|S]h | '[s|S]H
;
; octal_base ::= '[s|S]o | '[s|S]O
;
; binary_base ::= '[s|S]b | '[s|S]B
;
; decimal_base ::= '[s|S]d | '[s|S]D

(define vl-read-hex-base ((echars (and (vl-echarlist-p echars)
                                       (true-listp echars))))
  :inline t
  (vl-read-some-literal (list "'h" "'H" "'sh" "'sH" "'Sh" "'SH") echars)
  ///
  (def-prefix/remainder-thms vl-read-hex-base))

(define vl-read-octal-base ((echars (and (vl-echarlist-p echars)
                                         (true-listp echars))))
  :inline t
  (vl-read-some-literal (list "'o" "'O" "'so" "'sO" "'So" "'SO") echars)
  ///
  (def-prefix/remainder-thms vl-read-octal-base))

(define vl-read-binary-base ((echars (and (vl-echarlist-p echars)
                                          (true-listp echars))))
  :inline t
  (vl-read-some-literal (list "'b" "'B" "'sb" "'sB" "'Sb" "'SB") echars)
  ///
  (def-prefix/remainder-thms vl-read-binary-base))

(define vl-read-decimal-base ((echars (and (vl-echarlist-p echars)
                                           (true-listp echars))))
  :inline t
  (vl-read-some-literal (list "'d" "'D" "'sd" "'sD" "'Sd" "'SD") echars)
  ///
  (def-prefix/remainder-thms vl-read-decimal-base))


;; Holy fuxor fixme

(defun vl-orcar-mv2s-fn (forms)
  (if (consp forms)
      (if (consp (cdr forms))
          `(mv-let (a-for-vl-orcar-mv2s-do-not-use-elsewhere
                    b-for-vl-orcar-mv2s-do-not-use-elsewhere)
                   ,(car forms)
                   (if a-for-vl-orcar-mv2s-do-not-use-elsewhere
                       (mv a-for-vl-orcar-mv2s-do-not-use-elsewhere
                           b-for-vl-orcar-mv2s-do-not-use-elsewhere)
                     (check-vars-not-free
                      (a-for-vl-orcar-mv2s-do-not-use-elsewhere
                       b-for-vl-orcar-mv2s-do-not-use-elsewhere)
                     ,(vl-orcar-mv2s-fn (cdr forms)))))
        (car forms))
    (er hard? 'vl-orcar-mv2s "Expected at least one form.")))

(defmacro vl-orcar-mv2s (&rest forms)
  ;; Each form in FORMS should return (MV A B).  We return the first
  ;; of these MV pairs with A != nil.
  (vl-orcar-mv2s-fn forms))


(define vl-read-any-base ((echars (and (vl-echarlist-p echars)
                                       (true-listp echars))))
  (vl-orcar-mv2s (vl-read-hex-base echars)
                 (vl-read-octal-base echars)
                 (vl-read-binary-base echars)
                 (vl-read-decimal-base echars))
  ///
  (def-prefix/remainder-thms vl-read-any-base))



; Embedded spaces are also prohibited in the following productions.
;
; hex_value ::= hex_digit { _ | hex_digit }
;
; octal_value ::= octal_digit { _ | octal_digit }
;
; binary_value ::= binary_digit { _ | binary_digit }
;
; unsigned_number ::= decimal_digit { _ | decimal_digit }
;
; non_zero_unsigned_number ::= non_zero_decimal_digit { _ | decimal_digit }

(define vl-read-hex-value ((echars vl-echarlist-p))
  :inline t
  (if (or (not (consp echars))
          (not (vl-hex-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-hex-digit echars))
  ///
  (def-prefix/remainder-thms vl-read-hex-value))

(define vl-read-octal-value ((echars vl-echarlist-p))
  :inline t
  (if (or (not (consp echars))
          (not (vl-octal-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-octal-digit echars))
  ///
  (def-prefix/remainder-thms vl-read-octal-value))

(define vl-read-binary-value ((echars vl-echarlist-p))
  :inline t
  (if (or (not (consp echars))
          (not (vl-binary-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-binary-digit echars))
  ///
  (def-prefix/remainder-thms vl-read-binary-value))

(define vl-read-unsigned-number ((echars vl-echarlist-p))
  (if (or (not (consp echars))
          (not (vl-decimal-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-decimal-digit echars))
  ///
  (def-prefix/remainder-thms vl-read-unsigned-number))

(define vl-read-non-zero-unsigned-number ((echars vl-echarlist-p))
  :inline t
  (if (or (not (consp echars))
          (not (vl-non-zero-decimal-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-decimal-digit echars))
  ///
  (def-prefix/remainder-thms vl-read-non-zero-unsigned-number))



; Embedded spaces are not permitted in real numbers, either.
;
;   sign ::= + | -
;
;   exp ::= e | E
;
;   real_number ::=
;      unsigned_number . unsigned_number
;    | unsigned_number [ . unsigned_number ] exp [ sign ] unsigned_number

(define vl-read-real-number ((echars (and (vl-echarlist-p echars)
                                          (true-listp echars))))
  (b* (((mv prefix-intpart   rem1) (vl-read-unsigned-number echars))
       ((mv prefix-dot       rem1) (vl-read-literal "." rem1))
       ((mv prefix-fracpart  rem1) (vl-read-unsigned-number rem1))
       ((mv prefix-exp       rem2) (vl-read-some-literal '("e" "E") rem1))
       ((mv prefix-sign      rem2) (vl-read-some-literal '("+" "-") rem2))
       ((mv prefix-exppart   rem2) (vl-read-unsigned-number rem2)))
    (cond ((and prefix-intpart
                prefix-dot
                prefix-fracpart
                (not prefix-exp))
           ;; Production 1.
           (mv (append prefix-intpart prefix-dot prefix-fracpart)
               rem1))
          ((and prefix-intpart
                prefix-exp
                prefix-exppart)
           ;; Production 2.
           (mv (append prefix-intpart prefix-dot  prefix-fracpart
                       prefix-exp     prefix-sign prefix-exppart)
               rem2))
          (t
           (mv nil echars))))
  ///
  (def-prefix/remainder-thms vl-read-real-number))




; Note that spaces are permitted between the sizes, bases, and values of the
; following productions.
;
; size ::= non_zero_unsigned_number
;
; hex_number ::= [size] hex_base hex_value
;
; octal_number ::= [size] octal_base octal_value
;
; binary_number ::= [size] binary_base binary_value
;
; decimal_number ::=
;       unsigned_number
;     | [size] decimal_base unsigned_number
;     | [size] decimal_base x_digit { _ }
;     | [size] decimal_base z_digit { _ }
;
; number ::=
;       decimal_number
;     | octal_number
;     | binary_number
;     | hex_number
;     | real_number

(define vl-read-decimal-value ((echars vl-echarlist-p))
  :returns (mv prefix remainder)

; This is not part of the Verilog grammar.  But we think of introducing
; decimal_value as follows:
;
;   decimal_value ::= unsigned_number
;                   | x_digit { _ }
;                   | z_digit { _ }
;
; In other words, this is anything that can follow a decimal_base in the
; decimal_number production.

  (b* (((unless (consp echars))
        (mv nil echars))
       ((unless (or (vl-x-digit-echar-p (car echars))
                    (vl-z-digit-echar-p (car echars))))
        (vl-read-unsigned-number echars))
       ((mv prefix remainder) (vl-read-while-underscore (cdr echars))))
    (mv (cons (car echars) prefix) remainder))
  ///
  (def-prefix/remainder-thms vl-read-decimal-value))


(define vl-binary-digits-to-bitlist ((digits character-listp))
  :returns (bits vl-bitlist-p)
  :short "Convert MSB-First Binary Digits into an MSB-First Bitlist"
  (if (consp digits)
      (cons (case (car digits)
              (#\0           :vl-0val)
              (#\1           :vl-1val)
              ((#\x #\X)     :vl-xval)
              ((#\z #\Z #\?) :vl-zval)
              (otherwise
               (progn$ (raise "Not a binary digit: ~x0.~%" (car digits))
                       :vl-0val)))
            (vl-binary-digits-to-bitlist (cdr digits)))
    nil)
  ///
  (defthm len-of-vl-binary-digits-to-bitlist
    (equal (len (vl-binary-digits-to-bitlist x))
           (len x))))

(define vl-octal-digits-to-bitlist ((digits character-listp))
  :returns (bits vl-bitlist-p)
  :short "Convert MSB-First Octal Digits into an MSB-First Bitlist"
  (if (consp digits)
      (append (case (car digits)
                (#\0           (list :vl-0val :vl-0val :vl-0val))
                (#\1           (list :vl-0val :vl-0val :vl-1val))
                (#\2           (list :vl-0val :vl-1val :vl-0val))
                (#\3           (list :vl-0val :vl-1val :vl-1val))
                (#\4           (list :vl-1val :vl-0val :vl-0val))
                (#\5           (list :vl-1val :vl-0val :vl-1val))
                (#\6           (list :vl-1val :vl-1val :vl-0val))
                (#\7           (list :vl-1val :vl-1val :vl-1val))
                ((#\x #\X)     (list :vl-xval :vl-xval :vl-xval))
                ((#\z #\Z #\?) (list :vl-zval :vl-zval :vl-zval))
                (otherwise
                 (progn$ (raise "Not an octal digit: ~x0.~%" (car digits))
                         (list :vl-0val :vl-0val :vl-0val))))
              (vl-octal-digits-to-bitlist (cdr digits)))
    nil)
  ///
  (defthm len-of-vl-octal-digits-to-bitlist
    (equal (len (vl-octal-digits-to-bitlist x))
           (* 3 (len x)))))


(define vl-decimal-digits-to-bitlist ((digits character-listp))
  :returns (bits vl-bitlist-p)
  :long "<p>The only time this should be called is if digits is a singleton
  list containing exactly the digit x or z.</p>"
  (cond ((member-equal digits (list '(#\x)
                                    '(#\X)))
         (list :vl-xval))
        ((member-equal digits (list '(#\z)
                                    '(#\Z)
                                    '(#\?)))
         (list :vl-zval))
        (t
         (progn$
          (raise "Programming error")
          (list :vl-xval))))
  ///
  (defthm len-of-vl-decimal-digits-to-bitlist
    (equal (len (vl-decimal-digits-to-bitlist x))
           1)))


(define vl-hex-digits-to-bitlist ((digits character-listp))
  :returns (bits vl-bitlist-p)
  :short "Converts MSB-First Digits into an MSB-First Bitlist"
  (if (consp digits)
      (append (case (car digits)
                (#\0           (list :vl-0val :vl-0val :vl-0val :vl-0val))
                (#\1           (list :vl-0val :vl-0val :vl-0val :vl-1val))
                (#\2           (list :vl-0val :vl-0val :vl-1val :vl-0val))
                (#\3           (list :vl-0val :vl-0val :vl-1val :vl-1val))
                (#\4           (list :vl-0val :vl-1val :vl-0val :vl-0val))
                (#\5           (list :vl-0val :vl-1val :vl-0val :vl-1val))
                (#\6           (list :vl-0val :vl-1val :vl-1val :vl-0val))
                (#\7           (list :vl-0val :vl-1val :vl-1val :vl-1val))
                (#\8           (list :vl-1val :vl-0val :vl-0val :vl-0val))
                (#\9           (list :vl-1val :vl-0val :vl-0val :vl-1val))
                ((#\A #\a)     (list :vl-1val :vl-0val :vl-1val :vl-0val))
                ((#\B #\b)     (list :vl-1val :vl-0val :vl-1val :vl-1val))
                ((#\C #\c)     (list :vl-1val :vl-1val :vl-0val :vl-0val))
                ((#\D #\d)     (list :vl-1val :vl-1val :vl-0val :vl-1val))
                ((#\E #\e)     (list :vl-1val :vl-1val :vl-1val :vl-0val))
                ((#\F #\f)     (list :vl-1val :vl-1val :vl-1val :vl-1val))
                ((#\x #\X)     (list :vl-xval :vl-xval :vl-xval :vl-xval))
                ((#\z #\Z #\?) (list :vl-zval :vl-zval :vl-zval :vl-zval))
                (otherwise
                 (progn$ (raise "Not a hex digit: ~x0.~%" (car digits))
                         (list :vl-0val :vl-0val :vl-0val :vl-0val))))
              (vl-hex-digits-to-bitlist (cdr digits)))
    nil)
  ///
  (defthm len-of-vl-hex-digits-to-bitlist
    (equal (len (vl-hex-digits-to-bitlist x))
           (* 4 (len x)))))




(define vl-correct-bitlist
  :parents (lexer)
  :short "Extend (or truncate) a bit-list to match the size specifier for an
integer token."

  ((loc  vl-location-p "Context for any new warnings.")
   (bits vl-bitlist-p
         "A bitlist which might be shorter or longer than @('width'), which is
          the size specified for this integer or is @('nil') if no size was
          specified.  For instance, the user may have written @('3'bx') instead
          of @('3'bxxx').")
   (width maybe-posp
          "The desired width.  Note that we emulate a 32-bit Verilog
           implementation and treat unsized numbers as having width 32.")
   (warnings "An ordinary @(see warnings) accumulator."))

  :returns (mv (warnings vl-warninglist-p :hyp (force (vl-warninglist-p warnings)))
               (new-bits vl-bitlist-p :hyp (force (vl-bitlist-p bits))))

  :long "<p>Our goal is to produce a new list of bits that has the desired
width.  </p>

<p>The rules for extending or truncating are given in 3.5.1:</p>

<ul>

<li>If bits is shorter than width, we are usually supposed to zero-extend them.
However, when the most significant bit is X or Z, we are instead supposed to
X-extend or Z-extend, respectively.  (The specification notes that in
Verilog-1995, unsized constants whose high-order bit was X or Z were only
extended to 32 bits, so we detect and warn about this case.)</li>

<li>If bits is longer than width, we are to truncate it from the left, keeping
the least significant width-many bits.  We produce a truncation warning in this
case.</li>

</ul>"

  (b* ((actual-len  (len bits))
       (unsizedp    (not width))
       (desired-len (if width (lnfix width) 32))

       ((when (eql actual-len 0))
        ;; BOZO could probably prove this never happens
        (raise "Expected at least one bit.")
        (mv warnings (replicate desired-len :vl-0val)))

       (pad-bit (case (car bits)
                  (:vl-zval :vl-zval)
                  (:vl-xval :vl-xval)
                  (otherwise :vl-0val)))

       (warnings (if (and unsizedp
                          (or (eq pad-bit :vl-xval)
                              (eq pad-bit :vl-zval)))
                     (cons (make-vl-warning
                            :type :vl-warn-incompatible
                            :msg "~l0: unsized numbers with leading X or Z ~
                                    bit have a different interpretation in ~
                                    Verilog-1995 than in Verilog-2001 and ~
                                    beyond.  You may wish to use an explicit ~
                                    size specifier on this number."
                            :args (list loc)
                            :fn 'vl-correct-bitlist)
                           warnings)
                   warnings))

       ((when (eql desired-len actual-len))
        ;; Nothing to do
        (mv warnings bits))

       ((when (< desired-len actual-len))
        (b* ((msg "~l0: implicitly truncating ~s1 from ~x2 to ~x3 bits.")
             (msg (if unsizedp
                      (cat msg "  Note that this truncation emulates a ~
                                  32-bit Verilog implementation, and that on ~
                                  a 64-bit system a different value could be ~
                                  produced.  We strongly recommend adding an ~
                                  explicit size specifier.")
                    msg))
             (bitstr (vl-bitlist->string bits))
             (w (make-vl-warning
                 :type :vl-warn-overflow
                 :msg msg
                 :args (list loc bitstr actual-len desired-len)
                 :fn 'vl-correct-bitlist))
             (bits-prime (nthcdr (- actual-len desired-len)
                                 (redundant-list-fix bits)))
             (warnings
              (if (all-equalp :vl-xval bits)
                  ;; We suppress the truncation warning when all of the bits
                  ;; are X, because we often run into 29'h XXXX_XXXX or similar,
                  ;; and while perhaps {29{1'bX}} would be a better way to write
                  ;; it, the XXXX_XXXX form seems pretty legitimate, too.
                  warnings
                (cons w warnings))))
          (mv warnings bits-prime)))

       ;; Else, desired-len > actual-len
       (pad        (replicate (- desired-len actual-len) pad-bit))
       (bits-prime (append pad bits)))

    (mv warnings bits-prime))

  ///
  (defthm len-of-vl-correct-bitlist
    (equal (len (mv-nth 1 (vl-correct-bitlist loc bits width warnings)))
           (if width
               (nfix width)
             32)))

  (local
   (encapsulate
     ()

     ;; Basic extension test with a fixed width
     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "0111"))
                                        8
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits) "00000111"))))

     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "1111"))
                                        8
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits) "00001111"))))

     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "x111"))
                                        8
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits) "XXXXX111"))))

     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "z111"))
                                        8
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits) "ZZZZZ111"))))


     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "110111"))
                                        4
                                        nil)))
                (and (consp warn)
                     (equal (vl-bitlist->string bits) "0111"))))

     (assert! (b* (((mv warn ?bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "0111"))
                                        nil
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits)
                            (implode (append (replicate 29 #\0)
                                             (replicate 3 #\1)))))))

     (assert! (b* (((mv warn ?bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "Z111"))
                                        nil
                                        nil)))
                (and (consp warn)
                     (equal (vl-bitlist->string bits)
                            (implode (append (replicate 29 #\Z)
                                             (replicate 3 #\1))))))))))


(defsection vl-lex-integer

  (definlined vl-oct-basep (base)
    (declare (xargs :guard (character-listp base)))
    (consp (or (member #\o base)
               (member #\O base))))

  (definlined vl-signed-basep (base)
    (declare (xargs :guard (character-listp base)))
    (consp (or (member #\s base)
               (member #\S base))))

  (definlined vl-hex-basep (base)
    (declare (xargs :guard (character-listp base)))
    (consp (or (member #\h base)
               (member #\H base))))

  (definlined vl-dec-basep (base)
    (declare (xargs :guard (character-listp base)))
    (consp (or (member #\d base)
               (member #\D base))))

  (definlined vl-base-to-radix (base)
    (declare (xargs :guard (character-listp base)))
    (cond ((vl-hex-basep base) 16)
          ((vl-dec-basep base) 10)
          ((vl-oct-basep base) 8)
          (t 2)))

  (defthm vl-base-to-radix-upper
    (<= (vl-base-to-radix base) 16)
    :rule-classes :linear
    :hints(("Goal" :in-theory (enable vl-base-to-radix))))

  (defthm vl-base-to-radix-lower
    (<= 2 (vl-base-to-radix base))
    :rule-classes :linear
    :hints(("Goal" :in-theory (enable vl-base-to-radix))))




  (defund vl-lex-integer (echars warnings)
    "Returns (MV TOKEN/NIL REMAINDER WARNINGS)"
    (declare (xargs :guard (and (vl-echarlist-p echars)
                                (true-listp echars)
                                (vl-warninglist-p warnings))
                    :verify-guards nil))
    (b* ( ;; An integer token might begin with:
         ;;
         ;;  1. a regular unsigned number (which could be a size specifier or the actual
         ;;     value for a plain decimal constant), or
         ;;
         ;;  2. with a base specifier like 'sd (for unsized but based numbers)
         ;;
         ;; We first try to read any numeric portion of echars into NUMBER.
         ;; When there is no number, REMAINDER1 == ECHARS and NUMBER == NIL.
         ((mv number remainder1) (vl-read-unsigned-number echars))

         ;; Interpret NUMBER if it exists.  If there is no number,
         ;; value-of-number will become NIL.
         (normalized-number      (vl-echarlist-kill-underscores number))
         (value-of-number        (vl-echarlist-unsigned-value normalized-number 10))

         ;; Now try to read the base specifier, if it exists.  If not,
         ;; REMAINDER2 will be REMAINDER1.
         ((mv ws remainder2)     (vl-read-while-whitespace remainder1))
         ((mv base remainder2)   (vl-read-any-base remainder2))

         ((when (and (not number) (not base)))
          ;; If there is not a plain unsigned number or a base, then this is
          ;; not an integer at all, so we fail.
          (mv nil echars warnings))

         (firstchar (if number (car number) (car base)))

         ((when (and number (not value-of-number)))
          ;; Sanity check.  We could try to prove this away, but to do so we'd
          ;; have to reason about vl-read-unsigned-number, and that just seems
          ;; like a lot of work.
          (mv (er hard? 'vl-lex-integer
                  "Lexer error (~s0): thought this was impossible; cannot ~
                  interpret ~s1 as a number."
                  (vl-location-string (vl-echar->loc firstchar))
                  (vl-echarlist->string number))
              echars
              warnings))

         ((when (not base))
          ;; We know there is a NUMBER because otherwise we failed above.  So,
          ;; there is a number and no base, which means this is a plain decimal
          ;; number with no X or Z digits.  This should become a signed,
          ;; base-10 integer whose width is implementation dependent.  We treat
          ;; it as a 32-bit number.
          (b* ((val-fix (mod value-of-number (expt 2 32)))
               (warnings
                (cond ((< value-of-number (expt 2 31))
                       warnings)
                      ((< value-of-number (expt 2 32))
                       (cons (make-vl-warning
                              :type :vl-warn-overflow
                              :msg "~l0: the plain number ~s1 is in [2^31, ~
                                    2^32); it will be considered a negative ~
                                    number by 32-bit Verilog implementations, ~
                                    but will be positive on 64-bit systems ~
                                    and beyond.  We recommend adding a size ~
                                    specifier to this number."
                              :args (list (vl-echar->loc firstchar)
                                          (vl-echarlist->string number))
                              :fn 'vl-lex-integer)
                             warnings))
                      (t
                       (cons (make-vl-warning
                              :type :vl-warn-overflow
                              :msg "~l0: the plain number ~s1 is over 2^32; ~
                                    we truncate it to ~x2 to emulate a 32-bit ~
                                    Verilog implementation.  But this number ~
                                    will have a different value on 64-bit ~
                                    systems and beyond.  We strongly suggest ~
                                    adding a size specifier to this number."
                              :args (list (vl-echar->loc firstchar)
                                          (vl-echarlist->string number)
                                          val-fix)
                              :fn 'vl-lex-integer)
                             warnings))))
               (token (make-vl-inttoken :etext number
                                        :width 32
                                        :signedp t
                                        :value val-fix
                                        :bits nil
                                        :wasunsized t)))
            (mv token remainder1 warnings)))

         ;; Otherwise there is a base.  This means that if there is a NUMBER,
         ;; it is the size specifier.

         ((when (and number (equal value-of-number 0)))
          ;; It's illegal to have a width of zero.  After reading the grammar,
          ;; we believe it is never allowed for two numbers to follow one
          ;; another when separated only by whitespace.  So there is no way to
          ;; parse this, and we are justified in causing an error rather than
          ;; returning number as its own inttoken.
          (mv (cw "Lexer error (~s0): found a number whose size is zero.~%"
                  (vl-location-string (vl-echar->loc firstchar)))
              echars
              warnings))

         (unsizedp (not number))
         (width    (or value-of-number 32))

         ;; The signedness and radix are determined by the base.
         (chars-of-base  (vl-echarlist->chars base))
         (signedp        (vl-signed-basep chars-of-base))
         (radix          (vl-base-to-radix chars-of-base))

         ;; Now we need to read the rest of the number.  There can be some
         ;; whitespace before the value.
         ((mv ws2 remainder2)
          (vl-read-while-whitespace remainder2))

         ;; Read the value...
         ((mv edigits remainder2)
          (case radix
            (16        (vl-read-hex-value remainder2))
            (10        (vl-read-decimal-value remainder2))
            (8         (vl-read-octal-value remainder2))
            (otherwise (vl-read-binary-value remainder2))))

         (etext (append number ws base ws2 edigits))

         ;; Before we try to interpret the value, we first clean up the digits
         ;; by removing any underscore characters.

         (normalized-edigits (vl-echarlist-kill-underscores edigits))

         ;; Now we try to interpret the value.  We won't be able to compute a
         ;; value if there are z's or x's, but in that case
         ;; vl-echarlist-unsigned-value returns nil, which is the "value" we
         ;; want to use anyway.
         (value (vl-echarlist-unsigned-value normalized-edigits radix))

         ((when value)
          ;; If there was a value, then just check to make sure it is in range
          ;; for this width and build an inttoken.
          (b* ((val-fix (mod value (expt 2 width)))
               (token   (make-vl-inttoken :etext etext
                                          :width width
                                          :signedp signedp
                                          :value val-fix
                                          :bits nil
                                          :wasunsized unsizedp))
               (warnings
                ;; Truncation warnings.
                (cond ((not unsizedp)
                       (if (= value val-fix)
                           warnings
                         (cons (make-vl-warning
                                :type :vl-warn-overflow
                                :msg "~l0: the number ~s1 is not within the ~
                                      range [0, 2^~x2) indicated by its size, ~
                                      and is being truncated to ~x2 bits, ~
                                      yielding ~x3."
                                :args (list (vl-echar->loc firstchar)
                                            value
                                            width
                                            val-fix)
                                :fn 'vl-lex-integer)
                               warnings)))
                      ((< value (expt 2 31))
                       warnings)
                      ((and signedp (< value (expt 2 32)))
                       (cons (make-vl-warning
                              :type :vl-warn-overflow
                              :msg "~l0: the unsized, signed number ~s1 is in ~
                                    [2^31, 2^32); it will be considered a ~
                                    negative number by 32-bit Verilog ~
                                    implementations, but will be positive on ~
                                    64-bit systems and beyond.  We recommend ~
                                    adding a size specifier to this number."
                              :args (list (vl-echar->loc firstchar)
                                          (vl-echarlist->string number))
                              :fn 'vl-lex-integer)
                             warnings))
                      ((< value (expt 2 32))
                       warnings)
                      (t
                       (cons (make-vl-warning
                              :type :v-warn-overflow
                              :msg "~l0: the unsized number ~s1 is over 2^32; ~
                                    we truncate it to ~x2 to emulate a 32-bit ~
                                    Verilog implementation.  But this number ~
                                    will have a different value on 64-bit ~
                                    systems and beyond.  We strongly suggest ~
                                    adding a size specifier to this number."
                              :args (list (vl-echar->loc firstchar)
                                          (vl-echarlist->string number)
                                          val-fix)
                              :fn 'vl-lex-integer)
                             warnings)))))
            (mv token remainder2 warnings)))

         ;; Otherwise, we weren't able to interpret the normalized edigits as a
         ;; number.  The number might still be valid, but just contain X or Z
         ;; characters.
         (digits (vl-echarlist->chars normalized-edigits))
         (bits   (case radix
                   (16        (vl-hex-digits-to-bitlist digits))
                   (10        (vl-decimal-digits-to-bitlist digits))
                   (8         (vl-octal-digits-to-bitlist digits))
                   (otherwise (vl-binary-digits-to-bitlist digits))))
         ((unless bits)
          ;; There aren't even any bits?
          (mv (cw "Lexer error (~s0): invalid number: ~s1.~%"
                  (vl-location-string (vl-echar->loc firstchar))
                  (vl-echarlist->string etext))
              echars
              warnings))

         ((mv warnings bits)
          (vl-correct-bitlist (vl-echar->loc firstchar)
                              bits
                              value-of-number
                              warnings))
         (token (make-vl-inttoken :etext etext
                                  :width width
                                  :signedp signedp
                                  :value value
                                  :bits bits
                                  :wasunsized unsizedp)))
      (mv token remainder2 warnings)))

  (local (in-theory (enable vl-inttoken-constraint-p)))
  (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

  (verify-guards vl-lex-integer)

  (with-output
   :gag-mode :goals
   (def-token/remainder-thms vl-lex-integer
     :formals (echars warnings)))

  (defthm vl-warninglist-p-of-vl-lex-integer
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 2 (vl-lex-integer echars warnings))))
    :hints(("Goal" :in-theory (enable vl-lex-integer)))))



(define vl-lex-number
  :parents (lexer)
  ((echars (and (vl-echarlist-p echars)
                (true-listp echars)))
   (warnings vl-warninglist-p))
  :returns (mv token/nil
               remainder
               (warnings vl-warninglist-p :hyp (force (vl-warninglist-p warnings))))

  :long "<p>This routine finds either a real number or an integer.  We always
check for real numbers first, because @(see vl-lex-integer) could be fooled
into thinking, that a real number was just an integer with some other stuff
following it, e.g., it will give you \"3\" when you try to parse \"3.4\".</p>"

  :inline t
  (b* (((mv prefix remainder) (vl-read-real-number echars))
       ((when prefix)
        (mv (make-vl-realtoken :etext prefix)
            remainder
            warnings)))
    (vl-lex-integer echars warnings))
  ///
  (def-token/remainder-thms vl-lex-number
    :formals (echars warnings)))



;                          THE LEXER ITSELF
;
; Note that the lexer expects that its input stream has already been
; preprocessed, so there should not be any grave characters or compiler
; directives to worry about.

(define vl-lex-plain
  :parents (lexer)
  :short "Try to match a particular string literal corresponding to some
          plain token."
  ((echars "Characters we are lexing"
           (and (vl-echarlist-p echars)
                (true-listp echars)))
   (string "Exact string we are looking for."
           (and (stringp string)
                (not (equal string ""))))
   (type   vl-plaintokentype-p
           "The type of plain token to create, on success.")
   (warnings))
  :returns (mv token/nil
               remainder
               (warnings vl-warninglist-p :hyp (force (vl-warninglist-p warnings))))
  (b* ((string (mbe :logic (if (and (stringp string)
                                    (not (equal string "")))
                               string
                             "foo")
                    :exec string))
       ((unless (vl-matches-string-p string echars))
        (mv nil echars warnings))
       (len   (length string))
       (etext (take len echars)))
    (mv (make-vl-plaintoken :etext etext :type type)
        (nthcdr len echars)
        warnings))
  ///
  (def-token/remainder-thms vl-lex-plain
    :formals (echars string type warnings)
    :extra-tokenhyp (force (vl-plaintokentype-p type))
    :extra-appendhyp (force (vl-plaintokentype-p type))))


(define vl-lex-plain-alist
  ((echars (and (vl-echarlist-p echars)
                (true-listp echars)))
   (alist vl-plaintoken-alistp)
   (warnings vl-warninglist-p))
  :returns (mv token/nil
               remainder
               (warnings vl-warninglist-p :hyp (force (vl-warninglist-p warnings))))

  :long "<p>We walk through the alist, looking for the first string that
matches the beginning of echars.  If we find one, we build a plaintoken using
the matching echars and the corresponding type.  Since the alist is searched in
order, you can search for long prefixes first, e.g., @('>>>') before
@('>>').</p>"

  (b* (((when (atom alist))
        (mv nil echars warnings))
       ((mv token remainder warnings)
        (vl-lex-plain echars (caar alist) (cdar alist) warnings))
       ((when token)
        (mv token remainder warnings)))
    (vl-lex-plain-alist echars (cdr alist) warnings))
  ///
  (def-token/remainder-thms vl-lex-plain-alist
    :formals (echars alist warnings)
    :extra-tokenhyp (force (vl-plaintoken-alistp alist))
    :extra-appendhyp (force (vl-plaintoken-alistp alist))))

(define vl-lex-token1
  :parents (vl-lex)
  :short "Try to parse a single token at the front of @('echars')."

  ((char1  "The first character in the stream.  It helps a lot with guard
            verification to have this separate from @('echars')."
           characterp)
   (echars "The characters we're lexing."
           (and (vl-echarlist-p echars)
                (true-listp echars)
                (consp echars)))
   (st       "Low-level configuration options."
             vl-lexstate-p)
   (warnings vl-warninglist-p))
  :guard (eql char1 (vl-echar->char (car echars)))
  :returns (mv token/nil remainder warnings)
  :inline t
  (if (char<= char1 #\9)
      ;; Code is 57 or less.

      (cond
       ((vl-whitespace-p char1) ;; codes 9, 10, 12, 32
        (mv-let (prefix remainder)
          (vl-read-while-whitespace echars)
          (mv (make-vl-plaintoken :etext prefix :type :vl-ws)
              remainder
              warnings)))

       ((vl-decimal-digit-p char1) ;; codes 48...57
        (vl-lex-number echars warnings))

       (t
        (case char1
          ;; Other special characters whose codes are less than 57.

          (#\! ;; 33
           (vl-lex-plain-alist echars (vl-lexstate->bangops st) warnings))

          (#\" ;; 34
           (mv-let (tok rem)
             (vl-lex-string echars)
             (mv tok rem warnings)))

          (#\# ;; 35
           (vl-lex-plain-alist echars (vl-lexstate->poundops st) warnings))

          (#\$ ;; 36
           (mv-let (tok rem)
             (vl-lex-system-identifier echars)
             (mv tok rem warnings)))

          (#\% ;; 37
           (vl-lex-plain-alist echars (vl-lexstate->remops st) warnings))

          (#\& ;; 38
           (vl-lex-plain-alist echars (vl-lexstate->andops st) warnings))

          (#\' ;; 39
           (cond ((vl-matches-string-p "'{" echars)
                  (vl-lex-plain echars "'{" :vl-assignpat warnings))
                 (t
                  (vl-lex-number echars warnings))))

          (#\( ;; 40
           (vl-lex-plain-alist echars
                               '(("(*" . :vl-beginattr)
                                 ("("  . :vl-lparen))
                               warnings))

          (#\) ;; 41
           (vl-lex-plain echars ")" :vl-rparen warnings))

          (#\* ;; 42
           (vl-lex-plain-alist echars (vl-lexstate->starops st) warnings))

          (#\+ ;; 43
           (vl-lex-plain-alist echars (vl-lexstate->plusops st) warnings))

          (#\, ;; 44
           (vl-lex-plain echars "," :vl-comma warnings))

          (#\- ;; 45
           (vl-lex-plain-alist echars (vl-lexstate->dashops st) warnings))

          (#\. ;; 46
           (vl-lex-plain-alist echars (vl-lexstate->dotops st) warnings))

          (#\/ ;; 47
           (cond ((vl-matches-string-p "//" echars)
                  (mv-let (tok rem)
                    (vl-lex-oneline-comment echars)
                    (mv tok rem warnings)))
                 ((vl-matches-string-p "/*" echars)
                  (mv-let (tok rem)
                    (vl-lex-block-comment echars)
                    (mv tok rem warnings)))
                 (t
                  (vl-lex-plain-alist echars (vl-lexstate->divops st) warnings))))

          (otherwise
           (mv nil echars warnings)))))

    ;; Otherwise, we know that the character code is at least 58.

    (if (vl-simple-id-head-p char1) ;; codes 65...90, 95, 97...122
        (mv-let (tok rem)
          (vl-lex-simple-identifier-or-keyword echars (vl-lexstate->kwdtable st))
          (mv tok rem warnings))

      ;; Most of this stuff is pretty rare, so it probably isn't too
      ;; important to try to optimize the search.

      (case char1

        (#\: ;; 58
         (vl-lex-plain-alist echars (vl-lexstate->colonops st) warnings))

        (#\; ;; 59
         (vl-lex-plain echars ";" :vl-semi warnings))

        (#\< ;; 60
         (vl-lex-plain-alist echars (vl-lexstate->lessops st) warnings))

        (#\= ;; 61
         (vl-lex-plain-alist echars (vl-lexstate->eqops st) warnings))

        (#\> ;; 62
         (vl-lex-plain-alist echars (vl-lexstate->gtops st) warnings))

        (#\? ;; 63
         (vl-lex-plain echars "?" :vl-qmark warnings))

        (#\@ ;; 64
         (vl-lex-plain echars "@" :vl-atsign warnings))

        (#\[ ;; 91
         (vl-lex-plain echars "[" :vl-lbrack warnings))

        (#\\ ;; 92
         (mv-let (tok rem)
           (vl-lex-escaped-identifier echars)
           (mv tok rem warnings)))

        (#\] ;; 93
         (vl-lex-plain echars "]" :vl-rbrack warnings))

        (#\^ ;; 94
         (vl-lex-plain-alist echars (vl-lexstate->xorops st) warnings))

        (#\{ ;; 123
         (vl-lex-plain echars "{" :vl-lcurly warnings))

        (#\| ;; 124
         (vl-lex-plain-alist echars (vl-lexstate->barops st) warnings))

        (#\} ;; 125
         (vl-lex-plain echars "}" :vl-rcurly warnings))

        (#\~ ;; 126
         (vl-lex-plain-alist echars
                             ;; Agrees across Verilog-2005 and SystemVerilog-2012
                             '(("~&"   . :vl-nand)
                               ("~|"   . :vl-nor)
                               ("~^" . :vl-xnor)
                               ("~"  . :vl-bitnot))
                             warnings))

        (otherwise
         (mv nil echars warnings)))))

  ///
  (local (defthm lemma
           (equal (equal (acl2-count (second (vl-read-while-whitespace echars)))
                         (acl2-count echars))
                  (not (vl-whitespace-p (vl-echar->char (first echars)))))
           :hints(("Goal" :in-theory (enable vl-read-while-whitespace)))))

  (def-token/remainder-thms vl-lex-token1
    :formals (char1 echars st warnings)
    :extra-tokenhyp
    (and (force (consp echars))
         (force (equal char1 (vl-echar->char (car echars))))
         (force (vl-lexstate-p st)))
    :extra-appendhyp
    (and (force (consp echars))
         (force (equal char1 (vl-echar->char (car echars))))
         (force (vl-lexstate-p st)))
    :extra-strongcounthyp
    (force (equal char1 (vl-echar->char (car echars)))))

  (defthm vl-warninglist-p-of-vl-lex-token1
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 2 (vl-lex-token1 char1 echars st warnings))))
    :hints(("Goal" :in-theory (enable vl-lex-token1)))))


(define vl-lex-token ((echars (and (vl-echarlist-p echars)
                                   (true-listp echars)))
                      (st       vl-lexstate-p)
                      (warnings vl-warninglist-p))
  :parents (vl-lex)
  :returns (mv token/nil
               remainder
               (warnings vl-warninglist-p :hyp (force (vl-warninglist-p warnings))))
  :inline t
  (b* (((unless (consp echars))
        (mv nil echars warnings))
       (echar1 (car echars))
       (char1  (vl-echar->char echar1)))
    (vl-lex-token1 char1 echars st warnings))
  ///
  (def-token/remainder-thms vl-lex-token
    :formals (echars st warnings)
    :extra-tokenhyp (vl-lexstate-p st)
    :extra-appendhyp (vl-lexstate-p st)))


(define vl-lex-main-exec
  :parents (vl-lex)
  :short "Tail recursive implementation."
  ((echars (and (vl-echarlist-p echars)
                (true-listp echars)))
   (acc    (and (vl-tokenlist-p acc)
                (true-listp acc)))
   (st       vl-lexstate-p)
   (warnings vl-warninglist-p))
  :returns (mv successp token-list warnings)
  (b* (((when (atom echars))
        (mv t acc warnings))
       ((mv tok remainder warnings)
        (vl-lex-token echars st warnings))
       ((when tok)
        (vl-lex-main-exec remainder (cons tok acc) st warnings)))
    (cw "About to cause an error.~%")
    (mv (cw "Lexer error (~s0): unable to identify a valid token.~%~
             [[ Previous  ]]: ~s1~%~
             [[ Remaining ]]: ~s2~%"
            (vl-location-string (vl-echar->loc (car echars)))
            (let* ((rprev (reverse acc))
                   (chop  (nthcdr (nfix (- (length rprev) 30)) rprev))
                   (chars (vl-tokenlist->etext chop)))
              (vl-echarlist->string chars))
            (vl-echarlist->string (take (min 30 (length echars)) echars)))
        acc
        warnings)))

(define vl-lex-main ((echars (and (vl-echarlist-p echars)
                                  (true-listp echars)))
                     (st       vl-lexstate-p)
                     (warnings vl-warninglist-p))
  :parents (vl-lex)
  :returns (mv successp token-list warnings)
  :verify-guards nil
  (mbe :logic
       (b* (((when (atom echars))
             (mv t nil warnings))
            ((mv first echars warnings)
             (vl-lex-token echars st warnings))
            ((unless first)
             (mv nil nil warnings))
            ((mv successp rest warnings)
             (vl-lex-main echars st warnings)))
         (mv successp (cons first rest) warnings))
       :exec
       (b* (((mv successp tokens warnings)
             (vl-lex-main-exec echars nil st warnings)))
         (mv successp (reverse tokens) warnings)))
  ///
  (local (in-theory (enable vl-lex-main-exec)))

  (local (defthm vl-lex-main-exec-successp-removal
           (equal (mv-nth 0 (vl-lex-main-exec echars acc st warnings))
                  (mv-nth 0 (vl-lex-main echars st warnings)))))

  (local (defthm vl-lex-main-exec-tokens-removal
           (equal (mv-nth 1 (vl-lex-main-exec echars acc st warnings))
                  (revappend (mv-nth 1 (vl-lex-main echars st warnings)) acc))))

  (local (defthm vl-lex-main-exec-warnings-removal
           (equal (mv-nth 2 (vl-lex-main-exec echars acc st warnings))
                  (mv-nth 2 (vl-lex-main echars st warnings)))))

  (defthm vl-lex-main-exec-redefinition
    (equal (vl-lex-main-exec echars acc st warnings)
           (mv-let (successp tokens warnings)
                   (vl-lex-main echars st warnings)
                   (mv successp (revappend tokens acc) warnings))))

  (defthm type-of-vl-lex-main-successp
    (booleanp (mv-nth 0 (vl-lex-main echars st warnings)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-lex-main-tokens
    (true-listp (mv-nth 1 (vl-lex-main echars st warnings)))
    :rule-classes :type-prescription)

  (verify-guards vl-lex-main)

  (defthm vl-tokenlist-p-of-vl-lex-main
    ;; Correctness Claim 1.  The lexer produces a list of tokens.
    (implies (and (force (vl-echarlist-p echars))
                  (force (vl-lexstate-p st)))
             (vl-tokenlist-p (mv-nth 1 (vl-lex-main echars st warnings)))))

  (defthm vl-tokenlist->etext-of-vl-lex-main
    ;; Correctness Claim 2.  If we flatten the resulting tokens, we obtain the
    ;; original characters.
    (b* (((mv okp tokens ?warnings) (vl-lex-main echars st warnings)))
      (implies (and okp
                    (force (vl-echarlist-p echars))
                    (force (true-listp echars))
                    (force (vl-lexstate-p st)))
               (equal (vl-tokenlist->etext tokens)
                      echars))))

  (defthm vl-warninglist-p-of-vl-lex-main
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 2 (vl-lex-main echars st warnings)))))

  (defttag vl-optimize)
  (never-memoize vl-lex-main-exec)
  (progn! (set-raw-mode t)
          (defun vl-lex-main (echars st warnings)
            (mv-let (successp tokens warnings)
              (vl-lex-main-exec echars nil st warnings)
              (mv successp (nreverse tokens) warnings))))
  (defttag nil))


(define vl-lex
  :parents (lexer)
  :short "Top level lexing function."
  ((echars   "The @(see extended-characters) to tokenize."
             (and (vl-echarlist-p echars)
                  (true-listp echars)))
   &key
   (warnings "A @(see warnings) accumulator to extend with any warnings, e.g.,
              about overflows or incompatibilities involving integer literals."
              vl-warninglist-p)
   (config   "Options about which keywords and operators to accept, i.e., for
              implementing different Verilog editions."
             vl-lexconfig-p))
  :returns (mv (successp "Did we successfully tokenize the input?  Note that
                          even on success there may be some warnings."
                         booleanp
                         :rule-classes :type-prescription)
               (tokens   "The resulting @(see tokens), including any comment
                          or whitespace tokens."
                         vl-tokenlist-p
                         :hyp (force (vl-echarlist-p echars)))
               (warnings "Extended warnings accumulator."
                         vl-warninglist-p
                         :hyp (force (vl-warninglist-p warnings))))
  (b* ((st (vl-lexstate-init config))
       ((mv okp tokens warnings)
        (vl-lex-main echars st warnings)))
    (mv okp tokens warnings))
  ///
  (defthm vl-tokenlist->etext-of-vl-lex-tokens
    ;; If we flatten the resulting tokens, we obtain the original characters.
    (b* (((mv okp tokens ?warnings)
          (vl-lex echars
                  :warnings warnings
                  :config config)))
      (implies (and okp
                    (force (vl-echarlist-p echars))
                    (force (true-listp echars)))
               (equal (vl-tokenlist->etext tokens)
                      echars)))))


(define vl-kill-whitespace-and-comments-core
  ((tokens     vl-tokenlist-p "Tokens to process, in order.")
   (tokens-acc "Tokens to keep; we're building this, in reverse order.")
   (cmap-acc   "Comment map; we're building this, in reverse order."))
  :returns (mv tokens-acc cmap-acc)
  :parents (vl-kill-whitespace-and-comments)
  :short "Tail recursive implementation."
  (b* (((when (atom tokens))
        (mv tokens-acc cmap-acc))
       (type (vl-token->type (car tokens)))
       (tokens-acc
        (if (or (eq type :vl-ws)
                (eq type :vl-comment))
            tokens-acc
          (cons (car tokens) tokens-acc)))
       (cmap-acc
        (if (eq type :vl-comment)
            ;; See note on comment shifting in vl-commentmap-p to
            ;; understand why we change the column number to zero.
            (cons (cons (change-vl-location (vl-token->loc (car tokens)) :col 0)
                        (vl-token->string (car tokens)))
                  cmap-acc)
          cmap-acc)))
    (vl-kill-whitespace-and-comments-core (cdr tokens) tokens-acc cmap-acc)))

(define vl-kill-whitespace-and-comments
  :parents (tokens vl-commentmap-p)
  :short "Prepare a token list for parsing by removing whitespace and comment
tokens, and construct a comment map from any comment tokens."
  ((tokens vl-tokenlist-p "Token list to process."))
  :returns
  (mv (filtered-tokens "A copy of @('tokens') with comments and whitespace removed.")
      (comment-map     "A comment map generated from the comment tokens."))
  :verify-guards nil
  (mbe :logic
       (b* (((when (atom tokens))
             (mv nil nil))
            ((mv tokens-rest cmap-rest)
             (vl-kill-whitespace-and-comments (cdr tokens)))
            (type (vl-token->type (car tokens)))
            (new-tokens
             (if (or (eq type :vl-ws)
                     (eq type :vl-comment))
                 tokens-rest
               (cons (car tokens) tokens-rest)))
            (new-cmap
             (if (eq type :vl-comment)
                 (cons (cons (change-vl-location (vl-token->loc (car tokens)) :col 0)
                             (vl-token->string (car tokens)))
                       cmap-rest)
               cmap-rest)))
         (mv new-tokens new-cmap))
       :exec
       (b* (((mv tokens-acc cmap-acc)
             (vl-kill-whitespace-and-comments-core tokens nil nil)))
         (mv (reverse tokens-acc)
             (reverse cmap-acc))))
  ///
  (defttag vl-optimize)
  (never-memoize vl-kill-whitespace-and-comments-core)
  (progn! (set-raw-mode t)
          (defun vl-kill-whitespace-and-comments (tokens)
            (b* (((mv tokens-acc cmap-acc)
                  (vl-kill-whitespace-and-comments-core tokens nil nil)))
              (mv (nreverse tokens-acc)
                  (nreverse cmap-acc)))))
  (defttag nil)

  (local (in-theory (enable vl-kill-whitespace-and-comments-core)))

  (local (defthm lemma
           (implies (true-listp tacc)
                    (true-listp (mv-nth 0 (vl-kill-whitespace-and-comments-core
                                           tokens tacc cacc))))))

  (local (defthm lemma2
           (implies (true-listp cacc)
                    (true-listp (mv-nth 1 (vl-kill-whitespace-and-comments-core
                                           tokens tacc cacc))))))

  (local (defthm lemma3
           (implies (true-listp tacc)
                    (equal (mv-nth 0 (vl-kill-whitespace-and-comments-core
                                      tokens tacc cacc))
                           (revappend
                            (mv-nth 0 (vl-kill-whitespace-and-comments tokens))
                            tacc)))
           :hints(("Goal" :induct (vl-kill-whitespace-and-comments-core
                                   tokens tacc cacc)))))

  (local (defthm lemma4
           (implies (true-listp cacc)
                    (equal (mv-nth 1 (vl-kill-whitespace-and-comments-core
                                      tokens tacc cacc))
                           (revappend
                            (mv-nth 1 (vl-kill-whitespace-and-comments tokens))
                            cacc)))
           :hints(("Goal" :induct (vl-kill-whitespace-and-comments-core
                                   tokens tacc cacc)))))

  (defmvtypes vl-kill-whitespace-and-comments (true-listp true-listp))

  (verify-guards vl-kill-whitespace-and-comments)

  (defthm vl-tokenlist-p-of-vl-kill-whitespace-and-comments
    (implies (force (vl-tokenlist-p tokens))
             (vl-tokenlist-p (mv-nth 0 (vl-kill-whitespace-and-comments tokens)))))

  (defthm vl-commentmap-p-of-vl-kill-whitespace-and-comments
    (implies (force (vl-tokenlist-p tokens))
             (vl-commentmap-p (mv-nth 1 (vl-kill-whitespace-and-comments tokens))))))


(define vl-make-test-tstream
  :parents (lexer)
  :short "Simple way to lex an ACL2 string, for parser unit tests."
  ((string stringp "Should be free of preprocessor symbols.")
   &key
   ((config vl-lexconfig-p) '*vl-default-lexconfig*))
  :returns (tokens vl-tokenlist-p)
  :long "<p>This is mainly intended for testing parser routines.</p>"
  (b* ((echars (vl-echarlist-from-str string))
       ((mv successp tokens ?warnings) (vl-lex echars
                                               :config config
                                               :warnings nil))
       ((unless successp)
        (raise "Lexing failed."))
       ((mv tokens ?cmap) (vl-kill-whitespace-and-comments tokens)))
    tokens))





(define vl-read-identifier

;; BOZO I don't think we should be using this.  The lexer doesn't use it.  But
;; some other custom code (e.g., for STVs) is currently based on it.

  :parents (identifiers)
  :short "Read a simple or escaped identifier, without checking if it is a
  keyword (BOZO?)."
  ((echars vl-echarlist-p))
  :returns (mv (name "A stringp with the interpreted name of this identifier
                      on success, or nil otherwise.")
               prefix remainder)
  (b* (((mv prefix remainder) (vl-read-simple-identifier echars))
       ((when prefix)
        (mv (hons-copy (vl-echarlist->string prefix)) prefix remainder)))
    (vl-read-escaped-identifier echars))
  ///
  (defthm stringp-of-vl-read-identifier
    (implies (force (vl-echarlist-p echars))
             (equal (stringp (mv-nth 0 (vl-read-identifier echars)))
                    (if (mv-nth 0 (vl-read-identifier echars))
                        t
                      nil))))

  (defthm vl-read-identifier-under-iff
    (iff (mv-nth 1 (vl-read-identifier echars))
         (mv-nth 0 (vl-read-identifier echars))))

  (def-prefix/remainder-thms vl-read-identifier
    :prefix-n 1
    :remainder-n 2))