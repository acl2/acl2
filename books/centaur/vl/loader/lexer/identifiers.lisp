; VL Verilog Toolkit
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

(in-package "VL")
(include-book "lexstate")
(include-book "chartypes")
(include-book "utils")
(local (include-book "../../util/arithmetic"))

(local (defthm true-listp-of-cdr
           (implies (consp x)
                    (equal (true-listp (cdr x))
                           (true-listp x)))))

(defsection lex-identifiers
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
    escaped_identifier ::= \\ { any non-whitespace character } white_space
})

<p>However, Section 3.7.1 of the Verilog-2005 standard appears to contradict
the above definition.  It says that escaped identifiers \"provide a means of
including any of the <i>printable ASCII characters</i> in an identifier (the
decimal values 33 through 126...).  Section 5.6.1 of the SystemVerilog-2012
standard says the same thing, and its grammar has been updated with this
clarification:</p>

@({
    escaped_identifier ::= \\ { any printable non-whitespace character } white_space
})

<p>We therefore restrict the name characters in escaped identifiers to the
printable ASCII characters, i.e., characters whose codes are 33-126.</p>


<p>Both Verilog-2005 and SystemVerilog agree on the syntax for
system identifiers:</p>

@({
    system_tf_identifier ::= $[ a-zA-Z0-9_$ ] { [ a-zA-Z0-9_$ ] }
})

<p>Well, that's arguably true.  SystemVerilog adds certain pieces of syntax
such as @('$') and @('$root') that overlap with @('system_tf_identifier').  We
generally turn these into special tokens; see @(see vl-lex-system-identifier).
</p>


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
I exclude it on the grounds that it is suspicious and Cadence does not permit
it either.  Allowing it would make end-of-define even more complicated to
properly support in the @(see preprocessor).</p>


<h3>Notes about Honsing Identifiers</h3>

<p>We are always careful to @(see hons) the names of the identifier tokens we
create.  One reason it's a good idea is that identifiers are often repeated
many times, so making the actual string part a hons lets us use only one copy
of the string.  The other big reason is that identifier names are often used in
fast-alist lookups, and if the string isn't a hons, then @(see hons-get) will
have to hons it first anyway.  So, by honsing as we create the identifier
token, we potentially avoid a lot of repeated, redundant honsing later
on.</p>")

(local (xdoc::set-default-parents lex-identifiers))

(define vl-read-simple-identifier
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
  ((echars vl-echarlist-p)
   (breakp booleanp))
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
       (token (make-vl-idtoken :etext prefix
                               :name name
                               :breakp (and breakp t))))
    (mv token remainder)))

(def-token/remainder-thms vl-lex-escaped-identifier
  :formals (echars breakp))


(define vl-lex-simple-identifier-or-keyword
  :parents (lex-identifiers lex-keywords)
  :short "Match either a keyword or an ordinary, simple identifier."
  ((echars vl-echarlist-p     "The characters we're lexing.")
   (breakp booleanp)
   (table  vl-keyword-table-p "The table of keywords we're currently using."))
  :returns (mv token/nil remainder)
  (b* (((unless (and (consp echars)
                     (vl-simple-id-head-echar-p (car echars))))
        (mv nil echars))
       ((mv prefix remainder)
        (vl-read-simple-identifier echars))
       (str     (hons-copy (vl-echarlist->string prefix)))
       (lookup  (vl-keyword-lookup str table))
       (breakp (and breakp t))
       (token   (if lookup
                    (make-vl-plaintoken :etext prefix :type lookup :breakp breakp)
                  (make-vl-idtoken :etext prefix :name str :breakp breakp))))
      (mv token remainder)))

(def-token/remainder-thms vl-lex-simple-identifier-or-keyword
  :formals (echars breakp table)
  :extra-tokenhyp (vl-keyword-table-p table)
  :extra-appendhyp (vl-keyword-table-p table))




(define vl-lex-system-identifier
  :short "Try to match a system identifier (or some other special token
like @('$') or @('$root')."
  ((echars    vl-echarlist-p       "The characters we're lexing.")
   (breakp    booleanp)
   (dollarops vl-plaintoken-alistp "Any special @('$') tokens."))
  :returns (mv token/nil remainder)

  :long "<p>The order here is subtle.  We check for a hit in @('dollarops')
first, before even checking if there are any characters at all in the tail,
because @('$') is a valid token with special meaning in SystemVerilog, but is
just invalid in Verilog-2005.</p>"

  (b* (((unless (and (consp echars)
                     (eql (vl-echar->char (car echars)) #\$)))
        (mv nil echars))
       ((mv tail remainder)
        (vl-read-while-simple-id-tail (cdr echars)))
       (etext (cons (car echars) tail))
       (name (hons-copy (vl-echarlist->string etext))) ;; Includes $
       (look (hons-assoc-equal name dollarops))
       (breakp (and breakp t))
       ((when look)
        (mv (make-vl-plaintoken :type (cdr look) :etext etext :breakp breakp)
            remainder))
       ((unless tail)
        (mv nil echars)))
    ;; Not some special token, so just a system function.
    (mv (make-vl-sysidtoken :etext etext :name name :breakp breakp)
        remainder)))

(def-token/remainder-thms vl-lex-system-identifier
  :formals (echars breakp dollarops)
  :extra-tokenhyp (vl-plaintoken-alistp dollarops)
  :extra-appendhyp (vl-plaintoken-alistp dollarops))
