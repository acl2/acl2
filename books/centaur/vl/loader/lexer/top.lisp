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
(include-book "strings")
(include-book "numbers")
(include-book "identifiers")
(include-book "../../util/commentmap")
(local (include-book "../../util/arithmetic"))

(defxdoc lexer
  :parents (loader)
  :short "A lexer for Verilog and SystemVerilog."

  :long "<p>Our lexer is intended to correctly support the full syntax for
Verilog-2005 and SystemVerilog-2012.  There are some significant differences
between these languages, e.g., Verilog has only a subset of SystemVerilog's
keywords and operators.  You can configure which edition of the standard is
being used; see @(see vl-loadconfig-p).</p>

<p>Note: our support for SystemVerilog is preliminary and may be buggy.  Our
parser does not yet support much of SystemVerilog, and some lexer details may
change as we work to extend the parser.</p>


<h3>Interface</h3>

<p>This lexer is a small part of VL's @(see loader).  The input to the lexer
should already be <see topic='@(url preprocessor)'>preprocessed</see>, i.e.,
there should not be any grave characters (@('`')) in the input.</p>

<p>Conventional lexers are often implemented as a @('get-token') routine, the
idea being that, at the parser's request, the lexer should read just enough
from the input stream to provide the next token.</p>

<p>In contrast, our top-level lexer function, @(see vl-lex), processes the
whole list of input characters that are produced by the @(see preprocessor),
and generates a whole list of @(see tokens) as output.  (It also generates a
list of @(see warnings), e.g., when integer constants are truncated.)</p>

<p>This is obviously inefficient.  On the other hand, memory is abundant and
lexing is almost intrinsically @('O(n)').  Meanwhile, our approach allows our
parser to be state-free, with arbitrary lookahead, and also gives us the
convenience of list-based (rather than file-based) debugging and unit testing
throughout the whole process; see for instance @(see make-test-tokens).</p>

<p>A basic correctness result for our lexer is:</p>

@(thm vl-tokenlist->etext-of-vl-lex)

<p>That is, whenever the lexer successfully tokenizes its input @('echars'),
you could flatten the resulting tokens to recover exactly the input text.</p>

<p>This theorem is not entirely satisfying.  It doesn't say anything about
whether we've tokenized the input correctly, i.e., in the sense of the Verilog
standard.  We can't really think of a reasonable way to formalize that.  But it
does mean that we at least accounted for every character of input, and that's
probably worth something.</p>

<p>To make this theorem possible, our lexer produces tokens even for whitespace
and comments.  These tokens are not suitable as input for the @(see parser),
and should be removed using @(see vl-kill-whitespace-and-comments) before
parsing begins.</p>

<p>Since we often want to use VL to transform or simplify Verilog source code,
we don't throw away comments&mdash;instead, we collect them up into a @(see
vl-commentmap-p).  We that later use comment maps to re-attach the comments to
the right parts of the tree; see for instance @(see vl-ppc-module).</p>")


(defsection lex-comments
  :parents (lexer)
  :short "Support for Verilog comments."

  :long "<p>Both Verilog-2005 and SystemVerilog-2012 support two forms of
comments.  Single-line comments that start with @('//') and end with a newline.
Multi-line comments start with @('/*') and end with @('*/').</p>

<p>Many lexers would skip past comments (and whitespace).  We instead create
@(':vl-comment') tokens.  This is generally meant to allow us to preserve
comments as we process and pretty-print the source code.</p>

<p>See also the comments in @(see preprocessor-ifdef-minutia) regarding line
continuations and comments in macro text.</p>")

(define vl-lex-oneline-comment
  :parents (lex-comments)
  :short "Try to match a @('// ...') style comment."
  ((echars vl-echarlist-p))
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
  :parents (lex-comments)
  :short "Try to match a @('/* ... */') style comment."
  ((echars vl-echarlist-p))
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



(define vl-lex-plain
  :parents (vl-lex)
  :short "Try to match a particular string literal corresponding to some
          plain token."
  ((echars "Characters we are lexing"
           vl-echarlist-p)
   (string "Exact string we are looking for."
           (and (stringp string)
                (not (equal string ""))))
   (type   vl-plaintokentype-p
           "The type of plain token to create, on success.")
   (warnings vl-warninglist-p))
  :returns (mv token/nil
               remainder
               (warnings vl-warninglist-p))
  (b* ((string (mbe :logic (if (and (stringp string)
                                    (not (equal string "")))
                               string
                             "foo")
                    :exec string))
       (warnings (vl-warninglist-fix warnings))
       ((unless (vl-matches-string-p string echars))
        (mv nil echars warnings))
       (len   (length string))
       (etext (first-n len echars)))
    (mv (make-vl-plaintoken :etext etext :type type)
        (rest-n len echars)
        warnings))
  ///
  (def-token/remainder-thms vl-lex-plain
    :formals (echars string type warnings)
    :extra-tokenhyp (force (vl-plaintokentype-p type))
    :extra-appendhyp (force (vl-plaintokentype-p type))))


(define vl-lex-plain-alist
  :parents (vl-lex)
  ((echars vl-echarlist-p)
   (alist vl-plaintoken-alistp)
   (warnings vl-warninglist-p))
  :returns (mv token/nil
               remainder
               (warnings vl-warninglist-p))

  :long "<p>We walk through the alist, looking for the first string that
matches the beginning of echars.  If we find one, we build a plaintoken using
the matching echars and the corresponding type.  Since the alist is searched in
order, you can search for long prefixes first, e.g., @('>>>') before
@('>>').</p>"

  (b* (((when (atom alist))
        (mv nil echars (ok)))
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
                (consp echars)))
   (st       "Low-level configuration options."
             vl-lexstate-p)
   (warnings vl-warninglist-p))
  :guard (eql char1 (vl-echar->char (car echars)))
  :returns (mv token/nil remainder (warnings vl-warninglist-p))
  :inline t
  (if (char<= char1 #\9)
      ;; Code is 57 or less.

      (b* (((when (vl-whitespace-p char1)) ;; codes 9, 10, 12, 32
            (b* (((mv prefix remainder) (vl-read-while-whitespace echars)))
              (mv (make-vl-plaintoken :etext prefix :type :vl-ws)
                  remainder
                  (ok))))

           ((when (vl-decimal-digit-p char1)) ;; codes 48...57
            (vl-lex-number echars st warnings)))

        (case char1
          ;; Other special characters whose codes are less than 57.

          (#\! ;; 33
           (vl-lex-plain-alist echars (vl-lexstate->bangops st) warnings))

          (#\" ;; 34
           (mv-let (tok rem)
             (vl-lex-string echars st)
             (mv tok rem (ok))))

          (#\# ;; 35
           (vl-lex-plain-alist echars (vl-lexstate->poundops st) warnings))

          (#\$ ;; 36
           (b* (((mv tok remainder)
                 (vl-lex-system-identifier echars (vl-lexstate->dollarops st))))
             (mv tok remainder (ok))))

          (#\% ;; 37
           (vl-lex-plain-alist echars (vl-lexstate->remops st) warnings))

          (#\& ;; 38
           (vl-lex-plain-alist echars (vl-lexstate->andops st) warnings))

          (#\' ;; 39
           ;; Quotes mark is tricky.  Could be a casting operator, a structure literal,
           ;; or an extended integer like 'x or '1.
           ;;
           ;; NCVerilog appears to prohibit spaces between '{, but allows
           ;; spaces around casting operators like unsigned'(...).
           ;;
           ;; VCS appears to allow spaces between '{ and around casting
           ;; operators.
           ;;
           ;; We'll mimic VCS here and support spaces in either place.  That
           ;; is, instead of producing a single, combined token for '{, we'll
           ;; produce a two-token sequence, :vl-quote :vl-lcurly.  Similarly,
           ;; for '( we'll just produce :vl-quote :vl-lparen.
           (b* (((mv tok remainder warnings)
                 (vl-lex-number echars st warnings))
                ((when tok)
                 (mv tok remainder warnings))
                ((unless (vl-lexstate->quotesp st))
                 (mv nil remainder warnings)))
             (vl-lex-plain echars "'" :vl-quote warnings)))

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
                    (mv tok rem (ok))))
                 ((vl-matches-string-p "/*" echars)
                  (mv-let (tok rem)
                    (vl-lex-block-comment echars)
                    (mv tok rem (ok))))
                 (t
                  (vl-lex-plain-alist echars (vl-lexstate->divops st) warnings))))

          (otherwise
           (mv nil echars (ok)))))

    ;; Otherwise, we know that the character code is at least 58.

    (if (vl-simple-id-head-p char1) ;; codes 65...90, 95, 97...122
        (mv-let (tok rem)
          (vl-lex-simple-identifier-or-keyword echars (vl-lexstate->kwdtable st))
          (mv tok rem (ok)))

      ;; Most of this stuff is pretty rare, so it probably isn't too
      ;; important to try to optimize the search.

      (case char1

        (#\: ;; 58
         (if (vl-matches-string-p "://" echars)
             ;; Special case to fix Issue 507.  The new :/ operator in
             ;; SystemVerilog causes problems when a : is followed by a
             ;; one-line // style comment, e.g., in a ternary operator.  Both
             ;; NCV and VCS seem to treat ://foo as a lone : followed by a
             ;; //foo comment.  But if we just do the vl-lex-plain-alist here,
             ;; we will instead see a :/ operator followed by /.  So, as a
             ;; stupid hack to avoid problems, handle :// explicitly.
             (mv (make-vl-plaintoken :etext (list (car echars)) :type :vl-colon)
                 (cdr echars)
                 (ok))
           (vl-lex-plain-alist echars (vl-lexstate->colonops st) warnings)))

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
           (mv tok rem (ok))))

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
         (mv nil echars (ok))))))

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
    (force (equal char1 (vl-echar->char (car echars))))))


(define vl-lex-token ((echars   vl-echarlist-p)
                      (st       vl-lexstate-p)
                      (warnings vl-warninglist-p))
  :parents (vl-lex)
  :returns (mv token/nil
               remainder
               (warnings vl-warninglist-p))
  :inline t
  (b* (((when (atom echars))
        (mv nil echars (ok)))
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
  ((echars   vl-echarlist-p)
   (nrev     (vl-tokenlist-p (nrev-copy nrev)))
   (st       vl-lexstate-p)
   (warnings vl-warninglist-p))
  :returns (mv successp
               nrev
               (warnings vl-warninglist-p))
  (b* ((nrev (nrev-fix nrev))
       ((when (atom echars))
        (mv t nrev (ok)))
       ((mv tok remainder warnings)
        (vl-lex-token echars st warnings))
       ((when tok)
        (let ((nrev (nrev-push tok nrev)))
          (vl-lex-main-exec remainder nrev st warnings)))
       (- (cw "About to cause an error.~%"))
       (prev-chars (nrev-copy nrev))
       (prev-chop  (nthcdr (nfix (- (length prev-chars) 30)) prev-chars))
       (prev-str   (vl-echarlist->string (vl-tokenlist->etext prev-chop))))
    (mv (cw "Lexer error (~s0): unable to identify a valid token.~%~
             [[ Previous  ]]: ~s1~%~
             [[ Remaining ]]: ~s2~%"
            (vl-location-string (vl-echar->loc (car echars)))
            prev-str
            (vl-echarlist->string (first-n (min 30 (len echars)) echars)))
        nrev
        warnings)))

(define vl-lex-main ((echars   vl-echarlist-p)
                     (st       vl-lexstate-p)
                     (warnings vl-warninglist-p))
  :parents (vl-lex)
  :returns (mv successp
               token-list
               (warnings vl-warninglist-p))
  :verify-guards nil
  (mbe :logic
       (b* (((when (atom echars))
             (mv t nil (ok)))
            ((mv first echars warnings)
             (vl-lex-token echars st warnings))
            ((unless first)
             (mv nil nil warnings))
            ((mv successp rest warnings)
             (vl-lex-main echars st warnings)))
         (mv successp (cons first rest) warnings))
       :exec
       (with-local-stobj nrev
         (mv-let (successp tokens warnings nrev)
           (b* (((mv successp nrev warnings)
                 (vl-lex-main-exec echars nrev st warnings))
                ((mv tokens nrev)
                 (nrev-finish nrev)))
             (mv successp tokens warnings nrev))
           (mv successp tokens warnings))))
  ///
  (local (in-theory (enable vl-lex-main-exec)))

  (local (defthm vl-lex-main-exec-successp-removal
           (equal (mv-nth 0 (vl-lex-main-exec echars acc st warnings))
                  (mv-nth 0 (vl-lex-main echars st warnings)))))

  (local (defthm vl-lex-main-exec-tokens-removal
           (equal (mv-nth 1 (vl-lex-main-exec echars acc st warnings))
                  (append acc (mv-nth 1 (vl-lex-main echars st warnings))))))

  (local (defthm vl-lex-main-exec-warnings-removal
           (equal (mv-nth 2 (vl-lex-main-exec echars acc st warnings))
                  (mv-nth 2 (vl-lex-main echars st warnings)))))

  (defthm vl-lex-main-exec-redefinition
    (equal (vl-lex-main-exec echars acc st warnings)
           (mv-let (successp tokens warnings)
                   (vl-lex-main echars st warnings)
                   (mv successp (append acc tokens) warnings))))

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
                      echars)))))


(define vl-lex
  :parents (lexer)
  :short "Top level lexing function."
  ((echars   "The @(see extended-characters) to tokenize."
             vl-echarlist-p)
   &key
   (warnings "A @(see warnings) accumulator to extend with any warnings, which
              are mainly about overflows or potential incompatibilities ~
              involving integer literals."
              vl-warninglist-p)
   (config   "Options about which keywords and operators to accept, i.e., for
              implementing different Verilog editions."
             vl-loadconfig-p))
  :returns (mv (successp "Did we successfully tokenize the input?  Note that
                          even on success there may be some warnings."
                         booleanp
                         :rule-classes :type-prescription)
               (tokens   "The resulting @(see tokens), including any comment
                          or whitespace tokens."
                         vl-tokenlist-p
                         :hyp (force (vl-echarlist-p echars)))
               (warnings "Extended warnings accumulator."
                         vl-warninglist-p))
  (b* ((st (vl-lexstate-init config))
       ((mv okp tokens warnings)
        (vl-lex-main echars st warnings)))
    (mv okp tokens warnings))
  ///
  (defthm vl-tokenlist->etext-of-vl-lex
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
  :parents (vl-kill-whitespace-and-comments)
  ((tokens vl-tokenlist-p)
   (nrev   "tokens accumulator")
   (nrev2  "comments accumulator"))
  :returns (mv nrev nrev2)
  (b* ((nrev  (nrev-fix nrev))
       (nrev2 (nrev-fix nrev2))
       ((when (atom tokens))
        (mv nrev nrev2))
       (type (vl-token->type (car tokens)))
       (nrev
        (if (or (eq type :vl-ws)
                (eq type :vl-comment))
            nrev
          (nrev-push (car tokens) nrev)))
       (nrev2
        (if (eq type :vl-comment)
            (nrev-push
             ;; See note on comment shifting in vl-commentmap-p to understand
             ;; why we change the column number to zero.
             (cons (change-vl-location (vl-token->loc (car tokens)) :col 0)
                   (vl-token->string (car tokens)))
             nrev2)
          nrev2)))
    (vl-kill-whitespace-and-comments-core (cdr tokens) nrev nrev2)))

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
       (b* (((local-stobjs nrev nrev2)
             (mv tokens cmap nrev nrev2))
            ((mv nrev nrev2)
             (vl-kill-whitespace-and-comments-core tokens nrev nrev2))
            ((mv tokens nrev) (nrev-finish nrev))
            ((mv cmap nrev2)  (nrev-finish nrev2)))
         (mv tokens cmap nrev nrev2)))
  ///
  (local (in-theory (enable vl-kill-whitespace-and-comments-core)))

  (local (defthm lemma3
           (equal (mv-nth 0 (vl-kill-whitespace-and-comments-core tokens tacc cacc))
                  (append tacc (mv-nth 0 (vl-kill-whitespace-and-comments tokens))))
           :hints(("Goal" :induct (vl-kill-whitespace-and-comments-core
                                   tokens tacc cacc)))))

  (local (defthm lemma4
           (equal (mv-nth 1 (vl-kill-whitespace-and-comments-core tokens tacc cacc))
                  (append cacc (mv-nth 1 (vl-kill-whitespace-and-comments tokens))))
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


(define make-test-tokens
  :parents (lexer)
  :short "A simple way to lex an ACL2 string."
  ((string stringp "Should be free of preprocessor symbols.")
   &key
   ((config vl-loadconfig-p) '*vl-default-loadconfig*))
  :returns (tokens vl-tokenlist-p)
  :long "<p>This is mainly intended for testing parser routines.  We don't
bother to preprocess the input and just ignore any warning.</p>"
  (b* ((echars (vl-echarlist-from-str string))
       ((mv successp tokens ?warnings) (vl-lex echars
                                               :config config
                                               :warnings nil))
       ((unless successp)
        (raise "Lexing failed."))
       ((mv tokens ?cmap) (vl-kill-whitespace-and-comments tokens)))
    tokens))




;; BOZO I don't think we should be using VL-READ-IDENTIFIER.  The lexer doesn't
;; use it.  But some other custom code (e.g., for STVs) is currently based on
;; it.

(xdoc::without-xdoc ;; suppress xdoc here since this is deprecated
  (define vl-read-identifier
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
      :remainder-n 2)))
