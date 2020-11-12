; Centaur Lexer Library
; Copyright (C) 2013 Centaur Technology
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

(in-package "CLEX")
(include-book "top")
(include-book "std/util/top" :dir :system)
(include-book "std/strings/top" :dir :system)

(local (defthm characterp-of-car-when-character-listp
         (implies (character-listp x)
                  (equal (characterp (car x))
                         (consp x)))))


(defsection example-lexer
  :parents (clex)
  :short "A very basic lexer written using some CLEX utilities."

  :long "<p>We implement a simple lexer for the following, contrived
language:</p>

@({
// supporting definitions:

   Letter ::= 'A' | ... | 'Z'
            | 'a' | ... | 'z'

   Number ::= '0' | ... | '9'

// top-level tokens:

  Whitespace ::= (Space | Newline | Tab)*

  Punctuation ::= ';'
                | '+'  | '-'  | '*' | '/'
                | '++' | '--'

  Keyword ::= 'void' | 'int' | 'float'

  Identifier ::= Letter ( Letter | Number | '_' )*    // except keywords

  Comment ::= '//' [anything but newline]* (Newline | EOF)
})

<p>Our lexer produces simple @(see token-p) structures that have a <see
topic='@(url tokentype-p)'>type</see> and some text.</p>

<p>The main lexer loop is @(see lex*).  As basic correctness properties, we
prove that it returns a valid @(see tokenlist-p) and that, on success, we can
flatten out the tokens it produces to recreate the original input stream:</p>

@(thm tokenlist-all-text-of-lex*)

<p>This seems pretty good.  It isn't a total correctness statement&mdash;for
that, we might also want to know something like: if there exists any valid way
to tokenize the input, then we will find it.  Or we might want to know: there
is always exactly one unique way to validly tokenize a list.  These seem harder
to state and prove.</p>")

(defenum tokentype-p
  (:keyword :whitespace :id :punctuation :comment)
  :parents (example-lexer)
  :short "Valid types for tokens.")

(defaggregate token
  ((type tokentype-p)
   (text stringp))
  :parents (example-lexer)
  :short "Representation of a single token."
  :long "<p>I make these tagless and illegible so that they're more
compact, which is useful when running the examples.</p>"
  :tag nil
  :layout :fulltree)

(deflist tokenlist-p (x)
  (token-p x)
  :parents (example-lexer))

(define tokenlist-all-text ((x tokenlist-p))
  :returns (text stringp "Appeneded text from all the tokens.")
  (if (atom x)
      ""
    (cat (token->text (car x))
         (tokenlist-all-text (cdr x))))
  ///
  (defthm tokenlist-all-text-when-atom
    (implies (atom x)
             (equal (tokenlist-all-text x)
                    "")))
  (defthm tokenlist-all-text-of-cons
    (equal (tokenlist-all-text (cons x y))
           (cat (token->text x) (tokenlist-all-text y)))))


(defcharset whitespace
  (or (eql x #\Space)
      (eql x #\Newline)
      (eql x #\Tab))
  :parents (example-lexer)
  :short "Recognize basic whitespace.")

(defcharset letter
  (let ((code (char-code x)))
    (or (and (<= (char-code #\a) code)
             (<= code (char-code #\z)))
        (and (<= (char-code #\A) code)
             (<= code (char-code #\Z)))))
  :parents (example-lexer)
  :short "Recognize upper- and lower-case letters.")

(defcharset number
  (str::dec-digit-char-p x)
  :in-package-of foo
  :parents (example-lexer)
  :short "Recognize digits 0-9.")

(defcharset idtail
  (or (letter-char-p x)
      (number-char-p x)
      (eql x #\_))
  :in-package-of foo
  :parents (example-lexer)
  :short "Recogize characters that are okay in the \"tails\" of identifiers:
letters, numbers, and underscores.")



(define lex-whitespace
  :parents (example-lexer)
  :short "Match whitespace to create a :whitespace token."
  ((sin "The @(see sin) stobj."))
  :returns (mv (tok "A whitespace token that contains all of the whitespace
                     from the start of the input stream, or @('nil') if there
                     is no leading whitespace."
                    (equal (token-p tok) (if tok t nil)))
               (sin "The remaining input stream, with the leading whitespace
                     removed."))
  (b* (((mv match sin)
        (sin-match-charset* (whitespace-chars) sin))
       ((unless match)
        (mv nil sin)))
    (mv (make-token :type :whitespace :text match) sin))
  ///
  (def-sin-progress lex-whitespace :hyp tok)
  (defthm lex-whitespace-reconstruction
    (b* (((mv tok new-sin) (lex-whitespace sin)))
      (implies tok
               (equal (append (explode (token->text tok))
                              (strin-left new-sin))
                      (strin-left sin))))))


(define lex-punctuation
  :parents (example-lexer)
  :short "Match punctuation characters to create a :punctuation token."
  ((sin "The @(see sin) stobj."))
  :returns (mv (tok "A punctuation token taken from the start of the input
                     stream, or @('nil') if the input stream does not start
                     with some valid punctuation."
                    (equal (token-p tok) (if tok t nil)))
               (sin "The remaining input stream, with the leading digits
                     removed."))
  :long "<p>It's important to put the @('++') and @('--') operators first here.
For instance, if @('+') came first, then we'd end up converting @('++') into
two separate @('+') tokens.</p>"
  (b* (((mv match sin)
        (sin-match-some-lit '("++" "--" ";" "+" "-" "*" "/" ) sin))
       ((unless match)
        (mv nil sin)))
    (mv (make-token :type :punctuation :text match) sin))
  ///
  (def-sin-progress lex-punctuation :hyp tok)
  (defthm lex-punctuation-reconstruction
    (b* (((mv tok new-sin) (lex-punctuation sin)))
      (implies tok
               (equal (append (explode (token->text tok))
                              (strin-left new-sin))
                      (strin-left sin))))))


(define lex-id/keyword
  :parents (example-lexer)
  :short "Match identifier characters to create an @(':id') or @(':keyword')
token, as appropriate."
  ((sin "The @(see sin) stobj."))
  :returns (mv (tok "The id/keyword token taken from the start of the input
                     stream, or @('nil') if the input stream does not start
                     with some valid identifier or keyword."
                    (equal (token-p tok) (if tok t nil)))
               (sin "The remaining input stream, with the leading token
                     removed."))
  (b* (((when (sin-endp sin))
        (mv nil sin))
       (car (sin-car sin))
       ((unless (char-in-charset-p car (letter-chars)))
        ;; not a valid keyword or identifier
        (mv nil sin))
       ((mv match sin)
        (sin-match-charset* (idtail-chars) sin))
       ((when (or (equal match "void")
                  (equal match "int")
                  (equal match "float")))
        (mv (make-token :type :keyword :text match) sin)))
    (mv (make-token :type :id :text match) sin))

  :prepwork
  ;; We need a lemma like this to justify that MATCH will always be non-empty
  ;; above.
  ((local (defthm idtail-char-p-when-letter-char-p
            (implies (letter-char-p x)
                     (idtail-char-p x)))))
  ///
  (def-sin-progress lex-id/keyword :hyp tok)
  (defthm lex-id/keyword-reconstruction
    (b* (((mv tok new-sin) (lex-id/keyword sin)))
      (implies tok
               (equal (append (explode (token->text tok))
                              (strin-left new-sin))
                      (strin-left sin))))))



(defsection newline-string
  :parents (example-lexer)
  :short "A string with just the newline character."
  (defmacro newline-string ()
    (implode (list #\Newline))))

(define lex-comment
  :parents (example-lexer)
  :short "Match comment characters to create an @(':comment') token."
  ((sin "The @(see sin) stobj."))
  :returns (mv (tok "A comment token taken from the start of the input stream,
                     or @('nil') if the input stream does not start with a
                     comment."
                    (equal (token-p tok) (if tok t nil)))
               (sin "The remaining input stream, with the leading comment
                     removed."))
  (b* ((comment-p (sin-matches-p "//" sin))
       ((unless comment-p)
        ;; Doesn't start with //, hence not a valid comment.
        (mv nil sin))
       ((mv match sin) (sin-match-through-lit (newline-string) sin))
       ((when match)
        (mv (make-token :type :comment :text match) sin))
       ;; Failed to find a newline before EOF.  That's fine, just match
       ;; everything and turn it into a comment.
       ((mv match sin) (sin-match-everything sin)))
    (mv (make-token :type :comment :text match) sin))
  ///
  (def-sin-progress lex-comment :hyp tok)
  (defthm lex-comment-reconstruction
    (b* (((mv tok new-sin) (lex-comment sin)))
      (implies tok
               (equal (append (explode (token->text tok))
                              (strin-left new-sin))
                      (strin-left sin))))))


(define lex1
  :parents (example-lexer)
  :short "Lex a single token from the input stream."
  ((sin "The @(see sin) stobj, which we assume still has text remaining."
        (not (sin-endp sin))))
  :returns (mv (tok    "The first token from the start of the input stream,
                        or @('nil') on failure."
                       (equal (token-p tok) (if tok t nil)))
               (sin    "The remaining input stream, with the leading token
                        removed."))
  (b* ((char1 (sin-car sin))

       ((when (char-in-charset-p char1 (whitespace-chars)))
        ;; Can only be whitespace
        (lex-whitespace sin))

       ((when (char-in-charset-p char1 (letter-chars)))
        ;; Can only be identifiers or keywords
        (lex-id/keyword sin))

       ((when (sin-matches-p "//" sin))
        ;; Must be a comment
        (lex-comment sin)))

    ;; Else, must be punctuation or invalid
    (lex-punctuation sin))
  ///
  (def-sin-progress lex1 :hyp tok)
  (defthm lex1-reconstruction
    (b* (((mv tok new-sin) (lex1 sin)))
      (implies tok
               (equal (append (explode (token->text tok))
                              (strin-left new-sin))
                      (strin-left sin))))))



(define lex*-exec (sin acc)
  :parents (example-lexer)
  :short "Tail-recursive version of @(see lex*) (to prevent stack overflows)."
  :returns (mv okp new-acc sin)
  :measure (len (strin-left sin))
  (b* (((when (sin-endp sin))
        (mv t acc sin))
       ((mv tok1 sin) (lex1 sin))
       ((unless tok1)
        (mv nil acc sin)))
    (lex*-exec sin (cons tok1 acc))))


(define lex*
  :parents (example-lexer)
  :short "Main lexer loop: completely tokenize the entire input stream."
  ((sin "The @(see sin) stobj."))
  :returns (mv (okp     "Did we lex everything successfully?"
                        booleanp :rule-classes :type-prescription)
               (tokens  "The tokens we've collected."
                        tokenlist-p)
               (sin))
  :measure (len (strin-left sin))
  (mbe :logic (b* (((when (sin-endp sin))
                    (mv t nil sin))
                   ((mv tok1 sin) (lex1 sin))
                   ((unless tok1)
                    (mv nil nil sin))
                   ((mv okp rest-tokens sin) (lex* sin))
                   (ans (cons tok1 rest-tokens)))
                (mv okp ans sin))
       :exec (b* (((mv okp acc sin) (lex*-exec sin nil)))
               ;; To halve the memory usage, you could use a ttag to convert
               ;; this reverse into an nreverse.
               (mv okp (reverse acc) sin)))
  :verify-guards nil
  ///
  (defthm lex*-exec-removal
    (b* (((mv okp tokens new-sin) (lex* sin)))
      (equal (lex*-exec sin acc)
             (mv okp (revappend tokens acc) new-sin)))
    :hints(("Goal" :in-theory (enable lex*-exec))))

  (defthm true-listp-of-lex*-tokens
    (true-listp (mv-nth 1 (lex* sin)))
    :rule-classes :type-prescription)

  (verify-guards lex*)

  (defthm tokenlist-all-text-of-lex*
    (b* (((mv okp tokens ?new-sin) (lex* sin)))
      (implies okp
               (equal (tokenlist-all-text tokens)
                      (implode (strin-left sin)))))))


(define lex-main
  :parents (example-lexer)
  :short "Wrapper: lex the entire input stream or fail with a good error
message."
  ((sin "The @(see sin) stobj."))
  :returns (mv (errmsg "@('nil') on success, or a good error message (as a
                        string) on failure."
                       (or (stringp errmsg)
                           (not errmsg))
                       :rule-classes :type-prescription)
               (tokens tokenlist-p)
               (sin "Empty input stream on success, or the remaining part of
                     the input stream on failure."))
  (b* (((mv okp tokens sin) (lex* sin))
       ((when okp)
        ;; Good, no error
        (mv nil tokens sin))
       ;; Else, lexing failed.  Get the current position.
       (errmsg (cat (sin-file sin)
                    ":" (natstr (sin-line sin))
                    ":" (natstr (sin-col sin))
                    ": syntax error near: "
                    ;; Show up to 20 characters of offending text
                    (sin-firstn (min 20 (sin-len sin)) sin)
                    (newline-string))))
    (mv errmsg tokens sin))
  ///
  (defthm tokenlist-all-text-of-lex-main
    ;; Obvious consequence of the lex* property
    (b* (((mv errmsg tokens ?new-sin) (lex-main sin)))
      (implies (not errmsg)
               (equal (tokenlist-all-text tokens)
                      (implode (strin-left sin)))))))


(define lex-string
  :parents (example-lexer)
  :short "Complete wrapper: lex an ACL2 string."
  :long "<p>This just takes care of creating a local @(see sin) to use, then
calls @(see lex-main) to do the real work.</p>"
  ((contents stringp "What to lex, typically the contents of the file.")
   &key
   ((filename stringp "The name of the file, used only for better error
                       messages.")
    '""))
  :returns (mv (errmsg "@('nil') on success, or an error message (as a string)
                        on failure."
                       (or (stringp errmsg)
                           (not errmsg))
                       :rule-classes :type-prescription)
               (tokens tokenlist-p))
  (with-local-stobj
    sin
    (mv-let (errmsg tokens sin)
      (b* ((sin (sin-init contents filename sin)))
        (lex-main sin))
      (mv errmsg tokens)))
  ///
  (defthm tokenlist-all-text-of-lex-string
    ;; Obvious consequence of lex-main property
    (b* (((mv errmsg tokens) (lex-string contents :filename filename)))
      (implies (not errmsg)
               (equal (tokenlist-all-text tokens)
                      (if (stringp contents)
                          contents
                        ""))))))

#||

;; some examples that lex successfully:

(lex-string "a")
(lex-string "a + b")
(lex-string "a ++ b")

(lex-string
"int a;
 int b; // comment!
 a + b;")

(lex-string "a + b * c ++ d / ")
(lex-string "a+b*c++d/")

;; some examples that cause errors:

(lex-string "a + _invalid // identifiers must start with a letter")
            :filename "foo.c")

(lex-string "a + _invalid" :filename "foo.c")

(lex-string "a + b + #3 + 4" :filename "foo.c")

||#
