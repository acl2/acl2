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

(defsection lex-strings
  :parents (lexer)
  :short "Handling of string literals."

  :long "<p>String literals are sequences of ASCII characters that are
enclosed in \"double quotes.\"</p>

<p>Verilog-2005 and SystemVerilog-2012 have some differences here, and Verilog
implementations like Verilog-XL, NCVerilog, and VCS generally don't seem to
follow the standard.  We discuss some of the nuances here.</p>


<h5>Line Continuations</h5>

<p>The Verilog-2005 standard says that strings are contained on a single line,
but SystemVerilog-2012 adds a line continuation sequence, @('\\<newline>'),
which doesn't become part of the string.  That is,</p>

@({
     $display(\"Hello \\
     World\");
})

<p>Is invalid in Verilog-2005, but prints @('\"Hello World\"') in
SystemVerilog-2012.  While Verilog-XL doesn't appear to implement this new
syntax, but NCVerilog and VCS both do.</p>

<p>What counts as a newline?  Let @('NL') denote the newline character and
@('CR') denote carriage return.  Both NCVerilog and VCS appear to accept only
exactly @('\\ NL'):</p>

<ul>

<li>They report syntax errors complaining about multi-line strings when given
string literals that include @('\\ CR NL'); presumably they are translating
@('\\ CR') into a plain @('CR') and then hitting the @('NL'), thinking it is
not escaped.</li>

<li>They accept @('\\ CR'), but leave a @('CR') character in the output, so it
seems they are treating this as just an escaped CR character instead of a line
continuation.</li>

<li>They accept @('\\ NL CR'), but leave a @('CR') character in the output.
So, it seems they just matching the @('\\ NL') part as the line continuation,
and then treating the CR as an ordinary character.</li>

</ul>

<p>We will allow or prohibit line continuations based on the @(see
vl-edition-p) being used.  When it is allowed, we will accept only exactly
@('\\ NL'), like VCS and NCVerilog.</p>


<h5>Basic Escapes</h5>

<p>Verilog-2005 (Section 3.6.3) <i>could</i> be interpreted as prohibiting raw
tab characters, but experimentation with tools like Verilog-XL, NCVerilog, and
VCS suggest that tab characters should be accepted in strings, so we allow
them.</p>

<p>Strings in both Verilog-2005 and SystemVerilog-2012 can make use of the
following, basic escape sequences:</p>

<table>
<tr> <td> @(' \\n ')   </td> <td> Newline           </td> </tr>
<tr> <td> @(' \\t ')   </td> <td> Tab               </td> </tr>
<tr> <td> @(' \\\\ ')  </td> <td> @('\\') character </td> </tr>
<tr> <td> @(' \\\" ')  </td> <td> @('\"') character </td> </tr>
</table>

<p>These sequences seem to work on Verilog-XL, NCVerilog, and VCS without any
issues.</p>


<h5>Octal Escapes</h5>

<p>Verilog-2005 also allows for the encoding of arbitrary ASCII characters
using an octal escape sequences.</p>


<table>
<tr> <td> @(' \\ddd ') </td>
     <td> Character by octal code of 1-3 digits @('(0 <= d <= 7)')</td>
</tr>
</table>

<p>Note that 377 in octal is 255 in decimal, so a sequence such as @('\\378')
is not really a valid character code.  The Verilog standard says that
implementations may issue an error in such cases.  In practice, none of
Verilog-XL, NCVerilog, or VCS complain about @('\\378').  Even so, it seems
reasonable for us to notice and fail with errors in this case.</p>

<p>The Verilog-2005 standard explains the handling of @('\\ddd') nicely.
Unfortunately, SystemVerilog-2012 has made quite a muddle of it.</p>

<p>In the SystemVerilog standard, they have replaced the informal description
of octal digits with the more precise @('octal_digit') production.  This leads
to a mess because @('octal_digit'), used in numbers, can include X and Z
digits.  To work around this stupid new problem they've just caused, the
standard goes on to restrict these octal_digits not to be x_digits or z_digits.
They further say that an @('x_digit') or @('z_digit') cannot follow a
@('\\ddd') sequence with fewer than 3 characters.</p>

<p>This means that certain sequences like @('\\40x') or @('\\40?'), which were
perfectly valid in Verilog 2005, are no longer valid in SystemVerilog 2012.</p>

<p>In practice, none of Verilog-XL, NCVerilog, or VCS implements this
restriction.  However, since these are probably a very rare and esoteric thing
to write in the first place, it seems reasonable for VL to prohibit these
sequences.</p>


<h5>Additional SystemVerilog-2012 Escapes</h5>

<p>The SystemVerilog-2012 standard introduces some new, simple escape
sequences:</p>

<table>
<tr> <td> @(' \\v ')   </td> <td> Vertical Tab      </td> </tr>
<tr> <td> @(' \\f ')   </td> <td> Form Feed         </td> </tr>
<tr> <td> @(' \\a ')   </td> <td> Bell              </td> </tr>
</table>

<p>None of these sequences seem to be implemented on Verilog-XL, NCVerilog, or
VCS.  Instead, when these tools encounter sequences like @('\\v'), they seem to
simply produce @('v'), and for @('\\x00'), they simply produce @('x00').</p>

<p>We nevertheless try to follow the standard, and properly implement these
escape sequences for suitable @(see vl-edition-p)s.</p>

<p>SystemVerilog 2012 also adds some ambiguous language (Section 5.9) that
<i>Nonprinting and other special characters are preceded with a backslash</i>.
It's not clear whether this is just an informal description of what the escape
tables mean, or if we're supposed to allow any non-printable character to be
included in a string literal by preceding it with a backslash.  But it appears
(cosims/str) that other tools allow most characters to be preceded by a
backslash in which case they expand to themselves.  We try to be compatible
where we think this seems safe.</p>



<h5>Hex escapes</h5>

<p>SystemVerilog-2012 also adds a way to specify characters by hexadecimal
character codes:</p>

<table>
<tr> <td> @(' \\xdd ') </td> <td> Character by one or two hex digits</td> </tr>
</table>

<p>As with octal digits, the definition is muddled by the use of
@('hex_digit'), which leads to the possibility of x and z characters that then
have to be ruled out separately.</p>

<p>None of Verilog-XL, SystemVerilog, or VCS seems to implement hex escapes
yet.  Instead, sequences like @('\\x0') simply get displayed as @('x0'), as if
the @('\\x') is being converted into an @('x').  VL implements the
standard.</p>")

(local (xdoc::set-default-parents lex-strings))

(define vl-read-octal-string-escape
  :short "Try to read a @('\\ddd') string escape."

  ((echars "Characters we're lexing.  We know these start with a leading
            backslash, but we don't know what follows.  For instance, we might
            be at a valid octal string escape like @('\\123'), or we might be
            at some other kind of escape like @('\\n')."
           (and (vl-echarlist-p echars)
                (consp echars)
                (consp (cdr echars))
                (eql (vl-echar->char (first echars)) #\\))))

  :returns
  (mv (char/nil "If we're at a valid octal sequence, the particular
                 @(see characterp) indicated by that sequence."
                (equal (characterp char/nil)
                       (if char/nil t nil)))
      (prefix   (iff prefix char/nil))
      (remainder))

  :long "<p>This can fail for two reasons.</p>

<ul>

<li>We might just be looking at some non-octal escape sequence like @('\\n'),
which is fine and we'll fail without complaining about it.</li>

<li>We might encounter an invalid octal sequence, e.g., @('\\378') or
@('\\40x').  In this case, we'll print a message to standard output before
failing.</li>

</ul>

<p>BOZO consider revamping this to return an error @(see msg) instead of
printing.</p>"

  :prepwork
  ((local (defthm vl-echar-digit-value-upper-bound
            (implies (force (vl-echar-p echar))
                     (< (vl-echar-digit-value echar 8)
                        8))
            :rule-classes :linear
            :hints(("Goal" :in-theory (enable vl-echar-digit-value))))))

  (b* ((echar1 (first echars))
       (echar2 (second echars))
       (val2   (vl-echar-digit-value echar2 8))
       ((unless val2)
        ;; Not an octal digit, so it's not even an octal escape.
        (mv nil nil echars))

       ((unless (consp (cddr echars)))
        (mv (cw "Lexer error (~s0): EOF during string escape sequence: ~s1<EOF>~%"
                (vl-location-string (vl-echar->loc (car echars)))
                (vl-echarlist->string (list echar1 echar2)))
            nil echars))
       (echar3 (third echars))
       ((when (or (vl-z-digit-echar-p echar3)
                  (vl-x-digit-echar-p echar3)))
        (mv (cw "Lexer error (~s0): invalid string escape sequence: ~s1 ~
                  (x, z, and ? digits aren't allowed here)~%"
                (vl-location-string (vl-echar->loc (car echars)))
                (vl-echarlist->string (list echar1 echar2 echar3)))
            nil echars))
       (val3 (vl-echar-digit-value echar3 8))
       ((unless val3)
        ;; Just one octal digit.  Cannot overflow.
        (mv (code-char val2)
            (list echar1 echar2)
            (cddr echars)))

       ((unless (consp (cdddr echars)))
        (mv (cw "Lexer error (~s0): EOF during string escape sequence: ~s1<EOF>~%"
                (vl-location-string (vl-echar->loc (car echars)))
                (vl-echarlist->string (list echar1 echar2 echar3)))
            nil echars))
       (echar4 (fourth echars))
       ((when (or (vl-z-digit-echar-p echar4)
                  (vl-x-digit-echar-p echar4)))
        (mv (cw "Lexer error (~s0): invalid string escape sequence: ~s1 ~
                  (x, z, and ? digits aren't allowed here)~%"
                (vl-location-string (vl-echar->loc (car echars)))
                (vl-echarlist->string (list echar1 echar2 echar3 echar4)))
            nil echars))
       (val4 (vl-echar-digit-value echar4 8))
       ((unless val4)
        ;; Just two octal digits.  Cannot overflow.
        (mv (code-char (the (unsigned-byte 8)
                         (+ (the (unsigned-byte 8)
                              (* 8 (the (unsigned-byte 8) val2)))
                            (the (unsigned-byte 8) val3))))
            (list echar1 echar2 echar3)
            (cdddr echars)))

       ;; Three octal digits.  Might overflow.
       ((the (unsigned-byte 12) value)
        (+ (the (unsigned-byte 12) (* 64 (the (unsigned-byte 8) val2)))
           (the (unsigned-byte 8)
             (+ (the (unsigned-byte 8) (* 8 (the (unsigned-byte 8) val3)))
                (the (unsigned-byte 8) val4)))))
       ((unless (< value 256))
        (mv (cw "Lexer error (~s0): invalid escape sequence: ~s1. ~
                  (characters beyond \\377 aren't valid)~%"
                (vl-location-string (vl-echar->loc (car echars)))
                (vl-echarlist->string (list echar1 echar2 echar3 echar4)))
            nil echars)))
    (mv (code-char value)
        (list echar1 echar2 echar3 echar4)
        (cddddr echars))))

(def-prefix/remainder-thms vl-read-octal-string-escape
  :prefix-n 1
  :remainder-n 2)


(define vl-read-hex-string-escape
  :short "Try to read a @('\\xdd') string escape."

  ((echars "Characters we're lexing, starting with the leading backslash."
           (and (vl-echarlist-p echars)
                (consp echars)
                (consp (cdr echars))
                (eql (vl-echar->char (first echars)) #\\))))
  :returns
  (mv (char/nil "The character indicated by this hex sequence on success,
                 or @('nil') if this is not a valid escape sequence."
                (equal (characterp char/nil)
                       (if char/nil t nil)))
      (prefix (iff prefix char/nil))
      (remainder))

  :prepwork
  ((local (defthm vl-echar-digit-value-upper-bound
            (implies (force (vl-echar-p echar))
                     (< (vl-echar-digit-value echar 16)
                        16))
            :rule-classes :linear
            :hints(("Goal" :in-theory (enable vl-echar-digit-value))))))

  (b* ((echar1 (first echars))
       (echar2 (second echars))
       ((unless (eql (vl-echar->char echar2) #\x))
        ;; Not a hex escape.
        (mv nil nil echars))

       ((unless (consp (cddr echars)))
        (mv (cw "Lexer error (~s0): EOF during string escape sequence: ~s1<EOF>~%"
                (vl-location-string (vl-echar->loc (car echars)))
                (vl-echarlist->string (list echar1 echar2)))
            nil echars))
       (echar3 (third echars))
       ((when (or (vl-z-digit-echar-p echar3)
                  (vl-x-digit-echar-p echar3)))
        (mv (cw "Lexer error (~s0): invalid string escape sequence: ~s1 ~
                  (x/z/? aren't allowed after \\x)~%"
                (vl-location-string (vl-echar->loc (car echars)))
                (vl-echarlist->string (list echar1 echar2 echar3)))
            nil echars))

       (val3 (vl-echar-digit-value echar3 16))
       ((unless val3)
        (mv (cw "Lexer error (~s0): invalid string escape sequence: ~s1 ~
                  (hex digit required after \\x)~%"
                (vl-location-string (vl-echar->loc (car echars)))
                (vl-echarlist->string (list echar1 echar2 echar3)))
            nil echars))

       ((unless (consp (cdddr echars)))
        (mv (cw "Lexer error (~s0): EOF during string escape sequence: ~s1<EOF>~%"
                (vl-location-string (vl-echar->loc (car echars)))
                (vl-echarlist->string (list echar1 echar2 echar3)))
            nil echars))
       (echar4 (fourth echars))
       ((when (or (vl-z-digit-echar-p echar4)
                  (vl-x-digit-echar-p echar4)))
        (mv (cw "Lexer error (~s0): invalid string escape sequence: ~s1 ~
                  (x/z/? aren't allowed after \\x)~%"
                (vl-location-string (vl-echar->loc (car echars)))
                (vl-echarlist->string (list echar1 echar2 echar3 echar4)))
            nil echars))
       (val4 (vl-echar-digit-value echar4 16))
       ((unless val4)
        ;; Just one hex digit, can't overflow.
        (mv (code-char val3)
            (list echar1 echar2 echar3)
            (cdddr echars))))

    ;; Two hex digits, still can't overflow.
    (mv (code-char (the (unsigned-byte 8)
                     (+ (the (unsigned-byte 8) (* 16 (the (unsigned-byte 8) val3)))
                        (the (unsigned-byte 8) (the (unsigned-byte 8) val4)))))
        (list echar1 echar2 echar3 echar4)
        (cddddr echars))))

(def-prefix/remainder-thms vl-read-hex-string-escape
  :prefix-n 1
  :remainder-n 2)

(defchar string-self-escape
  (or
   ;; Most lowercase letters -- on other tools, all lowercase letters other
   ;; than 'n' and 't' seem to get escaped to themselves.  (These tools fail to
   ;; handle the new \v, \f, \a, and \x escapes, which we will rule out).
   (and (str::down-alpha-p x)
        (not (member x '(#\n #\t #\v #\f #\a #\x))))
   ;; On other tools, all uppercase letters seem to get escaped to themselves.
   (str::up-alpha-p x)
   ;; On other tools, 8 and 9 seem to get escaped to themselves.  0-7 do not
   ;; because they would be interpreted as octal byte sequences
   (consp (member x '(#\8 #\9)))
   ;; On other tools, these other random printable characters seem to get
   ;; escaped to themselves.
   (consp (member x '(#\~ #\! #\@ #\# #\$ #\%
                      #\^ #\& #\* #\( #\) #\_
                      #\- #\+ #\= #\[ #\] #\{ #\}
                      #\| #\; #\: #\< #\> #\,
                      #\. #\? #\/ #\` #\Space))))
  :parents (vl-read-string-escape-sequence)
  :short "I'm not sure the standard really says this is OK, but it seems like
          these characters escape to themselves when preceded by a backslash on
          other tools.")

(define vl-read-string-escape-sequence
  :short "Try to read a string escape sequence."

  ((echars "Characters we're lexing, starting with the leading backslash."
           (and (vl-echarlist-p echars)
                (consp echars)
                (equal (vl-echar->char (car echars)) #\\)))

   (st     "Governs which escape sequences are allowed."
           vl-lexstate-p))

  :returns
  (mv (char/nil "The interpretation of this escape sequence <b>if any</b>.
                 This will be @('nil') for line continuations, and also in
                 case of any error."
                (equal (characterp char/nil)
                       (if char/nil t nil)))
      (prefix   "The matched characters on success.  You have to check the
                 @('prefix') rather than @('char/nil') to determine success,
                 because line continuations don't result in any character.")
      (remainder))

  (b* (((unless (consp (cdr echars)))
        (mv nil nil echars))
       (echar1 (first echars))
       (echar2 (second echars))
       (char2 (vl-echar->char echar2))
       ((when (eql char2 #\n)) (mv #\Newline (list echar1 echar2) (cddr echars)))
       ((when (eql char2 #\t)) (mv #\Tab     (list echar1 echar2) (cddr echars)))
       ((when (eql char2 #\\)) (mv #\\       (list echar1 echar2) (cddr echars)))
       ((when (eql char2 #\")) (mv #\"       (list echar1 echar2) (cddr echars)))
       ((when (vl-echar-digit-value echar2 8))
        (vl-read-octal-string-escape echars))
       ((vl-lexstate st) st)
       ((unless st.strextsp)
        (mv nil nil echars))

       ((when (eql char2 #\Newline))
        ;; Line continuation.  Subtle.  No character, but still successful.
        (mv nil (list echar1 echar2) (cddr echars)))
       ((when (eql char2 #\v))
        (mv (vertical-tab-char) (list echar1 echar2) (cddr echars)))
       ((when (eql char2 #\f))
        (mv #\Page (list echar1 echar2) (cddr echars)))
       ((when (eql char2 #\a))
        (mv (code-char 7) (list echar1 echar2) (cddr echars)))
       ((when (eql char2 #\x))
        (vl-read-hex-string-escape echars))

       ((when (vl-string-self-escape-p char2))
        (mv char2 (list echar1 echar2) (cddr echars))))

    (mv (cw "Lexer error (~s0): invalid string escape sequence: ~s1~%"
            (vl-location-string (vl-echar->loc (car echars)))
            (vl-echarlist->string (list echar1 echar2)))
        nil echars)))

(def-prefix/remainder-thms vl-read-string-escape-sequence
  :formals (echars config)
  :prefix-n 1
  :remainder-n 2)


(define vl-read-string-aux
  :short "Main loop for reading string literals."
  ((echars vl-echarlist-p "Characters we're reading")
   (eacc "Accumulator for actual characters read (e.g., #\\n),
          as extended characters")
   (vacc "Accumulator for interpreted characters read (e.g., a newline),
          as ordinary characters")
   (st   vl-lexstate-p))
  :returns
  (mv (error "nil on success, stringp error message on failure."
             (equal (stringp error)
                    (if error t nil)))
      (eacc vl-echarlist-p
            :hyp (and (force (vl-echarlist-p echars))
                      (force (vl-echarlist-p eacc))))
      (vacc character-listp
            :hyp (and (force (vl-echarlist-p echars))
                      (force (character-listp vacc))))
      (remainder vl-echarlist-p
                 :hyp (force (vl-echarlist-p echars))))

  (b* (((unless (consp echars))
        (mv "the file ends before the string is closed." eacc vacc echars))
       (echar1 (first echars))
       ((the character char1) (vl-echar->char echar1))
       ((when (eql char1 #\"))
        (mv nil (cons echar1 eacc) vacc (rest echars)))
       ((when (eql char1 #\Newline))
        (mv "the line ends before the string is closed." eacc vacc echars))
       ((when (eql char1 #\\))
        (b* (((mv char prefix remainder)
              (vl-read-string-escape-sequence echars st))
             ((unless prefix)
              (mv "the string contains an invalid escape sequence."
                  eacc vacc echars))
             (eacc (revappend prefix eacc))
             (vacc (if char (cons char vacc) vacc)))
          (vl-read-string-aux remainder eacc vacc st))))
    (vl-read-string-aux (cdr echars)
                        (cons echar1 eacc)
                        (cons char1 vacc)
                        st))
  ///
  (defthm vl-read-string-aux-of-nil
    (implies (atom echars)
             (mv-nth 0 (vl-read-string-aux echars eacc vacc st))))

  (defthm true-listp-of-vl-read-string-aux.eacc
    (equal (true-listp (mv-nth 1 (vl-read-string-aux echars eacc vacc st)))
           (true-listp eacc)))

  (defthm true-listp-of-vl-read-string-aux.remainder
    (equal (true-listp (mv-nth 3 (vl-read-string-aux echars eacc vacc st)))
           (true-listp echars)))

  (defthm revappend-of-vl-read-string-aux
    (equal (append (rev (mv-nth 1 (vl-read-string-aux echars eacc vacc st)))
                   (mv-nth 3 (vl-read-string-aux echars eacc vacc st)))
           (append (rev eacc)
                   echars)))

  (defthm acl2-count-of-vl-read-string-aux-weak
    (<= (acl2-count (mv-nth 3 (vl-read-string-aux echars eacc vacc st)))
        (acl2-count echars))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-vl-read-string-aux-strong
    (implies (not (mv-nth 0 (vl-read-string-aux echars eacc vacc st)))
             (< (acl2-count (mv-nth 3 (vl-read-string-aux echars eacc vacc st)))
                (acl2-count echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force))))))


(define vl-read-string
  ((echars "Characters we're reading, which we assume begin with a double-quote."
           (and (vl-echarlist-p echars)
                (consp echars)
                (equal (vl-echar->char (car echars)) #\")))
   (st     vl-lexstate-p))
  :returns
  (mv (str? "NIL on failure.  A stringp with the interpreted characters from
             the string literal otherwise. That is, we'll have already expanded
             things like @('\\n') into proper newline characters."
            (equal (stringp str?)
                   (if str? t nil)))
      (prefix "The matched characters, starting at the opening double quote
               and extending through the closing double quote, inclusively,
               on success."
              (iff prefix str?))
      remainder)
  (b* (((mv err eacc vacc remainder)
        (vl-read-string-aux (cdr echars) nil nil st))
       ((when err)
        (mv (cw "Lexer error (~s0) while reading string: ~s1.~%"
                (vl-location-string (vl-echar->loc (car echars)))
                err)
            nil echars)))
    (mv (str::rchars-to-string vacc)
        (cons (car echars) (reverse eacc))
        remainder)))

(def-prefix/remainder-thms vl-read-string
  :formals (echars st)
  :prefix-n 1
  :remainder-n 2)

(define vl-lex-string
  :short "Lexing of string literals."
  ((echars vl-echarlist-p)
   (breakp booleanp)
   (st     vl-lexstate-p))
  :returns (mv token/nil remainder)
  (b* (((unless (and (consp echars)
                     (eql (vl-echar->char (car echars)) #\")))
        (mv nil echars))
       ((mv string prefix remainder)
        (vl-read-string echars st))
       ((unless string)
        (mv nil echars))
       (token (make-vl-stringtoken :etext prefix
                                   :expansion string
                                   :breakp (and breakp t))))
      (mv token remainder)))

(def-token/remainder-thms vl-lex-string
  :formals (echars breakp st))
