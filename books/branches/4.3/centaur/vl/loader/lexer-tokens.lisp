; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
(include-book "../parsetree") ; kinda yucky, for bitlist-p, etc.
(local (include-book "../util/arithmetic"))


(defsection vl-keyword-lookup
  :parents (lexer)
  :short "Determine if a string is a Verilog keyword."

  :long "<p>For every keyword, <tt>foo</tt>, we associate a symbol whose
name is <tt>:vl-kwd-foo</tt>, which we use as the token's type.  For instance,
<tt>:vl-kwd-module</tt> is our token type for the <tt>module</tt> keyword.</p>

<p>@(call vl-keyword-lookup) is given a string <tt>x</tt> of characters that
have just been read.  If <tt>x</tt> is a keyword, we return the corresponding
symbol.  Otherwise, we return <tt>nil</tt>.</p>

<p>The function just carries out a fast alist lookup against the pre-computed
<tt>*vl-keyword-table*</tt>.</p>

@(def vl-keyword-lookup)"

  (defconst *vl-list-of-keywords*

; The following list of keywords is copied and pasted from Annex B, "List of
; Keywords", on page 510 of the 2005 Verilog spec.

    (list "always"         "ifnone"               "rnmos"
          "and"            "incdir"               "rpmos"
          "assign"         "include"              "rtran"
          "automatic"      "initial"              "rtranif0"
          "begin"          "inout"                "rtranif1"
          "buf"            "input"                "scalared"
          "bufif0"         "instance"             "showcancelled"
          "bufif1"         "integer"              "signed"
          "case"           "join"                 "small"
          "casex"          "large"                "specify"
          "casez"          "liblist"              "specparam"
          "cell"           "library"              "strong0"
          "cmos"           "localparam"           "strong1"
          "config"         "macromodule"          "supply0"
          "deassign"       "medium"               "supply1"
          "default"        "module"               "table"
          "defparam"       "nand"                 "task"
          "design"         "negedge"              "time"
          "disable"        "nmos"                 "tran"
          "edge"           "nor"                  "tranif0"
          "else"           "noshowcancelled"      "tranif1"
          "end"            "not"                  "tri"
          "endcase"        "notif0"               "tri0"
          "endconfig"      "notif1"               "tri1"
          "endfunction"    "or"                   "triand"
          "endgenerate"    "output"               "trior"
          "endmodule"      "parameter"            "trireg"
          "endprimitive"   "pmos"                 "unsigned1"
          "endspecify"     "posedge"              "use"
          "endtable"       "primitive"            "uwire"
          "endtask"        "pull0"                "vectored"
          "event"          "pull1"                "wait"
          "for"            "pulldown"             "wand"
          "force"          "pullup"               "weak0"
          "forever"        "pulsestyle_onevent"   "weak1"
          "fork"           "pulsestyle_ondetect"  "while"
          "function"       "rcmos"                "wire"
          "generate"       "real"                 "wor"
          "genvar"         "realtime"             "xnor"
          "highz0"         "reg"                  "xor"
          "highz1"         "release"
          "if"             "repeat"
          ;; Per the footnote, we add unsigned since it is also reserved.
          "unsigned"

          ;; RAM EXTENSION -- VL adds the following keywords to support rams.

          "VL_RAM"
          "VL_ENDRAM"
          "VL_DATA_WIDTH"
          "VL_ADDR_WIDTH"
          "VL_READ"
          "VL_WRITE"
          "VL_CLEAR"

          ;; OVERRIDE FILES EXTENSIONS

          "VL_OVERRIDE"
          "VL_ORIGINAL"
          "VL_REPLACEMENT"
          "VL_REQUIRE"
          "VL_ENDOVERRIDE"

          ))

  (defun vl-make-keyword-table (x)
    (declare (xargs :verify-guards nil))
    (if (consp x)
        (hons-acons (car x)
                    (intern (str::cat "VL-KWD-" (string-upcase (car x))) "KEYWORD")
                    (vl-make-keyword-table (cdr x)))
      nil))

  (defconst *vl-keyword-table*
    (vl-make-keyword-table *vl-list-of-keywords*))

  (definlined vl-keyword-lookup (x)
    (declare (xargs :guard (stringp x)))
    (cdr (hons-get x *vl-keyword-table*)))

  (defthm symbolp-of-vl-keyword-lookup
    (and (symbolp (vl-keyword-lookup x))
         (not (equal (vl-keyword-lookup x) t)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable vl-keyword-lookup)))))





; Now we turn our attention to the whitespace, comments, operators, and
; punctuation tokens.  These are relatively more straightforward.

(defconst *vl-plain-nonkeyword-types*
  (list :vl-ws          ;;; any amount of contiguous whitespace
        :vl-comment     ;;; any single-line or block comment
        :vl-arrow       ;;; ->
        :vl-lbrack      ;;; [
        :vl-rbrack      ;;; ]
        :vl-lparen      ;;; (
        :vl-rparen      ;;; )
        :vl-lcurly      ;;; {
        :vl-rcurly      ;;; }
        :vl-colon       ;;; :
        :vl-pluscolon   ;;; +:
        :vl-minuscolon  ;;; -:
        :vl-semi        ;;; ;
        :vl-pound       ;;; #
        :vl-comma       ;;; ,
        :vl-dot         ;;; .
        :vl-atsign      ;;; @
        :vl-beginattr   ;;; (*
        :vl-endattr     ;;; *)
        :vl-equalsign   ;;; =
        :vl-plus        ;;; +
        :vl-minus       ;;; -
        :vl-times       ;;; *
        :vl-div         ;;; /
        :vl-rem         ;;; %
        :vl-power       ;;; **
        :vl-xor         ;;; ^
        :vl-qmark       ;;; ?
        :vl-lt          ;;; <
        :vl-lte         ;;; <=
        :vl-shl         ;;; <<
        :vl-ashl        ;;; <<<
        :vl-gt          ;;; >
        :vl-gte         ;;; >=
        :vl-shr         ;;; >>
        :vl-ashr        ;;; >>>
        :vl-cne         ;;; !==
        :vl-neq         ;;; !=
        :vl-lognot      ;;; !
        :vl-nand        ;;; ~&
        :vl-nor         ;;; ~|
        :vl-xnor        ;;; ~^ and ^~
        :vl-bitnot      ;;; ~
        :vl-logor       ;;; ||
        :vl-bitor       ;;; |
        :vl-logand      ;;; &&
        :vl-bitand      ;;; &
        :vl-ceq         ;;; ===
        :vl-eq          ;;; ==
        :vl-andandand   ;;; &&&
        ))

(defconst *vl-plaintoken-types*
  (append *vl-plain-nonkeyword-types*
          (strip-cdrs *vl-keyword-table*)))

(defund vl-plaintoken-type-p (x)
  (declare (xargs :guard t))
  (if (member x *vl-plaintoken-types*)
      t
    nil))

(defthm vl-plaintoken-type-p-of-vl-keyword-lookup
  (implies (vl-keyword-lookup str)
           (vl-plaintoken-type-p (vl-keyword-lookup str)))
  :hints(("Goal" :in-theory (enable vl-plaintoken-type-p vl-keyword-lookup))))

(defthm symbolp-when-vl-plaintoken-type-p
  (implies (vl-plaintoken-type-p x)
           (and (symbolp x)
                (not (equal x t))
                (not (equal x nil))))
  :rule-classes :compound-recognizer
  :hints(("Goal" :in-theory (enable vl-plaintoken-type-p))))

(defaggregate vl-plaintoken
  (etext type)
  :tag :vl-plaintoken
  :legiblep nil
  :require ((vl-echarlist-p-of-vl-plaintoken->etext
             (vl-echarlist-p etext))
            (type-of-vl-plaintoken->etext
             (and (consp etext)
                  (true-listp etext))
             :rule-classes :type-prescription)
            (vl-plaintoken-type-p-of-vl-plaintoken->type
             (vl-plaintoken-type-p type))
            )
  :parents (lexer)
  :short "Tokens for whitespace, comments, operators, punctuation, and keywords."
  :long "<p>Our lexer returns \"plain tokens\" when it encounters whitespace,
 comments, operators, punctuation, and keywords.  We call these tokens
 <i>plain</i> because they do not have any extended information beyond what
 kind of token they are and which characters formed them.</p>

<p><tt>etext</tt> is the @(see vl-echarlist-p) that gave rise to this token
from the Verilog source code.  Having this text is useful for error reporting,
e.g., it includes location information.</p>

<p><tt>type</tt> is a keyword symbol that identifies what kind of token this
is.  There are many valid types for plain tokens.  In fact, there are about 125
symbols for the various keyword tokens (see @(srclink *vl-keyword-table*)) and
about 50 other symbols for the various whitespace, comments, operators,
punctuation tokens, and real numbers (see @(srclink
*vl-plain-nonkeyword-types*)).</p>")

(defthm type-of-vl-plaintoken->type
  (implies (force (vl-plaintoken-p x))
           (and (symbolp (vl-plaintoken->type x))
                (not (equal (vl-plaintoken->type x) t))
                (not (equal (vl-plaintoken->type x) nil))))
  :rule-classes :type-prescription
  :hints(("Goal"
          :in-theory (disable symbolp-when-vl-plaintoken-type-p)
          :use ((:instance symbolp-when-vl-plaintoken-type-p
                           (x (vl-plaintoken->type x)))))))



(defaggregate vl-stringtoken
  (etext expansion)
  :tag :vl-stringtoken
  :legiblep nil
  :require ((vl-echarlist-p-of-vl-stringtoken->etext
             (vl-echarlist-p etext))
            (type-of-vl-stringtoken->etext
             (and (consp etext)
                  (true-listp etext))
             :rule-classes :type-prescription)
            (stringp-of-vl-stringtoken->expansion
             (stringp expansion)
             :rule-classes :type-prescription)
            )
  :parents (lexer)

  :short "Tokens for string literals."

  :long "<p><tt>etext</tt> is a @(see vl-echarlist-p) that gave rise to this
string literal from the Verilog source.  Note that this text is \"verbatim\"
and, as a consequence, character sequences like <tt>\\n</tt> will not have been
converted into newlines, etc.</p>

<p><tt>expansion</tt> is an ordinary ACL2 string object that holds the
\"expanded\" version of the string literal.  That is, character sequences like
<tt>\\n</tt> in the <tt>etext</tt> become real newline characters in the
<tt>expansion</tt>.</p>

<p>The expansion is carried out per Table 3-1, on page 14 of the Verilog
specification.</p>")



(defaggregate vl-idtoken
  (etext name)
  :tag :vl-idtoken
  :legiblep nil
  :require ((vl-echarlist-p-of-vl-idtoken->etext
             (vl-echarlist-p etext))
            (type-of-vl-idtoken->etext
             (and (consp etext)
                  (true-listp etext))
             :rule-classes :type-prescription)
            (stringp-of-vl-idtoken->name
             (stringp name)
             :rule-classes :type-prescription)
            )
  :parents (lexer)
  :short "Tokens for ordinary identifiers."
  :long "<p>Note that we distinguish between plain identifiers and system
identifiers, such as <tt>$display</tt>.  We only generate a <tt>vl-idtoken</tt>
for a plain identifier.</p>

<p><tt>etext</tt> is the actual characters that gave rise to this token.</p>

<p><tt>name</tt> is an ACL2 string whose characters are formed from the
<tt>etext</tt>.  Usually <tt>name</tt> matches up with <tt>etext</tt>, but note
that from Section 3.7.1 that in escaped identifiers, the initial backslash is
not considered to be part of the identifier's name.  So, if we process a
Verilog file which includes the identifiers <tt>\\foo</tt> and <tt>foo</tt>,
the resulting tokens will have different <tt>etext</tt> but the same
<tt>name</tt>.</p>")

(deflist vl-idtoken-list-p (x)
  (vl-idtoken-p x)
  :elementp-of-nil nil
  :parents (lexer))



(defaggregate vl-sysidtoken
  (etext name)
  :tag :vl-sysidtoken
  :legiblep nil
  :require ((vl-echarlist-p-of-vl-sysidtoken->etext
             (vl-echarlist-p etext))
            (type-of-vl-sysidtoken->etext
             (and (consp etext)
                  (true-listp etext))
             :rule-classes :type-prescription)
            (stringp-of-vl-sysidtoken->name
             (stringp name)
             :rule-classes :type-prescription)
            )
  :parents (lexer)
  :short "Tokens for system identifiers.")



(defaggregate vl-realtoken
  (etext)
  :tag :vl-realtoken
  :legiblep nil
  :require ((vl-echarlist-p-of-vl-realtoken->etext
             (vl-echarlist-p etext))
            (type-of-vl-realtoken->etext
             (and (consp etext)
                  (true-listp etext))
             :rule-classes :type-prescription))
  :parents (lexer)
  :short "Tokens for real numbers."
  :long "<p>We don't really support real numbers in most of our tools, so the
token just includes the original characters and does not try to interpret them
in any sort of useful way.</p>")





(defund vl-inttoken-constraint-p (width value bits)
  (declare (xargs :guard (and (posp width)
                              (vl-maybe-natp value)
                              (vl-bitlist-p bits))))
  (if value
      ;; Has a value: must not have bits, and value must be in bounds.
      (and (not bits)
           (< value (expt 2 width)))
    ;; Has no value: must have the right number of bits.
    (equal (len bits) width)))

(defaggregate vl-inttoken
  (etext width signedp value bits wasunsized)
  :tag :vl-inttoken
  :legiblep nil
  :require ((vl-echarlist-p-of-vl-inttoken->etext
             (vl-echarlist-p etext))
            (type-of-vl-inttoken->etext
             (and (consp etext)
                  (true-listp etext))
             :rule-classes :type-prescription)
            (posp-of-vl-inttoken->width
             (posp width)
             :rule-classes :type-prescription)
            (booleanp-of-vl-inttoken->signedp
             (booleanp signedp)
             :rule-classes :type-prescription)
            (vl-maybe-natp-of-vl-inttoken->value
             (vl-maybe-natp value)
             :rule-classes :type-prescription)
            (vl-bitlist-p-of-vl-inttoken->bits
             (vl-bitlist-p bits))
            (vl-inttoken-constraint-p-of-vl-inttoken-parts
             (vl-inttoken-constraint-p width value bits))
            (booleanp-of-vl-inttoken->wasunsized
             (booleanp wasunsized)
             :rule-classes :type-prescription)
            )
  :parents (lexer)
  :short "Tokens for integer constants."
  :long "<p>Integers are our most complicated tokens.</p>

<p><tt>etext</tt> represents the actual characters from the source code
that led to this token.</p>

<p><tt>width</tt> is a positive natural number that indicates the width of this
integer.  Note that VL acts like a 32-bit Verilog implementation and, for an
unsized integer like <tt>3</tt> or <tt>'b101</tt> we will produce a 32-bit
token.  See also some additional discussion in @(see vl-constint-p).</p>

<p><tt>signedp</tt> is a boolean that says whether this number is to be
treated as a signed value.  This is decided by in Section 3.5.1, and for
instance <tt>19</tt> is signed, <tt>'d19</tt> is unsigned, <tt>'sd19</tt> is
signed, and so on.</p>

<p><tt>value</tt> is <tt>nil</tt> if there are any <tt>X</tt> or <tt>Z</tt>
digits.  Otherwise, it contains a natural number that reflects the actual value
of this constant.  Note that there are no negative numbers because, e.g.,
<tt>-5</tt> basically is interpreted as a unary-minus operator applied to
5.</p>

<p><tt>bits</tt> is only used when there are any <tt>X</tt> or <tt>Z</tt>
digits.  In these cases, it is a @(see vl-bitlist-p) of precisely
<tt>width</tt>-many bits.</p>

<p><tt>wasunsized</tt> indicates whether the constant was originally unsized.
If so, VL acts like a 32-bit implementation and the resulting integer will have
width 32.  See also @(see vl-constint-p).</p>")

(defthm upper-bound-of-vl-inttoken->value
  (implies (and (vl-inttoken->value x)
                (force (vl-inttoken-p x)))
           (< (vl-inttoken->value x)
              (expt 2 (vl-inttoken->width x))))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal"
          :in-theory (e/d (vl-inttoken-constraint-p)
                          (vl-inttoken-constraint-p-of-vl-inttoken-parts))
          :use ((:instance vl-inttoken-constraint-p-of-vl-inttoken-parts)))))

(defthm len-of-vl-inttoken->bits
  (implies (force (vl-inttoken-p x))
           (equal (len (vl-inttoken->bits x))
                  (if (vl-inttoken->value x)
                      0
                    (vl-inttoken->width x))))
  :hints(("Goal"
          :in-theory (e/d (vl-inttoken-constraint-p)
                          (vl-inttoken-constraint-p-of-vl-inttoken-parts))
          :use ((:instance vl-inttoken-constraint-p-of-vl-inttoken-parts)))))



(defsection vl-token-p
  :parents (lexer)
  :short "Token structure produced by our lexer."
  :long "<p><tt>vl-token-p</tt> is a sum-of-products style recognizer.  Every
token is either a</p>

<ul>
  <li>@(see vl-plaintoken-p),</li>
  <li>@(see vl-inttoken-p),</li>
  <li>@(see vl-idtoken-p),</li>
  <li>@(see vl-sysidtoken-p),</li>
  <li>@(see vl-stringtoken-p), or</li>
  <li>@(see vl-realtoken-p).</li>
</ul>

<p>Our lexer produces a token list for our parser to consume.  Any token can be
inspected with the following operations:</p>

<ul>
  <li>@(see vl-token->type), get the token's type</li>
  <li>@(see vl-token->etext), get the token's actual text</li>
  <li>@(see vl-token->loc), get the location of the token's first character</li>
</ul>

<h3>Definition</h3>

@(def vl-token-p)"

  (defund vl-token-p (x)
    (declare (xargs :guard t))
    (mbe :logic
         (or (vl-plaintoken-p x)
             (vl-stringtoken-p x)
             (vl-idtoken-p x)
             (vl-sysidtoken-p x)
             (vl-inttoken-p x)
             (vl-realtoken-p x))
         :exec
         (case (tag x)
           (:vl-plaintoken  (vl-plaintoken-p x))
           (:vl-idtoken     (vl-idtoken-p x))
           (:vl-inttoken    (vl-inttoken-p x))
           (:vl-sysidtoken  (vl-sysidtoken-p x))
           (:vl-stringtoken (vl-stringtoken-p x))
           (otherwise       (vl-realtoken-p x)))))

  (local (in-theory (enable vl-token-p)))

  (defthm vl-token-p-when-vl-plaintoken-p
    (implies (vl-plaintoken-p x)
             (vl-token-p x)))

  (defthm vl-token-p-when-vl-stringtoken-p
    (implies (vl-stringtoken-p x)
             (vl-token-p x)))

  (defthm vl-token-p-when-vl-idtoken-p
    (implies (vl-idtoken-p x)
             (vl-token-p x)))

  (defthm vl-token-p-when-vl-sysidtoken-p
    (implies (vl-sysidtoken-p x)
             (vl-token-p x)))

  (defthm vl-token-p-when-vl-inttoken-p
    (implies (vl-inttoken-p x)
             (vl-token-p x)))

  (defthm vl-token-p-when-vl-realtoken-p
    (implies (vl-realtoken-p x)
             (vl-token-p x))))



(defsection vl-token->type
  :parents (vl-token-p)
  :short "Get the type of a token."
  :long "<p><b>Signature:</b> @(call vl-token->type) returns a keyword
symbol.</p>

<p>For plain tokens, the symbol we return is the <tt>type</tt> field of the
@(see vl-plaintoken-p).  You can see a list of the valid types by inspecting
the value of @(srclink *vl-plaintoken-types*), and examples include
<tt>:vl-ws</tt> for whitespace tokens, <tt>:vl-kwd-always</tt> for the Verilog
keyword <tt>always</tt>, and <tt>:vl-comma</tt> for commas.</p>

<p>For any other token, such as @(see vl-inttoken-p) or @(see vl-idtoken-p)
objects, the type is simply the <tt>tag</tt> from the @(see defaggregate).
That is, an integer token has type <tt>:vl-inttoken</tt>, an identifier has
type <tt>:vl-idtoken</tt>, and so on.</p>

<p>This is one of the most heavily used functions throughout our parser, so its
efficient implementation is beneficial.</p>

<h3>Definition</h3>

@(def vl-token->type)"

  (definlined vl-token->type (x)
    (declare (xargs :guard (vl-token-p x)
                    :guard-hints (("Goal" :in-theory (enable vl-token-p)))))
    (mbe :logic
         (if (vl-plaintoken-p x)
             (vl-plaintoken->type x)
           (tag x))
         :exec
         (let ((tag (tag x)))
           (if (eq tag :vl-plaintoken)
               (vl-plaintoken->type x)
             tag))))

  (local (in-theory (enable vl-token->type)))

  (defthm symbolp-of-vl-token-type
    (implies (force (vl-token-p x))
             (symbolp (vl-token->type x)))
    :hints(("Goal" :in-theory (enable vl-token-p))))

  (defthm vl-token->type-possibilities
    (implies (vl-token-p x)
             (member (vl-token->type x)
                     (append (list :vl-inttoken
                                   :vl-stringtoken
                                   :vl-idtoken
                                   :vl-sysidtoken
                                   :vl-realtoken)
                             *vl-plaintoken-types*)))
    :rule-classes nil
    :hints(("Goal"
            :in-theory (e/d (vl-token-p vl-plaintoken-type-p)
                            (vl-plaintoken-type-p-of-vl-plaintoken->type))
            :use ((:instance vl-plaintoken-type-p-of-vl-plaintoken->type)))))

  (defthm vl-inttoken-p-when-token-of-type-inttoken
    (implies (and (equal (vl-token->type x) :vl-inttoken)
                  (force (vl-token-p x)))
             (equal (vl-inttoken-p x)
                    t))
    :hints(("Goal" :in-theory (enable vl-token-p
                                      vl-plaintoken->type
                                      vl-plaintoken-p))))

  (defthm vl-stringtoken-p-when-token-of-type-stringtoken
    (implies (and (equal (vl-token->type x) :vl-stringtoken)
                  (force (vl-token-p x)))
             (equal (vl-stringtoken-p x)
                    t))
    :hints(("Goal" :in-theory (enable vl-token-p
                                      vl-plaintoken->type
                                      vl-plaintoken-p))))

  (defthm vl-realtoken-p-when-token-of-type-realtoken
    (implies (and (equal (vl-token->type x) :vl-realtoken)
                  (force (vl-token-p x)))
             (equal (vl-realtoken-p x)
                    t))
    :hints(("Goal" :in-theory (enable vl-token-p
                                      vl-plaintoken->type
                                      vl-plaintoken-p))))

  (defthm vl-idtoken-p-when-token-of-type-idtoken
    (implies (and (equal (vl-token->type x) :vl-idtoken)
                  (force (vl-token-p x)))
             (equal (vl-idtoken-p x)
                    t))
    :hints(("Goal" :in-theory (enable vl-token-p
                                      vl-plaintoken->type
                                      vl-plaintoken-p))))

  (defthm vl-sysidtoken-p-when-token-of-type-sysidtoken
    (implies (and (equal (vl-token->type x) :vl-sysidtoken)
                  (force (vl-token-p x)))
             (equal (vl-sysidtoken-p x)
                    t))
    :hints(("Goal" :in-theory (enable vl-token-p
                                      vl-token->type
                                      vl-plaintoken->type
                                      vl-plaintoken-p)))))


(defsection vl-token->etext
  :parents (vl-token-p)
  :short "Get the original text for a token."
  :long "<p><b>Signature:</b> @(call vl-token->etext) returns a @(see
vl-echarlist-p).</p>

<p>Each of the valid @(see vl-token-p) objects includes an <tt>etext</tt> field
which reflects the original characters in the source code that led to the
creation of that token.  Accordingly, we can extract the <tt>etext</tt> from
any token.</p>

<h3>Definition</h3>

@(def vl-token->etext)"

  (definlined vl-token->etext (x)
    (declare (xargs :guard (vl-token-p x)
                    :verify-guards nil))

; Every token has ETEXT, so we can get the ETEXT from any token.

    (mbe :logic
         (cond ((vl-plaintoken-p x)   (vl-plaintoken->etext x))
               ((vl-idtoken-p x)      (vl-idtoken->etext x))
               ((vl-sysidtoken-p x)   (vl-sysidtoken->etext x))
               ((vl-inttoken-p x)     (vl-inttoken->etext x))
               ((vl-stringtoken-p x)  (vl-stringtoken->etext x))
               ((vl-realtoken-p x)    (vl-realtoken->etext x)))
         :exec

; Special optimization.  Things just happen to line up this way.  If you change
; the format of any of the tokens, you'll have to rewrite this.

         (case (tag x)
           (:vl-inttoken (caadr x))
           (:vl-realtoken (cdr x))
           (t (cadr x)))))

  (encapsulate
   ()
   (local (defthmd crock
            (and (equal (vl-idtoken->etext x) (cadr x))
                 (equal (vl-sysidtoken->etext x) (cadr x))
                 (equal (vl-inttoken->etext x) (caadr x))
                 (equal (vl-stringtoken->etext x) (cadr x))
                 (equal (vl-realtoken->etext x) (cdr x))
                 (equal (vl-plaintoken->etext x) (cadr x)))
            :hints(("Goal" :in-theory (enable vl-idtoken->etext
                                              vl-sysidtoken->etext
                                              vl-inttoken->etext
                                              vl-stringtoken->etext
                                              vl-realtoken->etext
                                              vl-plaintoken->etext)))))

   (verify-guards vl-token->etext
                  :hints(("Goal" :in-theory (enable vl-token-p))
                         (and stable-under-simplificationp
                              '(:in-theory (enable crock
                                                   vl-plaintoken-p
                                                   vl-inttoken-p
                                                   vl-idtoken-p
                                                   vl-stringtoken-p
                                                   vl-realtoken-p
                                                   vl-sysidtoken-p
                                                   vl-plaintoken-type-p))))))

  (local (in-theory (enable vl-token->etext)))

  (defthm vl-echarlist-p-of-vl-token->etext
    (implies (force (vl-token-p x))
             (vl-echarlist-p (vl-token->etext x))))

  (defthm consp-of-vl-token->etext
    (implies (force (vl-token-p x))
             (consp (vl-token->etext x)))
    :hints(("Goal" :in-theory (enable vl-token-p))))

  (defthm true-listp-of-vl-token->etext
    (implies (force (vl-token-p x))
             (true-listp (vl-token->etext x))))

  (defthm vl-token->etext-of-vl-plaintoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext))
                  (force (vl-plaintoken-type-p name)))
             (equal (vl-token->etext (vl-plaintoken etext name))
                    etext)))

  (defthm vl-token->etext-of-vl-stringtoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext))
                  (force (stringp expansion)))
             (equal (vl-token->etext (vl-stringtoken etext expansion))
                    etext)))

  (defthm vl-token->etext-of-vl-idtoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext))
                  (force (stringp name)))
             (equal (vl-token->etext (vl-idtoken etext name))
                    etext)))

  (defthm vl-token->etext-of-vl-sysidtoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext))
                  (force (stringp name)))
             (equal (vl-token->etext (vl-sysidtoken etext name))
                    etext)))

  (defthm vl-token->etext-of-vl-inttoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext))
                  (force (posp width))
                  (force (booleanp signedp))
                  (force (vl-maybe-natp value))
                  (force (vl-inttoken-constraint-p width value bits))
                  (force (vl-bitlist-p bits))
                  (force (booleanp wasunsized)))
             (equal (vl-token->etext (vl-inttoken etext width signedp value bits wasunsized))
                    etext)))

  (defthm vl-token->etext-of-vl-realtoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext)))
             (equal (vl-token->etext (vl-realtoken etext))
                    etext))))



(defsection vl-token->loc
  :parents (vl-token-p)
  :short "Get the starting location for a token."
  :long "<p><b>Signature:</b> @(call vl-token->loc) returns a @(see
vl-location-p)</p>.

<p>Because <tt>etext</tt> is always required to be a non-empty, we can say that
 each token has a location, namely the location of its first character.</p>

<h3>Definition and Theorems</h3>

@(def vl-token->loc)
@(thm vl-location-p-of-vl-token-loc)"

  (definlined vl-token->loc (x)
    (declare (xargs :guard (vl-token-p x)))
    (vl-echar->loc (car (vl-token->etext x))))

  (defthm vl-location-p-of-vl-token-loc
    (implies (force (vl-token-p x))
             (equal (vl-location-p (vl-token->loc x))
                    t))
    :hints(("Goal" :in-theory (enable vl-token->loc vl-token-p)))))

(deflist vl-tokenlist-p (x)
  (vl-token-p x)
  :elementp-of-nil nil
  :parents (lexer))

(deflist vl-tokenlistlist-p (x)
  (vl-tokenlist-p x)
  :elementp-of-nil t
  :parents (lexer))


(defsection vl-tokenlist->etext

  (defmapappend vl-tokenlist->etext (x)
    (vl-token->etext x)
    :transform-true-list-p t
    :guard (vl-tokenlist-p x)
    :parents (lexer)
    :short "Append together all the text for a list of tokens.")

  (local (in-theory (enable vl-tokenlist->etext)))

  (defthm vl-echarlist-p-of-vl-tokenlist->etext
    (implies (force (vl-tokenlist-p x))
             (vl-echarlist-p (vl-tokenlist->etext x)))))



;; (defund vl-tokentype-p (x)
;;   (declare (xargs :guard t))
;;   (or (vl-plaintoken-type-p x)
;;       (eq x :vl-stringtoken)
;;       (eq x :vl-idtoken)
;;       (eq x :vl-sysidtoken)
;;       (eq x :vl-realtoken)
;;       (eq x :vl-inttoken)))

;; (deflist vl-tokentype-list-p (x)
;;   (vl-tokentype-p x)
;;   :guard t
;;   :elementp-of-nil nil)


(definline vl-token->string (x)
  (declare (xargs :guard (vl-token-p x)))
  (vl-echarlist->string (vl-token->etext x)))

