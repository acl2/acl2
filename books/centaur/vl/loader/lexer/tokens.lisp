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
(include-book "keywords")
(include-book "../../util/bits")
(include-book "../../util/echars")
(local (include-book "../../util/arithmetic"))

(defsection tokens
  :parents (lexer)
  :short "Representation of tokens structures that are produced by the lexer.")

(local (xdoc::set-default-parents tokens))


(defval *vl-2005-plain-nonkeywords*
  :parents (vl-plaintoken-p)
  :short "Simple token types other than keywords (e.g., whitespace, comments,
operators, and other kinds of separators and punctuation.) for use with
Verilog-2005 source code."
  :showval t

  '(:vl-ws             ;;; any amount of contiguous whitespace
    :vl-comment        ;;; any single-line or block comment
    :vl-arrow          ;;; ->
    :vl-lbrack         ;;; [
    :vl-rbrack         ;;; ]
    :vl-lparen         ;;; (
    :vl-rparen         ;;; )
    :vl-lcurly         ;;; {
    :vl-rcurly         ;;; }
    :vl-colon          ;;; :
    :vl-pluscolon      ;;; +:
    :vl-minuscolon     ;;; -:
    :vl-semi           ;;; ;
    :vl-pound          ;;; #
    :vl-comma          ;;; ,
    :vl-dot            ;;; .
    :vl-atsign         ;;; @
    :vl-beginattr      ;;; (*
    :vl-endattr        ;;; *)
    :vl-equalsign      ;;; =
    :vl-plus           ;;; +
    :vl-minus          ;;; -
    :vl-times          ;;; *
    :vl-div            ;;; /
    :vl-rem            ;;; %
    :vl-power          ;;; **
    :vl-xor            ;;; ^
    :vl-qmark          ;;; ?
    :vl-lt             ;;; <
    :vl-lte            ;;; <=
    :vl-shl            ;;; <<
    :vl-ashl           ;;; <<<
    :vl-gt             ;;; >
    :vl-gte            ;;; >=
    :vl-shr            ;;; >>
    :vl-ashr           ;;; >>>
    :vl-cne            ;;; !==
    :vl-neq            ;;; !=
    :vl-lognot         ;;; !
    :vl-nand           ;;; ~&
    :vl-nor            ;;; ~|
    :vl-xnor           ;;; ~^ and ^~
    :vl-bitnot         ;;; ~
    :vl-logor          ;;; ||
    :vl-bitor          ;;; |
    :vl-logand         ;;; &&
    :vl-bitand         ;;; &
    :vl-ceq            ;;; ===
    :vl-eq             ;;; ==
    :vl-andandand      ;;; &&&
    )

  ///
  (assert! (uniquep *vl-2005-plain-nonkeywords*)))

(defval *vl-2012-plain-nonkeywords*
  :parents (vl-plaintoken-p)
  :short "Simple token types other than keywords (e.g., whitespace, comments,
operators, and other kinds of separators and punctuation.) for use with
SystemVerilog 2012 source code."
  :showval t

  (append *vl-2005-plain-nonkeywords*
          ;; New additions for SystemVerilog
          '(:vl-eqarrow    ;;; =>
            :vl-arrowgt    ;;; ->>
            :vl-stararrow  ;;; *>
            :vl-bararrow   ;;; |->
            :vl-bareqarrow ;;; |=>
            :vl-equiv      ;;; <->
            :vl-wildeq     ;;; ==?
            :vl-wildneq    ;;; !=?
            :vl-dotstar    ;;; .*
            :vl-coloneq    ;;; :=
            :vl-colonslash ;;; :/
            :vl-scope      ;;; ::
            :vl-pounddash  ;;; #-#
            :vl-poundequal ;;; #=#
            :vl-poundpound ;;; ##
            :vl-plusplus   ;;; ++
            :vl-minusminus ;;; --
            :vl-pluseq     ;;; +=
            :vl-minuseq    ;;; -=
            :vl-timeseq    ;;; *=
            :vl-diveq      ;;; /=
            :vl-remeq      ;;; %=
            :vl-andeq      ;;; &=
            :vl-oreq       ;;; |=
            :vl-xoreq      ;;; ^=
            :vl-shleq      ;;; <<=
            :vl-shreq      ;;; >>=
            :vl-ashleq     ;;; <<<=
            :vl-ashreq     ;;; >>>=
            :vl-quote      ;;; '
            :vl-$          ;;; $
            :vl-$root      ;;; $root
            :vl-$unit      ;;; $unit
            :vl-1step      ;;; 1step
            ))
  ///
  (assert! (subsetp *vl-2005-plain-nonkeywords*
                    *vl-2012-plain-nonkeywords*))

  (assert! (uniquep *vl-2012-plain-nonkeywords*)))


(defval *vl-plaintoken-types*
  :parents (vl-plaintoken-p)
  :short "All valid plain tokens that can arise from any kind of supported
source code (Verilog-2005, SystemVerilog-2012, and VL Extensions)."
  :showval t
  (append *vl-2012-plain-nonkeywords*
          (alist-vals (vl-full-keyword-table)))
  ///
  (assert! (uniquep *vl-plaintoken-types*))
  (assert! (symbol-listp *vl-plaintoken-types*)))

(defval *vl-plaintoken-fal*
  :parents (vl-plaintoken-p)
  :short "Fast alist for looking up plain token types."
  :showval t
  (make-lookup-alist *vl-plaintoken-types*))

(define vl-plaintokentype-p (x)
  :parents (vl-plaintoken-p)
  :long "<p>We usually don't need to execute this, but it's used in, e.g., the
definition of @(see vl-plaintoken-p), so we probably want it to be fast if
we're ever actually running @(see vl-tokenlist-p).</p>"
  (consp (hons-get x *vl-plaintoken-fal*))
  ///
  (local (defruled crock
           (implies (and (symbol-listp (alist-keys al))
                         (hons-assoc-equal key al))
                    (symbolp key))))

  (defrule symbolp-when-vl-plaintokentype-p
    (implies (vl-plaintokentype-p x)
             (and (symbolp x)
                  (not (equal x t))
                  (not (equal x nil))))
    :rule-classes :compound-recognizer
    ;; Stupid hack to get it to do the proof by executing symbol-listp
    :use ((:instance crock
                     (key x)
                     (al *vl-plaintoken-fal*)))
    :enable vl-plaintokentype-p
    :disable (acl2::hons-assoc-equal-of-cons)))

(deflist vl-plaintokentypelist-p (x)
  :elementp-of-nil nil
  (vl-plaintokentype-p x))


(defsection vl-plaintokentype-p-of-vl-keyword-lookup
  :parents (vl-keyword-lookup vl-plaintokentype-p)
  :short "Dumb technical lemma showing that we always get a good plaintoken as
          long as we're using a valid keyword table."

  (local (defrule l0
           (implies (vl-plaintokentypelist-p (alist-vals table))
                    (equal (vl-plaintokentype-p (cdr (hons-assoc-equal key table)))
                           (if (hons-assoc-equal key table)
                               t
                             nil)))))

  (local (defrule l1
           (equal (vl-plaintokentype-p
                   (cdr (hons-assoc-equal key (vl-full-keyword-table))))
                  (if (cdr (hons-assoc-equal key (vl-full-keyword-table)))
                      t
                    nil))
           :enable ((vl-full-keyword-table))
           :use ((:instance l0 (table (vl-full-keyword-table))))))

  (local (defrule l2
           (implies (vl-keyword-table-p table)
                    (equal (cdr (hons-get str table))
                           (and (hons-get str table)
                                (cdr (hons-get str (vl-full-keyword-table))))))
           :rule-classes nil
           :enable vl-keyword-table-p))

  (defrule vl-plaintokentype-p-of-vl-keyword-lookup
    (implies (vl-keyword-table-p table)
             (equal (vl-plaintokentype-p (vl-keyword-lookup str table))
                    (if (vl-keyword-lookup str table)
                        t
                      nil)))
    :enable vl-keyword-lookup
    :use ((:instance l2))))




(defaggregate vl-plaintoken
  :short "Tokens for whitespace, comments, operators, punctuation, and keywords."
  :tag nil ;; Subtle, see below
  :layout :fulltree

  ((type  vl-plaintokentype-p
          "A keyword symbol that identifies what kind of token this is.
           There are many valid types for plain tokens, including
           @(see lex-keywords) and other kinds of nonkeyword tokens.")

   (etext (and (vl-echarlist-p etext)
               (consp etext))
          "The actual text that gave rise to this token from the Verilog source
           code.  Having this text is useful for error reporting, e.g., it
           includes location information.")

   (breakp booleanp :rule-classes :type-prescription
           "Was this the first token on a line."))

  :long "<p>Our lexer returns \"plain tokens\" when it encounters whitespace,
comments, operators, punctuation, and keywords.  We call these tokens
<i>plain</i> because they do not have any extended information beyond what kind
of token they are and which characters formed them.</p>

<p>Subtle.  As an optimization, our plaintokens are tagless aggregates, and the
particular ordering of the fields ensures that the type of the plaintoken is
simply its @('car').  We exploit this in the executable versions of functions
like @(see vl-token->etext).</p>"

  ///
  (defrule type-of-vl-plaintoken->type
    (implies (force (vl-plaintoken-p x))
             (and (symbolp (vl-plaintoken->type x))
                  (not (equal (vl-plaintoken->type x) t))
                  (not (equal (vl-plaintoken->type x) nil))))
    :rule-classes :type-prescription
    :disable symbolp-when-vl-plaintokentype-p
    :use ((:instance symbolp-when-vl-plaintokentype-p
                     (x (vl-plaintoken->type x)))))

  (defruled tag-when-vl-plaintoken-p
    (implies (vl-plaintoken-p x)
             (equal (tag x) (vl-plaintoken->type x)))
    :enable (vl-plaintoken->type tag)))


(defaggregate vl-stringtoken
  :short "Tokens for string literals."
  :tag :vl-stringtoken
  :layout :fulltree

  ((etext (and (vl-echarlist-p etext)
               (consp etext))
          "The characters that gave rise to this string literal from the
           Verilog source.  Note that this text is \"verbatim\" and, as a
           consequence, character sequences like @('\\n') will not have been
           converted into newlines, etc.")

   (expansion stringp
              :rule-classes :type-prescription
              "An ordinary ACL2 string object that holds the \"expanded\"
               version of the string literal.  That is, character sequences
               like @('\\n') in the @('etext') become real newline characters
               in the @('expansion').")

   (breakp booleanp :rule-classes :type-prescription
           "Was this the first token on a line."))

  :long "<p>The expansion is carried out per Table 3-1, on page 14 of the
Verilog-2005 standard.  BOZO is that still valid for SystemVerilog?</p>")


(defaggregate vl-idtoken
  :short "Tokens for ordinary identifiers."
  :tag :vl-idtoken
  :layout :fulltree

  ((etext (and (vl-echarlist-p etext)
               (consp etext))
          "The characters that gave rise to this token.")

   (name stringp
         :rule-classes :type-prescription
         "An ACL2 string with the name of this literal.")

   (breakp booleanp :rule-classes :type-prescription
           "Was this the first token on a line."))

  :long "<p>Note that we distinguish between plain identifiers and system
identifiers, such as @('$display').  We only generate a @('vl-idtoken') for a
plain identifier.</p>

<p>Usually @('name') matches up with @('etext'), but note that from Section
3.7.1 of the Verilog-2005 standard that in escaped identifiers, the initial
backslash is not considered to be part of the identifier's name.  So, if we
process a Verilog file which includes the identifiers @('\\foo') and @('foo'),
the resulting tokens will have different @('etext') but the same @('name').</p>

<p>BOZO double check that this is still how things work in SystemVerilog, give
updated references to the standard.</p>")

(deflist vl-idtoken-list-p (x)
  :elementp-of-nil nil
  (vl-idtoken-p x))


(defaggregate vl-sysidtoken
  :short "Tokens for system identifiers."
  :tag :vl-sysidtoken
  :layout :fulltree

  ((etext (and (vl-echarlist-p etext)
               (consp etext))
          "The characters that gave rise to this token.")

   (name stringp
         :rule-classes :type-prescription
         "An ACL2 string with the name of this system identifier.")

   (breakp booleanp :rule-classes :type-prescription
           "Was this the first token on a line.")))


(defaggregate vl-realtoken
  :short "Tokens for real numbers."
  :tag :vl-realtoken
  :layout :fulltree

  ((etext (and (vl-echarlist-p etext)
               (consp etext))
          "The characters that gave rise to this token.")

   (breakp booleanp :rule-classes :type-prescription
           "Was this the first token on a line."))

  :long "<p>We don't really support real numbers in most of our tools, so the
token just includes the original characters and does not try to interpret them
in any sort of useful way.</p>")


(define vl-inttoken-constraint-p
  :parents (vl-inttoken-p)
  :short "Basic well-formedness constraint on integer tokens."
  ((width posp)
   (value maybe-natp)
   (bits vl-bitlist-p))
  :returns okp
  :long "<p>If the integer has a value, then it must not have bits and the
value must be in bounds for its width.</p>

<p>If the integer has no value, then it must have exactly the right number of
bits.</p>"
  (if value
      (and (not bits)
           (< value (expt 2 width)))
    (equal (len bits) width)))

(defaggregate vl-inttoken
  :short "Tokens for integer constants."
  :tag :vl-inttoken
  :layout :tree

  ((etext (and (vl-echarlist-p etext)
               (consp etext))
          "The characters that gave rise to this token.")

   (width   posp
            :rule-classes :type-prescription
            "The width of this integer.  Note that VL acts like a 32-bit
             Verilog implementation and, for an unsized integer like @('3') or
             @(''b101') we will produce a 32-bit token.  See also some
             additional discussion in @(see vl-constint).")

   (signedp booleanp
            :rule-classes :type-prescription
            "Whether this number is to be treated as a signed value.  This is
             decided by in Section 3.5.1, and for instance @('19') is signed,
             @(''d19') is unsigned, @(''sd19') is signed, and so on.")

   (value   maybe-natp
            :rule-classes :type-prescription
            "@('nil') when there are any @('X') or @('Z') digits.  Otherwise,
             a natural number that reflects the actual value of this constant.
             Note that there are no negative numbers because, e.g., @('-5')
             basically is interpreted as a unary-minus operator applied to 5.")

   (bits    vl-bitlist-p
            "@('nil') unless there are any @('X') or @('Z') digits.  In these
             cases, it is a msb-first @(see vl-bitlist) that contains exactly
             @('width')-many bits.")

   (wasunsized booleanp
               :rule-classes :type-prescription
               "Indicates whether the constant was originally unsized.  If so,
                VL acts like a 32-bit implementation and the resulting integer
                will have width 32.  Mainly intended for use in linting or
                other kinds of heuristic checking.  See also @(see
                vl-constint) and @(see vl-weirdint).")

   (breakp booleanp :rule-classes :type-prescription
           "Was this the first token on a line."))

  :require ((vl-inttoken-constraint-p-of-vl-inttoken-parts
             (vl-inttoken-constraint-p width value bits)))
  ///
  (defrule upper-bound-of-vl-inttoken->value
    (implies (and (vl-inttoken->value x)
                  (force (vl-inttoken-p x)))
             (< (vl-inttoken->value x)
                (expt 2 (vl-inttoken->width x))))
    :rule-classes ((:rewrite) (:linear))
    :enable (vl-inttoken-constraint-p)
    :disable (vl-inttoken-constraint-p-of-vl-inttoken-parts)
    :use ((:instance vl-inttoken-constraint-p-of-vl-inttoken-parts)))

  (defrule len-of-vl-inttoken->bits
    (implies (force (vl-inttoken-p x))
             (equal (len (vl-inttoken->bits x))
                    (if (vl-inttoken->value x)
                        0
                      (vl-inttoken->width x))))
    :enable (vl-inttoken-constraint-p)
    :disable (vl-inttoken-constraint-p-of-vl-inttoken-parts)
    :use ((:instance vl-inttoken-constraint-p-of-vl-inttoken-parts))))


(defaggregate vl-extinttoken
  :short "Tokens for unsized, unbased SystemVerilog integers, e.g., @(''0'),
@(''1'), @(''x'), and @(''z')."
  :tag :vl-extinttoken
  :layout :fulltree

  ((etext (and (vl-echarlist-p etext)
               (consp etext))
          "The characters that gave rise to this token.")

   (breakp booleanp :rule-classes :type-prescription
           "Was this the first token on a line.")

   (value vl-bit-p
          "The kind of extended integer this is.")))


(defaggregate vl-timetoken
  :short "Tokens for time literals, like @('3ns') or @('45.617us')."
  :tag :vl-timetoken
  :layout :fulltree

  ((etext (and (vl-echarlist-p etext)
               (consp etext))
          "The characters that gave rise to this token.")

   (quantity stringp
             :rule-classes :type-prescription
             "An ACL2 string with the amount.  In practice, the amount should
              match either @('unsigned_number') or @('fixed_point_number'),
              e.g., @('\"3\"') or @('\"45.617\"').  We don't try to process
              this further because (1) we don't expect it to matter for much,
              and (2) ACL2 doesn't really support fixed point numbers.")

   (units  vl-timeunit-p
           "The kind of time unit this is, e.g., seconds, milliseconds,
            microseconds, ...")

   (breakp booleanp :rule-classes :type-prescription
           "Was this the first token on a line.")))


(define vl-token-p (x)
  :short "Token structure produced by our lexer."
  :long "<p>@('vl-token-p') is a sum-of-products style recognizer.  Every token
is one of the following:</p>

<ul>
  <li>@(see vl-plaintoken-p)</li>
  <li>@(see vl-inttoken-p)</li>
  <li>@(see vl-idtoken-p)</li>
  <li>@(see vl-sysidtoken-p)</li>
  <li>@(see vl-stringtoken-p)</li>
  <li>@(see vl-realtoken-p)</li>
  <li>@(see vl-timetoken-p)</li>
  <li>@(see vl-extinttoken-p)</li>
</ul>

<p>Our lexer produces a token list for our parser to consume.  Any token can be
inspected with the following operations:</p>

<ul>
  <li>@(see vl-token->type), get the token's type</li>
  <li>@(see vl-token->etext), get the token's actual text</li>
  <li>@(see vl-token->loc), get the location of the token's first character</li>
</ul>"

  :guard-hints(("Goal" :in-theory (enable tag-when-vl-plaintoken-p)))
  (mbe :logic
       (or (vl-idtoken-p x)
           (vl-inttoken-p x)
           (vl-sysidtoken-p x)
           (vl-stringtoken-p x)
           (vl-realtoken-p x)
           (vl-timetoken-p x)
           (vl-extinttoken-p x)
           (vl-plaintoken-p x))
       :exec
       (case (tag x)
         (:vl-idtoken     (vl-idtoken-p x))
         (:vl-inttoken    (vl-inttoken-p x))
         (:vl-sysidtoken  (vl-sysidtoken-p x))
         (:vl-stringtoken (vl-stringtoken-p x))
         (:vl-realtoken   (vl-realtoken-p x))
         (:vl-timetoken   (vl-timetoken-p x))
         (:vl-extinttoken (vl-extinttoken-p x))
         (otherwise       (vl-plaintoken-p x))))
  ///
  (defrule vl-token-p-when-vl-plaintoken-p
    (implies (vl-plaintoken-p x)
             (vl-token-p x)))

  (defrule vl-token-p-when-vl-stringtoken-p
    (implies (vl-stringtoken-p x)
             (vl-token-p x)))

  (defrule vl-token-p-when-vl-idtoken-p
    (implies (vl-idtoken-p x)
             (vl-token-p x)))

  (defrule vl-token-p-when-vl-sysidtoken-p
    (implies (vl-sysidtoken-p x)
             (vl-token-p x)))

  (defrule vl-token-p-when-vl-inttoken-p
    (implies (vl-inttoken-p x)
             (vl-token-p x)))

  (defrule vl-token-p-when-vl-realtoken-p
    (implies (vl-realtoken-p x)
             (vl-token-p x)))

  (defrule vl-token-p-when-vl-timetoken-p
    (implies (vl-timetoken-p x)
             (vl-token-p x)))

  (defrule vl-token-p-when-vl-extinttoken-p
    (implies (vl-extinttoken-p x)
             (vl-token-p x))))

(define vl-tokentype-p (x)
  (or (consp (member-eq x '(:vl-idtoken
                            :vl-inttoken
                            :vl-sysidtoken
                            :vl-stringtoken
                            :vl-realtoken
                            :vl-timetoken
                            :vl-extinttoken)))
      (vl-plaintokentype-p x))
  ///
  (deflist vl-tokentypelist-p (x)
    :elementp-of-nil nil
    :true-listp t
    (vl-tokentype-p x)))


(define vl-token->type
  :short "Get the type of a token."

  ((x vl-token-p))
  :returns (type symbolp :hyp :fguard)

  :long "<p>For plain tokens, the symbol we return is the @('type') field of
the @(see vl-plaintoken-p).  You can see a list of the valid types by
inspecting the value of @(see *vl-plaintoken-types*), and examples include
@(':vl-ws') for whitespace tokens, @(':vl-kwd-always') for the keyword
@('always'), and @(':vl-comma') for commas.</p>

<p>For any other token, such as @(see vl-inttoken-p) or @(see vl-idtoken-p)
objects, the type is simply the @('tag') from the @(see defaggregate).  That
is, an integer token has type @(':vl-inttoken'), an identifier has type
@(':vl-idtoken'), and so on.</p>

<p>This is one of the most heavily used functions throughout our parser, so its
efficient implementation is beneficial.  We specially arrange our definition of
@(see vl-plaintoken-p) so that the type of any token is always just its
@('car').</p>"

  :inline t
  :prepwork ((local (in-theory (enable vl-token-p))))
  :guard-hints(("Goal" :in-theory (enable tag-when-vl-plaintoken-p)))
  (mbe :logic
       (if (vl-plaintoken-p x)
           (vl-plaintoken->type x)
         (tag x))
       :exec
       (tag x))
  ///
  (local (defthm l0
           (implies (syntaxp (quotep alist))
                    (iff (hons-assoc-equal a alist)
                         (member a (alist-keys alist))))))

  (defrule vl-token->type-possibilities
    (implies (vl-token-p x)
             (member (vl-token->type x)
                     (append (list :vl-inttoken
                                   :vl-stringtoken
                                   :vl-idtoken
                                   :vl-sysidtoken
                                   :vl-realtoken
                                   :vl-timetoken
                                   :vl-extinttoken)
                             *vl-plaintoken-types*)))
    :rule-classes nil
    :enable (vl-token-p vl-plaintokentype-p)
    :disable (return-type-of-vl-plaintoken->type
              member acl2::member-of-cons
              hons-assoc-equal
              acl2::hons-assoc-equal-of-cons)
    :use ((:instance return-type-of-vl-plaintoken->type)))

  (defret vl-tokentype-p-of-<fn>
    (implies (vl-token-p x)
             (vl-tokentype-p type))
    :hints(("Goal" :in-theory (enable vl-tokentype-p))))

  (defrule vl-inttoken-p-when-token-of-type-inttoken
    (implies (and (equal (vl-token->type x) :vl-inttoken)
                  (force (vl-token-p x)))
             (equal (vl-inttoken-p x)
                    t))
    :enable (vl-token-p vl-plaintoken->type vl-plaintoken-p))

  (defrule vl-stringtoken-p-when-token-of-type-stringtoken
    (implies (and (equal (vl-token->type x) :vl-stringtoken)
                  (force (vl-token-p x)))
             (equal (vl-stringtoken-p x)
                    t))
    :enable (vl-token-p vl-plaintoken->type vl-plaintoken-p))

  (defrule vl-realtoken-p-when-token-of-type-realtoken
    (implies (and (equal (vl-token->type x) :vl-realtoken)
                  (force (vl-token-p x)))
             (equal (vl-realtoken-p x)
                    t))
    :enable (vl-token-p vl-plaintoken->type vl-plaintoken-p))

  (defrule vl-timetoken-p-when-token-of-type-timetoken
    (implies (and (equal (vl-token->type x) :vl-timetoken)
                  (force (vl-token-p x)))
             (equal (vl-timetoken-p x)
                    t))
    :enable (vl-token-p vl-plaintoken->type vl-plaintoken-p))

  (defrule vl-extinttoken-p-when-token-of-type-extinttoken
    (implies (and (equal (vl-token->type x) :vl-extinttoken)
                  (force (vl-token-p x)))
             (equal (vl-extinttoken-p x)
                    t))
    :enable (vl-token-p vl-plaintoken->type vl-plaintoken-p))

  (defrule vl-idtoken-p-when-token-of-type-idtoken
    (implies (and (equal (vl-token->type x) :vl-idtoken)
                  (force (vl-token-p x)))
             (equal (vl-idtoken-p x)
                    t))
    :enable (vl-token-p vl-plaintoken->type vl-plaintoken-p))

  (defrule vl-sysidtoken-p-when-token-of-type-sysidtoken
    (implies (and (equal (vl-token->type x) :vl-sysidtoken)
                  (force (vl-token-p x)))
             (equal (vl-sysidtoken-p x)
                    t))
    :enable (vl-token-p
             vl-token->type
             vl-plaintoken->type
             vl-plaintoken-p)))


(define vl-token->etext
  :short "Get the original text for a token."

  ((x vl-token-p))
  :returns (etext vl-echarlist-p :hyp :fguard)

  :long "<p>Each of the valid @(see vl-token-p) objects includes an @('etext')
field which reflects the original characters in the source code that led to the
creation of that token.  Accordingly, we can extract the @('etext') from any
token.</p>"

  :inline t
  :verify-guards nil
  (mbe :logic
       (cond ((vl-inttoken-p x)     (vl-inttoken->etext x))
             ((vl-idtoken-p x)      (vl-idtoken->etext x))
             ((vl-sysidtoken-p x)   (vl-sysidtoken->etext x))
             ((vl-stringtoken-p x)  (vl-stringtoken->etext x))
             ((vl-realtoken-p x)    (vl-realtoken->etext x))
             ((vl-timetoken-p x)    (vl-timetoken->etext x))
             ((vl-extinttoken-p x)  (vl-extinttoken->etext x))
             ((vl-plaintoken-p x)   (vl-plaintoken->etext x)))

       :exec
       ;; BOZO I wish I could do better than this.  But the number of fields in
       ;; each structure impacts the layout, so it's hard to get things to line
       ;; up better than this.  To improve this, we would probably have to
       ;; rework defaggregate to make the field layout more flexible.
       (case (tag x)
         ((:vl-inttoken :vl-timetoken)
          (caadr x))
         (otherwise
          (cadr x))))
  ///
  (encapsulate
    ()
    (local (defruled crock
             (and (equal (vl-idtoken->etext x) (cadr x))
                  (equal (vl-sysidtoken->etext x) (cadr x))
                  (equal (vl-inttoken->etext x) (caadr x))
                  (equal (vl-stringtoken->etext x) (cadr x))
                  (equal (vl-realtoken->etext x) (cadr x))
                  (equal (vl-timetoken->etext x) (caadr x))
                  (equal (vl-extinttoken->etext x) (cadr x))
                  (equal (vl-plaintoken->etext x) (cadr x))
                  )
             :enable (vl-idtoken->etext
                      vl-sysidtoken->etext
                      vl-inttoken->etext
                      vl-stringtoken->etext
                      vl-realtoken->etext
                      vl-timetoken->etext
                      vl-extinttoken->etext
                      vl-plaintoken->etext)))

    (verify-guards vl-token->etext$inline
      :hints(("Goal" :in-theory (enable vl-token-p))
             (and stable-under-simplificationp
                  '(:in-theory (enable crock
                                       vl-inttoken-p
                                       vl-idtoken-p
                                       vl-stringtoken-p
                                       vl-realtoken-p
                                       vl-timetoken-p
                                       vl-extinttoken-p
                                       vl-sysidtoken-p
                                       vl-plaintoken-p
                                       tag))))))

  (defrule consp-of-vl-token->etext
    (implies (force (vl-token-p x))
             (consp (vl-token->etext x)))
    :enable vl-token-p)

  (defrule true-listp-of-vl-token->etext
    (implies (force (vl-token-p x))
             (true-listp (vl-token->etext x))))

  (local (defrule crock
           (let ((token (make-vl-plaintoken :type type :etext etext :breakp breakp)))
             (implies (vl-plaintokentype-p type)
                      (and (not (vl-idtoken-p token))
                           (not (vl-sysidtoken-p token))
                           (not (vl-realtoken-p token))
                           (not (vl-timetoken-p token))
                           (not (vl-extinttoken-p token))
                           (not (vl-stringtoken-p token))
                           (not (vl-inttoken-p token)))))
           :enable (tag
                    vl-plaintoken
                    vl-idtoken-p
                    vl-sysidtoken-p
                    vl-realtoken-p
                    vl-timetoken-p
                    vl-extinttoken-p
                    vl-stringtoken-p
                    vl-inttoken-p)))

  (defrule vl-token->etext-of-vl-plaintoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext))
                  (force (booleanp breakp))
                  (force (vl-plaintokentype-p type)))
             (equal (vl-token->etext (make-vl-plaintoken :type type
                                                         :etext etext
                                                         :breakp breakp))
                    etext)))

  (defrule vl-token->etext-of-vl-stringtoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext))
                  (force (booleanp breakp))
                  (force (stringp expansion)))
             (equal (vl-token->etext (make-vl-stringtoken :etext etext
                                                          :expansion expansion
                                                          :breakp breakp))
                    etext)))

  (defrule vl-token->etext-of-vl-idtoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext))
                  (force (booleanp breakp))
                  (force (stringp name)))
             (equal (vl-token->etext (make-vl-idtoken :etext etext
                                                      :name name
                                                      :breakp breakp))
                    etext)))

  (defrule vl-token->etext-of-vl-sysidtoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext))
                  (force (booleanp breakp))
                  (force (stringp name)))
             (equal (vl-token->etext (make-vl-sysidtoken :etext etext
                                                         :name name
                                                         :breakp breakp))
                    etext)))

  (defrule vl-token->etext-of-vl-inttoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext))
                  (force (booleanp breakp))
                  (force (posp width))
                  (force (booleanp signedp))
                  (force (maybe-natp value))
                  (force (vl-inttoken-constraint-p width value bits))
                  (force (vl-bitlist-p bits))
                  (force (booleanp wasunsized)))
             (equal (vl-token->etext (make-vl-inttoken :etext etext
                                                       :width width
                                                       :signedp signedp
                                                       :value value
                                                       :bits bits
                                                       :wasunsized wasunsized
                                                       :breakp breakp))
                    etext)))

  (defrule vl-token->etext-of-vl-realtoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext))
                  (force (booleanp breakp)))
             (equal (vl-token->etext (make-vl-realtoken :etext etext
                                                        :breakp breakp))
                    etext)))

  (defrule vl-token->etext-of-vl-timetoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext))
                  (force (stringp quantity))
                  (force (vl-timeunit-p units))
                  (force (booleanp breakp)))
             (equal (vl-token->etext (make-vl-timetoken :etext etext
                                                        :quantity quantity
                                                        :units units
                                                        :breakp breakp))
                    etext)))

  (defrule vl-token->etext-of-vl-extinttoken
    (implies (and (force (vl-echarlist-p etext))
                  (force (consp etext))
                  (force (true-listp etext))
                  (force (vl-bit-p value))
                  (force (booleanp breakp)))
             (equal (vl-token->etext (make-vl-extinttoken :etext etext
                                                          :value value
                                                          :breakp breakp))
                    etext))))


(define vl-token->loc
  :short "Get the starting location for a token."

  ((x vl-token-p))
  :returns (loc vl-location-p :hyp :fguard)

  :long "<p>Because @('etext') is always required to be a non-empty, we can say
that each token has a location, namely the location of its first
character.</p>"

  :inline t
  (vl-echar->loc (car (vl-token->etext x))))



(define vl-token->breakp
  :short "Identify whether a token was the first token on a line."
  ((x vl-token-p))
  :returns (breakp booleanp :rule-classes :type-prescription)
  :inline t
  :verify-guards nil
  (mbe :logic
       (if (cond ((vl-inttoken-p x)     (vl-inttoken->breakp x))
                 ((vl-idtoken-p x)      (vl-idtoken->breakp x))
                 ((vl-sysidtoken-p x)   (vl-sysidtoken->breakp x))
                 ((vl-stringtoken-p x)  (vl-stringtoken->breakp x))
                 ((vl-realtoken-p x)    (vl-realtoken->breakp x))
                 ((vl-timetoken-p x)    (vl-timetoken->breakp x))
                 ((vl-extinttoken-p x)  (vl-extinttoken->breakp x))
                 ((vl-plaintoken-p x)   (vl-plaintoken->breakp x)))
           t
         nil)
       :exec
       ;; BOZO I wish I could do better than this.  But the number of fields in
       ;; each structure impacts the layout, so it's hard to get things to line
       ;; up better than this.  To improve this, we would probably have to
       ;; rework defaggregate to make the field layout more flexible.
       (case (tag x)
         (:vl-inttoken
          (cddddr x))
         ((:vl-idtoken :vl-sysidtoken :vl-stringtoken :vl-timetoken)
          (cdddr x))
         (:vl-extinttoken
          (caddr x))
         (otherwise ;; plain, real
          (cddr x))))
  ///
  (encapsulate
    ()
    (local (defruled crock
             (and (equal (vl-inttoken->breakp x) (cddddr x))
                  (equal (vl-idtoken->breakp x) (cdddr x))
                  (equal (vl-sysidtoken->breakp x) (cdddr x))
                  (equal (vl-stringtoken->breakp x) (cdddr x))
                  (equal (vl-timetoken->breakp x) (cdddr x))
                  (equal (vl-extinttoken->breakp x) (caddr x))
                  (equal (vl-realtoken->breakp x) (cddr x))
                  (equal (vl-plaintoken->breakp x) (cddr x)))
             :enable (vl-idtoken->breakp
                      vl-sysidtoken->breakp
                      vl-inttoken->breakp
                      vl-stringtoken->breakp
                      vl-realtoken->breakp
                      vl-timetoken->breakp
                      vl-extinttoken->breakp
                      vl-plaintoken->breakp)))

    (verify-guards vl-token->breakp$inline
      :hints(("Goal" :in-theory (enable vl-token-p))
             (and stable-under-simplificationp
                  '(:in-theory (enable crock
                                       vl-inttoken-p
                                       vl-idtoken-p
                                       vl-stringtoken-p
                                       vl-realtoken-p
                                       vl-timetoken-p
                                       vl-extinttoken-p
                                       vl-sysidtoken-p
                                       vl-plaintoken-p
                                       tag)))))))

(deflist vl-tokenlist-p (x)
  :elementp-of-nil nil
  (vl-token-p x))

(deflist vl-tokenlistlist-p (x)
  :elementp-of-nil t
  (vl-tokenlist-p x))

(defmapappend vl-tokenlist->etext (x)
  (vl-token->etext x)
  :short "Append together all the text for a list of tokens."
  :transform-true-list-p t
  :guard (vl-tokenlist-p x)
  :rest
  ((defrule vl-echarlist-p-of-vl-tokenlist->etext
     (implies (force (vl-tokenlist-p x))
              (vl-echarlist-p (vl-tokenlist->etext x))))))

(define vl-token->string
  :parents (tokens)
  :short "Get the original text that gave rise to any token, as a string."
  ((x vl-token-p))
  :returns (str stringp :rule-classes :type-prescription)
  (vl-echarlist->string (vl-token->etext x)))


(define vl-tokenlist->string-with-spaces-aux
  :parents (vl-tokenlist->string-with-spaces)
  ((x   vl-tokenlist-p)
   (acc "Accumulator for characters in reverse order."))
  (b* (((when (atom x))
        acc)
       (echars1 (vl-token->etext (car x)))
       (acc     (vl-echarlist->chars-exec echars1 acc))
       ((when (atom (cdr x)))
        ;; No more tokens, don't add a space.
        acc)
       (acc     (cons #\Space acc)))
    (vl-tokenlist->string-with-spaces-aux (cdr x) acc)))

(define vl-tokenlist->string-with-spaces
  :short "Join together a token list into a single string, putting a single
  space between each token."
  ((x vl-tokenlist-p))
  :returns (str stringp :rule-classes :type-prescription)
  :long "<p>This is occasionally useful for error reporting in the parser,
where typically the tokens have already had the comments/whitespace stripped
out of them.  So, to display them in any sort of sensible way, we need to at
least insert spaces between them.</p>"

  :verify-guards nil
  (mbe :logic (cond ((atom x)
                     "")
                    ((atom (cdr x))
                     (vl-token->string (car x)))
                    (t
                     (cat (vl-token->string (car x))
                          " "
                          (vl-tokenlist->string-with-spaces (cdr x)))))
       :exec
       (str::rchars-to-string
        (vl-tokenlist->string-with-spaces-aux x nil)))
  ///
  (local (defrule vl-tokenlist->string-with-spaces-aux-removal
           (implies (vl-tokenlist-p x)
                    (equal (vl-tokenlist->string-with-spaces-aux x acc)
                           (revappend (explode (vl-tokenlist->string-with-spaces x))
                                      acc)))
           :induct (vl-tokenlist->string-with-spaces-aux x acc)
           :enable (vl-tokenlist->string-with-spaces
                    vl-tokenlist->string-with-spaces-aux
                    vl-token->string
                    string-append)))

  (verify-guards vl-tokenlist->string-with-spaces))

