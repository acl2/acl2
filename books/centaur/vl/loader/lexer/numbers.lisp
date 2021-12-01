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
(include-book "../../util/warnings")
(local (include-book "../../util/arithmetic"))

(defxdoc lex-numbers
  :parents (lexer)
  :short "Handling of integer numbers, real numbers, and time literals."

  :long "<p>Verilog has a very rich (and correspondingly complicated) syntax
for numbers.  Fortunately, this part of the language tends to be well defined
and there are few differences here between Verilog-2005 and
SystemVerilog-2012.</p>")

(local (xdoc::set-default-parents lex-numbers))



(define vl-read-unsigned-number
  :short "@('unsigned_number ::= decimal_digit { _ | decimal_digit }')."
  :long "<p>Embedded spaces are not allowed.</p>"
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)
  :inline t
  (if (or (atom echars)
          (not (vl-decimal-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-decimal-digit echars))
  ///
  (def-prefix/remainder-thms vl-read-unsigned-number))

(define vl-read-non-zero-unsigned-number
  :short "@('non_zero_unsigned_number ::= non_zero_decimal_digit { _ | decimal_digit }')."
  :long "<p>Embedded spaces are not allowed.</p>"
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)
  :inline t
  (if (or (atom echars)
          (not (vl-non-zero-decimal-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-decimal-digit echars))
  ///
  (def-prefix/remainder-thms vl-read-non-zero-unsigned-number))



(define vl-timeunit-lookup
  :short "Get the @(see vl-timeunit-p) corresponding to a time unit string like
@('\"us\"')."
  ((x stringp))
  :returns (unit (equal (vl-timeunit-p unit)
                        (if unit t nil)))
  :inline t
  (cdr (assoc-equal x '(("s"  . :vl-s)
                        ("ms" . :vl-ms)
                        ("us" . :vl-us)
                        ("ns" . :vl-ns)
                        ("ps" . :vl-ps)
                        ("fs" . :vl-fs)))))

(define vl-read-time-unit
  :short "@('time_unit ::= s | ms | us | ns | ps | fs')."
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)
  :inline t
  (vl-read-some-literal '("s" "ms" "us" "ns" "ps" "fs") echars)
  ///
  (def-prefix/remainder-thms vl-read-time-unit)
  (defrule vl-timeunit-lookup-of-vl-read-time-unit
    (b* (((mv prefix ?remainder) (vl-read-time-unit echars)))
      (implies prefix
               (vl-timeunit-lookup
                (implode (vl-echarlist->chars prefix)))))
    :enable vl-timeunit-lookup
    :expand ((:free (x) (vl-read-some-literal x echars)))))

(define vl-read-real-tail
  :short "Match @('exp [sign] unsigned_number')"
  ((echars vl-echarlist-p))
  :returns (mv prefix? remainder)
  :inline t
  (b* (((mv e rem)    (vl-read-some-literal '("e" "E") echars))
       ((unless e)    (mv nil echars))
       ((mv sign rem) (vl-read-some-literal '("+" "-") rem))
       ((mv expt rem) (vl-read-unsigned-number rem))
       ((unless expt) (mv nil echars)))
    (mv (append e sign expt) rem))
  ///
  (def-prefix/remainder-thms vl-read-real-tail))

(define vl-lex-time-or-real-number
  :short "Match @('real_number') or @('time_literal')."

  ((echars vl-echarlist-p "Characters we're lexing.")
   (breakp booleanp)
   (st     vl-lexstate-p  "Governs whether @('time_literal')s are valid."))
  :returns (mv token? remainder)

  :long "<p>Verilog-2005 has no @('time_literal')s and the syntax for real
numbers is just:</p>

@({
    sign ::= + | -
    exp ::= e | E
    real_number ::=                        // no embedded spaces
       unsigned_number . unsigned_number
     | unsigned_number [ . unsigned_number ] exp [ sign ] unsigned_number
})

<p>SystemVerilog-2012 slightly tweaks @('real_number'), but it is exactly
equivalent to the above:</p>

@({
     real_number ::=                       // no embedded spaces
        fixed_point_number
      | unsigned_number [ . unsigned_number ] exp [ sign ] unsigned_number

     fixed_point_number ::= unsigned_number . unsigned_number
})

<p>However, this new @('fixed_point_number') is also used in
@('time_literal')s:</p>

@({
     time_literal ::=                      // no embedded spaces
          unsigned_number time_unit
        | fixed_point_number time_unit

     time_unit ::= s | ms | us | ns | ps | fs
})

<p>And lexing these is slightly subtle because we now need to check for these
extra possibilities, e.g., @('37.45us') is a time literal whereas @('37.45')
followed by something else is a real number.</p>"

  (b* (;; Match initial unsigned_number part
       (breakp (and breakp t))
       ((mv ipart ipart-rest) (vl-read-unsigned-number echars))
       ((unless ipart)        (mv nil echars))

       ;; Check for 123e+45 -- if so, can only be a real number
       ((mv tail tail-rest)   (vl-read-real-tail ipart-rest))
       ((when tail)
        (mv (make-vl-realtoken :etext (append ipart tail) :breakp breakp)
            tail-rest))

       ((vl-lexstate st) st)

       ;; Check for 123us -- if so, can only be a time literal
       ((mv units units-rest) (if st.timelitsp
                                  (vl-read-time-unit ipart-rest)
                                (mv nil ipart-rest)))
       ((when units)
        (mv (make-vl-timetoken
             :etext    (append ipart units)
             :quantity (vl-echarlist->string ipart)
             :units    (vl-timeunit-lookup (vl-echarlist->string units))
             :breakp   breakp)
            units-rest))

       ;; Not simply an integer with an expt/time tail, so now try
       ;; to match a fixed_point_number.
       ((mv dot dot-rest)     (vl-read-literal "." ipart-rest))
       ((unless dot)          (mv nil echars))
       ((mv fpart fpart-rest) (vl-read-unsigned-number dot-rest))
       ((unless fpart)        (mv nil echars))

       ;; Check for 123.45e+67 -- if so, can only be a real number
       ((mv tail tail-rest) (vl-read-real-tail fpart-rest))
       ((when tail)
        (mv (make-vl-realtoken :etext (append ipart dot fpart tail)
                               :breakp breakp)
            tail-rest))

       ;; Check for 123.45us -- if so, can only be a time literal
       ((mv units units-rest) (if st.timelitsp
                                  (vl-read-time-unit fpart-rest)
                                (mv nil fpart-rest)))
       ((when units)
        (mv (make-vl-timetoken
             :etext    (append ipart dot fpart units)
             :quantity (vl-echarlist->string (append ipart dot fpart))
             :units    (vl-timeunit-lookup (vl-echarlist->string units))
             :breakp   breakp)
            units-rest)))

    ;; Else we found 123.45 with no expt/time tail -- it's a valid real number
    (mv (make-vl-realtoken :etext (append ipart dot fpart)
                           :breakp breakp)
        fpart-rest))
  ///
  (def-token/remainder-thms vl-lex-time-or-real-number
    :formals (echars breakp st)))





(define vl-read-hex-base
  :short "@('hex_base ::= '[s|S]h | '[s|S]H')."
  :long "<p>Embedded spaces are not allowed.</p>"
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)
  :inline t
  (vl-read-some-literal '("'h" "'H" "'sh" "'sH" "'Sh" "'SH") echars)
  ///
  (def-prefix/remainder-thms vl-read-hex-base))

(define vl-read-octal-base
  :short "@('octal_base   ::= '[s|S]o | '[s|S]O')."
  :long "<p>Embedded spaces are not allowed.</p>"
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)
  :inline t
  (vl-read-some-literal '("'o" "'O" "'so" "'sO" "'So" "'SO") echars)
  ///
  (def-prefix/remainder-thms vl-read-octal-base))

(define vl-read-binary-base
  :short "@('binary_base  ::= '[s|S]b | '[s|S]B')."
  :long "<p>Embedded spaces are not allowed.</p>"
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)
  :inline t
  (vl-read-some-literal '("'b" "'B" "'sb" "'sB" "'Sb" "'SB") echars)
  ///
  (def-prefix/remainder-thms vl-read-binary-base))

(define vl-read-decimal-base
  :short "@('decimal_base ::= '[s|S]d | '[s|S]D')."
  :long "<p>Embedded spaces are not allowed.</p>"
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)
  :inline t
  (vl-read-some-literal '("'d" "'D" "'sd" "'sD" "'Sd" "'SD") echars)
  ///
  (def-prefix/remainder-thms vl-read-decimal-base))

(define vl-read-any-base
  :short "Matches @('binary_base | octal_base | decimal_base | hex_base')"
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)
  (b* (((mv prefix remainder) (vl-read-hex-base echars))
       ((when prefix) (mv prefix remainder))
       ((mv prefix remainder) (vl-read-octal-base echars))
       ((when prefix) (mv prefix remainder))
       ((mv prefix remainder) (vl-read-binary-base echars))
       ((when prefix) (mv prefix remainder)))
    (vl-read-decimal-base echars))
  ///
  (def-prefix/remainder-thms vl-read-any-base))

(define vl-signed-basep
  :parents (vl-read-any-base)
  :short "Determine signedness for a @('base') from @(see vl-read-any-base)."
  ((base character-listp))
  :returns (signedp booleanp :rule-classes :type-prescription)
  :inline t
  (consp (or (member #\s base)
             (member #\S base))))

(define vl-base-to-radix
  :parents (vl-read-any-base)
  :short "Determine the radix for a @('base') from @(see vl-read-any-base)."
  ((base character-listp))
  :returns (radix natp :rule-classes :type-prescription)
  (cond ((or (member #\h base) (member #\H base)) 16)
        ((or (member #\d base) (member #\D base)) 10)
        ((or (member #\o base) (member #\O base)) 8)
        ((or (member #\b base) (member #\B base)) 2)
        (t
         (progn$ (raise "programming error")
                 2)))
  ///
  (defthm vl-base-to-radix-upper
    (<= (vl-base-to-radix base) 16)
    :rule-classes :linear)
  (defthm vl-base-to-radix-lower
    (<= 2 (vl-base-to-radix base))
    :rule-classes :linear))



(define vl-read-hex-value
  :short "@('hex_value ::= hex_digit { _ | hex_digit }')."
  :long "<p>Embedded spaces are not allowed.</p>"
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)
  :inline t
  (if (or (atom echars)
          (not (vl-hex-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-hex-digit echars))
  ///
  (def-prefix/remainder-thms vl-read-hex-value))

(define vl-read-octal-value
  :short "@('octal_value ::= octal_digit { _ | octal_digit }')."
  :long "<p>Embedded spaces are not allowed.</p>"
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)
  :inline t
  (if (or (atom echars)
          (not (vl-octal-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-octal-digit echars))
  ///
  (def-prefix/remainder-thms vl-read-octal-value))

(define vl-read-binary-value
  :short "@('binary_value ::= binary_digit { _ | binary_digit }')."
  :long "<p>Embedded spaces are not allowed.</p>"
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)
  :inline t
  (if (or (atom echars)
          (not (vl-binary-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-binary-digit echars))
  ///
  (def-prefix/remainder-thms vl-read-binary-value))

(define vl-read-decimal-value
  :short "Matches @('unsigned_number | x_digit { _ } | z_digit { _ }')."
  ((echars vl-echarlist-p))
  :returns (mv prefix remainder)
  :long "<p>This doesn't correspond to a named production in the Verilog
grammars, but captures everything that's legal after the @('decimal_base') part
of a @('decimal_number').  That is, we're basically refactoring
@('decimal_number') as follows:</p>

@({
   decimal-number ::= unsigned_number
                    | [size] decimal_base decimal_value

   decimal_value ::= unsigned_number
                   | x_digit { _ }
                   | z_digit { _ }
})

<p>Neither Verilog-2005 and SystemVerilog-2012 explicitly rules out spaces in
the @('x_digit') and @('z_digit') cases here, so arguably the spec allows for
syntax like @('10 'd x__ __ __').  However, this seems crazy and none of
Verilog-XL, NCVerilog, or VCS accepts such syntax, so we think this is just a
minor oversight in the standards.</p>"

  (b* (((when (atom echars))
        (mv nil echars))
       ((unless (or (vl-x-digit-echar-p (car echars))
                    (vl-z-digit-echar-p (car echars))))
        (vl-read-unsigned-number echars))
       ((mv prefix remainder) (vl-read-while-underscore (cdr echars))))
    (mv (cons (car echars) prefix) remainder))
  ///
  (def-prefix/remainder-thms vl-read-decimal-value))



(define vl-binary-digits-to-bitlist
  :short "Convert MSB-first binary digits into an initial (not truncated,
not extended) MSB-first @(see vl-bitlist-p)."
  ((digits character-listp "A list of @('binary_digit') characters."))
  :returns (bits vl-bitlist-p)
  (if (atom digits)
      nil
    (cons (case (car digits)
            (#\0           :vl-0val)
            (#\1           :vl-1val)
            ((#\x #\X)     :vl-xval)
            ((#\z #\Z #\?) :vl-zval)
            (otherwise
             (progn$ (raise "Not a binary digit: ~x0.~%" (car digits))
                     :vl-0val)))
          (vl-binary-digits-to-bitlist (cdr digits))))
  ///
  (defthm len-of-vl-binary-digits-to-bitlist
    (equal (len (vl-binary-digits-to-bitlist x))
           (len x))))

(define vl-octal-digits-to-bitlist
  :short "Convert MSB-first octal digits into an initial (not truncated,
not extended) MSB-first @(see vl-bitlist-p)."
  ((digits character-listp "A list of @('octal_digit') characters."))
  :returns (bits vl-bitlist-p)
  (if (atom digits)
      nil
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
            (vl-octal-digits-to-bitlist (cdr digits))))
  ///
  (defthm len-of-vl-octal-digits-to-bitlist
    (equal (len (vl-octal-digits-to-bitlist x))
           (* 3 (len x)))))

(define vl-hex-digits-to-bitlist
  :short "Converts MSB-first digits into an initial (not truncated, not
extended) MSB-first @(see vl-bitlist-p)."
  ((digits character-listp))
  :returns (bits vl-bitlist-p)
  (if (atom digits)
      nil
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
            (vl-hex-digits-to-bitlist (cdr digits))))
  ///
  (defthm len-of-vl-hex-digits-to-bitlist
    (equal (len (vl-hex-digits-to-bitlist x))
           (* 4 (len x)))))

(define vl-decimal-digits-to-bitlist
  :short "Convert an @('decimal_value') with @('x')/@('z') digits into an
initial (not truncated, not extended) @(see vl-bitlist-p)."
  ((digits character-listp))
  :returns (bits vl-bitlist-p)
  :long "<p>See @(see vl-read-decimal-value).  The only time this should be
called is if digits is a singleton list containing exactly the digit x or
z.</p>"
  (cond ((member-equal digits (list '(#\x) '(#\X)))
         (list :vl-xval))
        ((member-equal digits (list '(#\z) '(#\Z) '(#\?)))
         (list :vl-zval))
        (t
         (progn$
          (raise "Programming error")
          (list :vl-xval))))
  ///
  (defthm len-of-vl-decimal-digits-to-bitlist
    (equal (len (vl-decimal-digits-to-bitlist x))
           1)))

;; get some extra rules about vl-bitlist-p.  BOZO we should have a way of doing
;; this without providing the whole form
(local (fty::deflist vl-bitlist
         :elt-type vl-bit-p
         :elementp-of-nil nil
         :true-listp nil
         :parents (vl-weirdint-p)))

(define vl-correct-bitlist
  :short "Extend (or truncate) a bit-list to match the size specifier for an
integer token."

  ((loc  vl-location-p
         "Context for any new warnings.")
   (bits vl-bitlist-p
         "The actual bits for this number.  This list of bits may be shorter or
          longer than @('width'), which is the size specified for this integer
          or is @('nil') if no size was specified.")
   (width maybe-posp
          "The desired width specified for this number.  For instance, this
           would be @('3') for @('3'bx').  Note that we emulate a 32-bit
           Verilog implementation and treat unsized numbers as having width
           32.")
   (etext vl-echarlist-p
          "Actual text for this number, for better warnings.")
   (warnings "An ordinary @(see warnings) accumulator."
             vl-warninglist-p))

  :returns (mv (warnings vl-warninglist-p)
               (new-bits vl-bitlist-p :hyp (force (vl-bitlist-p bits))))

  :long "<p>Our goal is to produce a new list of bits that has exactly the
desired width, by truncating or extending @('bits') as necessary.</p>

<p>The rules for how to do this are given in Section 3.5.1 of the Verilog-2005
standard, or Section 5.7.1 of the SystemVerilog-2012 standard.  Both standards
agree about the details.  Essentially:</p>

<ul>

<li>If the actual list of bits is longer than width, we are to truncate it from
the left, keeping the least significant width-many bits.  We produce a
truncation warning in this case.</li>

<li>If the actual list of bits is shorter than width, we are usually supposed
to zero-extend it.  However, when the most significant bit is X or Z, we are
instead supposed to X-extend or Z-extend, respectively.</li>

</ul>

<p>The specification notes that in the 1995 Verilog standard, an unsized
constant whose leading bit is X or Z is only X/Z extended to 32 bits.  We
therefore detect and warn about this very unusual case.</p>"

  (b* ((actual-len  (len bits))
       (desired-len (if width (lnfix width) 32))
       ((when (eql desired-len actual-len))
        ;; Nothing to do
        (mv (ok) bits))

       ((when (eql actual-len 0))
        ;; BOZO could probably prove this never happens
        (raise "Programming error: expected at least one bit.")
        (mv (ok) (replicate desired-len :vl-0val)))

       ((when (< actual-len desired-len))
        ;; We need to extend.
        (b* ((pad-bit (case (car bits)
                        (:vl-zval :vl-zval)
                        (:vl-xval :vl-xval)
                        (otherwise :vl-0val)))
             (warnings
              (if (and (not width)
                       (or (eq pad-bit :vl-xval)
                           (eq pad-bit :vl-zval)))
                  (warn :type :vl-warn-incompatible
                        :msg "~l0: unsized numbers with leading X or Z bit ~
                              have a different interpretation in Verilog-1995 ~
                              than in Verilog-2001 and beyond.  You should ~
                              put an explicit size on this number: ~s1."
                        :args (list loc
                                    (vl-echarlist->string etext)))
                (ok)))
             (pad        (replicate (- desired-len actual-len) pad-bit))
             (bits-prime (append pad bits)))
          (mv (ok) bits-prime)))

       ;; We need to truncate.
       (bits-prime (rest-n (- actual-len desired-len) bits))
       (warnings
        (if (all-equalp :vl-xval bits)
            ;; We suppress the truncation warning when all of the bits are X,
            ;; because we often run into 29'h XXXX_XXXX or similar, and while
            ;; perhaps {29{1'bX}} would be a better way to write it, the
            ;; XXXX_XXXX form seems pretty legitimate, too.
            (ok)
          (warn :type :vl-warn-overflow
                :msg  (cat "~l0: implicitly truncating ~s1 from ~x2 to ~x3 bits."
                           (if (not width)
                               " Note that we are emulating a 32-bit Verilog ~
                                implementation, but a 64-bit simulator would ~
                                get a different value here.  You should add ~
                                an explicit size specifier."
                             ""))
                :args (list loc
                            (vl-echarlist->string etext)
                            actual-len
                            desired-len)))))
    (mv (ok) bits-prime))
  ///
  (defthm len-of-vl-correct-bitlist
    (equal (len (mv-nth 1 (vl-correct-bitlist loc bits width etext warnings)))
           (if width
               (nfix width)
             32)))

  (local
   (progn

     ;; Basic extension test with a fixed width
     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "0111"))
                                        8
                                        nil
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits) "00000111"))))

     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "1111"))
                                        8
                                        nil
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits) "00001111"))))

     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "x111"))
                                        8
                                        nil
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits) "XXXXX111"))))

     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "z111"))
                                        8
                                        nil
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits) "ZZZZZ111"))))


     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "110111"))
                                        4
                                        nil
                                        nil)))
                (and (consp warn)
                     (equal (vl-bitlist->string bits) "0111"))))

     (assert! (b* (((mv warn ?bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "0111"))
                                        nil
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
                                        nil
                                        nil)))
                (and (consp warn)
                     (equal (vl-bitlist->string bits)
                            (implode (append (replicate 29 #\Z)
                                             (replicate 3 #\1))))))))))


(define vl-lex-integer
  :short "Match any @('integral_number')."
  ((echars   vl-echarlist-p)
   (breakp   booleanp)
   (warnings vl-warninglist-p))
  :returns (mv token?
               remainder
               (warnings vl-warninglist-p))
  :long "<p>We assume here that we have already checked @('echars') for
@('real_number') and @('time_literal') numbers and haven't found any.  So,
e.g., if we encounter a plain @('unsigned_number') here, we don't have to worry
that it might be part of a real number.</p>

<p>The @('integral_number') production is new in SystemVerilog-2012 and isn't
part of Verilog-2005.  However, except for @('real_number'), it's directly
compatible with Verilog-2005's @('number') production, so this is basically
completely compatible between both standards.  A slightly tweaked view of the
grammar is:</p>

@({
    integral_number ::= decimal_number
                      | octal_number
                      | binary_number
                      | hex_number

    hex_number     ::= [size] hex_base    hex_value
    octal_number   ::= [size] octal_base  octal_value
    binary_number  ::= [size] binary_base binary_value

    decimal_number ::= unsigned_number
                     | [size] decimal_base decimal_value

    size ::= non_zero_unsigned_number
})"

  :verify-guards nil
  (b* ((warnings (vl-warninglist-fix warnings))
       (breakp   (and breakp t))

       ;; We first try to read any numeric portion of echars into NUMBER.
       ;; When there is no number, REMAINDER1 == ECHARS and NUMBER == NIL.
       ((mv number remainder1) (vl-read-unsigned-number echars))

       ;; Interpret NUMBER if it exists.  When there is no number,
       ;; value-of-number is NIL.
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
        (mv (raise "Lexer error (~s0): thought this was impossible; cannot ~
                    interpret ~s1 as a number."
                   (vl-location-string (vl-echar->loc firstchar))
                   (vl-echarlist->string number))
            echars warnings))

       ((unless base)
        ;; We know there is a NUMBER because otherwise we failed above.  So,
        ;; there is a number and no base, which means this is a plain decimal
        ;; number with no X or Z digits.  This should become a signed, base-10
        ;; integer whose width is implementation dependent.  We treat it as a
        ;; 32-bit number.
        (b* ((val-fix (mod value-of-number (expt 2 32)))
             (warnings
              (cond ((< value-of-number (expt 2 31))
                     warnings)
                    ((< value-of-number (expt 2 32))
                     (warn :type :vl-warn-overflow
                           :msg "~l0: the plain number ~s1 is in [2^31, ~
                                 2^32); it will be considered a negative ~
                                 number by 32-bit Verilog implementations, ~
                                 but will be positive on 64-bit systems, so ~
                                 you should add an explicit size."
                           :args (list (vl-echar->loc firstchar)
                                       (vl-echarlist->string number))))
                    (t
                     (warn :type :vl-warn-overflow
                           :msg "~l0: the plain number ~s1 is over 2^32; we ~
                                 truncate it to ~x2 like a 32-bit Verilog ~
                                 implementation.  But this number will have a ~
                                 different value on 64-bit systems and ~
                                 beyond, so you should add an explicit size."
                            :args (list (vl-echar->loc firstchar)
                                        (vl-echarlist->string number)
                                        val-fix)))))
               (token (make-vl-inttoken :etext number
                                        :width 32
                                        :signedp t
                                        :value val-fix
                                        :bits nil
                                        :wasunsized t
                                        :breakp breakp)))
            (mv token remainder1 warnings)))

         ;; Otherwise there is a base.  This means that if there is a NUMBER,
         ;; it is the size specifier.

         ;; ((when (and number (equal value-of-number 0)))
         ;;  ;; It's illegal to have a width of zero.  After reading the
         ;;  ;; Verilog-2005 grammar, we believe it is never allowed for two
         ;;  ;; numbers to follow one another when separated only by whitespace.
         ;;  ;; So there is no way to parse this, and we are justified in causing
         ;;  ;; an error rather than returning number as its own inttoken.

         ;;  ;; BOZO is this still true for the SystemVerilog-2012 grammar?
         ;;  (mv (cw "Lexer error (~s0): found a number whose size is zero.~%"
         ;;          (vl-location-string (vl-echar->loc firstchar)))
         ;;      echars warnings))

         (width-was-0 (eql 0 value-of-number))
         (unsizedp (or (not number) width-was-0))
         (width (if unsizedp
                    32
                  value-of-number))

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
                                          :wasunsized unsizedp
                                          :breakp breakp))
               (warnings
                (if width-was-0
                    (warn :type :vl-0-width-number-literal
                          :msg "~l0: Number ~s1 has explicit width 0, which ~
                                is not allowed by the SystemVerilog standard. ~
                                Implementations usually interpret these as ~
                                unsized (that is, actually 32 bits wide)."
                          :args (list (vl-echar->loc firstchar)
                                      (vl-echarlist->string etext)))
                  warnings))
               (warnings
                ;; Truncation warnings.
                (cond ((not unsizedp)
                       (if (eql value val-fix)
                           warnings
                         (warn :type :vl-warn-overflow
                               :msg "~l0: the number ~s1 is not within the ~
                                     range [0, 2^~x2) indicated by its size, ~
                                     and is being truncated to ~x2 bits, ~
                                     yielding ~x2'd~x3 (hex: ~x2'h~s4)."
                               :args (list (vl-echar->loc firstchar)
                                           (vl-echarlist->string etext)
                                           width
                                           val-fix
                                           (str::nat-to-hex-string val-fix)))))
                      ((< value (expt 2 31))
                       warnings)
                      ((and signedp (< value (expt 2 32)))
                       (warn :type :vl-warn-overflow
                             :msg "~l0: the unsized, signed number ~s1 is in ~
                                   [2^31, 2^32).  It will be considered a ~
                                   negative number by 32-bit Verilog ~
                                   implementations, but positive by 64-bit ~
                                   tools.  You should add an explicit size."
                              :args (list (vl-echar->loc firstchar)
                                          (vl-echarlist->string number))))
                      ((< value (expt 2 32))
                       warnings)
                      (t
                       (warn :type :vl-warn-overflow
                             :msg "~l0: the unsized number ~s1 is over 2^32; ~
                                   we truncate it to 32'd~x2 (hex: 32'h~s3) ~
                                   to emulate a 32-bit Verilog ~
                                   implementation, but it will have a ~
                                   different value on 64-bit tools.  You ~
                                   should add an explicit size."
                              :args (list (vl-echar->loc firstchar)
                                          (vl-echarlist->string number)
                                          val-fix
                                          (str::nat-to-hex-string val-fix)))))))
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
                              (and (not width-was-0) value-of-number)
                              etext
                              warnings))
         (token (make-vl-inttoken :etext etext
                                  :width width
                                  :signedp signedp
                                  :value value
                                  :bits bits
                                  :wasunsized unsizedp
                                  :breakp breakp)))
      (mv token remainder2 warnings))

  ///

  (local (in-theory (enable vl-inttoken-constraint-p)))
  (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

  (verify-guards vl-lex-integer)

  (with-output
   :gag-mode :goals
   (def-token/remainder-thms vl-lex-integer
     :formals (echars breakp warnings))))




(define vl-lex-unbased-unsized-literal
  :short "@('unbased_unsized_literal ::= '0 | '1 | 'z_or_x')."
  :long "<p>Embedded spaces are not allowed.</p>"
  ((echars vl-echarlist-p)
   (breakp booleanp))
  :returns (mv token? remainder)
  (b* ((breakp (and breakp t))
       ((mv prefix val remainder)
        (b* (((mv prefix remainder) (vl-read-literal "'0" echars))
             ((when prefix)         (mv prefix :vl-0val remainder))
             ((mv prefix remainder) (vl-read-literal "'1" echars))
             ((when prefix)         (mv prefix :vl-1val remainder))
             ((mv prefix remainder) (vl-read-some-literal '("'x" "'X") echars))
             ((when prefix)         (mv prefix :vl-xval remainder))
             ;; Note that a "?" character isn't allowed as a Z here, which is a
             ;; bit unusual.
             ((mv prefix remainder) (vl-read-some-literal '("'z" "'Z") echars))
             ((when prefix)         (mv prefix :vl-zval remainder)))
          (mv nil nil echars)))
       ((when prefix)
        (mv (make-vl-extinttoken :etext prefix :value val :breakp breakp)
            remainder)))
    (mv nil echars))
  ///
  (def-token/remainder-thms vl-lex-unbased-unsized-literal
    :formals (echars breakp)))


(define vl-lex-number
  :short "Match @('number'), @('time_literal'), and @('unbased_unsized_literal')."
  ((echars   vl-echarlist-p)
   (breakp   booleanp)
   (st       vl-lexstate-p)
   (warnings vl-warninglist-p))
  :returns (mv token?
               remainder
               (warnings vl-warninglist-p))
  :inline t
  (b* ((warnings (vl-warninglist-fix warnings))

       ;; Try to match real/time tokens first, because otherwise we could get
       ;; fooled by things like 123.45 or 123us: we don't want to turn just
       ;; "123" into an integer and leave the ".45" or "us" sitting there in
       ;; the remainder.
       ((mv token remainder) (vl-lex-time-or-real-number echars breakp st))
       ((when token) (mv token remainder warnings))

       ;; Ordinary numbers
       ((mv token remainder warnings) (vl-lex-integer echars breakp warnings))
       ((when token) (mv token remainder warnings))

       ((unless (vl-lexstate->extintsp st))
        (mv nil echars warnings))
       ((mv token remainder) (vl-lex-unbased-unsized-literal echars breakp)))
    (mv token remainder warnings))
  ///
  (def-token/remainder-thms vl-lex-number
    :formals (echars breakp st warnings)))
