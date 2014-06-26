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
(include-book "find-module")
(include-book "stmt-tools")
(include-book "modnamespace") ;; bozo at least for portdecllist->names
(include-book "../loader/lexer/lexer") ; yucky, for simple-id-tail-p, etc.
(include-book "../util/print")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc verilog-printing
  :parents (printer)
  :short "Printing routines for displaying Verilog constructs."

  :long "<p>Using the VL @(see printer), we implement pretty-printing routines
to display our internal parse-tree representation (see @(see syntax)) as
Verilog code.  These functions produce either plain text or html output,
depending upon the @('htmlp') setting in the printer state, @(see ps).</p>")

(define vl-ps->show-atts-p (&key (ps 'ps))
  :parents (verilog-printing)
  :short "Should Verilog-2005 @('(* key = val *)')-style attributes be shown?"
  :long "<p>See also @(see vl-ps-update-show-atts).</p>"
  (let ((hidep (cdr (assoc-equal :vl-hide-atts (vl-ps->misc)))))
    (not hidep)))

(define vl-ps-update-show-atts ((showp booleanp) &key (ps 'ps))
  :parents (verilog-printing)
  :short "Set whether Verilog-2005 @('(* key = val *)')-style attributes should
be displayed."
  :long "<p>We want the default to be @('t'), so we look for @('hide-atts')
instead of @('show-atts').</p>"
  :verbosep t
  (let ((hidep (not showp))
        (misc  (vl-ps->misc)))
    (vl-ps-update-misc (acons :vl-hide-atts hidep misc))))

(define vl-simple-id-tail-string-p ((x stringp)
                                    (i natp)
                                    (len (eql len (length x))))
  :guard (<= i len)
  :measure (nfix (- (nfix len) (nfix i)))
  :parents (vl-maybe-escape-identifier)
  (if (mbe :logic (zp (- (nfix len) (nfix i)))
           :exec (eql i len))
      t
    (and (vl-simple-id-tail-p (char x i))
         (vl-simple-id-tail-string-p x (+ 1 (lnfix i)) len))))


(define vl-maybe-escape-identifier ((x stringp "Name of some identifier."))
  :returns (x-escaped stringp :rule-classes :type-prescription)
  :parents (verilog-printing)
  :short "Add escape characters to an identifier name, if necessary."

  :long "<p>Usually @('x') contains only ordinary characters and does not need
to be escaped, and in such cases we return @('x') unchanged.  Otherwise, we add
the leading @('\\') character and trailing space.</p>

<p>Note: we assume that @('x') has no embedded spaces and at least one
character.  These requirements aren't explicit about the names used in
structures like @(see vl-id-p), @(see vl-modinst-p), and so forth.  But they
should hold for any valid Verilog that we parse or generate.</p>"

  :prepwork
  ((local (defthm optimization
            (implies (stringp x)
                     (iff (member #\$ (explode x))
                          (position #\$ x)))
            :hints(("Goal" :in-theory (enable position))))))

  (b* ((x (string-fix x))
       (len (length x))
       ((when (zp len))
        (raise "Empty identifier")
        "")
       ((when (and (vl-simple-id-head-p (char x 0))
                   (vl-simple-id-tail-string-p x 1 len)
                   (mbe :logic (not (member #\$ (explode x)))
                        :exec (not (position #\$ x)))))
        ;; A simple identifier, nothing to add.
        x)
       ;; Escaped identifier.  This isn't efficient but this should be pretty
       ;; unusual.
       ((when (position #\Space x))
        (raise "Identifier name has spaces?  ~x0" x)
        ""))
    (implode (cons #\\ (str::append-chars x (list #\Space))))))


(define vl-print-modname ((x stringp) &key (ps 'ps))
  :parents (verilog-printing)
  :short "@(call vl-print-modname) prints a module's name."

  :long "<p>When we are printing plain-text output, this function behaves the
same as @(see vl-print) except that we may escape @('x') if necessary; see
@(see vl-maybe-escape-identifier).</p>

<p>When we are printing HTML output, we print something like:</p>

@({
<a class=\"vl_modlink\" href=\"javascript:showModule('foo')\">foo</a>
})

<p>This function is used in various warning messages, reports, and other
displays.  The module browser's web pages are responsible for defining the
@('showModule') function to carry out some sensible behavior.</p>"

  (vl-ps-span
   "vl_id"
   (vl-when-html
    (vl-print-markup "<a class=\"vl_modlink\" href=\"javascript:void(0);\" onClick=\"showModule('")
    (vl-print-url (string-fix x))
    (vl-print-markup "')\">"))
   (vl-print-str (vl-maybe-escape-identifier x))
   (vl-when-html (vl-print-markup "</a>"))))

(define vl-print-wirename ((x stringp) &key (ps 'ps))
  :parents (verilog-printing)
  :verbosep t
  :short "@(call vl-print-wirename) prints a wire's name."

  :long "<p>This is much like @(see vl-print-modname) except that we use it for
the names of identifiers within a module -- most commonly wire names, but we also
use it for the names of blocks, module instances, and so on.</p>

<p>In text mode, we just print @('x'), escaping it if necessary.  In HTML mode,
we print something like:</p>

@({
<a class=\"vl_wirelink\" href=\"javascript:showWire('foo')\">foo</a>
})

<p>This function is used in various warning messages, reports, and other
displays.  The module browser's web pages are responsible for defining the
@('showWire') function to carry out some sensible behavior.</p>"

  (b* ((x (string-fix x)))
    (vl-ps-span
     "vl_id"
     (vl-when-html (vl-print-markup "<a class=\"")
                   (b* ((misc  (vl-ps->misc))
                        (ports (cdr (hons-assoc-equal :portnames misc))))
                     (vl-print-markup (if (member-equal x (redundant-list-fix ports))
                                          "vl_wirelink_port"
                                        "vl_wirelink")))
                   (vl-print-markup "\" href=\"javascript:void(0);\" onClick=\"showWire('")
                   (vl-print-url x)
                   (vl-print-markup "')\">"))
     (vl-print-str (vl-maybe-escape-identifier x))
     (vl-when-html (vl-print-markup "</a>")))))

(define vl-pp-set-portnames ((portdecls vl-portdecllist-p) &key (ps 'ps))
  (b* ((names (vl-portdecllist->names portdecls))
       (misc  (vl-ps->misc)))
    (vl-ps-update-misc (acons :portnames names misc))))

(define vl-print-ext-wirename ((modname stringp)
                               (wirename stringp)
                               &key (ps 'ps))
  :parents (verilog-printing)
  :short "@(call vl-print-ext-wirename) prints a wire's name."

  :long "<p>This is almost identical to @(see vl-print-wirename), but is intended
for messages where the module might not be apparent.</p>

<p>In text mode, we just print @('x'), escaping it if necessary.  In HTML mode,
we print something like:</p>

@({
<a class=\"vl_wirelink\" href=\"javascript:showWireExt('mod', 'w')\">w</a>
})

<p>The module browser's web pages are responsible for defining the
@('showWireExt') function to carry out some sensible behavior.</p>"

  (vl-ps-span
   "vl_id"
   (vl-when-html
    (vl-print-markup "<a class=\"vl_wirelink\" href=\"javascript:void(0);\" onClick=\"showWireExt('")
    (vl-print-url (string-fix modname))
    (vl-print-markup "', '")
    (vl-print-url (string-fix wirename))
    (vl-print-markup "')\">"))
   (vl-print-str (vl-maybe-escape-identifier wirename))
   (vl-when-html (vl-print-markup "</a>"))))

(define vl-print-loc ((x vl-location-p) &key (ps 'ps))
  :parents (verilog-printing)
  :short "@(call vl-print-loc) prints a @(see vl-location-p)."

  :long "<p>In text mode, this function basically prints the string produced by
@(see vl-location-string).  But when HTML mode is active, we instead print
something along the lines of:</p>

@({
<a class=\"vl_loclink\"
   href=\"javascript:void(0);\"
   onClick=\"showLoc('foo', 'line', 'col')\">
  foo:line:col
</a>
})

<p>This function is used in various warning messages, reports, and other
displays.  The module browser's web pages are responsible for defining the
@('showLoc') function to carry out some sensible behavior.</p>"

  (if (not (vl-ps->htmlp))
      (let* ((str (vl-location-string x))
             (len (length str))
             (col (vl-ps->col))
             (autowrap-col (vl-ps->autowrap-col))
             (autowrap-ind (vl-ps->autowrap-ind)))
        (cond ((or (< (+ col len) autowrap-col)
                   (< col (+ autowrap-ind 10)))
               (vl-print-str str))
              (t
               (vl-ps-seq
                (vl-println "")
                (vl-indent autowrap-ind)
                (vl-print-str str)))))
    (let* ((filename   (vl-location->filename x))
           (line       (vl-location->line x))
           (col        (vl-location->col x))
           (flen       (length filename))
           (last-slash (str::strrpos "/" filename))
           (shortname  (if (and last-slash (< last-slash flen))
                           (subseq filename (1+ last-slash) nil)
                         filename)))
      (vl-ps-seq
       (vl-print-markup "<a class=\"vl_loclink\" href=\"javascript:void(0);\" onClick=\"showLoc('")
       (vl-print-url (vl-location->filename x))
       (vl-print-markup "', '")
       (vl-print-url line)
       (vl-print-markup "', '")
       (vl-print-url col)
       (vl-print-markup "')\")>")
       (vl-print-str shortname)
       (vl-print-str ":")
       (vl-print-nat line)
       (vl-print-str ":")
       (vl-print-nat col)
       (vl-print-markup "</a>")))))

(define vl-pp-constint ((x vl-constint-p) &key (ps 'ps))
  ;; BOZO origwidth/origtype okay here???
  ;; BOZO maybe add origbase or something for printing in the same radix
  ;; as the number was read in?
  (b* (((vl-constint x) x)

       ((when (and (eq x.origtype :vl-signed)
                   (eql x.origwidth 32)))
        ;; BOZO this might not be quite right.  We hope that it allows us to
        ;; print plain decimal integers when the user used them originally,
        ;; mainly because things like foo[32'd5] is a lot uglier than foo[5].
        ;; But we might eventually want to think hard about whether this is
        ;; really okay.
        (vl-ps-span "vl_int" (vl-print-nat x.value))))

    (vl-ps-span "vl_int"
                (vl-print-nat x.origwidth)
                (if (eq x.origtype :vl-signed)
                    (vl-print-str "'sd")
                  (vl-print-str "'d"))
                (vl-print-nat x.value))))

(define vl-pp-weirdint ((x vl-weirdint-p) &key (ps 'ps))
  ;; BOZO origwidth/origtype okay here??
  ;; BOZO maybe add origbase
  (b* (((vl-weirdint x) x))
    (vl-ps-span "vl_int"
                (vl-print-nat x.origwidth)
                (if (eq x.origtype :vl-signed)
                    (vl-print-str "'sb")
                  (vl-print-str "'b"))
                (vl-print (vl-bitlist->charlist x.bits)))))

(define vl-maybe-escape-string ((x stringp)
                                (i natp)
                                (len (and (natp len)
                                          (eql len (length x))))
                                (acc character-listp))
  :guard (<= i len)
  :returns (new-acc character-listp :hyp :fguard)
  :measure (nfix (- (nfix len) (nfix i)))
  :hooks nil
  (if (mbe :logic (zp (- (nfix len) (nfix i)))
           :exec (int= i len))
      (reverse acc)
    (let ((car (char x i)))
      (vl-maybe-escape-string x (+ 1 (lnfix i)) len
                              (case car
                                (#\Newline (list* #\n #\\ acc))
                                (#\Tab     (list* #\t #\\ acc))
                                (#\\       (list* #\\ #\\ acc))
                                (#\"       (list* #\" #\\ acc))
                                ;; BOZO do we need to do anything about
                                ;; nonprintable characters?  Convert them into
                                ;; \039 format, etc?
                                (t         (cons car acc)))))))

(define vl-pp-string ((x vl-string-p) &key (ps 'ps))
  (b* (((vl-string x) x)
       (length        (length x.value)))
    (vl-ps-span "vl_str"
                (vl-print (vl-maybe-escape-string x.value 0 length (list #\")))
                (vl-println? #\"))))

(define vl-pp-real ((x vl-real-p) &key (ps 'ps))
  (vl-ps-span "vl_real"
              (vl-println? (vl-real->value x))))

(define vl-pp-id ((x vl-id-p) &key (ps 'ps))
  :inline t
  (vl-print-wirename (vl-id->name x)))

(define vl-pp-hidpiece ((x vl-hidpiece-p) &key (ps 'ps))
  (vl-ps-span "vl_id"
              (vl-print-str (vl-maybe-escape-identifier (vl-hidpiece->name x)))))

(define vl-pp-sysfunname ((x vl-sysfunname-p) &key (ps 'ps))
  (vl-ps-span "vl_sys"
              (vl-print-str (vl-sysfunname->name x))))

(define vl-pp-funname ((x vl-funname-p) &key (ps 'ps))
  (vl-ps-span "vl_id"
              (vl-print-str (vl-maybe-escape-identifier (vl-funname->name x)))))

(define vl-pp-tagname ((x vl-tagname-p) &key (ps 'ps))
  (vl-ps-span "vl_tagname"
              (vl-print-str (vl-tagname->name x))))


(define vl-keygutstype->string ((x vl-keygutstype-p))
  :returns (str stringp :rule-classes :type-prescription)
  (case (vl-keygutstype-fix x)
    (:vl-null  "null")
    (:vl-this  "this")
    (:vl-super "super")
    (:vl-local "local")
    (:vl-$     "$")
    (:vl-$root "$root")
    (:vl-$unit "$unit")
    (:vl-emptyqueue "{}")
    (otherwise (progn$ (impossible) "null"))))

(define vl-pp-keyguts ((x vl-keyguts-p) &key (ps 'ps))
  (vl-ps-span "vl_key"
              (vl-print-str (vl-keygutstype->string
                             (vl-keyguts->type x)))))

(define vl-pp-extint ((x vl-extint-p) &key (ps 'ps))
  (b* (((vl-extint x) x))
    (vl-print-str
     (case x.value
       (:vl-0val "'0")
       (:vl-1val "'1")
       (:vl-xval "'x")
       (:vl-zval "'z")))))

(define vl-pp-time ((x vl-time-p) &key (ps 'ps))
  (b* (((vl-time x) x))
    (vl-ps-seq
     (vl-print-str x.quantity)
     (vl-print (vl-timeunit->string x.units)))))


(define vl-basictypekind->string ((x vl-basictypekind-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints(("Goal" :in-theory (enable vl-basictypekind-p)))
  (case (vl-basictypekind-fix x)
    (:vl-byte      "byte")
    (:vl-shortint  "shortint")
    (:vl-int       "int")
    (:vl-longint   "longint")
    (:vl-integer   "integer")
    (:vl-time      "time")
    (:vl-bit       "bit")
    (:vl-logic     "logic")
    (:vl-reg       "reg")
    (:vl-shortreal "shortreal")
    (:vl-real      "real")
    (:vl-realtime  "realtime")
    (otherwise (progn$ (impossible) "reg"))))

(define vl-pp-basictype ((x vl-basictype-p) &key (ps 'ps))
  (vl-ps-span "vl_key"
              (vl-print-str (vl-basictypekind->string
                             (vl-basictype->kind x)))))




(define vl-pp-atomguts ((x vl-atomguts-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-atomguts-p)))
  (let ((x (vl-atomguts-fix x)))
    (case (tag x)
      (:vl-id         (vl-pp-id x))
      (:vl-constint   (vl-pp-constint x))
      (:vl-weirdint   (vl-pp-weirdint x))
      (:vl-string     (vl-pp-string x))
      (:vl-real       (vl-pp-real x))
      (:vl-hidpiece   (vl-pp-hidpiece x))
      (:vl-funname    (vl-pp-funname x))
      (:vl-extint     (vl-pp-extint x))
      (:vl-time       (vl-pp-time x))
      (:vl-keyguts    (vl-pp-keyguts x))
      (:vl-basictype  (vl-pp-basictype x))
      (:vl-tagname    (vl-pp-tagname x))
      (otherwise      (vl-pp-sysfunname x)))))

(define vl-pp-atom ((x vl-expr-p) &key (ps 'ps))
  :guard (vl-atom-p x)
  :inline t
  (vl-pp-atomguts (vl-atom->guts x)))

(define vl-op-string ((x vl-op-p))
  :returns (str stringp :rule-classes :type-prescription)
  (case (vl-op-fix x)
    (:vl-unary-bitnot "~")
    (:vl-binary-bitand "&")
    (:vl-binary-bitor "|")

    (:vl-unary-plus "+")
    (:vl-unary-minus "-")
    (:vl-unary-lognot "!")
    (:vl-unary-bitand "&")
    (:vl-unary-nand "~&")
    (:vl-unary-bitor "|")
    (:vl-unary-nor "~|")
    (:vl-unary-xor "^")
    (:vl-unary-xnor "~^")

    (:vl-binary-plus "+")
    (:vl-binary-minus "-")
    (:vl-binary-times "*")
    (:vl-binary-div "/")
    (:vl-binary-rem "%")
    (:vl-binary-eq "==")
    (:vl-binary-neq "!=")
    (:vl-binary-ceq "===")
    (:vl-binary-cne "!==")
    (:vl-binary-wildeq "==?")
    (:vl-binary-wildneq "!=?")
    (:vl-binary-logand "&&")
    (:vl-binary-logor "||")
    (:vl-binary-power "**")
    (:vl-binary-lt "<")
    (:vl-binary-lte "<=")
    (:vl-binary-gt ">")
    (:vl-binary-gte ">=")
    (:vl-binary-xor "^")
    (:vl-binary-xnor "~^")
    (:vl-binary-shr ">>")
    (:vl-binary-shl "<<")
    (:vl-binary-ashr ">>>")
    (:vl-binary-ashl "<<<")

    (:vl-implies "->")
    (:vl-equiv "<->")

    (:vl-partselect-colon ":")
    (:vl-partselect-pluscolon "+:")
    (:vl-partselect-minuscolon "-:")

    (:vl-scope "::")

    (t
     (or (raise "Bad operator: ~x0.~%" x) ""))))

(defmacro vl-ops-precedence-table ()
  ''(;; These aren't real operators as far as the precedence rules are
     ;; concerned, but they need to bind even more tightly than +, -, etc.
     (:VL-BITSELECT             . 20)
     (:VL-ARRAY-INDEX           . 20)
     (:VL-INDEX                 . 20)
     (:VL-PARTSELECT-COLON      . 20)
     (:VL-PARTSELECT-PLUSCOLON  . 20)
     (:VL-PARTSELECT-MINUSCOLON . 20)
     (:VL-FUNCALL               . 20)
     (:VL-SYSCALL               . 20)
     (:VL-HID-DOT               . 20)
     ;(:VL-HID-ARRAYDOT          . 20)
     (:VL-SCOPE                 . 20)
     (:VL-WITH-INDEX            . 20)
     (:VL-WITH-COLON            . 20)
     (:VL-WITH-PLUSCOLON        . 20)
     (:VL-WITH-MINUSCOLON       . 20)


     ;; In Verilog-2005 Table 5-4, concats are said to have minimal precedence.
     ;; But that doesn't really make sense.  For instance, in: a + {b + c} the
     ;; {b + c} term acts more like an operand than another operator.  So, here
     ;; I say that concats and multiconcats also have precedence 20, so they
     ;; will be treated just like operands.  That is, we want to write
     ;; &{foo,bar} rather than &({foo,bar}).  For similar reasons, I put the
     ;; mintypmax operand here with precedence 20.
     (:VL-CONCAT             . 20)
     (:VL-MULTICONCAT        . 20)
     (:VL-MINTYPMAX          . 20)
     (:VL-STREAM-LEFT        . 20)
     (:VL-STREAM-RIGHT       . 20)
     (:VL-STREAM-LEFT-SIZED  . 20)
     (:VL-STREAM-RIGHT-SIZED . 20)
     (:VL-TAGGED             . 20)

     ;; This part is based on Verilog-2005 Table 5-4, and SystemVerilog-2012
     ;; Table 11-2.
     (:VL-UNARY-PLUS    . 14)
     (:VL-UNARY-MINUS   . 14)
     (:VL-UNARY-LOGNOT  . 14)
     (:VL-UNARY-BITNOT  . 14)
     (:VL-UNARY-BITAND  . 14)
     (:VL-UNARY-NAND    . 14)
     (:VL-UNARY-BITOR   . 14)
     (:VL-UNARY-NOR     . 14)
     (:VL-UNARY-XOR     . 14)
     (:VL-UNARY-XNOR    . 14)

     (:VL-BINARY-POWER  . 13)

     (:VL-BINARY-TIMES  . 12)
     (:VL-BINARY-DIV    . 12)
     (:VL-BINARY-REM    . 12)

     (:VL-BINARY-PLUS   . 11)
     (:VL-BINARY-MINUS  . 11)

     (:VL-BINARY-SHR    . 10)
     (:VL-BINARY-SHL    . 10)
     (:VL-BINARY-ASHR   . 10)
     (:VL-BINARY-ASHL   . 10)

     (:VL-BINARY-LT     . 9)
     (:VL-BINARY-LTE    . 9)
     (:VL-BINARY-GT     . 9)
     (:VL-BINARY-GTE    . 9)

     (:VL-BINARY-EQ     . 8)
     (:VL-BINARY-NEQ    . 8)
     (:VL-BINARY-CEQ    . 8)
     (:VL-BINARY-CNE    . 8)
     (:vl-binary-wildeq . 8)
     (:vl-binary-wildneq . 8)

     (:VL-BINARY-BITAND . 7)

     (:VL-BINARY-XOR    . 6)
     (:VL-BINARY-XNOR   . 6)

     (:VL-BINARY-BITOR  . 5)

     (:VL-BINARY-LOGAND . 4)

     (:VL-BINARY-LOGOR  . 3)

     (:VL-QMARK         . 2)

     (:vl-implies . 1)
     (:vl-equiv   . 1)
     ))

(define vl-op-precedence-< ((x vl-op-p) (y vl-op-p))
  :inline t
  :guard-hints(("Goal" :in-theory (enable vl-op-p)))
  (let ((table (vl-ops-precedence-table)))
    (< (the (unsigned-byte 8) (cdr (assoc (vl-op-fix x) table)))
       (the (unsigned-byte 8) (cdr (assoc (vl-op-fix y) table))))))

(define vl-op-precedence-<= ((x vl-op-p) (y vl-op-p))
  :inline t
  :guard-hints(("Goal" :in-theory (enable vl-op-p)))
  (let ((table (vl-ops-precedence-table)))
    (<= (the (unsigned-byte 8) (cdr (assoc (vl-op-fix x) table)))
        (the (unsigned-byte 8) (cdr (assoc (vl-op-fix y) table))))))

(defmacro vl-pp-expr-special-atts ()
  ''("VL_ORIG_EXPR"
     "VL_EXPLICIT_PARENS"))

(defrule vl-atts-count-of-vl-remove-keys
  (<= (vl-atts-count (vl-remove-keys keys x))
      (vl-atts-count x))
  :rule-classes ((:rewrite) (:linear))
  :enable (vl-remove-keys vl-atts-count)
  :disable vl-atts-p-of-vl-remove-keys)


(defines vl-pp-expr
  :parents (verilog-printing)
  :short "Pretty-printer for expressions."
  :long "<p>@(call vl-pp-expr) pretty-prints the expression @('x') to @(see
ps). See also @(see vl-pps-expr) and @(see vl-pp-origexpr).</p>

<p>Originally we defensively introduced parens around every operator.  But that
was kind of ugly.  Now each operator is responsible for putting parens around
its arguments, if necessary.</p>"

  :prepwork
  ((local (in-theory (disable MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF
                              double-containment
                              ACL2::TRUE-LISTP-MEMBER-EQUAL
                              ACL2::CONSP-MEMBER-EQUAL
                              ACL2::SUBSETP-MEMBER
                              default-car
                              default-cdr
                              assoc-equal-elim
                              acl2::consp-under-iff-when-true-listp
                              member-equal-when-all-equalp
                              acl2::cancel_times-equal-correct
                              acl2::cancel_plus-equal-correct
                              CAR-WHEN-ALL-EQUALP
                              CONSP-WHEN-MEMBER-EQUAL-OF-VL-MODALIST-P
                              CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P
                              CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P
                              CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP
                              CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P
                              VL-ATOMLIST-P-WHEN-NOT-CONSP
                              VL-ATOM-P-OF-CAR-WHEN-VL-ATOMLIST-P
                              acl2::consp-by-len))))

  (define vl-pp-expr ((x vl-expr-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-expr-count x) 2)
    (if (vl-fast-atom-p x)
        (vl-pp-atom x)
      (let ((op   (vl-nonatom->op x))
            (args (vl-nonatom->args x))
            (atts (vl-remove-keys (vl-pp-expr-special-atts) (vl-nonatom->atts x))))
        (case op
          ((:vl-unary-plus
            :vl-unary-minus :vl-unary-lognot :vl-unary-bitnot :vl-unary-bitand
            :vl-unary-nand :vl-unary-bitor :vl-unary-nor :vl-unary-xor
            :vl-unary-xnor)
           (b* (((unless (consp args))
                 (impossible)
                 ps)
                (arg (first args))
                (want-parens-p (if (vl-fast-atom-p arg)
                                   nil
                                 (vl-op-precedence-<= (vl-nonatom->op arg) op))))
             (vl-ps-seq
              (vl-print-str (vl-op-string op))
              (if atts (vl-pp-atts atts) ps)
              (vl-print-str " ")
              (if want-parens-p (vl-print "(") ps)
              (vl-pp-expr arg)
              (if want-parens-p (vl-print ")") ps)
              (vl-println? ""))))

          ((:vl-binary-plus
            :vl-binary-minus :vl-binary-times :vl-binary-div :vl-binary-rem
            :vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
            :vl-binary-wildeq :vl-binary-wildneq
            :vl-binary-logand :vl-binary-logor
            :vl-binary-power
            :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte
            :vl-binary-bitand :vl-binary-bitor
            :vl-binary-xor :vl-binary-xnor
            :vl-binary-shr :vl-binary-shl :vl-binary-ashr :vl-binary-ashl)
           (b* (((unless (consp args))
                 (impossible)
                 ps)
                (arg1 (first args))
                (arg2 (second args))
                ;; they associate left to right, so we only need parens around the first
                ;; arg if its precedence is less than ours.
                (want-parens-1p (if (vl-fast-atom-p arg1)
                                    nil
                                  (or (vl-op-precedence-< (vl-nonatom->op arg1) op)
                                      (assoc-equal "VL_EXPLICIT_PARENS" (vl-nonatom->atts arg1)))))
                (want-parens-2p
                 (b* (((when (vl-fast-atom-p arg2))
                       nil)

                      (op2 (vl-nonatom->op arg2))
                      ((when (vl-op-precedence-<= op2 op))
                       t))

; We found that Verilog-XL and NCVerilog got upset about expressions like:
;
;  a & &b
;  a | |b
;
; even though they seem legal per the Verilog-2005 standard.  So, in our
; pretty-printer we now add parens around the 2nd operand when we hit these
; cases, just so that when we write out test benches they work.  We tried a lot
; of other combinations like a ^ ^b, a && &b, etc., but these tools don't seem
; to care about those things.

                   (or (and (eq op :vl-binary-bitand)
                            (eq op2 :vl-unary-bitand))
                       (and (eq op :vl-binary-bitor)
                            (eq op2 :vl-unary-bitor))
                       (assoc-equal "VL_EXPLICIT_PARENS" (vl-nonatom->atts arg2))))))

             (vl-ps-seq (if want-parens-1p (vl-print "(") ps)
                        (vl-pp-expr arg1)
                        (if want-parens-1p (vl-print ")") ps)
                        (vl-print-str " ")
                        (vl-print-str (vl-op-string op))
                        (if atts (vl-pp-atts atts) ps)
                        (vl-println? " ")
                        (if want-parens-2p (vl-print "(") ps)
                        (vl-pp-expr arg2)
                        (if want-parens-2p (vl-print ")") ps)
                        (vl-println? ""))))

          ((:vl-qmark)
           (b* (((unless (consp args))
                 (impossible)
                 ps)
                ((list arg1 arg2 arg3) args)
                ;; these associate right to left, so "a ? b : (c ? d : e)" doesn't
                ;; need parens, but "(a ? b : c) ? d : e" does need parens.

                ;; In Verilog-2005 every other operator has precedence greater
                ;; than ?:, so we never needed parens around arg3, and only
                ;; rarely needed them around arg1/arg2.

                ;; In SystemVerilog there are some operators (assignment
                ;; operators and things like <->) that are lower precedence, so
                ;; we need to check.
                (want-parens-1p (if (vl-fast-atom-p arg1)
                                    nil
                                  (vl-op-precedence-<= (vl-nonatom->op arg1) op)))
                (want-parens-2p (if (vl-fast-atom-p arg2)
                                    nil
                                  (vl-op-precedence-<= (vl-nonatom->op arg2) op)))
                (want-parens-3p (if (vl-fast-atom-p arg3)
                                    nil
                                  (vl-op-precedence-< (vl-nonatom->op arg3) op))))
             (vl-ps-seq (if want-parens-1p (vl-print "(") ps)
                        (vl-pp-expr arg1)
                        (if want-parens-1p (vl-print ")") ps)

                        (vl-print-str " ? ")
                        (if atts
                            (vl-ps-seq (vl-pp-atts atts)
                                       (vl-print " "))
                          ps)
                        (vl-println? "")

                        (if want-parens-2p (vl-print "(") ps)
                        (vl-pp-expr arg2)
                        (if want-parens-2p (vl-print ")") ps)

                        (vl-println? " : ")

                        (if want-parens-3p (vl-print "(") ps)
                        (vl-pp-expr arg3)
                        (if want-parens-3p (vl-print ")") ps)

                        (vl-println? ""))))

          ((:vl-implies :vl-equiv)
           (b* (((unless (consp args))
                 (impossible)
                 ps)
                ((list arg1 arg2) args)
                ;; these associate right to left, so "a <-> (b <-> c)" does
                ;; not need parens, but (a <-> b) <-> c does.
                (want-parens-1p (if (vl-fast-atom-p arg1)
                                    nil
                                  (vl-op-precedence-<= (vl-nonatom->op arg1) op)))
                (want-parens-2p (if (vl-fast-atom-p arg2)
                                    nil
                                  (vl-op-precedence-< (vl-nonatom->op arg2) op))))
             (vl-ps-seq (if want-parens-1p (vl-print "(") ps)
                        (vl-pp-expr arg1)
                        (if want-parens-1p (vl-print ")") ps)
                        (vl-print-str (vl-op-string op))
                        (if atts
                            (vl-ps-seq (vl-pp-atts atts)
                                       (vl-print " "))
                          ps)
                        (vl-println? "")
                        (if want-parens-2p (vl-print "(") ps)
                        (vl-pp-expr arg2)
                        (if want-parens-2p (vl-print ")") ps)
                        (vl-println? ""))))

          ((:vl-mintypmax)
           ;; Unlike other operands, I put mintypmax expressions in their own
           ;; parens so that I'm basically justified in treating them as having
           ;; operand-level precedence.
           (if (not (consp args))
               (prog2$ (impossible) ps)
             (vl-ps-seq (vl-print "(")
                        (vl-pp-expr (first args))
                        (vl-println? " : ")
                        (vl-pp-expr (second args))
                        (vl-println? " : ")
                        (vl-pp-expr (third args))
                        (vl-println? ")"))))

          ((:vl-bitselect :vl-array-index :vl-index)
           ;; These don't need parens because they have maximal precedence
           (cond ((not (consp args))
                  (prog2$ (impossible) ps))
                 (t
                  (vl-ps-seq (vl-pp-expr (first args))
                             (vl-print "[")
                             (vl-pp-expr (second args))
                             (vl-print "]")))))

          ((:vl-partselect-colon :vl-partselect-pluscolon :vl-partselect-minuscolon)
           ;; These don't need parens because they have maximal precedence
           (cond ((not (consp args))
                  (prog2$ (impossible) ps))
                 (t
                  (vl-ps-seq (vl-pp-expr (first args))
                             (vl-print "[")
                             (vl-pp-expr (second args))
                             (vl-print-str (vl-op-string op))
                             (vl-pp-expr (third args))
                             (vl-print "]")))))

          ((:vl-hid-dot)
           ;; These don't need parens because they have maximal precedence
           (if (atom args)
               (prog2$ (impossible) ps)
             (vl-ps-seq (vl-pp-expr (first args))
                        (vl-print ".")
                        (vl-pp-expr (second args)))))

          ((:vl-scope)
           ;; These don't need parens because they have maximal precedence
           (if (atom args)
               (prog2$ (impossible) ps)
             (vl-ps-seq (vl-pp-expr (first args))
                        (vl-print "::")
                        (vl-pp-expr (second args)))))

          ((:vl-multiconcat)
           ;; These don't need parens because they have maximal precedence
           (cond ((atom args)
                  (prog2$ (impossible) ps))

                 ((and (not (vl-atom-p (second args)))
                       (eq (vl-nonatom->op (second args)) :vl-concat))
                  ;; The concat inserts its own braces
                  (vl-ps-seq (vl-print "{")
                             (vl-pp-expr (first args))
                             (vl-println? " ")
                             (vl-pp-expr (second args))
                             (vl-print "}")))

                 (t
                  ;; Otherwise we've simplified the concat away.  Put in braces
                  ;; around whatever our arg is.
                  (vl-ps-seq (vl-print "{")
                             (vl-pp-expr (first args))
                             (vl-println? " {")
                             (vl-pp-expr (second args))
                             (vl-print "}}")))))

          ((:vl-concat)
           ;; This doesn't need parens because it has maximal precedence
           (vl-ps-seq (vl-print "{")
                      (vl-pp-exprlist args)
                      (vl-print "}")))

          ((:vl-stream-left :vl-stream-right)
           (if (atom args)
               (progn$ (raise "Bad streaming concatenation")
                       ps)
             (vl-ps-seq (vl-print "{")
                        (vl-print (if (eq op :vl-stream-left) "<<" ">>"))
                        (vl-print "{")
                        (vl-pp-exprlist args)
                        (vl-print "}}"))))

          ((:vl-stream-left-sized :vl-stream-right-sized)
           (if (atom args)
               (progn$ (raise "Bad streaming concatenation")
                       ps)
             (vl-ps-seq (vl-print "{")
                        (vl-print (if (eq op :vl-stream-left-sized) "<<" ">>"))
                        (vl-pp-expr (first args))
                        (vl-print " {")
                        (vl-pp-exprlist (rest args))
                        (vl-print "}}"))))

          ((:vl-with-index :vl-with-colon :vl-with-pluscolon :vl-with-minuscolon)
           (if (atom args)
               (progn$ (raise "Bad with expression")
                       ps)
             (vl-ps-seq (vl-pp-expr (first args))
                        (vl-ps-span "vl_key" (vl-print " with "))
                        (vl-print "[")
                        (vl-pp-expr (second args))
                        (case op
                          (:vl-with-index     ps)
                          (:vl-with-colon     (vl-ps-seq (vl-print ":")
                                                         (vl-pp-expr (third args))))
                          (:vl-with-pluscolon (vl-ps-seq (vl-print "+:")
                                                         (vl-pp-expr (third args))))
                          (otherwise          (vl-ps-seq (vl-print "-:")
                                                         (vl-pp-expr (third args)))))
                        (vl-print "]"))))

          ((:vl-tagged)
           (if (atom args)
               (prog2$ (raise "Bad tagged expr")
                       ps)
             (vl-ps-seq (vl-ps-span "vl_key" (vl-print "tagged "))
                        (vl-pp-expr (first args))
                        (if (atom (cdr args))
                            ps
                          (vl-ps-seq (vl-print " ")
                                     (vl-pp-expr (second args))))
                        (vl-println? ""))))

          ((:vl-funcall)
           ;; This doesn't need parens because it has maximal precedence
           (if (atom args)
               (prog2$ (raise "Bad funcall")
                       ps)
             (vl-ps-seq (vl-pp-expr (first args))
                        (vl-print "(")
                        (vl-pp-exprlist (rest args))
                        (vl-println? ")"))))

          ((:vl-syscall)
           ;; This doesn't need parens because it has maximal precedence
           (if (atom args)
               (prog2$ (raise "Bad syscall.")
                       ps)
             (vl-ps-seq (vl-pp-expr (first args))
                        ;; Something tricky about system calls is: if there
                        ;; aren't any arguments, then there should not even be
                        ;; any parens!
                        (if (consp (rest args))
                            (vl-print "(")
                          ps)
                        (vl-pp-exprlist (rest args))
                        (if (consp (rest args))
                            (vl-println? ")")
                          ps))))

          (t
           (prog2$ (raise "Bad op: ~x0.~%" op)
                   ps))))))

  (define vl-pp-atts-aux ((x vl-atts-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-atts-count x) 0)
    (let ((x (vl-atts-fix x)))
      (cond ((atom x)
             ps)
            ;; ((atom (car x)) ;; Non-alist convention
            ;;  (vl-pp-atts-aux (cdr x)))
            (t
             (vl-ps-seq (vl-print-str (caar x)) ;; name
                        ;; Expr, if exists
                        (if (cdar x)
                            (vl-ps-seq (vl-print " = ")
                                       (vl-pp-expr (cdar x)))
                          ps)
                        ;; Comma, if more atts
                        (if (consp (cdr x))
                            (vl-println? ", ")
                          ps)
                        ;; The rest of the atts
                        (vl-pp-atts-aux (cdr x)))))))

  (define vl-pp-atts ((x vl-atts-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-atts-count x) 1)
    (let ((x (vl-atts-fix x)))
      (if (and (consp x)
               (vl-ps->show-atts-p))
          (vl-ps-span "vl_cmt"
                      (vl-print "(* ")
                      (vl-pp-atts-aux x)
                      (vl-println? " *)"))
        ps)))

  (define vl-pp-exprlist ((x vl-exprlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-exprlist-count x) 0)
    (cond ((atom x)
           ps)
          ((atom (cdr x))
           (vl-pp-expr (car x)))
          (t
           (vl-ps-seq (vl-pp-expr (car x))
                      (vl-println? ", ")
                      (vl-pp-exprlist (cdr x))))))

  ///
  (local (defthm vl-pp-atts-aux-when-atom
           (implies (atom x)
                    (equal (vl-pp-atts-aux x)
                           ps))
           :hints(("Goal" :expand (vl-pp-atts-aux x)))))

  (local (defthm vl-pp-atts-when-atom
           (implies (atom x)
                    (equal (vl-pp-atts x)
                           ps))
           :hints(("Goal" :expand (vl-pp-atts x)))))

  (local (in-theory (disable acl2::member-of-cons
                             acl2::member-when-atom
                             arg1-exists-by-arity
                             ARG2-EXISTS-BY-ARITY)))

  (local (in-theory (disable vl-pp-expr
                             vl-pp-atts
                             vl-pp-atts-aux
                             vl-pp-exprlist)))

  (deffixequiv-mutual vl-pp-expr
    :hints(("Goal"
            :expand ((vl-pp-expr (vl-expr-fix x))
                     (vl-pp-expr x)
                     (vl-pp-atts-aux (vl-atts-fix x))
                     (vl-pp-atts-aux x)
                     (vl-pp-atts (vl-atts-fix x))
                     (vl-pp-atts x)
                     (vl-pp-exprlist (vl-exprlist-fix x))
                     (vl-pp-exprlist x)
                     )))))


(define vl-pps-expr ((x vl-expr-p))
  :returns (pretty-x stringp :rule-classes :type-prescription)
  :parents (expr-tools verilog-printing)
  :short "Pretty-print an expression into a string."
  :long "<p>This pretty-prints an expression \"as is,\" i.e., in its current,
possibly transformed state.  Depending on what you're trying to do, it may be
better to use @(see vl-pps-origexpr) instead, which tries to print the
\"original,\" pre-transformed version of the expression, as it occurred in the
real Verilog file.</p>"
  (with-local-ps (vl-pp-expr x)))

(define vl-pp-origexpr ((x vl-expr-p) &key (ps 'ps))
  :parents (origexprs verilog-printing)
  :short "Pretty-print the \"original,\" un-transformed version of an
expression."
  :long "<p>This is like @(see vl-pp-expr) but, if @('x') has a
@('VL_ORIG_EXPR') attribute (see @(see origexprs)), we actually pretty-print
the original version of @('x') rather than the current version (which may be
simplified, and hence not correspond as closely to the original source
code.)</p>

<p>This only works if the @(see origexprs) transform is run early in the
transformation sequence.  When there's no @('VL_ORIG_EXPR') attribute, we just
print @('x') as is.</p>"
  (b* (((when (vl-fast-atom-p x))
        (vl-pp-expr x))
       (atts   (vl-nonatom->atts x))
       (lookup (cdr (hons-assoc-equal "VL_ORIG_EXPR" atts)))
       ((when lookup)
        (vl-pp-expr lookup)))
    (vl-pp-expr x)))

(define vl-pps-origexpr ((x vl-expr-p))
  :returns (pretty-x stringp :rule-classes :type-prescription)
  :parents (expr-tools verilog-printing)
  :short "Pretty-print the \"original,\" un-transformed version of an
expression into a string."
  (with-local-ps (vl-pp-origexpr x)))

(define vl-pp-port ((x vl-port-p) &key (ps 'ps))
  (b* (((vl-port x) x)
       ((when (and (not x.name)
                   (not x.expr)))
        ;; A truly blank port... we'll put in a comment.
        (vl-ps-span "vl_cmt" (vl-println? "/* blank port */")))

       ((unless x.name)
        ;; Just a complex expression like foo[3:0] with no name.
        (vl-pp-expr x.expr))

       ((when (and x.expr
                   (vl-fast-atom-p x.expr)
                   (vl-fast-id-p (vl-atom->guts x.expr))
                   (equal (vl-id->name (vl-atom->guts x.expr)) x.name)))
        ;; Ordinary case, internal expression is just the same as the
        ;; externally visible name.
        (vl-print-wirename x.name)))

    ;; .name(expr) or .name()
    (vl-ps-seq (vl-print ".")
               (vl-ps-span "vl_id"
                           (vl-print-str (vl-maybe-escape-identifier x.name)))
               (vl-print "(")
               (if x.expr
                   (vl-pp-expr x.expr)
                 ps)
               (vl-print ")"))))

(define vl-pp-portlist ((x vl-portlist-p) &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-pp-port (car x)))
        (t
         (vl-ps-seq (vl-pp-port (car x))
                    (vl-println? ", ")
                    (vl-pp-portlist (cdr x))))))


(define vl-netdecltype-string ((x vl-netdecltype-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-netdecltype-p)))
  (case (vl-netdecltype-fix x)
    (:vl-wire    "wire")
    (:vl-supply0 "supply0")
    (:vl-supply1 "supply1")
    (:vl-tri     "tri")
    (:vl-triand  "triand")
    (:vl-trior   "trior")
    (:vl-tri0    "tri0")
    (:vl-tri1    "tri1")
    (:vl-trireg  "trireg")
    (:vl-uwire   "uwire")
    (:vl-wand    "wand")
    (:vl-wor     "wor")
    (otherwise   (or (impossible) ""))))

(define vl-direction-string ((x vl-direction-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-direction-p)))
  (case (vl-direction-fix x)
    (:vl-input  "input")
    (:vl-output "output")
    (:vl-inout  "inout")
    (otherwise  (or (impossible) ""))))

(define vl-pp-range ((x vl-range-p) &key (ps 'ps))
  (b* (((vl-range x) x))
    (vl-ps-seq (vl-print "[")
               (vl-pp-expr x.msb)
               (vl-println? ":")
               (vl-pp-expr x.lsb)
               (vl-print "]"))))

(define vl-pps-range ((x vl-range-p))
  :returns (str stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-range x)))

(define vl-pp-rangelist ((x vl-rangelist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-range (car x))
               (vl-pp-rangelist (cdr x)))))




(define vl-randomqualifier-string ((x vl-randomqualifier-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints(("Goal" :in-theory (enable vl-randomqualifier-p)))
  (case (vl-randomqualifier-fix x)
    ('nil         "")
    (:vl-rand     "rand")
    (:vl-randc    "randc")
    (otherwise    (or (impossible) ""))))

(define vl-coretypename-string ((x vl-coretypename-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints(("Goal" :in-theory (enable vl-coretypename-p)))
  (case (vl-coretypename-fix x)
    (:vl-void      "void")
    (:vl-byte      "byte")
    (:vl-shortint  "shortint")
    (:vl-int       "int")
    (:vl-longint   "longint")
    (:vl-integer   "integer")
    (:vl-time      "time")
    (:vl-bit       "bit")
    (:vl-logic     "logic")
    (:vl-reg       "reg")
    (:vl-shortreal "shortreal")
    (:vl-real      "real")
    (:vl-realtime  "realtime")
    (:vl-string    "string")
    (:vl-chandle   "chandle")
    (:vl-event     "event")
    (otherwise     (or (impossible) ""))))

(define vl-pp-packeddimension ((x vl-packeddimension-p) &key (ps 'ps))
  (b* ((x (vl-packeddimension-fix x)))
    (if (eq x :vl-unsized-dimension)
        (vl-print "[]")
      (vl-pp-range x))))

(define vl-pp-packeddimensionlist ((x vl-packeddimensionlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-packeddimension (car x))
               (vl-pp-packeddimensionlist (cdr x)))))

(define vl-pp-enumbasekind ((x vl-enumbasekind-p) &key (ps 'ps))
  :guard-hints(("Goal" :in-theory (enable vl-enumbasekind-p)))
  (b* ((x (vl-enumbasekind-fix x))
       ((when (stringp x))
        (vl-print-modname x)))
    (vl-ps-span "vl_key" (vl-print-str (case x
                                         (:vl-byte     "byte")
                                         (:vl-shortint "shortint")
                                         (:vl-int      "int")
                                         (:vl-longint  "longint")
                                         (:vl-integer  "integer")
                                         (:vl-time     "time")
                                         (:vl-bit      "bit")
                                         (:vl-logic    "logic")
                                         (:vl-reg      "reg"))))))

(define vl-pp-enumbasetype ((x vl-enumbasetype-p) &key (ps 'ps))
  (b* (((vl-enumbasetype x) x))
    (vl-ps-seq (vl-pp-enumbasekind x.kind)
               ;; BOZO this isn't quite right, should only print signedness if it's
               ;; not the default for this type
               (vl-ps-span "vl_key" (vl-print (if x.signedp " signed" " unsigned")))
               (if x.dim
                   (vl-ps-seq (vl-print " ")
                              (vl-pp-packeddimension x.dim))
                 ps))))

(define vl-pp-enumitem ((x vl-enumitem-p) &key (ps 'ps))
  (b* (((vl-enumitem x) x))
    (vl-ps-seq (vl-indent 4)
               (vl-print-wirename x.name)
               (if x.range
                   ;; Special case to print [5:5] style ranges as just [5]
                   (b* ((msb (vl-range->msb x.range))
                        (lsb (vl-range->lsb x.range))
                        ((when (and (vl-expr-resolved-p msb)
                                    (vl-expr-resolved-p lsb)
                                    (equal (vl-resolved->val msb)
                                           (vl-resolved->val lsb))))
                         (vl-ps-seq (vl-print-str "[")
                                    (vl-print-nat (vl-resolved->val msb))
                                    (vl-print-str "]"))))
                     ;; Otherwise just print a normal range
                     (vl-pp-range x.range))
                 ps)
               (if x.value
                   (vl-ps-seq (vl-print " = ")
                              (vl-pp-expr x.value))
                 ps)
               (vl-println " ;"))))

(define vl-pp-enumitemlist ((x vl-enumitemlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-enumitem (car x))
               (vl-pp-enumitemlist (cdr x)))))

(defines vl-pp-datatype

  (define vl-pp-datatype ((x vl-datatype-p) &key (ps 'ps))
    :measure (vl-datatype-count x)
    (vl-datatype-case x
      (:vl-coretype
       (vl-ps-seq (vl-indent 2)
                  (vl-ps-span "vl_key" (vl-print-str (vl-coretypename-string x.name)))
                  ;; BOZO this isn't quite right -- we shouldn't print the
                  ;; signedness if it's not applicable to this kind of type.
                  (vl-print " ")
                  ;; signing, if applicable
                  (cond ((and (member x.name '(:vl-byte :vl-shortint :vl-int :vl-longint :vl-integer))
                              (not x.signedp))
                         ;; default signed, but this one is unsigned
                         (vl-ps-span "vl_key" (vl-print-str "unsigned")))
                        ((and (member x.name '(:vl-time :vl-bit :vl-logic :vl-reg))
                              x.signedp)
                         ;; default unsigned, but this one is signed
                         (vl-ps-span "vl_key" (vl-print-str "signed")))
                        (t
                         ;; other core types don't have an optional signing.  they'd better
                         ;; be marked as unsigned or it doesn't make sense
                         (progn$ (or (not x.signedp)
                                     (raise "core type ~x0 marked as signed? ~x1" x.name x))
                                 ps)))
                  (vl-print " ")
                  (vl-pp-packeddimensionlist x.dims)))

      (:vl-struct
       (vl-ps-seq (vl-indent 2)
                  (vl-ps-span "vl_key"
                              (vl-print "struct ")
                              (if x.packedp
                                  (vl-ps-seq (vl-print "packed ")
                                             (if x.signedp
                                                 (vl-print "signed ")
                                               ps))
                                ps))
                  (vl-println "{")
                  (vl-pp-structmemberlist x.members)
                  (vl-print "} ")
                  (vl-pp-packeddimensionlist x.dims)))

      (:vl-union
       (vl-ps-seq (vl-indent 2)
                  (vl-ps-span "vl_key"
                              (vl-print "union ")
                              (if x.taggedp
                                  (vl-print "tagged ")
                                ps)
                              (if x.packedp
                                  (vl-ps-seq (vl-print "packed ")
                                             (if x.signedp
                                                 (vl-print "signed ")
                                               ps))
                                ps))
                  (vl-println "{")
                  (vl-pp-structmemberlist x.members)
                  (vl-indent 2)
                  (vl-print "} ")
                  (vl-pp-packeddimensionlist x.dims)))

      (:vl-enum
       (vl-ps-seq (vl-indent 2)
                  (vl-ps-span "vl_key" (vl-print "enum "))
                  (vl-pp-enumbasetype x.basetype)
                  (vl-println " {")
                  (vl-pp-enumitemlist x.items)
                  (vl-indent 2)
                  (vl-println "} ")
                  (vl-pp-packeddimensionlist x.dims)))

      (:vl-usertype
       (vl-ps-seq (vl-pp-expr x.kind)
                  (vl-print " ")
                  (vl-pp-packeddimensionlist x.dims)))))

  (define vl-pp-structmemberlist ((x vl-structmemberlist-p) &key (ps 'ps))
    :measure (vl-structmemberlist-count x)
    (if (atom x)
        ps
      (vl-ps-seq (vl-pp-structmember (car x))
                 (vl-pp-structmemberlist (cdr x)))))

  (define vl-pp-structmember ((x vl-structmember-p) &key (ps 'ps))
    :measure (vl-structmember-count x)
    (b* (((vl-structmember x) x))
      (vl-ps-seq (vl-indent 4)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (if x.rand
                     (vl-ps-span "vl_key"
                                 (vl-print-str (vl-randomqualifier-string x.rand))
                                 (vl-print " "))
                   ps)
                 (vl-pp-datatype x.type)
                 (vl-print " ")
                 (vl-print-wirename x.name)
                 (vl-print " ")
                 (vl-pp-packeddimensionlist x.dims)
                 (if x.rhs
                     (vl-ps-seq (vl-print " = ")
                                (vl-pp-expr x.rhs))
                   ps)
                 (vl-println " ;")))))


(define vl-pp-portdecl ((x vl-portdecl-p) &key (ps 'ps))
  (b* (((vl-portdecl x) x))
    (vl-ps-seq (vl-print "  ")
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key"
                           (vl-println? (vl-direction-string x.dir))
                           (if (not x.signedp)
                               ps
                             (vl-println? " signed")))
               (if (not x.range)
                   ps
                 (vl-ps-seq (vl-print " ")
                            (vl-pp-range x.range)))
               (vl-println? " ")
               (vl-print-wirename x.name)
               (vl-println " ;"))))

(define vl-pp-portdecllist ((x vl-portdecllist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-portdecl (car x))
               (vl-pp-portdecllist (cdr x)))))


(define vl-lifetime-string ((x vl-lifetime-p))
  (case (vl-lifetime-fix x)
    ('nil          "")
    (:vl-static    "static")
    (:vl-automatic "automatic")
    (otherwise (progn$ (impossible) ""))))

(define vl-pp-vardecl ((x vl-vardecl-p) &key (ps 'ps))
  (b* (((vl-vardecl x) x))
    (vl-ps-seq
     (vl-print "  ")
     (if x.atts
         (vl-ps-seq (vl-pp-atts x.atts)
                    (vl-print " "))
       ps)
     (if x.constp
         (vl-ps-span "vl_key" (vl-print "const "))
       ps)
     (if x.varp
         (vl-ps-span "vl_key" (vl-print "var "))
       ps)
     (if x.lifetime
         (vl-ps-span "vl_key"
                     (vl-ps-seq (vl-print-str (vl-lifetime-string x.lifetime))
                                (vl-println? " ")))
       ps)
     (vl-pp-datatype x.vartype)
     (vl-print " ")
     (vl-print-wirename x.name)
     (if x.dims
         (vl-pp-packeddimensionlist x.dims)
       ps)
     (if x.initval
         (vl-ps-seq (vl-print " = ")
                    (vl-pp-expr x.initval))
       ps)
     (vl-println " ;"))))

(define vl-pp-vardecllist ((x vl-vardecllist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-vardecl (car x))
               (vl-pp-vardecllist (cdr x)))))

(define vl-pp-eventdecl ((x vl-eventdecl-p) &key (ps 'ps))
  (b* (((vl-eventdecl x) x))
    (vl-ps-seq
     (if x.atts (vl-pp-atts x.atts) ps)
     (vl-ps-span "vl_key" (vl-print "  event "))
     (vl-print-wirename x.name)
     (if x.arrdims
         (vl-pp-rangelist x.arrdims)
       ps)
     (vl-println " ;"))))

(define vl-pp-eventdecllist ((x vl-eventdecllist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-eventdecl (car x))
               (vl-pp-eventdecllist (cdr x)))))

(define vl-pp-paramdecl ((x vl-paramdecl-p) &key (ps 'ps))
  (b* (((vl-paramdecl x) x))
    (vl-ps-seq (vl-print "  ")
               (if x.atts
                   (vl-ps-seq (vl-pp-atts x.atts)
                              (vl-print " "))
                 ps)
               (vl-ps-span "vl_key"
                           (if x.localp
                               (vl-print "localparam ")
                             (vl-print "parameter "))
                           (case x.type
                             (:vl-signed (vl-print "signed "))
                             (:vl-integer (vl-print "integer "))
                             (:vl-real (vl-print "real "))
                             (:vl-time (vl-print "time "))
                             (:vl-realtime (vl-print "realtime "))
                             (otherwise ps)))
               (if x.range
                   (vl-ps-seq (vl-pp-range x.range)
                              (vl-print " "))
                 ps)
               (vl-print-wirename x.name)
               (vl-print " = ")
               (vl-pp-expr x.expr)
               (vl-println ";"))))

(define vl-pp-paramdecllist ((x vl-paramdecllist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-paramdecl (car x))
               (vl-pp-paramdecllist (cdr x)))))

(define vl-pp-blockitem ((x vl-blockitem-p) &key (ps 'ps))
  (b* ((x (vl-blockitem-fix x)))
    (case (tag x)
      (:vl-vardecl   (vl-pp-vardecl x))
      (:vl-eventdecl (vl-pp-eventdecl x))
      (:vl-paramdecl (vl-pp-paramdecl x))
      (otherwise     (progn$ (impossible) ps)))))

(define vl-pp-blockitemlist ((x vl-blockitemlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-blockitem (car x))
               (vl-pp-blockitemlist (cdr x)))))



(define vl-pp-gatedelay ((x vl-gatedelay-p) &key (ps 'ps))
  (b* (((vl-gatedelay x) x))
    (cond
     ((and (hide (equal x.rise x.fall))
           (hide (equal x.fall x.high))
           (vl-fast-atom-p x.rise)
           (vl-constint-p (vl-atom->guts x.rise)))
      ;; Almost always the delays should just be #3, etc.
      (vl-ps-seq
       (vl-print "#")
       (vl-ps-span "vl_int"
                   (vl-print-nat (vl-constint->value (vl-atom->guts x.rise))))))

     ((and (hide (equal x.rise x.fall))
           (hide (equal x.fall x.high)))
      ;; Print #(a,a,a) just as #(a)
      (vl-ps-seq
       (vl-print "#(")
       (vl-pp-expr x.rise)
       (vl-print ")")))

     (x.high
      ;; All three specified, and not equal...
      (vl-ps-seq (vl-print "#(")
                 (vl-pp-expr x.rise)
                 (vl-println? ", ")
                 (vl-pp-expr x.fall)
                 (vl-println? ", ")
                 (vl-pp-expr x.high)
                 (vl-println? ")")))

     (t
      (vl-ps-seq (vl-print "#(")
                 (vl-pp-expr x.rise)
                 (vl-println? ", ")
                 (vl-pp-expr x.fall)
                 (vl-println? ")"))))))

(define vl-pp-gatestrength ((x vl-gatestrength-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-gatestrength-p
                                           vl-dstrength-p
                                           vl-gatestrength->zero
                                           vl-gatestrength->one)))
  (b* (((vl-gatestrength x) x))
    (vl-ps-seq
     (vl-print "(")
     (vl-ps-span "vl_key"
                 (vl-print-str (case x.zero
                                 (:vl-supply "supply0")
                                 (:vl-strong "strong0")
                                 (:vl-pull   "pull0")
                                 (:vl-weak   "weak0")
                                 (:vl-highz  "highz0"))))
     (vl-print ", ")
     (vl-ps-span "vl_key"
                 (vl-print-str (case x.one
                                 (:vl-supply "supply1")
                                 (:vl-strong "strong1")
                                 (:vl-pull   "pull1")
                                 (:vl-weak   "weak1")
                                 (:vl-highz  "highz1"))))
     (vl-println? ")"))))

(define vl-pp-assign ((x vl-assign-p) &key (ps 'ps))
  (b* (((vl-assign x) x))
    (vl-ps-seq
     (if x.atts
         (vl-ps-seq (vl-println "")
                    (vl-pp-atts x.atts)
                    (vl-println ""))
       ps)
     (vl-ps-span "vl_key" (vl-print "  assign "))
     (if (not x.strength)
         ps
       (vl-ps-seq (vl-pp-gatestrength x.strength)
                  (vl-print " ")))
     (if (not x.delay)
         ps
       (vl-ps-seq (vl-pp-gatedelay x.delay)
                  (vl-print " ")))
     (vl-pp-expr x.lvalue)
     (vl-println? " = ")
     (vl-pp-expr x.expr)
     (vl-println " ;"))))

(define vl-pp-assignlist ((x vl-assignlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-assign (car x))
               (vl-pp-assignlist (cdr x)))))

(define vl-cstrength-string ((x vl-cstrength-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-cstrength-p)))
  (case (vl-cstrength-fix x)
    (:vl-large  "large")
    (:vl-medium "medium")
    (:vl-small  "small")
    (otherwise  (or (impossible) ""))))

(defmacro vl-pp-netdecl-special-atts ()
  ''("VL_IMPLICIT"
     "VL_PORT_IMPLICIT"
     "VL_UNUSED"
     "VL_MAYBE_UNUSED"
     "VL_UNSET"
     "VL_MAYBE_UNSET"
     "VL_DESIGN_WIRE"))

(define vl-pp-netdecl-atts-begin ((x vl-atts-p) &key (ps 'ps))
  :measure (vl-atts-count x)
  (b* ((x (vl-atts-fix x))
       ((unless x)
        ps)
       (x (vl-remove-keys (vl-pp-netdecl-special-atts) x))
       ((unless x)
        ps)
       ((when (and (tuplep 1 x)
                   (equal (caar x) "VL_FOR")))
        (if (not (and (cdar x)
                      (vl-atom-p (cdar x))
                      (vl-string-p (vl-atom->guts (cdar x)))))
            (prog2$
             (raise "Expected FROM to contain a string.")
             ps)
          (vl-ps-seq
           (vl-println "")
           (vl-ps-span "vl_cmt"
                       (vl-print "/* For ")
                       (vl-print-str (vl-string->value (vl-atom->guts (cdar x))))
                       (vl-println " */"))))))
    (vl-ps-seq (vl-println "")
               (vl-pp-atts x)
               (vl-println ""))))

(define vl-pp-strings-separated-by-commas ((x string-listp) &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-print-str (car x)))
        (t
         (vl-ps-seq
          (vl-print-str (car x))
          (vl-print ", ")
          (vl-pp-strings-separated-by-commas (cdr x))))))

(define vl-pp-netdecl-atts-end ((x vl-atts-p) &key (ps 'ps))
  (b* ((x (vl-atts-fix x))
       ((unless x)
        (vl-println ""))
       (cars    (strip-cars x))
       (notes   nil)
       (notes   (if (member-equal "VL_IMPLICIT" cars)
                    (cons "Implicit" notes)
                  notes))
       (notes   (if (member-equal "VL_PORT_IMPLICIT" cars)
                    (cons "Port implicit" notes)
                  notes))
       (notes   (cond ((member-equal "VL_UNUSED" cars)
                       (cons "Unused" notes))
                      ((member-equal "VL_MAYBE_UNUSED" cars)
                       (cons "Unused?" notes))
                      (t notes)))
       (notes   (cond ((member-equal "VL_UNSET" cars)
                       (cons "Unset" notes))
                      ((member-equal "VL_MAYBE_UNSET" cars)
                       (cons "Unset?" notes))
                      (t notes)))
       ((unless notes)
        (vl-println "")))
    (vl-ps-span "vl_cmt"
                (vl-indent 30)
                (vl-print "// ")
                (vl-pp-strings-separated-by-commas notes)
                (vl-println ""))))

(define vl-pp-netdecl ((x vl-netdecl-p) &key (ps 'ps))
  (b* (((vl-netdecl x) x))
    (vl-ps-seq
     (if (not x.atts)
         ps
       (vl-pp-netdecl-atts-begin x.atts))
     (vl-print "  ")
     (vl-ps-span "vl_key"
                 (vl-print-str (vl-netdecltype-string x.type))
                 (if (not x.cstrength)
                     ps
                   (vl-ps-seq (vl-print " ")
                              (vl-println? (vl-cstrength-string x.cstrength))))
                 (if (not x.vectoredp)
                     ps
                   (vl-println? " vectored"))
                 (if (not x.scalaredp)
                     ps
                   (vl-println? " scalared"))
                 (if (not x.signedp)
                     ps
                   (vl-println? " signed")))
     (if (not x.range)
         ps
       (vl-ps-seq (vl-print " ")
                  (vl-pp-range x.range)))
     (if (not x.delay)
         ps
       (vl-ps-seq (vl-print " ")
                  (vl-pp-gatedelay x.delay)))
     (vl-print " ")
     (vl-print-wirename x.name)
     (if (not x.arrdims)
         ps
       (vl-ps-seq (vl-print " ")
                  (vl-pp-rangelist x.arrdims)))
     (vl-print " ;")
     (vl-pp-netdecl-atts-end x.atts)
     )))

(define vl-pp-netdecllist ((x vl-netdecllist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-netdecl (car x))
               (vl-pp-netdecllist (cdr x)))))

(define vl-pp-plainarg ((x vl-plainarg-p) &key (ps 'ps))
  (b* (((vl-plainarg x) x)
       (htmlp (vl-ps->htmlp))
       (name-hack-p (if (and htmlp x.portname) t nil))
       ;; ;; Do we want to print a goofy name
       ;; (and htmlp
       ;;      x.portname
       ;;      ;; Exclude .foo(foo)
       ;;      (not (and x.expr
       ;;                (vl-idexpr-p x.expr)
       ;;                (equal (vl-idexpr->name x.expr) x.portname)))
       ;;      ;; Exclude .foo(foo[a:b])
       ;;      (not (and x.expr
       ;;                (not (vl-fast-atom-p x.expr))
       ;;                (eq (vl-nonatom->op x.expr) :vl-partselect-colon)
       ;;                (vl-idexpr-p (first (vl-nonatom->args x.expr)))
       ;;                (equal (vl-idexpr->name (first (vl-nonatom->args x.expr)))
       ;;                       x.portname)))))
       )
    (vl-ps-seq
     (if htmlp
         (vl-print-markup (case x.dir
                            (:vl-input  "<span class=\"vl_input_arg\">")
                            (:vl-output "<span class=\"vl_output_arg\">")
                            (:vl-inout  "<span class=\"vl_inout_arg\">")
                            (otherwise  "<span class=\"vl_unknown_arg\">")))
       ps)
     (if x.atts
         (vl-pp-atts x.atts)
       ps)
     (if name-hack-p
         (vl-ps-seq (vl-print ".")
                    ;; BOZO shouldn't we be calling maybe-escape-identifier?
                    (vl-print-str x.portname)
                    (vl-print "("))
       ps)
     (if x.expr
         (vl-pp-expr x.expr)
       ps)
     (if name-hack-p
         (vl-print ")")
       ps)
     (if htmlp (vl-print-markup "</span>") ps))))

(define vl-pp-plainarglist ((x vl-plainarglist-p) force-newlinesp &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-pp-plainarg (car x)))
        (t
         (vl-ps-seq (vl-pp-plainarg (car x))
                    (if force-newlinesp
                        (vl-ps-seq (vl-println ",")
                                   (vl-indent (vl-ps->autowrap-ind)))
                      (vl-println? ", "))
                    (vl-pp-plainarglist (cdr x) force-newlinesp)))))

(define vl-pp-namedarg ((x vl-namedarg-p) &key (ps 'ps))
  (let ((name (vl-namedarg->name x))
        (expr (vl-namedarg->expr x))
        (atts (vl-namedarg->atts x)))
    (vl-ps-seq (if atts (vl-pp-atts atts) ps)
               (vl-print ".")
               (vl-ps-span "vl_id"
                           (vl-print (vl-maybe-escape-identifier name)))
               (vl-print "(")
               (if expr
                   (vl-pp-expr expr)
                 ps)
               (vl-print ")"))))

(define vl-pp-namedarglist ((x vl-namedarglist-p) force-newlinesp &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-pp-namedarg (car x)))
        (t
         (vl-ps-seq (vl-pp-namedarg (car x))
                    (if force-newlinesp
                        (vl-ps-seq (vl-println ",")
                                   (vl-indent (vl-ps->autowrap-ind)))
                      (vl-println? ", "))
                    (vl-pp-namedarglist (cdr x) force-newlinesp)))))

(define vl-pp-arguments ((x vl-arguments-p) &key (ps 'ps))
  (b* ((namedp         (eq (vl-arguments-kind x) :named))
       (args           (vl-arguments-case x
                         :named (vl-arguments-named->args x)
                         :plain (vl-arguments-plain->args x)))
       (force-newlinep (longer-than-p 5 args))
       ((when namedp)
        (vl-pp-namedarglist args force-newlinep))
       ((when (and (consp args)
                   (not (consp (cdr args)))
                   (not (vl-plainarg->expr (car args)))))
        ;; Horrible corner case!  Positional arg list with just one
        ;; argument and a blank actual.  No way to print this.  If
        ;; possible we'll trust the portname and try to turn it into a
        ;; named argument list.
        (if (vl-plainarg->portname (car args))
            (b* ((namedarg (make-vl-namedarg :name (vl-plainarg->portname (car args))
                                             :expr nil
                                             :atts (vl-plainarg->atts (car args)))))
              (cw "; Warning: horrible corner case in vl-pp-arguments, ~
                   printing named.~%")
              (vl-pp-namedarglist (list namedarg) force-newlinep))
          ;; We don't even have a name.  How did this happen?
          (progn$
           (raise "Congrats!  You have reached a remarkably obscure corner ~
                   case.  You are trying to print a plain argument list, of ~
                   length 1, which contains a \"blank\" entry.  But there is ~
                   actually no way to express this in Verilog.  See ~
                   cbooks/vl/blank.v for a basic summary of the problem. ~
                   There are some ways we can work around this: (1) convert ~
                   into a named argument list, or (2) eliminating the blank ~
                   by, for outputs, adding a wire name of the appropriate ~
                   width; for inputs, convert into n'bz where n is the ~
                   appropriate width.  But there isn't enough information in ~
                   vl-pp-arguments to carry out this transformation.  At any ~
                   rate, we give up.  Well done!")
           ps))))
    (vl-pp-plainarglist args force-newlinep)))

(define vl-pp-modinst-atts-begin ((x vl-atts-p) &key (ps 'ps))
  (b* ((x (vl-atts-fix x))
       ((unless x)
        ps)
       ((when (and (tuplep 1 x)
                   (equal (caar x) "VL_FOR")))
        (if (not (and (cdar x)
                      (vl-atom-p (cdar x))
                      (vl-string-p (vl-atom->guts (cdar x)))))
            (prog2$
             (raise "Expected VL_FOR to contain a string.")
             ps)
          (vl-ps-span "vl_cmt"
                      (vl-println "")
                      (vl-print "/* For ")
                      (vl-print-str (vl-string->value (vl-atom->guts (cdar x))))
                      (vl-println " */")))))
    (vl-ps-seq (vl-println "")
               (vl-pp-atts x)
               (vl-println ""))))

(define vl-pp-modulename-link-aux ((name stringp) (origname stringp) &key (ps 'ps))
  (b* ((name     (string-fix name))
       (origname (string-fix origname)))
    (vl-ps-seq
     (vl-print-modname origname)
     (vl-print-markup "<a class=\"vl_trans\" href=\"javascript:showTranslatedModule('")
     (vl-print-url origname)
     (vl-print-markup "', '")
     (vl-print-url name)
     (vl-print-markup "')\">")
     ;; Now, what part gets linked to the translation?  If the names agree,
     ;; we just add a lone $.  Otherwise, we add the remaining part of the
     ;; name.
     (b* ((nl  (length name))
          (onl (length origname))
          ((when (equal origname name))
           (vl-print "$"))
          ((when (and (<= onl nl)
                      (equal origname (subseq name 0 onl))))
           (vl-print-str (subseq name onl nl))))
       (prog2$ (raise "Naming convention violated: name = ~s0, origname = ~s1.~%"
                      name origname)
               ps))
     (vl-print-markup "</a>"))))

(define vl-pp-modulename-link ((name stringp)
                               (mods vl-modulelist-p)
                               (modalist (equal modalist (vl-modalist mods)))
                               &key (ps 'ps))
  ;; Assumes HTML mode.
  (b* ((name       (string-fix name))
       (target-mod (vl-fast-find-module name mods modalist))
       ((unless target-mod)
        ;; I sometimes hit this case when pretty-printing the source for modules
        ;; that were thrown away.
        (prog2$ (cw "Warning: linking to module ~s0, which isn't in the modalist.~%"
                    name)
                (vl-print-modname name)))
       (origname (vl-module->origname target-mod)))
    (vl-pp-modulename-link-aux name origname)))

(define vl-pp-modinst ((x        vl-modinst-p)
                       (mods     vl-modulelist-p)
                       (modalist (equal modalist (vl-modalist mods)))
                       &key (ps 'ps))
  (b* (((vl-modinst x) x)
       (paramargs (vl-arguments-case x.paramargs
                    :named x.paramargs.args
                    :plain x.paramargs.args)))
    (if (or x.str x.delay)
        (prog2$ (cw "; Note: in vl-pp-modinst, dropping str/delay from ~x0 instance.~%"
                    x.modname)
                ps)
      (vl-ps-seq (vl-println "")
                 (if x.atts
                     (vl-pp-modinst-atts-begin x.atts)
                   ps)
                 (vl-print "  ")
                 (if (vl-ps->htmlp)
                     (vl-pp-modulename-link x.modname mods modalist)
                   (vl-print-modname x.modname))
                 (if (not paramargs)
                     ps
                   (vl-ps-seq (vl-print " #(")
                              (vl-pp-arguments x.paramargs)
                              (vl-println? ")")))
                 (vl-print " ")
                 (if x.instname
                     ;; BOZO maybe a different function for instance/gate names?
                     (vl-print-wirename x.instname)
                   (prog2$ (cw "Warning: instance of ~x0 has no instname.~%"
                               x.modname)
                           ps))
                 (if (not x.range)
                     ps
                   (vl-ps-seq (vl-print " ")
                              (vl-pp-range x.range)))
                 (vl-print " (")
                 (vl-pp-arguments x.portargs)
                 (vl-println ") ;")))))

(define vl-pp-modinstlist ((x        vl-modinstlist-p)
                           (mods     vl-modulelist-p)
                           (modalist (equal modalist (vl-modalist mods)))
                           &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-modinst (car x) mods modalist)
               (vl-pp-modinstlist (cdr x) mods modalist))))

(define vl-gatetype-string ((x vl-gatetype-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-gatetype-p)))
  (case (vl-gatetype-fix x)
    (:vl-cmos     "cmos")
    (:vl-rcmos    "rcmos")
    (:vl-bufif0   "bufif0")
    (:vl-bufif1   "bufif1")
    (:vl-notif0   "notif0")
    (:vl-notif1   "notif1")
    (:vl-nmos     "nmos")
    (:vl-pmos     "pmos")
    (:vl-rnmos    "rnmos")
    (:vl-rpmos    "rpmos")
    (:vl-and      "and")
    (:vl-nand     "nand")
    (:vl-or       "or")
    (:vl-nor      "nor")
    (:vl-xor      "xor")
    (:vl-xnor     "xnor")
    (:vl-buf      "buf")
    (:vl-not      "not")
    (:vl-tranif0  "tranif0")
    (:vl-tranif1  "tranif1")
    (:vl-rtranif1 "rtranif1")
    (:vl-rtranif0 "rtranif0")
    (:vl-tran     "tran")
    (:vl-rtran    "rtran")
    (:vl-pulldown "pulldown")
    (:vl-pullup   "pullup")
    (otherwise    (or (impossible) ""))))

(define vl-pp-gateinst-atts-begin ((x vl-atts-p) &key (ps 'ps))
  (b* ((x (vl-atts-fix x))
       ((unless x)
        ps)
       ((when (and (tuplep 1 x)
                   (equal (caar x) "VL_FOR")))
        (if (not (and (cdar x)
                      (vl-atom-p (cdar x))
                      (vl-string-p (vl-atom->guts (cdar x)))))
            (prog2$
             (raise "Expected VL_FOR to contain a string.")
             ps)
          (vl-ps-span "vl_cmt"
                      (vl-println "")
                      (vl-print "/* For ")
                      (vl-print-str (vl-string->value (vl-atom->guts (cdar x))))
                      (vl-println " */")))))
    (vl-ps-seq (vl-println "")
               (vl-pp-atts x)
               (vl-println ""))))

(define vl-pp-gateinst ((x vl-gateinst-p) &key (ps 'ps))
  (b* (((vl-gateinst x) x))
    (vl-ps-seq (if x.atts
                   (vl-pp-gateinst-atts-begin x.atts)
                 ps)
               (vl-print "  ")
               (vl-ps-span "vl_key" (vl-print-str (vl-gatetype-string x.type)))
               (if (not x.strength)
                   ps
                 (vl-ps-seq (vl-print " ")
                            (vl-pp-gatestrength x.strength)))
               (if (not x.delay)
                   ps
                 (vl-ps-seq (vl-print " ")
                            (vl-pp-gatedelay x.delay)))
               (if (not x.name)
                   ps
                 (vl-ps-seq (vl-print " ")
                            ;; BOZO maybe a different function than wirename?
                            (vl-print-wirename x.name)
                            (vl-println? "")))
               (if (not x.range)
                   ps
                 (vl-pp-range x.range))
               (vl-print " (")
               (vl-pp-plainarglist x.args nil)
               (vl-println ") ;"))))

(define vl-pp-gateinstlist ((x vl-gateinstlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-gateinst (car x))
               (vl-pp-gateinstlist (cdr x)))))

(define vl-pp-delaycontrol ((x vl-delaycontrol-p) &key (ps 'ps))
  (let ((value (vl-delaycontrol->value x)))
    (if (and (vl-fast-atom-p value)
             (vl-fast-constint-p (vl-atom->guts value)))
        (vl-ps-seq
         (vl-print "#")
         (vl-ps-span "vl_int"
                     (vl-println? (vl-constint->value (vl-atom->guts value)))))
      (vl-ps-seq
       (vl-print "#(")
       (vl-pp-expr value)
       (vl-println? ")")))))

(define vl-pp-evatom ((x vl-evatom-p) &key (ps 'ps))
  (let ((type (vl-evatom->type x))
        (expr (vl-evatom->expr x)))
    (if (eq type :vl-noedge)
        (vl-pp-expr expr)
      (vl-ps-seq (vl-ps-span "vl_key"
                             (if (eq type :vl-posedge)
                                 (vl-print "posedge ")
                               (vl-print "negedge ")))
                 (vl-pp-expr expr)))))

(define vl-pp-evatomlist ((x vl-evatomlist-p) &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-pp-evatom (car x)))
        (t
         (vl-ps-seq (vl-pp-evatom (car x))
                    (vl-ps-span "vl_key" (vl-print " or "))
                    (vl-pp-evatomlist (cdr x))))))

(define vl-pp-eventcontrol ((x vl-eventcontrol-p) &key (ps 'ps))
  (let ((starp (vl-eventcontrol->starp x))
        (atoms (vl-eventcontrol->atoms x)))
    (if starp
        (vl-print "@*")
      (vl-ps-seq (vl-print "@(")
                 (vl-pp-evatomlist atoms)
                 (vl-println? ")")))))

(define vl-pp-repeateventcontrol ((x vl-repeateventcontrol-p) &key (ps 'ps))
  (let ((expr (vl-repeateventcontrol->expr x))
        (ctrl (vl-repeateventcontrol->ctrl x)))
    (vl-ps-seq (vl-ps-span "vl_key" (vl-print "repeat "))
               (vl-print "(")
               (vl-pp-expr expr)
               (vl-print ")")
               (vl-pp-eventcontrol ctrl))))

(define vl-pp-delayoreventcontrol ((x vl-delayoreventcontrol-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-delayoreventcontrol-p)))
  (b* ((x (vl-delayoreventcontrol-fix x)))
    (case (tag x)
      (:vl-delaycontrol (vl-pp-delaycontrol x))
      (:vl-eventcontrol (vl-pp-eventcontrol x))
      (otherwise        (vl-pp-repeateventcontrol x)))))



; Statement printing.  I want to do at least something to allow nested
; statements to get progressively more indented.  As a very basic way to
; implement this, I piggy-back on the autowrap column and autowrap indent
; fields of the printer state.
;
; Ordinarily autowrap-col is around 80 and autowrap-ind is around 5.  The
; autowrap-ind normally doesn't matter except for what happens when lines get
; wrapped.  We'll have statements start at autowrap-ind - 2.
;
; Convention: every statement starts by automatically indenting itself, and
; every statement prints a newline at the end!

(define vl-pp-stmt-autoindent (&key (ps 'ps))
  (vl-indent (nfix (- (vl-ps->autowrap-ind) 2))))

(defmacro vl-pp-stmt-indented (&rest args)
  `(let* ((_pp_stmt_autowrap_ind_ (vl-ps->autowrap-ind))
          (_pp_stmt_autowrap_col_ (vl-ps->autowrap-col))
          (ps (vl-ps-update-autowrap-col (+ 2 _pp_stmt_autowrap_col_)))
          (ps (vl-ps-update-autowrap-ind (+ 2 _pp_stmt_autowrap_ind_)))
          (ps (vl-ps-seq . ,args))
          (ps (vl-ps-update-autowrap-col _pp_stmt_autowrap_col_))
          (ps (vl-ps-update-autowrap-ind _pp_stmt_autowrap_ind_)))
     ps))

(define vl-pp-blockitemlist-indented ((x vl-blockitemlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq
     (vl-pp-stmt-indented (vl-pp-blockitem (car x)))
     (vl-pp-blockitemlist-indented (cdr x)))))

(define vl-casetype-string ((x vl-casetype-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-casetype-p)))
  (case (vl-casetype-fix x)
    ('nil         "case")
    (:vl-casex    "casex")
    (:vl-casez    "casez")
    (otherwise    (or (impossible) ""))))


(defines vl-pp-stmt

  (define vl-pp-stmt ((x vl-stmt-p) &key (ps 'ps))
    :measure (vl-stmt-count x)
    (vl-stmt-case x
      :vl-nullstmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-println " ;"))

      :vl-assignstmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key"
                             (case x.type
                               (:vl-assign (vl-println? "assign "))
                               (:vl-force  (vl-println? "force "))
                               (otherwise  ps)))
                 (vl-pp-expr x.lvalue)
                 (case x.type
                   (:vl-nonblocking (vl-println? " <= "))
                   (otherwise       (vl-println? " = ")))
                 (if x.ctrl
                     (vl-ps-seq (vl-pp-delayoreventcontrol x.ctrl)
                                (vl-println? " "))
                   ps)
                 (vl-pp-expr x.expr)
                 (vl-println " ;"))

      :vl-enablestmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-pp-expr x.id)
                 ;; Bug fixed 2012-10-22: if there are no arguments, we must not
                 ;; print even the parens.  (Doing so isn't syntactically legal.)
                 (if (consp x.args)
                     (vl-ps-seq
                      (vl-println? "(")
                      (vl-pp-exprlist x.args)
                      (vl-print ")"))
                   ps)
                 (vl-println " ;"))

      :vl-disablestmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key"
                             (vl-print "disable "))
                 (vl-pp-expr x.id)
                 (vl-println " ;"))

      :vl-deassignstmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key"
                             (case x.type
                               (:vl-deassign (vl-print "deassign "))
                               (:vl-release  (vl-print "release "))
                               (otherwise    (progn$ (impossible) ps))))
                 (vl-pp-expr x.lvalue)
                 (vl-println " ;"))

      :vl-eventtriggerstmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-print "-> ")
                 (vl-pp-expr x.id)
                 (vl-println " ;"))

      :vl-ifstmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "if"))
                 (vl-print " (")
                 (vl-pp-expr x.condition)
                 (vl-println ")")
                 (vl-pp-stmt-indented (vl-pp-stmt x.truebranch))
                 (vl-pp-stmt-autoindent)
                 (vl-ps-span "vl_key" (vl-print "else"))
                 (if (eq (vl-stmt-kind x.falsebranch) :vl-ifstmt)
                     ;; It's very common for if/else if structures to be
                     ;; deeply nested.  In this case we don't want to
                     ;; print the sub-statement with extra indentation,
                     ;; and we want it to occur on the same line.
                     (vl-ps-seq (vl-print " ")
                                (vl-pp-stmt x.falsebranch))
                   ;; A plain "else", not an "else if".  Go ahead and
                   ;; give it a new line and indent its body.
                   (vl-ps-seq (vl-println "")
                              (vl-pp-stmt-indented (vl-pp-stmt x.falsebranch)))))

      :vl-blockstmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key"
                             (vl-print (if x.sequentialp "begin " "fork ")))
                 (if (not x.name)
                     (vl-println "")
                   (vl-ps-seq
                    (vl-print " : ")
                    (vl-ps-span "vl_id"
                                (vl-print-str (vl-maybe-escape-identifier x.name)))
                    (if (not x.decls)
                        (vl-println "")
                      (vl-ps-seq
                       (vl-println "")
                       (vl-pp-blockitemlist-indented x.decls)))))
                 (vl-pp-stmt-indented (vl-pp-stmtlist x.stmts))
                 (vl-pp-stmt-autoindent)
                 (vl-ps-span "vl_key" (vl-print-str (if x.sequentialp "end" "join")))
                 (vl-println ""))

      :vl-forstmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "for "))
                 (vl-print "(")
                 (vl-pp-expr x.initlhs) (vl-print " = ") (vl-pp-expr x.initrhs)
                 (vl-print "; ")
                 (vl-pp-expr x.test)
                 (vl-print "; ")
                 (vl-pp-expr x.nextlhs) (vl-print " = ") (vl-pp-expr x.nextrhs)
                 (vl-println ")")
                 (vl-pp-stmt-indented (vl-pp-stmt x.body))
                 ;; no ending semicolon, the body prints one
                 )

      :vl-timingstmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-pp-delayoreventcontrol x.ctrl)
                 (if (eq (tag x.ctrl) :vl-eventcontrol)
                     ;; Something like @(posedge clk) or @(foo or bar),
                     ;; want to get a newline.
                     (vl-ps-seq (vl-println "")
                                (vl-pp-stmt-indented (vl-pp-stmt x.body)))
                   ;; Something like #5 foo <= bar, try to keep it on the
                   ;; same line.
                   (vl-ps-seq (vl-print " ")
                              (vl-pp-stmt x.body))))

      :vl-foreverstmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-println "forever"))
                 (vl-pp-stmt-indented (vl-pp-stmt x.body))
                 ;; no ending semicolon, the body prints one
                 )

      :vl-repeatstmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "repeat"))
                 (vl-print " (")
                 (vl-pp-expr x.condition)
                 (vl-println ")")
                 (vl-pp-stmt-indented (vl-pp-stmt x.body))
                 ;; no ending semicolon, the body prints one
                 )

      :vl-waitstmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "wait"))
                 (vl-print " (")
                 (vl-pp-expr x.condition)
                 (vl-println ")")
                 (vl-pp-stmt-indented (vl-pp-stmt x.body))
                 ;; no ending semicolon, the body prints one
                 )

      :vl-whilestmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "while"))
                 (vl-print " (")
                 (vl-pp-expr x.condition)
                 (vl-println ")")
                 (vl-pp-stmt-indented (vl-pp-stmt x.body))
                 ;; no ending semicolon, the body prints one
                 )

      :vl-casestmt
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key"
                             (vl-print-str (vl-casetype-string x.casetype)))
                 (vl-print " (")
                 (vl-pp-expr x.test)
                 (vl-println ")")
                 (vl-pp-stmt-indented (vl-pp-cases x.cases))
                 (vl-pp-stmt-autoindent)
                 (vl-ps-span "vl_key" (vl-print "default"))
                 (vl-println " :")
                 (vl-pp-stmt-indented (vl-pp-stmt x.default))
                 (vl-pp-stmt-autoindent)
                 (vl-ps-span "vl_key" (vl-print "endcase"))
                 (vl-println ""))))

  (define vl-pp-stmtlist ((x vl-stmtlist-p) &key (ps 'ps))
    :measure (vl-stmtlist-count x)
    (if (atom x)
        ps
      (vl-ps-seq (vl-pp-stmt (car x))
                 (vl-pp-stmtlist (cdr x)))))

  (define vl-pp-cases ((x vl-caselist-p) &key (ps 'ps))
    :measure (vl-caselist-count x)
    (b* ((x (vl-caselist-fix x))
         ((when (atom x))
          ps)
         ((cons expr stmt) (car x)))
      (vl-ps-seq (vl-pp-stmt-autoindent)
                 (vl-pp-expr expr)
                 (vl-println " :")
                 (vl-pp-stmt-indented (vl-pp-stmt stmt))
                 (vl-pp-cases (cdr x)))))

  ///
  (local (in-theory (disable vl-pp-stmt
                             vl-pp-stmtlist
                             vl-pp-cases)))

  (deffixequiv-mutual vl-pp-stmt
    :hints(("Goal" :expand ((vl-pp-stmt x)
                            (vl-pp-stmt (vl-stmt-fix x))
                            (vl-pp-stmtlist x)
                            (vl-pp-stmtlist (vl-stmtlist-fix x))
                            (vl-pp-stmtlist nil)
                            (vl-pp-cases x)
                            (vl-pp-cases (vl-caselist-fix x))
                            (vl-pp-cases nil))))))

(define vl-pp-always ((x vl-always-p) &key (ps 'ps))
  (b* (((vl-always x) x))
    (vl-ps-seq (vl-print "  ")
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "always "))
               (vl-pp-stmt x.stmt))))

(define vl-pp-alwayslist ((x vl-alwayslist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-always (car x))
               (vl-println "")
               (vl-pp-alwayslist (cdr x)))))

(define vl-pp-initial ((x vl-initial-p) &key (ps 'ps))
  (b* (((vl-initial x) x))
    (vl-ps-seq (vl-print "  ")
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "initial "))
               (vl-pp-stmt x.stmt)
               (vl-println ""))))

(define vl-pp-initiallist ((x vl-initiallist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-initial (car x))
               (vl-println "")
               (vl-pp-initiallist (cdr x)))))


(define vl-taskporttype-string ((x vl-taskporttype-p))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (vl-taskporttype-p)
  :short "@(call vl-taskporttype-string) returns a string describing this
function type, for pretty-printing."
  :long "<p>We just return the empty string for @(':vl-unsigned'), but it seems
like it would be valid to print @('reg').</p>"
  :guard-hints (("Goal" :in-theory (enable vl-taskporttype-p)))
  (case (vl-taskporttype-fix x)
    (:vl-unsigned "")
    (:vl-signed   "signed")
    (:vl-integer  "integer")
    (:vl-real     "real")
    (:vl-realtime "realtime")
    (:vl-time     "time")
    (otherwise    (progn$ (impossible) ""))))

(define vl-pp-taskport ((x vl-taskport-p) &key (ps 'ps))
  (b* (((vl-taskport x) x)
       (typestr (vl-taskporttype-string x.type))
       (dirstr  (vl-direction-string x.dir)))
    (vl-ps-seq (vl-print "  ")
               (if x.atts
                   (vl-ps-seq (vl-pp-atts x.atts)
                              (vl-print " "))
                 ps)
               (vl-ps-span "vl_key"
                           (vl-print-str dirstr)
                           (vl-print " ")
                           (vl-print-str typestr)
                           (if (equal typestr "")
                               ps
                             (vl-print " ")))
               (if x.range
                   (vl-ps-seq (vl-pp-range x.range)
                              (vl-print " "))
                 ps)
               (vl-print-wirename x.name))))

(define vl-pp-taskportlist ((x vl-taskportlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-taskport (car x))
               (vl-println " ;")
               (vl-pp-taskportlist (cdr x)))))

(define vl-pp-fundecl ((x vl-fundecl-p) &key (ps 'ps))
  ;; We print these off using "variant 1" style (see parse-functions)
  (b* (((vl-fundecl x) x)
       (typestr (vl-taskporttype-string x.rtype)))
    (vl-ps-seq (vl-print "  ")
               (if x.atts
                   (vl-ps-seq (vl-pp-atts x.atts)
                              (vl-print " "))
                 ps)
               (vl-ps-span "vl_key"
                           (vl-print "function ")
                           (if x.automaticp
                               (vl-print "automatic ")
                             ps)
                           (vl-print-str typestr)
                           (if (equal typestr "")
                               ps
                             (vl-print " ")))
               (if x.rrange
                   (vl-ps-seq (vl-pp-range x.rrange)
                              (vl-print " "))
                 ps)
               (vl-print-wirename x.name)
               (vl-println ";")
               (vl-pp-taskportlist x.inputs)
               (vl-pp-blockitemlist x.decls)
               (vl-print "  ")
               (vl-pp-stmt x.body)
               (vl-basic-cw "~|") ;; newline only if necessary
               (vl-print "  ")
               (vl-ps-span "vl_key" (vl-print "endfunction"))
               (vl-println ""))))

(define vl-pp-fundecllist ((x vl-fundecllist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-fundecl (car x))
               (vl-println "")
               (vl-pp-fundecllist (cdr x)))))

(define vl-pp-taskdecl ((x vl-taskdecl-p) &key (ps 'ps))
  (b* (((vl-taskdecl x) x))
    (vl-ps-seq (vl-print "  ")
               (if x.atts
                   (vl-ps-seq (vl-pp-atts x.atts)
                              (vl-print " "))
                 ps)
               (vl-ps-span "vl_key"
                           (vl-print "task ")
                           (if x.automaticp
                               (vl-print "automatic ")
                             ps))
               (vl-print-wirename x.name)
               (vl-println ";")
               (vl-pp-taskportlist x.ports)
               (vl-pp-blockitemlist x.decls)
               (vl-print "  ")
               (vl-pp-stmt x.body)
               (vl-basic-cw "~|") ;; newline only if necessary
               (vl-print "  ")
               (vl-ps-span "vl_key" (vl-print "endtask"))
               (vl-println ""))))

(define vl-pp-taskdecllist ((x vl-taskdecllist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-taskdecl (car x))
               (vl-println "")
               (vl-pp-taskdecllist (cdr x)))))

(define vl-pp-module
  ((x    vl-module-p     "Module to pretty-print.")
   (mods vl-modulelist-p "A list of all modules; only used for hyperlinking in
                          HTML mode.")
   (modalist (equal modalist (vl-modalist mods)))
   &key (ps 'ps))
  :parents (verilog-printing)
  :short "Pretty-print a module to @(see ps)."
  :long "<p>You might instead want to use @(see vl-ppc-module), which preserves
the order of module elements and its comments.  For interactive use, you may
want @(see vl-pps-module) or @(see vl-ppcs-module), which write to a string
instead of @(see ps).</p>"
  (b* (((vl-module x) x))
    (vl-ps-seq (vl-pp-set-portnames x.portdecls)
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "module "))
               (if (vl-ps->htmlp)
                   (vl-pp-modulename-link x.name mods modalist)
                 (vl-print-modname x.name))
               (vl-print " (")
               (vl-pp-portlist x.ports)
               (vl-println ");")
               (vl-pp-paramdecllist x.paramdecls)
               (vl-pp-portdecllist x.portdecls)
               (vl-pp-netdecllist x.netdecls)
               (vl-pp-vardecllist x.vardecls)
               (vl-pp-eventdecllist x.eventdecls)
               (vl-pp-fundecllist x.fundecls) ;; put them here, so they can refer to declared wires
               (vl-pp-taskdecllist x.taskdecls)
               (vl-pp-assignlist x.assigns)
               (vl-pp-modinstlist x.modinsts mods modalist)
               (vl-pp-gateinstlist x.gateinsts)
               (vl-pp-alwayslist x.alwayses)
               (vl-pp-initiallist x.initials)
               (vl-ps-span "vl_key" (vl-println "endmodule"))
               (vl-println ""))))

(define vl-pps-module ((x vl-module-p))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (verilog-printing)
  :short "Pretty-print a module to a plain-text string."
  :long "<p>@(call vl-pps-module) pretty-prints the @(see vl-module-p) @('x')
into a plain-text string.  You may prefer @(see vl-ppcs-module) which preserves
the order of module elements and its comments.</p>"
  ;; We exploit the fact that the mods/modalist are only needed in HTML mode to
  ;; avoid generating it or requiring it as an argument.
  (with-local-ps (vl-pp-module x nil nil)))

(define vl-pp-modulelist ((x vl-modulelist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-module (car x) nil nil)
               (vl-pp-modulelist (cdr x)))))

(define vl-pps-modulelist ((x vl-modulelist-p))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (verilog-printing)
  :short "Pretty-print a list of modules to a plain-text string."
  :long "<p>See also @(see vl-ppcs-modulelist), which preserves the order of
module elements and its comments.</p>"
  (with-local-ps (vl-pp-modulelist x)))



(define vl-pp-udp ((x vl-udp-p) &key (ps 'ps))
  (b* (((vl-udp x) x))
    (vl-ps-seq (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "primitive "))
               (vl-print-modname x.name)
               (vl-println "( /* bozo need to print ports */ ) ;")
               (vl-println " // BOZO implement vl-pp-udp")
               (vl-ps-span "vl_key" (vl-println "endprimitive"))
               (vl-println ""))))

(define vl-pp-udplist ((x vl-udplist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-udp (car x))
               (vl-pp-udplist (cdr x)))))



(define vl-pp-config ((x vl-config-p) &key (ps 'ps))
  (b* (((vl-config x) x))
    (vl-ps-seq (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "config "))
               (vl-print-modname x.name)
               (vl-println " ;")
               (vl-println " // BOZO implement vl-pp-config")
               (vl-ps-span "vl_key" (vl-println "endconfig"))
               (vl-println ""))))

(define vl-pp-configlist ((x vl-configlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-config (car x))
               (vl-pp-configlist (cdr x)))))


(define vl-pp-package ((x vl-package-p) &key (ps 'ps))
  (b* (((vl-package x) x))
    (vl-ps-seq (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "package "))
               (vl-print-modname x.name)
               (vl-println " ;")
               (vl-println " // BOZO implement vl-pp-package")
               (vl-ps-span "vl_key" (vl-println "endpackage"))
               (vl-println ""))))

(define vl-pp-packagelist ((x vl-packagelist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-package (car x))
               (vl-pp-packagelist (cdr x)))))



(define vl-pp-interface ((x vl-interface-p) &key (ps 'ps))
  (b* (((vl-interface x) x))
    (vl-ps-seq (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "interface "))
               (vl-print-modname x.name)
               (vl-println " ;")
               (vl-println " // BOZO implement vl-pp-interface")
               (vl-ps-span "vl_key" (vl-println "endinterface"))
               (vl-println ""))))

(define vl-pp-interfacelist ((x vl-interfacelist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-interface (car x))
               (vl-pp-interfacelist (cdr x)))))



(define vl-pp-program ((x vl-program-p) &key (ps 'ps))
  (b* (((vl-program x) x))
    (vl-ps-seq (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "program "))
               (vl-print-modname x.name)
               (vl-println " ;")
               (vl-println " // BOZO implement vl-pp-program")
               (vl-ps-span "vl_key" (vl-println "endprogram"))
               (vl-println ""))))

(define vl-pp-programlist ((x vl-programlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-program (car x))
               (vl-pp-programlist (cdr x)))))


;; BOZO move to parsetree
(encapsulate
  ()
  (local (defthm l0
           (implies (vl-importpart-p x)
                    (equal (stringp x)
                           (not (equal x :vl-import*))))
           :hints(("Goal" :in-theory (enable vl-importpart-p)))))

  (defthm stringp-of-vl-import->part
    (implies (vl-import-p x)
             (equal (stringp (vl-import->part x))
                    (not (equal (vl-import->part x) :vl-import*))))))

(define vl-pp-import ((x vl-import-p) &key (ps 'ps))
  :guard-hints(("Goal" :in-theory (enable vl-importpart-p)))
  (b* (((vl-import x) x))
    (vl-ps-seq (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "import "))
               (vl-print-modname x.pkg)
               (vl-print "::")
               (if (eq x.part :vl-import*)
                   (vl-print "*")
                 (vl-print-str x.part))
               (vl-println " ;"))))

(define vl-pp-importlist ((x vl-importlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-import (car x))
               (vl-pp-importlist (cdr x)))))




(define vl-fwdtypedefkind-string ((x vl-fwdtypedefkind-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints(("Goal" :in-theory (enable vl-fwdtypedefkind-p)))
  (case (vl-fwdtypedefkind-fix x)
    (:vl-enum            "enum")
    (:vl-struct          "struct")
    (:vl-union           "union")
    (:vl-class           "class")
    (:vl-interfaceclass  "interfaceclass")
    (otherwise           (or (impossible) ""))))

(define vl-pp-fwdtypedef ((x vl-fwdtypedef-p) &key (ps 'ps))
  (b* (((vl-fwdtypedef x) x))
    (vl-ps-seq (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key"
                           (vl-print "typedef ")
                           (vl-print-str (vl-fwdtypedefkind-string x.kind)))
               (vl-print " ")
               (vl-print-wirename x.name)
               (vl-println " ;"))))

(define vl-pp-fwdtypedeflist ((x vl-fwdtypedeflist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-fwdtypedef (car x))
               (vl-pp-fwdtypedeflist (cdr x)))))

(define vl-pp-typedef ((x vl-typedef-p) &key (ps 'ps))
  (b* (((vl-typedef x) x))
    (vl-ps-seq (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key"
                           (vl-print "typedef "))
               (vl-pp-datatype x.type)
               ;; BOZO add dimensions
               (vl-println " ;"))))

(define vl-pp-typedeflist ((x vl-typedeflist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-typedef (car x))
               (vl-pp-typedeflist (cdr x)))))

