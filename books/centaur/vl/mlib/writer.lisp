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
(include-book "find-module")
(include-book "stmt-tools")
(include-book "modnamespace") ;; bozo at least for portdecllist->names
(include-book "../loader/lexer") ; yucky, for simple-id-tail-p, etc.
(include-book "../util/print")
(include-book "str/strrpos" :dir :system)
(local (include-book "../util/arithmetic"))


(defxdoc verilog-printing
  :parents (printer)
  :short "Printing routines for displaying Verilog constructs."

  :long "<p>Using the VL @(see printer), we implement pretty-printing routines
to display our @(see modules) and other parse-tree structures.  These functions
produce either plain text or html output, depending upon the <tt>htmlp</tt>
setting in the printer state, @(see ps).</p>")




(defsection vl-ps->show-atts-p
  :parents (verilog-printing)
  :short "Controls whether Verilog-2005 <tt>(* key = val *)</tt>-style
attributes should be displayed."

  (defun vl-ps->show-atts-p-fn (ps)
    (declare (xargs :stobjs ps))
    ;; We want the default to be T, so we check whether hide-atts is present
    ;; rather than whether show-atts is present.
    (let ((hidep (cdr (assoc-equal :vl-hide-atts (vl-ps->misc)))))
      (not hidep)))

  (defmacro vl-ps->show-atts-p ()
    `(vl-ps->show-atts-p-fn ps))

  (add-macro-alias vl-ps->show-atts-p vl-ps->show-atts-p-fn)


  (defund vl-ps-update-show-atts-fn (showp ps)
    (declare (xargs :guard (booleanp showp)
                    :stobjs ps))
    (let ((hidep (not showp))
          (misc  (vl-ps->misc)))
      (vl-ps-update-misc (acons :vl-hide-atts hidep misc))))

  (defmacro vl-ps-update-show-atts (showp)
    `(vl-ps-update-show-atts-fn ,showp ps))

  (add-macro-alias vl-ps-update-show-atts vl-ps-update-show-atts-fn))




(defsection vl-maybe-escape-identifier
  :parents (verilog-printing)
  :short "Add escape characters to an identifier name, but only if they are
necessary."

  :long "<p>@(call vl-maybe-escape-identifier) is given <tt>x</tt>, the name of
an identifier as a string.  Usually <tt>x</tt> contains only ordinary
characters and does not need to be escaped, and in such cases we return
<tt>x</tt> unchanged.  Otherwise, we add the leading <tt>\\</tt> character and
trailing space.</p>

<p>This function assumes that the name has no embedded spaces and at least one
character, and will cause a run-time error if these conditions are
violated.</p>"

  (defund vl-simple-id-tail-string-p (x i len)
    (declare (xargs :guard (and (stringp x)
                                (natp i)
                                (natp len)
                                (= len (length x))
                                (<= i len))
                    :measure (nfix (- (nfix len) (nfix i)))))
    (if (mbe :logic (zp (- (nfix len) (nfix i)))
             :exec (= i len))
        t
      (and (vl-simple-id-tail-p (char x i))
           (vl-simple-id-tail-string-p x (+ 1 (lnfix i)) len))))

  (defund vl-maybe-escape-identifier (x)
    (declare (xargs :guard (stringp x)))
    (let ((len (length x)))
      (cond ((= len 0)
             (prog2$
              (er hard? 'vl-maybe-escape-identifier "Empty identifier")
              ""))
            ((and (vl-simple-id-head-p (char x 0))
                  (vl-simple-id-tail-string-p x 1 len)
                  (not (member #\$ (coerce x 'list))))
             ;; A simple identifier, nothing to add.
             (mbe :logic (string-fix x)
                  :exec x))
            (t
             ;; Escaped identifier.  This isn't efficient but this should be
             ;; pretty unusual.
             (let ((chars (coerce x 'list)))
               (if (member #\Space chars)
                   (prog2$ (er hard? 'vl-maybe-escape-identifier
                               "Identifier name has spaces?  ~x0" x)
                           "")
                 (coerce (cons #\\ (append chars (list #\Space)))
                         'string)))))))

  (defthm stringp-of-vl-maybe-escape-identifier
    (stringp (vl-maybe-escape-identifier x))
    :rule-classes :type-prescription))




(defpp vl-print-modname (x)
  :guard (stringp x)
  :parents (verilog-printing)
  :short "@(call vl-print-modname) prints a module's name."

  :long "<p>When we are printing plain-text output, this function behaves the
same as @(see vl-print) except that we may escape <tt>x</tt> if necessary; see
@(see vl-maybe-escape-identifier).</p>

<p>When we are printing HTML output, we print something like:</p>

<code>
&lt;a class=\"vl_modlink\" href=\"javascript:showModule('foo')\"&gt;foo&lt;/a&gt;
</code>

<p>This function is used in various warning messages, reports, and other
displays.  The module browser's web pages are responsible for defining the
<tt>showModule</tt> function to carry out some sensible behavior.</p>"

  :body
  (vl-ps-span
   "vl_id"
   (vl-when-html
    (vl-print-markup "<a class=\"vl_modlink\" href=\"javascript:void(0);\" onClick=\"showModule('")
    (vl-print-url x)
    (vl-print-markup "')\">"))
   (vl-print-str (vl-maybe-escape-identifier x))
   (vl-when-html (vl-print-markup "</a>"))))




(defpp vl-print-wirename (x)
  :guard (stringp x)
  :parents (verilog-printing)
  :short "@(call vl-print-wirename) prints a wire's name."

  :long "<p>This is much like @(see vl-print-modname) except that we use it for
the names of identifiers within a module -- most commonly wire names, but we also
use it for the names of blocks, module instances, and so on.</p>

<p>In text mode, we just print <tt>x</tt>, escaping it if necessary.  In HTML mode,
we print something like:</p>

<code>
&lt;a class=\"vl_wirelink\" href=\"javascript:showWire('foo')\"&gt;foo&lt;/a&gt;
</code>

<p>This function is used in various warning messages, reports, and other
displays.  The module browser's web pages are responsible for defining the
<tt>showWire</tt> function to carry out some sensible behavior.</p>"

  :body
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
   (vl-when-html (vl-print-markup "</a>"))))

(defpp vl-pp-set-portnames (portdecls)
  :guard (vl-portdecllist-p portdecls)
  :body (b* ((names (vl-portdecllist->names portdecls))
             (misc  (vl-ps->misc)))
          (vl-ps-update-misc (acons :portnames names misc))))


(defpp vl-print-ext-wirename (modname wirename)
  :guard (and (stringp modname)
              (stringp wirename))
  :parents (verilog-printing)
  :short "@(call vl-print-ext-wirename) prints a wire's name."

  :long "<p>This is almost identical to @(see vl-print-wirename), but is intended
for messages where the module might not be apparent.</p>

<p>In text mode, we just print <tt>x</tt>, escaping it if necessary.  In HTML mode,
we print something like:</p>

<code>
&lt;a class=\"vl_wirelink\" href=\"javascript:showWireExt('mod', 'w')\"&gt;w&lt;/a&gt;
</code>

<p>The module browser's web pages are responsible for defining the
<tt>showWireExt</tt> function to carry out some sensible behavior.</p>"

  :body
  (vl-ps-span
   "vl_id"
   (vl-when-html
    (vl-print-markup "<a class=\"vl_wirelink\" href=\"javascript:void(0);\" onClick=\"showWireExt('")
    (vl-print-url modname)
    (vl-print-markup "', '")
    (vl-print-url wirename)
    (vl-print-markup "')\">"))
   (vl-print-str (vl-maybe-escape-identifier wirename))
   (vl-when-html (vl-print-markup "</a>"))))



(defpp vl-print-loc (x)
  :guard (vl-location-p x)
  :parents (verilog-printing)
  :short "@(call vl-print-loc) prints a @(see vl-location-p)."

  :long "<p>In text mode, this function basically prints the string produced by
@(see vl-location-string).  But when HTML mode is active, we instead print
something along the lines of:</p>

<code>
&lt;a class=\"vl_loclink\"
   href=\"javascript:void(0);\"
   onClick=\"showLoc('foo', 'line', 'col')\"&gt;
  foo:line:col
&lt;/a&gt;
</code>

<p>This function is used in various warning messages, reports, and other
displays.  The module browser's web pages are responsible for defining the
<tt>showLoc</tt> function to carry out some sensible behavior.</p>"

  :body
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



(defpp vl-pp-constint (x)
  :guard (vl-constint-p x)
  :body
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

(defpp vl-pp-weirdint (x)
  :guard (vl-weirdint-p x)

  ;; BOZO origwidth/origtype okay here??
  ;; BOZO maybe add origbase

  :body (b* (((vl-weirdint x) x))
            (vl-ps-span "vl_int"
                        (vl-print-nat x.origwidth)
                        (if (eq x.origtype :vl-signed)
                            (vl-print-str "'sb")
                          (vl-print-str "'b"))
                        (vl-print (vl-bitlist->charlist x.bits)))))


(defund vl-maybe-escape-string (x i len acc)
  (declare (xargs :guard (and (stringp x)
                              (natp i)
                              (natp len)
                              (= len (length x))
                              (<= i len)
                              (character-listp acc))
                  :measure (nfix (- (nfix len) (nfix i)))))
  (if (mbe :logic (zp (- (nfix len) (nfix i)))
           :exec (= i len))
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

(defthm character-listp-of-vl-maybe-escape-string
  (implies (and (force (stringp x))
                (force (natp i))
                (force (natp len))
                (force (= len (length x)))
                (force (<= i len))
                (force (character-listp acc)))
           (character-listp (vl-maybe-escape-string x i len acc)))
  :hints(("Goal" :in-theory (enable vl-maybe-escape-string))))

(defpp vl-pp-string (x)
  :guard (vl-string-p x)
  :body
  (b* (((vl-string x) x)
       (length        (length x.value)))
      (vl-ps-span "vl_str"
                  (vl-print (vl-maybe-escape-string x.value 0 length (list #\")))
                  (vl-println? #\"))))


(defpp vl-pp-real (x)
  :guard (vl-real-p x)
  :body (vl-ps-span "vl_real"
                    (vl-println? (vl-real->value x))))



(defpp vl-pp-id (x)
  :guard (vl-id-p x)
  :inlinep t
  :body  (vl-print-wirename (vl-id->name x)))

(defpp vl-pp-hidpiece (x)
  :guard (vl-hidpiece-p x)
  :body  (vl-ps-span "vl_id"
                     (vl-print-str (vl-maybe-escape-identifier (vl-hidpiece->name x)))))

(defpp vl-pp-sysfunname (x)
  :guard (vl-sysfunname-p x)
  :body  (vl-ps-span "vl_sys"
                     (vl-print-str (vl-sysfunname->name x))))

(defpp vl-pp-funname (x)
  :guard (vl-funname-p x)
  :body  (vl-ps-span "vl_id"
                     (vl-print-str (vl-maybe-escape-identifier (vl-funname->name x)))))

(defpp vl-pp-atomguts (x)
  :guard (vl-atomguts-p x)
  :guard-hints (("Goal" :in-theory (enable vl-atomguts-p)))
  :body (case (tag x)
          (:vl-constint   (vl-pp-constint x))
          (:vl-weirdint   (vl-pp-weirdint x))
          (:vl-string     (vl-pp-string x))
          (:vl-real       (vl-pp-real x))
          (:vl-id         (vl-pp-id x))
          (:vl-hidpiece   (vl-pp-hidpiece x))
          (:vl-funname    (vl-pp-funname x))
          (otherwise      (vl-pp-sysfunname x))))

(defpp vl-pp-atom (x)
  :guard (vl-atom-p x)
  :inlinep t
  :body  (vl-pp-atomguts (vl-atom->guts x)))

(defund vl-op-string (x)
  (declare (xargs :guard (vl-op-p x)))
  (case x
    (:vl-unary-plus "+")
    (:vl-unary-minus "-")
    (:vl-unary-lognot "!")
    (:vl-unary-bitnot "~")
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
    (:vl-binary-logand "&&")
    (:vl-binary-logor "||")
    (:vl-binary-power "**")
    (:vl-binary-lt "<")
    (:vl-binary-lte "<=")
    (:vl-binary-gt ">")
    (:vl-binary-gte ">=")
    (:vl-binary-bitand "&")
    (:vl-binary-bitor "|")
    (:vl-binary-xor "^")
    (:vl-binary-xnor "~^")
    (:vl-binary-shr ">>")
    (:vl-binary-shl "<<")
    (:vl-binary-ashr ">>>")
    (:vl-binary-ashl "<<<")

    (:vl-partselect-colon ":")
    (:vl-partselect-pluscolon "+:")
    (:vl-partselect-minuscolon "-:")

    (t
     (prog2$ (er hard? 'vl-op-string "Bad operator: ~x0.~%" x)
             ""))))

(defthm stringp-of-vl-op-string
  (stringp (vl-op-string x))
  :hints(("Goal" :in-theory (enable vl-op-string))))

(defmacro vl-pp-expr (x &optional (ps$ 'ps))
  `(vl-pp-expr-fn ,x ,ps$))

(defmacro vl-pp-atts (x &optional (ps$ 'ps))
  `(vl-pp-atts-fn ,x ,ps$))

(defmacro vl-pp-atts-aux (x &optional (ps$ 'ps))
  `(vl-pp-atts-aux-fn ,x ,ps$))

(defmacro vl-pp-exprlist (x &optional (ps$ 'ps))
  `(vl-pp-exprlist-fn ,x ,ps$))



(defconst *vl-ops-precedence-table*
  '(;; These aren't real operators as far as the precedence rules are
    ;; concerned, but they need to bind even more tightly than +, -, etc.
    (:VL-BITSELECT             . 20)
    (:VL-ARRAY-INDEX           . 20)
    (:VL-PARTSELECT-COLON      . 20)
    (:VL-PARTSELECT-PLUSCOLON  . 20)
    (:VL-PARTSELECT-MINUSCOLON . 20)
    (:VL-FUNCALL               . 20)
    (:VL-SYSCALL               . 20)
    (:VL-HID-DOT               . 20)
    (:VL-HID-ARRAYDOT          . 20)

    ;; In Table 5-4, concats are said to have minimal precedence.  But that
    ;; doesn't really make sense.  For instance, in: a + {b + c} the {b + c}
    ;; term acts more like an operand than another operator.  So, here I say
    ;; that concats and multiconcats also have precedence 20, so they will be
    ;; treated just like operands.  That is, we want to write &{foo,bar} rather
    ;; than &({foo,bar}).  For similar reasons, I put the mintypmax operand
    ;; here with precedence 20.
    (:VL-CONCAT        . 20)
    (:VL-MULTICONCAT   . 20)
    (:VL-MINTYPMAX     . 20)

    ;; This part is from Table 5-4 verbatim:
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
    (:VL-BINARY-BITAND . 7)
    (:VL-BINARY-XOR    . 6)
    (:VL-BINARY-XNOR   . 6)
    (:VL-BINARY-BITOR  . 5)
    (:VL-BINARY-LOGAND . 4)
    (:VL-BINARY-LOGOR  . 3)
    (:VL-QMARK         . 2)
    ))

(definlined vl-op-precedence-< (x y)
  (declare (xargs :guard (and (vl-op-p x)
                              (vl-op-p y))
                  :guard-hints(("Goal" :in-theory (enable vl-op-p)))))
  (< (cdr (assoc x *vl-ops-precedence-table*))
     (cdr (assoc y *vl-ops-precedence-table*))))

(definlined vl-op-precedence-<= (x y)
  (declare (xargs :guard (and (vl-op-p x)
                              (vl-op-p y))
                  :guard-hints(("Goal" :in-theory (enable vl-op-p)))))
  (<= (cdr (assoc x *vl-ops-precedence-table*))
      (cdr (assoc y *vl-ops-precedence-table*))))

(defconst *vl-pp-expr-special-atts*
  (list "VL_ORIG_EXPR"
        "VL_EXPLICIT_PARENS"))

(mutual-recursion
 (defund vl-pp-expr-fn (x ps)

; Originally we defensively introduced parens around every operator.  But that
; was kind of ugly.  Now each operator is responsible for putting parens around
; its arguments, if necessary.

   (declare (xargs :guard (and (vl-expr-p x)
                               (vl-pstate-p ps))
                   :stobjs ps
                   :hints(("Goal" :in-theory (disable (force))))
                   :verify-guards nil
                   :measure (two-nats-measure (acl2-count x) 2)))
   (if (vl-fast-atom-p x)
       (vl-pp-atom x)
     (let ((op   (vl-nonatom->op x))
           (args (vl-nonatom->args x))
           (atts (vl-remove-keys *vl-pp-expr-special-atts* (vl-nonatom->atts x))))
       (case op
         ((:vl-unary-plus
           :vl-unary-minus :vl-unary-lognot :vl-unary-bitnot :vl-unary-bitand
           :vl-unary-nand :vl-unary-bitor :vl-unary-nor :vl-unary-xor
           :vl-unary-xnor)
          (b* (((unless (consp args))
                (er hard 'vl-pp-expr "Impossible")
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
           :vl-binary-logand :vl-binary-logor
           :vl-binary-power
           :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte
           :vl-binary-bitand :vl-binary-bitor
           :vl-binary-xor :vl-binary-xnor
           :vl-binary-shr :vl-binary-shl :vl-binary-ashr :vl-binary-ashl)
          (b* (((unless (consp args))
                (er hard 'vl-pp-expr "Impossible")
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
; even though they seem legal per the spec.  So, in our pretty-printer we
; now add parens around the 2nd operand when we hit these cases, just so
; that when we write out test benches they work.  We tried a lot of other
; combinations like a ^ ^b, a && &b, etc., but these tools don't seem to
; care about those things.

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
                (er hard 'vl-pp-expr "Impossible")
                ps)
               (arg1 (first args))
               (arg2 (second args))
               (arg3 (third args))
               ;; these associate right to left, so "a ? b : (c ? d : e)" doesn't
               ;; need parens, but "(a ? b : c) ? d : e" does need parens.  every
               ;; other operator has precedence greater than ?:, so we never need
               ;; parens around arg3, and only rarely need them around arg1/arg2.
               ;; don't need parens around any of the components.
               (want-parens-1p (if (vl-fast-atom-p arg1)
                                   nil
                                 (vl-op-precedence-<= (vl-nonatom->op arg1) op)))
               (want-parens-2p (if (vl-fast-atom-p arg2)
                                   nil
                                 (vl-op-precedence-<= (vl-nonatom->op arg2) op))))
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
                       (vl-pp-expr arg3)
                       (vl-println? ""))))

         ((:vl-mintypmax)
          ;; Unlike other operands, I put mintypmax expressions in their own
          ;; parens so that I'm basically justified in treating them as having
          ;; operand-level precedence.
          (if (not (consp args))
              (prog2$ (er hard 'vl-pp-expr "Impossible")
                      ps)
            (vl-ps-seq (vl-print "(")
                       (vl-pp-expr (first args))
                       (vl-println? " : ")
                       (vl-pp-expr (second args))
                       (vl-println? " : ")
                       (vl-pp-expr (third args))
                       (vl-println? ")"))))

         ((:vl-bitselect :vl-array-index)
          ;; These don't need parens because they have maximal precedence
          (cond ((not (consp args))
                 (prog2$ (er hard 'vl-pp-expr "Impossible")
                         ps))
                (t
                 (vl-ps-seq (vl-pp-expr (first args))
                            (vl-print "[")
                            (vl-pp-expr (second args))
                            (vl-print "]")))))

         ((:vl-partselect-colon :vl-partselect-pluscolon :vl-partselect-minuscolon)
          ;; These don't need parens because they have maximal precedence
          (cond ((not (consp args))
                 (prog2$ (er hard 'vl-pp-expr "Impossible")
                         ps))
                (t
                 (vl-ps-seq (vl-pp-expr (first args))
                            (vl-print "[")
                            (vl-pp-expr (second args))
                            (vl-print-str (vl-op-string op))
                            (vl-pp-expr (third args))
                            (vl-print "]")))))

         ((:vl-hid-dot)
          ;; These don't need parens because they have maximal precedence
          (if (not (consp args))
              (prog2$ (er hard 'vl-pp-expr "Impossible")
                      ps)
            (vl-ps-seq (vl-pp-expr (first args))
                       (vl-print ".")
                       (vl-pp-expr (second args)))))

         ((:vl-hid-arraydot)
          ;; These don't need parens because they have maximal precedence
          (if (not (consp args))
              (prog2$ (er hard 'vl-pp-expr "Impossible")
                      ps)
            (vl-ps-seq (vl-pp-expr (first args))
                       (vl-print "[")
                       (vl-pp-expr (second args))
                       (vl-print "].")
                       (vl-pp-expr (third args)))))

         ((:vl-multiconcat)
          ;; These don't need parens because they have maximal precedence
          (cond ((not (consp args))
                 (prog2$ (er hard 'vl-pp-expr "Impossible")
                         ps))

                ((and (vl-nonatom-p (second args))
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
          ;; These don't need parens because they have maximal precedence
          (vl-ps-seq (vl-print "{")
                     (vl-pp-exprlist args)
                     (vl-print "}")))

         ((:vl-funcall :vl-syscall)
          ;; These don't need parens because they have maximal precedence
          (if (not (consp args))
              (prog2$ (er hard? 'vl-pp-expr "Bad funcall")
                      ps)
            (vl-ps-seq (vl-pp-expr (first args))
                       (vl-print "(")
                       (vl-pp-exprlist (rest args))
                       (vl-println? ")"))))

         (t
          (prog2$ (er hard? 'vl-pp-expr "Bad op: ~x0.~%" op)
                  ps))))))

 (defund vl-pp-atts-aux-fn (x ps)
   (declare (xargs :guard (and (vl-atts-p x)
                               (vl-pstate-p ps))
                   :stobjs ps
                   :measure (two-nats-measure (acl2-count x) 0)))
   (cond ((atom x)
          ps)
         (t
          (vl-ps-seq
           ;; Name
           (vl-print-str (caar x))
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
           (vl-pp-atts-aux (cdr x))))))

 (defund vl-pp-atts-fn (x ps)
   (declare (xargs :guard (and (vl-atts-p x)
                               (vl-pstate-p ps))
                   :stobjs ps
                   :measure (two-nats-measure (acl2-count x) 1)))
   (if (and x (vl-ps->show-atts-p))
       (vl-ps-span "vl_cmt"
                   (vl-print "(* ")
                   (vl-pp-atts-aux x)
                   (vl-println? " *)"))
     ps))

 (defund vl-pp-exprlist-fn (x ps)
   (declare (xargs :guard (and (vl-exprlist-p x)
                               (vl-pstate-p ps))
                   :stobjs ps
                   :measure (two-nats-measure (acl2-count x) 0)))
   (cond ((atom x)
          ps)
         ((atom (cdr x))
          (vl-pp-expr (car x)))
         (t
          (vl-ps-seq (vl-pp-expr (car x))
                     (vl-println? ", ")
                     (vl-pp-exprlist (cdr x)))))))

(FLAG::make-flag flag-vl-pp-expr
                 vl-pp-expr
                 :flag-mapping ((vl-pp-expr-fn . expr)
                                (vl-pp-atts-fn . atts)
                                (vl-pp-atts-aux-fn . atts-aux)
                                (vl-pp-exprlist-fn . list)))

(encapsulate
  ()
  ;; Speed hint
  (local (in-theory (disable acl2::member-equal-of-cons
                             MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF
                             double-containment
                             ACL2::TRUE-LISTP-MEMBER-EQUAL
                             ACL2::CONSP-MEMBER-EQUAL
                             ACL2::SUBSETP-EQUAL-MEMBER
                             (:ruleset tag-reasoning)
                             )))

  (defthm-flag-vl-pp-expr vl-pstate-p-of-flag-vl-pp-expr
    (expr (implies (and (force (vl-pstate-p ps))
                        (force (vl-expr-p x)))
                   (vl-pstate-p (vl-pp-expr x))))
    (atts (implies (and (force (vl-pstate-p ps))
                        (force (vl-atts-p x)))
                   (vl-pstate-p (vl-pp-atts x))))
    (atts-aux (implies (and (force (vl-pstate-p ps))
                            (force (vl-atts-p x)))
                       (vl-pstate-p (vl-pp-atts-aux x))))
    (list (implies (and (force (vl-pstate-p ps))
                        (force (vl-exprlist-p x)))
                   (vl-pstate-p (vl-pp-exprlist x))))
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :induct (flag-vl-pp-expr flag x ps)
            :expand ((vl-pp-expr-fn x ps)
                     (:free (ps) (vl-pp-expr-fn nil ps))
                     (vl-pp-atts-fn x ps)
                     (vl-pp-atts-fn nil ps)
                     (vl-pp-atts-aux-fn nil ps)
                     (vl-pp-atts-aux-fn x ps)
                     (vl-pp-exprlist-fn x ps)
                     ))))

  (local (defthm crock0
           (implies (and (vl-exprlist-p x)
                         (= (len x) 1))
                    (car x))))

  (local (defthm crock0b
           (implies (and (vl-exprlist-p x)
                         (= (len x) 2))
                    (and (car x)
                         (cadr x)))))

  (local (defthm crock0c
           (implies (and (vl-exprlist-p x)
                         (= (len x) 3))
                    (and (car x)
                         (cadr x)
                         (caddr x)))))

  (local (defthm crock0d
           (implies (and (vl-exprlist-p x)
                         (consp x))
                    (car x))))

  (local (in-theory (disable crock0 crock0b crock0c crock0d)))

  (local (defthm crock1
           (implies (and (= (len (vl-nonatom->args x)) 1)
                         (force (not (vl-atom-p x)))
                         (force (vl-expr-p x)))
                    (iff (car (vl-nonatom->args x))
                         t))
           :hints(("Goal"
                   :in-theory (e/d (vl-expr-p))
                   :use ((:instance crock0
                                    (x (vl-nonatom->args x))))))))
  (local (defthm crock1b
           (implies (and (= (len (vl-nonatom->args x)) 2)
                         (force (not (vl-atom-p x)))
                         (force (vl-expr-p x)))
                    (and (car (vl-nonatom->args x))
                         (cadr (vl-nonatom->args x))))
           :hints(("Goal"
                   :in-theory (e/d (vl-expr-p))
                   :use ((:instance crock0b (x (vl-nonatom->args x))))))))

  (local (defthm crock1c
           (implies (and (= (len (vl-nonatom->args x)) 3)
                         (force (not (vl-atom-p x)))
                         (force (vl-expr-p x)))
                    (and (car (vl-nonatom->args x))
                         (cadr (vl-nonatom->args x))
                         (caddr (vl-nonatom->args x))))
           :hints(("Goal"
                   :in-theory (e/d (vl-expr-p))
                   :use ((:instance crock0c (x (vl-nonatom->args x))))))))

  (local (defthm crock1d
           (implies (and (consp (vl-nonatom->args x))
                         (force (not (vl-atom-p x)))
                         (force (vl-expr-p x)))
                    (car (vl-nonatom->args x)))
           :hints(("Goal"
                   :in-theory (e/d (vl-expr-p))
                   :use ((:instance crock0d (x (vl-nonatom->args x))))))))

  (local (in-theory (enable acl2::member-equal-of-cons)))


  (verify-guards vl-pp-expr-fn
    :hints(("Goal"
            :expand (vl-expr-p x)
            :in-theory (e/d () ((force)))))))

(defund vl-pps-expr (x)
  (declare (xargs :guard (vl-expr-p x)))
  (with-local-ps (vl-pp-expr x)))

(defthm stringp-of-vl-pps-expr
  (stringp (vl-pps-expr x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-pps-expr))))



(defsection vl-pps-origexpr
  :parents (origexprs)
  :short "Pretty-print an expression, preferably in its original form."
  :long "<p><b>Signature:</b> @(call vl-pps-origexpr) returns a string.</p>

<p>This function is similar to @(see vl-pps-expr), in that it pretty-prints
<tt>x</tt> and returns the result as a string.  However, if <tt>x</tt> has a
<tt>VL_ORIG_EXPR</tt> attribute (see @(see origexprs)), we actually
pretty-print the original version of <tt>x</tt> rather than the current
version (which may be simplified, and hence not correspond as closely to the
original source code.)</p>"

  (defpp vl-pp-origexpr (x)
    :guard (vl-expr-p x)
    :body
    (if (vl-fast-atom-p x)
        (vl-pp-expr x)
      (let* ((atts   (vl-nonatom->atts x))
             (lookup (cdr (hons-assoc-equal "VL_ORIG_EXPR" atts))))
        (if lookup
            (vl-pp-expr lookup)
          (vl-pp-expr x)))))

  (defund vl-pps-origexpr (x)
    (declare (xargs :guard (vl-expr-p x)))
    (with-local-ps (vl-pp-origexpr x)))

  (defthm stringp-of-vl-pps-origexpr
    (stringp (vl-pps-origexpr x))
    :hints(("Goal" :in-theory (enable vl-pps-origexpr)))))


(defpp vl-pp-port (x)
  :guard (vl-port-p x)
  :body (let ((name (vl-port->name x))
              (expr (vl-port->expr x)))
          (cond ((and (not name)
                      (not expr))
                 ;; A truly blank port... we'll put in a comment.
                 (vl-ps-span "vl_cmt" (vl-println? "/* blank port */")))

                ((not name)
                 ;; Just a complex expression like foo[3:0] with no name.
                 (vl-pp-expr expr))

                ((and expr
                      (vl-fast-atom-p expr)
                      (vl-fast-id-p (vl-atom->guts expr))
                      (equal (vl-id->name (vl-atom->guts expr)) name))
                 ;; Ordinary case, internal expression is just the same as the
                 ;; externally visible name.
                 (vl-print-wirename name))

                (t
                 ;; .name(expr) or .name()
                 (vl-ps-seq (vl-print ".")
                            (vl-ps-span "vl_id"
                                        (vl-print-str (vl-maybe-escape-identifier name)))
                            (vl-print "(")
                            (if expr
                                (vl-pp-expr expr)
                              ps)
                            (vl-print ")"))))))

(defpp vl-pp-portlist (x)
  :guard (vl-portlist-p x)
  :body (cond ((atom x)
               ps)
              ((atom (cdr x))
               (vl-pp-port (car x)))
              (t
               (vl-ps-seq (vl-pp-port (car x))
                          (vl-println? ", ")
                          (vl-pp-portlist (cdr x))))))

(defund vl-netdecltype-string (x)
  (declare (xargs :guard (vl-netdecltype-p x)
                  :guard-hints (("Goal" :in-theory (enable vl-netdecltype-p)))))
  (case x
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
    (otherwise   (prog2$ (er hard 'vl-netdecltype-string "Provably impossible")
                         ""))))

(defthm stringp-of-vl-netdecltype-string
  (stringp (vl-netdecltype-string x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-netdecltype-string))))

(defund vl-direction-string (x)
  (declare (xargs :guard (vl-direction-p x)
                  :guard-hints (("Goal" :in-theory (enable vl-direction-p)))))
  (case x
    (:vl-input  "input")
    (:vl-output "output")
    (:vl-inout  "inout")
    (otherwise  (prog2$ (er hard? 'vl-direction-string "Provably impossible")
                        ""))))

(defthm stringp-of-vl-direction-string
  (stringp (vl-direction-string x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-direction-string))))

(defpp vl-pp-range (x)
  :guard (vl-range-p x)
  :body
  (b* (((vl-range x) x))
      (vl-ps-seq
       (vl-print "[")
       (vl-pp-expr x.msb)
       (vl-println? ":")
       (vl-pp-expr x.lsb)
       (vl-print "]"))))

(defund vl-pps-range (x)
  (declare (xargs :guard (vl-range-p x)))
  (with-local-ps (vl-pp-range x)))

(defpp vl-pp-rangelist (x)
  :guard (vl-rangelist-p x)
  :body (if (consp x)
            (vl-ps-seq (vl-pp-range (car x))
                       (vl-pp-rangelist (cdr x)))
          ps))

(defpp vl-pp-portdecl (x)
  :guard (vl-portdecl-p x)
  :body
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

(defpp vl-pp-portdecllist (x)
  :guard (vl-portdecllist-p x)
  :body (if (consp x)
            (vl-ps-seq (vl-pp-portdecl (car x))
                       (vl-pp-portdecllist (cdr x)))
          ps))

(defpp vl-pp-regdecl (x)
  :guard (vl-regdecl-p x)
  :body
  (b* (((vl-regdecl x) x)
       ((when (and x.initval x.arrdims))
        (prog2$
         (er hard? 'vl-pp-regdecl "Unreasonable regdecl: ~x0.~%" x)
         ps)))
      (vl-ps-seq
       (if x.atts (vl-pp-atts x.atts) ps)
       (vl-ps-span "vl_key"
                   (vl-print "  reg")
                   (if (not x.signedp)
                       ps
                     (vl-println? " signed")))
       (if (not x.range)
           ps
         (vl-ps-seq (vl-print " ")
                    (vl-pp-range x.range)))
       (vl-print " ")
       (vl-print-wirename x.name)
       (if x.initval
           (vl-ps-seq (vl-print " = ")
                      (vl-pp-expr x.initval))
         (vl-pp-rangelist x.arrdims))
       (vl-println " ;"))))

(defpp vl-pp-regdecllist (x)
  :guard (vl-regdecllist-p x)
  :body (if (consp x)
            (vl-ps-seq (vl-pp-regdecl (car x))
                       (vl-pp-regdecllist (cdr x)))
          ps))


(defund vl-vardecltype-string (x)
  (declare (xargs :guard (vl-vardecltype-p x)
                  :guard-hints(("Goal" :in-theory (enable vl-vardecltype-p)))))
  (case x
    (:vl-integer  "integer")
    (:vl-real     "real")
    (:vl-time     "time")
    (:vl-realtime "realtime")
    (otherwise
     (prog2$ (er hard 'vl-vardecltype-string "Impossible")
             ""))))

(defpp vl-pp-vardecl (x)
  :guard (vl-vardecl-p x)
  :body
  (b* (((vl-vardecl x) x)
       ((when (and x.initval x.arrdims))
        (prog2$
         (er hard? 'vl-pp-vardecl "Unreasonable vardecl: ~x0.~%" x)
         ps)))
      (vl-ps-seq
       (if x.atts (vl-pp-atts x.atts) ps)
       (vl-ps-span "vl_key"
                   (vl-print "  ")
                   (vl-print-str (vl-vardecltype-string x.type))
                   (vl-print " "))
       (vl-print-wirename x.name)
       (if x.arrdims
           (vl-pp-rangelist x.arrdims)
         ps)
       (if x.initval
           (vl-ps-seq (vl-print " = ")
                      (vl-pp-expr x.initval))
         ps)
       (vl-println " ;"))))

(defpp vl-pp-vardecllist (x)
  :guard (vl-vardecllist-p x)
  :body (if (consp x)
            (vl-ps-seq (vl-pp-vardecl (car x))
                       (vl-pp-vardecllist (cdr x)))
          ps))


(defpp vl-pp-gatedelay (x)
  :guard (vl-gatedelay-p x)
  :body
  (b* (((vl-gatedelay x) x))
      (cond
       ((and (hide (equal x.rise x.fall))
             (hide (equal x.fall x.high))
             (vl-fast-atom-p x.rise)
             (vl-constint-p (vl-atom->guts x.rise)))
        ;; Almost always the delays should just be #3, etc.
        (vl-ps-seq (vl-print "#")
                   (vl-ps-span "vl_int"
                               (vl-print-nat (vl-constint->value (vl-atom->guts x.rise))))))

       (x.high
        ;; All three specified
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

(defpp vl-pp-gatestrength (x)
  :guard (vl-gatestrength-p x)
  :guard-hints (("Goal" :in-theory (enable vl-gatestrength-p
                                           vl-dstrength-p
                                           vl-gatestrength->zero
                                           vl-gatestrength->one)))
  :body
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

(defpp vl-pp-assign (x)
  :guard (vl-assign-p x)
  :body
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

(defpp vl-pp-assignlist (x)
  :guard (vl-assignlist-p x)
  :body (if (consp x)
            (vl-ps-seq (vl-pp-assign (car x))
                       (vl-pp-assignlist (cdr x)))
          ps))

(defund vl-cstrength-string (x)
  (declare (xargs :guard (vl-cstrength-p x)
                  :guard-hints (("Goal" :in-theory (enable vl-cstrength-p)))))
  (case x
    (:vl-large  "large")
    (:vl-medium "medium")
    (:vl-small  "small")
    (otherwise  (prog2$ (er hard 'vl-cstrength-string "Provably impossible")
                        ""))))

(defthm stringp-of-vl-cstrength-string
  (stringp (vl-cstrength-string x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-cstrength-string))))



(defconst *vl-pp-netdecl-special-atts*
  (list "VL_IMPLICIT"
        "VL_PORT_IMPLICIT"
        "VL_UNUSED"
        "VL_MAYBE_UNUSED"
        "VL_UNSET"
        "VL_MAYBE_UNSET"
        "VL_DESIGN_WIRE"))

(defpp vl-pp-netdecl-atts-begin (x)
  :guard (vl-atts-p x)
  :body (if (not x)
            ps
          (let ((x (vl-remove-keys *vl-pp-netdecl-special-atts* x)))
            (cond ((not x)
                   ps)

                  ((and (tuplep 1 x)
                        (equal (caar x) "VL_FOR"))
                   (if (not (and (vl-atom-p (cdar x))
                                 (vl-string-p (vl-atom->guts (cdar x)))))
                       (prog2$
                        (er hard? 'vl-pp-netdecl "Expected FROM to contain a string.")
                        ps)
                     (vl-ps-seq (vl-println "")
                                (vl-ps-span "vl_cmt"
                                            (vl-print "/* For ")
                                            (vl-print-str (vl-string->value (vl-atom->guts (cdar x))))
                                            (vl-println " */")))))

                  (t
                   (vl-ps-seq (vl-println "")
                              (vl-pp-atts x)
                              (vl-println "")))))))

(defpp vl-pp-strings-separated-by-commas (x)
  :guard (string-listp x)
  :body  (cond ((atom x)
                ps)
               ((atom (cdr x))
                (vl-print-str (car x)))
               (t
                (vl-ps-seq
                 (vl-print-str (car x))
                 (vl-print ", ")
                 (vl-pp-strings-separated-by-commas (cdr x))))))

(defpp vl-pp-netdecl-atts-end (x)
  :guard (vl-atts-p x)
  :body (if (not x)
            (vl-println "")
          (let* ((cars    (strip-cars x))
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
                                (t notes))))
            (if (not notes)
                (vl-println "")
              (vl-ps-span "vl_cmt"
                          (vl-indent 30)
                          (vl-print "// ")
                          (vl-pp-strings-separated-by-commas notes)
                          (vl-println ""))))))

(defpp vl-pp-netdecl (x)
  :guard (vl-netdecl-p x)
  :body
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

(defpp vl-pp-netdecllist (x)
  :guard (vl-netdecllist-p x)
  :body (if (consp x)
            (vl-ps-seq (vl-pp-netdecl (car x))
                       (vl-pp-netdecllist (cdr x)))
          ps))

(defpp vl-pp-plainarg (x)
  :guard (vl-plainarg-p x)
  :body
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

(defpp vl-pp-plainarglist (x force-newlinesp)
  :guard (vl-plainarglist-p x)
  :body (cond ((atom x)
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

(defpp vl-pp-namedarg (x)
  :guard (vl-namedarg-p x)
  :body (let ((name (vl-namedarg->name x))
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

(defpp vl-pp-namedarglist (x force-newlinesp)
  :guard (vl-namedarglist-p x)
  :body (cond ((atom x)
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

(defpp vl-pp-arguments (x)
  :guard (vl-arguments-p x)
  :body (b* ((namedp         (vl-arguments->namedp x))
             (args           (vl-arguments->args x))
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
                    (cw "; Warning: horrible corner case in vl-pp-arguments, printing named.~%")
                    (vl-pp-namedarglist (list namedarg) force-newlinep))
                ;; We don't even have a name.  How did this happen?
                (progn$
                 (er hard? 'vl-pp-arguments
                     "Congrats!  You have reached a remarkably obscure corner ~
                      case.  You are trying to print a plain argument list, ~
                      of length 1, which contains a \"blank\" entry.  But ~
                      there is actually no way to express this in Verilog.  ~
                      See cbooks/vl/blank.v for a basic summary of the ~
                      problem. There are some ways we can work around this: ~
                      (1) convert into a named argument list, or (2) ~
                      eliminating the blank by, for outputs, adding a wire ~
                      name of the appropriate width; for inputs, convert into ~
                      n'bz where n is the appropriate width.  But there isn't ~
                      enough information in vl-pp-arguments to carry out this ~
                      transformation.  At any rate, we give up.  Well done!")
                 ps))))
          (vl-pp-plainarglist args force-newlinep)))

(defpp vl-pp-modinst-atts-begin (x)
  :guard (vl-atts-p x)
  :body (cond ((not x)
               ps)

              ((and (tuplep 1 x)
                    (equal (caar x) "VL_FOR"))
               (if (not (and (vl-atom-p (cdar x))
                             (vl-string-p (vl-atom->guts (cdar x)))))
                   (prog2$
                    (er hard? 'vl-pp-modinst-atts-begin
                        "Expected VL_FOR to contain a string.")
                    ps)
                 (vl-ps-span "vl_cmt"
                             (vl-println "")
                             (vl-print "/* For ")
                             (vl-print-str (vl-string->value (vl-atom->guts (cdar x))))
                             (vl-println " */"))))

              (t
               (vl-ps-seq (vl-println "")
                          (vl-pp-atts x)
                          (vl-println "")))))



(defpp vl-pp-modulename-link-aux (name origname)
  ;; Assumes HTML mode.
  :guard (and (stringp name)
              (stringp origname))
  :body
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
   (let ((nl  (length name))
         (onl (length origname)))
     (cond ((equal origname name)
            (vl-print "$"))
           ((and (<= onl nl)
                 (equal origname (subseq name 0 onl)))
            (vl-print-str (subseq name onl nl)))
           (t
            (prog2$ (er hard? 'vl-pp-modulename-link-aux
                        "Naming convention violated: name = ~s0, origname = ~s1.~%"
                        name origname)
                    ps))))
   (vl-print-markup "</a>")))

(defpp vl-pp-modulename-link (name mods modalist)
  ;; Assumes HTML mode.
  :guard (and (stringp name)
              (vl-modulelist-p mods)
              (equal modalist (vl-modalist mods)))
  :body (let ((target-mod (vl-fast-find-module name mods modalist)))
          (if (not target-mod)
              ;; I sometimes hit this case when pretty-printing the source for modules
              ;; that were thrown away.
              (prog2$ (cw "Warning: linking to module ~s0, which isn't in the modalist.~%"
                          name)
                      (vl-print-modname name))
            (let ((origname (vl-module->origname target-mod)))
              (vl-pp-modulename-link-aux name origname)))))

(defpp vl-pp-modinst (x mods modalist)
  :guard (and (vl-modinst-p x)
              (vl-modulelist-p mods)
              (equal modalist (vl-modalist mods)))
  :body (let ((instname  (vl-modinst->instname x))
              (modname   (vl-modinst->modname x))
              (range     (vl-modinst->range x))
              (paramargs (vl-modinst->paramargs x))
              (portargs  (vl-modinst->portargs x))
              (str       (vl-modinst->str x))
              (delay     (vl-modinst->delay x))
              (atts      (vl-modinst->atts x)))
          (if (or str delay)
              (prog2$ (cw "; Note: in vl-pp-modinst, dropping str/delay from ~x0 instance.~%"
                          modname)
                      ps)
            (vl-ps-seq (vl-println "")
                       (if atts
                           (vl-pp-modinst-atts-begin atts)
                         ps)
                       (vl-print "  ")
                       (if (vl-ps->htmlp)
                           (vl-pp-modulename-link modname mods modalist)
                         (vl-print-modname modname))
                       (if (not (vl-arguments->args paramargs))
                           ps
                         (vl-ps-seq (vl-print " #(")
                                    (vl-pp-arguments paramargs)
                                    (vl-println? ")")))
                       (vl-print " ")
                       (if instname
                           ;; BOZO maybe a different function for instance/gate names?
                           (vl-print-wirename instname)
                         (prog2$ (cw "Warning: instance of ~x0 has no instname.~%"
                                     modname)
                                 ps))
                       (if (not range)
                           ps
                         (vl-ps-seq (vl-print " ")
                                    (vl-pp-range range)))
                       (vl-print " (")
                       (vl-pp-arguments portargs)
                       (vl-println ") ;")))))

(defpp vl-pp-modinstlist (x mods modalist)
  :guard (and (vl-modinstlist-p x)
              (vl-modulelist-p mods)
              (equal modalist (vl-modalist mods)))
  :body (if (consp x)
            (vl-ps-seq (vl-pp-modinst (car x) mods modalist)
                       (vl-pp-modinstlist (cdr x) mods modalist))
          ps))

(defund vl-gatetype-string (x)
  (declare (xargs :guard (vl-gatetype-p x)
                  :guard-hints (("Goal" :in-theory (enable vl-gatetype-p)))))
  (case x
    (:vl-cmos     "cmos")
    (:vl-rcmos    "rcmos")
    (:vl-bufif0   "bufif0")
    (:vl-bufif1   "bufif1")
    (:vl-notif0   "notif0")
    (:vl-notif1   "notif")
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
    (otherwise    (prog2$ (er hard 'vl-gatetype-string "Provably impossible")
                          ""))))

(defthm stringp-of-vl-gatetype-string
  (stringp (vl-gatetype-string x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-gatetype-string))))


(defpp vl-pp-gateinst-atts-begin (x)
  :guard (vl-atts-p x)
  :body (cond ((not x)
               ps)

              ((and (tuplep 1 x)
                    (equal (caar x) "VL_FOR"))
               (if (not (and (vl-atom-p (cdar x))
                             (vl-string-p (vl-atom->guts (cdar x)))))
                   (prog2$
                    (er hard? 'vl-pp-gateinst-atts-begin
                        "Expected VL_FOR to contain a string.")
                    ps)
                 (vl-ps-span "vl_cmt"
                             (vl-println "")
                             (vl-print "/* For ")
                             (vl-print-str (vl-string->value (vl-atom->guts (cdar x))))
                             (vl-println " */"))))

              (t
               (vl-ps-seq (vl-println "")
                          (vl-pp-atts x)
                          (vl-println "")))))

(defpp vl-pp-gateinst (x)
  :guard (vl-gateinst-p x)
  :body (let ((type     (vl-gateinst->type x))
              (name     (vl-gateinst->name x))
              (range    (vl-gateinst->range x))
              (strength (vl-gateinst->strength x))
              (delay    (vl-gateinst->delay x))
              (args     (vl-gateinst->args x))
              (atts     (vl-gateinst->atts x)))
          (declare (ignorable strength delay))
          (vl-ps-seq (if atts
                         (vl-pp-gateinst-atts-begin atts)
                       ps)
                     (vl-print "  ")
                     (vl-ps-span "vl_key" (vl-print-str (vl-gatetype-string type)))
                     ;(if (not strength)
                     ;    ps
                     ;  (vl-ps-seq (vl-print " ")
                     ;             (vl-pp-gatestrength strength)))
                     ;(if (not delay)
                     ;    ps
                     ;  (vl-ps-seq (vl-print " ")
                     ;             (vl-pp-gatedelay delay)))
                     (if (not name)
                         ps
                       (vl-ps-seq (vl-print " ")
                                  ;; BOZO maybe a different function than wirename?
                                  (vl-print-wirename name)
                                  (vl-println? "")))
                     (if (not range)
                         ps
                       (vl-pp-range range))
                     (vl-print " (")
                     (vl-pp-plainarglist args nil)
                     (vl-println ") ;"))))

(defpp vl-pp-gateinstlist (x)
  :guard (vl-gateinstlist-p x)
  :body (if (consp x)
            (vl-ps-seq (vl-pp-gateinst (car x))
                       (vl-pp-gateinstlist (cdr x)))
          ps))



(defpp vl-pp-delaycontrol (x)
  :guard (vl-delaycontrol-p x)
  :body (let ((value (vl-delaycontrol->value x)))
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


(defpp vl-pp-evatom (x)
  :guard (vl-evatom-p x)
  :body (let ((type (vl-evatom->type x))
              (expr (vl-evatom->expr x)))
          (if (eq type :vl-noedge)
              (vl-pp-expr expr)
            (vl-ps-seq (vl-ps-span "vl_key"
                                   (if (eq type :vl-posedge)
                                       (vl-print "posedge ")
                                     (vl-print "negedge ")))
                       (vl-pp-expr expr)))))

(defpp vl-pp-evatomlist (x)
  :guard (vl-evatomlist-p x)
  :body (cond ((atom x)
               ps)
              ((atom (cdr x))
               (vl-pp-evatom (car x)))
              (t
               (vl-ps-seq (vl-pp-evatom (car x))
                          (vl-ps-span "vl_key" (vl-print " or "))
                          (vl-pp-evatomlist (cdr x))))))

(defpp vl-pp-eventcontrol (x)
  :guard (vl-eventcontrol-p x)
  :body (let ((starp (vl-eventcontrol->starp x))
              (atoms (vl-eventcontrol->atoms x)))
          (if starp
              (vl-print "@*")
            (vl-ps-seq (vl-print "@(")
                       (vl-pp-evatomlist atoms)
                       (vl-println? ")")))))

(defpp vl-pp-repeateventcontrol (x)
  :guard (vl-repeateventcontrol-p x)
  :body (let ((expr (vl-repeateventcontrol->expr x))
              (ctrl (vl-repeateventcontrol->ctrl x)))
          (vl-ps-seq (vl-ps-span "vl_key" (vl-print "repeat "))
                     (vl-print "(")
                     (vl-pp-expr expr)
                     (vl-print ")")
                     (vl-pp-eventcontrol ctrl))))

(defpp vl-pp-delayoreventcontrol (x)
  :guard (vl-delayoreventcontrol-p x)
  :guard-hints (("Goal" :in-theory (enable vl-delayoreventcontrol-p)))
  :body (cond ((vl-delaycontrol-p x) (vl-pp-delaycontrol x))
              ((vl-eventcontrol-p x) (vl-pp-eventcontrol x))
              (t (vl-pp-repeateventcontrol x))))





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

(defpp vl-pp-stmt-autoindent ()
  :body (vl-indent (nfix (- (vl-ps->autowrap-ind) 2))))

(defmacro vl-pp-stmt-indented (&rest args)
  `(let* ((_pp_stmt_autowrap_ind_ (vl-ps->autowrap-ind))
          (_pp_stmt_autowrap_col_ (vl-ps->autowrap-col))
          (ps (vl-ps-update-autowrap-col (+ 2 _pp_stmt_autowrap_col_)))
          (ps (vl-ps-update-autowrap-ind (+ 2 _pp_stmt_autowrap_ind_)))
          (ps (vl-ps-seq . ,args))
          (ps (vl-ps-update-autowrap-col _pp_stmt_autowrap_col_))
          (ps (vl-ps-update-autowrap-ind _pp_stmt_autowrap_ind_)))
     ps))

(defpp vl-pp-assignstmt (x)
  :guard (vl-assignstmt-p x)
  :body (b* (((vl-assignstmt x) x))
          (vl-ps-seq (vl-pp-stmt-autoindent)
                     (if x.atts (vl-pp-atts x.atts) ps)
                     (vl-ps-span "vl_key"
                                 (case x.type
                                   (:vl-assign (vl-println? "assign "))
                                   (:vl-force  (vl-println? "force "))
                                   (otherwise  ps)))
                     (vl-pp-expr x.lvalue)
                     (case x.type
                       (:vl-nonblocking (vl-println? "<="))
                       (otherwise       (vl-println? "=")))
                     (if x.ctrl
                         (vl-pp-delayoreventcontrol x.ctrl)
                       ps)
                     (vl-pp-expr x.expr)
                     (vl-println " ;"))))

(defpp vl-pp-nullstmt (x)
  :guard (vl-nullstmt-p x)
  :body (b* (((vl-nullstmt x) x))
          (vl-ps-seq (vl-pp-stmt-autoindent)
                     (if x.atts (vl-pp-atts x.atts) ps)
                     (vl-println " ;"))))

(defpp vl-pp-enablestmt (x)
  :guard (vl-enablestmt-p x)
  :body (b* (((vl-enablestmt x) x))
          (vl-ps-seq (vl-pp-stmt-autoindent)
                     (if x.atts (vl-pp-atts x.atts) ps)
                     (vl-pp-expr x.id)
                     (vl-println? "(")
                     (vl-pp-exprlist x.args)
                     (vl-println ") ;"))))

(defpp vl-pp-atomicstmt (x)
  :guard (vl-atomicstmt-p x)
  :body (cond ((vl-fast-nullstmt-p x)
               (vl-pp-nullstmt x))
              ((vl-fast-assignstmt-p x)
               (vl-pp-assignstmt x))
              ((vl-fast-enablestmt-p x)
               (vl-pp-enablestmt x))
              (t
               (vl-ps-seq
                (vl-print "// OOPS, IMPLEMENT ")
                (vl-println (symbol-name (tag x)))
                ps))))


(defund vl-casetype-string (x)
  (declare (xargs :guard (vl-casetype-p x)
                  :guard-hints (("Goal" :in-theory (enable vl-casetype-p)))))
  (case x
    ('nil         "case")
    (:vl-casex    "casex")
    (:vl-casez    "casez")
    (otherwise    (prog2$ (er hard 'vl-casetype-string "Provably impossible")
                          ""))))

(defthm stringp-of-vl-casetype-string
  (stringp (vl-casetype-string x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-casetype-string))))


(defmacro vl-pp-stmt (x)
  `(vl-pp-stmt-fn ,x ps))

(defmacro vl-pp-stmtlist (x)
  `(vl-pp-stmtlist-fn ,x ps))

(defmacro vl-pp-cases (exprs bodies)
  `(vl-pp-cases-fn ,exprs ,bodies ps))

(mutual-recursion

 (defund vl-pp-stmt-fn (x ps)
   (declare (xargs :guard (and (vl-stmt-p x)
                               (vl-pstate-p ps))
                   :stobjs ps
                   :verify-guards nil
                   :measure (two-nats-measure (acl2-count x) 1)))
   (cond
    ((vl-fast-atomicstmt-p x)
     (vl-pp-atomicstmt x))

    ((mbe :logic (not (consp x))
          :exec nil)
     (prog2$
      (er hard 'vl-pp-stmt-fn "Impossible case for termination")
      ps))

    (t
     (let ((type  (vl-compoundstmt->type x))
           (atts  (vl-compoundstmt->atts x)))

       (case type

         ((:vl-ifstmt)
          (vl-ps-seq (vl-pp-stmt-autoindent)
                     (if atts (vl-pp-atts atts) ps)
                     (vl-ps-span "vl_key" (vl-print "if"))
                     (vl-print " (")
                     (vl-pp-expr (vl-ifstmt->condition x))
                     (vl-println ")")
                     (vl-pp-stmt-indented (vl-pp-stmt (vl-ifstmt->truebranch x)))
                     (vl-pp-stmt-autoindent)
                     (vl-ps-span "vl_key" (vl-println "else"))
                     (vl-pp-stmt-indented (vl-pp-stmt (vl-ifstmt->falsebranch x)))))

         ((:vl-blockstmt)
          (let ((sequentialp (vl-blockstmt->sequentialp x))
                (name        (vl-blockstmt->name x))
                (decls       (vl-blockstmt->decls x))
                (stmts       (vl-blockstmt->stmts x)))
            (vl-ps-seq (vl-pp-stmt-autoindent)
                       (if atts (vl-pp-atts atts) ps)
                       (vl-ps-span "vl_key" (vl-print (if sequentialp "begin " "fork ")))
                       (if (not name)
                           ps
                         (vl-ps-seq
                          (vl-print " : ")
                          (vl-ps-span "vl_id" (vl-print-str (vl-maybe-escape-identifier name)))
                          (if (not decls)
                              ps
                            (vl-ps-span
                             "vl_cmt"
                             (vl-print "// BOZO implement vl-pp-stmt for block with decls")))))
                       (vl-println "")
                       (vl-pp-stmt-indented (vl-pp-stmtlist stmts))
                       (vl-pp-stmt-autoindent)
                       (vl-ps-span "vl_key" (vl-print-str (if sequentialp "end" "join")))
                       (vl-println ""))))

         ((:vl-forstmt)
          (let ((initlhs (vl-forstmt->initlhs x))
                (initrhs (vl-forstmt->initrhs x))
                (test    (vl-forstmt->test x))
                (nextlhs (vl-forstmt->nextlhs x))
                (nextrhs (vl-forstmt->nextrhs x))
                (body    (vl-forstmt->body x)))
            (vl-ps-seq (vl-pp-stmt-autoindent)
                       (if atts (vl-pp-atts atts) ps)
                       (vl-ps-span "vl_key" (vl-print "for "))
                       (vl-print "(")
                       (vl-pp-expr initlhs) (vl-print " = ") (vl-pp-expr initrhs)
                       (vl-print "; ")
                       (vl-pp-expr test)
                       (vl-print "; ")
                       (vl-pp-expr nextlhs) (vl-print " = ") (vl-pp-expr nextrhs)
                       (vl-println ")")
                       (vl-pp-stmt-indented (vl-pp-stmt body)))))

         ((:vl-timingstmt)
          (let ((ctrl (vl-timingstmt->ctrl x))
                (stmt (vl-timingstmt->body x)))
            (vl-ps-seq (vl-pp-stmt-autoindent)
                       (if atts (vl-pp-atts atts) ps)
                       (vl-pp-delayoreventcontrol ctrl)
                       (vl-print " ")
                       (vl-pp-stmt stmt))))

         ((:vl-casestmt)
          (let ((type    (vl-casestmt->casetype x))
                (test    (vl-casestmt->test x))
                (exprs   (vl-casestmt->exprs x))
                (bodies  (vl-casestmt->bodies x))
                (default (vl-casestmt->default x)))
            (vl-ps-seq (vl-pp-stmt-autoindent)
                       (if atts (vl-pp-atts atts) ps)
                       (vl-ps-span "vl_key" (vl-print-str (vl-casetype-string type)))
                       (vl-print " (")
                       (vl-pp-expr test)
                       (vl-println ")")
                       (vl-pp-stmt-indented (vl-pp-cases exprs bodies))
                       (vl-pp-stmt-autoindent)
                       (vl-ps-span "vl_key" (vl-print "default"))
                       (vl-println " :")
                       (vl-pp-stmt-indented (vl-pp-stmt default))
                       (vl-pp-stmt-autoindent)
                       (vl-ps-span "vl_key" (vl-print "endcase")))))

         (otherwise
          ;; :vl-forstmt :vl-foreverstmt
          ;; :vl-waitstmt :vl-repeatstmt :vl-whilestmt
          (vl-ps-span "vl_cmt"
                      (vl-pp-stmt-autoindent)
                      (vl-print "// BOZO implement vl-pp-stmt for ")
                      (vl-println (symbol-name type)))))))))

 (defund vl-pp-stmtlist-fn (x ps)
   (declare (xargs :guard (and (vl-stmtlist-p x)
                               (vl-pstate-p ps))
                   :stobjs ps
                   :measure (two-nats-measure (acl2-count x) 0)))
   (if (atom x)
       ps
     (vl-ps-seq (vl-pp-stmt (car x))
                (vl-pp-stmtlist (cdr x)))))

 (defund vl-pp-cases-fn (exprs bodies ps)
   (declare (xargs :guard (and (vl-exprlist-p exprs)
                               (vl-stmtlist-p bodies)
                               (vl-pstate-p ps))
                   :stobjs ps
                   :measure (two-nats-measure (acl2-count bodies) 0)))
   (cond ((and (atom exprs)
               (atom bodies))
          ps)
         ((or (atom exprs)
              (atom bodies))
          (progn$ (er hard? 'vl-pp-cases-fn
                      "Case statement with different number of match expressions and bodies???")
                  ps))
         (t
          (vl-ps-seq (vl-pp-stmt-autoindent)
                     (vl-pp-expr (car exprs))
                     (vl-println " :")
                     (vl-pp-stmt-indented (vl-pp-stmt (car bodies)))
                     (vl-pp-cases (cdr exprs) (cdr bodies)))))))

(FLAG::make-flag flag-vl-pp-stmt-fn
                 vl-pp-stmt-fn
                 :flag-mapping ((vl-pp-stmt-fn . stmt)
                                (vl-pp-stmtlist-fn . list)
                                (vl-pp-cases-fn . case)))

(defthm-flag-vl-pp-stmt-fn vl-pstate-p-of-flag-vl-pp-stmt-fn
  (defthm vl-pstate-p-of-vl-pp-stmt
    (implies (and (force (vl-stmt-p x))
                  (force (vl-pstate-p ps)))
             (vl-pstate-p (vl-pp-stmt x)))
    :flag stmt)
  (defthm vl-pstate-p-of-vl-pp-stmtlist
    (implies (and (force (vl-stmtlist-p x))
                  (force (vl-pstate-p ps)))
             (vl-pstate-p (vl-pp-stmtlist x)))
    :flag list)
  (defthm vl-pstate-p-of-vl-pp-cases
    (implies (and (force (vl-exprlist-p exprs))
                  (force (vl-stmtlist-p bodies))
                  (force (vl-pstate-p ps)))
             (vl-pstate-p (vl-pp-cases exprs bodies)))
    :flag case)
  :hints(("Goal"
          :expand ((vl-pp-stmt-fn x ps)
                   (vl-pp-stmtlist-fn x ps)
                   (vl-pp-cases-fn exprs bodies ps)))))

(verify-guards vl-pp-stmt-fn)



(defpp vl-pp-always (x)
  :guard (vl-always-p x)
  :body (let ((stmt (vl-always->stmt x))
              (atts (vl-always->atts x)))
          (vl-ps-seq (vl-print "  ")
                     (if atts (vl-pp-atts atts) ps)
                     (vl-ps-span "vl_key" (vl-print "always "))
                     (vl-pp-stmt stmt))))

(defpp vl-pp-alwayslist (x)
  :guard (vl-alwayslist-p x)
  :body (if (consp x)
            (vl-ps-seq (vl-pp-always (car x))
                       (vl-println "")
                       (vl-pp-alwayslist (cdr x)))
          ps))

(defpp vl-pp-initial (x)
  :guard (vl-initial-p x)
  :body (let ((stmt (vl-initial->stmt x))
              (atts (vl-initial->atts x)))
          (vl-ps-seq (vl-print "  ")
                     (if atts (vl-pp-atts atts) ps)
                     (vl-ps-span "vl_key" (vl-print "initial "))
                     (vl-pp-stmt stmt)
                     (vl-println ""))))

(defpp vl-pp-initiallist (x)
  :guard (vl-initiallist-p x)
  :body (if (consp x)
            (vl-ps-seq (vl-pp-initial (car x))
                       (vl-println "")
                       (vl-pp-initiallist (cdr x)))
          ps))

(defpp vl-pp-paramdecl (x)
  :guard (vl-paramdecl-p x)
  :body (b* (((vl-paramdecl x) x))
          (vl-ps-seq
           (vl-print "  ")
           (if x.atts
               (vl-ps-seq (vl-pp-atts x.atts)
                          (vl-print " "))
             ps)
           (vl-ps-span
            "vl_key"
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

(defpp vl-pp-paramdecllist (x)
  :guard (vl-paramdecllist-p x)
  :body (if (consp x)
            (vl-ps-seq (vl-pp-paramdecl (car x))
                       (vl-pp-paramdecllist (cdr x)))
          ps))



(defpp vl-pp-blockitem (x)
  :guard (vl-blockitem-p x)
  :body
  (case (tag x)
    (:vl-regdecl   (vl-pp-regdecl x))
    (:vl-vardecl   (vl-pp-vardecl x))
    (:vl-eventdecl (vl-println "// BOZO implement eventdecl printing"))
    (:vl-paramdecl (vl-pp-paramdecl x))
    (otherwise
     (prog2$ (er hard 'vl-pp-blockitem "Impossible")
             ps))))

(defpp vl-pp-blockitemlist (x)
  :guard (vl-blockitemlist-p x)
  :body (if (consp x)
            (vl-ps-seq (vl-pp-blockitem (car x))
                       (vl-pp-blockitemlist (cdr x)))
          ps))



(defsection vl-funtype-string
  :parents (vl-funtype-p)
  :short "@(call vl-funtype-string) returns a string describing this function
type, for pretty-printing."

  :long "<p>We just return the empty don't print anything for
<tt>:vl-unsigned</tt>, but it seems like; it would be valid to print
<tt>reg</tt>.</p>"

  (local (in-theory (enable vl-funtype-p)))

  (defund vl-funtype-string (x)
    (declare (xargs :guard (vl-funtype-p x)))
    (case x
      (:vl-unsigned "")
      (:vl-signed   "signed")
      (:vl-integer  "integer")
      (:vl-real     "real")
      (:vl-realtime "realtime")
      (:vl-time     "time")
      (otherwise
       (prog2$ (er hard 'vl-funtype-string "Provably impossible")
               ""))))

  (local (in-theory (enable vl-funtype-string)))

  (defthm stringp-of-vl-funtype-string
    (stringp (vl-funtype-string x))
    :rule-classes :type-prescription))

(defpp vl-pp-funinput (x)
  :guard (vl-funinput-p x)
  :body (b* (((vl-funinput x) x)
             (typestr (vl-funtype-string x.type)))
          (vl-ps-seq
           (vl-print "  ")
           (if x.atts
               (vl-ps-seq (vl-pp-atts x.atts)
                          (vl-print " "))
             ps)
           (vl-ps-span "vl_key"
                       (vl-print "input ")
                       (vl-print-str typestr)
                       (if (equal typestr "")
                           ps
                         (vl-print " ")))
           (if x.range
               (vl-ps-seq (vl-pp-range x.range)
                          (vl-print " "))
             ps)
           (vl-print-wirename x.name))))

(defpp vl-pp-funinputlist (x)
  :guard (vl-funinputlist-p x)
  :body (if (atom x)
            ps
          (vl-ps-seq (vl-pp-funinput (car x))
                     (vl-println " ;")
                     (vl-pp-funinputlist (cdr x)))))

(defpp vl-pp-fundecl (x)
  :guard (vl-fundecl-p x)
  ;; We print these off using "variant 1" style (see parse-functions)
  :body (b* (((vl-fundecl x) x)
             (typestr (vl-funtype-string x.rtype)))
          (vl-ps-seq
           (vl-print "  ")
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
           (vl-pp-funinputlist x.inputs)
           (vl-pp-blockitemlist x.decls)
           (vl-print "  ")
           (vl-pp-stmt x.body)
           (vl-basic-cw "~|")  ;; newline only if necessary
           (vl-print "  ")
           (vl-ps-span "vl_key" (vl-print "endfunction"))
           (vl-println ""))))

(defpp vl-pp-fundecllist (x)
  :guard (vl-fundecllist-p x)
  :body (if (atom x)
            ps
          (vl-ps-seq (vl-pp-fundecl (car x))
                     (vl-println "")
                     (vl-pp-fundecllist (cdr x)))))


(defpp vl-pp-module (x mods modalist)
  :parents (verilog-printing)
  :short "Pretty-print a module to @(see ps)."

  :long "<p>@(call vl-pp-module) extends @(see ps) with a pretty-printed
representation of the module <tt>x</tt>.</p>

<p>You may prefer @(see vl-ppc-module), which preserves the order of module
elements and its comments.  For interactive use, you may prefer @(see
vl-pps-module) or @(see vl-ppcs-module), which write to a string instead of
@(see ps).</p>

<p>The <tt>mods</tt> here should be the list of all modules and
<tt>modalist</tt> is its @(see vl-modalist); these arguments are only needed
for hyperlinking to submodules in HTML mode.</p>"

  :guard (and (vl-module-p x)
              (vl-modulelist-p mods)
              (equal modalist (vl-modalist mods)))
  :body (b* (((vl-module x) x))
          (vl-ps-seq
           (vl-pp-set-portnames x.portdecls)
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
           (vl-pp-regdecllist x.regdecls)
           (vl-pp-netdecllist x.netdecls)
           (vl-pp-vardecllist x.vardecls)
           (if (not x.eventdecls)
               ps
             (vl-println "// BOZO implement eventdecl printing"))
           (vl-pp-fundecllist x.fundecls) ;; put them here, so they can refer to declared wires
           (vl-pp-assignlist x.assigns)
           (vl-pp-modinstlist x.modinsts mods modalist)
           (vl-pp-gateinstlist x.gateinsts)
           (vl-pp-alwayslist x.alwayses)
           (vl-pp-initiallist x.initials)
           (vl-ps-span "vl_key" (vl-println "endmodule"))
           (vl-println ""))))


(defsection vl-pps-module
  :parents (verilog-printing)
  :short "Pretty-print a module to a plain-text string."

  :long "<p>@(call vl-pps-module) pretty-prints the @(see vl-module-p)
<tt>x</tt> into a plain-text string.  You may prefer @(see vl-ppcs-module)
which preserves the order of module elements and its comments.</p>"

  (defund vl-pps-module (x)
    (declare (xargs :guard (vl-module-p x)))
    ;; We exploit the fact that the modalist is only needed in HTML mode
    ;; to avoid generating it or requiring it as an argument.
    (with-local-ps (vl-pp-module x nil nil)))

  (defthm stringp-of-vl-pps-module
    (stringp (vl-pps-module x))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable vl-pps-module)))))



(defpp vl-pp-modulelist (x)
  :guard (vl-modulelist-p x)
  :body (if (consp x)
            (vl-ps-seq (vl-pp-module (car x) nil nil)
                       (vl-pp-modulelist (cdr x)))
          ps))


(defsection vl-pps-modulelist
  :parents (verilog-printing)
  :short "Pretty-print a list of modules to a plain-text string."

  :long "<p>See also @(see vl-ppcs-modulelist), which preserves the order of
module elements and its comments.</p>"

  (defund vl-pps-modulelist (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (with-local-ps (vl-pp-modulelist x)))

  (defthm stringp-of-vl-pps-modulelist
    (stringp (vl-pps-modulelist x))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable vl-pps-modulelist)))))



