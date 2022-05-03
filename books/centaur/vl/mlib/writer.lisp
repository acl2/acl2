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
(include-book "find")
(include-book "stmt-tools")
(include-book "scopestack")
(include-book "../loader/lexer/chartypes") ; yucky, for simple-id-tail-p, etc.
(include-book "../util/print")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable double-containment
                           (tau-system))))

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

(defxdoc verilog-printing
  :parents (printer)
  :short "Printing routines for displaying SystemVerilog constructs."

  :long "<p>Using the VL @(see printer), we implement pretty-printing routines
to display our internal parse-tree representation (see @(see syntax)) as
SystemVerilog code.  These functions produce either plain text or html output,
depending upon the @('htmlp') setting in the printer state, @(see ps).</p>

<p>The pretty-printer is intended to be useful and convenient for humans to
read, but it is <b>not necessarily trustworthy</b>.  For instance:</p>

<ul>

<li>Internally, VL generally keeps constructs like wire declarations and port
declarations separate from assignments and module instances.  When we print out
a module with routines like @(see vl-pp-module), the result is often
reasonable, but it is easy to imagine cases where it could not be given to
another Verilog tool because the resulting module no longer corresponds to the
original parse order.</li>

<li>For certain constructs, such as post-elaborated generate blocks, there is
no corresponding Verilog syntax that provides the same scoping and name
resolution.  In this case we print out something that resembles Verilog and
that is not hard for a human to understand, but that would not be accepted by
any tool that expected to get well-formed Verilog as input.</li>

</ul>")

(local (xdoc::set-default-parents verilog-printing))

(define vl-ps->show-atts-p (&key (ps 'ps))
  :short "Should Verilog-2005 @('(* key = val *)')-style attributes be shown?"
  :long "<p>See also @(see vl-ps-update-show-atts).</p>"
  (let ((hidep (cdr (assoc-equal :vl-hide-atts (vl-ps->misc)))))
    (not hidep)))

(define vl-ps-update-show-atts ((showp booleanp) &key (ps 'ps))
  :short "Set whether Verilog-2005 @('(* key = val *)')-style attributes should
be displayed."
  :long "<p>We want the default to be @('t'), so we look for @('hide-atts')
instead of @('show-atts').</p>"
  :verbosep t
  (let* ((hidep (not showp))
         (misc  (vl-ps->misc))
         (misc  (remove-from-alist :vl-hide-atts misc)))
    (vl-ps-update-misc (acons :vl-hide-atts hidep misc))))


(define vl-ps->mimic-linebreaks-p (&key (ps 'ps))
  :short "Should we try to emulate linebreaks from the original input?"
  :long "<p>See also @(see vl-ps-update-mimic-linebreaks).</p>"
  (let ((disregardp (cdr (assoc-equal :vl-disregard-linebreaks (vl-ps->misc)))))
    (not disregardp)))

(define vl-ps-update-mimic-linebreaks ((mimicp booleanp) &key (ps 'ps))
  :short "Set whether we should emulate linebreaks from the original input."
  :long "<p>We want the default to be @('t'), so we look for
@('disregard-linebreaks') instead of @('mimic-linebreaks').</p>"
  :verbosep t
  (let* ((disregardp (not mimicp))
         (misc  (vl-ps->misc))
         (misc  (remove-from-alist :vl-disregard-linebreaks misc)))
    (vl-ps-update-misc (acons :vl-disregard-linebreaks disregardp misc))))

(defmacro without-mimicking-linebreaks (&rest args)
  `(let* ((__vl-ps-mimic-linebreaks-prev (vl-ps->mimic-linebreaks-p))
          (ps (vl-ps-update-mimic-linebreaks nil))
          (ps (vl-ps-seq . ,args))
          (ps (vl-ps-update-mimic-linebreaks __vl-ps-mimic-linebreaks-prev)))
     ps))


(define vl-ps->use-origexprs-p (&key (ps 'ps))
  :short "Should we print VL_ORIG_EXPR fields?"
  :long "<p>See also @(see vl-ps-update-use-origexprs).</p>"
  (cdr (assoc-equal :vl-use-origexprs (vl-ps->misc))))

(define vl-ps-update-use-origexprs ((usep booleanp) &key (ps 'ps))
  :short "Set whether we should print expressions as VL_ORIG_EXPRs, when
they have such annotations."
  :verbosep t
  (let ((misc (vl-ps->misc)))
    (vl-ps-update-misc (acons :vl-use-origexprs (and usep t) misc))))


(define vl-ps->copious-parens-p (&key (ps 'ps))
  :short "Should we print expressions with extra parentheses?  This may be
  useful when you want to show the precedence in a very explicit way."
  :long "<p>See also @(see vl-ps-update-copious-parens).</p>"
  (cdr (assoc-equal :vl-copious-parens (vl-ps->misc))))

(define vl-ps-update-copious-parens ((copiousp booleanp) &key (ps 'ps))
  :short "Set whether we should print expressions with extra parentheses even
where they are not needed."
  :verbosep t
  (let* ((misc (vl-ps->misc))
         (misc (remove-from-alist :vl-copious-parens misc)))
    (vl-ps-update-misc (acons :vl-copious-parens (and copiousp t) misc))))



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

(define vl-progindent (&key (ps 'ps))
  :short "Indent until wherever the next line should start, suitable for
          however many nested constructs are currently open."

  :long "<p>When we go into a construct such as a @('module'), @('function')
body, @('always') statement, @('begin') block, @('for') loop, and so forth, we
would like to progressively increase our indentation level.  We (arbitrarily)
choose to indent by 2 columns for every ``open'' construct, i.e., we want our
output to look something like this:</p>

@({
     module foo;
       function bar (...);
         begin
           integer a = 1;
           for(integer b = 0; ...; ...)
             foo[b] = a + ...;
         end
       endfunction
     endmodule
})

<p>To implement progressive indentation, we tinker with the @('autowrap-col')
and @('autowrap-ind'); see @(see ps) for background.  We generally expect that
@('autowrap-col') starts out at something like 80 or more, while
@('autowrap-ind') starts at 5.</p>

<p>It seems nice for the @('autowrap-ind') to consistently be set to a little
bit past our current progressive indent level.  The @('autowrap-ind') controls
how far we'll indent after a long line goes past the right margin.  If we're
wrapping such a line in, e.g., the for loop above, then we probably want to
indent to: 8 columns for the foo loop itself, then some extra since it was a
long line we were autowrapping.</p>

<p>So my convention is that @('vl-progindent') will always indent to 5 less
than the @('autowrap-ind').  Note also that whenever we increase the progindent
level, we bump the right margin out, so that the visual width of each line is
roughly constant no matter how far indented over it gets.</p>"

  (vl-indent (nfix (- (vl-ps->autowrap-ind) 5))))

(defsection vl-progindent-block
  :parents (vl-progindent)
  :short "Like @(see vl-ps-seq), but increase the progressive indentation while
          for all of the statements in the block."

  (define vl-progindent-block-start (&key (ps 'ps))
    (let* ((ind (vl-ps->autowrap-ind))
           (ps  (vl-ps-update-autowrap-ind (+ 2 ind)))
           (col (vl-ps->autowrap-col))
           (ps  (vl-ps-update-autowrap-col (+ 2 col))))
      ps))

  (define vl-progindent-block-end (&key (ps 'ps))
    (let* ((ind (vl-ps->autowrap-ind))
           (ps  (vl-ps-update-autowrap-ind (nfix (+ -2 ind))))
           (col (vl-ps->autowrap-col))
           (ps  (vl-ps-update-autowrap-col (nfix (+ -2 col)))))
      ps))

  (defmacro vl-progindent-block (&rest args)
    `(let* ((ps (vl-progindent-block-start))
            (ps (vl-ps-seq . ,args))
            (ps (vl-progindent-block-end)))
       ps)))

(define vl-simple-id-tail-string-p ((x stringp)
                                    (i natp)
                                    (len (eql len (length x))))
  :guard (<= i len)
  :measure (nfix (- (nfix len) (nfix i)))
  :parents (vl-maybe-escape-identifier)
  :prepwork ((local (in-theory (disable nth))))
  :hooks ((:fix :hints (("goal" :induct (vl-simple-id-tail-string-p x i len)
                         :in-theory (disable (:d vl-simple-id-tail-string-p) nfix)
                         :expand ((:free (x len) (vl-simple-id-tail-string-p x i len))
                                  (:free (x len) (vl-simple-id-tail-string-p x (nfix i) len)))))))
  (if (mbe :logic (zp (- (nfix len) (nfix i)))
           :exec (eql i len))
      t
    (and (vl-simple-id-tail-p (char x i))
         (vl-simple-id-tail-string-p x (+ 1 (lnfix i)) len))))


(define vl-maybe-escape-identifier ((x stringp "Name of some identifier."))
  :returns (x-escaped stringp :rule-classes :type-prescription)
  :short "Add escape characters to an identifier name, if necessary."

  :long "<p>Usually @('x') contains only ordinary characters and does not need
to be escaped, and in such cases we return @('x') unchanged.  Otherwise, we add
the leading @('\\') character and trailing space.</p>

<p>Note: we assume that @('x') has no embedded spaces and at least one
character.  These requirements aren't explicit about the names used in
structures like @(see vl-scopeexpr), @(see vl-modinst), and so forth.  But they
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
                     (vl-print-markup (if (member-equal x (list-fix ports))
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

  :prepwork ((local (in-theory (disable str::completeness-of-strrpos))))
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

(define vl-pp-constint ((x vl-value-p) &key (ps 'ps))
  :guard (vl-value-case x :vl-constint)
  ;; BOZO origwidth/origsign okay here???
  ;; BOZO maybe add origbase or something for printing in the same radix
  ;; as the number was read in?
  (b* (((vl-constint x) x)

       ((when (and (eq x.origsign :vl-signed)
                   (eql x.origwidth 32)))
        ;; BOZO this might not be quite right.  We hope that it allows us to
        ;; print plain decimal integers when the user used them originally,
        ;; mainly because things like foo[32'd5] is a lot uglier than foo[5].
        ;; But we might eventually want to think hard about whether this is
        ;; really okay.
        (vl-ps-span "vl_int"
                    (vl-print-nat (acl2::logext 32 x.value)))))

    (vl-ps-span "vl_int"
                (vl-print-nat x.origwidth)
                (if (eq x.origsign :vl-signed)
                    (vl-ps-seq (vl-print-str "'sd")
                               (vl-print-nat (acl2::logext x.origwidth x.value)))
                  (vl-ps-seq (vl-print-str "'d")
                             (vl-print-nat x.value))))))

(define vl-pp-weirdint ((x vl-value-p) &key (ps 'ps))
  :guard (vl-value-case x :vl-weirdint)
  ;; BOZO origwidth/origsign okay here??
  ;; BOZO maybe add origbase
  (b* (((vl-weirdint x) x))
    (vl-ps-span "vl_int"
                (vl-print-nat (len x.bits))
                (if (eq x.origsign :vl-signed)
                    (vl-print-str "'sb")
                  (vl-print-str "'b"))
                (vl-print (vl-bitlist->charlist x.bits)))))

(define vl-maybe-escape-string ((x stringp)
                                (i natp)
                                (len (and (natp len)
                                          (eql len (length x))))
                                (acc character-listp))
  :guard (<= i len)
  :returns (new-acc character-listp :hyp :fguard
                    :hints (("goal" :induct (vl-maybe-escape-string
                                             x i len acc)
                             :in-theory (disable (:d vl-maybe-escape-string) not)
                             :expand ((:free (len) (vl-maybe-escape-string x i len acc))))))
  :measure (nfix (- (nfix len) (nfix i)))
  :hooks nil
  :prepwork ((local (in-theory (disable nth
                                        acl2::len-when-atom
                                        nth-of-atom acl2::nth-when-atom
                                        stringp-when-true-listp
                                        acl2::rev-of-cons
                                        acl2::consp-when-member-equal-of-atom-listp
                                        acl2::consp-under-iff-when-true-listp))))
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

(define vl-pp-string ((x vl-value-p) &key (ps 'ps))
  :guard (vl-value-case x :vl-string)
  (b* (((vl-string x) x)
       (length        (length x.value)))
    (vl-ps-span "vl_str"
                (vl-print (vl-maybe-escape-string x.value 0 length (list #\")))
                (vl-println? #\"))))

(define vl-pp-real ((x vl-value-p) &key (ps 'ps))
  :guard (vl-value-case x :vl-real)
  (vl-ps-span "vl_real"
              (vl-println? (vl-real->value x))))

(define vl-pp-time ((x vl-value-p) &key (ps 'ps))
  :guard (vl-value-case x :vl-time)
  (b* (((vl-time x) x))
    (vl-ps-seq
     (vl-print-str x.quantity)
     (vl-print (vl-timeunit->string x.units)))))


(define vl-pp-extint ((x vl-value-p) &key (ps 'ps))
  :guard (vl-value-case x :vl-extint)
  :prepwork ((local (in-theory (enable (tau-system)))))
  (b* (((vl-extint x) x))
    (vl-ps-span "vl_int"
                (vl-print-str
                 (case x.value
                   (:vl-0val "'0")
                   (:vl-1val "'1")
                   (:vl-xval "'x")
                   (:vl-zval "'z"))))))

(define vl-pp-value ((x vl-value-p) &key (ps 'ps))
  (vl-value-case x
    :vl-constint (vl-pp-constint x)
    :vl-weirdint (vl-pp-weirdint x)
    :vl-string   (vl-pp-string x)
    :vl-real     (vl-pp-real x)
    :vl-time     (vl-pp-time x)
    :vl-extint   (vl-pp-extint x)))




(define vl-randomqualifier-string ((x vl-randomqualifier-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints(("Goal" :in-theory (enable vl-randomqualifier-p)))
  (case (vl-randomqualifier-fix x)
    ('nil         "")
    (:vl-rand     "rand")
    (:vl-randc    "randc")
    (otherwise    (or (impossible) ""))))

(define vl-nettypename-string ((x vl-nettypename-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-nettypename-p)))
  (case (vl-nettypename-fix x)
    (:vl-wire    "wire")
    (:vl-tri     "tri")
    (:vl-supply0 "supply0")
    (:vl-supply1 "supply1")
    (:vl-triand  "triand")
    (:vl-trior   "trior")
    (:vl-tri0    "tri0")
    (:vl-tri1    "tri1")
    (:vl-trireg  "trireg")
    (:vl-uwire   "uwire")
    (:vl-wand    "wand")
    (:vl-wor     "wor")
    (otherwise   (or (impossible) ""))))

(define vl-coretypename-string ((x vl-coretypename-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints(("Goal" :in-theory (enable vl-coretypename-p)))
  (case (vl-coretypename-fix x)
    (:vl-logic     "logic")
    (:vl-reg       "reg")
    (:vl-bit       "bit")
    (:vl-void      "void")
    (:vl-byte      "byte")
    (:vl-shortint  "shortint")
    (:vl-int       "int")
    (:vl-longint   "longint")
    (:vl-integer   "integer")
    (:vl-time      "time")
    (:vl-shortreal "shortreal")
    (:vl-real      "real")
    (:vl-realtime  "realtime")
    (:vl-string    "string")
    (:vl-chandle   "chandle")
    (:vl-event     "event")
    (:vl-untyped   "untyped")
    (:vl-sequence  "sequence")
    (:vl-property  "property")
    (otherwise     (or (impossible) ""))))

(define vl-pp-scopename ((x vl-scopename-p) &key (ps 'ps))
  :prepwork ((local (in-theory (enable vl-scopename-p))))
  (b* ((x (vl-scopename-fix x)))
    (cond ((eq x :vl-local) (vl-ps-span "vl_key" (vl-print "local")))
          ((eq x :vl-$unit) (vl-ps-span "vl_key" (vl-print "$unit")))
          (t (vl-ps-span "vl_id" (vl-print-str x))))))



(define vl-pp-specialkey ((x vl-specialkey-p) &key (ps 'ps))
  (b* ((x (vl-specialkey-fix x)))
    (case x
      (:vl-null (vl-print "null"))
      (:vl-$    (vl-print "$"))
      (:vl-emptyqueue (vl-print "{ }"))
      (:vl-1step (vl-print "1step"))
      (otherwise (prog2$ (impossible) ps)))))


(define vl-binaryop-precedence ((x vl-binaryop-p))
  :returns (precedence posp :rule-classes :type-prescription)
  :prepwork ((local (Defthm vl-binaryop-fix-forward
                      (vl-binaryop-p (vl-binaryop-fix x))
                      :rule-classes
                      ((:forward-chaining :trigger-terms ((vl-binaryop-fix x)))))))
  (case (vl-binaryop-fix x)
    (:VL-BINARY-POWER    140)

    (:VL-BINARY-TIMES    130)
    (:VL-BINARY-DIV      130)
    (:VL-BINARY-REM      130)

    (:VL-BINARY-PLUS     120)
    (:VL-BINARY-MINUS    120)

    (:VL-BINARY-SHR      110)
    (:VL-BINARY-SHL      110)
    (:VL-BINARY-ASHR     110)
    (:VL-BINARY-ASHL     110)

    (:VL-BINARY-LT       100)
    (:VL-BINARY-LTE      100)
    (:VL-BINARY-GT       100)
    (:VL-BINARY-GTE      100)
    (:VL-INSIDE          100)

    (:VL-BINARY-EQ       90)
    (:VL-BINARY-NEQ      90)
    (:VL-BINARY-CEQ      90)
    (:VL-BINARY-CNE      90)
    (:vl-binary-wildeq   90)
    (:vl-binary-wildneq  90)

    (:VL-BINARY-BITAND   80)

    (:VL-BINARY-XOR      70)
    (:VL-BINARY-XNOR     70)

    (:VL-BINARY-BITOR    60)

    (:VL-BINARY-LOGAND   50)

    (:VL-BINARY-LOGOR    40)

    (:vl-implies         20)
    (:vl-equiv           20)

    ;; SystemVerilog assignment operators have lowest precedence
    (:vl-binary-assign       10)
    (:vl-binary-plusassign   10)
    (:vl-binary-minusassign  10)
    (:vl-binary-timesassign  10)
    (:vl-binary-divassign    10)
    (:vl-binary-remassign    10)
    (:vl-binary-andassign    10)
    (:vl-binary-orassign     10)
    (:vl-binary-xorassign    10)
    (:vl-binary-shlassign    10)
    (:vl-binary-shrassign    10)
    (:vl-binary-ashlassign   10)
    (:vl-binary-ashrassign   10)
    (otherwise (impossible))))


(define vl-expr-precedence ((x vl-expr-p))
  :short "Returns a symbol representing the operation that's being done at the top level."
  :returns (precedence posp :rule-classes :type-prescription)
  (vl-expr-case x
    :vl-unary 150
    :vl-binary (vl-binaryop-precedence x.op)
    :vl-qmark 30
    :otherwise 200))


(defmacro vl-pp-expr-special-atts ()
  ;; Special attributes that we will remove from expressions and not print, because
  ;; they are internal things that VL uses.
  ''("VL_ORIG_EXPR"
     "VL_EXPLICIT_PARENS"
     "VL_PARAMNAME"
     "VL_LINESTART"
     "VL_COLON_LINESTART"
     "VL_QMARK_LINESTART"))

(defthm vl-atts-p-of-vl-remove-keys
  (implies (force (vl-atts-p x))
           (vl-atts-p (vl-remove-keys keys x)))
  :hints(("Goal" :induct (len x))))

(defrule vl-atts-count-of-vl-remove-keys
  (<= (vl-atts-count (vl-remove-keys keys x))
      (vl-atts-count x))
  :rule-classes ((:rewrite) (:linear))
  :enable (vl-remove-keys vl-atts-count)
  :disable vl-atts-p-of-vl-remove-keys)


(define vl-atts-find-paramname ((atts vl-atts-p))
  ;; See vl-expr-scopesubst.  When we substitute a parameter's value into its
  ;; expression, we add a paramname annotation.
  :returns (paramname maybe-stringp :rule-classes :type-prescription)
  (b* ((look (hons-assoc-equal "VL_PARAMNAME" (vl-atts-fix atts)))
       ((unless look)
        nil)
       (val (cdr look))
       ((unless val) nil))
    (vl-expr-case val
      :vl-literal (vl-value-case val.val
                    :vl-string val.val.value
                    :otherwise nil)
      :otherwise nil)))

(define vl-leftright-string ((x vl-leftright-p))
  :returns (str stringp :rule-classes :type-prescription)
  (case (vl-leftright-fix x)
    (:left "<<")
    (otherwise ">>")))

(local (defthm hidname-equals-$root
         (implies (vl-hidname-p x)
                  (equal (equal x :vl-$root)
                         (not (stringp x))))
         :hints(("Goal" :in-theory (enable vl-hidname-p)))))

(local (defthm vl-expr-count-of-hons-assoc-equal
         (implies (and (cdr (hons-assoc-equal name atts))
                       (vl-atts-p atts))
                  (< (Vl-expr-count (cdr (hons-assoc-equal name atts)))
                     (vl-atts-count atts)))
         :hints (("goal" :induct (hons-assoc-equal name atts)
                  :expand ((vl-atts-count atts)
                           (vl-atts-p atts))
                  :in-theory (enable hons-assoc-equal
                                     vl-maybe-expr-count)))
         :rule-classes :linear))

(local (defthm alistp-when-vl-atts-p-rw
         (implies (vl-atts-p x)
                  (alistp x))
         :hints(("Goal" :in-theory (enable (tau-system))))))

(define vl-mimic-linestart ((atts vl-atts-p) &key
                            ((attname stringp) '"VL_LINESTART")
                            (ps 'ps))
  :short "Mechanism to try to indent expressions like the user had done."
  :long "<p>See in particular @(see parse-expressions), which annotates certain
         expressions with a @('VL_LINESTART') attribute that indicates that the
         expression was the first thing on a new line, and gives the column
         number that the expression was found on.</p>

         <p>This function should be called when we are ready to insert a
         newline but only if one was present in the original source code.  If
         the attributes indicate that there was a newline here, we insert a
         newline and indent appropriately.</p>"
  (b* (((unless atts)
        ps)
       (look (assoc-equal (string-fix attname) (vl-atts-fix atts)))
       ((unless look)
        ps)
       ((unless (vl-ps->mimic-linebreaks-p))
        ;; It's useful to be able to suppress linebreak mimicry, especially
        ;; when printing things like argument lists, where the arguments are
        ;; likely to have their own linebreaks but we're going to print them in
        ;; a custom way anyway.
        ps)
       ;; See vl-extend-atts-with-linestart.  The attribute should say how far
       ;; to indent to.
       (indent (if (and (vl-expr-p (cdr look))
                        (vl-expr-resolved-p (cdr look))
                        (<= 0 (vl-resolved->val (cdr look))))
                   (vl-resolved->val (cdr look))
                 0))
       (indent (max indent (vl-ps->autowrap-ind))))
    (vl-ps-seq
     (vl-println "")
     (vl-indent indent))))



(define vl-maybe-strip-outer-linestart ((x vl-expr-p))
  :returns (new-x vl-expr-p)
  :measure (vl-expr-count x)
  :verify-guards nil
  (b* ((x (vl-expr-fix x)))
    (vl-expr-case x
      :vl-special (if (assoc-equal "VL_LINESTART" x.atts)
                      (change-vl-special x :atts (vl-remove-keys '("VL_LINESTART") x.atts))
                    x)
      :vl-literal (if (assoc-equal "VL_LINESTART" x.atts)
                      (change-vl-literal x :atts (vl-remove-keys '("VL_LINESTART") x.atts))
                    x)
      :vl-index   (if (assoc-equal "VL_LINESTART" x.atts)
                      (change-vl-index x :atts (vl-remove-keys '("VL_LINESTART") x.atts))
                    x)

      :vl-unary
      ;; Any linestart is an initial linestart, so remove it.
      (if (assoc-equal "VL_LINESTART" x.atts)
          (change-vl-unary x :atts (vl-remove-keys '("VL_LINESTART") x.atts))
        x)

      :vl-binary
      ;; Any linestart is the linestart info for the operator, not for the
      ;; argument.  So go into the left argument and remove starting linestart
      ;; stuff from it, if applicable.
      (change-vl-binary x :left (vl-maybe-strip-outer-linestart x.left))

      :vl-qmark
      ;; Similar to the binary case
      (change-vl-qmark x :test (vl-maybe-strip-outer-linestart x.test))

      :vl-mintypmax
      (change-vl-mintypmax x :min (vl-maybe-strip-outer-linestart x.min))

      :vl-concat      (if (assoc-equal "VL_LINESTART" x.atts)
                          (change-vl-concat x :atts (vl-remove-keys '("VL_LINESTART") x.atts))
                        x)
      :vl-multiconcat (if (assoc-equal "VL_LINESTART" x.atts)
                          (change-vl-multiconcat x :atts (vl-remove-keys '("VL_LINESTART") x.atts))
                        x)
      :vl-stream      (if (assoc-equal "VL_LINESTART" x.atts)
                          (change-vl-stream x :atts (vl-remove-keys '("VL_LINESTART") x.atts))
                        x)
      :vl-call        (if (assoc-equal "VL_LINESTART" x.atts)
                          (change-vl-call x :atts (vl-remove-keys '("VL_LINESTART") x.atts))
                        x)
      :vl-cast    x ;; BOZO?
      :vl-inside  x ;; BOZO?

      :vl-tagged    (if (assoc-equal "VL_LINESTART" x.atts)
                        (change-vl-tagged x :atts (vl-remove-keys '("VL_LINESTART") x.atts))
                      x)

      :vl-pattern   (if (assoc-equal "VL_LINESTART" x.atts)
                        (change-vl-pattern x :atts (vl-remove-keys '("VL_LINESTART") x.atts))
                      x)
      :vl-eventexpr x ;; BOZO?
      ))
  ///
  (verify-guards vl-maybe-strip-outer-linestart)
  (defret vl-expr-count-of-vl-maybe-strip-outer-linestart
    (<= (vl-expr-count (vl-maybe-strip-outer-linestart x))
        (vl-expr-count x))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable vl-expr-count)))))

(defines vl-pp-expr
  :short "Main pretty-printer for an expression."

  :prepwork ((local (in-theory (disable acl2::member-of-cons))))
  :ruler-extenders :all
  (define vl-pp-indexlist ((x vl-exprlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-exprlist-count x) 10)
    (if (atom x)
        ps
      (vl-ps-seq (vl-print "[")
                 (vl-pp-expr (car x))
                 (vl-print "]")
                 (vl-pp-indexlist (cdr x)))))

  (define vl-pp-hidindex ((x vl-hidindex-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-hidindex-count x) 10)
    (b* (((vl-hidindex x)))
      (vl-ps-seq (if (eq x.name :vl-$root)
                     (vl-ps-span "vl_key"
                                 (vl-print "$root"))
                   (vl-print-wirename x.name))
                 (vl-pp-indexlist x.indices))))

  (define vl-pp-hidexpr ((x vl-hidexpr-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-hidexpr-count x) 10)
    (vl-hidexpr-case x
      :end (vl-print-wirename x.name)
      :dot (vl-ps-seq (vl-pp-hidindex x.first)
                      (vl-print ".")
                      (vl-pp-hidexpr x.rest))))

  (define vl-pp-scopeexpr ((x vl-scopeexpr-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-scopeexpr-count x) 10)
    (vl-scopeexpr-case x
      :end (vl-pp-hidexpr x.hid)
      :colon (vl-ps-seq (vl-pp-scopename x.first)
                        (vl-print "::")
                        (vl-pp-scopeexpr x.rest))))

  (define vl-pp-range ((x vl-range-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-range-count x) 10)
    (b* (((vl-range x)))
      (vl-ps-seq (vl-print "[")
                 (vl-pp-expr x.msb)
                 (vl-print ":")
                 (vl-pp-expr x.lsb)
                 (vl-print "]"))))

  (define vl-pp-plusminus ((x vl-plusminus-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-plusminus-count x) 10)
    (b* (((vl-plusminus x)))
      (vl-ps-seq (vl-print "[")
                 (vl-pp-expr x.base)
                 (vl-print-str (if x.minusp "-:" "+:"))
                 (vl-pp-expr x.width)
                 (vl-print "]"))))


  (define vl-pp-partselect ((x vl-partselect-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-partselect-count x) 10)
    (vl-partselect-case x
      :none ps
      :range (vl-pp-range x.range)
      :plusminus (vl-pp-plusminus x.plusminus)))

  (define vl-pp-arrayrange ((x vl-arrayrange-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-arrayrange-count x) 10)
    (vl-arrayrange-case x
      :none  ps
      :index (vl-ps-seq (vl-ps-span "vl_key" (vl-print " with "))
                        (vl-print "[")
                        (vl-pp-expr x.expr)
                        (vl-print "]"))
      :range (vl-ps-seq (vl-ps-span "vl_key" (vl-print " with "))
                        (vl-pp-range x.range))
      :plusminus (vl-ps-span "vl_key" (vl-print " with ")
                             (vl-pp-plusminus x.plusminus))))

  (define vl-pp-streamexpr ((x vl-streamexpr-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-streamexpr-count x) 10)
    (b* (((vl-streamexpr x)))
      (vl-ps-seq (vl-pp-expr x.expr)
                 (vl-pp-arrayrange x.part))))

  (define vl-pp-streamexprlist ((x vl-streamexprlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-streamexprlist-count x) 10)
    (if (atom x)
        ps
      (if (atom (cdr x))
          (vl-pp-streamexpr (car x))
        (vl-ps-seq (vl-pp-streamexpr (car x))
                   (vl-print ", ")
                   (vl-pp-streamexprlist (cdr x))))))

  (define vl-pp-valuerange ((x vl-valuerange-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-valuerange-count x) 10)
    (vl-valuerange-case x
      :valuerange-single (vl-pp-expr x.expr)
      :valuerange-range (vl-ps-seq (vl-print "[")
                                   (vl-pp-expr x.low)
                                   (vl-print ":")
                                   (vl-pp-expr x.high)
                                   (vl-print "]"))))

  (define vl-pp-valuerangelist ((x vl-valuerangelist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-valuerangelist-count x) 10)
    (if (atom x)
        ps
      (if (atom (cdr x))
          (vl-pp-valuerange (car x))
        (vl-ps-seq (vl-pp-valuerange (car x))
                   (vl-print ", ")
                   (vl-pp-valuerangelist (cdr x))))))

  (define vl-pp-patternkey ((x vl-patternkey-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-patternkey-count x) 10)
    (vl-patternkey-case x
      :expr (vl-pp-expr x.key)
      :structmem (vl-ps-span "vl_id" (vl-print-str (vl-maybe-escape-identifier x.name)))
      :type (vl-pp-datatype x.type)
      :default (vl-print "default")))

  (define vl-pp-keyvallist ((x vl-keyvallist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-keyvallist-count x) 10)
    (b* ((x (vl-keyvallist-fix x)))
      (if (atom x)
          ps
        (vl-ps-seq (vl-pp-patternkey (caar x))
                   (vl-print ":")
                   (vl-pp-expr (cdar x))
                   (if (atom (cdr x))
                       ps
                     (vl-ps-seq (vl-print ", ")
                                (vl-pp-keyvallist (cdr x))))))))

  (define vl-pp-assignpat ((x vl-assignpat-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-assignpat-count x) 10)
    :ruler-extenders :all
    (vl-ps-seq (vl-print "'{")
               (vl-assignpat-case x
                 :positional (vl-pp-exprlist x.vals)
                 :keyval (vl-pp-keyvallist x.pairs)
                 :repeat (vl-ps-seq (vl-pp-expr x.reps)
                                    (vl-print " { ")
                                    (vl-pp-exprlist x.vals)
                                    (vl-print " }")))
               (vl-print "}")))

  (define vl-pp-casttype ((x vl-casttype-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-casttype-count x) 10)
    (vl-casttype-case x
      :type (vl-pp-datatype x.type)
      :size (vl-ps-seq (vl-print "(") (vl-pp-expr x.size) (vl-print ")"))
      :signedness (vl-ps-span "vl_key"
                              (if x.signedp
                                  (vl-print "signed")
                                (vl-print "unsigned")))
      :const (vl-ps-span "vl_key" (vl-print "const"))))


  (define vl-pp-expr ((x vl-expr-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-expr-count x) 10)
    :ruler-extenders :all
    (b* ((atts (vl-expr->atts x))
         (origexpr (cdr (assoc-equal "VL_ORIG_EXPR" atts)))
         ((when (and origexpr
                     (vl-ps->use-origexprs-p)))
          (vl-pp-expr origexpr))
         (unspecial-atts (vl-remove-keys (vl-pp-expr-special-atts) atts)))
      (vl-expr-case x

        :vl-special (vl-ps-seq
                     (vl-mimic-linestart atts)
                     (vl-pp-specialkey x.key))

        :vl-literal (vl-ps-seq
                     (vl-mimic-linestart atts)
                     (vl-pp-value x.val)
                     (vl-when-html
                      (let ((paramname (vl-atts-find-paramname atts)))
                        (if paramname
                            (vl-ps-seq (vl-print-markup "<span class='vl_paramname'>")
                                       (vl-print-str paramname)
                                       (vl-print-markup "</span>"))
                          ps))))

        :vl-index (vl-ps-seq (vl-mimic-linestart atts)
                             (vl-pp-scopeexpr x.scope)
                             (vl-pp-indexlist x.indices)
                             (vl-pp-partselect x.part))

        :vl-unary (b* ((prec (vl-expr-precedence x))
                       (arg-prec (vl-expr-precedence x.arg))
                       (want-parens (or* (<= arg-prec prec)
                                         (and (vl-ps->copious-parens-p)
                                              ;; Special case: even with copious parens, don't print
                                              ;; parens around plain numbers and wire references
                                              (vl-expr-case x.arg
                                                :vl-index nil
                                                :vl-literal nil
                                                :otherwise t))))
                       ((when (member x.op '(:vl-unary-postinc
                                             :vl-unary-postdec)))
                        (vl-ps-seq
                         ;; For post-increment operators we don't bother with linestart because
                         ;; it'd just be weird to have a newline between the arg and the ++/--.
                         (if want-parens (vl-print "(") ps)
                         (vl-pp-expr x.arg)
                         (if unspecial-atts (vl-pp-atts unspecial-atts) ps)
                         (vl-print-str (vl-unaryop-string x.op))
                         (vl-println? ""))))
                    (vl-ps-seq
                     ;; For any other unary operator, the linestart indicates that a newline
                     ;; comes before the operator itself.
                     (vl-mimic-linestart atts)
                     (vl-print-str (vl-unaryop-string x.op))
                     (if unspecial-atts (vl-pp-atts unspecial-atts) ps)
                     (vl-print-str " ")
                     (if want-parens (vl-print "(") ps)
                     (vl-pp-expr x.arg)
                     (if want-parens (vl-print ")") ps)
                     (vl-println? "")))

        :vl-binary (b* ((prec         (vl-expr-precedence x))
                        (left-prec    (vl-expr-precedence x.left))
                        (right-prec   (vl-expr-precedence x.right))
                        (right-assocp (member x.op '(:vl-implies :vl-equiv)))
                        (left-parens  (or* (< left-prec prec)
                                           (and right-assocp (eql left-prec prec))
                                           (hons-assoc-equal "VL_EXPLICIT_PARENS" (vl-expr->atts x.left))
                                           ;; Special case: even with copious parens, don't print
                                           ;; parens around plain numbers and wire references
                                           (and* (vl-ps->copious-parens-p)
                                                 (vl-expr-case x.left
                                                   :vl-index nil
                                                   :vl-literal nil
                                                   :otherwise t))))
                        (right-parens (or* (< right-prec prec)
                                           (and (not right-assocp) (eql right-prec prec))
                                           (hons-assoc-equal "VL_EXPLICIT_PARENS"
                                                             (vl-expr->atts x.right))
                                           ;; Special case: even with copious parens, don't print
                                           ;; parens around plain numbers and wire references
                                           (and* (vl-ps->copious-parens-p)
                                                 (vl-expr-case x.right
                                                   :vl-index nil
                                                   :vl-literal nil
                                                   :otherwise t))
                                           (b* ((rightop (vl-expr-case x.right
                                                           :vl-binary x.right.op
                                                           :otherwise nil)))
                                             (or (and (eq x.op :vl-binary-bitand)
                                                      (eq rightop :vl-binary-bitand))
                                                 (and (eq x.op :vl-binary-bitor)
                                                      (eq rightop :vl-binary-bitor)))))))
                     ;; BOZO used to be a special case for assignment
                     ;; operators, but I think it boils down to precedence and
                     ;; should work OK -- am I missing something?
                     (vl-ps-seq
                      (if left-parens (vl-print "(") ps)
                      (vl-pp-expr x.left)
                      (if left-parens (vl-print ")") ps)
                      (vl-print " ")
                      ;; For all binary operators, linestart indicates that a
                      ;; newline comes immediately before or after the
                      ;; operator.  We will put the newline before the operator
                      ;; either way, as God so clearly intended.
                      (vl-mimic-linestart atts)
                      (vl-print-str (vl-binaryop-string x.op))
                      (if unspecial-atts (vl-pp-atts unspecial-atts) ps)
                      (vl-println? " ")
                      (if right-parens (vl-print "(") ps)
                      (vl-pp-expr (vl-maybe-strip-outer-linestart x.right))
                      (if right-parens (vl-print ")") ps)
                      (vl-println? "")))

        :vl-qmark (b* ((prec (vl-expr-precedence x))
                       (copious-parens (vl-ps->copious-parens-p))
                       (test-parens (or* (<= (vl-expr-precedence x.test) prec) copious-parens))
                       (then-parens (or* (<= (vl-expr-precedence x.then) prec) copious-parens))
                       (else-parens (or* (<  (vl-expr-precedence x.else) prec) copious-parens)))
                    (vl-ps-seq
                     (if test-parens (vl-print "(") ps)
                     (vl-pp-expr x.test)
                     (if test-parens (vl-print ")") ps)
                     (vl-print " ")
                     (vl-mimic-linestart x.atts :attname "VL_QMARK_LINESTART")
                     (vl-print "? ")
                     (if unspecial-atts (vl-ps-seq (vl-pp-atts unspecial-atts) (vl-print " ")) ps)
                     (vl-println? "")
                     (if then-parens (vl-print "(") ps)
                     (vl-pp-expr (vl-maybe-strip-outer-linestart x.then))
                     (if then-parens (vl-print ")") ps)
                     (vl-print " ")
                     (vl-mimic-linestart x.atts :attname "VL_COLON_LINESTART")
                     (vl-print ": ")
                     (if else-parens (vl-print "(") ps)
                     (vl-pp-expr (vl-maybe-strip-outer-linestart x.else))
                     (if else-parens (vl-print ")") ps)))

        :vl-mintypmax (vl-ps-seq
                       ;; Unlike other operands, I put mintypmax expressions in their own
                       ;; parens so that I'm basically justified in treating them as having
                       ;; operand-level precedence.
                       (vl-print "(")
                       (vl-pp-expr x.min)
                       (vl-println? " : ")
                       (vl-pp-expr x.typ)
                       (vl-println? " : ")
                       (vl-pp-expr x.max)
                       (vl-println? ")"))

        :vl-concat (vl-ps-seq (vl-mimic-linestart atts)
                              (vl-print "{")
                              (vl-pp-exprlist x.parts)
                              (vl-print "}"))

        :vl-multiconcat (vl-ps-seq (vl-mimic-linestart atts)
                                   (vl-print "{")
                                   (vl-pp-expr x.reps)
                                   (vl-print "{")
                                   (vl-pp-exprlist x.parts)
                                   (vl-print "}}"))

        :vl-stream (vl-ps-seq (vl-mimic-linestart atts)
                              (vl-print "{")
                              (vl-print-str (vl-leftright-string x.dir))
                              (vl-print " ")
                              (vl-slicesize-case x.size
                                :expr (vl-ps-seq (vl-pp-expr x.size.expr)
                                                 (vl-print " "))
                                :type (vl-ps-seq (vl-pp-datatype x.size.type)
                                                 (vl-print " "))
                                :otherwise ps)
                              (vl-print "{")
                              (vl-pp-streamexprlist x.parts)
                              (vl-print "}}"))

        :vl-call (vl-ps-seq (vl-mimic-linestart atts)
                            (if (and x.systemp
                                     (vl-scopeid-p x.name)
                                     (stringp x.name))
                                (vl-ps-seq (vl-ps-span "vl_sys")
                                           (vl-print-str x.name))
                              (vl-pp-scopeexpr x.name))
                            (vl-print "(")
                            (if x.typearg
                                (vl-ps-seq (vl-pp-datatype x.typearg)
                                           (if (consp x.plainargs)
                                               (vl-print ", ")
                                             ps))
                              ps)
                            (vl-pp-maybe-exprlist x.plainargs)
                            (if (and (consp x.plainargs) (consp x.namedargs))
                                (vl-print ", ")
                              ps)
                            (vl-pp-call-namedargs x.namedargs)
                            (vl-print ")"))

        :vl-cast (vl-ps-seq
                  ;; Do we ever need parens around the type?
                  (vl-pp-casttype x.to)
                  (vl-print "' (")
                  (vl-pp-expr x.expr)
                  (vl-print ")"))

        :vl-inside (b* ((parens (or* (< (vl-expr-precedence x.elem) (vl-expr-precedence x))
                                     (vl-ps->copious-parens-p))))
                     (vl-ps-seq (if parens (vl-print "(") ps)
                                (vl-pp-expr x.elem)
                                (if parens (vl-print ")") ps)
                                (vl-print " ")
                                (vl-mimic-linestart atts)
                                (vl-print "inside {")
                                (vl-pp-valuerangelist x.set)
                                (vl-print "}")))

        :vl-tagged (b* ((parens (and x.expr
                                     (or* (< (vl-expr-precedence x.expr) (vl-expr-precedence x))
                                          (vl-ps->copious-parens-p)))))
                     (vl-ps-seq (vl-mimic-linestart atts)
                                (vl-ps-span "vl_key" (vl-print "tagged "))
                                (vl-print-str x.tag)
                                (vl-print " ")
                                (if x.expr
                                    (vl-ps-seq (if parens (vl-print "(") ps)
                                               (vl-pp-expr x.expr)
                                               (if parens (vl-print ")") ps))
                                  ps)))

        :vl-pattern (vl-ps-seq
                     ;; Do we ever need parens around the type?
                     (vl-mimic-linestart atts)
                     (if x.pattype (vl-pp-datatype x.pattype) ps)
                     (vl-pp-assignpat x.pat))

        :vl-eventexpr (vl-ps-seq
                       ;; BOZO atts?
                       (vl-print "@(")
                       (vl-pp-evatomlist x.atoms)
                       (vl-print ")")))))

  (define vl-pp-exprlist ((x vl-exprlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-exprlist-count x) 10)
    (if (atom x)
        ps
      (vl-ps-seq (vl-pp-expr (car x))
                 (if (atom (cdr x))
                     ps
                   (vl-ps-seq (vl-print ", ")
                              (vl-pp-exprlist (cdr X)))))))

  (define vl-pp-maybe-exprlist ((x vl-maybe-exprlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-maybe-exprlist-count x) 10)
    (if (atom x)
        ps
      (vl-ps-seq (if (car x) (vl-pp-expr (car x)) ps)
                 (if (atom (cdr x))
                     ps
                   (vl-ps-seq (vl-print ", ")
                              (vl-pp-maybe-exprlist (cdr X)))))))

  (define vl-pp-call-namedargs ((x vl-call-namedargs-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-call-namedargs-count x) 10)
    (b* ((x (vl-call-namedargs-fix x)))
      (if (atom x)
          ps
      (vl-ps-seq (vl-print-str ".")
                 (vl-print-str (caar x))
                 (vl-print-str "(")
                 (if (cdar x) (vl-pp-expr (cdar x)) ps)
                 (vl-print-str ")")
                 (if (atom (cdr x))
                     ps
                   (vl-ps-seq (vl-print ", ")
                              (vl-pp-call-namedargs (cdr X))))))))

  (define vl-pp-atts-aux ((x vl-atts-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-atts-count x) 10)
    :ruler-extenders :all
    (b* ((x (vl-atts-fix x)))
      (if (atom x)
          ps
        (vl-ps-seq (vl-print-str (caar x))
                   (if (cdar x)
                       (vl-ps-seq (vl-print " = ")
                                  (vl-pp-expr (cdar x)))
                     ps)
                   (if (atom (cdr x))
                       ps
                     (vl-ps-seq (vl-print ", ")
                                (vl-pp-atts-aux (cdr x))))))))

  (define vl-pp-atts ((x vl-atts-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-atts-count x) 20)
    (vl-ps-seq (vl-print "(* ")
               (vl-pp-atts-aux x)
               (vl-print " *)")))

  (define vl-pp-datatype ((x vl-datatype-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-datatype-count x) 10)
    (vl-datatype-case x
      (:vl-coretype
       (vl-ps-seq (vl-ps-span "vl_key" (vl-print-str (vl-coretypename-string x.name)))
                  ;; BOZO this isn't quite right -- we shouldn't print the
                  ;; signedness if it's not applicable to this kind of type.
                  ;; signing, if applicable
                  (cond ((member x.name '(:vl-byte :vl-shortint :vl-int :vl-longint :vl-integer))
                         ;; Default is signed.  Only need to print anything if it's unsigned.
                         (if x.signedp
                             ps
                           (vl-ps-span "vl_key" (vl-print-str " unsigned"))))

                        ((member x.name '(:vl-time :vl-bit :vl-logic :vl-reg))
                         ;; Default is unsigned.  Only need to print anything if it's signed.
                         (if x.signedp
                             (vl-ps-span "vl_key" (vl-print-str " signed"))
                           ps))

                        (t
                         ;; other core types don't have an optional signing.  they'd better
                         ;; be marked as unsigned or it doesn't make sense
                         (progn$ (or (not x.signedp)
                                     (raise "core type ~x0 marked as signed? ~x1" x.name x))
                                 ps)))
                  (if (consp x.pdims)
                      (vl-ps-seq (vl-print " ")
                                 (vl-pp-dimensionlist x.pdims))
                    ps)))

      (:vl-struct
       (vl-ps-seq (vl-ps-span "vl_key"
                              (vl-print "struct ")
                              (if x.packedp
                                  (vl-ps-seq (vl-print "packed ")
                                             (if x.signedp
                                                 (vl-print "signed ")
                                               ps))
                                ps))
                  (vl-println "{")
                  (vl-progindent-block (vl-pp-structmemberlist x.members))
                  (vl-progindent)
                  (vl-print "}")
                  (if (consp x.pdims)
                      (vl-ps-seq (vl-print " ")
                                 (vl-pp-dimensionlist x.pdims))
                    ps)))

      (:vl-union
       (vl-ps-seq (vl-ps-span "vl_key"
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
                  (vl-progindent-block (vl-pp-structmemberlist x.members))
                  (vl-progindent)
                  (vl-print "} ")
                  (vl-pp-dimensionlist x.pdims)))

      (:vl-enum
       (vl-ps-seq (vl-ps-span "vl_key" (vl-print "enum "))
                  (vl-pp-datatype x.basetype)
                  (vl-println " {")
                  (vl-progindent-block (vl-pp-enumitemlist x.items))
                  (vl-progindent)
                  (vl-print "}")
                  (if (consp x.pdims)
                      (vl-ps-seq (vl-print " ")
                                 (vl-pp-dimensionlist x.pdims))
                    ps)))

      (:vl-usertype
       (vl-ps-seq (vl-pp-scopeexpr x.name)
                  ;; (if x.res
                  ;;     (vl-ps-seq (vl-print "=[") (vl-pp-datatype x.res) (vl-print "] "))
                  ;;   ps)
                  (if (consp x.pdims)
                      (vl-ps-seq (vl-print " ")
                                 (vl-pp-dimensionlist x.pdims))
                    ps)))))

  (define vl-pp-structmemberlist ((x vl-structmemberlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-structmemberlist-count x) 10)
    (if (atom x)
        ps
      (vl-ps-seq (vl-pp-structmember (car x))
                 (vl-pp-structmemberlist (cdr x)))))

  (define vl-pp-structmember ((x vl-structmember-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-structmember-count x) 10)
    :ruler-extenders :all
    (b* (((vl-structmember x) x)
         (udims (vl-datatype->udims x.type)))
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (if x.rand
                     (vl-ps-span "vl_key"
                                 (vl-print-str (vl-randomqualifier-string x.rand))
                                 (vl-print " "))
                   ps)
                 (vl-pp-datatype x.type)
                 (vl-print " ")
                 (vl-print-wirename x.name)
                 (if (consp udims)
                     (vl-ps-seq (vl-print " ")
                                (vl-pp-dimensionlist udims))
                   ps)
                 (if x.rhs
                     (vl-ps-seq (vl-print " = ")
                                (vl-pp-expr x.rhs))
                   ps)
                 (vl-println " ;"))))

  (define vl-pp-dimension ((x vl-dimension-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-dimension-count x) 10)
    (vl-dimension-case x
      :unsized  (vl-print "[]")
      :star     (vl-print "[*]")
      :range    (vl-pp-range x.range)
      :datatype (vl-ps-seq (vl-print "[")
                           (vl-pp-datatype x.type)
                           (vl-print "]"))
      :queue    (vl-ps-seq (vl-print "[$")
                           (if x.maxsize
                               (vl-ps-seq (vl-print " : ")
                                          (vl-pp-expr x.maxsize))
                             ps)
                           (vl-print "]"))))

  (define vl-pp-dimensionlist ((x vl-dimensionlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-dimensionlist-count x) 10)
    (if (atom x)
        ps
      (vl-ps-seq (vl-pp-dimension (car x))
                 (vl-pp-dimensionlist (cdr x)))))

  (define vl-pp-enumitem ((x vl-enumitem-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-enumitem-count x) 10)
    :ruler-extenders :all
    (b* (((vl-enumitem x) x))
      (vl-ps-seq (vl-progindent)
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
                                      (vl-print (vl-resolved->val msb))
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
    :measure (two-nats-measure (vl-enumitemlist-count x) 10)
    (if (atom x)
        ps
      (vl-ps-seq (vl-pp-enumitem (car x))
                 (vl-pp-enumitemlist (cdr x)))))


  (define vl-pp-evatom ((x vl-evatom-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-evatom-count x) 10)
    (b* (((vl-evatom x)))
      (case x.type
        (:vl-noedge  (vl-pp-expr x.expr))
        (:vl-posedge (vl-ps-seq (vl-ps-span "vl_key" (vl-print "posedge "))
                                (vl-pp-expr x.expr)))
        (:vl-negedge (vl-ps-seq (vl-ps-span "vl_key" (vl-print "negedge "))
                                (vl-pp-expr x.expr)))
        (:vl-edge    (vl-ps-seq (vl-ps-span "vl_key" (vl-print "edge "))
                                (vl-pp-expr x.expr)))
        (otherwise   (progn$ (impossible)
                             ps))))
    :prepwork
    ((local (defthm vl-evatom->type-forward
              (or (equal (vl-evatom->type x) :vl-noedge)
                  (equal (vl-evatom->type x) :vl-posedge)
                  (equal (vl-evatom->type x) :vl-negedge)
                  (equal (vl-evatom->type x) :vl-edge))
              :rule-classes ((:forward-chaining :trigger-terms ((vl-evatom->type x))))
              :hints(("Goal" :cases ((vl-evatomtype-p (vl-evatom->type x)))))))))

  (define vl-pp-evatomlist ((x vl-evatomlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-evatomlist-count x) 10)
    (cond ((atom x)
           ps)
          ((atom (cdr x))
           (vl-pp-evatom (car x)))
          (t
           (vl-ps-seq (vl-pp-evatom (car x))
                      (vl-ps-span "vl_key" (vl-print " or "))
                      (vl-pp-evatomlist (cdr x))))))

  ///
  (deffixequiv-mutual vl-pp-expr))


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
  :short "Pretty-print the \"original,\" un-transformed version of an
expression."
  :long "<p>This is like @(see vl-pp-expr) but, if @('x') has a
@('VL_ORIG_EXPR') attribute, we actually pretty-print the original version of
@('x') rather than the current version (which may be simplified, and hence not
correspond as closely to the original source code.)  Specifically, the
elaboration transform may replace certain subexpressions with constants and
leave behind an annotation giving the original version of @('x').</p>"
  (b* ((misc (vl-ps->misc))
       (prev-p (vl-ps->use-origexprs-p)))
    (vl-ps-seq
     (if (not prev-p)
         (vl-ps-update-use-origexprs t)
       ps)
     (vl-pp-expr x)
     (vl-ps-update-misc misc))))

(define vl-pps-origexpr ((x vl-expr-p))
  :returns (pretty-x stringp :rule-classes :type-prescription)
  :parents (expr-tools verilog-printing)
  :short "Pretty-print the \"original,\" un-transformed version of an
expression into a string."
  (with-local-ps (vl-pp-origexpr x)))


(define vl-direction-string ((x vl-direction-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-direction-p)))
  (case (vl-direction-fix x)
    (:vl-input  "input")
    (:vl-output "output")
    (:vl-inout  "inout")
    (otherwise  (or (impossible) ""))))


(define vl-pps-range ((x vl-range-p))
  :returns (str stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-range x)))

(define vl-pp-rangelist ((x vl-rangelist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-range (car x))
               (vl-pp-rangelist (cdr x)))))



(define vl-pp-interfaceport ((x vl-interfaceport-p) &key (ps 'ps))
  ;; Print an interface port like `simplebus.master foo [3:0]`
  (b* (((vl-interfaceport x) x))
    (vl-ps-seq (vl-print-modname x.ifname)
               (if x.modport
                   (vl-ps-seq (vl-print ".")
                              (vl-ps-span "vl_id" (vl-print-str (vl-maybe-escape-identifier x.modport))))
                 ps)
               (vl-print " ")
               (vl-ps-span "vl_id" (vl-print-str (vl-maybe-escape-identifier x.name)))
               (if (consp x.udims)
                   (vl-ps-seq (vl-print " ")
                              (vl-pp-dimensionlist x.udims))
                 ps))))

(define vl-pp-regularport ((x vl-regularport-p) &key (ps 'ps))
  (b* (((vl-regularport x) x)

       ((when (and (not x.name)
                   (not x.expr)))
        ;; A truly blank port... we'll put in a comment.
        (vl-ps-span "vl_cmt" (vl-println? "/* blank port */")))

       ((unless x.name)
        ;; Just a complex expression like foo[3:0] with no name.
        (vl-pp-expr x.expr))

       ((when (and x.expr
                   (vl-idexpr-p x.expr)
                   (equal (vl-idexpr->name x.expr) x.name)))
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

(define vl-pp-port ((x vl-port-p) &key (ps 'ps))
  (b* ((x (vl-port-fix x)))
    (if (eq (tag x) :vl-interfaceport)
        (vl-pp-interfaceport x)
      (vl-pp-regularport x))))

(define vl-pp-portlist ((x vl-portlist-p) &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-pp-port (car x)))
        (t
         (vl-ps-seq (vl-pp-port (car x))
                    (vl-println? ", ")
                    (vl-pp-portlist (cdr x))))))

(define vl-pp-regularportlist ((x vl-regularportlist-p) &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-pp-regularport (car x)))
        (t
         (vl-ps-seq (vl-pp-regularport (car x))
                    (vl-println? ", ")
                    (vl-pp-regularportlist (cdr x))))))

(define vl-pp-interfaceportlist ((x vl-interfaceportlist-p) &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-pp-interfaceport (car x)))
        (t
         (vl-ps-seq (vl-pp-interfaceport (car x))
                    (vl-println? ", ")
                    (vl-pp-interfaceportlist (cdr x))))))




(define vl-pp-portdecl ((x vl-portdecl-p) &key (ps 'ps))
  (b* (((vl-portdecl x) x))
    (vl-ps-seq (vl-progindent)
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key"
                           (vl-println? (vl-direction-string x.dir)))
               (vl-print " ")
               (if x.nettype
                   (vl-ps-seq (vl-ps-span "vl_key"
                                          (vl-println? (vl-nettypename-string x.nettype)))
                              (vl-print " "))
                 ps)
               (if (and (vl-datatype-case x.type :vl-coretype)
                        (eq (vl-coretype->name x.type) :vl-logic))
                   ;; logic type, which is the default -- just print the
                   ;; signedness/packed dims
                   (vl-ps-seq (if (vl-coretype->signedp x.type)
                                  (vl-ps-span "vl_key" (vl-print-str "signed "))
                                ps)
                              (vl-pp-dimensionlist (vl-coretype->pdims x.type))
                              (if (consp (vl-coretype->pdims x.type))
                                  (vl-print " ")
                                ps))
                 (vl-ps-seq (vl-pp-datatype x.type)
                            (vl-print " ")))
               (vl-print-wirename x.name)
               (let ((udims (vl-datatype->udims x.type)))
                 (if (consp udims)
                     (vl-ps-seq (vl-print " ")
                                (vl-pp-dimensionlist udims))
                   ps))
               (if x.default
                   (vl-ps-seq (vl-print " = ")
                              (vl-pp-expr x.default))
                 ps)
               (vl-println " ;"))))

(define vl-pp-portdecllist ((x vl-portdecllist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-portdecl (car x))
               (vl-pp-portdecllist (cdr x)))))


;; for debugging
(define vl-pp-ansi-portdecl ((x vl-ansi-portdecl-p) &key (ps 'ps))
  (b* (((vl-ansi-portdecl x)))
    (vl-ps-seq (vl-progindent)
               (if x.atts
                   (vl-ps-seq (vl-pp-atts x.atts)
                              (vl-print " "))
                 ps)
               (if x.dir
                   (vl-ps-seq
                    (vl-ps-span "vl_key"
                                (vl-println? (vl-direction-string x.dir)))
                    (vl-print " "))
                 ps)
               (if x.nettype
                   (vl-ps-seq
                    (vl-ps-span "vl_key"
                                (vl-println? (vl-nettypename-string x.nettype)))
                    (vl-print " "))
                 ps)
               (if x.typename
                   (vl-ps-seq (vl-print-str x.typename) (vl-print " "))
                 ps)
               (if x.type
                   (vl-ps-seq (vl-pp-datatype x.type) (vl-print " "))
                 ps)
               (if x.signedness
                   (if (eq x.signedness :vl-signed)
                       (vl-print "signed ")
                     (vl-print "unsigned "))
                 ps)
               (if x.pdims
                   (vl-ps-seq (vl-pp-dimensionlist x.pdims)
                              (vl-print " "))
                 ps)
               (vl-print-wirename x.name)
               (if x.udims
                   (vl-ps-seq (vl-print " ")
                              (vl-pp-dimensionlist x.pdims))
                 ps))))




(define vl-pp-paramdecl ((x vl-paramdecl-p) &key (ps 'ps))
  (b* (((vl-paramdecl x) x))
    (vl-ps-seq (vl-progindent)
               (if x.atts
                   (vl-ps-seq (vl-pp-atts x.atts)
                              (vl-print " "))
                 ps)
               (vl-ps-span "vl_key"
                           (if x.localp
                               (vl-print "localparam ")
                             (vl-print "parameter ")))
               (vl-paramtype-case x.type
                 (:vl-implicitvalueparam
                  ;; Something like "parameter a = 1" or "parameter signed [3:0] a = 2"
                  ;; The signed part, if any, comes first.
                  (vl-ps-seq (case x.type.sign
                               (:vl-signed   (vl-ps-span "vl_key" (vl-print "signed ")))
                               (:vl-unsigned (vl-ps-span "vl_key" (vl-print "unsigned ")))
                               (otherwise    ps))
                             (if x.type.range
                                 (vl-ps-seq (vl-pp-range x.type.range)
                                            (vl-print " "))
                               ps)
                             (vl-print-wirename x.name)
                             (if x.type.default
                                 (vl-ps-seq (vl-print " = ")
                                            (vl-pp-expr x.type.default))
                               ps)))

                 (:vl-explicitvalueparam
                  ;; Something like "parameter integer a = 1";
                  (vl-ps-seq (vl-pp-datatype x.type.type)
                             (vl-print " ")
                             (vl-print-wirename x.name)
                             (let ((udims (vl-datatype->udims x.type.type)))
                               (if (consp udims)
                                   (vl-ps-seq (vl-print " ")
                                              (vl-pp-dimensionlist udims))
                                 ps))
                             (if x.type.default
                                 (vl-ps-seq (vl-print " = ")
                                            (vl-pp-expr x.type.default))
                               ps)))

                 (:vl-typeparam
                  ;; Something like "parameter type foo = struct { int a; };"
                  (vl-ps-seq (vl-ps-span "vl_key" (vl-print "type "))
                             (vl-print-wirename x.name)
                             (if x.type.default
                                 (vl-ps-seq (vl-print " ")
                                            (vl-pp-datatype x.type.default))
                               ps))))

               ;; BOZO do we want to print a closing semicolon here?  Almost
               ;; always there is supposed to be one, but not in certain cases
               ;; such as in parameter_port_declaration lists.  But I don't know
               ;; if we're ever going to try to print a parameter_port_declaration
               ;; list, so for now I think I'm just going to print the semicolon.
               (vl-println ";"))))

(define vl-pp-paramdecllist ((x vl-paramdecllist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-paramdecl (car x))
               (vl-pp-paramdecllist (cdr x)))))



(define vl-cstrength-string ((x vl-cstrength-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-cstrength-p)))
  (case (vl-cstrength-fix x)
    (:vl-large  "large")
    (:vl-medium "medium")
    (:vl-small  "small")
    (otherwise  (or (impossible) ""))))

(define vl-lifetime-string ((x vl-lifetime-p))
  (case (vl-lifetime-fix x)
    ('nil          "")
    (:vl-static    "static")
    (:vl-automatic "automatic")
    (otherwise (progn$ (impossible) ""))))

(define vl-pp-lifetime ((x vl-lifetime-p) &key (ps 'ps))
  (case (vl-lifetime-fix x)
    (:vl-static (vl-ps-span "vl_key" (vl-print-str "static ")))
    (:vl-automatic (vl-ps-span "vl_key" (vl-print-str "automatic ")))
    ('nil    ps)
    (otherwise (progn$ (impossible) ps))))

(define vl-pp-gatedelay ((x vl-gatedelay-p) &key (ps 'ps))
  (b* (((vl-gatedelay x) x))
    (cond
     ((and (hide (equal x.rise x.fall))
           (hide (equal x.fall x.high))
           (vl-expr-resolved-p x.rise)
           (<= 0 (vl-resolved->val x.rise)))
      ;; Almost always the delays should just be #3, etc.
      (vl-ps-seq
       (vl-print "#")
       (vl-ps-span "vl_int"
                   (vl-print-nat (vl-resolved->val x.rise)))))

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

(defmacro vl-pp-vardecl-special-atts ()
  ;; Attributes that will get turned into nice comments.
  ''("VL_IMPLICIT"
     ;; Historically we also included VL_PORT_IMPLICIT and printed the net
     ;; declarations.  But that's chatty and doesn't work correctly with
     ;; ANSI-style ports lists where it's illegal to re-declare the net.  So,
     ;; now, we hide any VL_PORT_IMPLICIT ports separately; see vl-pp-vardecl.
     "VL_UNUSED"
     "VL_MAYBE_UNUSED"
     "VL_UNSET"
     "VL_MAYBE_UNSET"
     "VL_DESIGN_WIRE"))

(define vl-pp-vardecl-atts-begin ((x vl-atts-p) &key (ps 'ps))
; Removed after v7-2 by Matt K. since the definition is non-recursive:
; :measure (vl-atts-count x)
  (b* ((x (vl-atts-fix x))
       ((unless x)
        ps)
       (x (vl-remove-keys (vl-pp-vardecl-special-atts) x))
       ((unless x)
        ps)
       ((when (and (tuplep 1 x)
                   (equal (caar x) "VL_FOR")))
        (b* ((str (cdar x))
             (strval (and str
                          (vl-expr-case str
                            :vl-literal (vl-value-case str.val
                                          :vl-string str.val.value
                                          :otherwise nil)
                            :otherwise nil))))
          (if (not strval)
              (prog2$
               (raise "Expected FROM to contain a string.")
               ps)
            (vl-ps-seq
             (vl-println "")
             (vl-progindent)
             (vl-ps-span "vl_cmt"
                         (vl-print "/* For ")
                         (vl-print-str strval)
                         (vl-println " */")))))))
    (vl-ps-seq (vl-println "")
               (vl-progindent)
               (vl-pp-atts x)
               (vl-println ""))))

(define vl-pp-vardecl-atts-end ((x vl-atts-p) &key (ps 'ps))
  (b* ((x (vl-atts-fix x))
       ((unless x)
        (vl-println ""))
       (cars    (acl2::alist-keys x))
       (notes   nil)
       (notes   (if (member-equal "VL_IMPLICIT" cars)
                    (cons "Implicit" notes)
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

(define vl-vardecl-hiddenp ((x vl-vardecl-p))
  (b* (((vl-vardecl x) x))
    (or
     ;; As a special hack, we now do not print any net declarations that are
     ;; implicitly derived from the port.  These were just noisy and may not be
     ;; allowed if we're printing the nets for an ANSI style module.  See also
     ;; make-implicit-wires.
     (assoc-equal "VL_PORT_IMPLICIT" x.atts)
     ;; As another special hack, hide declarations that we add for function and
     ;; task inputs and function return values.
     (assoc-equal "VL_HIDDEN_DECL_FOR_TASKPORT" x.atts)
     ;; And similarly let's hide any vardecls that are introduced via ansi
     ;; style ports.
     (assoc-equal "VL_ANSI_PORT_VARDECL" x.atts)
     )))

(define vl-pp-rhs ((x vl-rhs-p) &key (ps 'ps))
  (vl-rhs-case x
    :vl-rhsexpr (vl-pp-expr x.guts)
    :vl-rhsnew
    (vl-ps-seq
     (vl-ps-span "vl_key" (vl-print-str "new "))
     (if x.arrsize
         (vl-ps-seq (vl-print "[")
                    (vl-pp-expr x.arrsize)
                    (vl-print "]"))
       ps)
     (if (consp x.args)
         (vl-ps-seq (vl-print "(")
                    (vl-pp-exprlist x.args)
                    (vl-print ")"))
       ps))))

(define vl-pp-vardecl-aux ((x vl-vardecl-p) &key (ps 'ps))
  ;; This just prints a vardecl, but with no final semicolon and no final atts,
  ;; so we can use it in places where vardecls are separated by commas
  ;; (i.e. for loop initializations) vs. semicolons.

  ;; This used to just print nets.  We use custom code here because we need
  ;; to put the vectored/scalared stuff in the middle of the type...
  (b* (((vl-vardecl x) x))
    (vl-ps-seq
     (vl-progindent)
     (if (not x.atts)
         ps
       (vl-pp-vardecl-atts-begin x.atts))
     (vl-ps-span "vl_key"
                 (if x.nettype
                     (vl-ps-seq (vl-print-str (vl-nettypename-string x.nettype))
                                (vl-print " "))
                   ps)
                 (if (not x.cstrength)
                     ps
                   (vl-ps-seq (vl-println? (vl-cstrength-string x.cstrength))
                              (vl-print " ")))
                 (if (not x.vectoredp)
                     ps
                   (vl-println? "vectored "))
                 (if (not x.scalaredp)
                     ps
                   (vl-println? "scalared ")))
     (if (and (vl-datatype-case x.type :vl-coretype)
              (eq (vl-coretype->name x.type) :vl-logic)
              x.nettype)
         ;; netdecl with logic type, which is the default -- just print the
         ;; signedness/packed dims
         (vl-ps-seq (if (vl-coretype->signedp x.type)
                        (vl-ps-span "vl_key" (vl-print-str " signed "))
                      ps)
                    (vl-pp-dimensionlist (vl-coretype->pdims x.type)))
       (vl-pp-datatype x.type))
     (if (not x.delay)
         ps
       (vl-ps-seq (vl-print " ")
                  (vl-pp-gatedelay x.delay)))
     (vl-print " ")
     (vl-print-wirename x.name)
     (let ((udims (vl-datatype->udims x.type)))
       (if (not udims)
           ps
         (vl-ps-seq (vl-print " ")
                    (vl-pp-dimensionlist udims))))
     (if x.initval
         (vl-ps-seq (vl-print " = ")
                    (vl-pp-rhs x.initval))
       ps))))

(define vl-pp-vardecl ((x vl-vardecl-p) &key (ps 'ps))
  (if (vl-vardecl-hiddenp x)
      ps
    (vl-ps-seq (vl-pp-vardecl-aux x)
               (vl-print " ;")
               (vl-pp-vardecl-atts-end (vl-vardecl->atts x)))))

(define vl-pp-vardecllist ((x vl-vardecllist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-vardecl (car x))
               (vl-pp-vardecllist (cdr x)))))

(define vl-pp-vardecllist-comma-separated ((x vl-vardecllist-p) &key (ps 'ps))
  (b* (((when (atom x)) ps)
       ;; for this purpose we don't care whether it's hidden
       (ps (vl-pp-vardecl-aux (car x)))
       ((when (atom (cdr x))) ps)
       (ps (vl-print " ,")))
    (vl-pp-vardecllist-comma-separated (cdr x))))





(define vl-pp-assign ((x vl-assign-p) &key (ps 'ps))
  (b* (((vl-assign x) x))
    (vl-ps-seq
     (if x.atts
         (vl-ps-seq (vl-println "")
                    (vl-progindent)
                    (vl-pp-atts x.atts)
                    (vl-println ""))
       ps)
     (vl-progindent)
     (vl-ps-span "vl_key" (vl-print "assign "))
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

(define vl-pp-alias ((x vl-alias-p) &key (ps 'ps))
  (b* (((vl-alias x) x))
    (vl-ps-seq
     (if x.atts
         (vl-ps-seq (vl-println "")
                    (vl-progindent)
                    (vl-pp-atts x.atts)
                    (vl-println ""))
       ps)
     (vl-progindent)
     (vl-ps-span "vl_key" (vl-print "  alias "))
     (vl-pp-expr x.lhs)
     (vl-println? " = ")
     (vl-pp-expr x.rhs)
     (vl-println " ;"))))



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
    (vl-ps-seq (vl-progindent)
               (if x.atts (vl-pp-atts x.atts) ps)
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
    (vl-ps-seq (vl-progindent)
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key"
                           (vl-print "typedef "))
               (vl-pp-datatype x.type)
               (vl-print " ")
               (vl-print-wirename x.name)
               (let ((udims (vl-datatype->udims x.type)))
                 (if (consp udims)
                     (vl-ps-seq (vl-print " ")
                                (vl-pp-dimensionlist udims))
                   ps))
               ;; BOZO add dimensions
               (vl-println " ;"))))

(define vl-pp-typedeflist ((x vl-typedeflist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-typedef (car x))
               (vl-pp-typedeflist (cdr x)))))


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
  (b* (((vl-namedarg x)))
    (vl-ps-seq (if x.atts (vl-pp-atts x.atts) ps)
               (vl-print ".")
               (vl-ps-span "vl_id"
                           (vl-print (vl-maybe-escape-identifier x.name)))
               (if (and x.nameonly-p
                        x.expr
                        (vl-idexpr-p x.expr)
                        (equal (vl-idexpr->name x.expr) x.name))
                   ;; Seems reasonable to keep it in .foo format instead of using .foo(foo)
                   ps
                 (vl-ps-seq (vl-print "(")
                            (if x.expr
                                (vl-pp-expr x.expr)
                              ps)
                            (vl-print ")"))))))

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
  (without-mimicking-linebreaks
    (b* ((namedp         (vl-arguments-case x :vl-arguments-named))
         (args           (vl-arguments-case x
                           :vl-arguments-named (vl-arguments-named->args x)
                           :vl-arguments-plain (vl-arguments-plain->args x)))
         (force-newlinep (longer-than-p 5 args))
         ((when namedp)
          (vl-ps-seq
           ;; We'll arbitrarily put the .* at the beginning of the list.
           (if (vl-arguments-named->starp x)
               (vl-ps-seq (vl-print ".*")
                          (cond ((atom args)          ps)
                                ((not force-newlinep) (vl-println? ", "))
                                (t                    (vl-println ","))))
             ps)
           (vl-pp-namedarglist args force-newlinep)))
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
             ;; BOZO should just print something ugly instead of causing an error
             (raise "Trying to print a plain argument list, of length 1, which ~
                   contains a \"blank\" entry.  But there is actually no way ~
                   to express this in Verilog.")
             ps))))
      (vl-pp-plainarglist args force-newlinep))))


(define vl-pp-paramvalue ((x vl-paramvalue-p) &key (ps 'ps))
  (b* ((x (vl-paramvalue-fix x)))
    (vl-paramvalue-case x
      :expr     (vl-pp-expr x.expr)
      :type     (vl-pp-datatype x.type))))

(define vl-pp-paramvaluelist ((x vl-paramvaluelist-p) force-newlinesp &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-pp-paramvalue (car x)))
        (t
         (vl-ps-seq (vl-pp-paramvalue (car x))
                    (if force-newlinesp
                        (vl-ps-seq (vl-println ",")
                                   (vl-indent (vl-ps->autowrap-ind)))
                      (vl-println? ", "))
                    (vl-pp-paramvaluelist (cdr x) force-newlinesp)))))

(define vl-pp-namedparamvalue ((x vl-namedparamvalue-p) &key (ps 'ps))
  (b* (((vl-namedparamvalue x) x))
    (vl-ps-seq (vl-print ".")
               (vl-ps-span "vl_id" (vl-print (vl-maybe-escape-identifier x.name)))
               (vl-print "(")
               (if x.value
                   (vl-pp-paramvalue x.value)
                 ps)
               (vl-print ")"))))

(define vl-pp-namedparamvaluelist ((x vl-namedparamvaluelist-p) force-newlinesp &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-pp-namedparamvalue (car x)))
        (t
         (vl-ps-seq (vl-pp-namedparamvalue (car x))
                    (if force-newlinesp
                        (vl-ps-seq (vl-println ",")
                                   (vl-indent (vl-ps->autowrap-ind)))
                      (vl-println? ", "))
                    (vl-pp-namedparamvaluelist (cdr x) force-newlinesp)))))

(define vl-pp-paramargs ((x vl-paramargs-p) &key (ps 'ps))
  (without-mimicking-linebreaks
    (vl-paramargs-case x
      :vl-paramargs-named
      (b* ((force-newlinep (longer-than-p 5 x.args)))
        (vl-pp-namedparamvaluelist x.args force-newlinep))
      :vl-paramargs-plain
      (b* ((force-newlinep (longer-than-p 5 x.args)))
        (vl-pp-paramvaluelist x.args force-newlinep)))))


(define vl-pp-modinst-atts-begin ((x vl-atts-p) &key (ps 'ps))
  (b* ((x (vl-atts-fix x))
       ((unless x)
        ps)
       ((when (and (tuplep 1 x)
                   (equal (caar x) "VL_FOR")))
        (b* ((val (cdar x))
             (str (and val
                       (vl-expr-case val
                         :vl-literal (vl-value-case val.val
                                       :vl-string val.val.value
                                       :otherwise nil)
                         :otherwise nil)))
             ((unless str)
              (raise "Expected VL_FOR to contain a string.")
              ps))
          (vl-ps-span "vl_cmt"
                      (vl-println "")
                      (vl-progindent)
                      (vl-print "/* For ")
                      (vl-print-str str)
                      (vl-println " */")))))
    (vl-ps-seq (vl-println "")
               (vl-progindent)
               (vl-pp-atts x)
               (vl-println ""))))

(define vl-pp-modulename-link-aux ((name stringp) (origname stringp) &key (ps 'ps))
  (declare (ignorable name))
  (b* (;(name     (string-fix name))
       (origname (string-fix origname)))
    ;;(vl-ps-seq
    (vl-print-modname origname)
     ;; (vl-print-markup "<a class=\"vl_trans\" href=\"javascript:showTranslatedModule('")
     ;; (vl-print-url origname)
     ;; (vl-print-markup "', '")
     ;; (vl-print-url name)
     ;; (vl-print-markup "')\">")
     ;; ;; Now, what part gets linked to the translation?  If the names agree,
     ;; ;; we just add a lone $.  Otherwise, we add the remaining part of the
     ;; ;; name.
     ;; (b* ((nl  (length name))
     ;;      (onl (length origname))
     ;;      ((when (equal origname name))
     ;;       (vl-print "$"))
     ;;      ((when (and (<= onl nl)
     ;;                  (equal origname (subseq name 0 onl))))
     ;;       (vl-print-str (subseq name onl nl))))
     ;;   (prog2$ (raise "Naming convention violated: name = ~s0, origname = ~s1.~%"
     ;;                  name origname)
     ;;           ps))
     ;; (vl-print-markup "</a>"))))
    ))

(define vl-pp-modulename-link ((name stringp)
                               (ss   vl-scopestack-p)
                               &key (ps 'ps))
  ;; Assumes HTML mode.
  (b* ((name (string-fix name))
       (def  (vl-scopestack-find-definition name ss))
       ((unless def)
        ;; I sometimes hit this case when pretty-printing the source for modules
        ;; that were thrown away.
        (prog2$ (cw "Warning: instance of undefined module ~s0?~%" name)
                (vl-print-modname name)))
       ((unless (eq (tag def) :vl-module))
        (prog2$ (cw "Warning: module instance of non-module ~s0? (~s1)~%" name (tag def))
                (vl-print-modname name)))
       (origname (vl-module->origname def)))
    (vl-pp-modulename-link-aux name origname)))

(define vl-pp-modinst ((x  vl-modinst-p)
                       (ss vl-scopestack-p)
                       &key (ps 'ps))
  (b* (((vl-modinst x) x)
       (have-params-p (vl-paramargs-case x.paramargs
                        :vl-paramargs-named (consp x.paramargs.args)
                        :vl-paramargs-plain (consp x.paramargs.args))))
    (if (or x.str x.delay)
        (prog2$ (cw "; Note: in vl-pp-modinst, dropping str/delay from ~x0 instance.~%"
                    x.modname)
                ps)
      (vl-ps-seq (if x.atts
                     (vl-pp-modinst-atts-begin x.atts)
                   ps)
                 (vl-progindent)
                 (if (vl-ps->htmlp)
                     (vl-pp-modulename-link x.modname ss)
                   (vl-print-modname x.modname))
                 (if (not have-params-p)
                     ps
                   (vl-ps-seq (vl-print " #(")
                              (vl-pp-paramargs x.paramargs)
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

(define vl-pp-modinstlist ((x  vl-modinstlist-p)
                           (ss vl-scopestack-p)
                           &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-modinst (car x) ss)
               (vl-pp-modinstlist (cdr x) ss))))

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
        (b* ((val (cdar x))
             (str (and val
                       (vl-expr-case val
                         :vl-literal (vl-value-case val.val
                                       :vl-string val.val.value
                                       :otherwise nil)
                         :otherwise nil)))
             ((unless str)
              (prog2$
               (raise "Expected VL_FOR to contain a string.")
               ps)))
          (vl-ps-span "vl_cmt"
                      (vl-println "")
                      (vl-progindent)
                      (vl-print "/* For ")
                      (vl-print-str str)
                      (vl-println " */")))))
    (vl-ps-seq (vl-println "")
               (vl-progindent)
               (vl-pp-atts x)
               (vl-println ""))))

(define vl-pp-gateinst ((x vl-gateinst-p) &key (ps 'ps))
  (b* (((vl-gateinst x) x))
    (vl-ps-seq (if x.atts
                   (vl-pp-gateinst-atts-begin x.atts)
                 ps)
               (vl-progindent)
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
    (if (vl-expr-resolved-p value)
        (vl-ps-seq
         (vl-print "#")
         (vl-ps-span "vl_int"
                     (vl-println? (vl-resolved->val value))))
      (vl-ps-seq
       (vl-print "#(")
       (vl-pp-expr value)
       (vl-println? ")")))))

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
  :guard-hints (("Goal" :in-theory (enable vl-delayoreventcontrol-p
                                           tag-reasoning)))
  (b* ((x (vl-delayoreventcontrol-fix x)))
    (case (tag x)
      (:vl-delaycontrol (vl-pp-delaycontrol x))
      (:vl-eventcontrol (vl-pp-eventcontrol x))
      (otherwise        (vl-pp-repeateventcontrol x)))))




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
    (vl-ps-seq (vl-progindent)
               (if x.atts (vl-pp-atts x.atts) ps)
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


(define vl-distweighttype-string ((x vl-distweighttype-p))
  :returns (str stringp :rule-classes :type-prescription)
  (case (vl-distweighttype-fix x)
    (:vl-weight-each ":=")
    (:vl-weight-total ":/")
    (otherwise (progn$ (impossible) ""))))

(define vl-pp-distitem ((x vl-distitem-p) &key (ps 'ps))
  :guard-hints(("Goal" :in-theory (enable vl-distweighttype-p)))
  (b* (((vl-distitem x)))
    (vl-ps-seq (if x.right
                   (vl-ps-seq (vl-print "[")
                              (vl-pp-expr x.left)
                              (vl-print ":")
                              (vl-pp-expr x.right)
                              (vl-print "]"))
                 (vl-pp-expr x.left))
               (if (and (vl-distweighttype-equiv x.type :vl-weight-each)
                        (vl-expr-resolved-p x.weight)
                        (equal (vl-resolved->val x.weight) 1))
                   ;; foo := 1 can be printed as just foo.
                   ps
                 (vl-ps-seq (vl-print " ")
                            (vl-print-str (vl-distweighttype-string x.type))
                            (vl-print " ")
                            (vl-pp-expr x.weight))))))

(define vl-pp-distlist ((x vl-distlist-p) &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-pp-distitem (car x)))
        (t
         (vl-ps-seq (vl-pp-distitem (car x))
                    (vl-println? ", ")
                    (vl-pp-distlist (cdr x))))))

(define vl-pp-exprdist ((x vl-exprdist-p) &key (ps 'ps))
  (b* (((vl-exprdist x)))
    (vl-ps-seq (vl-pp-expr x.expr)
               (if (atom x.dist)
                   ps
                 (vl-ps-seq (vl-ps-span "vl_key" (vl-print " dist "))
                            (vl-print "{")
                            (vl-pp-distlist x.dist)
                            (vl-print "}"))))))

(define vl-pp-exprdistlist-with-commas ((x vl-exprdistlist-p) &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-pp-exprdist (car x)))
        (t
         (vl-ps-seq (vl-pp-exprdist (car x))
                    (vl-println? ", ")
                    (vl-pp-exprdistlist-with-commas (cdr x))))))

(define vl-expr-dollarsign-p ((x vl-expr-p))
  (vl-expr-case x
    :vl-special (vl-specialkey-equiv x.key :vl-$)
    :otherwise nil))


(define vl-pp-repetition ((x vl-repetition-p) &key (ps 'ps))
  (b* (((vl-repetition x)))
    (case x.type
      (:vl-repetition-consecutive ;; [* ...]
       (cond ((and (vl-expr-resolved-p x.left)
                   (equal (vl-resolved->val x.left) 0)
                   x.right
                   (vl-expr-dollarsign-p x.right))
              ;; [* 0:$] is just longhand for [*]
              (vl-print "[*]"))
             ((and (vl-expr-resolved-p x.left)
                   (equal (vl-resolved->val x.left) 1)
                   x.right
                   (vl-expr-dollarsign-p x.right))
              ;; [* 1:$] is just longhand for [+]
              (vl-print "[+]"))
             (t
              (vl-ps-seq (vl-print "[* ")
                         (vl-pp-expr x.left)
                         (if x.right
                             (vl-ps-seq (vl-print ":")
                                        (vl-pp-expr x.right))
                           ps)
                         (vl-print "]")))))
      (:vl-repetition-goto
       (vl-ps-seq (vl-print "[-> ")
                  (vl-pp-expr x.left)
                  (if x.right
                      (vl-ps-seq (vl-print ":")
                                 (vl-pp-expr x.right))
                    ps)
                  (vl-print "]")))
      (:vl-repetition-nonconsecutive
       (vl-ps-seq (vl-print "[= ")
                  (vl-pp-expr x.left)
                  (if x.right
                      (vl-ps-seq (vl-print ":")
                                 (vl-pp-expr x.right))
                    ps)
                  (vl-print "]")))
      (otherwise
       (progn$ (impossible) ps))))
  :prepwork
  ((local (defthm vl-repetition->type-forward
            (or (equal (vl-repetition->type x) :vl-repetition-consecutive)
                (equal (vl-repetition->type x) :vl-repetition-goto)
                (equal (vl-repetition->type x) :vl-repetition-nonconsecutive))
            :rule-classes ((:forward-chaining :trigger-terms ((vl-repetition->type x))))
            :hints(("Goal" :cases ((vl-repetitiontype-p (vl-repetition->type x)))))))))


(define vl-property-unaryop->string ((x vl-property-unaryop-p))
  :parents (vl-property-unaryop-p)
  :guard-hints(("Goal" :in-theory (enable vl-property-unaryop-p)))
  :returns (ans stringp :rule-classes :type-prescription)
  (case (vl-property-unaryop-fix x)
    (:vl-prop-firstmatch "first_match")
    (:vl-prop-not        "not")
    (:vl-prop-strong     "strong")
    (:vl-prop-weak       "weak")
    (otherwise           (progn$ (impossible) ""))))

(define vl-property-binaryop->string ((x vl-property-binaryop-p))
  :parents (vl-property-binaryop-p)
  :guard-hints(("Goal" :in-theory (enable vl-property-binaryop-p)))
  :returns (ans stringp :rule-classes :type-prescription)
  (case (vl-property-binaryop-fix x)
    (:vl-prop-and              "and")
    (:vl-prop-intersect        "intersect")
    (:vl-prop-or               "or")
    (:vl-prop-within           "within")
    (:vl-prop-iff              "iff")
    (:vl-prop-until            "until")
    (:vl-prop-suntil           "s_until")
    (:vl-prop-untilwith        "until_with")
    (:vl-prop-suntilwith       "s_until_with")
    (:vl-prop-word-implies     "implies")
    (:vl-prop-thin-implies     "|->")
    (:vl-prop-fat-implies      "|=>")
    (:vl-prop-thin-follows     "#-#")
    (:vl-prop-fat-follows      "#=#")
    (otherwise                 (progn$ (impossible) ""))))

(define vl-property-acceptop->string ((x vl-property-acceptop-p))
  :parents (vl-property-acceptop-p)
  :guard-hints(("Goal" :in-theory (enable vl-property-acceptop-p)))
  :returns (ans stringp :rule-classes :type-prescription)
  (case (vl-property-acceptop-fix x)
    (:vl-prop-accepton        "accept_on")
    (:vl-prop-syncaccepton    "sync_accept_on")
    (:vl-prop-rejecton        "reject_on")
    (:vl-prop-syncrejecton    "sync_reject_on")
    (otherwise                (progn$ (impossible) ""))))


(defines vl-pp-propexpr

  (define vl-pp-propexpr ((x vl-propexpr-p) &key (ps 'ps))
    :measure (vl-propexpr-count x)
    (vl-propexpr-case x

      (:vl-propcore
       (vl-pp-exprdist x.guts))

      (:vl-propinst
       (vl-ps-seq (vl-pp-scopeexpr x.ref)
                  (vl-print "(")
                  (vl-pp-propactuallist x.args)
                  (vl-print ")")))

      (:vl-propthen
       (b* (((vl-range x.delay))
            (parens-left-p (vl-propexpr-case x.left
                             (:vl-proprepeat nil)
                             (:vl-propcore nil)
                             (:otherwise t)))
            (parens-right-p (vl-propexpr-case x.right
                              (:vl-proprepeat nil)
                              (:vl-propcore nil)
                              (:otherwise t))))
         (vl-ps-seq (if parens-left-p (vl-print "(") ps)
                    (vl-pp-propexpr x.left)
                    (if parens-left-p (vl-println? ") ") (vl-println? " "))
                    (vl-print "##")
                    (cond ((and (vl-expr-resolved-p x.delay.msb)
                                (vl-expr-dollarsign-p x.delay.lsb)
                                (equal (vl-resolved->val x.delay.msb) 0))
                           (vl-print "[*]"))
                          ((and (vl-expr-resolved-p x.delay.msb)
                                (vl-expr-dollarsign-p x.delay.lsb)
                                (equal (vl-resolved->val x.delay.msb) 1))
                           (vl-print "[+]"))
                          ((and (vl-expr-resolved-p x.delay.msb)
                                (vl-expr-resolved-p x.delay.lsb)
                                (equal (vl-resolved->val x.delay.msb)
                                       (vl-resolved->val x.delay.lsb)))
                           (vl-pp-expr x.delay.msb))
                          (t
                           (vl-pp-range x.delay)))
                    (if parens-right-p (vl-print " (") ps)
                    (vl-pp-propexpr x.right)
                    (if parens-right-p (vl-println? ")") (vl-println? "")))))

      (:vl-proprepeat
       (b* ((parens-p (vl-propexpr-case x.seq
                        (:vl-propcore nil)
                        (:otherwise t))))
         (vl-ps-seq (if parens-p (vl-print "(") ps)
                    (vl-pp-propexpr x.seq)
                    (if parens-p (vl-print ")") ps)
                    (vl-pp-repetition x.reps))))

      (:vl-propassign
       (vl-ps-seq (vl-print "(")
                  (vl-pp-propexpr x.seq)
                  (if (atom x.items)
                      ps
                    (vl-ps-seq (vl-println? ", ")
                               (vl-pp-exprlist x.items)))
                  (vl-println? ")")))

      (:vl-propthroughout
       (vl-ps-seq
        ;; No parens should be needed around LEFT since it's just an exprdist instead
        ;; of some kind of sequence.
        (vl-pp-exprdist x.left)
        (vl-ps-span "vl_key" (vl-print " throughout "))
        (vl-print "(")
        (vl-pp-propexpr x.right)
        (vl-println? ")")))

      (:vl-propclock
       (vl-ps-seq (vl-print "@(")
                  (vl-pp-evatomlist x.trigger)
                  (vl-println? ") ")
                  (vl-print "(")
                  (vl-pp-propexpr x.then)
                  (vl-println? ")")))

      (:vl-propunary
       (vl-ps-seq (vl-ps-span "vl_key" (vl-print-str (vl-property-unaryop->string x.op)))
                  (vl-print "(")
                  (vl-pp-propexpr x.arg)
                  (vl-println? ")")))

      (:vl-propbinary
       (vl-ps-seq (vl-print "(")
                  (vl-pp-propexpr x.left)
                  (vl-print ") ")
                  (vl-ps-span "vl_key" (vl-print-str (vl-property-binaryop->string x.op)))
                  (vl-print " (")
                  (vl-pp-propexpr x.right)
                  (vl-println? ")")))

      (:vl-propalways
       (vl-ps-seq (vl-ps-span "vl_key" (if x.strongp
                                           (vl-print "s_always ")
                                         (vl-print "always ")))
                  (if x.range
                      (vl-ps-seq (vl-pp-range x.range)
                                 (vl-print " "))
                    ps)
                  (vl-print "(")
                  (vl-pp-propexpr x.prop)
                  (vl-println? ")")))

      (:vl-propeventually
       (vl-ps-seq (vl-ps-span "vl_key" (if x.strongp
                                           (vl-print "s_eventually ")
                                         (vl-print "eventually ")))
                  (if x.range
                      (vl-ps-seq (vl-pp-range x.range)
                                 (vl-print " "))
                    ps)
                  (vl-print "(")
                  (vl-pp-propexpr x.prop)
                  (vl-println? ")")))

      (:vl-propaccept
       (vl-ps-seq (vl-ps-span "vl_key" (vl-print-str (vl-property-acceptop->string x.op)))
                  (vl-print "(")
                  (vl-pp-exprdist x.condition)
                  (vl-println? ") ")
                  (vl-print "(")
                  (vl-pp-propexpr x.prop)
                  (vl-println? ")")))

      (:vl-propnexttime
       (vl-ps-seq (vl-ps-span "vl_key" (if x.strongp
                                           (vl-print "s_nexttime ")
                                         (vl-print "nexttime ")))
                  (if x.expr
                      (vl-ps-seq (vl-print "[")
                                 (vl-pp-expr x.expr)
                                 (vl-print "] "))
                    ps)
                  (vl-print "(")
                  (vl-pp-propexpr x.prop)
                  (vl-println? ")")))

      (:vl-propif
       (vl-ps-seq (vl-ps-span "vl_key" (vl-print "if "))
                  (vl-print "(")
                  (vl-pp-exprdist x.condition)
                  (vl-println ")")
                  (vl-indent 6)
                  (vl-print "(")
                  (vl-pp-propexpr x.then)
                  (vl-println ")")
                  (vl-indent 6)
                  (vl-ps-span "vl_key" (vl-print " else "))
                  (vl-print "(")
                  (vl-pp-propexpr x.else)
                  (vl-println ")")))

      (:vl-propcase
       (vl-ps-seq (vl-ps-span "vl_key" (vl-print "case "))
                  (vl-print "(")
                  (vl-pp-exprdist x.condition)
                  (vl-println ")")
                  (vl-pp-propcaseitemlist x.cases)
                  (vl-ps-span "vl_key" (vl-println "endcase"))))))

  (define vl-pp-propactual ((x vl-propactual-p) &key (ps 'ps))
    :measure (vl-propactual-count x)
    (vl-propactual-case x
      (:blank (if (not x.name)
                  ps
                (vl-ps-seq (vl-print ".")
                           (vl-print-str (vl-maybe-escape-identifier x.name))
                           (vl-print "()"))))
      (:event (if (not x.name)
                  ;; Scary because it's so ambiguous, but can't really do
                  ;; anything about it, I think.  Maybe print extra parens?
                  ;; Yeah that seems good.
                  (vl-ps-seq (vl-print "(")
                             (vl-pp-evatomlist x.evatoms)
                             (vl-print ")"))
                (vl-ps-seq (vl-print ".")
                           (vl-print-str (vl-maybe-escape-identifier x.name))
                           (vl-print "(")
                           (vl-pp-evatomlist x.evatoms)
                           (vl-print ")"))))
      (:prop (if (not x.name)
                 (vl-ps-seq (vl-print "(")
                            (vl-pp-propexpr x.prop)
                            (vl-print ")"))
               (vl-ps-seq (vl-print ".")
                          (vl-print-str (vl-maybe-escape-identifier x.name))
                          (vl-print "(")
                          (vl-pp-propexpr x.prop)
                          (vl-print ")"))))))

  (define vl-pp-propactuallist ((x vl-propactuallist-p) &key (ps 'ps))
    :measure (vl-propactuallist-count x)
    (cond ((atom x)
           ps)
          ((atom (cdr x))
           (vl-pp-propactual (car x)))
          (t
           (vl-ps-seq (vl-pp-propactual (car x))
                      (vl-println? ", ")
                      (vl-pp-propactuallist (cdr x))))))

  (define vl-pp-propcaseitem ((x vl-propcaseitem-p) &key (ps 'ps))
    :measure (vl-propcaseitem-count x)
    (b* (((vl-propcaseitem x)))
      (vl-ps-seq
       (vl-progindent)
       (if (atom x.match)
           (vl-ps-seq (vl-ps-span "vl_key" (vl-print "default")))
         (vl-pp-exprdistlist-with-commas x.match))
       (vl-println ": ")
       (vl-progindent-block (vl-progindent)
                            (vl-print "(")
                            (vl-pp-propexpr x.prop)
                            (vl-println ");")))))

  (define vl-pp-propcaseitemlist ((x vl-propcaseitemlist-p) &key (ps 'ps))
    :measure (vl-propcaseitemlist-count x)
    (if (atom x)
        ps
      (vl-ps-seq (vl-pp-propcaseitem (car x))
                 (vl-pp-propcaseitemlist (cdr x))))))

(define vl-pp-propspec ((x vl-propspec-p) &key (ps 'ps))
  (b* (((vl-propspec x))
       (col (vl-ps->col)))
    ;; BOZO switch to progindent
    (vl-ps-seq (if (consp x.evatoms)
                   (vl-ps-seq (vl-print "@(")
                              (vl-pp-evatomlist x.evatoms)
                              (vl-println ")")
                              (if x.disable
                                  (vl-indent col)
                                ps))
                 ps)
               (if x.disable
                   (vl-ps-seq (vl-ps-span "vl_key" (vl-print "disable iff "))
                              (vl-pp-exprdist x.disable)
                              (vl-println ""))
                 ps)
               (if (or x.evatoms x.disable)
                   (vl-indent (+ (vl-ps->autowrap-ind) 2))
                 ps)
               (vl-pp-propexpr x.prop))))



;; BOZO these four probably aren't necessary now.
(define vl-pp-vardecllist-indented ((x vl-vardecllist-p)
                                    &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-progindent)
               (vl-pp-vardecl (car x))
               (vl-pp-vardecllist-indented (cdr x)))))

(define vl-pp-paramdecllist-indented ((x vl-paramdecllist-p)
                                    &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-progindent)
               (vl-pp-paramdecl (car x))
               (vl-pp-paramdecllist-indented (cdr x)))))

(define vl-pp-importlist-indented ((x vl-importlist-p)
                                    &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-progindent)
               (vl-pp-import (car x))
               (vl-pp-importlist-indented (cdr x)))))

(define vl-pp-typedeflist-indented ((x vl-typedeflist-p)
                                    &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-progindent)
               (vl-pp-typedef (car x))
               (vl-pp-typedeflist-indented (cdr x)))))

(define vl-casetype-string ((x vl-casetype-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-casetype-p)))
  (case (vl-casetype-fix x)
    ('nil         "case")
    (:vl-casex    "casex")
    (:vl-casez    "casez")
    (otherwise    (or (impossible) ""))))

(define vl-casecheck-string ((x vl-casecheck-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-casecheck-p)))
  (case (vl-casecheck-fix x)
    ('nil         "")
    (:vl-priority "priority")
    (:vl-unique   "unique")
    (:vl-unique0  "unique0")
    (otherwise    (or (impossible) ""))))

(define vl-asserttype-string ((x vl-asserttype-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-asserttype-p)))
  (case (vl-asserttype-fix x)
    (:vl-assert         "assert")
    (:vl-assume         "assume")
    (:vl-cover          "cover")
    (:vl-expect         "expect")
    (:vl-restrict       "restrict")
    (otherwise          (or (impossible) ""))))

(define vl-assertdeferral-string ((x vl-assertdeferral-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-assertdeferral-p)))
  (case (vl-assertdeferral-fix x)
    ('nil               "")
    (:vl-defer-0        "#0")
    (:vl-defer-final    "final")
    (otherwise          (or (impossible) ""))))

(define vl-blocktype-startstring ((x vl-blocktype-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-blocktype-p)))
  (case (vl-blocktype-fix x)
    (:vl-beginend     "begin")
    (:vl-forkjoin     "fork")
    (:vl-forkjoinany  "fork")
    (:vl-forkjoinnone "fork")
    (otherwise        (or (impossible) ""))))

(define vl-blocktype-endstring ((x vl-blocktype-p))
  :returns (str stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-blocktype-p)))
  (case (vl-blocktype-fix x)
    (:vl-beginend     "end")
    (:vl-forkjoin     "join")
    (:vl-forkjoinany  "join_any")
    (:vl-forkjoinnone "join_none")
    (otherwise        (or (impossible) ""))))

(define vl-pp-forloop-assigns ((x vl-stmtlist-p) &key (ps 'ps))
  (b* (((when (atom x)) ps)
       (x1 (car x))
       (ps (vl-stmt-case x1
             (:vl-assignstmt
              (vl-ps-seq (vl-pp-expr x1.lvalue)
                         (vl-println? " = ")
                         (vl-pp-rhs x1.rhs)))
             ;; BOZO might need to handle enablestmt for function calls
             (:otherwise
              (prog2$ (raise "Bad type of statement for for loop initialization/step: ~x0~%"
                             (vl-stmt-kind x1))
                      ps))))
       ((when (atom (cdr x))) ps)
       (ps (vl-print ", ")))
    (vl-pp-forloop-assigns (cdr x))))

(define vl-pp-foreachstmt-loopvars ((loopvars vl-maybe-string-list-p) &key (ps 'ps))
  :measure (len loopvars)
  (b* ((loopvars (vl-maybe-string-list-fix loopvars)))
    (if (atom loopvars)
        ps
      (if (atom (car loopvars))
          (vl-ps-seq (vl-print ", ")
                     (vl-pp-foreachstmt-loopvars (cdr loopvars)))
        (vl-ps-seq (vl-ps-span "vl_id" (vl-print-str (vl-maybe-escape-identifier (car loopvars))))
                   (vl-print ", ")
                   (vl-pp-foreachstmt-loopvars (cdr loopvars)))))))


(defines vl-pp-stmt
  :prepwork ((local (in-theory (disable not)))
             (local (defthm vl-deassignstmt->type-possibilities
                      (or (eq (vl-deassignstmt->type x) :vl-deassign)
                          (eq (vl-deassignstmt->type x) :vl-release))
                      :hints (("goal" :use vl-deassign-type-p-of-vl-deassignstmt->type
                               :in-theory '(vl-deassign-type-p)))
                      :rule-classes ((:forward-chaining :trigger-terms ((vl-deassignstmt->type x)))))))

  (define vl-pp-stmt ((x vl-stmt-p) &key (ps 'ps))
    :measure (vl-stmt-count x)
    (vl-stmt-case x
      :vl-nullstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-println " ;"))

      :vl-assignstmt
      (vl-ps-seq (vl-progindent)
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
                 (vl-pp-rhs x.rhs)
                 (vl-println " ;"))

      :vl-callstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (if x.voidp
                     (vl-ps-seq (vl-ps-span "vl_key" (vl-print "void"))
                                (vl-print "'("))
                   ps)
                 (if (and x.systemp
                          (vl-scopeid-p x.id)
                          (stringp x.id))
                     (vl-ps-seq (vl-ps-span "vl_sys")
                                (vl-print-str x.id))
                   (vl-pp-scopeexpr x.id))
                 ;; In Verilog-2005 a task enable with no arguments must be
                 ;; written as `foo;`, not `foo();`.  However, in SystemVerilog
                 ;; it's OK to include the parens, so we no longer are careful
                 ;; not to do so.
                 (vl-println? "(")
                 (if x.typearg
                     (vl-ps-seq (vl-pp-datatype x.typearg)
                                (if (consp x.args)
                                    (vl-println? ", ")
                                  ps))
                   ps)
                 (vl-pp-maybe-exprlist x.args)
                 (vl-println ");"))

      :vl-disablestmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key"
                             (vl-print "disable "))
                 (vl-pp-scopeexpr x.id)
                 (vl-println " ;"))

      :vl-breakstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "break "))
                 (vl-println " ;"))

      :vl-continuestmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "continue "))
                 (vl-println " ;"))

      :vl-returnstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "return "))
                 (if x.val (vl-pp-expr x.val) ps)
                 (vl-println " ;"))

      :vl-deassignstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key"
                             (case x.type
                               (:vl-deassign (vl-print "deassign "))
                               (:vl-release  (vl-print "release "))
                               (otherwise    (progn$ (impossible) ps))))
                 (vl-pp-expr x.lvalue)
                 (vl-println " ;"))

      :vl-eventtriggerstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-print "-> ")
                 (vl-pp-expr x.id)
                 (vl-println " ;"))

      :vl-ifstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "if"))
                 (vl-print " (")
                 (vl-pp-expr x.condition)
                 (vl-println ")")
                 (vl-progindent-block (vl-pp-stmt x.truebranch))
                 (vl-progindent)
                 (vl-ps-span "vl_key" (vl-print "else"))
                 (if (vl-stmt-case x.falsebranch :vl-ifstmt)
                     ;; It's very common for if/else if structures to be
                     ;; deeply nested.  In this case we don't want to
                     ;; print the sub-statement with extra indentation,
                     ;; and we want it to occur on the same line.
                     (vl-ps-seq (vl-print " ")
                                (vl-pp-stmt x.falsebranch))
                   ;; A plain "else", not an "else if".  Go ahead and
                   ;; give it a new line and indent its body.
                   (vl-ps-seq (vl-println "")
                              (vl-progindent-block (vl-pp-stmt x.falsebranch)))))

      :vl-blockstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key"
                             (vl-print-str (vl-blocktype-startstring x.blocktype)))
                 (if (not x.name)
                     (vl-println "")
                   (vl-ps-seq
                    (vl-print " : ")
                    (vl-ps-span "vl_id"
                                (vl-print-str (vl-maybe-escape-identifier x.name)))
                    (vl-println "")))
                 (if (not x.imports)
                     ps
                   (vl-pp-importlist-indented x.imports))
                 ;; BOZO order here may be incorrect.  Maybe need to do something to
                 ;; smartly reorder these using location data.
                 (if (not x.paramdecls)
                     ps
                   (vl-pp-paramdecllist-indented x.paramdecls))
                 (if (not x.typedefs)
                     ps
                   (vl-pp-typedeflist-indented x.typedefs))
                 (if (not x.vardecls)
                     ps
                   (vl-pp-vardecllist-indented x.vardecls))
                 (vl-progindent-block (vl-pp-stmtlist x.stmts))
                 (vl-progindent)
                 (vl-ps-span "vl_key"
                             (vl-print-str (vl-blocktype-endstring x.blocktype)))
                 (vl-println ""))

      :vl-forstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "for "))
                 (vl-print "(")
                 (if x.initdecls
                     ;; There can only be one of initdecls or initassigns.
                     ;; Either way, special care needs to be taken to print
                     ;; them comma-separated instead of semicolon-separated.
                     (vl-pp-vardecllist-comma-separated x.initdecls)
                   (vl-pp-forloop-assigns x.initassigns))
                 (vl-print "; ")
                 (vl-pp-expr x.test)
                 (vl-print "; ")
                 (vl-pp-forloop-assigns x.stepforms)
                 (vl-println ")")
                 (vl-progindent-block (vl-pp-stmt x.body))
                 ;; no ending semicolon, the body prints one
                 )

      :vl-foreachstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "foreach "))
                 (vl-print "(")
                 (vl-pp-scopeexpr x.array)
                 (vl-print " [")
                 (vl-pp-foreachstmt-loopvars x.loopvars)
                 (vl-println " ])")
                 (vl-progindent-block (vl-pp-stmt x.body))
                 ;; no ending semicolon, the body prints one
                 )

      :vl-timingstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-pp-delayoreventcontrol x.ctrl)
                 (if (eq (tag x.ctrl) :vl-eventcontrol)
                     ;; Something like @(posedge clk) or @(foo or bar),
                     ;; want to get a newline.
                     (vl-ps-seq (vl-println "")
                                (vl-progindent-block (vl-pp-stmt x.body)))
                   ;; Something like #5 foo <= bar, try to keep it on the
                   ;; same line.
                   (vl-ps-seq (vl-print " ")
                              (vl-pp-stmt x.body))))

      :vl-foreverstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-println "forever"))
                 (vl-progindent-block (vl-pp-stmt x.body))
                 ;; no ending semicolon, the body prints one
                 )

      :vl-repeatstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "repeat"))
                 (vl-print " (")
                 (vl-pp-expr x.condition)
                 (vl-println ")")
                 (vl-progindent-block (vl-pp-stmt x.body))
                 ;; no ending semicolon, the body prints one
                 )

      :vl-waitstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "wait"))
                 (vl-print " (")
                 (vl-pp-expr x.condition)
                 (vl-println ")")
                 (vl-progindent-block (vl-pp-stmt x.body))
                 ;; no ending semicolon, the body prints one
                 )

      :vl-whilestmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-print "while"))
                 (vl-print " (")
                 (vl-pp-expr x.condition)
                 (vl-println ")")
                 (vl-progindent-block (vl-pp-stmt x.body))
                 ;; no ending semicolon, the body prints one
                 )

      :vl-dostmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key" (vl-println "do"))
                 (vl-progindent-block (vl-pp-stmt x.body))
                 (vl-ps-span "vl_key" (vl-print "while"))
                 (vl-print " (")
                 (vl-pp-expr x.condition)
                 (vl-println ");")
                 ;; yes ending semicolon, i think
                 )

      :vl-casestmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-ps-span "vl_key"
                             (if x.check
                                 (vl-ps-seq
                                  (vl-print-str (vl-casecheck-string x.check))
                                  (vl-print " "))
                               ps)
                             (vl-print-str (vl-casetype-string x.casetype)))
                 (vl-print " (")
                 (vl-pp-expr x.test)
                 (vl-println ")")
                 (vl-progindent-block (vl-pp-cases x.caselist))
                 (vl-progindent)
                 (vl-ps-span "vl_key" (vl-print "default"))
                 (vl-println " :")
                 (vl-progindent-block (vl-pp-stmt x.default))
                 (vl-progindent)
                 (vl-ps-span "vl_key" (vl-print "endcase"))
                 (vl-println ""))

      :vl-assertstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-pp-assertion x.assertion :include-name nil))

      :vl-cassertstmt
      (vl-ps-seq (vl-progindent)
                 (if x.atts (vl-pp-atts x.atts) ps)
                 (vl-pp-cassertion x.cassertion :include-name nil))))

  (define vl-pp-assertion ((x vl-assertion-p) &key (include-name booleanp) (ps 'ps))
    :measure (vl-assertion-count x)
    (b* (((vl-assertion x)))
      (vl-ps-seq (vl-progindent)
                 (if (and include-name x.name)
                     (vl-ps-seq (vl-ps-span "vl_id" (vl-print (vl-maybe-escape-identifier x.name)))
                                (vl-print " : "))
                   ps)
                 (vl-ps-span "vl_key"
                             (vl-print-str (vl-asserttype-string x.type))
                             (vl-print " ")
                             (if x.deferral
                                 (vl-ps-seq (vl-print-str (vl-assertdeferral-string x.deferral))
                                            (vl-print " "))
                               ps))
                 (vl-print "(")
                 (vl-pp-expr x.condition)
                 (vl-print ")")
                 (vl-stmt-case x.success
                   (:vl-nullstmt ps)
                   (:otherwise (vl-ps-seq (vl-println "")
                                          (vl-progindent-block (vl-pp-stmt x.success)))))
                 (vl-stmt-case x.failure
                   (:vl-nullstmt ps)
                   (:otherwise (vl-ps-seq (vl-println "")
                                          (vl-progindent)
                                          (vl-ps-span "vl_key" (vl-println " else "))
                                          (vl-println "")
                                          (vl-progindent-block (vl-pp-stmt x.failure)))))
                 (vl-println ";")
                 (vl-println ""))))

  (define vl-pp-cassertion ((x vl-cassertion-p) &key (include-name booleanp) (ps 'ps))
    :measure (vl-cassertion-count x)
    (b* (((vl-cassertion x)))
      (vl-ps-seq (vl-progindent)
                 (if (and include-name x.name)
                     (vl-ps-seq (vl-ps-span "vl_id" (vl-print (vl-maybe-escape-identifier x.name)))
                                (vl-print " : "))
                   ps)
                 (vl-ps-span "vl_key"
                             (vl-print-str (vl-asserttype-string x.type))
                             (cond ((vl-asserttype-equiv x.type :vl-expect)
                                    ;; expect just uses "expect (...)" instead of "expect property (...)"
                                    (vl-print " "))
                                   ((and (vl-asserttype-equiv x.type :vl-cover)
                                         x.sequencep)
                                    ;; cover statements can be "cover sequence" statements
                                    (vl-print " sequence "))
                                   (t
                                    ;; everything else has "property" after it, e.g., "assert property"
                                    (vl-print " property "))))
                 (vl-print "(")
                 (vl-pp-propspec x.condition)
                 (vl-print ")")
                 (vl-stmt-case x.success
                   (:vl-nullstmt ps)
                   (:otherwise (vl-ps-seq (vl-println "")
                                          (vl-progindent-block (vl-pp-stmt x.success)))))
                 (vl-stmt-case x.failure
                   (:vl-nullstmt ps)
                   (:otherwise (vl-ps-seq (vl-println "")
                                          (vl-progindent)
                                          (vl-ps-span "vl_key" (vl-println " else "))
                                          (vl-println "")
                                          (vl-progindent-block (vl-pp-stmt x.failure)))))
                 (vl-println ";")
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
         ((cons exprs stmt) (car x)))
      (vl-ps-seq (vl-progindent)
                 (vl-pp-exprlist exprs)
                 (vl-println " :")
                 (vl-progindent-block (vl-pp-stmt stmt))
                 (vl-pp-cases (cdr x)))))
  ///
  (local (in-theory (disable vl-pp-stmt
                             vl-pp-stmtlist
                             vl-pp-cases)))

  (deffixequiv-mutual vl-pp-stmt
    :hints (("Goal" :expand ((vl-pp-stmt x)
                             (vl-pp-stmt (vl-stmt-fix x))
                             (vl-pp-stmtlist x)
                             (vl-pp-stmtlist (vl-stmtlist-fix x))
                             (vl-pp-stmtlist nil)
                             (vl-pp-cases x)
                             (vl-pp-cases (vl-caselist-fix x))
                             (vl-pp-cases nil)
                             (:free (include-name) (vl-pp-assertion x :include-name include-name))
                             (:free (include-name) (vl-pp-cassertion x :include-name include-name))
                             )))))

(define vl-alwaystype-string ((x vl-alwaystype-p))
  :returns (str stringp :rule-classes :type-prescription)
  (case (vl-alwaystype-fix x)
    (:vl-always       "always")
    (:vl-always-comb  "always_comb")
    (:vl-always-ff    "always_ff")
    (:vl-always-latch "always_latch")
    (otherwise         (progn$ (impossible) ""))))

(define vl-pp-always ((x vl-always-p) &key (ps 'ps))
  (b* (((vl-always x) x))
    (vl-ps-seq (vl-progindent)
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print-str (vl-alwaystype-string x.type)))
               (vl-print " ")
               (vl-pp-stmt x.stmt))))

(define vl-pp-alwayslist ((x vl-alwayslist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-always (car x))
               (vl-println "")
               (vl-pp-alwayslist (cdr x)))))

(define vl-pp-initial ((x vl-initial-p) &key (ps 'ps))
  (b* (((vl-initial x) x))
    (vl-ps-seq (vl-progindent)
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


(define vl-pp-final ((x vl-final-p) &key (ps 'ps))
  (b* (((vl-final x) x))
    (vl-ps-seq (vl-progindent)
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "final "))
               (vl-pp-stmt x.stmt)
               (vl-println ""))))

(define vl-pp-finallist ((x vl-finallist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-final (car x))
               (vl-println "")
               (vl-pp-finallist (cdr x)))))


(define vl-pp-fundecl ((x vl-fundecl-p) &key (ps 'ps))
  ;; We print these off using "variant 1" style (see parse-functions)
  (b* (((vl-fundecl x) x))
    (vl-ps-seq (vl-progindent)
               (if x.atts
                   (vl-ps-seq (vl-pp-atts x.atts)
                              (vl-print " "))
                 ps)
               (vl-ps-span "vl_key"
                           (vl-print "function ")
                           (vl-pp-lifetime x.lifetime)
                           (vl-pp-datatype x.rettype)
                           (vl-print " "))
               (vl-print-wirename x.name)
               (vl-println ";")
               ;; BOZO this order might not be right, maybe need something
               ;; smarter that takes locations into account
               (vl-progindent-block (vl-pp-portdecllist x.portdecls)
                                    (vl-pp-importlist x.imports)
                                    (vl-pp-paramdecllist x.paramdecls)
                                    (vl-pp-typedeflist x.typedefs)
                                    (vl-pp-vardecllist x.vardecls)
                                    (vl-pp-stmt x.body)
                                    (vl-basic-cw "~|")) ;; newline only if necessary
               (vl-progindent)
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
    (vl-ps-seq (vl-progindent)
               (if x.atts
                   (vl-ps-seq (vl-pp-atts x.atts)
                              (vl-print " "))
                 ps)
               (vl-ps-span "vl_key"
                           (vl-print "task ")
                           (vl-pp-lifetime x.lifetime))
               (vl-print-wirename x.name)
               (vl-println ";")
               ;; BOZO this order might not be right, maybe need something
               ;; smarter that takes locations into account
               (vl-progindent-block (vl-pp-portdecllist x.portdecls)
                                    (vl-pp-importlist x.imports)
                                    (vl-pp-paramdecllist x.paramdecls)
                                    (vl-pp-typedeflist x.typedefs)
                                    (vl-pp-vardecllist x.vardecls)
                                    (vl-pp-stmt x.body)
                                    (vl-basic-cw "~|")) ;; newline only if necessary
               (vl-progindent)
               (vl-ps-span "vl_key" (vl-print "endtask"))
               (vl-println ""))))

(define vl-pp-taskdecllist ((x vl-taskdecllist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-taskdecl (car x))
               (vl-println "")
               (vl-pp-taskdecllist (cdr x)))))



(define vl-pp-genvar ((x vl-genvar-p) &key (ps 'ps))
  (b* (((vl-genvar x)))
    (vl-ps-seq (vl-progindent)
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key"
                           (vl-print "genvar "))
               (vl-print-wirename x.name)
               (vl-println ";"))))

(define vl-pp-modport-port ((x vl-modport-port-p) &key (ps 'ps))
  (b* (((vl-modport-port x)))
    (vl-ps-seq
     (if x.atts (vl-pp-atts x.atts) ps)
     (vl-ps-span "vl_key" (vl-print-str (vl-direction-string x.dir)))
     (vl-print " ")
     (if (and x.expr
              (vl-idexpr-p x.expr)
              (equal (vl-idexpr->name x.expr) x.name))
         ;; Very common case where external and internal names align, just print
         ;; the wire instead of the extended .foo(bar) syntax.
         (vl-print-wirename x.name)
       ;; Else, some custom expression, so use .foo(bar)
       (vl-ps-seq (vl-print ".")
                  (vl-print-wirename x.name)
                  (vl-print "(")
                  (if x.expr
                      (vl-pp-expr x.expr)
                    ps)
                  (vl-print ")"))))))

(define vl-pp-modport-portlist ((x vl-modport-portlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-modport-port (car x))
               (if (atom (cdr x))
                   ps
                 (vl-println? ", "))
               (vl-pp-modport-portlist (cdr x)))))

(define vl-pp-modport ((x vl-modport-p) &key (ps 'ps))
  (b* (((vl-modport x)))
    (vl-ps-seq (vl-progindent)
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "modport "))
               (vl-print-wirename x.name)
               (vl-print " ( ")
               (vl-pp-modport-portlist x.ports)
               (vl-println " );"))))


(define vl-pp-propport ((x vl-propport-p) &key (ps 'ps))
  (b* (((vl-propport x))
       (x.type.udims (vl-datatype->udims x.type)))
    (vl-ps-seq (if x.atts (vl-pp-atts x.atts) ps)
               (if (not x.localp)
                   ps
                 (vl-ps-span "vl_key"
                             (vl-print "local ")
                             (if (vl-direction-equiv x.dir :vl-input)
                                 ;; the default, don't print it
                                 ps
                               (vl-ps-seq (vl-print-str (vl-direction-string x.dir))
                                          (vl-print " ")))))
               (vl-pp-datatype x.type)
               (vl-print " ")
               (vl-ps-span "vl_id"
                           (vl-print (vl-maybe-escape-identifier x.name)))
               (if (not x.type.udims)
                   ps
                 (vl-ps-seq (vl-print " ")
                            (vl-pp-dimensionlist x.type.udims)))
               (vl-propactual-case x.arg
                 (:blank ps)
                 (:event
                  (vl-ps-seq (vl-print " = ")
                             (vl-pp-propactual
                              (change-vl-propactual-event x.arg :name nil))))
                 (:prop
                  (vl-ps-seq (vl-print " = ")
                             (vl-pp-propactual
                              (change-vl-propactual-prop x.arg :name nil))))))))

(define vl-pp-propportlist ((x vl-propportlist-p) &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-pp-propport (car x)))
        (t (vl-ps-seq (vl-pp-propport (car x))
                      (vl-print ", ")
                      (vl-pp-propportlist (cdr x))))))

(define vl-pp-property ((x vl-property-p) &key (ps 'ps))
  (b* (((vl-property x)))
    (vl-ps-seq (vl-progindent)
               (vl-ps-span "vl_key" (vl-print "property "))
               (vl-ps-span "vl_id"
                           (vl-print (vl-maybe-escape-identifier x.name)))
               (vl-print " (")
               (vl-pp-propportlist x.ports)
               (vl-println ");")
               (vl-progindent-block (vl-pp-vardecllist x.decls)
                                    (vl-pp-propspec x.spec)
                                    (vl-println ";"))
               (vl-progindent)
               (vl-ps-span "vl_key" (vl-println "endproperty ")))))

(define vl-pp-propertylist ((x vl-propertylist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-property (car x))
               (vl-pp-propertylist (cdr x)))))

(define vl-pp-sequence ((x vl-sequence-p) &key (ps 'ps))
  (b* (((vl-sequence x)))
    (vl-ps-seq (vl-progindent)
               (vl-ps-span "vl_key" (vl-print "sequence "))
               (vl-ps-span "vl_id"
                           (vl-print (vl-maybe-escape-identifier x.name)))
               (vl-print " (")
               (vl-pp-propportlist x.ports)
               (vl-println ");")
               (vl-progindent-block (vl-pp-vardecllist x.decls)
                                    (vl-pp-propexpr x.expr)
                                    (vl-println ";"))
               (vl-progindent)
               (vl-ps-span "vl_key" (vl-println "endsequence ")))))

(define vl-pp-sequencelist ((x vl-sequencelist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-sequence (car x))
               (vl-pp-sequencelist (cdr x)))))

(define vl-dpispec->string ((x vl-dpispec-p))
  (case (vl-dpispec-fix x)
    (:vl-dpi   "\"DPI\"")
    (:vl-dpi-c "\"DPI-C\"")
    (otherwise (progn$ (impossible) ""))))

(define vl-dpiprop->string ((x vl-dpiprop-p))
  (case (vl-dpiprop-fix x)
    ((nil)           "")
    (:vl-dpi-context "context")
    (:vl-dpi-pure    "pure")
    (otherwise       (progn$ (impossible) ""))))

(define vl-pp-dpiimport ((x vl-dpiimport-p) &key (ps 'ps))
  (b* (((vl-dpiimport x)))
    (vl-ps-seq (vl-progindent)
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "import "))
               ;; "DPI" or "DPI-C"
               (vl-ps-span "vl_str" (vl-print-str (vl-dpispec->string x.spec)))
               (vl-print " ")
               ;; context or pure, if applicable:
               (if x.prop
                   (vl-ps-span "vl_key"
                               (vl-print-str (vl-dpiprop->string x.prop))
                               (vl-print " "))
                 ps)
               ;; [ c_identifier '=' ], if different than SV name:
               (if (not (equal x.c-name x.name))
                   (vl-ps-seq (vl-ps-span "vl_id" (vl-print-str x.c-name))
                              (vl-print " = "))
                 ps)
               ;; function and return type or task:
               (if x.rettype
                   (vl-ps-seq (vl-ps-span "vl_key" (vl-print "function "))
                              (vl-pp-datatype x.rettype))
                 (vl-ps-span "vl_key" (vl-print "task ")))
               ;; SV name:
               (vl-ps-span "vl_id"
                           (vl-print-str (vl-maybe-escape-identifier x.name))
                           (vl-print " "))
               (vl-print "(")
               (if x.portdecls
                   (vl-ps-span "vl_cmt"
                               (vl-print " /* bozo print ports */ "))
                 ps)
               (vl-print ")")
               (vl-println ";"))))

(define vl-pp-dpiimportlist ((x vl-dpiimportlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-dpiimport (car x))
               (vl-pp-dpiimportlist (cdr x)))))

(define vl-dpifntask->string ((x vl-dpifntask-p))
  (case (vl-dpifntask-fix x)
    (:vl-dpi-function "function")
    (:vl-dpi-task     "task")
    (otherwise        (progn$ (impossible) ""))))

(define vl-pp-dpiexport ((x vl-dpiexport-p) &key (ps 'ps))
  (b* (((vl-dpiexport x)))
    (vl-ps-seq (vl-progindent)
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "  export "))
               ;; "DPI" or "DPI-C"
               (vl-ps-span "vl_str" (vl-print-str (vl-dpispec->string x.spec)))
               (vl-print " ")
               ;; [ c_identifier '=' ], if different than SV name:
               (if (not (equal x.c-name x.name))
                   (vl-ps-seq (vl-ps-span "vl_id" (vl-print-str x.c-name))
                              (vl-print " = "))
                 ps)
               ;; function or task
               (vl-ps-span "vl_key" (vl-print-str (vl-dpifntask->string x.fntask)))
               (vl-print " ")
               ;; SV name
               (vl-ps-span "vl_id"
                           (vl-print-str (vl-maybe-escape-identifier x.name))
                           (vl-print " "))
               (vl-println ";"))))

(define vl-pp-dpiexportlist ((x vl-dpiexportlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-dpiexport (car x))
               (vl-pp-dpiexportlist (cdr x)))))


(define vl-pp-bind ((x vl-bind-p) (ss vl-scopestack-p) &key (ps 'ps))
  (b* (((vl-bind x)))
    (vl-ps-seq (vl-progindent)
               (vl-ps-span "vl_key" (vl-print "bind "))
               ;; Print everything up to bind_instantiation.  This depends on whether
               ;; we are scoped or scopeless.
               (if x.scope
                   ;; For scoped we have:
                   ;;   'bind' bind_target_scope [ ':' bind_target_instance_list ] bind_instantiation ';'
                   (vl-ps-seq (vl-ps-span "vl_id"
                                          (vl-print-str (vl-maybe-escape-identifier x.scope)))
                              (if (atom x.addto)
                                  ps
                                (vl-ps-seq (vl-print " : ")
                                           (vl-pp-exprlist x.addto))))
                 ;; For scopeless we have:
                 ;;   'bind' bind_target_instance bind_instantiation ';'
                 (vl-pp-exprlist x.addto))
               ;; Now just print the bind_instantiation part.
               (if (and (consp x.modinsts)
                        (atom (cdr x.modinsts)))
                   (vl-pp-modinst (car x.modinsts) ss)
                 (vl-println "// BOZO print multiple modinsts in a BIND?")))))

(define vl-pp-bindlist ((x vl-bindlist-p) (ss vl-scopestack-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-bind (car x) ss)
               (vl-pp-bindlist (cdr x) ss))))

(define vl-pp-clkskew ((x vl-clkskew-p) &key (ps 'ps))
  :prepwork ((local (in-theory (enable vl-evatomtype-p))))
  :guard-hints(("Goal"
                :in-theory (disable vl-evatomtype-p-of-vl-clkskew->edge)
                :use ((:instance vl-evatomtype-p-of-vl-clkskew->edge))))
  (b* (((vl-clkskew x)))
    (vl-ps-seq
     ;; Print the edge, if there is one
     (if (eq x.edge :vl-noedge)
         ps
       (vl-ps-span "vl_key" (case x.edge
                              (:vl-posedge (vl-print "posedge"))
                              (:vl-negedge (vl-print "negedge"))
                              (:vl-edge (vl-print "edge"))
                              (otherwise (progn$ (impossible) ps)))))
     ;; Space if there's an edge and a delay
     (if (and (not (eq x.edge :vl-noedge))
              x.delay)
         (vl-print " ")
       ps)
     ;; Print the delay, if there is one
     (if x.delay
         (vl-pp-expr x.delay)
       ps))))

(define vl-pp-clkassign ((x vl-clkassign-p) &key (ps 'ps))
  (b* (((vl-clkassign x)))
    (vl-ps-seq (vl-progindent)
               (vl-ps-span "vl_key"
                           (if x.inputp
                               (vl-print "  input ")
                             (vl-print "  output ")))
               (if x.skew
                   (vl-pp-clkskew x.skew)
                 ps)
               (vl-ps-span "vl_id"
                           (vl-print-str (vl-maybe-escape-identifier x.name)))
               (if x.rhs
                   (vl-ps-seq (vl-print " = ")
                              (vl-pp-expr x.rhs))
                 ps)
               (vl-println "; "))))

(define vl-pp-clkassignlist ((x vl-clkassignlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-clkassign (car x))
               (vl-pp-clkassignlist (cdr x)))))

(define vl-pp-clkdecl ((x vl-clkdecl-p) &key (ps 'ps))
  (b* (((vl-clkdecl x)))
    (vl-ps-seq (vl-progindent)
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-print "  ")
               (vl-ps-span "vl_key"
                           (if x.defaultp (vl-print "default ") ps)
                           (vl-print "clocking "))
               (if x.name
                   (vl-ps-span "vl_id"
                               (vl-print-str (vl-maybe-escape-identifier x.name))
                               (vl-print " "))
                 ps)
               (vl-pp-evatomlist x.event)
               (vl-println ";")
               (vl-progindent-block
                (if x.iskew
                    (vl-ps-seq (vl-progindent)
                               (vl-print "  ")
                               (vl-ps-span "vl_key" (vl-print "input "))
                               (vl-pp-clkskew x.iskew)
                               (vl-println ";"))
                  ps)
                (if x.oskew
                    (vl-ps-seq (vl-progindent)
                               (vl-print "  ")
                               (vl-ps-span "vl_key" (vl-print "output "))
                               (vl-pp-clkskew x.oskew)
                               (vl-println ";"))
                  ps)
                (vl-pp-clkassignlist x.clkassigns)
                (vl-pp-propertylist x.properties)
                (vl-pp-sequencelist x.sequences))
               (vl-ps-span "vl_key"
                           (vl-println "endclocking")))))

(define vl-pp-clkdecllist ((x vl-clkdecllist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-clkdecl (car x))
               (vl-pp-clkdecllist (cdr x)))))

(define vl-pp-defaultdisable ((x vl-defaultdisable-p) &key (ps 'ps))
  (b* (((vl-defaultdisable x)))
    (vl-ps-seq (vl-progindent)
               (vl-ps-span "vl_key"
                           (vl-print "default disable iff "))
               (vl-pp-exprdist x.exprdist)
               (vl-println ";"))))

(define vl-pp-defaultdisablelist ((x vl-defaultdisablelist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-defaultdisable (car x))
               (vl-pp-defaultdisablelist (cdr x)))))

(define vl-pp-gclkdecl ((x vl-gclkdecl-p) &key (ps 'ps))
  (b* (((vl-gclkdecl x)))
    (vl-ps-seq (vl-progindent)
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-print "  ")
               (vl-ps-span "vl_key"
                           (vl-print "global clocking "))
               (if x.name
                   (vl-ps-span "vl_id"
                               (vl-print-str (vl-maybe-escape-identifier x.name))
                               (vl-print " "))
                 ps)
               (vl-pp-evatomlist x.event)
               (vl-println ";"))))

(define vl-pp-gclkdecllist ((x vl-gclkdecllist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-gclkdecl (car x))
               (vl-pp-gclkdecllist (cdr x)))))


(define vl-pp-class ((x vl-class-p) &key (ps 'ps))
  (b* (((vl-class x) x))
    (vl-ps-seq (if x.atts (vl-pp-atts x.atts) ps)
               (if x.virtualp (vl-ps-span "vl_key" (vl-print "virtual ")) ps)
               (vl-ps-span "vl_key" (vl-print "class "))
               (vl-pp-lifetime x.lifetime)
               (vl-print-modname x.name)
               (vl-println " ;")
               (vl-println " // BOZO implement vl-pp-class")
               (vl-ps-span "vl_key" (vl-println "endclass"))
               (vl-println ""))))

(define vl-pp-classlist ((x vl-classlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-class (car x))
               (vl-pp-classlist (cdr x)))))



(define vl-pp-covergroup ((x vl-covergroup-p) &key (ps 'ps))
  (b* (((vl-covergroup x) x))
    (vl-ps-seq (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "covergroup "))
               (vl-print-modname x.name)
               (vl-println "/* BOZO */ ;")
               (vl-println " // BOZO implement cover groups")
               (vl-ps-span "vl_key" (vl-println "endgroup"))
               (vl-println ""))))

(define vl-pp-covergrouplist ((x vl-covergrouplist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-covergroup (car x))
               (vl-pp-covergrouplist (cdr x)))))



(define vl-pp-elabtask ((x vl-elabtask-p) &key (ps 'ps))
  (b* (((vl-elabtask x) x))
    (vl-pp-stmt x.stmt)))

(define vl-pp-elabtasklist ((x vl-elabtasklist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-elabtask (car x))
               (vl-pp-elabtasklist (cdr x)))))


(define vl-pp-modelement ((x vl-modelement-p) &key (ps 'ps))
  (let ((x (vl-modelement-fix x)))
    (case (tag x)
      (:VL-PORT       (VL-pp-PORT X))
      (:VL-PORTDECL   (VL-pp-PORTDECL X))
      (:VL-ASSIGN     (VL-pp-ASSIGN X))
      (:VL-ALIAS      (VL-pp-ALIAS X))
      (:VL-VARDECL    (VL-pp-VARDECL X))
      (:VL-PARAMDECL  (VL-pp-PARAMDECL X))
      (:VL-FUNDECL    (VL-pp-FUNDECL X))
      (:VL-TASKDECL   (VL-pp-TASKDECL X))
      (:VL-MODINST    (VL-pp-MODINST X nil))
      (:VL-GATEINST   (VL-pp-GATEINST X))
      (:VL-ALWAYS     (VL-pp-ALWAYS X))
      (:VL-INITIAL    (VL-pp-INITIAL X))
      (:VL-FINAL      (VL-pp-FINAL X))
      (:VL-TYPEDEF    (VL-pp-TYPEDEF X))
      (:VL-IMPORT     (VL-pp-IMPORT X))
      (:VL-FWDTYPEDEF (VL-pp-FWDTYPEDEF X))
      (:vl-modport    (vl-pp-modport x))
      (:vl-genvar     (vl-pp-genvar x))
      (:vl-property   (vl-pp-property x))
      (:vl-sequence   (vl-pp-sequence x))
      (:vl-clkdecl    (vl-pp-clkdecl x))
      (:vl-gclkdecl   (vl-pp-gclkdecl x))
      (:vl-defaultdisable (vl-pp-defaultdisable x))
      (:vl-dpiimport  (vl-pp-dpiimport x))
      (:vl-dpiexport  (vl-pp-dpiexport x))
      (:vl-bind       (vl-pp-bind x nil))
      (:vl-class      (vl-pp-class x))
      (:vl-covergroup (vl-pp-covergroup x))
      (:vl-elabtask   (vl-pp-elabtask x))
      (:vl-assertion  (vl-pp-assertion x :include-name t))
      (:vl-cassertion (vl-pp-cassertion x :include-name t))
      (:vl-letdecl    (vl-println "/* Implement LETDECL printing */"))
      (OTHERWISE (progn$ (impossible) ps)))))

(define vl-pp-modelementlist ((x vl-modelementlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-modelement (car x))
               (vl-pp-modelementlist (cdr x)))))

(defines vl-pp-genelement

  (define vl-pp-genelement ((x vl-genelement-p) &key (ps 'ps))
    :measure (vl-genelement-count x)
    (vl-genelement-case x
      :vl-genbase  (vl-pp-modelement x.item)
      :vl-genbegin (vl-pp-genblock x.block)
      :vl-genloop  (vl-ps-seq (vl-println "")
                              (vl-progindent)
                              (vl-ps-span "vl_key" (vl-print "for "))
                              (vl-print "(")
                              (vl-print-str x.var)
                              (vl-print "=")
                              (vl-pp-expr x.initval)
                              (vl-print "; ")
                              (vl-pp-expr x.continue)
                              (vl-print "; ")
                              (vl-print-str x.var)
                              (vl-print "=")
                              (vl-pp-expr x.nextval)
                              (vl-print ")")
                              (vl-pp-genblock x.body))
      :vl-genif    (vl-ps-seq (vl-println "")
                              (vl-progindent)
                              (vl-ps-span "vl_key" (vl-print "if"))
                              (vl-print " (")
                              (vl-pp-expr x.test)
                              (vl-print ")")
                              (vl-pp-genblock x.then)
                              (vl-ps-span "vl_key" (vl-print "else"))
                              (vl-pp-genblock x.else))
      :vl-gencase  (vl-ps-seq (vl-println "")
                              (vl-progindent)
                              (vl-ps-span "vl_key" (vl-print "case"))
                              (vl-print " (")
                              (vl-pp-expr x.test)
                              (vl-pp-gencaselist x.cases)
                              (vl-println "")
                              (vl-ps-span "vl_key" (vl-print "default"))
                              (vl-print ":")
                              (vl-pp-genblock x.default))
      :vl-genarray (vl-ps-seq (vl-println "")
                              (vl-progindent)
                              (vl-ps-span "vl_key" (vl-print "begin"))
                              (if x.name
                                  (vl-ps-seq (vl-print " : ")
                                             (vl-print-wirename x.name))
                                ps)
                              (vl-println "")
                              (vl-pp-genblocklist x.blocks)
                              (vl-ps-span "vl_key" (vl-println "end")))))

  (define vl-pp-genblock ((x vl-genblock-p) &key (ps 'ps))
    :measure (vl-genblock-count x)
    (b* (((vl-genblock x)))
      (vl-ps-seq (vl-println "")
                 (vl-progindent)
                 (vl-ps-span "vl_key" (vl-print "begin"))
                 (if x.name
                     (vl-ps-seq (vl-print " : ")
                                (if (stringp x.name)
                                    (vl-print-wirename x.name)
                                  (vl-ps-seq (vl-print "\\[")
                                             (vl-print x.name)
                                             (vl-print "]"))))
                   ps)
                 (vl-println "")
                 (vl-progindent-block (vl-pp-genelementlist x.elems))
                 (vl-progindent)
                 (vl-ps-span "vl_key" (vl-println "end"))
                 (vl-println ""))))

  (define vl-pp-genelementlist ((x vl-genelementlist-p) &key (ps 'ps))
    :measure (vl-genelementlist-count x)
    (if (atom x)
        ps
      (vl-ps-seq (vl-pp-genelement (car x))
                 (vl-pp-genelementlist (cdr x)))))

  (define vl-pp-gencaselist ((x vl-gencaselist-p) &key (ps 'ps))
    :measure (vl-gencaselist-count x)
    (b* ((x (vl-gencaselist-fix x)))
      (if (atom x)
          ps
        (vl-ps-seq (vl-println "")
                   (vl-progindent)
                   (vl-pp-exprlist (caar x))
                   (vl-print ": ")
                   (vl-pp-genblock (cdar x))
                   (vl-pp-gencaselist (cdr x))))))

  (define vl-pp-genblocklist ((x vl-genblocklist-p)
                              &key (ps 'ps))
    :measure (vl-genblocklist-count x)
    (if (atom x)
        ps
      (vl-ps-seq (vl-pp-genblock (car x))
                 (vl-pp-genblocklist (cdr x)))))

  ///
  (deffixequiv-mutual vl-pp-genelement))

(define vl-pp-assertionlist ((x vl-assertionlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-assertion (car x) :include-name t)
               (vl-pp-assertionlist (cdr x)))))

(define vl-pp-cassertionlist ((x vl-cassertionlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-cassertion (car x) :include-name t)
               (vl-pp-cassertionlist (cdr x)))))



(define vl-pp-genblob-guts ((x vl-genblob-p)
                            (ss vl-scopestack-p)
                            &key (ps 'ps))
  (b* (((vl-genblob x)))
    (vl-ps-seq (vl-pp-paramdecllist x.paramdecls)
               (vl-pp-typedeflist x.typedefs)
               (vl-pp-portdecllist x.portdecls)
               (vl-pp-vardecllist x.vardecls)
               (vl-println "")
               (vl-pp-dpiimportlist x.dpiimports)
               (vl-pp-dpiexportlist x.dpiexports)
               (vl-pp-fundecllist x.fundecls) ;; put them here, so they can refer to declared wires
               (vl-pp-taskdecllist x.taskdecls)
               (vl-pp-assignlist x.assigns)
               (vl-pp-modinstlist x.modinsts ss)
               (vl-pp-gateinstlist x.gateinsts)
               (vl-pp-alwayslist x.alwayses)
               (vl-pp-initiallist x.initials)
               (vl-pp-finallist x.finals)
               (vl-pp-genelementlist x.generates)
               (vl-pp-propertylist x.properties)
               (vl-pp-sequencelist x.sequences)
               (vl-pp-clkdecllist x.clkdecls)
               (vl-pp-gclkdecllist x.gclkdecls)
               (vl-pp-defaultdisablelist x.defaultdisables)
               (vl-pp-assertionlist x.assertions)
               (vl-pp-cassertionlist x.cassertions)
               (vl-pp-bindlist x.binds ss)
               (vl-pp-classlist x.classes)
               (vl-pp-covergrouplist x.covergroups)
               (vl-pp-elabtasklist x.elabtasks))))

(define vl-pp-module
  ((x    vl-module-p     "Module to pretty-print.")
   (ss   vl-scopestack-p)
   &key (ps 'ps))
  :short "Pretty-print a module to @(see ps)."
  :long "<p>You might instead want to use @(see vl-ppc-module), which preserves
the order of module elements and its comments.  For interactive use, you may
want @(see vl-pps-module) or @(see vl-ppcs-module), which write to a string
instead of @(see ps).</p>"
  (b* (((vl-module x) (vl-module-fix x))
       (ss (vl-scopestack-push x ss)))
    (vl-ps-seq (vl-pp-set-portnames x.portdecls)
               (vl-progindent)
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "module "))
               (if (vl-ps->htmlp)
                   (vl-pp-modulename-link x.name ss)
                 (vl-print-modname x.name))
               (vl-print " (")
               (vl-pp-portlist x.ports)
               (vl-println ");")
               (vl-progindent-block (vl-pp-genblob-guts (vl-module->genblob x) ss))
               (vl-progindent)
               (vl-ps-span "vl_key" (vl-println "endmodule"))
               (vl-println ""))))


(define vl-pp-genblob ;; BOZO temporary weird nonrecursive version
  ((x    vl-genblob-p)
   (ss   vl-scopestack-p)
   &key (ps 'ps))
  (b* (((vl-genblob x) (vl-genblob-fix x))
       (ss (vl-scopestack-push x ss)))
    (vl-ps-seq (vl-pp-set-portnames x.portdecls)
               (vl-progindent)
               (vl-ps-span "vl_key" (vl-print "genblob "))
               (vl-print " (")
               (vl-pp-portlist x.ports)
               (vl-println ");")
               (vl-progindent-block (vl-pp-genblob-guts x ss))
               (vl-progindent)
               (vl-ps-span "vl_key" (vl-println "endgenblob"))
               (vl-println ""))))

(define vl-pps-module ((x vl-module-p))
  :returns (str stringp :rule-classes :type-prescription)
  :short "Pretty-print a module to a plain-text string."
  :long "<p>@(call vl-pps-module) pretty-prints the @(see vl-module-p) @('x')
into a plain-text string.</p>

<p>Alternatives:</p>

<ul>

<li>@(see vl-ppcs-module) preserves the order of module elements and its
comments.</li>

<li>@(see vl-pp-module) can pretty-print @('x') into a plain-text or HTML
string.  For proper printing it requires a @(see scopestack).</li>

</ul>"
  (with-local-ps (vl-pp-module x nil)))

(define vl-pp-modulelist ((x vl-modulelist-p)
                          (ss vl-scopestack-p)
                          &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-module (car x) ss)
               (vl-pp-modulelist (cdr x) ss))))

(define vl-pps-modulelist ((x vl-modulelist-p))
  :returns (str stringp :rule-classes :type-prescription)
  :short "Pretty-print a list of modules to a plain-text string."
  :long "<p>See also @(see vl-ppcs-modulelist), which preserves the order of
module elements and its comments.</p>"
  (with-local-ps (vl-pp-modulelist x nil)))



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

(define vl-pp-package ((x vl-package-p)
                       (ss vl-scopestack-p)
                       &key (ps 'ps))
  (b* (((vl-package x) x))
    (vl-ps-seq (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "package "))
               (vl-print-modname x.name)
               (vl-println " ;")
               (vl-progindent-block (vl-pp-genblob-guts (vl-package->genblob x) ss))
               (vl-progindent)
               (vl-ps-span "vl_key" (vl-println "endpackage"))
               (vl-println ""))))

(define vl-pp-packagelist ((x vl-packagelist-p)
                           (ss vl-scopestack-p)
                           &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-package (car x) ss)
               (vl-pp-packagelist (cdr x) ss))))


(define vl-pp-interface ((x vl-interface-p) (ss vl-scopestack-p) &key (ps 'ps))
  (b* (((vl-interface x) (vl-interface-fix x))
       (ss (vl-scopestack-push x ss)))
    (vl-ps-seq (vl-pp-set-portnames x.portdecls)
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "interface "))
               (if (vl-ps->htmlp)
                   (vl-pp-modulename-link x.name ss)
                 (vl-print-modname x.name))
               (vl-print " (")
               (vl-pp-portlist x.ports)
               (vl-println ");")
               (vl-progindent-block (vl-pp-genblob-guts (vl-interface->genblob x) ss))
               (vl-progindent)
               (vl-ps-span "vl_key" (vl-println "endinterface"))
               (vl-println ""))))

(define vl-pp-interfacelist ((x vl-interfacelist-p) (ss vl-scopestack-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-interface (car x) ss)
               (vl-pp-interfacelist (cdr x) ss))))



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



(define vl-pp-design ((x vl-design-p) &key (ps 'ps))
  ;; arbitrary order
  (b* (((vl-design x))
       (ss (vl-scopestack-init x)))
    (vl-ps-seq (vl-pp-fwdtypedeflist x.fwdtypes)
               (vl-pp-paramdecllist x.paramdecls)
               (vl-pp-typedeflist x.typedefs)
               (vl-pp-vardecllist x.vardecls)
               (vl-pp-fundecllist x.fundecls)
               (vl-pp-taskdecllist x.taskdecls)
               (vl-pp-packagelist x.packages ss)
               (vl-pp-importlist x.imports)
               (vl-pp-dpiimportlist x.dpiimports)
               (vl-pp-dpiexportlist x.dpiexports)
               (vl-pp-bindlist x.binds ss)
               (vl-pp-interfacelist x.interfaces ss)
               (vl-pp-modulelist x.mods ss)
               (vl-pp-udplist x.udps)
               (vl-pp-programlist x.programs)
               (vl-pp-classlist x.classes)
               (vl-pp-configlist x.configs))))



(define vl-pp-scopetype ((x vl-scopetype-p) &key (ps 'ps))
  (vl-print (case (vl-scopetype-fix x)
              (:vl-module     "module")
              (:vl-interface  "interface")
              (:vl-fundecl    "function")
              (:vl-taskdecl   "task")
              (:vl-blockstmt  "block statement")
              (:vl-forstmt    "for statement")
              (:vl-foreachstmt "foreach statement")
              (:vl-design     "global design")
              (:vl-package    "package")
              (:vl-genblock   "generate block")
              (:vl-genarrayblock "generate array block")
              (:vl-genarray      "generate array")
              (otherwise "anonymous scope"))))


(define vl-pp-definition-scope-summary ((x vl-scopestack-p)
                                        &key (ps 'ps))
  :measure (vl-scopestack-count x)
  (b* ((scope (vl-scopestack-case x
                :global x.design
                :local x.top
                :otherwise nil))
       ((unless scope) (vl-print "[empty scopestack]"))
       (id (vl-scope->id scope))
       (type (vl-scope->scopetype scope)))
    (case type
      (:vl-module (vl-ps-seq (vl-pp-scopetype type)
                             (vl-print " ")
                             (if (stringp id)
                                 (vl-pp-modulename-link id x)
                               (vl-print "[unknown]"))))
      ((:vl-interface
        :vl-package) (vl-ps-seq (vl-pp-scopetype type)
                                (vl-print " ")
                                (if (stringp id)
                                    (vl-print-modname id)
                                  (vl-print "[unknown]"))))
      (:vl-design     (vl-pp-scopetype type))
      (otherwise
       (vl-scopestack-case x
         :local (vl-pp-definition-scope-summary x.super)
         :otherwise (vl-print "[empty scopestack]"))))))


(define vl-pp-scope-summary ((x vl-scopestack-p)
                             &key (ps 'ps))
  (b* ((scope (vl-scopestack-case x
                :global x.design
                :local x.top
                :otherwise nil))
       ((unless scope) (vl-print "[empty scopestack]"))
       (id (vl-scope->id scope))
       (type (vl-scope->scopetype scope)))
    (case type
      ((:vl-module
        :vl-interface
        :vl-package
        :vl-design)
       (vl-pp-definition-scope-summary x))
      (otherwise      (vl-ps-seq (vl-pp-scopetype type)
                                 (vl-print " ")
                                 (if (stringp id)
                                     (vl-print-wirename id)
                                   (vl-print "[unknown]"))
                                 (vl-print " inside ")
                                 (vl-pp-definition-scope-summary x))))))

