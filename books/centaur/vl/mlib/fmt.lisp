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
(include-book "writer")
(include-book "print-context")
(local (include-book "../util/arithmetic"))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (in-theory (enable acl2::arith-equiv-forwarding)))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable (tau-system))))

(defxdoc vl-fmt
  :parents (verilog-printing)
  :short "Print format strings with support for Verilog constructs."

  :long "<p>@(call vl-fmt) extends the basic @(see formatted-printing) routine,
@(see vl-basic-fmt), with new directives for more conveniently printing Verilog
modules.  In particular, while @('vl-basic-fmt') only supports a small set of
directives like @('~|'), @('~%'), @('~x0'), and @('~s0'), @('vl-fmt')
additionally supports @('~a') and @('~m'), which are convenient when we want to
tell the user about some parse-tree construct.</p>

<p>Although @('vl-basic-fmt') does not yet implement many ACL2 directives, we
might imagine wanting to support its other directives.  So we have kept our
directives separate from those mentioned in @(':doc fmt').</p>

<dl>

<dt><b>~a</b>, the \"(almost) anything directive\"</dt>

<dd>This directive can handle most Verilog constructs and is our preferred way
to print things in warning messages.  It understands how to pretty-print:

<ul>

 <li><see topic=\"@(url vl-location-p)\">locations</see>,</li>

 <li><see topic=\"@(url vl-expr-p)\">expressions</see> (and automatically
prefers to print \"original expressions\" rather than \"simplified
expressions\"),</li>

 <li><see topic=\"@(url vl-range-p)\">ranges</see>,</li>

 <li><see topic=\"@(url vl-stmt-p)\">statements</see>,</li>

 <li><see topic=\"@(url vl-plainarg-p)\">plain</see> or <see topic=\"@(url
 vl-namedarg-p)\">named</see> arguments,</li>

 <li><see topic=\"@(url vl-context-p)\">contexts</see>,</li>

 <li>any <see topic=\"@(url vl-modelement-p)\">module element</see>,</li>

 <li>or even a whole <see topic=\"@(url vl-module-p)\">module</see> (for which
it only prints the name of the module, perhaps with links).</li>

</ul>

Because this directive is intended for warning messages, it only prints short
summaries of any contexts and module elements.  On the other hand, it prints
expressions, ranges, statements, and arguments \"in full\".</dd>

<dt><b>~m</b>, the \"module name directive\"</dt>

<dd>The corresponding argument should be a string that is the name of a module,
but can also be an entire module.  In html mode, a link to this module will be
printed.</dd>

<dt><b>~w</b>, the \"wire name directive\"</dt>

<dd>The corresponding argument should be a string that is the name of something
in the module's namespace, for instance wire names.  But this can also be used
for names of module instances, gate instances, parameters, etc.  In html mode,
a link to this module element will be printed.</dd>

</dl>

<p>The <b>~l</b> directive is deprecated and is now a synonym for ~a.  It was
formerly the \"location directive\" and printed a location.</p>")

(define vl-fmt-tilde-m (x &key (ps 'ps))
  (cond ((stringp x)
         (vl-print-modname x))
        ((vl-module-p x)
         (vl-pp-modulename-link-aux (vl-module->name x)
                                    (vl-module->origname x)))
        (t
         (vl-fmt-tilde-x x))))

(define vl-fmt-tilde-w (x &key (ps 'ps))
  (cond ((stringp x)
         (vl-print-wirename x))
        ;; BOZO is there anything else this should print as a string?
        ;; ((vl-id-p x)
        ;;  (vl-print-wirename (vl-id->name x)))
        (t
         (vl-fmt-tilde-x x))))




(defconst *vl-enable-unsafe-but-fast-printing* nil)

(defmacro vl-fmt-tilde-a-case (foo-p vl-print-foo)
  `(let ((ps (if (or unsafe-okp (,foo-p x))
                 ,(if (symbolp vl-print-foo)
                      `(,vl-print-foo x)
                    vl-print-foo)
               (vl-fmt-tilde-x x))))
     (mv ',foo-p ps)))



(define vl-fmt-tilde-a-aux (x &key (ps 'ps))
  :returns (mv (type "Used only for the so-called coverage proof.")
               (ps))
  :prepwork ((local (defthm hidexpr-p-when-stringp
                      (implies (stringp x)
                               (Vl-hidexpr-p x))
                      :hints(("Goal" :in-theory (enable vl-hidexpr-p)))))
             (local (defthm tag-when-vl-location-p
                      ;; Locations are special and don't have a sensible tag.
                      (implies (vl-location-p x)
                               (or (integerp (tag x))
                                   (consp (tag x))))
                      :rule-classes ((:type-prescription)
                                     (:forward-chaining))
                      :hints(("Goal" :in-theory (enable vl-location-p
                                                        vl-linecol-p
                                                        tag)))))
             (local (defthm hidexpr-p-when-vl-location-p
                      (implies (vl-location-p x)
                               (not (vl-hidexpr-p x)))
                      :hints(("Goal" :in-theory (enable vl-hidexpr-p vl-location-p))))))
  (b* ((unsafe-okp *vl-enable-unsafe-but-fast-printing*)
       ((when (atom x))
        (if (stringp x)
            (let ((ps (vl-pp-hidexpr x)))
              (mv 'vl-hidexpr-p ps))
          (let ((ps (vl-fmt-tilde-x x)))
            (mv nil ps))))
       ((when (vl-location-p x))
        ;; Locations use a special encoding to increase structure sharing, so
        ;; we don't get to just check them via tag.  Note that vl-location-p
        ;; is pretty darn cheap, so it's not terrible to check it first here.
        (let ((ps (vl-print-loc x)))
          (mv 'vl-location-p ps))))
    (case (tag x)
      ((:vl-special :vl-literal :vl-index :vl-unary :vl-binary
        :vl-qmark :vl-mintypmax :vl-concat :vl-multiconcat :vl-stream
        :vl-call :vl-cast :vl-inside :vl-tagged :vl-pattern :vl-eventexpr)
       (vl-fmt-tilde-a-case vl-expr-p vl-pp-origexpr))
      ((:vl-hidindex)
       (vl-fmt-tilde-a-case vl-hidindex-p vl-pp-hidindex))
      ((:vl-exprdist)
       (vl-fmt-tilde-a-case vl-exprdist-p vl-pp-exprdist))
      ((:vl-repetition)
       (vl-fmt-tilde-a-case vl-repetition-p vl-pp-repetition))
      ((:colon)
       (vl-fmt-tilde-a-case vl-scopeexpr-p vl-pp-scopeexpr))
      ((:vl-range)
       (vl-fmt-tilde-a-case vl-range-p vl-pp-range))
      ((:vl-nullstmt :vl-assignstmt :vl-deassignstmt :vl-callstmt
        :vl-disablestmt :vl-eventtriggerstmt :vl-casestmt :vl-ifstmt
        :vl-foreverstmt :vl-waitstmt :vl-repeatstmt :vl-whilestmt :vl-dostmt
        :vl-forstmt :vl-foreachstmt :vl-blockstmt :vl-timingstmt :vl-breakstmt
        :vl-continuestmt :vl-returnstmt :vl-assertstmt :vl-cassertstmt)
       (vl-fmt-tilde-a-case vl-stmt-p vl-pp-stmt))
      ((:vl-propcore :vl-propinst :vl-propthen :vl-proprepeat
        :vl-propassign :vl-propthroughout :vl-propclock :vl-propunary
        :vl-propbinary :vl-propalways :vl-propeventually :vl-propaccept
        :vl-propnexttime :vl-propif :vl-propcase)
       (vl-fmt-tilde-a-case vl-propexpr-p vl-pp-propexpr))
      ((:vl-propspec)
       (vl-fmt-tilde-a-case vl-propspec-p vl-pp-propspec))
      ((:vl-context)
       (vl-fmt-tilde-a-case vl-context1-p vl-pp-context-summary))
      ((:vl-regularport :vl-interfaceport :vl-portdecl :vl-assign
        :vl-alias :vl-vardecl :vl-paramdecl :vl-fundecl :vl-taskdecl
        :vl-modinst :vl-gateinst :vl-always :vl-initial :vl-final
        :vl-typedef :vl-fwdtypedef :vl-assertion :vl-cassertion
        :vl-property :vl-sequence :vl-clkdecl :vl-gclkdecl
        :vl-import :vl-dpiimport :vl-dpiexport :vl-bind :vl-class
        :vl-covergroup :vl-elabtask :vl-defaultdisable
        :vl-genarray :vl-genbegin :vl-genbase :vl-genif :vl-gencase :vl-genloop :vl-modport)
       (vl-fmt-tilde-a-case vl-ctxelement-p vl-pp-ctxelement-summary))
      ((:vl-genvar)
       (vl-fmt-tilde-a-case vl-genvar-p vl-pp-genvar))
      (:vl-ansi-portdecl
       (vl-fmt-tilde-a-case vl-ansi-portdecl-p vl-pp-ansi-portdecl))
      ;; ((:vl-plainarg)
      ;;  (vl-fmt-tilde-a-case vl-plainarg-p vl-pp-plainarg))
      ;; ((:vl-namedarg)
      ;;  (vl-fmt-tilde-a-case vl-namedarg-p vl-pp-namedarg))
      ((:vl-unsized-dimension :vl-star-dimension :vl-type-dimension :vl-queue-dimension)
       (vl-fmt-tilde-a-case vl-dimension-p vl-pp-dimension))
      ((:vl-enumitem)
       (vl-fmt-tilde-a-case vl-enumitem-p vl-pp-enumitem))
      ((:vl-coretype :vl-struct :vl-union :vl-enum :vl-usertype)
       (vl-fmt-tilde-a-case vl-datatype-p vl-pp-datatype))
      ((:vl-structmember)
       (vl-fmt-tilde-a-case vl-structmember-p vl-pp-structmember))
      ((:vl-fwdtypedef)
       (vl-fmt-tilde-a-case vl-fwdtypedef-p vl-pp-fwdtypedef))
      ((:vl-evatom)
       (vl-fmt-tilde-a-case vl-evatom-p vl-pp-evatom))
      ((:vl-eventcontrol)
       (vl-fmt-tilde-a-case vl-eventcontrol-p vl-pp-eventcontrol))
      ((:vl-delaycontrol)
       (vl-fmt-tilde-a-case vl-delaycontrol-p vl-pp-delaycontrol))
      ((:vl-repeat-eventcontrol)
       (vl-fmt-tilde-a-case vl-repeateventcontrol-p vl-pp-repeateventcontrol))
      ((:vl-module)
       (vl-fmt-tilde-a-case vl-module-p
         (vl-pp-modulename-link-aux (vl-module->name x)
                                    (vl-module->origname x))))
      (otherwise
       (if (vl-hidexpr-p x)
           (let ((ps (vl-pp-hidexpr x)))
             (mv 'vl-hidexpr-p ps))
         (let ((ps (vl-fmt-tilde-x x)))
           (mv nil ps))))))
  ///
  (local (defthm tag-when-vl-expr-p
           (implies (vl-expr-p x)
                    (equal (tag x) (vl-expr-kind x)))
           :rule-classes :forward-chaining
           :hints(("Goal" :in-theory (enable vl-expr-kind tag vl-expr-p)))))

  (local (defthm tag-when-vl-datatype-p
           (implies (vl-datatype-p x)
                    (equal (tag x) (vl-datatype-kind x)))
           :rule-classes :forward-chaining
           :hints(("Goal" :in-theory (enable vl-datatype-kind tag vl-datatype-p)))))

  (local (defthm tag-when-vl-stmt-p
           (implies (vl-stmt-p x)
                    (equal (tag x) (vl-stmt-kind x)))
           :rule-classes :forward-chaining
           :hints(("Goal" :in-theory (enable vl-stmt-kind tag vl-stmt-p)))))

  ;; (local (defthm tag-when-vl-hidexpr-p
  ;;          (implies (vl-hidexpr-p x)
  ;;                   (equal (tag x) (vl-hidexpr-kind x)))
  ;;          :rule-classes :forward-chaining
  ;;          :hints(("Goal" :in-theory (enable vl-hidexpr-kind tag vl-hidexpr-p)))))

  ;; (local (defthm tag-when-vl-scopeexpr-p
  ;;          (implies (vl-scopeexpr-p x)
  ;;                   (equal (tag x) (vl-scopeexpr-kind x)))
  ;;          :rule-classes :forward-chaining
  ;;          :hints(("Goal" :in-theory (enable vl-scopeexpr-kind tag vl-scopeexpr-p)))))

  (local (defthm tag-when-vl-propexpr-p
           (implies (vl-propexpr-p x)
                    (equal (tag x) (vl-propexpr-kind x)))
           :rule-classes :forward-chaining
           :hints(("Goal" :in-theory (enable vl-propexpr-kind tag vl-propexpr-p)))))

  ;; (local (defthm vl-hidexpr-p-means-not-vl-scopeexpr-p
  ;;          (implies (vl-hidexpr-p x)
  ;;                   (not (vl-scopeexpr-p x)))
  ;;          :rule-classes :forward-chaining
  ;;          :hints(("Goal" :expand ((vl-scopeexpr-p x)
  ;;                                  (vl-hidexpr-p x))))))

  (local (defthm not-hidexpr-when-non-string-atom
           (implies (and (atom x) (not (stringp x)))
                    (and (not (vl-hidexpr-p x))
                         (not (vl-scopeexpr-p x))))
           :hints(("Goal" :in-theory (enable vl-hidexpr-p
                                             vl-scopeexpr-p)))))

  (local (defthm not-hid/scopeexpr-when-location
           (and (implies (and (symbolp (tag x))
                              (consp x))
                         (not (vl-hidexpr-p x)))
                (implies (and (symbolp (tag x))
                              (consp x)
                              (not (equal (tag x) :colon)))
                         (not (vl-scopeexpr-p x))))
           :hints(("Goal" :in-theory (enable tag
                                             vl-scopeexpr-p
                                             vl-hidexpr-p
                                             vl-hidindex-p)
                   :expand ((vl-hidexpr-p x)
                            (vl-scopeexpr-p x))))))

  (local (defthm not-scopeexpr-when-not-colon-or-hidexpr
           (implies (and (not (vl-hidexpr-p x))
                         (not (Equal (tag x) :colon)))
                    (not (vl-scopeexpr-p x)))
           :hints(("Goal" :in-theory (enable tag)
                   :expand ((vl-scopeexpr-p x))))))

  (local (in-theory (enable tag-reasoning)))

  (defrule vl-fmt-tilde-a-aux-coverage
    (b* (((mv type &) (vl-fmt-tilde-a-aux x)))
      (and (implies (vl-location-p x) (equal type 'vl-location-p))
           (implies (vl-expr-p x) (equal type 'vl-expr-p))
           (implies (vl-hidexpr-p x) (equal type 'vl-hidexpr-p))
           (implies (vl-scopeexpr-p x) (or (equal type 'vl-scopeexpr-p)
                                           (equal type 'vl-hidexpr-p)))
           (implies (vl-exprdist-p x) (equal type 'vl-exprdist-p))
           (implies (vl-range-p x) (equal type 'vl-range-p))
           (implies (vl-propexpr-p x) (equal type 'vl-propexpr-p))
           (implies (vl-propspec-p x) (equal type 'vl-propspec-p))
           (implies (vl-datatype-p x) (equal type 'vl-datatype-p))
           (implies (vl-structmember-p x) (equal type 'vl-structmember-p))
           (implies (vl-ctxelement-p x) (equal type 'vl-ctxelement-p))
           (implies (vl-enumitem-p x) (equal type 'vl-enumitem-p))
           (implies (vl-stmt-p x) (equal type 'vl-stmt-p))
           (implies (vl-evatom-p x) (equal type 'vl-evatom-p))
           (implies (vl-eventcontrol-p x) (equal type 'vl-eventcontrol-p))
           (implies (vl-delaycontrol-p x) (equal type 'vl-delaycontrol-p))
           (implies (vl-repeateventcontrol-p x) (equal type 'vl-repeateventcontrol-p))
           ))
    :rule-classes nil))

(define vl-fmt-tilde-a (x &key (ps 'ps))
  (b* (((mv ?type ps)
        (vl-fmt-tilde-a-aux x)))
    ps))


(define vl-fmt-pair-args ((args true-listp))
  :returns (res alistp)
  (pairlis$ (take (min (len args) 10)
                  '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
            args)
  ///
  (local (defthm strip-cdrs-of-pairlis$
           (equal (strip-cdrs (pairlis$ a b))
                  (take (len a) b))))
  (local
   (defthm acl2-count-of-take
     (implies (<= n (len x))
              (<= (acl2-count (take n x))
                  (acl2-count x)))
     :hints (("goal" :induct (nth n x)
              :in-theory (enable acl2::take)))
     :rule-classes :linear))
  (defthm acl2-count-of-vl-fmt-pair-args
    (<= (acl2-count (strip-cdrs (vl-fmt-pair-args args)))
        (acl2-count args))
    :rule-classes :linear))

(define vl-fmt-aux ((x stringp)
                    (n natp)
                    (xl (eql xl (length x)))
                    (alist alistp)
                    &key
                    (ps 'ps))
  :verbosep t
  :guard (<= n xl)
  :ruler-extenders :all
  :measure (two-nats-measure (acl2-count (strip-cdrs alist))
                             (- (nfix xl) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
                   :exec (eql xl n)))
        ps)
       ((mv type val n)
        (vl-basic-fmt-parse-tilde x n xl))
       (ps (case type
             (:skip   ps)
             (:normal (vl-fmt-print-normal val))
             (:hard-space (vl-print #\Space))
             (:cbreak (if (zp (vl-ps->col)) ps (vl-println "")))
             (otherwise
              (b* ((lookup (assoc val alist))
                   ((unless lookup)
                    (prog2$ (raise "alist does not bind ~x0; fmt-string is ~x1." val x)
                            ps)))
                (case type
                  (#\s (vl-fmt-tilde-s (cdr lookup)))
                  (#\& (vl-fmt-tilde-& (cdr lookup)))
                  (#\x (vl-fmt-tilde-x (cdr lookup)))
                  (#\m (vl-fmt-tilde-m (cdr lookup)))
                  (#\w (vl-fmt-tilde-w (cdr lookup)))
                  (#\l (vl-fmt-tilde-a (cdr lookup)))
                  (#\a (vl-fmt-tilde-a (cdr lookup)))
                  (#\@ (b* ((look (cdr lookup))
                            ((unless (vl-msg-p look))
                             (prog2$ (raise "Bad ~~@ argument: ~x0.  fmt-string is ~x1~%" look x)
                                     ps))
                            ((vl-msg look)))
                         (vl-fmt-aux look.msg 0 (length look.msg)
                                     (vl-fmt-pair-args look.args))))

                  (otherwise
                   (prog2$ (raise "Unsupported directive: ~~~x0.  fmt-string is ~x1~%" type x)
                           ps))))))))
    (vl-fmt-aux x n xl alist))
  :prepwork
  ((local (in-theory (disable assoc-equal-elim)))
   (local (defthm acl2-count-of-vl-msg->args
            (implies (vl-msg-p x)
                     (<= (acl2-count (vl-msg->args x))
                         (acl2-count x)))
            :hints(("Goal" :in-theory (enable vl-msg-p
                                              vl-msg->args)))
            :rule-classes :linear))
   (local (defthm acl2-count-of-assoc
            (implies (assoc key alist)
                     (< (acl2-count (cdr (assoc key alist)))
                        (acl2-count (strip-cdrs alist))))
            :hints(("Goal" :in-theory (enable assoc-equal strip-cdrs)))
            :rule-classes :linear))
   (local (defthm assoc-when-not-consp
            (implies (not (consp alist))
                     (not (assoc-equal k alist)))
            :hints(("Goal" :in-theory (enable assoc-equal)))))))

(define vl-fmt ((x stringp) (alist alistp) &key (ps 'ps))
  :inline t
  (let ((x (string-fix x)))
    (vl-fmt-aux x 0 (length x) alist)))


(defsection vl-cw
  :parents (verilog-printing)
  :short "@(see cw)-like function for printing to @(see ps), with support for
pretty-printing Verilog constructs as in @(see vl-fmt)."

  (defmacro vl-cw (x &rest args)
    `(vl-fmt ,x (vl-fmt-pair-args (list ,@args)))))


(define vl-cw-obj ((msg stringp) args &key (ps 'ps))
  :parents (verilog-printing)
  :short "Similar to @(see vl-cw), but the arguments are given as a list
instead of as macro arguments."
  :long "<p>For example:</p>

@({
    (vl-cw \"hello ~x0 ~x1 ~x2\" 3 4 5)
      --->
    (vl-cw-obj \"hello ~x0 ~x1 ~x2\" (list 3 4 5))
})

<p>This can be useful for grouping up arguments into cons structures.</p>

<p>BOZO I should probably implement something like @('~@') and use @(see msg)
instead.</p>"

  (cond ((<= (len args) 10)
         (vl-fmt msg (pairlis$
                      '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                      (list-fix args))))
        (t
         (prog2$ (raise "vl-cw-obj is limited to 10 arguments.")
                 ps))))


(define vl-print-msg ((x vl-msg-p) &key (ps 'ps))
  (b* (((vl-msg x)))
    (vl-fmt-aux x.msg 0 (length x.msg)
                (vl-fmt-pair-args x.args))))
