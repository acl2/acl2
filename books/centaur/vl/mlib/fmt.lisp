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
(include-book "writer")
(include-book "context")
(include-book "print-context")
(local (include-book "../util/arithmetic"))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (in-theory (enable acl2::arith-equiv-forwarding)))
(local (std::add-default-post-define-hook :fix))


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
        ((vl-id-p x)
         (vl-print-wirename (vl-id->name x)))
        (t
         (vl-fmt-tilde-x x))))

(define vl-fmt-tilde-a (x &key (ps 'ps))
  (case (tag x)
    (:vl-location
     (if (vl-location-p x)
         (vl-print-loc x)
       (vl-fmt-tilde-x x)))
    ((:atom :nonatom)
     (if (vl-expr-p x)
         (vl-pp-origexpr x)
       (vl-fmt-tilde-x x)))
    ((:vl-range)
     (if (vl-range-p x)
         (vl-pp-range x)
       (vl-fmt-tilde-x x)))
    ((:vl-context)
     (if (vl-context-p x)
         (vl-pp-context-summary x)
       (vl-fmt-tilde-x x)))
    ((:vl-port :vl-portdecl :vl-assign :vl-netdecl :vl-vardecl
      :vl-regdecl :vl-eventdecl :vl-paramdecl :vl-fundecl :vl-taskdecl
      :vl-modinst :vl-gateinst :vl-always :vl-initial)
     (if (vl-modelement-p x)
         (vl-pp-modelement-summary x)
       (vl-fmt-tilde-x x)))
    ((:vl-plainarg)
     (if (vl-plainarg-p x)
         (vl-pp-plainarg x)
       (vl-fmt-tilde-x x)))
    ((:vl-namedarg)
     (if (vl-namedarg-p x)
         (vl-pp-namedarg x)
       (vl-fmt-tilde-x x)))
    ((:vl-nullstmt :vl-assignstmt :vl-deassignstmt :vl-enablestmt
      :vl-disablestmt :vl-eventtriggerstmt :vl-casestmt :vl-ifstmt
      :vl-foreverstmt :vl-waitstmt :vl-repeatstmt :vl-whilestmt
      :vl-forstmt :vl-blockstmt :vl-timingstmt)
     (if (vl-stmt-p x)
         (vl-pp-stmt x)
       (vl-fmt-tilde-x x)))
    ((:vl-module)
     (if (vl-module-p x)
         (vl-pp-modulename-link-aux (vl-module->name x)
                                    (vl-module->origname x))
       (vl-fmt-tilde-x x)))
    (otherwise
     (vl-fmt-tilde-x x))))

(define vl-fmt-aux ((x stringp)
                    (n natp)
                    (xl (eql xl (length x)))
                    (alist alistp)
                    &key
                    (ps 'ps))
  :verbosep t
  :guard (<= n xl)
  :measure (nfix (- (nfix xl) (nfix n)))
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
                  (otherwise
                   (prog2$ (raise "Unsupported directive: ~~~x0.~%" type)
                           ps))))))))
    (vl-fmt-aux x n xl alist))
  :prepwork
  ((local (in-theory (disable assoc-equal-elim)))))

(define vl-fmt ((x stringp) (alist alistp) &key (ps 'ps))
  :inline t
  (let ((x (string-fix x)))
    (vl-fmt-aux x 0 (length x) alist)))


(defsection vl-cw
  :parents (verilog-printing)
  :short "@(see cw)-like function for printing to @(see ps), with support for
pretty-printing Verilog constructs as in @(see vl-fmt)."

  (defmacro vl-cw (x &rest args)
    `(vl-fmt ,x (pairlis$
                 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                 (list ,@args)))))


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
                      (redundant-list-fix args))))
        (t
         (prog2$ (raise "vl-cw-obj is limited to 10 arguments.")
                 ps))))

