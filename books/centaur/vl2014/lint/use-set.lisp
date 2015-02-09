; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "typo-detect")
(include-book "use-set-report")
(include-book "../mlib/allexprs")
(include-book "../mlib/port-tools")
(include-book "../mlib/find")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(set-state-ok t)


(defxdoc use-set
  :parents (vl2014)
  :short "Tool for detecting unused and unset wires."

  :long "<p><b>USE-SET</b> is a simple tool for detecting wires which may be
unset or unused.  This is a primitive, static analysis that can be carried out
on the Verilog source tree.</p>

<p><b>Unset</b> wires are those which have no values flowing into them. An
unset wire should satisfy the following properties:</p>

<ol>
 <li>No \"assign\" statement is assigning a value to it, and</li>
 <li>It is not in any submodule's output (\"driven from below\")</li>
 <li>It is not a primary input (\"driven from above\")</li>
</ol>

<p><b>Unused</b> wires are those whose values are not sent anywhere. An unused
wire should satisfy the following properties:</p>

<ol>
 <li>It is not in the RHS of any assignment</li>
 <li>It is not in any submodule's input (\"possibly used below\")</li>
 <li>It is not a primary output (\"possibly used above\")</li>
</ol>

<h3>Limitations</h3>

<ul>

<li>USE-SET does not currently look at always or initial statements. If wires
are only used or set in these statements, they may not be reported
correctly.</li>

<li>USE-SET is not at all clever: it will not realize that @('bar') is unused
in code such as @('assign foo = 1'b0 & bar;') or @('assign foo = {0
{bar}};')</li>

<li>USE-SET does not know about the C code that implements RAM modules in
speedsim, etc., and will think that such wires are unset.</li>

<li>USE-SET does not consider the individual bits of a vector. For instance, if
you just write:

@({
wire [7:0] foo;
assign foo[0] = 1'b0;
})

It treats the entire wire @('foo') as set, even though @('foo[0]') is the only
bit that has really been set.</li>

</ul>

<h3>Implementation</h3>

<p>To carry out the analysis, our high-level approach is as follows.  For each
module, we construct a fast alist that associates each wire with a VL-WIREINFO
object.  This info object includes boolean flags that indicate whether the
wire has been used or set.  Then, we simply walk over this alist to print out
any wires which are either unused or unset.  We imagine that we may eventually
want to add additional kinds of information here.</p>")

(local (xdoc::set-default-parents use-set))

(define vl-vardecllist-impexp-names ((decls vl-vardecllist-p) implicit explicit)
  :short "Split a list of net declarations into those which are implicit and
          those which are explicit.  Note that this only works if
          vl-modulelist-make-implicit-wires has been run!"
  :returns (mv (implicit string-listp
                         :hyp (force (string-listp implicit)))
               (explicit string-listp
                         :hyp (force (string-listp explicit))))
  (b* (((when (atom decls))
        (mv implicit explicit))
       ((vl-vardecl x1) (vl-vardecl-fix (car decls)))
       ((when (assoc-equal "VL_IMPLICIT" x1.atts))
        (vl-vardecllist-impexp-names (cdr decls)
                                     (cons x1.name implicit)
                                     explicit)))
    (vl-vardecllist-impexp-names (cdr decls)
                                 implicit
                                 (cons x1.name explicit))))

(define vl-module-impexp-names ((x vl-module-p))
  :returns (mv (implicit string-listp :hyp :fguard)
               (explicit string-listp :hyp :fguard))
  (vl-vardecllist-impexp-names (vl-module->vardecls x) nil nil))

(defaggregate vl-wireinfo
  ((usedp booleanp :rule-classes :type-prescription)
   (setp  booleanp :rule-classes :type-prescription))
  :tag :vl-wireinfo
  :short "Information about a single wire.")

(defalist vl-wireinfo-alistp (x)
  :key (stringp x)
  :val (vl-wireinfo-p x)
  :keyp-of-nil nil
  :valp-of-nil nil)

(define vl-collect-unused-or-unset-wires ((x vl-wireinfo-alistp)
                                          (unused string-listp)
                                          (unset string-listp))
  :short "Gather names of unused/unset wires from a wireinfo alist."
  :returns (mv (unused string-listp :hyp :fguard)
               (unset  string-listp :hyp :fguard))
  (b* (((when (atom x))
        (mv unused unset))
       (name  (caar x))
       (info  (cdar x))
       (usedp (vl-wireinfo->usedp info))
       (setp  (vl-wireinfo->setp info)))
    (vl-collect-unused-or-unset-wires (cdr x)
                                      (if usedp unused (cons name unused))
                                      (if setp unset (cons name unset)))))

(define vl-make-initial-wireinfo-alist
  :short "Create an initial wireinfo alist by we associating each wire with a
  new vl-wireinfo entry."
  ((x string-listp "Names of all wires declared in a module."))
  :returns (alist vl-wireinfo-alistp :hyp :fguard)
  (if (atom x)
      nil
    (hons-acons (car x)
                (make-vl-wireinfo :usedp nil :setp nil)
                (vl-make-initial-wireinfo-alist (cdr x)))))

(define vl-mark-wire-used ((x stringp)
                           warnp
                           (alist vl-wireinfo-alistp))
  :returns (new-alist vl-wireinfo-alistp :hyp :fguard)
  (b* ((info (cdr (hons-get x alist)))
       ;; If we are properly finding and inferring all wire declarations, then
       ;; the following case should never occur.  We check for it anyway, just
       ;; in case.
       (- (or info
              (not warnp)
              (cw "In vl-mark-wire-used: expected all wires to be in the ~
                   wireinfo-alist, but ~x0 is not.  Adding a new entry for ~
                   it.~%" x)))
       (current-usedp (and info (vl-wireinfo->usedp info)))
       (current-setp  (and info (vl-wireinfo->setp info)))
       ((when current-usedp)
        alist))
    (hons-acons x
                (make-vl-wireinfo :usedp t :setp current-setp)
                alist)))

(define vl-mark-wires-used ((x string-listp)
                            warnp
                            (alist vl-wireinfo-alistp))
  :returns (new-alist vl-wireinfo-alistp :hyp :fguard)
  (if (atom x)
      alist
    (let ((alist (vl-mark-wire-used (car x) warnp alist)))
      (vl-mark-wires-used (cdr x) warnp alist))))

(define vl-mark-wire-set ((x stringp)
                          warnp
                          (alist vl-wireinfo-alistp))
  :returns (new-alist vl-wireinfo-alistp :hyp :fguard)
  (b* ((info (cdr (hons-get x alist)))
       ;; As above, we expect that this should never occur, but we check for it
       ;; and handle it, just in case.
       (- (or info
              (not warnp)
              (cw "In vl-mark-wire-set: expected all wires to be in the ~
                   wireinfo-alist, but ~x0 is not.  Adding a new entry for ~
                   it.~%" x)))
       (current-usedp (and info (vl-wireinfo->usedp info)))
       (current-setp  (and info (vl-wireinfo->setp info)))
       ;; Only update the alist if necessary
       ((when current-setp)
        alist))
    (hons-acons x
                (make-vl-wireinfo :usedp current-usedp :setp t)
                alist)))

(define vl-mark-wires-set ((x string-listp)
                           warnp
                           (alist vl-wireinfo-alistp))
  :returns (new-alist vl-wireinfo-alistp :hyp :fguard)
  (if (atom x)
      alist
    (let ((alist (vl-mark-wire-set (car x) warnp alist)))
      (vl-mark-wires-set (cdr x) warnp alist))))


; We now get into the actual analysis.

(define vl-mark-wires-for-assignment ((x vl-assign-p)
                                      (alist vl-wireinfo-alistp))
  :returns (new-alist vl-wireinfo-alistp :hyp :fguard)
  (b* ((lvalue (vl-assign->lvalue x))
       (rhs    (vl-assign->expr x))
       ;; BOZO consider removing duplicates
       (alist  (vl-mark-wires-set (vl-expr-names lvalue) t alist)))
    (vl-mark-wires-used (vl-expr-names rhs) t alist)))

(define vl-mark-wires-for-assignlist ((x vl-assignlist-p)
                                      (alist vl-wireinfo-alistp))
  :returns (new-alist vl-wireinfo-alistp :hyp :fguard)
  (b* (((when (atom x))
        alist)
       (alist (vl-mark-wires-for-assignment (car x) alist)))
    (vl-mark-wires-for-assignlist (cdr x) alist)))


(define vl-mark-wires-for-plainarg ((x vl-plainarg-p)
                                    (alist vl-wireinfo-alistp)
                                    (warning-wires string-listp))
  :short "Process a plain argument and mark its wires in the alist.  If the
          direction of the argument hasn't been resolved, return the list of
          any wires that have been used, so that we can issue a warning about
          them."
  :returns (mv (new-alist vl-wireinfo-alistp :hyp :fguard)
               (warning-wires string-listp :hyp :fguard))
  (b* ((expr (vl-plainarg->expr x))
       (dir  (vl-plainarg->dir x))
       ((unless expr)
        (mv alist warning-wires))
       ;; BOZO worthwhile to remove duplicates?
       (wires (vl-expr-names expr)))
    (case dir
      (:vl-input
       ;; The argument is an input to the submodule, so the wire is being
       ;; USED.
       (mv (vl-mark-wires-used wires t alist) warning-wires))
      (:vl-output
       ;; The argument is an output from the submodule, so the wire is
       ;; being SET.
       (mv (vl-mark-wires-set wires t alist) warning-wires))
      (:vl-inout
       ;; The argument is simultaneously an input and output to the
       ;; submodule; I guess we should call it both marked and set.
       (let* ((alist (vl-mark-wires-used wires t alist))
              (alist (vl-mark-wires-set wires t alist)))
         (mv alist warning-wires)))
      (t
       ;; We really want to expect that everything has a direction, but
       ;; if the direction isn't marked we'll at least issue a warning.
       (mv alist (revappend wires warning-wires))))))

(define vl-mark-wires-for-plainarglist ((x vl-plainarglist-p)
                                        (alist vl-wireinfo-alistp)
                                        (warning-wires string-listp))
  :returns (mv (new-alist vl-wireinfo-alistp :hyp :fguard)
               (warning-wires string-listp :hyp :fguard))
  (b* (((when (atom x))
        (mv alist warning-wires))
       ((mv alist warning-wires)
        (vl-mark-wires-for-plainarg (car x) alist warning-wires)))
    (vl-mark-wires-for-plainarglist (cdr x) alist warning-wires)))

(define vl-mark-wires-for-arguments ((x vl-arguments-p)
                                     (alist vl-wireinfo-alistp))
  :returns (mv (new-alist vl-wireinfo-alistp :hyp :fguard)
               (warning-wires string-listp :hyp :fguard))
  (vl-arguments-case x
    :vl-arguments-named
    ;; Argresolve should have gotten rid of these.  We just collect up all of
    ;; the wires, so we can report about them.
    (mv alist (vl-exprlist-names (vl-namedarglist-allexprs x.args)))
    :vl-arguments-plain
    (vl-mark-wires-for-plainarglist x.args alist nil)))


(define vl-mark-wires-for-modinst ((x vl-modinst-p)
                                   (alist vl-wireinfo-alistp)
                                   (warnings vl-warninglist-p))
  :returns (mv (new-alist vl-wireinfo-alistp
                          :hyp (and (force (vl-modinst-p x))
                                    (force (vl-wireinfo-alistp alist))))
               (new-warnings vl-warninglist-p)
               (warning-wires string-listp
                              :hyp (and (force (vl-modinst-p x))
                                        (force (vl-wireinfo-alistp alist)))))
  (b* ((portargs  (vl-modinst->portargs x))
       (paramargs (vl-modinst->paramargs x))
       (range     (vl-modinst->range x))
       ((mv alist warning-wires) (vl-mark-wires-for-arguments portargs alist))
       (warnings (if (not warning-wires)
                     (ok)
                   (warn :type :vl-modinst-args-unresolved
                         :msg "In ~a0, arguments are not resolved."
                         :args (list x))))
       ;; We originally thought we would stop there.  But now I have realized
       ;; that parameters are sometimes only used in the paramlist or ranges of
       ;; module instances.  So, now we collect wires from those and mark them
       ;; as used.
       (param-wires (vl-exprlist-names (vl-paramargs-allexprs paramargs)))
       (range-wires (vl-exprlist-names (vl-maybe-range-allexprs range)))
       (alist       (vl-mark-wires-used param-wires t alist))
       (alist       (vl-mark-wires-used range-wires t alist)))
      (mv alist warnings warning-wires)))

(define vl-mark-wires-for-modinstlist ((x vl-modinstlist-p)
                                       (alist vl-wireinfo-alistp)
                                       (warnings vl-warninglist-p))
  :returns (mv (new-alist vl-wireinfo-alistp
                          :hyp (and (force (vl-modinstlist-p x))
                                    (force (vl-wireinfo-alistp alist))))
               (new-warnings vl-warninglist-p)
               (warning-wires string-listp
                              :hyp (and (force (vl-modinstlist-p x))
                                        (force (vl-wireinfo-alistp alist)))))
  (b* (((when (atom x))
        (mv alist (ok) nil))
       ((mv alist warnings warning-wires1)
        (vl-mark-wires-for-modinst (car x) alist warnings))
       ((mv alist warnings warning-wires2)
        (vl-mark-wires-for-modinstlist (cdr x) alist warnings)))
    (mv alist warnings (append warning-wires1 warning-wires2))))

(define vl-mark-wires-for-gateinst ((x vl-gateinst-p)
                                    (alist vl-wireinfo-alistp)
                                    (warnings vl-warninglist-p))
  :returns (mv (new-alist vl-wireinfo-alistp
                          :hyp (and (force (vl-gateinst-p x))
                                    (force (vl-wireinfo-alistp alist))))
               (new-warnings vl-warninglist-p)
               (warning-wires string-listp
                              :hyp (and (force (vl-gateinst-p x))
                                        (force (vl-wireinfo-alistp alist)))))
  (b* ((args  (vl-gateinst->args x))
       (range (vl-gateinst->range x))
       ((mv alist warning-wires) (vl-mark-wires-for-plainarglist args alist nil))
       (warnings (if (not warning-wires)
                     (ok)
                   (warn :type :vl-gateinst-args-unresolved
                         :msg "In ~a0, arguments are not resolved."
                         :args (list x))))
       (range-wires (vl-exprlist-names (vl-maybe-range-allexprs range)))
       (alist       (vl-mark-wires-used range-wires t alist)))
      (mv alist warnings warning-wires)))

(define vl-mark-wires-for-gateinstlist ((x vl-gateinstlist-p)
                                        (alist vl-wireinfo-alistp)
                                        (warnings vl-warninglist-p))
  :returns (mv (new-alist vl-wireinfo-alistp
                          :hyp (and (force (vl-gateinstlist-p x))
                                    (force (vl-wireinfo-alistp alist))))
               (new-warnings vl-warninglist-p)
               (warning-wires string-listp
                              :hyp (and (force (vl-gateinstlist-p x))
                                        (force (vl-wireinfo-alistp alist)))))
  (b* (((when (atom x))
        (mv alist (ok) nil))
       ((mv alist warnings warning-wires1)
        (vl-mark-wires-for-gateinst (car x) alist warnings))
       ((mv alist warnings warning-wires2)
        (vl-mark-wires-for-gateinstlist (cdr x) alist warnings)))
    (mv alist warnings (append warning-wires1 warning-wires2))))

; That's definitely most of the analysis.  Now there are some odd cases that we
; wish to cover.  In particular, the declarations of wires, registers, and so on,
; can include ranges, which may include the names of parameters.  We want to be
; sure to mark those as used.

(define vl-clean-up-warning-wires ((wires string-listp)
                                   (alist vl-wireinfo-alistp))
  :short "Remove any warning wires that we know are used and set."
  :long "<p>We are given the list of warning wires that have been generated,
and the completedly wireinfo alist.  We only want to actually warn about wires
which were (1) flagged as maybe bad, and (2) currently appear to be unset or
unused.  The other wires are thrown away.</p>"
  :returns (new-warning-wires string-listp :hyp :fguard)
  (b* (((when (atom wires))
        nil)
       (entry        (cdr (hons-get (car wires) alist)))
       (really-warnp (or (not entry)
                         (not (vl-wireinfo->usedp entry))
                         (not (vl-wireinfo->setp entry))))
       ((when really-warnp)
        (cons (car wires) (vl-clean-up-warning-wires (cdr wires) alist))))
    (vl-clean-up-warning-wires (cdr wires) alist)))


(define vl-annotate-vardecl-with-wireinfo
  :short "Annotate vardecls with the results of use-set analysis."
  ((x      vl-vardecl-p       "A net declaration.")
   (alist  vl-wireinfo-alistp "The wireinfo alist we collected for this module.")
   (wwires string-listp       "The warning wires we're unsure about."))
  :returns (new-x vl-vardecl-p :hyp (force (vl-vardecl-p x))
                  "A copy of X, possibly extended with some attributes.")

  :long "<p>We add as many as two annotations to X.  The possible annotations
we add are</p>

<ul>
<li>@('VL_UNUSED') - Appears to be unused, not a warning wire</li>
<li>@('VL_MAYBE_UNUSED') - Appears to be unused, but is a warning wire</li>
<li>@('VL_UNSET') - Appears to be unset, not a warning wire</li>
<li>@('VL_MAYBE_UNSET') - Appears to be unset, but is a warning wire</li>
</ul>"

  (b* ((name         (vl-vardecl->name x))
       (info         (cdr (hons-get name alist)))
       ((unless info)
        (raise "No wireinfo entry for ~s0." name)
        x)
       (usedp        (vl-wireinfo->usedp info))
       (setp         (vl-wireinfo->setp info))
       ((when (and usedp setp))
        ;; No annotations to make, so just return x unchanged right away.
        x)
       (atts         (vl-vardecl->atts x))
       (warnp        (member-equal name wwires))
       (atts         (cond (usedp atts)
                           (warnp (cons (list "VL_MAYBE_UNUSED") atts))
                           (t     (cons (list "VL_UNUSED") atts))))
       (atts         (cond (setp  atts)
                           (warnp (cons (list "VL_MAYBE_UNSET") atts))
                           (t     (cons (list "VL_UNSET") atts)))))
    (change-vl-vardecl x :atts atts)))

(defprojection vl-annotate-vardecllist-with-wireinfo (x alist wwires)
  (vl-annotate-vardecl-with-wireinfo x alist wwires)
  :guard (and (vl-vardecllist-p x)
              (vl-wireinfo-alistp alist)
              (string-listp wwires))
  ///
  (defthm vl-vardecllist-p-of-vl-annotate-vardecllist-with-wireinfo
    (implies (force (vl-vardecllist-p x))
             (vl-vardecllist-p
              (vl-annotate-vardecllist-with-wireinfo x alist wwires)))))

(define vl-mark-wires-for-module
  :short "Main function that performs the use-set analysis.  We figure out
          which wires appear to be used and unused in the module X.  We
          annotate the vardecls for the module with these attributes, and also
          generate a more concise vl-useset-report-entry object describing the
          status of this module."
  ((x    vl-module-p  "Module to analyze.")
   (omit string-listp "Names of any special wires to omit,"))
  :returns (mv (new-x vl-module-p :hyp (vl-module-p x))
               (report-entry vl-useset-report-entry-p :hyp :fguard))
  (b* (((vl-module x) x)

       (warnings x.warnings)

; This stuff never was any good.
;
; ; New addition: active high/low computation.  We just do this at the start of
; ; things.
;
;        (active-entry        (vl-module-active-check x))
;        (mismatches          (vl-activereportentry->mismatches active-entry))
;       ;; I think we don't want these warnings.  They're just noisy.
;       ;; (active-warnings     (vl-activereportentry->warnings active-entry))
;       ;; (warnings            (append-without-guard active-warnings warnings))

; We construct the initial alist by grabbing the names of all declared wires
; and marking them as unused and unset.  Then, fill in the alist so that the
; parameters, inputs, and inouts are regarded as "set from above", and the
; outputs and inouts are regarded as "used above."


       (declared-wires      (vl-vardecllist->names-exec x.vardecls nil))

       (params              (vl-paramdecllist->names-exec x.paramdecls nil))
       ((mv in out inout)   (vl-portdecllist-names-by-direction x.portdecls nil nil nil))

       (alist               (vl-make-initial-wireinfo-alist
                             (revappend params declared-wires)))

; Special addition: we allow the user to specify that certain wires should be
; omitted from the report.  To accomplish this, just mark these wires as both
; used and set before we continue.

       (alist (vl-mark-wires-set omit nil alist))
       (alist (vl-mark-wires-used omit nil alist))

; Basic initialization for inputs, outputs, parameters.  We think of inputs and
; parameters as set, and outputs as used.

       (alist (vl-mark-wires-set params t alist))
       (alist (vl-mark-wires-set in t alist))
       (alist (vl-mark-wires-set inout t alist))
       (alist (vl-mark-wires-used out t alist))
       (alist (vl-mark-wires-used inout t alist))

; Additional initialization, mainly to catch the use of parameters in
; declarations.

       (alist (vl-mark-wires-used (vl-exprlist-names (vl-portdecllist-allexprs x.portdecls)) t alist))
       (alist (vl-mark-wires-used (vl-exprlist-names (vl-vardecllist-allexprs x.vardecls)) t alist))
       (alist (vl-mark-wires-used (vl-exprlist-names (vl-paramdecllist-allexprs x.paramdecls)) t alist))

; Now we're on to the core of our analysis.  We sweep through the assignments,
; module instances, and gate instances and mark that every wire is either used
; or set when it is encountered.  If we do not know the direction of a port, we
; may issue warnings about particular wires.  So, in addition to updating the
; alist, we generate lists of warnings and a list of wires that we are not sure
; about.

       (warnings (if (and (atom x.alwayses)
                          (atom x.initials))
                     (ok)
                   (warn :type :vl-useset-statements-ignored
                         :msg "Use-Set note: always and initial statements ~
                               are currently ignored in our wire analysis, so ~
                               use-set results may be incorrect.")))
       (alist (vl-mark-wires-for-assignlist x.assigns alist))
       ((mv alist warnings warning-wires1)
        (vl-mark-wires-for-modinstlist x.modinsts alist warnings))
       ((mv alist warnings warning-wires2)
        (vl-mark-wires-for-gateinstlist x.gateinsts alist warnings))

; We now clean up the warning wires.  What is this about?  Well, initially
; every wire is marked as unused and unset.  When we encounter a port and
; aren't sure about its direction, we don't update the alist but we note that
; every wire used in the port is suspicious.  If, later, it turns out that we
; actually used and set that wire, then we don't really need to think of it as
; suspicious anymore, so we throw it away.

       (warning-wires       (vl-clean-up-warning-wires
                             (mergesort (append warning-wires1 warning-wires2))
                             alist))

; Now gather up the info out of the alist, make the new list of vardecls, and
; update the module.

       (-                   (fast-alist-free alist))
       (alist               (hons-shrink-alist alist nil))
       ((mv unused unset)   (vl-collect-unused-or-unset-wires alist nil nil))
       (unused              (mergesort unused))
       (unset               (mergesort unset))

       (new-vardecls        (if (or unused unset)
                                (vl-annotate-vardecllist-with-wireinfo x.vardecls alist warning-wires)
                              x.vardecls))
       (x-prime             (change-vl-module x
                                              :vardecls new-vardecls
                                              :warnings warnings))

; For typo detection, figure out which wires are implicit.  The wires we
; will look at are the implicit wires that are either unused or unset.

       ((mv implicit ?explicit) (vl-module-impexp-names x))
       (implicit                (mergesort implicit))
       (bad                     (intersect implicit (union unused unset)))
       (good                    (difference (mergesort declared-wires) bad))
       (typos                   (typo-detect bad good))


; For input lvalues, we just need to look at the ports, since we annotate
; them separately.

;       (lvalue-inputs (vl-portdecllist->names
;                       (vl-gather-portdecls-with-attribute portdecls "VL_LVALUE_INPUT")))


; Finally, build the report.
       (spurious            (intersect unused unset))
       (unused              (difference unused spurious))
       (unset               (difference unset spurious))



       (report-entry        (make-vl-useset-report-entry :name x.name
                                                         :spurious spurious
                                                         :unused unused
                                                         :unset unset
                                                         :wwires warning-wires
                                                         :warnings warnings
                                                         :typos typos
;:mismatches mismatches
;:lvalue-inputs lvalue-inputs
                                                         )))
    (fast-alist-free alist)
    (mv x-prime report-entry)))

(define vl-mark-wires-for-modulelist
  :short "Carry out use-set analysis on all modules."
  ((x    vl-modulelist-p "Modules to analyze")
   (omit string-listp    "Special wires not to report as unused/unset."))
  :returns
  (mv (new-x vl-modulelist-p :hyp (vl-modulelist-p x)
             "Updated modules, where perhaps some wires have been annotated
              with attributes like @('VL_UNUSED').")
      (report vl-useset-report-p :hyp :guard
              "Report about unused/unset wires for all modules."))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv car-prime car-entry) (vl-mark-wires-for-module (car x) omit))
       ((mv cdr-prime cdr-report) (vl-mark-wires-for-modulelist (cdr x) omit)))
    (mv (cons car-prime cdr-prime)
        (cons car-entry cdr-report))))

(define vl-design-use-set-report ((x    vl-design-p)
                                  (omit string-listp))
  :returns (mv (new-x  vl-design-p)
               (report vl-useset-report-p))
  (b* ((x    (vl-design-fix x))
       (omit (mbe :logic (if (string-listp omit) omit nil)
                  :exec omit))
       ((vl-design x) x)
       ((mv new-mods report)
        (vl-mark-wires-for-modulelist x.mods omit))
       (new-x (change-vl-design x :mods new-mods)))
    (mv new-x report)))


