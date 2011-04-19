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
(include-book "typo-detect")
(include-book "use-set-report")
(include-book "../mlib/warnings")
(include-book "../mlib/allexprs")
(include-book "../mlib/find-item")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(set-state-ok t)


(defxdoc use-set
  :parents (vl)

  :short "Tool for detecting unused and unset wires."

  :long "<p><b>USE-SET</b> is a simple tool for detecting wires which may be
unset or unused.  This is a primitive, static analysis that can be carried out
on the Verilog source tree, and does involve any use of E.</p>

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

<li>USE-SET is not at all clever: it will not realize that <tt>bar</tt> is
unused in code such as <tt>assign foo = 1'b0 &amp; bar;</tt> or <tt>assign foo = {0
{bar}};</tt></li>

<li>USE-SET does not know about the C code that implements RAM modules in
speedsim, etc., and will think that such wires are unset.</li>

<li>USE-SET does not consider the individual bits of a vector. For instance, if
you just write:

<code>
wire [7:0] foo;
assign foo[0] = 1'b0;
</code>

It treats the entire wire <tt>foo</tt> as set, even though <tt>foo[0]</tt> is
the only bit that has really been set.</li>

</ul>

<h3>Implementation</h3>

<p>To carry out the analysis, our high-level approach is as follows.  For each
module, we construct a fast alist that associates each wire with a VL-WIREINFO
object.  This info object includes boolean flags that indicate whether the
wire has been used or set.  Then, we simply walk over this alist to print out
any wires which are either unused or unset.  We imagine that we may eventually
want to add additional kinds of information here.</p>")


(defsection vl-netdecllist-impexp-names

  (defund vl-netdecllist-impexp-names (decls implicit explicit)
    ;; Split a list of net declarations into those which are implicit and those
    ;; which are explicit.  Note that this only works if
    ;; vl-modulelist-make-implicit-wires has been run!
    "Returns (MV IMPLICIT EXPLICIT)"
    (declare (xargs :guard (vl-netdecllist-p decls)))
    (cond ((atom decls)
           (mv implicit explicit))
          ((assoc-equal "VL_IMPLICIT" (vl-netdecl->atts (car decls)))
           (vl-netdecllist-impexp-names (cdr decls)
                                        (cons (vl-netdecl->name (car decls)) implicit)
                                        explicit))
          (t
           (vl-netdecllist-impexp-names (cdr decls)
                                        implicit
                                        (cons (vl-netdecl->name (car decls)) explicit)))))

  (local (in-theory (enable vl-netdecllist-impexp-names)))

  (defthm string-listp-of-vl-netdecllist-impexp-names-0
    (implies (and (force (vl-netdecllist-p decls))
                  (force (string-listp implicit)))
             (string-listp (mv-nth 0 (vl-netdecllist-impexp-names decls implicit explicit)))))

  (defthm string-listp-of-vl-netdecllist-impexp-names-1
    (implies (and (force (vl-netdecllist-p decls))
                  (force (string-listp explicit)))
             (string-listp (mv-nth 1 (vl-netdecllist-impexp-names decls implicit explicit))))))


(defsection vl-module-impexp-names

  (defund vl-module-impexp-names (x)
    "Returns (MV IMPLICIT EXPLICIT)"
    (declare (xargs :guard (vl-module-p x)))
    (vl-netdecllist-impexp-names (vl-module->netdecls x) nil nil))

  (local (in-theory (enable vl-module-impexp-names)))

  (defthm string-listp-of-vl-module-impexp-names-0
    (implies (force (vl-module-p x))
             (string-listp (mv-nth 0 (vl-module-impexp-names x)))))

  (defthm string-listp-of-vl-module-impexp-names-1
    (implies (force (vl-module-p x))
             (string-listp (mv-nth 1 (vl-module-impexp-names x))))))


(defaggregate vl-wireinfo
  (usedp setp)
  :require ((booleanp-of-vl-wireinfo->usedp  (booleanp usedp))
            (booleanp-of-vl-wireinfo->setp   (booleanp setp)))
  :tag :vl-wireinfo
  :parents (use-set))


(defsection vl-wireinfo-alistp

  (defund vl-wireinfo-alistp (x)
    (declare (xargs :guard t))
    (if (atom x)
        (not x)
      (and (consp (car x))
           (stringp (caar x))
           (vl-wireinfo-p (cdar x))
           (vl-wireinfo-alistp (cdr x)))))

  (local (in-theory (enable vl-wireinfo-alistp)))

  (defthm vl-wireinfo-alistp-when-atom
    (implies (atom x)
             (equal (vl-wireinfo-alistp x)
                    (not x))))

  (defthm vl-wireinfo-alistp-of-cons
    (equal (vl-wireinfo-alistp (cons a x))
           (and (consp a)
                (stringp (car a))
                (vl-wireinfo-p (cdr a))
                (vl-wireinfo-alistp x))))

  (defthm alistp-when-vl-wireinfo-alistp
    (implies (vl-wireinfo-alistp x)
             (alistp x)))

  (defthm vl-wireinfo-alistp-of-hons-shrink-alist
    (implies (and (vl-wireinfo-alistp x)
                  (vl-wireinfo-alistp y))
             (vl-wireinfo-alistp (hons-shrink-alist x y)))
    :hints(("Goal" :in-theory (enable (:induction hons-shrink-alist)))))

  (defthm vl-wireinfo-p-of-cdr-of-hons-assoc-equal
    (implies (vl-wireinfo-alistp alist)
             (equal (vl-wireinfo-p (cdr (hons-assoc-equal wire alist)))
                    (if (hons-assoc-equal wire alist)
                        t
                      nil)))))



(defsection vl-collect-unused-or-unset-wires

  (defund vl-collect-unused-or-unset-wires (x unused unset)
    "Returns (MV UNUSED UNSET)"
    (declare (xargs :guard (and (vl-wireinfo-alistp x)
                                (string-listp unused)
                                (string-listp unset))))

; X is a wireinfo alist.  We accumulate the names of any wires which are unused
; or unset into the provided accumulators.

    (if (atom x)
        (mv unused unset)
      (let* ((name  (caar x))
             (info  (cdar x))
             (usedp (vl-wireinfo->usedp info))
             (setp  (vl-wireinfo->setp info)))
        (vl-collect-unused-or-unset-wires (cdr x)
                                          (if usedp unused (cons name unused))
                                          (if setp unset (cons name unset))))))

  (local (in-theory (enable vl-collect-unused-or-unset-wires)))

  (defthm string-listp-of-vl-collect-unused-or-unset-wires-0
    (implies (and (force (vl-wireinfo-alistp x))
                  (force (string-listp unused)))
             (string-listp (mv-nth 0 (vl-collect-unused-or-unset-wires x unused unset)))))

  (defthm string-listp-of-vl-collect-unused-or-unset-wires-1
    (implies (and (force (vl-wireinfo-alistp x))
                  (force (string-listp unset)))
             (string-listp (mv-nth 1 (vl-collect-unused-or-unset-wires x unused unset))))))



(defsection vl-make-initial-wireinfo-alist

  (defund vl-make-initial-wireinfo-alist (x)
    (declare (xargs :guard (string-listp x)))

; X is a list of the names of the wires declared in a module.  To create an
; initial wireinfo alist, we associate each wire with a new vl-wireinfo entry.

    (if (atom x)
        nil
      (hons-acons (car x)
                  (make-vl-wireinfo :usedp nil :setp nil)
                  (vl-make-initial-wireinfo-alist (cdr x)))))

  (local (in-theory (enable vl-make-initial-wireinfo-alist)))

  (defthm vl-wireinfo-alistp-of-vl-make-initial-wireinfo-alist
    (implies (force (string-listp x))
             (vl-wireinfo-alistp (vl-make-initial-wireinfo-alist x)))))



(defsection vl-mark-wire-used

  (defund vl-mark-wire-used (x warnp alist)
    (declare (xargs :guard (and (stringp x)
                                (vl-wireinfo-alistp alist))))

    (let ((info (cdr (hons-get x alist))))
      (prog2$
       ;; If we are properly finding and inferring all wire declarations, then
       ;; the following case should never occur.  We check for it anyway, just in
       ;; case.
       (or info
           (not warnp)
           (cw "In vl-mark-wire-used: expected all wires to be in the ~
                wireinfo-alist, but ~x0 is not.  Adding a new entry ~
                for it.~%" x))
       (let ((current-usedp (and info (vl-wireinfo->usedp info)))
             (current-setp  (and info (vl-wireinfo->setp info))))
         (if current-usedp
             alist
           (hons-acons x
                       (make-vl-wireinfo :usedp t :setp current-setp)
                       alist))))))

  (local (in-theory (enable vl-mark-wire-used)))

  (defthm vl-wireinfo-alistp-of-vl-mark-wire-used
    (implies (and (force (stringp x))
                  (force (vl-wireinfo-alistp alist)))
             (vl-wireinfo-alistp (vl-mark-wire-used x warnp alist)))))



(defsection vl-mark-wires-used

  (defund vl-mark-wires-used (x warnp alist)
    (declare (xargs :guard (and (string-listp x)
                                (vl-wireinfo-alistp alist))))
    (if (atom x)
        alist
      (let ((alist (vl-mark-wire-used (car x) warnp alist)))
        (vl-mark-wires-used (cdr x) warnp alist))))

  (local (in-theory (enable vl-mark-wires-used)))

  (defthm vl-wireinfo-alistp-of-vl-mark-wires-used
    (implies (and (force (string-listp x))
                  (force (vl-wireinfo-alistp alist)))
             (vl-wireinfo-alistp (vl-mark-wires-used x warnp alist)))))


(defsection vl-mark-wire-set

  (defund vl-mark-wire-set (x warnp alist)
    (declare (xargs :guard (and (stringp x)
                                (vl-wireinfo-alistp alist))))
    (let ((info (cdr (hons-get x alist))))
      (prog2$
       ;; As above, we expect that this should never occur, but we check for it
       ;; and handle it, just in case.
       (or info
           (not warnp)
           (cw "In vl-mark-wire-set: expected all wires to be in the ~
                wireinfo-alist, but ~x0 is not.  Adding a new entry ~
                for it.~%" x))

       (let ((current-usedp (and info (vl-wireinfo->usedp info)))
             (current-setp  (and info (vl-wireinfo->setp info))))
         ;; Only update the alist if necessary
         (if current-setp
             alist
           (hons-acons x
                       (make-vl-wireinfo :usedp current-usedp :setp t)
                       alist))))))

  (local (in-theory (enable vl-mark-wire-set)))

  (defthm vl-wireinfo-alistp-of-vl-mark-wire-set
    (implies (and (force (stringp x))
                  (force (vl-wireinfo-alistp alist)))
             (vl-wireinfo-alistp (vl-mark-wire-set x warnp alist)))))


(defsection vl-mark-wires-set

  (defund vl-mark-wires-set (x warnp alist)
    (declare (xargs :guard (and (string-listp x)
                                (vl-wireinfo-alistp alist))))
    (if (atom x)
        alist
      (let ((alist (vl-mark-wire-set (car x) warnp alist)))
        (vl-mark-wires-set (cdr x) warnp alist))))

  (local (in-theory (enable vl-mark-wires-set)))

  (defthm vl-wireinfo-alistp-of-vl-mark-wires-set
    (implies (and (force (string-listp x))
                  (force (vl-wireinfo-alistp alist)))
             (vl-wireinfo-alistp (vl-mark-wires-set x warnp alist)))))




; We now get into the actual analysis.

(defund vl-mark-wires-for-assignment (x alist)
  (declare (xargs :guard (and (vl-assign-p x)
                              (vl-wireinfo-alistp alist))))
  (let* ((lvalue (vl-assign->lvalue x))
         (rhs    (vl-assign->expr x))
         ;; BOZO consider removing duplicates
         (alist  (vl-mark-wires-set (vl-expr-names lvalue) t alist))
         (alist  (vl-mark-wires-used (vl-expr-names rhs) t alist)))
    alist))

(defthm vl-wireinfo-alistp-of-vl-mark-wires-for-assignment
  (implies (and (force (vl-assign-p x))
                (force (vl-wireinfo-alistp alist)))
           (vl-wireinfo-alistp (vl-mark-wires-for-assignment x alist)))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-assignment))))

(defund vl-mark-wires-for-assignlist (x alist)
  (declare (xargs :guard (and (vl-assignlist-p x)
                              (vl-wireinfo-alistp alist))))
  (if (atom x)
      alist
    (let* ((alist (vl-mark-wires-for-assignment (car x) alist))
           (alist (vl-mark-wires-for-assignlist (cdr x) alist)))
      alist)))

(defthm vl-wireinfo-alistp-of-mark-wires-for-assignlist
  (implies (and (force (vl-assignlist-p x))
                (force (vl-wireinfo-alistp alist)))
           (vl-wireinfo-alistp (vl-mark-wires-for-assignlist x alist)))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-assignlist))))




(defund vl-mark-wires-for-plainarg (x alist warning-wires)
  "Returns (MV ALIST' WARNING-WIRES')"
  (declare (xargs :guard (and (vl-plainarg-p x)
                              (vl-wireinfo-alistp alist)
                              (string-listp warning-wires))))

; Process a plain argument and mark its wires in the alist.  If the direction
; of the argument hasn't been resolved, return the list of any wires that have
; been used, so that we can issue a warning about them.

  (let ((expr (vl-plainarg->expr x))
        (dir  (vl-plainarg->dir x)))
    (if (not expr)
        (mv alist warning-wires)
      ;; BOZO worthwhile to remove duplicates?
      (let ((wires (vl-expr-names expr)))
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
           (mv alist (revappend wires warning-wires))))))))

(defthm vl-wireinfo-alistp-of-vl-mark-wires-for-plainarg
  (implies (and (force (vl-plainarg-p x))
                (force (vl-wireinfo-alistp alist)))
           (vl-wireinfo-alistp (mv-nth 0 (vl-mark-wires-for-plainarg x alist warning-wires))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-plainarg))))

(defthm string-listp-of-vl-mark-wires-for-plainarg
  (implies (and (force (vl-plainarg-p x))
                (force (string-listp warning-wires)))
           (string-listp (mv-nth 1 (vl-mark-wires-for-plainarg x alist warning-wires))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-plainarg))))



(defund vl-mark-wires-for-plainarglist (x alist warning-wires)
  "Returns (MV ALIST' WARNING-WIRES')"
  (declare (xargs :guard (and (vl-plainarglist-p x)
                              (vl-wireinfo-alistp alist)
                              (string-listp warning-wires))))
  (if (atom x)
      (mv alist warning-wires)
    (mv-let (alist warning-wires)
            (vl-mark-wires-for-plainarg (car x) alist warning-wires)
            (vl-mark-wires-for-plainarglist (cdr x) alist warning-wires))))

(defthm vl-wireinfo-alistp-of-vl-mark-wires-for-plainarglist
  (implies (and (force (vl-plainarglist-p x))
                (force (vl-wireinfo-alistp alist)))
           (vl-wireinfo-alistp (mv-nth 0 (vl-mark-wires-for-plainarglist x alist warning-wires))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-plainarglist))))

(defthm string-listp-of-vl-mark-wires-for-plainarglist
  (implies (and (force (vl-plainarglist-p x))
                (force (string-listp warning-wires)))
           (string-listp (mv-nth 1 (vl-mark-wires-for-plainarglist x alist warning-wires))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-plainarglist))))






(defund vl-mark-wires-for-arguments (x alist)
  "Returns (MV ALIST' WARNING-WIRES)"
  (declare (xargs :guard (and (vl-arguments-p x)
                              (vl-wireinfo-alistp alist))))
  (if (vl-arguments->namedp x)
      ;; Argresolve should have gotten rid of these.  We just collect up all of
      ;; the wires, so we can report about them.
      (mv alist (vl-exprlist-names (vl-namedarglist-allexprs (vl-arguments->args x))))
    (vl-mark-wires-for-plainarglist (vl-arguments->args x) alist nil)))

(defthm vl-wireinfo-alistp-of-vl-mark-wires-for-arguments
  (implies (and (force (vl-arguments-p x))
                (force (vl-wireinfo-alistp alist)))
           (vl-wireinfo-alistp (mv-nth 0 (vl-mark-wires-for-arguments x alist))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-arguments))))

(defthm string-listp-of-vl-mark-wires-for-arguments
  (implies (force (vl-arguments-p x))
           (string-listp (mv-nth 1 (vl-mark-wires-for-arguments x alist))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-arguments))))






(defund vl-mark-wires-for-modinst (x alist warnings)
  "Returns (MV ALIST' WARNINGS' WARNING-WIRES)"
  (declare (xargs :guard (and (vl-modinst-p x)
                              (vl-wireinfo-alistp alist)
                              (vl-warninglist-p warnings))))
  (b* ((portargs  (vl-modinst->portargs x))
       (paramargs (vl-modinst->paramargs x))
       (range     (vl-modinst->range x))
       ((mv alist warning-wires) (vl-mark-wires-for-arguments portargs alist))
       (warnings (if (not warning-wires)
                     warnings
                   (cons (make-vl-warning
                          :type :vl-modinst-args-unresolved
                          :msg "In ~a0, arguments are not resolved."
                          :args (list x)
                          :fn 'vl-mark-wires-for-modinst)
                         warnings)))
       ;; We originally thought we would stop there.  But now I have realized
       ;; that parameters are sometimes only used in the paramlist or ranges of
       ;; module instances.  So, now we collect wires from those and mark them
       ;; as used.
       (param-wires (vl-exprlist-names (vl-arguments-allexprs paramargs)))
       (range-wires (vl-exprlist-names (vl-maybe-range-allexprs range)))
       (alist       (vl-mark-wires-used param-wires t alist))
       (alist       (vl-mark-wires-used range-wires t alist)))
      (mv alist warnings warning-wires)))

(defthm vl-wireinfo-alistp-of-vl-mark-wires-for-modinst
  (implies (and (force (vl-modinst-p x))
                (force (vl-wireinfo-alistp alist)))
           (vl-wireinfo-alistp (mv-nth 0 (vl-mark-wires-for-modinst x alist warnings))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-modinst))))

(defthm vl-warninglist-p-of-vl-mark-wires-for-modinst
  (implies (force (vl-warninglist-p warnings))
           (vl-warninglist-p (mv-nth 1 (vl-mark-wires-for-modinst x alist warnings))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-modinst))))

(defthm string-listp-of-vl-mark-wires-for-modinst
  (implies (force (vl-modinst-p x))
           (string-listp (mv-nth 2 (vl-mark-wires-for-modinst x alist warnings))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-modinst))))




(defund vl-mark-wires-for-modinstlist (x alist warnings)
  "Returns (MV ALIST' WARNINGS' WARNING-WIRES)"
  (declare (xargs :guard (and (vl-modinstlist-p x)
                              (vl-wireinfo-alistp alist)
                              (vl-warninglist-p warnings))))
  (if (atom x)
      (mv alist warnings nil)
    (b* (((mv alist warnings warning-wires1)
          (vl-mark-wires-for-modinst (car x) alist warnings))
         ((mv alist warnings warning-wires2)
          (vl-mark-wires-for-modinstlist (cdr x) alist warnings)))
        (mv alist warnings (append warning-wires1 warning-wires2)))))

(defthm vl-wireinfo-alistp-of-vl-mark-wires-for-modinstlist
  (implies (and (force (vl-modinstlist-p x))
                (force (vl-wireinfo-alistp alist)))
           (vl-wireinfo-alistp (mv-nth 0 (vl-mark-wires-for-modinstlist x alist warnings))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-modinstlist))))

(defthm vl-warninglist-p-of-vl-mark-wires-for-modinstlist
  (implies (force (vl-warninglist-p warnings))
           (vl-warninglist-p (mv-nth 1 (vl-mark-wires-for-modinstlist x alist warnings))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-modinstlist))))

(defthm string-listp-of-vl-mark-wires-for-modinstlist
  (implies (force (vl-modinstlist-p x))
           (string-listp (mv-nth 2 (vl-mark-wires-for-modinstlist x alist warnings))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-modinstlist))))




(defund vl-mark-wires-for-gateinst (x alist warnings)
  "Returns (MV ALIST' WARNINGS' WARNING-WIRES)"
  (declare (xargs :guard (and (vl-gateinst-p x)
                              (vl-wireinfo-alistp alist)
                              (vl-warninglist-p warnings))))
  (b* ((args  (vl-gateinst->args x))
       (range (vl-gateinst->range x))
       ((mv alist warning-wires) (vl-mark-wires-for-plainarglist args alist nil))
       (warnings (if (not warning-wires)
                     warnings
                   (cons (make-vl-warning
                          :type :vl-gateinst-args-unresolved
                          :msg "In ~a0, arguments are not resolved."
                          :args (list x)
                          :fn 'vl-mark-wires-for-gateinst)
                         warnings)))
       (range-wires (vl-exprlist-names (vl-maybe-range-allexprs range)))
       (alist       (vl-mark-wires-used range-wires t alist)))
      (mv alist warnings warning-wires)))

(defthm vl-wireinfo-alistp-of-vl-mark-wires-for-gateinst
  (implies (and (force (vl-gateinst-p x))
                (force (vl-wireinfo-alistp alist)))
           (vl-wireinfo-alistp (mv-nth 0 (vl-mark-wires-for-gateinst x alist warnings))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-gateinst))))

(defthm vl-warninglist-p-of-vl-mark-wires-for-gateinst
  (implies (force (vl-warninglist-p warnings))
           (vl-warninglist-p (mv-nth 1 (vl-mark-wires-for-gateinst x alist warnings))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-gateinst))))

(defthm string-listp-of-vl-mark-wires-for-gateinst
  (implies (force (vl-gateinst-p x))
           (string-listp (mv-nth 2 (vl-mark-wires-for-gateinst x alist warnings))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-gateinst))))



(defund vl-mark-wires-for-gateinstlist (x alist warnings)
  "Returns (MV ALIST' WARNINGS' WARNING-WIRES)"
  (declare (xargs :guard (and (vl-gateinstlist-p x)
                              (vl-wireinfo-alistp alist)
                              (vl-warninglist-p warnings))))
  (if (atom x)
      (mv alist warnings nil)
    (b* (((mv alist warnings warning-wires1)
          (vl-mark-wires-for-gateinst (car x) alist warnings))
         ((mv alist warnings warning-wires2)
          (vl-mark-wires-for-gateinstlist (cdr x) alist warnings)))
        (mv alist warnings (append warning-wires1 warning-wires2)))))

(defthm vl-wireinfo-alistp-of-vl-mark-wires-for-gateinstlist
  (implies (and (force (vl-gateinstlist-p x))
                (force (vl-wireinfo-alistp alist)))
           (vl-wireinfo-alistp (mv-nth 0 (vl-mark-wires-for-gateinstlist x alist warnings))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-gateinstlist))))

(defthm vl-warninglist-p-of-vl-mark-wires-for-gateinstlist
  (implies (force (vl-warninglist-p warnings))
           (vl-warninglist-p (mv-nth 1 (vl-mark-wires-for-gateinstlist x alist warnings))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-gateinstlist))))

(defthm string-listp-of-vl-mark-wires-for-gateinstlist
  (implies (force (vl-gateinstlist-p x))
           (string-listp (mv-nth 2 (vl-mark-wires-for-gateinstlist x alist warnings))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-gateinstlist))))


; That's definitely most of the analysis.  Now there are some odd cases that we
; wish to cover.  In particular, the declarations of wires, registers, and so on,
; can include ranges, which may include the names of parameters.  We want to be
; sure to mark those as used.



(defund vl-clean-up-warning-wires (wires alist)
  (declare (xargs :guard (and (string-listp wires)
                              (vl-wireinfo-alistp alist))))

; We are given the list of warning wires that have been generated, and the
; completedly wireinfo alist.  We only want to actually warn about wires which
; were (1) flagged as maybe bad, and (2) currently appear to be unset or
; unused.  The other wires are thrown away.

  (if (atom wires)
      nil
    (let* ((entry        (cdr (hons-get (car wires) alist)))
           (really-warnp (or (not entry)
                             (not (vl-wireinfo->usedp entry))
                             (not (vl-wireinfo->setp entry)))))
      (if really-warnp
          (cons (car wires) (vl-clean-up-warning-wires (cdr wires) alist))
        (vl-clean-up-warning-wires (cdr wires) alist)))))

(defthm string-listp-of-vl-clean-up-warning-wires
  (implies (force (string-listp wires))
           (string-listp (vl-clean-up-warning-wires wires alist)))
  :hints(("Goal" :in-theory (enable vl-clean-up-warning-wires))))




(defund vl-annotate-netdecl-with-wireinfo (x alist wwires)
  (declare (xargs :guard (and (vl-netdecl-p x)
                              (vl-wireinfo-alistp alist)
                              (string-listp wwires))))

; As one way to record our use-set analysis, we can directly extend the
; netdecls in the module with our conclusions.
;
; Given:
;
;   - X is an ordinary net declaration,
;   - ALIST is the wireinfo alist that we have collected for this module
;   - WWIRES is a string list of all the wires we are unsure about.
;
; This function produces a new net declaration, X', which is formed by adding
; as many as two annotations to X.  The possible annotations we add are
;
;     VL_UNUSED       - Appears to be unused, not a warning wire
;     VL_MAYBE_UNUSED - Appears to be unused, but is a warning wire
;
;     VL_UNSET        - Appears to be unset, not a warning wire
;     VL_MAYBE_UNSET  - Appears to be unset, but is a warning wire

  (b* ((name         (vl-netdecl->name x))
       (info         (cdr (hons-get name alist)))

       ((when (not info))
        (prog2$ (er hard? 'vl-annotate-netdecl-with-unused/unset
                    "No wireinfo entry for ~s0." name)
                x))

       (usedp        (vl-wireinfo->usedp info))
       (setp         (vl-wireinfo->setp info))

       ((when (and usedp setp))
        ;; No annotations to make, so just return x unchanged right away.
        x)

       (atts         (vl-netdecl->atts x))
       (warnp        (member-equal name wwires))

       ;; Maybe annotate with unused warning
       (atts         (cond (usedp atts)
                           (warnp (cons (list "VL_MAYBE_UNUSED") atts))
                           (t     (cons (list "VL_UNUSED") atts))))

       ;; Maybe annotate with unset warning
       (atts         (cond (setp  atts)
                           (warnp (cons (list "VL_MAYBE_UNSET") atts))
                           (t     (cons (list "VL_UNSET") atts)))))

      (change-vl-netdecl x :atts atts)))

(defthm vl-netdecl-p-of-vl-annotate-netdecl-with-wireinfo
  (implies (force (vl-netdecl-p x))
           (vl-netdecl-p (vl-annotate-netdecl-with-wireinfo x alist wwires)))
  :hints(("Goal" :in-theory (e/d (vl-annotate-netdecl-with-wireinfo)
                                 ((force))))))


(encapsulate
 ()
 (local (in-theory (disable (force))))
 (defprojection vl-annotate-netdecllist-with-wireinfo (x alist wwires)
   (vl-annotate-netdecl-with-wireinfo x alist wwires)
   :guard (and (vl-netdecllist-p x)
               (vl-wireinfo-alistp alist)
               (string-listp wwires))))

(defthm vl-netdecllist-p-of-vl-annotate-netdecllist-with-wireinfo
  (implies (force (vl-netdecllist-p x))
           (vl-netdecllist-p (vl-annotate-netdecllist-with-wireinfo x alist wwires)))
  :hints(("Goal" :in-theory (e/d (vl-annotate-netdecllist-with-wireinfo)
                                 ((force))))))



(defund vl-mark-wires-for-module (x omit)
  "Returns (X-PRIME REPORT-ENTRY)"
  (declare (xargs :guard (and (vl-module-p x)
                              (string-listp omit))))

; This is our main function that performs the use-set analysis.  We figure out
; which wires appear to be used and unused in the module X.  We annotate the
; netdecls for the module with these attributes, and also generate a more
; concise vl-useset-report-entry object describing the status of this module.

  (b* ((name                (vl-module->name x))
       (portdecls           (vl-module->portdecls x))
       (assigns             (vl-module->assigns x))
       (netdecls            (vl-module->netdecls x))
       (vardecls            (vl-module->vardecls x))
       (regdecls            (vl-module->regdecls x))
       (eventdecls          (vl-module->eventdecls x))
       (paramdecls          (vl-module->paramdecls x))
       (modinsts            (vl-module->modinsts x))
       (gateinsts           (vl-module->gateinsts x))
       (alwayses            (vl-module->alwayses x))
       (initials            (vl-module->initials x))
       (warnings            (vl-module->warnings x))

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


       (declared-wires      (vl-netdecllist->names-exec netdecls nil))
       (declared-wires      (vl-regdecllist->names-exec regdecls declared-wires))

       (params              (vl-paramdecllist->names-exec paramdecls nil))
       ((mv in out inout)   (vl-portdecllist-names-by-direction portdecls nil nil nil))

       (alist               (vl-make-initial-wireinfo-alist (revappend params declared-wires)))

; Special addition: we allow the user to specify that certain wires should be
; omitted from the report.  To accomplish this, just mark these wires as both
; used and set before we continue.

       (alist               (vl-mark-wires-set omit nil alist))
       (alist               (vl-mark-wires-used omit nil alist))

; Basic initialization for inputs, outputs, parameters.  We think of inputs and
; parameters as set, and outputs as used.

       (alist               (vl-mark-wires-set params t alist))
       (alist               (vl-mark-wires-set in t alist))
       (alist               (vl-mark-wires-set inout t alist))
       (alist               (vl-mark-wires-used out t alist))
       (alist               (vl-mark-wires-used inout t alist))

; Additional initialization, mainly to catch the use of parameters in
; declarations.

       (alist               (vl-mark-wires-used (vl-exprlist-names (vl-portdecllist-allexprs portdecls)) t alist))
       (alist               (vl-mark-wires-used (vl-exprlist-names (vl-netdecllist-allexprs netdecls)) t alist))
       (alist               (vl-mark-wires-used (vl-exprlist-names (vl-vardecllist-allexprs vardecls)) t alist))
       (alist               (vl-mark-wires-used (vl-exprlist-names (vl-regdecllist-allexprs regdecls)) t alist))
       (alist               (vl-mark-wires-used (vl-exprlist-names (vl-eventdecllist-allexprs eventdecls)) t alist))
       (alist               (vl-mark-wires-used (vl-exprlist-names (vl-paramdecllist-allexprs paramdecls)) t alist))

; Now we're on to the core of our analysis.  We sweep through the assignments,
; module instances, and gate instances and mark that every wire is either used
; or set when it is encountered.  If we do not know the direction of a port, we
; may issue warnings about particular wires.  So, in addition to updating the
; alist, we generate lists of warnings and a list of wires that we are not sure
; about.

       (warnings
        (if (and (atom alwayses)
                 (atom initials))
            warnings
          (cons (make-vl-warning
                 :type :vl-useset-statements-ignored
                 :msg "Use-Set note: always and initial statements are currently ~
                       ignored in our wire analysis, so use-set results may be ~
                       incorrect."
                 :fn 'vl-mark-wires-for-module)
                warnings)))
       (alist
        (vl-mark-wires-for-assignlist assigns alist))
       ((mv alist warnings warning-wires1)
        (vl-mark-wires-for-modinstlist modinsts alist warnings))
       ((mv alist warnings warning-wires2)
        (vl-mark-wires-for-gateinstlist gateinsts alist warnings))

; We now clean up the warning wires.  What is this about?  Well, initially
; every wire is marked as unused and unset.  When we encounter a port and
; aren't sure about its direction, we don't update the alist but we note that
; every wire used in the port is suspicious.  If, later, it turns out that we
; actually used and set that wire, then we don't really need to think of it as
; suspicious anymore, so we throw it away.

       (warning-wires       (vl-clean-up-warning-wires
                             (mergesort (append warning-wires1 warning-wires2))
                             alist))

; Now gather up the info out of the alist, make the new list of netdecls, and
; update the module.

       (-                   (flush-hons-get-hash-table-link alist))
       (alist               (hons-shrink-alist alist nil))
       ((mv unused unset)   (vl-collect-unused-or-unset-wires alist nil nil))
       (unused              (mergesort unused))
       (unset               (mergesort unset))

       (new-netdecls        (if (or unused unset)
                                (vl-annotate-netdecllist-with-wireinfo netdecls alist warning-wires)
                              netdecls))
       (x-prime             (change-vl-module x
                                              :netdecls new-netdecls
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



       (report-entry        (make-vl-useset-report-entry :name name
                                                         :spurious spurious
                                                         :unused unused
                                                         :unset unset
                                                         :wwires warning-wires
                                                         :warnings warnings
                                                         :typos typos
                                                         ;:mismatches mismatches
                                                         ;:lvalue-inputs lvalue-inputs
                                                         ))
       (-                   (flush-hons-get-hash-table-link alist)))

      (mv x-prime report-entry)))

(defthm vl-module-p-of-vl-mark-wires-for-module
  (implies (vl-module-p x)
           (vl-module-p (mv-nth 0 (vl-mark-wires-for-module x omit))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-module))))

(defthm vl-useset-report-entry-p-of-vl-mark-wires-for-module
  (implies (and (vl-module-p x)
                (string-listp omit))
           (vl-useset-report-entry-p (mv-nth 1 (vl-mark-wires-for-module x omit))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-module))))

(defthm vl-module->name-of-vl-mark-wires-for-module
  (equal (vl-module->name (mv-nth 0 (vl-mark-wires-for-module x omit)))
         (vl-module->name x))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-module))))



(defund vl-mark-wires-for-modulelist (x omit)
  "Returns (MV X-PRIME REPORT)"
  (declare (xargs :guard (and (vl-modulelist-p x)
                              (string-listp omit))))

; We carry out the use-set analysis on all modules, and return the updated
; modules (where perhaps some wires are annotated with VL_UNUSED, etc.) and the
; report for all modules.

  (if (atom x)
      (mv nil nil)
    (b* (((mv car-prime car-entry) (vl-mark-wires-for-module (car x) omit))
         ((mv cdr-prime cdr-report) (vl-mark-wires-for-modulelist (cdr x) omit)))
        (mv (cons car-prime cdr-prime)
            (cons car-entry cdr-report)))))

(defthm vl-modulelist-p-of-vl-mark-wires-for-modulelist
  (implies (vl-modulelist-p x)
           (vl-modulelist-p (mv-nth 0 (vl-mark-wires-for-modulelist x omit))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-modulelist))))

(defthm vl-useset-report-p-of-vl-mark-wires-for-modulelist
  (implies (and (vl-modulelist-p x)
                (string-listp omit))
           (vl-useset-report-p (mv-nth 1 (vl-mark-wires-for-modulelist x omit))))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-modulelist))))

(defthm vl-modulelist->names-of-vl-mark-wires-for-modulelist
  (equal (vl-modulelist->names (mv-nth 0 (vl-mark-wires-for-modulelist x omit)))
         (vl-modulelist->names x))
  :hints(("Goal" :in-theory (enable vl-mark-wires-for-modulelist))))

