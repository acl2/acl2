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
(include-book "../mlib/scopestack")
(include-book "../mlib/port-tools")
(include-book "../mlib/strip")
(include-book "../mlib/fmt")
(local (include-book "../util/arithmetic"))

(defxdoc dupeinst-check
  :parents (vl-lint)
  :short "Check for module instances that are driving wires in identical ways."

  :long "<p>This is a trivially simple check for cases like:</p>

@({
   mymod m1 (o1, a, b);
   mymod m2 (o2, a, b);
})

<p>That is, instances of the same module with the same inputs but perhaps with
different outputs.  The @(see duperhs-check) is similar but looks for
assignments whose right-hand sides are the same.</p>

<p>Sometimes this sort of thing is necessary and expected, e.g., you might have
a particular signal that needs to be distributed widely and hence is being
given to multiple inverters.</p>

<p>But in other cases this kind of redundancy can be some legacy stuff that you
want to identify and eliminate.  For instance, it's especially useful to
eliminate redundant registers, to improve power usage.</p>")

(local (xdoc::set-default-parents dupeinst-check))

(defconst *dupeinst-check-debug* nil)

(defaggregate vl-dupeinst-key
  :short "Keys used to determine if module instances have the same inputs."

  ((modname stringp :rule-classes :type-prescription
            "Name of the submodule being instantiated.  We need to know the
             name of each instance so that we don't get confused by things
             like

             @({
                 mymod1 m1 (o1, a, b);
                 mymod2 m2 (o2, a, b);
             })

             which, despite having the same arguments, are presumably very
             different things.")

   (inputs  vl-exprlist-p
            "Inputs (not outputs or inouts) to the submodule instance.  We
             expect instances to be argresolved so that these are already in
             some canonical order.  We just keep the expressions because we
             don't care about port names, directions, etc.  We also expect all
             of these expressions to be fixed so that attributes are
             ignored."))

  :long "<p>We generate a key from each modinst.  Modinsts with the same keys
are regarded as having the same inputs.  That is, the whole point of the
dupeinst check is to find modinsts with the same key.</p>

<p>Our keys should arguably include the parameter arguments.  But if the inputs
are the same, then the parameters should probably be the same or, at any rate,
seem basically compatible?  Well, whatever.  It probably doesn't matter much at
all in practice.</p>

<p>We always hons keys because we're going to use them as fast alist keys.</p>"

  :tag :vl-dupeinst-key
  :hons t)

(defalist vl-dupeinst-alistp (x)
  :key (vl-dupeinst-key-p x)
  :val (vl-modinstlist-p x)
  :keyp-of-nil nil
  :valp-of-nil t
  :long "<p>The basic idea is to bind keys to the lists of modinsts that have
that key, which lets us immediately see which modinsts have the same key.</p>
@(def vl-dupeinst-alistp)")

(define vl-pp-dupeinst-key ((x vl-dupeinst-key-p) &key (ps 'ps))
  (b* (((vl-dupeinst-key x)))
    (vl-ps-seq (vl-print-str x.modname)
               (vl-print "{")
               (vl-pp-exprlist x.inputs)
               (vl-println "}"))))

(define vl-pp-dupeinst-alist ((x vl-dupeinst-alistp) &key (ps 'ps))
  (b* (((when (atom x))
        ps)
       ((cons key insts) (car x)))
    (vl-ps-seq (vl-print "** ")
               (vl-pp-dupeinst-key key)
               (vl-pp-modinstlist insts nil)
               (vl-pp-dupeinst-alist (cdr x)))))

(define vl-make-dupeinst-alist-aux
  ((x     vl-modinstlist-p)
   (alist vl-dupeinst-alistp))
  :returns (new-alist vl-dupeinst-alistp :hyp :fguard)
  :parents (vl-make-dupeinst-alist)
  (b* (((when (atom x))
        alist)
       (x1 (car x))
       ((vl-modinst x1) x1)

       ((when (eq (vl-arguments-kind x1.portargs) :vl-arguments-named))
        (and *dupeinst-check-debug*
             (vl-cw-ps-seq (vl-cw "~a0: Arguments not resolved, skipping!~%" x1)))
        (vl-make-dupeinst-alist-aux (cdr x) alist))

       ((mv inputs ?outputs inouts unknowns)
        (vl-partition-plainargs (vl-arguments-plain->args x1.portargs) nil nil nil nil))

       ((unless (and (atom inouts)
                     (atom unknowns)))
        (and *dupeinst-check-debug*
             (vl-cw-ps-seq (vl-cw "~a0: Arguments too hard (inouts or unknowns).~%" x1)))
        (vl-make-dupeinst-alist-aux (cdr x) alist))

       (ins    (vl-plainarglist->exprs inputs))
       ((when (member nil ins))
        (and *dupeinst-check-debug*
             (vl-cw-ps-seq (vl-cw "~a0: Blanks in argument list.~%" x1)))
        (vl-make-dupeinst-alist-aux (cdr x) alist))
       (ins    (vl-exprlist-strip ins))
       (key    (make-vl-dupeinst-key :modname x1.modname :inputs ins))
       (look   (hons-get key alist))
       (alist  (hons-acons key (cons x1 (cdr look)) alist)))
    (vl-make-dupeinst-alist-aux (cdr x) alist)))

(define vl-make-dupeinst-alist ((x vl-modinstlist-p))
  :returns (alist vl-dupeinst-alistp :hyp :fguard)
  :short "Builds a (slow) @(see vl-dupeinst-alistp) for a list of assignments."

  (b* ((alist (len x))
       (alist (vl-make-dupeinst-alist-aux x alist))
       (ans   (hons-shrink-alist alist nil)))
    (fast-alist-free alist)
    (fast-alist-free ans)
    ans))


(defsection vl-dupeinst-trivial-p
  :short "Customizable filter for duplicate module instances."

  :long "<p>By default, all duplicated modules are considered worth warning
about.  But you can configure which modules are considered trivial/okay to
duplicate by attaching a function to @('vl-dupeinst-trivial-p').  These will be
filtered out into minor warnings.</p>

@(def vl-dupeinst-trivial-p)"

  (encapsulate
    (((vl-dupeinst-trivial-p *) => *
      :formals (modname)
      :guard (stringp modname)))

    (local (defun vl-dupeinst-trivial-p (modname)
             (declare (xargs :guard (stringp modname))
                      (ignore modname))
             nil)))

  (defund vl-dupeinst-trivial-p-default (modname)
    (declare (xargs :guard (stringp modname))
             (ignore modname))
    nil)

  (defattach vl-dupeinst-trivial-p vl-dupeinst-trivial-p-default))



(define vl-modinstlist-fixed-up-outs ((x vl-modinstlist-p))
  :parents (vl-maybe-warn-dupeinst)
  :short "Extract the @(see vl-expr-strip)ed outputs from each module instance."
  (b* (((when (atom x))
        nil)
       ((vl-modinst x1) (car x))
       ((when (eq (vl-arguments-kind x1.portargs) :vl-arguments-named))
        (raise "expected resolved args"))
       ((mv ?inputs outputs ?inouts ?unknowns)
        (vl-partition-plainargs (vl-arguments->args x1.portargs) nil nil nil nil))
       (outexprs (vl-plainarglist->exprs outputs))
       (fixed-outexprs (if (member nil outexprs)
                           ;; Can't fix them up because there are blanks.
                           ;; Well, who cares.  We'll just leave them unfixed.
                           outexprs
                         (vl-exprlist-strip outexprs))))
    (cons fixed-outexprs
          (vl-modinstlist-fixed-up-outs (cdr x)))))

(define vl-maybe-warn-dupeinst
  ((key      vl-dupeinst-key-p "The shared key for a group of modinsts.")
   (modinsts vl-modinstlist-p  "The modinsts that share this key.")
   (ss       vl-scopestack-p   "Scopestack for doing module lookups.")
   (warnings vl-warninglist-p  "The @(see warnings) accumulator to extend."))
  :returns (new-warnings vl-warninglist-p)
  :short "Possibly add warnings about a group of module instances."
  :long "<p>Modinsts might not have multiple entries, in which case there is
nothing to do and we just return @('warnings') unchanged.  Otherwise, we issue
a warning about the modules.</p>"

  (b* (((when (or (atom modinsts)
                  (atom (cdr modinsts))))
        ;; Nothing to do -- there isn't more than one assignment for this RHS.
        (ok))

       (mod (vl-scopestack-find-definition (vl-dupeinst-key->modname key) ss))
       ((when (eq (tag mod) :vl-interface))
        ;; Don't want to warn about interfaces.
        (and *dupeinst-check-debug*
             (vl-cw-ps-seq (vl-cw "Skipping ~s0 because it's an interface:~%")
                           (vl-pp-dupeinst-key key)
                           (vl-cw "~%")))
        (ok))
       ((when (and (eq (tag mod) :vl-module)
                   (atom (vl-module->ports mod))))
        ;; Don't want to warn about modules with no ports.
        (and *dupeinst-check-debug*
             (vl-cw-ps-seq (vl-cw "Skipping ~s0 because it has no ports.~%")
                           (vl-pp-dupeinst-key key)
                           (vl-cw "~%")))
        (ok))

       (fixed-up-outs (vl-modinstlist-fixed-up-outs modinsts))
       (dupes         (duplicated-members fixed-up-outs))

       (modname (vl-dupeinst-key->modname key))
       (minor-p (vl-dupeinst-trivial-p modname)))
    (warn :type (if (consp dupes)
                    (if minor-p :vl-warn-same-ports-minor :vl-warn-same-ports)
                  (if minor-p :vl-warn-same-inputs-minor :vl-warn-same-inputs))
          :msg "Found instances of the same module with ~s0:~%~%~s1"
          :args (list (if (consp dupes)
                          "the same arguments"
                        "the same inputs (but different outputs)")
                      (str::prefix-lines (with-local-ps
                                          ;; may help avoid unnecessary line wrapping
                                          (vl-ps-update-autowrap-col 200)
                                          (vl-pp-modinstlist modinsts nil))
                                         "     ")
                      ;; These aren't printed, but we include them in the
                      ;; warning so our suppression mechanism can be
                      ;; applied.
                      modinsts))))

(define vl-warnings-for-dupeinst-alist ((alist    vl-dupeinst-alistp)
                                        (ss       vl-scopestack-p)
                                        (warnings vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* (((when (atom alist))
        (ok))
       (rhs      (caar alist))
       (assigns  (cdar alist))
       (warnings (vl-maybe-warn-dupeinst rhs assigns ss warnings)))
    (vl-warnings-for-dupeinst-alist (cdr alist) ss warnings)))

(define vl-module-dupeinst-check ((x  vl-module-p)
                                  (ss vl-scopestack-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) x)
       (- (and *dupeinst-check-debug*
               (cw "Dupeinst checking ~s0~%" x.name)))
       (ss       (vl-scopestack-push x ss))

; BOZO.  We should do something to also consider instances within generates,
; but doing so leads to false positives because we find things like
;
;  if (mode == 1)
;  begin
;    submod foo (o, a, b);
;    ...
;  else
;  begin
;    submod foo (o, a, b);
;    ...
;  end
;
; Anyway, this is annoying, so, at least for now, we just won't check
; generates.

       ;; if you try to bring this back note that i changed flatten-modinsts
       ;; to also return instances from binds!
       ;; (modinsts (vl-module->flatten-modinsts x))
       (modinsts (vl-module->modinsts x))
       (alist    (vl-make-dupeinst-alist modinsts))
       (warnings (vl-warnings-for-dupeinst-alist alist ss x.warnings)))
    (change-vl-module x :warnings warnings)))

(defprojection vl-modulelist-dupeinst-check ((x  vl-modulelist-p)
                                             (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-dupeinst-check x ss))

(define vl-design-dupeinst-check ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) (vl-design-fix x))
       (ss       (vl-scopestack-init x))
       (new-mods (vl-modulelist-dupeinst-check x.mods ss)))
    (vl-scopestacks-free)
    (clear-memoize-table 'vl-expr-strip)
    (change-vl-design x :mods new-mods)))
