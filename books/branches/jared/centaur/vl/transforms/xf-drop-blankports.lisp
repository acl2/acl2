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
(include-book "../mlib/find-module")
(local (include-book "../util/arithmetic"))

(defxdoc drop-blankports
  :parents (transforms)
  :short "Eliminate \"blank ports\" from modules and delete all corresponding
arguments from module instances."

  :long "<p>For background on blank ports and argument see @(see vl-port-p) and
@(see vl-plainarg-p).</p>

<p>Blank ports are completely useless.  This transform removes blank ports from
all modules and simultaneously removes all arguments given to blank ports from
all instances of all modules.</p>

<p>Prerequisites.  We expect to only see plain argument lists, i.e., @(see
argresolve) should have already been run.  There are no other requirements.
However, note that we do not respect @(see vl-module->hands-offp) since it does
not seem legitimate to do so: the correctness of this transformation requires
that the instances throughout every module be updated.</p>

<p>We may add fatal warnings if we find instances of undefined modules or arity
mismatches.  But we do <i>not</i> add any warnings about connections to blank
ports because we expect @(see argresolve) to have done that.</p>")

(local (xdoc::set-default-parents drop-blankports))

(define vl-plainarglist-drop-blankports
  :short "Drop arguments to blank ports from an plain argument list."
  ((args  "arguments to some module instance"      vl-plainarglist-p)
   (ports "corresponding ports from the submodule" vl-portlist-p))
  :guard (same-lengthp args ports)
  :returns (new-args "copy of @('args') with blank ports removed"
                     vl-plainarglist-p :hyp :fguard)
  (cond ((atom args)
         nil)
        ((vl-port->expr (car ports))
         (cons (car args)
               (vl-plainarglist-drop-blankports (cdr args) (cdr ports))))
        (t
         (vl-plainarglist-drop-blankports (cdr args) (cdr ports)))))

(define vl-modinst-drop-blankports
  :short "Drop arguments to blank ports from a module instance."
  ((x        "module instance to rewrite" vl-modinst-p)
   (mods     "list of all modules" vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods)))
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-modinst-p     :hyp :fguard))
  (b* (((vl-modinst x) x)

       (target-mod (vl-fast-find-module x.modname mods modalist))
       ((unless target-mod)
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0 refers to undefined module ~m1."
                   :args (list x x.modname))
            x))
       ((unless (eq (vl-arguments-kind x.portargs) :plain))
        (mv (fatal :type :vl-programming-error
                   :msg "~a0: expected all modules to be using plain ~
                         arguments, but found named arguments.  Did you ~
                         forget to run the argresolve transform first?"
                   :args (list x))
            x))

       (ports         (vl-module->ports target-mod))
       (plainargs     (vl-arguments-plain->args x.portargs))
       ((unless (same-lengthp plainargs ports))
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: bad arity.  Expected ~x1 arguments but found ~
                         ~x2 arguments."
                   :args (list x (len ports) (len plainargs)))
            x))
       (new-plainargs (vl-plainarglist-drop-blankports plainargs ports))
       (new-arguments (make-vl-arguments-plain :args new-plainargs))
       (new-x         (change-vl-modinst x :portargs new-arguments)))
    (mv (ok) new-x)))

(define vl-modinstlist-drop-blankports
  :short "Drop arguments to blank ports from module instances."
  ((x        "modinsts to rewrite" vl-modinstlist-p)
   (mods     "list of all modules" vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods)))
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-modinstlist-p :hyp :fguard))
  (b* (((when (atom x))
        (mv (ok) nil))
       ((mv warnings car)
        (vl-modinst-drop-blankports (car x) mods modalist warnings))
       ((mv warnings cdr)
        (vl-modinstlist-drop-blankports (cdr x) mods modalist warnings)))
    (mv warnings (cons car cdr))))

(define vl-portlist-drop-blankports
  :short "Drop any blank ports from a list of ports."
  ((x vl-portlist-p))
  :returns (new-x vl-portlist-p :hyp :fguard)
  (cond ((atom x)
         nil)
        ((vl-port->expr (car x))
         (cons (car x) (vl-portlist-drop-blankports (cdr x))))
        (t
         (vl-portlist-drop-blankports (cdr x)))))

(define vl-module-drop-blankports
  :short "Drop any blank ports from a module, and simultaneously remove all
arguments to blank ports from all module instances within the module."
  ((x    "module to rewrite"   vl-module-p)
   (mods "list of all modules" vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((vl-module x) x)
       (ports (vl-portlist-drop-blankports x.ports))
       ((mv warnings modinsts)
        (vl-modinstlist-drop-blankports x.modinsts mods modalist x.warnings)))
    (change-vl-module x
                      :ports ports
                      :modinsts modinsts
                      :warnings warnings)))

(defprojection vl-modulelist-drop-blankports-aux (x mods modalist)
  (vl-module-drop-blankports x mods modalist)
  :guard (and (vl-modulelist-p x)
              (vl-modulelist-p mods)
              (equal modalist (vl-modalist mods)))
  :result-type vl-modulelist-p)

(define vl-modulelist-drop-blankports
  ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p :hyp :fguard)
  (b* ((modalist (vl-modalist x))
       (new-x    (vl-modulelist-drop-blankports-aux x x modalist)))
    (fast-alist-free modalist)
    new-x))

(define vl-design-drop-blankports
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-drop-blankports x.mods))))

