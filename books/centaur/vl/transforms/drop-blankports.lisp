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
                     vl-plainarglist-p)
  (b* (((when (atom args))
        nil)
       (port1 (vl-port-fix (car ports)))
       ((when (or (eq (tag port1) :vl-interfaceport)
                  (vl-regularport->expr port1)))
        (cons (vl-plainarg-fix (car args))
              (vl-plainarglist-drop-blankports (cdr args) (cdr ports)))))
    (vl-plainarglist-drop-blankports (cdr args) (cdr ports))))

(define vl-modinst-drop-blankports
  :short "Drop arguments to blank ports from a module instance."
  ((x        "module instance to rewrite" vl-modinst-p)
   (ss       vl-scopestack-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-modinst-p    ))
  (b* ((x (vl-modinst-fix x))
       ((vl-modinst x) x)
       (target-mod (vl-scopestack-find-definition x.modname ss))
       ((unless (and target-mod (eq (tag target-mod) :vl-module)))
        (mv (fatal :type :vl-unresolved-instance
                   :msg "~a0 refers to undefined module ~m1."
                   :args (list x x.modname))
            x))
       ((unless (eq (vl-arguments-kind x.portargs) :vl-arguments-plain))
        (mv (fatal :type :vl-programming-error
                   :msg "~a0: expected all modules to be using plain ~
                         arguments, but found named arguments.  Did you ~
                         forget to run the argresolve transform first?"
                   :args (list x))
            x))

       (ports         (vl-module->ports target-mod))
       (plainargs     (vl-arguments-plain->args x.portargs))
       ((unless (same-lengthp plainargs ports))
        ;; note: same warning is in argresolve.lisp
        (b* ((nports   (len ports))
             (nargs    (len plainargs)))
          (mv (fatal :type :vl-instance-wrong-arity
                     ;; Wow this is hideous
                     :msg "~a0 ~s1 ~x2 ~s3, but module ~m4 ~s5 ~x6 ~s7."
                     :args (list x
                                 (if (< nargs nports) "only has" "has")
                                 nargs
                                 (if (= nargs 1) "argument" "arguments")
                                 x.modname
                                 (if (< nargs nports) "has" "only has")
                                 nports
                                 (if (= nports 1) "port" "ports")))
              x)))
       (new-plainargs (vl-plainarglist-drop-blankports plainargs ports))
       (new-arguments (make-vl-arguments-plain :args new-plainargs))
       (new-x         (change-vl-modinst x :portargs new-arguments)))
    (mv (ok) new-x)))

(define vl-modinstlist-drop-blankports
  :short "Drop arguments to blank ports from module instances."
  ((x        "modinsts to rewrite" vl-modinstlist-p)
   (ss       vl-scopestack-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-modinstlist-p))
  (b* (((when (atom x))
        (mv (ok) nil))
       ((mv warnings car)
        (vl-modinst-drop-blankports (car x) ss warnings))
       ((mv warnings cdr)
        (vl-modinstlist-drop-blankports (cdr x) ss warnings)))
    (mv warnings (cons car cdr))))

(define vl-portlist-drop-blankports
  :short "Drop any blank ports from a list of ports."
  ((x vl-portlist-p))
  :returns (new-x vl-portlist-p)
  (b* (((when (atom x)) nil)
       (x1 (vl-port-fix (car x)))
       ((when (or (eq (tag x1) :vl-interfaceport)
                  (vl-regularport->expr (car x))))
        (cons (vl-port-fix (car x))
              (vl-portlist-drop-blankports (cdr x)))))
    (vl-portlist-drop-blankports (cdr x))))

(define vl-module-drop-blankports
  :short "Drop any blank ports from a module, and simultaneously remove all
arguments to blank ports from all module instances within the module."
  ((x    "module to rewrite"   vl-module-p)
   (ss       vl-scopestack-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) x)
       (ss (vl-scopestack-push (vl-module-fix x) ss))
       (ports (vl-portlist-drop-blankports x.ports))
       ((mv warnings modinsts)
        (vl-modinstlist-drop-blankports x.modinsts ss x.warnings)))
    (change-vl-module x
                      :ports ports
                      :modinsts modinsts
                      :warnings warnings)))

(defprojection vl-modulelist-drop-blankports ((x vl-modulelist-p)
                                                  (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-drop-blankports x ss))

(define vl-design-drop-blankports
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x)
       (ss (vl-scopestack-init x))
       (mods (vl-modulelist-drop-blankports x.mods ss)))
    (vl-scopestacks-free)
    (change-vl-design x :mods mods)))

