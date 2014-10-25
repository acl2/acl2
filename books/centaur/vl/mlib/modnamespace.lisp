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
(include-book "scopestack")
(include-book "stmt-tools")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc modnamespace
  :parents (mlib)
  :short "Functions related to a module's namespace."

  :long "<p>Namespaces are discussed in Section 4.11 of the Verilog-2005
standard.  In particular, note that ports and port declarations are given
special treatment: they are said to be in a separate namespace which
\"overlaps\" the regular module namespace.</p>

<p>I think this distinction is only made so that you can refer to both ports and
 to items in the regular module namespace from expressions, etc.  The
 important consequence of this is that it is legal to write things such as:</p>

@({
     input x ;
     wire x ;
})

<p>Even though it would be illegal to declare x to be a wire twice, or as both a
wire and a reg, and so on.</p>

<p>At any rate, in this file we introduce a number of routines for extracting
the names from lists of port declarations, net declarations, and so on.  These
culminate in</p>

@({
    (VL-MODULE->MODNAMESPACE X) : MODULE -> STRING LIST
})

<p>Which returns a list of all names found the module's namespace.  Note that
any reasonable module is required to have a unique modnamespace.</p>

<p>BOZO this does not get named blocks.  Unclear how nested blocks are supposed
to be handled.  We do at least get function and task names, and names from
events.</p>")

(local (xdoc::set-default-parents modnamespace))

(defprojection vl-namedarglist->names ((x vl-namedarglist-p))
  ;; BOZO this function is somewhat misplaced, it doesn't really have anything
  ;; to do with the modnamespace.
  :parents (vl-namedarglist-p)
  :short "Collect all names from a @(see vl-namedarglist-p)."
  :returns (names string-listp)
  (vl-namedarg->name x))

(defprojection vl-modinstlist->modnames ((x vl-modinstlist-p))
  ;; BOZO also somewhat misplaced -- doesn't have to do with the namespace.
  :parents (vl-modinstlist-p)
  :short "Collect all module names (not instance names!) from a
          @(see vl-modinstlist-p)."
  :returns (modnames string-listp)
  (vl-modinst->modname x))

(defprojection vl-paramdecllist->names ((x vl-paramdecllist-p))
  :parents (vl-paramdecllist-p modnamespace)
  :short "Collect all names declared in a @(see vl-paramdecllist-p)."
  :returns (names string-listp)
  (vl-paramdecl->name x))

(defprojection vl-portdecllist->names ((x vl-portdecllist-p))
  :parents (vl-portdecllist-p modnamespace)
  :short "Collect all names declared in a @(see vl-portdecllist-p)."
  :returns (names string-listp)
  (vl-portdecl->name x))

(defprojection vl-vardecllist->names ((x vl-vardecllist-p))
  :parents (vl-vardecllist-p modnamespace)
  :short "Collect all names declared in a @(see vl-vardecllist-p)."
  :returns (names string-listp)
  (vl-vardecl->name x))








(define vl-module->modnamespace-nrev ((x vl-module-p) nrev)
  :parents (vl-module->modnamespace)
  :short "Tail-recursive implementation of @(see vl-module->modnamespace)."
  :long "<p>This is sort of an inherently inefficient operation, since we are
to perform a cons for every object in the module.  But we can at least do
everything tail recursively, etc.</p>"
  (b* (((vl-module x) x)
       (nrev (vl-vardecllist->names-nrev     x.vardecls   nrev))
       (nrev (vl-paramdecllist->names-nrev   x.paramdecls nrev))
       (nrev (vl-fundecllist->names-nrev     x.fundecls   nrev))
       (nrev (vl-taskdecllist->names-nrev    x.taskdecls  nrev))
       (nrev (vl-modinstlist->instnames-nrev x.modinsts   nrev))
       (nrev (vl-gateinstlist->names-nrev    x.gateinsts  nrev)))
    nrev))

(define vl-module->modnamespace ((x vl-module-p))
  :returns (names string-listp)
  :parents (modnamespace)
  :short "Main function for gathering up the names that are declared as
parameters, wires, variables, registers, and so on."

  :long "<p>Note: this function <b>does not</b> include the names of ports,
because as noted above they are considered to be in their own namespace which
is \"separate but overlapping\" the main namespace in the module; see @(see
modnamespace) for details.</p>

<p>If this function returns a list that is not duplicate-free, it means the
module illegally declares those duplicated names more than once.</p>

<p>To reduce memory usage, we optimize this function using @('nreverse').</p>"
  :verify-guards nil
  (mbe :logic
       (b* (((vl-module x) x))
         (append (vl-vardecllist->names     x.vardecls)
                 (vl-paramdecllist->names   x.paramdecls)
                 (vl-fundecllist->names     x.fundecls)
                 (vl-taskdecllist->names    x.taskdecls)
                 (vl-modinstlist->instnames x.modinsts)
                 (vl-gateinstlist->names    x.gateinsts)))
       :exec
       (with-local-nrev
         (vl-module->modnamespace-nrev x nrev)))

  ///
  (defthm vl-module->modnamespace-nrev-removal
    (equal (vl-module->modnamespace-nrev x nrev)
           (append nrev (vl-module->modnamespace x)))
    :hints(("Goal" :in-theory (enable vl-module->modnamespace-nrev))))

  (verify-guards vl-module->modnamespace)

  (defthm true-listp-of-vl-module->modnamespace
    (true-listp (vl-module->modnamespace x))
    :rule-classes :type-prescription))

