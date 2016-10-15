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
(include-book "find")
(include-book "stmt-tools")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc modnamespace
  :parents (mlib)
  :short "Functions related to a module's namespace."

  :long "<p>BOZO this is generally obviated by @(see scopestack).  New code
shouldn't be written using modnamespace.</p>

<p>Namespaces are discussed in Section 4.11 of the Verilog-2005
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

<p>Which returns a list of all names found in the module's namespace.  Note
that any reasonable module is required to have a unique modnamespace.</p>

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








(define vl-find-moduleitem
  :short "Legacy -- Use @(see scopestack) instead.  A (naive) lookup operation
  that can find any name in the module's namespace."

  :long "<p>This is our main, naive spec for what it means to look up a name in
a module's namespace.  Note that we don't look for port declarations!  (But
typically this <i>will</i> find the corresponding net/reg declaration for a
port.)</p>

<p>Typically you will want to use @(see vl-fast-find-moduleitem) when looking
up multiple items.</p>"

  ((name stringp)
   (x    vl-module-p))

  :returns item?

  (b* (((vl-module x) x)
       (name (string-fix name)))
    (or (vl-find-vardecl   name x.vardecls)
        (vl-find-paramdecl name x.paramdecls)
        (vl-find-fundecl   name x.fundecls)
        (vl-find-taskdecl  name x.taskdecls)
        (vl-find-modinst   name x.modinsts)
        (vl-find-gateinst  name x.gateinsts)))

  ///
  (defthm vl-find-moduleitem-type-when-nothing-else
    (implies (and (vl-find-moduleitem name x)
                  (not (vl-vardecl-p   (vl-find-moduleitem name x)))
                  (not (vl-paramdecl-p (vl-find-moduleitem name x)))
                  (not (vl-fundecl-p   (vl-find-moduleitem name x)))
                  (not (vl-taskdecl-p  (vl-find-moduleitem name x)))
                  (not (vl-modinst-p   (vl-find-moduleitem name x))))
             (vl-gateinst-p (vl-find-moduleitem name x)))
    :hints(("Goal" :in-theory (enable vl-find-moduleitem)))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm type-of-vl-find-moduleitem
    ;; This is gross, but I'm not sure of a better approach.
    (and (equal (equal (tag (vl-find-moduleitem name x)) :vl-vardecl)
                (vl-vardecl-p (vl-find-moduleitem name x)))

         (equal (equal (tag (vl-find-moduleitem name x)) :vl-paramdecl)
                (vl-paramdecl-p (vl-find-moduleitem name x)))

         (equal (equal (tag (vl-find-moduleitem name x)) :vl-fundecl)
                (vl-fundecl-p (vl-find-moduleitem name x)))

         (equal (equal (tag (vl-find-moduleitem name x)) :vl-taskdecl)
                (vl-taskdecl-p (vl-find-moduleitem name x)))

         (equal (equal (tag (vl-find-moduleitem name x)) :vl-modinst)
                (vl-modinst-p (vl-find-moduleitem name x)))

         (equal (equal (tag (vl-find-moduleitem name x)) :vl-gateinst)
                (vl-gateinst-p (vl-find-moduleitem name x))))
    :hints(("Goal"
            :in-theory (e/d (tag-reasoning)
                            (vl-find-moduleitem
                             vl-find-moduleitem-type-when-nothing-else))
            :use ((:instance vl-find-moduleitem-type-when-nothing-else)))))

  (defthm consp-of-vl-find-moduleitem
    (equal (consp (vl-find-moduleitem name x))
           (if (vl-find-moduleitem name x)
               t
             nil))
    :hints(("Goal"
            :in-theory (disable vl-find-moduleitem-type-when-nothing-else
                                vl-find-moduleitem)
            :use ((:instance vl-find-moduleitem-type-when-nothing-else)))))

  (defthm vl-find-moduleitem-when-in-namespace
    (implies (member-equal name (vl-module->modnamespace x))
             (vl-find-moduleitem name x))
    :hints(("Goal" :in-theory (enable vl-module->modnamespace vl-find-moduleitem)))))




; FAST-ALIST BASED LOOKUPS ----------------------------------------------------

(deftranssum vl-moditem
  :short "Legacy -- Use @(see scopestack) instead.  Module items are basically
any named object that can occur within a module (except that we don't support,
e.g., named blocks.)"
  (vl-vardecl
   vl-paramdecl
   vl-fundecl
   vl-taskdecl
   vl-modinst
   vl-gateinst))

(fty::deflist vl-moditemlist
  :elt-type vl-moditem-p
  :elementp-of-nil nil)

(fty::defalist vl-moditem-alist
  :key-type stringp
  :val-type vl-moditem-p
  :keyp-of-nil nil
  :valp-of-nil nil)

(local (defthm l0
         (implies (vl-moditem-alist-p acc)
                  (and (vl-moditem-alist-p (vl-vardecllist-alist x acc))
                       (vl-moditem-alist-p (vl-paramdecllist-alist x acc))
                       (vl-moditem-alist-p (vl-fundecllist-alist x acc))
                       (vl-moditem-alist-p (vl-taskdecllist-alist x acc))
                       (vl-moditem-alist-p (vl-modinstlist-alist x acc))
                       (vl-moditem-alist-p (vl-gateinstlist-alist x acc))))
         :hints(("Goal" :in-theory (enable vl-vardecllist-alist
                                           vl-paramdecllist-alist
                                           vl-fundecllist-alist
                                           vl-taskdecllist-alist
                                           vl-modinstlist-alist
                                           vl-gateinstlist-alist)))))

(define vl-make-moditem-alist ((x vl-module-p))
  :short "Legacy -- Use @(see scopestack) instead.  Main routine for building an
  fast alist for looking up module items."

  :long "<p>Note that the order the alist is constructed in is particularly
important: we want it to agree, completely, with the naive @(see
vl-find-moduleitem).  The alist can be constructed in a one pass, using our
@(see fast-finding-by-name) functions.</p>"

  (b* (((vl-module x) x)
       ;; Reverse order from vl-find-moduleitem
       (acc (vl-gateinstlist-alist x.gateinsts nil))
       (acc (vl-modinstlist-alist x.modinsts acc))
       (acc (vl-taskdecllist-alist x.taskdecls acc))
       (acc (vl-fundecllist-alist x.fundecls acc))
       (acc (vl-paramdecllist-alist x.paramdecls acc))
       (acc (vl-vardecllist-alist x.vardecls acc)))
    (make-fast-alist acc))
  ///
  (defthm vl-moditem-alist-p-of-vl-make-moditem-alist
    (vl-moditem-alist-p (vl-make-moditem-alist x)))

  (defthm hons-assoc-equal-of-vl-make-moditem-alist
    (implies (force (stringp name))
             (equal (hons-assoc-equal name (vl-make-moditem-alist x))
                    (if (vl-find-moduleitem name x)
                        (cons name (vl-find-moduleitem name x))
                      nil)))
    :hints(("Goal" :in-theory (enable vl-find-moduleitem)))))

(define vl-fast-find-moduleitem
  ((name stringp)
   (x    vl-module-p)
   (itemalist (equal itemalist (vl-make-moditem-alist x))))
  :short "Legacy -- Use @(see scopestack) instead.  Alternative to @(see
  vl-find-moduleitem) using fast alist lookups."
  :enabled t
  :hooks nil
  (mbe :logic (vl-find-moduleitem name x)
       :exec (cdr (hons-get name itemalist))))

