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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))


(defxdoc fixing-functions
  :parents (mlib)
  :short "Functions for throwing away attributes, widths, etc., so that
expressions and module elements can be compared using @(see equal)."

  :long "<p>In many basic kinds of linting and well-formedness checking, it is
useful to be able to compare module elements using @('equal').  But @('equal')
can report that elements are different because of, e.g., their location
information, widths and other annotations on expressions, and other kinds of
semantically irrelevant attributes.</p>

<p>These fixing functions attempt to throw away these kind of semantically
irrelevant components of module elements, so that they can be compared with
@('equal').  For instance, we replace all locations with @(see *vl-fakeloc*),
etc.</p>

<p>Exactly what we throw away depends on the kind of module element.  In some
cases this may not be exactly what you want.  See the individual functions for
details.</p>")

(local (xdoc::set-default-parents fixing-functions))

(define vl-atom-fix
  :short "Throw away widths and types from an atom."
  ((x vl-atom-p))
  :returns (x-fix vl-atom-p :hyp :fguard)

  :prepwork ((local (in-theory (enable vl-atom-p
                                       vl-atom
                                       vl-atom->finalwidth
                                       vl-atom->finaltype
                                       vl-atom->guts))))

  (mbe :logic (change-vl-atom x
                              :finalwidth nil
                              :finaltype nil)
       :exec (if (or (vl-atom->finalwidth x)
                     (vl-atom->finaltype x))
                 (change-vl-atom x
                                 :finalwidth nil
                                 :finaltype nil)
               x)))


(defsection vl-expr-strip
  :short "Throw away attributes and widths, keeping just the core of an
expression."
  ;; BOZO consider optimizing to avoid reconsing already-fixed expressions
  (mutual-recursion
   (defund vl-expr-strip (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atom-p x)
         (vl-atom-fix x)
       (change-vl-nonatom x
                          :args (vl-exprlist-fix (vl-nonatom->args x))
                          :atts nil
                          :finalwidth nil
                          :finaltype nil)))
   (defund vl-exprlist-fix (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         nil
       (cons (vl-expr-strip (car x))
             (vl-exprlist-fix (cdr x))))))

  (flag::make-flag flag-vl-expr-strip
                   vl-expr-strip
                   :flag-mapping ((vl-expr-strip . expr)
                                  (vl-exprlist-fix . list)))

  (defthm len-of-vl-exprlist-fix
    (equal (len (vl-exprlist-fix x))
           (len x))
    :hints(("Goal"
            :induct (len x)
            :expand (vl-exprlist-fix x))))

  (defthm-flag-vl-expr-strip lemma
    (expr (implies (force (vl-expr-p x))
                   (vl-expr-p (vl-expr-strip x)))
          :name vl-expr-p-of-vl-expr-strip)
    (list (implies (force (vl-exprlist-p x))
                   (vl-exprlist-p (vl-exprlist-fix x)))
          :name vl-exprlist-p-of-vl-exprlist-fix)
    :hints(("Goal"
            :induct (flag-vl-expr-strip flag x)
            :expand ((vl-expr-strip x)
                     (vl-exprlist-fix x))))))


(define vl-range-fix ((x vl-range-p))
  :returns (x-fix vl-range-p :hyp :fguard)
  (b* (((vl-range x) x))
    (change-vl-range x
                     :msb (vl-expr-strip x.msb)
                     :lsb (vl-expr-strip x.lsb))))

(define vl-maybe-range-fix ((x vl-maybe-range-p))
  :returns (x-fix vl-maybe-range-p :hyp :fguard)
  (if x
      (vl-range-fix x)
    x))

(defprojection vl-rangelist-fix (x)
  (vl-range-fix x)
  :guard (vl-rangelist-p x)
  :result-type vl-rangelist-p)

(define vl-assign-fix ((x vl-assign-p))
  :returns (x-fix vl-assign-p :hyp :fguard)
  (b* (((vl-assign x) x))
    (change-vl-assign x
                      :lvalue   (vl-expr-strip x.lvalue)
                      :expr     (vl-expr-strip x.expr)
                      :delay    nil
                      :strength nil
                      :loc      *vl-fakeloc*
                      :atts     nil)))

(defprojection vl-assignlist-fix (x)
  (vl-assign-fix x)
  :guard (vl-assignlist-p x)
  :result-type vl-assignlist-p)

(define vl-plainarg-fix ((x vl-plainarg-p))
  :returns (x-fix vl-plainarg-p :hyp :fguard)
  (b* (((vl-plainarg x) x))
    (change-vl-plainarg x
                        :expr     (if x.expr
                                      (vl-expr-strip x.expr)
                                    nil)
                        :atts     nil
                        :portname nil
                        :dir      nil)))

(defprojection vl-plainarglist-fix (x)
  (vl-plainarg-fix x)
  :guard (vl-plainarglist-p x)
  :result-type vl-plainarglist-p)

(define vl-namedarg-fix ((x vl-namedarg-p))
  :returns (x-fix vl-namedarg-p :hyp :fguard)
  (b* (((vl-namedarg x) x))
    (change-vl-namedarg x
                        :expr (if x.expr
                                  (vl-expr-strip x.expr)
                                nil)
                        :atts nil)))

(defprojection vl-namedarglist-fix (x)
  (vl-namedarg-fix x)
  :guard (vl-namedarglist-p x)
  :result-type vl-namedarglist-p)

(define vl-arguments-fix ((x vl-arguments-p))
  :returns (x-fix vl-arguments-p :hyp :fguard)
  (b* ((namedp (vl-arguments->namedp x))
       (args   (vl-arguments->args x))
       (args-fix (if namedp
                     (vl-namedarglist-fix args)
                   (vl-plainarglist-fix args))))
    (vl-arguments namedp args-fix)))

(define vl-modinst-fix ((x vl-modinst-p))
  :returns (x-fix vl-modinst-p :hyp :fguard)
  (b* (((vl-modinst x) x))
    (change-vl-modinst x
                       :range     (vl-maybe-range-fix x.range)
                       :paramargs (vl-arguments-fix x.paramargs)
                       :portargs  (vl-arguments-fix x.portargs)
                       :str nil
                       :delay nil
                       :atts nil
                       :loc *vl-fakeloc*)))

(defprojection vl-modinstlist-fix (x)
  (vl-modinst-fix x)
  :guard (vl-modinstlist-p x)
  :result-type vl-modinstlist-p)

(define vl-gateinst-fix ((x vl-gateinst-p))
  :returns (x-fix vl-gateinst-p :hyp :fguard)
  (b* (((vl-gateinst x) x))
    (change-vl-gateinst x
                        :range     (vl-maybe-range-fix x.range)
                        :strength  nil
                        :delay     nil
                        :args      (vl-plainarglist-fix x.args)
                        :atts      nil
                        :loc       *vl-fakeloc*)))

(defprojection vl-gateinstlist-fix (x)
  (vl-gateinst-fix x)
  :guard (vl-gateinstlist-p x)
  :result-type vl-gateinstlist-p)



