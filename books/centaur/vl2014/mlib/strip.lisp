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
(include-book "../parsetree")
(include-book "expr-tools")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc stripping-functions
  :parents (mlib)
  :short "Functions for throwing away attributes, widths, etc., so that
expressions and module elements can be compared using @(see equal)."

  :long "<p>In many basic kinds of @(see lint)ing and well-formedness checking,
it is useful to be able to compare module elements using @('equal').  But
@('equal') can report that elements are different because of, e.g., their
location information, widths and other annotations on expressions, and other
kinds of semantically irrelevant attributes.</p>

<p>These <b>stripping</b> functions attempt to strip away these kind of
semantically irrelevant components of module elements, so that they can be
compared with @('equal').  For instance, we replace all locations with @(see
*vl-fakeloc*), replace all attributes with @('nil'), etc.</p>

<p>Exactly what we throw away depends on the kind of module element.  In some
cases this may not be exactly what you want.  See the individual functions for
details.</p>")

(local (xdoc::set-default-parents stripping-functions))

(define vl-atom-strip
  :short "Throw away widths and types from an atom."
  ((x vl-expr-p))
  :guard (vl-atom-p x)
  :returns (x-strip (and (vl-expr-p x-strip)
                         (eq (vl-expr-kind x-strip) :atom)))
  :inline t
  (mbe :logic (change-vl-atom x
                              :finalwidth nil
                              :finaltype nil
                              :atts nil)
       :exec (if (or (vl-atom->finalwidth x)
                     (vl-atom->finaltype x)
                     (vl-atom->atts x))
                 (change-vl-atom x
                                 :finalwidth nil
                                 :finaltype nil
                                 :atts nil)
               x)))

(defines vl-expr-strip
  :short "Throw away attributes and widths, keeping just the core of an
expression. (memoized)"

  :long "<p>Note that we gain significant performance in @(see leftright-check)
by memoizing this function.</p>"

  (define vl-expr-strip ((x vl-expr-p))
    :returns (new-x vl-expr-p)
    :measure (vl-expr-count x)
    :flag :expr
    :verify-guards nil
    (if (vl-fast-atom-p x)
        (vl-atom-strip x)
      (change-vl-nonatom x
                         :args (vl-exprlist-strip (vl-nonatom->args x))
                         :atts nil
                         :finalwidth nil
                         :finaltype nil)))

  (define vl-exprlist-strip ((x vl-exprlist-p))
    :returns (new-x (and (vl-exprlist-p new-x)
                         (equal (len new-x) (len x))))
    :measure (vl-exprlist-count x)
    :flag :list
    (if (atom x)
        nil
      (cons (vl-expr-strip (car x))
            (vl-exprlist-strip (cdr x)))))
  ///
  (deffixequiv-mutual vl-expr-strip)
  (verify-guards vl-expr-strip)

  (memoize 'vl-expr-strip))

(define vl-range-strip ((x vl-range-p))
  :returns (x-strip vl-range-p)
  (b* (((vl-range x) x))
    (change-vl-range x
                     :msb (vl-expr-strip x.msb)
                     :lsb (vl-expr-strip x.lsb))))

(define vl-maybe-range-strip ((x vl-maybe-range-p))
  :returns (x-strip vl-maybe-range-p)
  (if x
      (vl-range-strip x)
    nil))

(defprojection vl-rangelist-strip ((x vl-rangelist-p))
  :returns (x-strip vl-rangelist-p)
  (vl-range-strip x))

(define vl-assign-strip ((x vl-assign-p))
  :returns (x-strip vl-assign-p)
  (b* (((vl-assign x) x))
    (change-vl-assign x
                      :lvalue   (vl-expr-strip x.lvalue)
                      :expr     (vl-expr-strip x.expr)
                      :delay    nil
                      :strength nil
                      :loc      *vl-fakeloc*
                      :atts     nil)))

(defprojection vl-assignlist-strip ((x vl-assignlist-p))
  :returns (x-strip vl-assignlist-p)
  (vl-assign-strip x))

(define vl-plainarg-strip ((x vl-plainarg-p))
  :returns (x-strip vl-plainarg-p)
  (b* (((vl-plainarg x) x))
    (change-vl-plainarg x
                        :expr     (if x.expr
                                      (vl-expr-strip x.expr)
                                    nil)
                        :atts     nil
                        :portname nil
                        :dir      nil)))

(defprojection vl-plainarglist-strip ((x vl-plainarglist-p))
  :returns (x-strip vl-plainarglist-p)
  (vl-plainarg-strip x))

(define vl-namedarg-strip ((x vl-namedarg-p))
  :returns (x-strip vl-namedarg-p)
  (b* (((vl-namedarg x) x))
    (change-vl-namedarg x
                        :expr (if x.expr
                                  (vl-expr-strip x.expr)
                                nil)
                        :atts nil)))

(defprojection vl-namedarglist-strip ((x vl-namedarglist-p))
  :returns (x-strip vl-namedarglist-p)
  (vl-namedarg-strip x))

(define vl-arguments-strip ((x vl-arguments-p))
  :returns (x-strip vl-arguments-p)
  (vl-arguments-case x
    :vl-arguments-named (change-vl-arguments-named x :args (vl-namedarglist-strip x.args))
    :vl-arguments-plain (change-vl-arguments-plain x :args (vl-plainarglist-strip x.args))))


(define vl-modinst-strip ((x vl-modinst-p))
  :returns (x-strip vl-modinst-p)
  (b* (((vl-modinst x) x))
    (change-vl-modinst x
                       :range     (vl-maybe-range-strip x.range)
                       :portargs  (vl-arguments-strip x.portargs)
                       :str nil
                       :delay nil
                       :atts nil
                       :loc *vl-fakeloc*)))

(defprojection vl-modinstlist-strip ((x vl-modinstlist-p))
  :returns (x-strip vl-modinstlist-p)
  (vl-modinst-strip x))

(define vl-gateinst-strip ((x vl-gateinst-p))
  :returns (x-strip vl-gateinst-p)
  (b* (((vl-gateinst x) x))
    (change-vl-gateinst x
                        :range     (vl-maybe-range-strip x.range)
                        :strength  nil
                        :delay     nil
                        :args      (vl-plainarglist-strip x.args)
                        :atts      nil
                        :loc       *vl-fakeloc*)))

(defprojection vl-gateinstlist-strip ((x vl-gateinstlist-p))
  :returns (x-strip vl-gateinstlist-p)
  (vl-gateinst-strip x))

