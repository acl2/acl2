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
(include-book "../parsetree")
(include-book "centaur/fty/visitor" :dir :system)
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


(fty::defvisitor-template strip ((x :object))
  :returns (new-x :update)
  :field-fns ((atts (lambda (x) (declare (ignore x)) nil)))
  :prod-fns ((vl-special     (type (lambda (x) (declare (ignore x)) nil)))
             (vl-literal     (type (lambda (x) (declare (ignore x)) nil)))
             (vl-index       (type (lambda (x) (declare (ignore x)) nil)))
             (vl-unary       (type (lambda (x) (declare (ignore x)) nil)))
             (vl-binary      (type (lambda (x) (declare (ignore x)) nil)))
             (vl-qmark       (type (lambda (x) (declare (ignore x)) nil)))
             (vl-mintypmax   (type (lambda (x) (declare (ignore x)) nil)))
             (vl-concat      (type (lambda (x) (declare (ignore x)) nil)))
             (vl-multiconcat (type (lambda (x) (declare (ignore x)) nil)))
             (vl-call        (type (lambda (x) (declare (ignore x)) nil)))
             (vl-cast        (type (lambda (x) (declare (ignore x)) nil)))
             (vl-inside      (type (lambda (x) (declare (ignore x)) nil)))
             (vl-tagged      (type (lambda (x) (declare (ignore x)) nil)))
             (vl-pattern     (type (lambda (x) (declare (ignore x)) nil))))
  :fnname-template <type>-strip)

(fty::defvisitors vl-strip
  :template strip
  :types (vl-modinstlist vl-gateinstlist vl-assignlist))
