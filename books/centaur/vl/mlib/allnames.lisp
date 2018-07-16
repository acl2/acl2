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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "VL")
(include-book "scopestack")
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(fty::defalist nameset :key-type stringp)

(define nameset-add ((k stringp)
                     (x nameset-p))
  :returns (new-x nameset-p)
  (b* ((k (string-fix k))
       (x (nameset-fix x)))
    (if (hons-get k x)
        x
      (hons-acons k t x))))

(define maybe-nameset-add ((k maybe-stringp)
                           (x nameset-p))
  :returns (new-x nameset-p)
  :prepwork ((local (Defthm stringp-of-maybe-string-fix
                      (implies k
                               (stringp (maybe-string-fix k)))
                      :hints(("Goal" :in-theory (enable maybe-string-fix))))))
  (b* ((k (maybe-string-fix k))
       (x (nameset-fix x)))
    (if k
        (if (hons-get k x)
            x
          (hons-acons k t x))
      x)))

(define vl-maybe-scopeid-nameset-add ((k vl-maybe-scopeid-p)
                                      (x nameset-p))
  :returns (new-x nameset-p)
  (b* ((k (vl-maybe-scopeid-fix k))
       (x (nameset-fix x)))
    (if (stringp k)
        (if (hons-get k x)
            x
          (hons-acons k t x))
      x)))

(fty::defvisitor-template allnames ((x :object)
                                    (nameset nameset-p))
  :returns (new-nameset (:acc nameset :fix (nameset-fix nameset))
                        nameset-p)
  :fnname-template <type>-allnames
  :prod-fns
  ;; BOZO.  Should we be also collecting names from other places?  It might be
  ;; safer to gether up all names from all expressions, arguments, named
  ;; parameter actuals, etc.

  ;; BOZO what about names for properties, sequences, etc...

  ;; We should at least keep this in sync with scopeitems (i.e. anything that
  ;; can be looked up by name should have its name listed here).
  ((vl-interfaceport (name nameset-add))
   (vl-regularport   (name maybe-nameset-add))
   (vl-portdecl      (name nameset-add))
   (vl-vardecl       (name nameset-add))
   (vl-modinst       (instname maybe-nameset-add))
   (vl-gateinst      (name maybe-nameset-add))
   (vl-paramdecl     (name nameset-add))
   (vl-blockstmt     (name maybe-nameset-add))
   (vl-fundecl       (name nameset-add))
   (vl-taskdecl      (name nameset-add))
   (vl-fwdtypedef    (name nameset-add))
   (vl-typedef       (name nameset-add))
   (vl-genvar        (name nameset-add))
   (vl-genblock      (name vl-maybe-scopeid-nameset-add))
   (vl-genarray      (name maybe-nameset-add))
   (vl-module        (name nameset-add)
                     (origname nameset-add))
   (vl-udp           (name nameset-add))
   (vl-config        (name nameset-add))
   (vl-package       (name nameset-add))
   (vl-interface     (name nameset-add))
   (vl-program       (name nameset-add))
   (vl-class         (name nameset-add))
   (vl-dpiimport     (name nameset-add))
   ))

; Added by Matt K. 2/20/2016, pending possible mod by Sol to defvisitor.
(set-bogus-measure-ok t)

(fty::defvisitors vl-design-allnames
  :template allnames
  :types (vl-design))
