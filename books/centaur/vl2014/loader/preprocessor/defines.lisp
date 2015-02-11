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
(include-book "../../util/defs")
(include-book "../../util/echars")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(local (xdoc::set-default-parents vl-define))

(fty::defprod vl-define-formal
  :short "A formal argument to a @('`define') directive."
  ((name    stringp
            :rule-classes :type-prescription
            "Name of the formal argument.  This should be a simple
             identifier.")
   (default stringp
            :rule-classes :type-prescription
            "SystemVerilog only: default text for the argument, if applicable,
             or the empty string if no default was provided.  Note that we
             generally expect this to be trimmed of any whitespace."
            :default "")))

(fty::deflist vl-define-formallist
  :elt-type vl-define-formal)

(defprojection vl-define-formallist->names ((x vl-define-formallist-p))
  :returns (names string-listp)
  (vl-define-formal->name x))

(defprojection vl-define-formallist->defaults ((x vl-define-formallist-p))
  :returns (defaults string-listp)
  (vl-define-formal->default x))

(fty::defprod vl-define
  :parents (preprocessor)
  :short "Internal representation of a @('`define') directive."
  ((name    stringp :rule-classes :type-prescription)
   (formals vl-define-formallist-p
            "Formal arguments to the text macro, if any.")
   (body    stringp :rule-classes :type-prescription
            "Macro text associated with this definition. Note that we generally
             expect this to be trimmed of any whitespace.")
   (loc     vl-location-p
            "Location of this definition in the source code.")))

(fty::deflist vl-defines
  :parents (preprocessor)
  :elt-type vl-define)


(define vl-find-define
  :short "Look up a definition in the defines list."
  ((name stringp)
   (x    vl-defines-p))
  :returns (guts (iff (vl-define-p guts) guts))
  :parents (vl-defines-p)
  (cond ((atom x)
         nil)
        ((equal (string-fix name) (vl-define->name (car x)))
         (vl-define-fix (car x)))
        (t
         (vl-find-define name (cdr x)))))

(define vl-delete-define
  :short "Delete an entry from the defines list, if it exists."
  ((name stringp)
   (x    vl-defines-p))
  :returns (new-x vl-defines-p)
  :parents (vl-defines-p)
  (cond ((atom x)
         nil)
        ((equal (string-fix name) (vl-define->name (car x)))
         (vl-delete-define name (cdr x)))
        (t
         (cons (vl-define-fix (car x))
               (vl-delete-define name (cdr x))))))

(define vl-add-define
  :short "Add a definition to the defines list."
  ((a vl-define-p)
   (x vl-defines-p))
  :returns (new-x vl-defines-p)
  (cons (vl-define-fix a) (vl-defines-fix x)))

(define vl-make-initial-defines ((x string-listp))
  :returns (defs vl-defines-p)
  :parents (vl-defines-p)
  :short "Simple way to build a @(see vl-defines-p) that @('`define')s a list
of names to @('1')."
  (if (atom x)
      nil
    (cons (make-vl-define :name (car x)
                          :formals nil
                          :body "1"
                          :loc *vl-fakeloc*)
          (vl-make-initial-defines (cdr x)))))

