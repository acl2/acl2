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
(include-book "defines")
(include-book "../../mlib/writer")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(define vl-pp-define-formal ((x vl-define-formal-p) &key (ps 'ps))
  (b* (((vl-define-formal x))
       (ps (vl-print-str x.name))
       ((unless x.default)
        ps))
    (vl-ps-seq (vl-print " = ")
               (vl-print x.default))))

(define vl-pp-define-formals ((x vl-define-formallist-p) &key (ps 'ps))
  (b* (((when (atom x))
        ps)
       (ps (vl-pp-define-formal (car x)))
       ((when (atom (cdr x)))
        ;; Last argument, no comma.
        ps))
    (vl-ps-seq (vl-print ", ")
               (vl-pp-define-formals (cdr x)))))

(define vl-pp-define ((name stringp) (x vl-maybe-define-p) &key (ps 'ps))
  :parents (vl-define)
  :short "Pretty print a @('`define') directive."
  (if x
      (b* (((vl-define x)))
        (vl-ps-seq (vl-print "`define ")
                   (vl-print-str (vl-maybe-escape-identifier name))
                   (vl-print " ")
                   (if (not x.formals)
                       ps
                     (vl-ps-seq (vl-print "(")
                                (vl-pp-define-formals x.formals)
                                (vl-print ") ")))
                   (vl-print-str x.body)
                   (vl-println "")))
    (vl-ps-seq (vl-print "`undef ")
               (vl-print-str (vl-maybe-escape-identifier name))
               (vl-println ""))))


(define vl-pps-define ((name stringp) (x vl-maybe-define-p))
  :returns (str stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-define name x)))

(define vl-pp-defines ((x vl-defines-p) &key (ps 'ps))
  :measure (len (vl-defines-fix x))
  (b* ((x (vl-defines-fix x)))
    (if (atom x)
        ps
      (vl-ps-seq (vl-pp-define (caar x) (cdar x))
                 (vl-pp-defines (cdr x))))))
