; Copyright (C) 2018 Centaur Technology
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
; Original author (this file): Sol Swords <sswords@centtech.com>

(in-package "AIGNET")

(include-book "xdoc/archive-matching-topics" :dir :system)
(local
 (progn
   (include-book "aig-cnf")
   (include-book "aiger")
   (include-book "aignet-absstobj")
   (include-book "aig-sim")
   (include-book "arrays")
   (include-book "bit-lemmas")
   (include-book "cnf")
   (include-book "construction")
   (include-book "copying")
   (include-book "eval")
   (include-book "from-hons-aig-fast")
   (include-book "from-hons-aig")
   (include-book "litp")
   (include-book "portcullis")
   (include-book "prune")
   (include-book "refcounts")
   (include-book "semantics")
   (include-book "snodes")
   (include-book "to-hons-aig")
   (include-book "transforms")
   (include-book "simplify-marked")
   ;; (include-book "types")
   (include-book "vecsim")
   ))


(xdoc::archive-matching-topics
 (or (str::strprefixp "[books]/centaur/aignet/" (cdr (assoc :from x)))
     (str::strprefixp "[books]/centaur/truth/" (cdr (assoc :from x)))
     (equal "[books]/centaur/misc/nth-nat-equiv.lisp" (cdr (assoc :from x)))))
