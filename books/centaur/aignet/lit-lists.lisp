; AIGNET - And-Inverter Graph Networks
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
; Original author: Sol Swords <sswords@centtech.com>


(in-package "AIGNET")

(include-book "centaur/satlink/litp" :dir :system)
(include-book "arrays")
(include-book "std/stobjs/clone" :dir :system)
(local (std::add-default-post-define-hook :fix))

  ;; Measure for aignet-lit->cnf is just the id-val of the lit-IDs, but we need to
  ;; take the max over a list of lits for the list case
(define lits-max-id-val ((lits lit-listp))
  (if (atom lits)
      0
    (max (lit->var (car lits))
         (lits-max-id-val (cdr lits))))
  ///
  (fty::deffixequiv lits-max-id-val)
  
  ;; (local (in-theory (disable lookup-id-out-of-bounds member)))



  (defthm lits-max-id-val-of-cdr
    (<= (lits-max-id-val (cdr x)) (lits-max-id-val x))
    :rule-classes :linear)

  (defthm lits-max-id-val-of-car
    (<= (lit->var (car x)) (lits-max-id-val x))
    :rule-classes :linear))




(define lit-copy ((lit litp) copy)
  :guard (< (lit->var lit) (lits-length copy))
  :inline t
  :returns (copylit litp :rule-classes :type-prescription)
  (lit-negate-cond (get-lit (lit->var lit) copy) (lit->neg lit))
  ///
  (defret lit->var-of-lit-copy
    (equal (lit->var copylit) (lit->var (get-lit (lit->var lit) copy))))

  (defretd lit->neg-of-lit-copy
    (equal (lit->neg copylit) (b-xor (lit->neg lit) (lit->neg (get-lit (lit->var lit) copy))))))

(define lit-list-copies ((lits lit-listp)
                         (copy))
  :guard (< (lits-max-id-val lits) (lits-length copy))
  :guard-hints (("goal" :in-theory (enable lits-max-id-val)))
  :returns (lits lit-listp)
  (if (atom lits)
      nil
    (cons (lit-copy (car lits) copy)
          (lit-list-copies (cdr lits) copy))))


(define lit-list-marked ((lits lit-listp)
                         (mark))
  :guard (< (lits-max-id-val lits) (bits-length mark))
  :guard-hints (("goal" :in-theory (enable lits-max-id-val)))
  (if (atom lits)
      t
    (and (eql (get-bit (lit->var (car lits)) mark) 1)
         (lit-list-marked (cdr lits) mark))))

