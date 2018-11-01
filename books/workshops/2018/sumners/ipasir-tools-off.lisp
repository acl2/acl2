; IPASIR - Link from ACL2 to IPASIR incremental sat solvers
; Copyright (C) 2017 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>

(in-package "IPASIR")

(include-book "centaur/ipasir/ipasir-tools" :dir :system)
(local (include-book "centaur/satlink/cnf-basics" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))

(local (in-theory (disable ifix)))
             
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lit+off ((a litp) (off litp))
  :inline t
  :returns (b litp)
  (satlink::make-lit (+ (satlink::lit->var a) off)
                     (satlink::lit->neg a)))

(define clause+off ((cls lit-listp) (off litp))
  :returns (r lit-listp)
  (if (atom cls) ()
    (cons (lit+off (first cls) off)
          (clause+off (rest cls) off))))

(define clauses+off ((clss lit-list-listp) (off litp))
  :returns (r lit-list-listp)
  (if (atom clss) ()
    (cons (clause+off (first clss) off)
          (clauses+off (rest clss) off))))

(define ipasir-add-unary+off (ipasir (a litp) (off litp))
  :guard (and (not (eq (ipasir::ipasir-get-status ipasir) :undef))
              (ipasir::ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add a unary clause to the formula, permanently restricting the given literal to be true."
  (b* ((ipasir (ipasir-cancel-new-clause ipasir))
       (ipasir (ipasir-add-lit ipasir (lit+off a off))))
    (ipasir-finalize-clause ipasir))
  ///
  (defret ipasir-add-unary+off-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-unary+off-formula
    (equal (ipasir$a->formula new-ipasir)
           (cons (lit-list-fix (list (lit+off a off))) (ipasir$a->formula ipasir))))

  (defret ipasir-add-unary+off-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (b-and (eval-lit (lit+off a off) env)
                  (eval-formula (ipasir$a->formula ipasir) env))))

  (defret ipasir-add-unary+off-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-unary+off-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))


(define ipasir-add-list+off-aux (ipasir (clause lit-listp) (off litp))
  :guard (not (eq (ipasir-get-status ipasir) :undef))
  :returns (new-ipasir)
  (if (atom clause)
      (ipasir-finalize-clause ipasir)
    (b* ((ipasir (ipasir-add-lit ipasir (lit+off (car clause) off))))
      (ipasir-add-list+off-aux ipasir (cdr clause) off)))
  ///
  (defret ipasir-add-list+off-aux-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-list+off-aux-formula
    (equal (ipasir$a->formula new-ipasir)
           (cons (revappend (lit-list-fix (clause+off clause off))
                            (ipasir$a->new-clause ipasir))
                 (ipasir$a->formula ipasir)))
    :hints (("Goal" :in-theory (enable clause+off))))

  (defret ipasir-add-list+off-aux-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (eval-formula (cons (append (clause+off clause off)
                                       (ipasir$a->new-clause ipasir))
                               (ipasir$a->formula ipasir))
                         env))
    :hints (("Goal" :in-theory (enable clause+off))))

  (defret ipasir-add-list+off-aux-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-list+off-aux-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))


(define ipasir-add-list+off (ipasir (clause lit-listp) (off litp))
  :guard (and (not (eq (ipasir::ipasir-get-status ipasir) :undef))
              (ipasir::ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add a clause (given as a list of literals) to the formula"
  (b* ((ipasir (ipasir-cancel-new-clause ipasir)))
    (ipasir-add-list+off-aux ipasir clause off))
  ///
  (defret ipasir-add-list+off-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-list+off-formula
    (equal (ipasir$a->formula new-ipasir)
           (cons (rev (lit-list-fix (clause+off clause off)))
                 (ipasir$a->formula ipasir)))
    :hints(("Goal" :in-theory (enable ipasir-add-list+off-aux-formula))))

  (defret ipasir-add-list+off-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (eval-formula (cons (clause+off clause off)
                               (ipasir$a->formula ipasir))
                         env)))

  (defret ipasir-add-list+off-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-list+off-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))


(define ipasir-add-clauses+off (ipasir (clauses lit-list-listp) (off litp))
  :guard (and (not (eq (ipasir::ipasir-get-status ipasir) :undef))
              (ipasir::ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add a list of clauses to the formula"
  (if (atom clauses)
      (b* ((ipasir (ipasir-cancel-new-clause ipasir)))
        (ipasir-input ipasir))
    (b* ((ipasir (ipasir-add-list+off ipasir (car clauses) off)))
      (ipasir-add-clauses+off ipasir (cdr clauses) off)))
  ///
  (defret ipasir-add-clauses+off-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-clauses+off-formula
    (equal (ipasir$a->formula new-ipasir)
           (append (rev (rev-each (lit-list-list-fix (clauses+off clauses off))))
                   (ipasir$a->formula ipasir)))
    :hints(("Goal" :in-theory (enable lit-list-list-fix
                                      rev-each
                                      clauses+off
                                      ipasir-add-list+off-formula))))

  (defret ipasir-add-clauses+off-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (eval-formula (append (clauses+off clauses off)
                                 (ipasir$a->formula ipasir))
                         env))
    :hints(("Goal" :in-theory (enable clauses+off))))

  (defret ipasir-add-clauses+off-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-clauses+off-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))

