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

(include-book "ipasir-logic")
(local (include-book "centaur/satlink/cnf-basics" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))

(local (in-theory (disable ifix)))

(defmacro l- (x)
  `(lit-negate ,x))

(defmacro l+ (x)
  `(lit-fix ,x))

(local (defthm eval-lit-of-negate-strong
         (implies (equal (lit-fix z) (lit-negate x))
                  (equal (eval-lit z assign)
                         (b-not (eval-lit x assign))))
         :hints(("Goal" :in-theory (enable eval-lit)))))


(define ipasir-cancel-new-clause (ipasir)
  :parents (ipasir-formula)
  :short "Identity function in execution; in the logic, ensures that the new-clause
          field of the ipasir is empty, which it must be by the guard."
  :long "<p>See @(see ipasir-add-binary), particularly
@('ipasir-add-binary-formula'), for an example: if we didn't use this function
at the beginning of @('ipasir-add-binary'), then we'd need a hypothesis of
@('(not (ipasir$a->new-clause ipasir))') in
@('ipasir-add-binary-formula').</p>"
  :guard (ipasir-empty-new-clause ipasir)
  :inline t
  :returns (new-ipasir)
  (mbe :logic (non-exec (change-ipasir$a ipasir :new-clause nil))
       :exec ipasir)
  ///
  (defret ipasir-cancel-new-clause-status
    (equal (ipasir$a->status new-ipasir)
           (ipasir$a->status ipasir)))

  (defret ipasir-cancel-new-clause-formula
    (equal (ipasir$a->formula new-ipasir)
           (ipasir$a->formula ipasir)))

  (defret ipasir-cancel-new-clause-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-cancel-new-clause-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir)))

  (in-theory (disable (ipasir-cancel-new-clause))))

(define ipasir-cancel-assumption (ipasir)
  :parents (ipasir-formula)
  :short "Identity function in execution; in the logic, ensures that the assumption
          field of the ipasir is empty, which it must be by the guard."
  :long "<p>See @(see ipasir-add-binary), particularly
@('ipasir-add-binary-formula'), for an example: if we didn't use this function
at the beginning of @('ipasir-add-binary'), then we'd need a hypothesis of
@('(not (ipasir$a->assumption ipasir))') in
@('ipasir-add-binary-formula').</p>"
  :guard (not (ipasir-get-assumption ipasir))
  :inline t
  :returns (new-ipasir)
  (mbe :logic (non-exec (change-ipasir$a ipasir :assumption nil))
       :exec ipasir)
  ///
  (defret ipasir-cancel-assumption-status
    (equal (ipasir$a->status new-ipasir)
           (ipasir$a->status ipasir)))

  (defret ipasir-cancel-assumption-formula
    (equal (ipasir$a->formula new-ipasir)
           (ipasir$a->formula ipasir)))

  (defret ipasir-cancel-assumption-assumption
    (not (ipasir$a->assumption new-ipasir)))

  (defret ipasir-cancel-assumption-new-clause
    (equal (ipasir$a->new-clause new-ipasir)
           (ipasir$a->new-clause ipasir)))

  (in-theory (disable (ipasir-cancel-assumption))))

(define ipasir-add-empty (ipasir)
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add an empty clause.  Likely useless because the solver is then unsat forever."
  (b* ((ipasir (ipasir-cancel-new-clause ipasir)))
    (ipasir-finalize-clause ipasir))
  ///
  (defret ipasir-add-empty-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-empty-formula
    (equal (ipasir$a->formula new-ipasir)
           (cons nil (ipasir$a->formula ipasir))))

  (defretd ipasir-add-empty-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env) 0)
    :hints(("Goal" :in-theory (enable eval-formula eval-clause))))

  (defret ipasir-add-empty-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-empty-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))

(define ipasir-add-unary (ipasir (a litp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add a unary clause to the formula, permanently restricting the given literal to be true."
  (b* ((ipasir (ipasir-cancel-new-clause ipasir))
       (ipasir (ipasir-add-lit ipasir a)))
    (ipasir-finalize-clause ipasir))
  ///
  (defret ipasir-add-unary-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-unary-formula
    (equal (ipasir$a->formula new-ipasir)
           (cons (lit-list-fix (list a)) (ipasir$a->formula ipasir))))

  (defret ipasir-add-unary-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (b-and (eval-lit a env)
                  (eval-formula (ipasir$a->formula ipasir) env))))

  (defret ipasir-add-unary-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-unary-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))


(define ipasir-add-binary (ipasir (a litp) (b litp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add a binary clause to the formula"
  (b* ((ipasir (ipasir-cancel-new-clause ipasir))
       (ipasir (ipasir-add-lit ipasir a))
       (ipasir (ipasir-add-lit ipasir b)))
    (ipasir-finalize-clause ipasir))
  ///
  (defret ipasir-add-binary-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-binary-formula
    (equal (ipasir$a->formula new-ipasir)
           (cons (lit-list-fix (list b a))
                 (ipasir$a->formula ipasir))))

  (defret ipasir-add-binary-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) assum)
           (eval-formula (cons (list a b)
                               (ipasir$a->formula ipasir))
                         assum)))

  (defret ipasir-add-binary-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-binary-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))

(define ipasir-add-ternary (ipasir (a litp) (b litp) (c litp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add a ternary clause to the formula"
  (b* ((ipasir (ipasir-cancel-new-clause ipasir))
       (ipasir (ipasir-add-lit ipasir a))
       (ipasir (ipasir-add-lit ipasir b))
       (ipasir (ipasir-add-lit ipasir c)))
    (ipasir-finalize-clause ipasir))
  ///
  (defret ipasir-add-ternary-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-ternary-formula
    (equal (ipasir$a->formula new-ipasir)
           (cons (lit-list-fix (list c b a))
                 (ipasir$a->formula ipasir))))

  (defret ipasir-add-ternary-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) assum)
           (eval-formula (cons (list c b a)
                               (ipasir$a->formula ipasir))
                         assum)))

  (defret ipasir-add-ternary-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-ternary-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))

;; Note: at one point we defined this form of add-clause which checked for
;; duplicate/contradictory literals.  But we think all reasonable solvers
;; already do this for us so we'll just use the non-checking versions for now.

;; (define ipasir-add-4ary (ipasir (a litp) (b litp) (c litp) (d litp))
;;   :guard (and (not (eq (ipasir-get-status ipasir) :undef))
;;               (ipasir-empty-new-clause ipasir))
;;   :returns (new-ipasir)
;;   :parents (ipasir-formula)
;;   (b* ((a (lit-fix a))
;;        (b (lit-fix b))
;;        (c (lit-fix c))
;;        (d (lit-fix d))
;;        (ipasir (ipasir-cancel-new-clause ipasir))
;;        ((when (or (int= (- a) b) (int= (- a) c) (int= (- a) d)
;;                   (int= (- b) c) (int= (- b) d)
;;                   (int= (- c) d)))
;;         (ipasir-input ipasir))
;;        (ipasir (ipasir-add-lit ipasir a))
;;        (ipasir (if (int= a b)
;;                    (if (int= a c)
;;                        (if (int= a d)
;;                            ipasir
;;                          (ipasir-add-lit ipasir d))
;;                      (b* ((ipasir (ipasir-add-lit ipasir c)))
;;                        (if (or (int= a d) (int= c d))
;;                            ipasir
;;                          (ipasir-add-lit ipasir d))))
;;                  (b* ((ipasir (ipasir-add-lit ipasir b)))
;;                    (if (or (int= a c) (int= b c))
;;                        (if (or (int= a d) (int= b d))
;;                            ipasir
;;                          (ipasir-add-lit ipasir d))
;;                      (b* ((ipasir (ipasir-add-lit ipasir c)))
;;                        (if (or (int= a d) (int= b d) (int= c d))
;;                            ipasir
;;                          (ipasir-add-lit ipasir d))))))))
;;     (ipasir-finalize-clause ipasir))
;;   ///
;;   (defret ipasir-add-4ary-status
;;     (equal (ipasir$a->status new-ipasir) :input))

;;   (defret ipasir-add-4ary-formula
;;     (equal (eval-formula (ipasir$a->formula new-ipasir) env)
;;            (eval-formula (cons (list d c b a)
;;                                (ipasir$a->formula ipasir))
;;                          env)))

;;   (defret ipasir-add-4ary-new-clause
;;     (not (ipasir$a->new-clause new-ipasir)))

;;   (defret ipasir-add-4ary-assumption
;;     (equal (ipasir$a->assumption new-ipasir)
;;            (ipasir$a->assumption ipasir))))

(define ipasir-add-4ary (ipasir (a litp) (b litp) (c litp) (d litp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add a 4-literal clause to the formula"
  (b* ((ipasir (ipasir-cancel-new-clause ipasir))
       (ipasir (ipasir-add-lit ipasir a))
       (ipasir (ipasir-add-lit ipasir b))
       (ipasir (ipasir-add-lit ipasir c))
       (ipasir (ipasir-add-lit ipasir d)))
    (ipasir-finalize-clause ipasir))
  ///
  (defret ipasir-add-4ary-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-4ary-formula
    (equal (ipasir$a->formula new-ipasir)
           (cons (lit-list-fix (list d c b a))
                 (ipasir$a->formula ipasir))))

  (defret ipasir-add-4ary-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (eval-formula (cons (list d c b a)
                               (ipasir$a->formula ipasir))
                         env)))

  (defret ipasir-add-4ary-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-4ary-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))


(define ipasir-add-list-aux (ipasir (clause lit-listp))
  :guard (not (eq (ipasir-get-status ipasir) :undef))
  :returns (new-ipasir)
  (if (atom clause)
      (ipasir-finalize-clause ipasir)
    (b* ((ipasir (ipasir-add-lit ipasir (car clause))))
      (ipasir-add-list-aux ipasir (cdr clause))))
  ///
  (defret ipasir-add-list-aux-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-list-aux-formula
    (equal (ipasir$a->formula new-ipasir)
           (cons (revappend (lit-list-fix clause) (ipasir$a->new-clause ipasir))
                 (ipasir$a->formula ipasir))))

  (defret ipasir-add-list-aux-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (eval-formula (cons (append clause (ipasir$a->new-clause ipasir))
                               (ipasir$a->formula ipasir))
                         env)))

  (defret ipasir-add-list-aux-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-list-aux-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))

(define ipasir-add-list (ipasir (clause lit-listp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add a clause (given as a list of literals) to the formula"
  (b* ((ipasir (ipasir-cancel-new-clause ipasir)))
    (ipasir-add-list-aux ipasir clause))
  ///
  (defret ipasir-add-list-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-list-formula
    (equal (ipasir$a->formula new-ipasir)
           (cons (rev (lit-list-fix clause))
                 (ipasir$a->formula ipasir)))
    :hints(("Goal" :in-theory (enable ipasir-add-list-aux-formula))))

  (defret ipasir-add-list-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (eval-formula (cons clause (ipasir$a->formula ipasir))
                         env)))

  (defret ipasir-add-list-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-list-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))

(define ipasir-add-list-ordered-aux (ipasir (clause lit-listp))
  :guard (not (eq (ipasir-get-status ipasir) :undef))
  :returns (new-ipasir)
  (if (atom clause)
      (ipasir-input ipasir)
    (b* ((ipasir (ipasir-add-list-ordered-aux ipasir (cdr clause))))
      (ipasir-add-lit ipasir (car clause))))
  ///
  (defret ipasir-add-list-ordered-aux-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defret ipasir-add-list-ordered-aux-formula
    (equal (ipasir$a->formula new-ipasir)
           (ipasir$a->formula ipasir)))

  (defret ipasir-add-list-ordered-aux-new-clause
    (equal (ipasir$a->new-clause new-ipasir)
           (append (lit-list-fix clause) (ipasir$a->new-clause ipasir))))

  (defret ipasir-add-list-ordered-aux-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))

(define ipasir-add-list-ordered (ipasir (clause lit-listp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add a clause (given as a list of literals) to the formula"
  (b* ((ipasir (ipasir-cancel-new-clause ipasir))
       (ipasir (ipasir-add-list-ordered-aux ipasir clause)))
    (ipasir-finalize-clause ipasir))
  ///
  (defret ipasir-add-list-ordered-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-list-ordered-formula
    (equal (ipasir$a->formula new-ipasir)
           (cons (lit-list-fix clause)
                 (ipasir$a->formula ipasir)))
    :hints(("Goal" :in-theory (enable ipasir-add-list-ordered-aux-formula))))

  (defret ipasir-add-list-ordered-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-list-ordered-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))

(define rev-each (x)
  (if (atom x)
      nil
    (cons (rev (car x))
          (rev-each (cdr x)))))

(define ipasir-add-clauses (ipasir (clauses lit-list-listp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add a list of clauses to the formula"
  (if (atom clauses)
      (b* ((ipasir (ipasir-cancel-new-clause ipasir)))
        (ipasir-input ipasir))
    (b* ((ipasir (ipasir-add-list ipasir (car clauses))))
      (ipasir-add-clauses ipasir (cdr clauses))))
  ///
  (defret ipasir-add-clauses-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-clauses-formula
    (equal (ipasir$a->formula new-ipasir)
           (append (rev (rev-each (lit-list-list-fix clauses)))
                   (ipasir$a->formula ipasir)))
    :hints(("Goal" :in-theory (enable lit-list-list-fix
                                      rev-each
                                      ipasir-add-list-formula))))

  (defret ipasir-add-clauses-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (eval-formula (append clauses (ipasir$a->formula ipasir))
                         env)))

  (defret ipasir-add-clauses-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-clauses-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))

(define ipasir-add-clauses-ordered (ipasir (clauses lit-list-listp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add a list of clauses to the formula"
  (if (atom clauses)
      (b* ((ipasir (ipasir-cancel-new-clause ipasir)))
        (ipasir-input ipasir))
    (b* ((ipasir (ipasir-add-clauses-ordered ipasir (cdr clauses))))
      (ipasir-add-list-ordered ipasir (car clauses))))
  ///
  (defret ipasir-add-clauses-ordered-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defretd ipasir-add-clauses-ordered-formula
    (equal (ipasir$a->formula new-ipasir)
           (append (lit-list-list-fix clauses)
                   (ipasir$a->formula ipasir)))
    :hints(("Goal" :in-theory (enable lit-list-list-fix
                                      ipasir-add-list-ordered-formula))))

  (defret ipasir-add-clauses-ordered-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-add-clauses-ordered-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))


(define ipasir-set-buf (ipasir (out litp) (in litp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add clauses restricting @('out') to have the same value as @('in')."
  (b* ((ipasir (ipasir-cancel-new-clause ipasir))
       (ipasir (ipasir-add-binary ipasir (l- out) in)))
    (ipasir-add-binary ipasir out (l- in)))
  ///
  (defret ipasir-set-buf-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defret ipasir-set-buf-formula
    (implies (syntaxp (not (equal ipasir ''nil)))
             (equal (ipasir$a->formula new-ipasir)
                    (append (ipasir$a->formula (ipasir-set-buf nil out in))
                            (ipasir$a->formula ipasir))))
    :hints(("Goal" :in-theory (e/d (ipasir-add-binary-formula)
                                   ((ipasir-cancel-new-clause))))))

  (defret ipasir-set-buf-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (b-and (b-eqv (eval-lit out env)
                         (eval-lit in env))
                  (eval-formula (ipasir$a->formula ipasir) env))))

  (defret ipasir-set-buf-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-set-buf-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))

(define ipasir-set-and (ipasir (out litp) (in1 litp) (in2 litp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add clauses restricting @('out') to be the AND of @('in1') and @('in2')."
  (b* ((ipasir (ipasir-cancel-new-clause ipasir))
       ;; ~in1 -> ~out
       (ipasir (ipasir-add-binary ipasir (l- out) in1))
       ;; ~in2 -> ~out
       (ipasir (ipasir-add-binary ipasir (l- out) in2)))
    ;; in1 & in2 -> out
    (ipasir-add-ternary ipasir out (l- in1) (l- in2)))
  ///
  (defret ipasir-set-and-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defret ipasir-set-and-formula
    (implies (syntaxp (not (equal ipasir ''nil)))
             (equal (ipasir$a->formula new-ipasir)
                    (append (ipasir$a->formula (ipasir-set-and nil out in1 in2))
                            (ipasir$a->formula ipasir))))
    :hints(("Goal" :in-theory (e/d (ipasir-add-binary-formula
                                    ipasir-add-ternary-formula)
                                   ((ipasir-cancel-new-clause))))))

  (defret ipasir-set-and-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (b-and (b-eqv (eval-lit out env)
                         (b-and (eval-lit in1 env)
                                (eval-lit in2 env)))
                  (eval-formula (ipasir$a->formula ipasir) env))))

  (defret ipasir-set-and-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-set-and-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))

(define ipasir-set-or (ipasir (out litp) (in1 litp) (in2 litp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :inline t
  :short "Add clauses restricting @('out') to be the OR of @('in1') and @('in2')."
  (ipasir-set-and ipasir (l- out) (l- in1) (l- in2))
  ///
  (defret ipasir-set-or-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defret ipasir-set-or-formula
    (implies (syntaxp (not (equal ipasir ''nil)))
             (equal (ipasir$a->formula new-ipasir)
                    (append (ipasir$a->formula (ipasir-set-or nil out in1 in2))
                            (ipasir$a->formula ipasir)))))

  (defret ipasir-set-or-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (b-and (b-eqv (eval-lit out env)
                         (b-ior (eval-lit in1 env)
                                (eval-lit in2 env)))
                  (eval-formula (ipasir$a->formula ipasir) env))))

  (defret ipasir-set-or-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-set-or-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))

(define ipasir-set-mux (ipasir (out litp) (test litp) (then litp) (else litp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add clauses restricting @('out') to be @('(if test then else)')."
  (b* (;; test & then -> out
       (ipasir (ipasir-add-ternary ipasir out (l- test) (l- then)))
       ;; test & ~then -> ~out
       (ipasir (ipasir-add-ternary ipasir (l- out) (l- test) then))
       ;; ~test & else -> out
       (ipasir (ipasir-add-ternary ipasir out test (l- else)))
       ;; ~test & ~else -> ~out
       (ipasir (ipasir-add-ternary ipasir (l- out) test else))
       ;; the above clauses are sufficient but the two below are helpful,
       ;; then & else -> out
       (ipasir (ipasir-add-ternary ipasir out (l- then) (l- else)))
       ;; ~then & ~else -> ~out
       (ipasir (ipasir-add-ternary ipasir (l- out) then else)))
    ipasir)
  
  ///
  (defret ipasir-set-mux-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defret ipasir-set-mux-formula
    (implies (syntaxp (not (equal ipasir ''nil)))
             (equal (ipasir$a->formula new-ipasir)
                    (append (ipasir$a->formula (ipasir-set-mux nil out test then else))
                            (ipasir$a->formula ipasir))))
    :hints(("Goal" :in-theory (e/d (ipasir-add-ternary-formula)))))

  (defret ipasir-set-mux-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (b-and (b-eqv (eval-lit out env)
                         (b-ite (eval-lit test env)
                                (eval-lit then env)
                                (eval-lit else env)))
                  (eval-formula (ipasir$a->formula ipasir) env))))

  (defret ipasir-set-mux-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-set-mux-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))
       

(define ipasir-set-xor (ipasir (out litp) (in1 litp) (in2 litp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :short "Add clauses restricting @('out') to be the XOR of @('in1') and @('in2')."
  (b* (;; in1 & in2 -> ~out
       (ipasir (ipasir-add-ternary ipasir out (l- in1) in2))
       ;; in1 & ~in2 -> out
       (ipasir (ipasir-add-ternary ipasir (l- out) (l- in1) (l- in2)))
       ;; ~in1 & in2 -> out
       (ipasir (ipasir-add-ternary ipasir out in1 (l- in2)))
       ;; ~in1 & ~in2 -> ~out
       (ipasir (ipasir-add-ternary ipasir (l- out) in1 in2)))
    ipasir)

  ///
  (defret ipasir-set-xor-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defret ipasir-set-xor-formula
    (implies (syntaxp (not (equal ipasir ''nil)))
             (equal (ipasir$a->formula new-ipasir)
                    (append (ipasir$a->formula (ipasir-set-xor nil out in1 in2))
                            (ipasir$a->formula ipasir))))
    :hints(("Goal" :in-theory (e/d (ipasir-add-ternary-formula)))))

  (defret ipasir-set-xor-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (b-and (b-eqv (eval-lit out env)
                         (b-xor (eval-lit in1 env)
                                (eval-lit in2 env)))
                (eval-formula (ipasir$a->formula ipasir) env))))

  (defret ipasir-set-xor-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-set-xor-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))

(define ipasir-set-iff (ipasir (out litp) (in1 litp) (in2 litp))
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :parents (ipasir-formula)
  :inline t
  :short "Add clauses restricting @('out') to be the IFF of @('in1') and @('in2')."
  (ipasir-set-xor ipasir out (l- in1) in2)
  ///
  (defret ipasir-set-iff-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defret ipasir-set-iff-formula
    (implies (syntaxp (not (equal ipasir ''nil)))
             (equal (ipasir$a->formula new-ipasir)
                    (append (ipasir$a->formula (ipasir-set-iff nil out in1 in2))
                            (ipasir$a->formula ipasir)))))

  (defret ipasir-set-iff-eval-formula
    (equal (eval-formula (ipasir$a->formula new-ipasir) env)
           (b-and (b-eqv (eval-lit out env)
                         (b-eqv (eval-lit in1 env)
                                (eval-lit in2 env)))
                  (eval-formula (ipasir$a->formula ipasir) env))))

  (defret ipasir-set-iff-new-clause
    (not (ipasir$a->new-clause new-ipasir)))

  (defret ipasir-set-iff-assumption
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir))))



(defxdoc ipasir-formula
  :parents (ipasir)
  :short "Tools for constructing the ipasir formula."
  :long "<p>We provide several helper functions for constructing formulas:</p>

<ul>
<li>@('ipasir-add-*ary') add a fixed-length clause to the formula</li>
<li>@('ipasir-add-list') adds a clause from a list to the formula</li>
<li>@('ipasir-set-*') add clauses restricting the literal @('out') to be
assigned the given logical function of the other input literals</li>
</ul>

<p>These all have a guard saying that the current new-clause of the ipasir
stobj must be empty, and they preserve this property unconditionally.</p>")



(defthm ipasir-solve$a-unsat-implies-unsat
  (b* (((ipasir$a solver))
       ((mv status &) (ipasir-solve$a solver)))
    (implies (and (equal formula solver.formula)
                  (equal 1 (eval-formula formula env$))
                  (case-split (equal 1 (eval-cube solver.assumption env$))))
             (not (equal status :unsat))))
  :hints (("goal" :use ipasir-solve$a-unsat
           :in-theory (e/d (satlink::eval-cube-when-subset)
                           (ipasir-solve$a-unsat)))))

(defthm ipasir-solve$a-unsat-when-not-sat-or-failed
  (b* (((mv status &) (ipasir-solve$a solver)))
    (implies (not (equal status :sat))
             (equal (equal status :failed)
                    (not (equal status :unsat))))))


(define ipasir-check-equivalence (ipasir (lit1 litp) (lit2 litp))
  :returns (mv (status (or (equal status :failed)
                           (equal status :unsat)
                           (equal status :sat))
                       :rule-classes ((:forward-chaining :trigger-terms (status))))
               new-ipasir)
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (not (ipasir-get-assumption ipasir))
              (ipasir-empty-new-clause ipasir))
  (b* ((ipasir (ipasir-cancel-assumption ipasir))
       (ipasir (ipasir-assume ipasir lit1))
       (ipasir (ipasir-assume ipasir (lit-negate lit2)))
       ((mv status1 ipasir) (ipasir-solve ipasir))
       ((when (or (eq status1 :sat)
                  (eq status1 :failed)))
        (mv status1 ipasir))
       (ipasir (ipasir-assume ipasir (lit-negate lit1)))
       (ipasir (ipasir-assume ipasir lit2)))
    (ipasir-solve ipasir))
  ///
  (defret ipasir-check-equivalence-ipasir-status
    (equal (ipasir$a->status new-ipasir)
           (case status
             (:sat :sat)
             (:unsat :unsat)
             (otherwise :input))))

  (defret ipasir-check-equivalence-formula
    (equal (ipasir$a->formula new-ipasir)
           (ipasir$a->formula ipasir)))

  (defret ipasir-check-equivalence-new-clause
    (equal (ipasir$a->new-clause new-ipasir) nil))

  (defret ipasir-check-equivalence-assumption
    (equal (ipasir$a->assumption new-ipasir) nil))


  (defret ipasir-check-equivalence-unsat
    (implies (and (equal 1 (eval-formula (ipasir$a->formula ipasir) env))
                  (case-split (not (equal (eval-lit lit1 env)
                                          (eval-lit lit2 env)))))
             (not (equal status :unsat)))))
             
             
