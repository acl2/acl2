; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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
(include-book "aignet-logic")
(local (include-book "clause-processors/join-thms" :dir :system))

(defevaluator nodetyp-ev nodetyp-evlst
  ((if a b c)
   (not a)
   (equal a b)
   (stype a)
   (ctype a)
   (regp a)))

(local (acl2::def-join-thms nodetyp-ev))

;; get-stype-info-clause:

;; Goes over the clause looking for literals whose atoms are of one of the forms:
;; (equal (stype x) (quote val))
;; (equal (ctype (stype x)) (quote val))
;; (equal (reg (stype x)) (quote val))
;; or symmetric.

;; For each such literal, we store some information about x in typetab.
;; Each entry associates a term with its list of possible stypes.  A term that
;; isn't bound in the table implicitly has all 6 possible stypes.  Each literal
;; of one of the forms above may cause the possibilities associated with term X
;; to be reduced.

(define recognize-equal-quote-atom ((atom pseudo-termp))
  :returns (mv ok quote (term pseudo-termp :hyp :guard))
  (b* (((unless (and (consp atom)
                     (eq (car atom) 'equal)))
        (mv nil nil nil))
       (args (cdr atom))
       ((mv quote term) (if (quotep (first args))
                            (mv (first args) (second args))
                          (mv (second args) (first args))))
       ((unless (quotep quote))
        (mv nil nil nil)))
    (mv t (cadr quote) term))

  ///

  (defthm eval-when-recognize-equal-quote-atom
    (b* (((mv ok quote term)
          (recognize-equal-quote-atom atom)))
      (implies ok
               (equal (nodetyp-ev atom a)
                      (equal (nodetyp-ev term a) quote))))))

(deflist stype-listp (x)
  (stypep x)
  :true-listp t)

(local (defthm eqlable-listp-when-stype-listp
         (implies (stype-listp x)
                  (and (eqlable-listp x)
                       (true-listp x)))
         :hints(("Goal" :in-theory (enable stype-listp stypep)))))

(define vartablep (vartable)
  (if (atom vartable)
      (eq vartable nil)
    (and (consp (car vartable))
         (pseudo-termp (caar vartable))
         (stype-listp (cdar vartable))
         (vartablep (cdr vartable))))
  ///
  (defthm vartablep-cdr
    (implies (vartablep x)
             (vartablep (cdr x))))

  (defthm vartablep-cons
    (equal (vartablep (cons a x))
           (and (consp a)
                (pseudo-termp (car a))
                (stype-listp (cdr a))
                (vartablep x))))
  (defthm vartable-alistp
    (implies (vartablep x)
             (alistp x))
    :rule-classes :forward-chaining)

  (defthm stype-listp-assoc-vartable
    (implies (and (vartablep vartable)
                  (consp (assoc x vartable)))
             (stype-listp (cdr (assoc x vartable))))))


(define stype-vartable-lookup (x (vartable vartablep))
  :returns (possibilities stype-listp :hyp :guard)
  (let ((look (assoc-equal x vartable)))
    (if (consp look)
        (cdr look)
      '(:const :pi :reg :gate :po :nxst))))

(define stype-vartable-invariant ((vartable vartablep)
                                  (a alistp))
  "The stype of each term bound in vartable evaluates under a to one of the
symbols in its list."
  (if (atom vartable)
      t
    (and (member-equal (stype (nodetyp-ev (caar vartable) a)) (cdar vartable))
         (stype-vartable-invariant (cdr vartable) a)))

  ///

  (local (defthm eval-of-assoc-vartable
           (implies (and (stype-vartable-invariant vartable a)
                         (consp (assoc term vartable)))
                    (member (stype (nodetyp-ev term a))
                            (cdr (assoc term vartable))))))

  (defthm eval-of-stype-vartable-lookup
    (implies (stype-vartable-invariant vartable a)
             (member (stype (nodetyp-ev term a))
                     (stype-vartable-lookup term vartable)))
    :hints(("Goal" :in-theory (enable stype-vartable-lookup))
           (and stable-under-simplificationp
                '(:in-theory (enable stype stype-fix stypep)))))

  (defthm stype-vartable-invariant-of-cons
    (iff (stype-vartable-invariant (cons x vartable) a)
         (and (stype-vartable-invariant vartable a)
              (member (stype (nodetyp-ev (car x) a)) (cdr x)))))

  (local (defthm consp-remove-equal-when-member
           (implies (and (member a x)
                         (not (equal a b)))
                    (consp (remove b x)))
           :hints(("Goal" :in-theory (enable member remove)))))

  (defthm consp-remove-equal-of-stype-variable-lookup
    (implies (and (stype-vartable-invariant vartable a)
                  (not (equal (stype (nodetyp-ev term a)) val)))
             (consp (remove-equal val (stype-vartable-lookup term vartable))))
    :hints (("goal" :use eval-of-stype-vartable-lookup
             :in-theory (disable eval-of-stype-vartable-lookup))))

  (defthm stype-vartable-invariant-nil
    (stype-vartable-invariant nil a)))


(define filter-ctype (negp val (stypes stype-listp))
  :returns (new-stypes stype-listp :hyp :guard)
  (if (atom stypes)
      nil
    (if (iff negp
             (equal (ctype (car stypes)) val))
        (cons (car stypes)
              (filter-ctype negp val (cdr stypes)))
      (filter-ctype negp val (cdr stypes))))
  ///

  (defthm filter-ctype-correct
    (implies (member x stypes)
             (and (implies (equal (ctype x) val)
                           (member x (filter-ctype t val stypes)))
                  (implies (not (equal (ctype x) val))
                           (member x (filter-ctype nil val stypes))))))

  (defthm consp-filter-ctype-of-vartable-lookup
    (implies (stype-vartable-invariant vartable a)
             (and (implies (equal (ctype (stype (nodetyp-ev x a))) val)
                           (consp (filter-ctype t val (stype-vartable-lookup x vartable))))
                  (implies (not (equal (ctype (stype (nodetyp-ev x a))) val))
                           (consp (filter-ctype nil val (stype-vartable-lookup x vartable))))))
    :hints (("goal" :use ((:instance filter-ctype-correct
                           (x (stype (nodetyp-ev x a)))
                           (stypes (stype-vartable-lookup x vartable))))
             :in-theory (disable filter-ctype-correct)))))

(local (Defthm stype-listp-remove
         (implies (stype-listp x)
                  (stype-listp (remove a x)))))

(define filter-regp (negp val (stypes stype-listp))
  :returns (new-stypes stype-listp :hyp :guard)
  (if (atom stypes)
      nil
    (if (iff negp
             (equal (regp (car stypes)) val))
        (cons (car stypes)
              (filter-regp negp val (cdr stypes)))
      (filter-regp negp val (cdr stypes))))
  ///

  (defthm filter-regp-correct
    (implies (member x stypes)
             (and (implies (equal (regp x) val)
                           (member x (filter-regp t val stypes)))
                  (implies (not (equal (regp x) val))
                           (member x (filter-regp nil val stypes))))))

  (defthm consp-filter-regp-of-vartable-lookup
    (implies (stype-vartable-invariant vartable a)
             (and (implies (equal (regp (stype (nodetyp-ev x a))) val)
                           (consp (filter-regp t val (stype-vartable-lookup x vartable))))
                  (implies (not (equal (regp (stype (nodetyp-ev x a))) val))
                           (consp (filter-regp nil val (stype-vartable-lookup x vartable))))))
    :hints (("goal" :use ((:instance filter-regp-correct
                           (x (stype (nodetyp-ev x a)))
                           (stypes (stype-vartable-lookup x vartable))))
             :in-theory (disable filter-regp-correct)))))


(define get-stype-info-lit ((lit pseudo-termp)
                            (vartable vartablep))
  :prepwork ((local (defthm pseudo-termp-cadr-of-function-call
                      (implies (and (pseudo-termp x)
                                    (consp x)
                                    (not (eq (car x) 'quote)))
                               (pseudo-termp (cadr x)))
                      :hints(("Goal" :expand ((pseudo-termp x)))))))
  :returns (mv contra (new-vartable vartablep :hyp :guard))
  (b* (((mv negp atom)
        (if (and (consp lit)
                 (eq (car lit) 'not))
            (mv t (cadr lit))
          (mv nil lit)))
       ((mv ok val typterm)
        (recognize-equal-quote-atom atom))
       ((unless ok) (mv nil vartable)))
    (case-match typterm
      (('stype x)
       (b* (((when negp)
             ;; Already know the stype of this term, so do nothing.  Revisit this
             ;; if we want to do any advanced strategic stuff like looking at
             ;; equivalences between stypes of different terms.
             (mv nil vartable))
            ;; hyp: (not (equal (stype x) val))
            (possibilities (stype-vartable-lookup x vartable))
            (remaining (remove val possibilities))
            (vartable (cons (cons x remaining) vartable))
            ((when (endp remaining))
             ;; contradiction
             (mv t vartable)))
         (mv nil vartable)))
      (('ctype ('stype x))
       (b* ((possibilities (stype-vartable-lookup x vartable))
            (remaining (filter-ctype negp val possibilities))

            (vartable (cons (cons x remaining) vartable))
            ((when (endp remaining))
             ;; contradiction
             (mv t vartable)))
         (mv nil vartable)))
      (('regp ('stype x))
       (b* ((possibilities (stype-vartable-lookup x vartable))
            (remaining (filter-regp negp val possibilities))

            (vartable (cons (cons x remaining) vartable))
            ((when (endp remaining))
             ;; contradiction
             (mv t vartable)))
         (mv nil vartable)))
      (& (mv nil vartable))))

  ///

  (defthm get-stype-info-lit-correct
    (mv-let (contra new-vartable)
      (get-stype-info-lit lit vartable)
      (implies (and (not (nodetyp-ev lit a))
                    (stype-vartable-invariant vartable a))
               (and (stype-vartable-invariant new-vartable a)
                    (not contra))))))



(define get-stype-info-clause ((clause pseudo-term-listp))
  :returns (mv contra (vartable vartablep :hyp :guard))
  (b* (((when (atom clause)) (mv nil nil))
       ((mv contra2 vartable) (get-stype-info-clause (cdr clause)))
       ((when contra2) (mv contra2 vartable)))
    (get-stype-info-lit (car clause) vartable))
  ///
  (defthm get-stype-info-clause-correct
    (mv-let (contra vartable)
      (get-stype-info-clause clause)
      (implies (not (nodetyp-ev (acl2::disjoin clause) a))
               (and (not contra)
                    (stype-vartable-invariant vartable a))))))


(define get-stype-equivs ((vartable vartablep))
  :returns (new-lits pseudo-term-listp :hyp :guard)
  (b* (((when (atom vartable)) nil)
       ((cons term possible) (car vartable))
       ((when (consp (cdr possible)))
        ;; more than one possibility
        (get-stype-equivs (cdr vartable))))
    (cons `(not (equal (stype ,term) ',(car possible)))
          (get-stype-equivs (cdr vartable))))
  ///
  (defthm get-stype-equivs-correct
    (implies (stype-vartable-invariant vartable a)
             (not (nodetyp-ev (acl2::disjoin (get-stype-equivs vartable))
                              a)))))

(define stype-cp ((clause pseudo-term-listp))
  (b* (((mv contra vartable) (get-stype-info-clause clause))
       ((when contra)
        ;; done
        nil))
    (list (append (get-stype-equivs vartable) clause)))
  ///
  (defthm stype-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (nodetyp-ev (acl2::conjoin-clauses (stype-cp clause)) a))
             (nodetyp-ev (acl2::disjoin clause) a))
    :rule-classes :clause-processor))

(local
 (progn
   (defund is-gate (x)
     (equal (stype x) (gate-stype)))

   (defthm prove-is-gate
     (implies (equal (stype x) (gate-stype))
              (is-gate x))
     :hints(("Goal" :in-theory (enable is-gate))))

   (defthm is-gate-by-elim
     (implies (and (not (equal (ctype (stype x)) (const-ctype)))
                   (not (equal (ctype (stype x)) (in-ctype)))
                   (equal (regp (stype x)) 0)
                   (not (equal (stype x) (po-stype))))
              (is-gate x))
     :hints (("goal" :in-theory '(prove-is-gate))
             (and stable-under-simplificationp
                  '(:clause-processor stype-cp))))))


