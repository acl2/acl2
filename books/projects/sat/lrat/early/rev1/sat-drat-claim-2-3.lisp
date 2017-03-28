; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book.

(in-package "ACL2")

(include-book "satisfiable-add-proof-clause-base")

; possible helpful lemmas:
(include-book "sat-drat-claim-1")

; Temporary, during development:
; (local (include-book "tools/remove-hyps" :dir :system))

(defun drat-indices (j index formula nlit drat-hints assignment)

; based on RATp1

  (if (zp index)
      nil
    (let ((next-clause (cdr (hons-get index (formula-fal formula)))))
      (cond
       ((or (deleted-clause-p next-clause)
            (not (member nlit next-clause)))
        (drat-indices j (1- index) formula nlit drat-hints assignment))
       (t ; otherwise, we have a RAT clause
        (let ((new-assignment (rat-assignment assignment nlit next-clause)))
          (if (eq new-assignment t)
              (drat-indices j (1- index) formula nlit drat-hints assignment)
            (mv-let (indices rest-drat-hints)
              (drat-indices-and-hints index drat-hints)
              (if (equal j index)
                  indices
                (drat-indices j (1- index) formula nlit rest-drat-hints
                              assignment))))))))))

(set-ignore-ok t)

(defun b-fn (x)
  `(let* ((a assignment)
          (fal (formula-fal formula))
          (d (cdr (hons-assoc-equal index fal)))
          (c (access add-step entry :clause))
          (lit (car c))
          (nlit (negate lit))
          (dp (remove-literal nlit d))
          (nc (negate-clause-or-assignment c))
          (rup-indices (access add-step entry :rup-indices))
          (nc-up (unit-propagation formula rup-indices nc))
          (rat-a (rat-assignment a nlit d))
          (rat-nc (rat-assignment nc-up nlit d))
          (entry-index (access add-step entry :index))
          (drat-hints (access add-step entry :drat-hints))
          (drat-indices (drat-indices index (formula-max formula) formula nlit
                                      drat-hints nc-up)))
     ,x))

(defmacro b (x)
  (b-fn x))

(defun b-lst-fn (lst)
  (cond ((endp lst) nil)
        (t (cons (b-fn (car lst))
                 (b-lst-fn (cdr lst))))))

(defmacro b-lst (lst)
  (b-lst-fn lst))

(defconst *all-hyps*

; Warning: Keep this in sync with sat-drat-claim-2-3.  Actually, never mind:
; this constant is no longer used, and some hypotheses have disappeared from
; sat-drat-claim-2-3.

  '((member nlit d)
    (not (equal (evaluate-clause dp a)
                t))
    (verify-clause formula c rup-indices drat-hints)
    (proof-entry-p entry)
    (not (proof-entry-deletion-p entry))
    (formula-p formula)
    (solution-p a formula)
    (not (equal nc-up t))
    (consp c)
    (< (formula-max formula) entry-index)
    (not (satisfiable (add-proof-clause entry-index c formula)))
    (hons-assoc-equal index fal)
    (not (equal d *deleted-clause*))
    (not (equal (evaluate-clause d (flip-literal lit a))
                t))))

(defun make-claim-fn (hyps body)
  (let ((hyps (if (eq hyps :all)
                  *all-hyps*
                hyps)))
    `(implies
      (and ,@(b-lst-fn hyps))
      ,(b-fn body))))

; For interactive use:
(defmacro make-claim (hyps x)
  (make-claim-fn hyps x))

(defmacro verify-claim (hyps x)
  `(verify (make-claim ,hyps ,x)))

(defmacro defclaim (n hyps body &rest args)
  (declare (xargs :guard (keyword-value-listp args)))
  `(local (defthm ,(if n
                       (packn (list 'main '- n))
                     'main)
            ,(make-claim-fn hyps body)
            ,@args
            ,@(and (not (assoc-keyword :rule-classes args))
                   '(:rule-classes nil)))))

; Start proof of rat-assignment-not-t.

(defthm member-both-implies-evaluate-clause
  (implies (and (member lit c)
                (member lit a))
           (equal (evaluate-clause c a) t)))

(defthm evaluate-clause-subsetp
  (implies (and (equal (evaluate-clause c b) t)
                (clause-or-assignment-p a)
                (clause-or-assignment-p c)
                (subsetp b a))
           (equal (evaluate-clause c a) t)))

(defthm evaluate-clause-cons
  (implies (and (equal (evaluate-clause c (cons lit a))
                       t)
                (not (member lit c)))
           (equal (evaluate-clause c a)
                  t)))

(defthm rat-assignment-not-t
  (implies (and (clause-or-assignment-p a)
                (clause-or-assignment-p c)
                (not (equal (evaluate-clause (remove-literal nlit c)
                                             a)
                            t)))
           (not (equal (rat-assignment a nlit c) t)))
  :hints (("Goal"
           :in-theory (enable clause-or-assignment-p))))

(defthm formula-p-implies-formula-fal-p
  (implies (formula-p formula)
           (formula-fal-p (formula-fal formula)))
  :hints (("Goal" :in-theory (enable formula-p))))

(defclaim 1
  ((not (equal (evaluate-clause dp a) t))
   (formula-p formula)
   (solution-p a formula)
   (not (equal d *deleted-clause*)))
  (clause-or-assignment-p rat-a))

(defclaim 2
  ((formula-p formula)
   (solution-p a formula))
  (equal (unit-propagation formula rup-indices a)
         a)
  :rule-classes :rewrite)

(defclaim 3-1
  ((proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (< (formula-max formula) entry-index)
   (not (satisfiable (add-proof-clause entry-index c formula))))
  (subsetp nc-up
           (unit-propagation formula rup-indices a))
  :hints (("Goal"
           :use main-1
           :in-theory (disable main-2 unit-propagation-identity))))

(defclaim 3
  ((proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (< (formula-max formula) entry-index)
   (not (satisfiable (add-proof-clause entry-index c formula))))
  (subsetp nc-up a)
  :hints (("Goal" :use main-3-1)))

(defun rat-assignment-monotone-induction (a1 a2 nlit clause)

; This is based on rat-assignment, and is relevant when (subsetp a1 a2) and
; (rat-assignment a2 nlit c) is not t.

  (cond ((endp clause) (list a1 a2))
        ((or (eql (car clause) nlit)
             (member (negate (car clause)) a1))
         (rat-assignment-monotone-induction a1 a2 nlit (cdr clause)))
        ((member (negate (car clause)) a2)
         (rat-assignment-monotone-induction (cons (negate (car clause)) a1)
                                            a2
                                            nlit
                                            (cdr clause)))
        (t
         (rat-assignment-monotone-induction (cons (negate (car clause)) a1)
                                            (cons (negate (car clause)) a2)
                                            nlit
                                            (cdr clause)))))

(defthm rat-assignment-monotone
  (implies (and (subsetp a1 a2)
                (not (equal (rat-assignment a2 lit c)
                            t)))
           (subsetp (rat-assignment a1 lit c)
                    (rat-assignment a2 lit c)))
  :hints (("Goal" :induct (rat-assignment-monotone-induction a1 a2 lit c))))

(defthm clause-or-assignment-p-implies-literalp-car
  (implies (and (clause-or-assignment-p x)
                (consp x))
           (literalp (car x)))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p)))
  :rule-classes :type-prescription)

(defthm rat-assignment-monotone-2
  (implies (and (subsetp a1 a2)
                (clause-or-assignment-p a1)
                (clause-or-assignment-p a2)
                (clause-or-assignment-p c)
                (not (equal (rat-assignment a2 lit c)
                            t)))
           (clause-or-assignment-p (rat-assignment a1 lit c)))
  :hints (("Goal" :induct (rat-assignment-monotone-induction a1 a2 lit c))))

(defclaim 4
  ((not (equal (evaluate-clause dp a) t))
   (proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (not (equal nc-up t))
   (< (formula-max formula) entry-index)
   (not (satisfiable (add-proof-clause entry-index c formula)))
   (not (equal d *deleted-clause*)))
  (and (clause-or-assignment-p rat-nc)
       (subsetp rat-nc rat-a))
  :hints (("Goal" :use (main-1 main-3))))

(defthm ratp1-implies-unit-propagation-t-lemma
  (let* ((next-clause (cdr (hons-assoc-equal index (formula-fal formula))))
         (drat-indices (drat-indices index index2 formula nlit drat-hints
                                     assignment))
         (new-assignment (rat-assignment assignment nlit next-clause)))
    (implies (and (RATp1 index2 formula nlit drat-hints assignment)
                  (posp index)
                  (natp index2) ; (formula-max formula)
                  (<= index index2) ; (formula-max formula)
                  (not (or (deleted-clause-p next-clause)
                           (not (member nlit next-clause))))
                  (not (equal new-assignment t)))
             (equal (unit-propagation formula drat-indices new-assignment)
                    t)))
  :hints (("Goal" :induct (RATp1 index2 formula nlit drat-hints assignment))))

(defthm natp-formula-max
  (implies (formula-p formula)
           (natp (formula-max formula)))
  :hints (("Goal" :in-theory (enable formula-p)))
  :rule-classes :forward-chaining)

(defclaim 5
  ((member nlit d)
   (not (equal (evaluate-clause dp a) t))
   (verify-clause formula c rup-indices drat-hints)
   (proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (not (equal nc-up t))
   (< (formula-max formula) entry-index)
   (not (satisfiable (add-proof-clause entry-index c formula)))
   (hons-assoc-equal index fal)
   (not (equal d *deleted-clause*)))
  (equal (unit-propagation formula drat-indices rat-nc)
         t)
  :hints (("Goal"
           :in-theory (enable verify-clause)
           :use main-4)))

(defclaim 6
  ((member nlit d)
   (not (equal (evaluate-clause dp a) t))
   (verify-clause formula c rup-indices drat-hints)
   (proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (not (equal nc-up t))
   (< (formula-max formula) entry-index)
   (not (satisfiable (add-proof-clause entry-index c formula))))
  (equal (unit-propagation formula drat-indices rat-a)
         t)
  :hints (("Goal" :use (main-1 main-4 main-5))))

(in-theory (disable ratp1-implies-unit-propagation-t-lemma))

(defthm negate-clause-or-assignment-self-inverts
  (implies (clause-or-assignment-p a)
           (equal (negate-clause-or-assignment
                   (negate-clause-or-assignment a))
                  a)))

(defclaim 7
  ((member nlit d)
   (not (equal (evaluate-clause dp a) t))
   (verify-clause formula c rup-indices drat-hints)
   (proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (not (equal nc-up t))
   (< (formula-max formula) entry-index)
   (not (satisfiable (add-proof-clause entry-index c formula)))
   (not (equal d *deleted-clause*)))
  (equal (evaluate-clause (negate-clause-or-assignment rat-a) a)
         t)
  :hints (("Goal"
           :use main-6
           :restrict ((unit-propagation-correct
                       ((indices
                         (drat-indices
                          index (car formula)
                          formula (- (cadr (car entry)))
                          (cddr entry)
                          (unit-propagation formula (cadr entry)
                                            (negate-clause-or-assignment
                                             (cdr (car entry))))))))))))

(defthm negate-rat-assignment-key-base-lemma
  (implies (and (clause-or-assignment-p a)
                (clause-or-assignment-p b)
                (subsetp b a))
           (not (equal (evaluate-clause (negate-clause-or-assignment b)
                                        a)
                       t))))

(defthm negate-rat-assignment-key-base
  (implies (clause-or-assignment-p a)
           (not (equal (evaluate-clause (negate-clause-or-assignment a)
                                        a)
                       t))))

(defthm clause-or-assignment-p-implies-negate-car-not-member-cdr
  (implies (and (clause-or-assignment-p c)
                (consp c))
           (not (member (negate (car c)) (cdr c))))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p)))
  :rule-classes :forward-chaining)

(defthm negate-rat-assignment-key
  (implies (and (clause-or-assignment-p a)
                (clause-or-assignment-p d)
                (equal (evaluate-clause (negate-clause-or-assignment
                                         (rat-assignment a x d))
                                        a)
                       t))
           (equal (evaluate-clause (remove-literal x d) a)
                  t)))

(defclaim 8
  ((member nlit d)
   (verify-clause formula c rup-indices drat-hints)
   (proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (not (equal nc-up t))
   (< (formula-max formula) entry-index)
   (not (satisfiable (add-proof-clause entry-index c formula)))
   (not (equal d *deleted-clause*)))
  (equal (evaluate-clause dp a) t)
  :hints (("Goal" :use main-7)))

(defclaim 9
  ((member nlit d)
   (not (equal (evaluate-clause dp a) t))
   (verify-clause formula c rup-indices drat-hints)
   (proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (not (equal nc-up t))
   (< (formula-max formula) entry-index)
   (not (satisfiable (add-proof-clause entry-index c formula))))
  (equal (evaluate-clause dp b) t)
  :hints (("Goal" :use main-8)))

(defclaim nil
  ((member nlit d)
   (not (equal (evaluate-clause dp a) t))
   (verify-clause formula c rup-indices drat-hints)
   (proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (not (equal nc-up t))
   (< (formula-max formula) entry-index)
   (not (satisfiable (add-proof-clause entry-index c formula))))
  nil
  :hints (("Goal" :use (main-8 main-9))))

(defthm sat-drat-claim-2-3

; Warning: Keep this in sync with *all-hyps*.

  (implies (and (member (negate (car (access add-step entry :clause)))
                        (cdr (hons-assoc-equal index
                                               (formula-fal formula))))
                (not (equal (evaluate-clause
                             (remove-literal
                              (negate (car (access add-step entry :clause)))
                              (cdr (hons-assoc-equal index (formula-fal formula))))
                             assignment)
                            t))
                (verify-clause formula
                               (access add-step entry :clause)
                               (access add-step entry :rup-indices)
                               (access add-step entry :drat-hints))
                (proof-entry-p entry)
                (formula-p formula)
                (solution-p assignment formula)
                (not (equal (unit-propagation formula
                                              (access add-step entry
                                                      :rup-indices)
                                              (negate-clause-or-assignment
                                               (access add-step entry
                                                       :clause)))
                            t))
                (< (formula-max formula)
                   (access add-step entry :index))
                (not (satisfiable (add-proof-clause
                                   (access add-step entry :index)
                                   (access add-step entry :clause)
                                   formula))))
           (equal (evaluate-clause
                   (cdr (hons-assoc-equal index (formula-fal formula)))
                   (flip-literal (car (access add-step entry :clause))
                                 assignment))
                  t))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use main))
  :rule-classes nil)
