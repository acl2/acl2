; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book.

(in-package "ACL2")

(include-book "satisfiable-add-proof-clause-base")

; possible helpful lemmas:
(include-book "sat-drat-claim-1")

; Temporary, during development:
(local (include-book "tools/remove-hyps" :dir :system))

(defun drat-indices (j alist drat-hints)

; based on RATp1

  (if (endp alist)
      nil
    (let* ((index (caar alist))
           (clause (cdar alist)))
      (cond
       ((deleted-clause-p clause)
        (drat-indices j (cdr alist) drat-hints))
       ((eql index (caar drat-hints)) ; perform RAT
        (if (equal j index)
            (cdar drat-hints)
          (drat-indices j (cdr alist) (cdr drat-hints))))
       (t (drat-indices j (cdr alist) drat-hints))))))

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
          (vc (verify-clause formula c rup-indices drat-hints ncls ndel))
          (vc-success (car vc))
          (new-formula (mv-nth 2 vc))
          (drat-indices (drat-indices index (formula-fal new-formula) drat-hints)))
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
    vc-success
    (proof-entry-p entry)
    (not (proof-entry-deletion-p entry))
    (formula-p formula)
    (solution-p a formula)
    (not (equal nc-up t))
    (consp c)
    (not (satisfiable (add-proof-clause entry-index c new-formula)))
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

(defun defclaim-fn (n hyps body args)
  `(defthm ,(if n
                (packn (list 'main '- n))
              'main)
     ,(make-claim-fn hyps body)
     ,@args
     ,@(and (not (assoc-keyword :rule-classes args))
            '(:rule-classes nil))))

(defmacro defclaim! (n hyps body &rest args)
  (defclaim-fn n hyps body args))

(defmacro defclaim (n hyps body &rest args)
  `(local ,(defclaim-fn n hyps body args)))

; Start proof of rat-assignment-not-t.

(defthm member-both-implies-evaluate-clause
  (implies (and (member lit c)
                (member lit a))
           (equal (evaluate-clause c a) t)))

(defthm evaluate-clause-subsetp
  (implies (and (equal (evaluate-clause c b) t)
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

(encapsulate
  ()
  (local (include-book "satisfiable-maybe-shrink-formula"))

  (defclaim 3-1-1
    (vc-success
     (proof-entry-p entry)
     (formula-p formula)
     (solution-p a formula)
     (not (satisfiable (add-proof-clause entry-index c new-formula))))
    (subsetp nc-up
             (unit-propagation formula rup-indices a))
    :hints (("Goal"
             :use main-1
             :in-theory (disable main-2 unit-propagation-identity))))

  (defclaim! 3-1
    (vc-success
     (proof-entry-p entry)
     (formula-p formula)
     (solution-p a formula)
     (not (satisfiable (add-proof-clause entry-index c new-formula))))
    (subsetp nc-up
             (unit-propagation formula rup-indices a))
    :hints (("Goal"
             :use main-1
             :in-theory (disable main-2 unit-propagation-identity)))))

(defclaim 3
  (vc-success
   (proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (not (satisfiable (add-proof-clause entry-index c new-formula))))
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
  (vc-success
   (not (equal (evaluate-clause dp a) t))
   (proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (not (equal nc-up t))
   (not (satisfiable (add-proof-clause entry-index c new-formula)))
   (not (equal d *deleted-clause*)))
  (and (clause-or-assignment-p rat-nc)
       (subsetp rat-nc rat-a))
  :hints (("Goal" :use (main-1 main-3))))

(defun tail-of (x1 x2)
  (cond ((equal x1 x2) t)
        (t (and (consp x2)
                (tail-of x1 (cdr x2))))))

(defthm tail-of-cdr
  (implies (and (true-listp x2)
                (tail-of x1 x2))
           (tail-of (cdr x1) x2)))

(defthm formula-fal-p-tail

; This is a :forward-chaining rule so that we can continue chaining forward
; from formula-fal-p to alistp, etc.

  (implies (and (tail-of x1 x2)
                (formula-fal-p x2))
           (formula-fal-p x1))
  :rule-classes :forward-chaining)

(defthm ratp1-implies-unit-propagation-t-lemma
  (implies (and (RATp1 alist formula nlit drat-hints assignment)
                (formula-p formula)
                (drat-hint-listp drat-hints)
                (clause-or-assignment-p assignment)
                (equal clause
                       (cdr (hons-assoc-equal index alist)))
                (equal new-assignment
                       (rat-assignment assignment nlit clause))
                (not (or (not (member nlit clause))
                         (deleted-clause-p
                          (cdr (hons-assoc-equal index
                                                 (formula-fal formula))))))
                (not (equal new-assignment t))
                (tail-of alist (formula-fal formula)))
           (equal (unit-propagation formula
                                    (drat-indices index alist drat-hints)
                                    new-assignment)
                  t))
  :hints (("Goal"
           :induct (RATp1 alist formula nlit drat-hints assignment)
           :in-theory (enable formula-p))))

(encapsulate
  ()
  (local (include-book "satisfiable-maybe-shrink-formula"))
  (local (in-theory (enable maybe-shrink-formula formula-p)))

  (defclaim 5-1
    ((member nlit d)
     (not (equal (evaluate-clause dp a) t))
     vc-success
     (proof-entry-p entry)
     (formula-p formula)
     (solution-p a formula)
     (not (equal nc-up t))
     (not (satisfiable (add-proof-clause entry-index c new-formula)))
     (not (equal d *deleted-clause*)))
    (equal (unit-propagation new-formula drat-indices rat-nc)
           t)
    :hints (("Goal"
             :in-theory (e/d (verify-clause) (ratp1))
             :use main-4)))

  (defclaim! 5
    ((member nlit d)
     (not (equal (evaluate-clause dp a) t))
     vc-success
     (proof-entry-p entry)
     (formula-p formula)
     (solution-p a formula)
     (not (equal nc-up t))
     (not (satisfiable (add-proof-clause entry-index c new-formula)))
     (not (equal d *deleted-clause*)))
    (equal (unit-propagation formula drat-indices rat-nc)
           t)
    :hints (("Goal"
             :in-theory
             (union-theories '(verify-clause
                               unit-propagation-maybe-shrink-formula)
                             (theory 'minimal-theory))
             :use main-5-1))))

(defclaim 6
  ((member nlit d)
   (not (equal (evaluate-clause dp a) t))
   vc-success
   (proof-entry-p entry)
   (not (proof-entry-deletion-p entry))
   (formula-p formula)
   (solution-p a formula)
   (not (equal nc-up t))
   (not (satisfiable (add-proof-clause entry-index c new-formula))))
  (equal (unit-propagation formula drat-indices rat-a)
         t)
  :hints (("Goal" :use (main-1 main-4 main-5))))

(defthm negate-clause-or-assignment-self-inverts
  (implies (clause-or-assignment-p a)
           (equal (negate-clause-or-assignment
                   (negate-clause-or-assignment a))
                  a)))

(defclaim 7
  ((member nlit d)
   (not (equal (evaluate-clause dp a) t))
   vc-success
   (proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (not (equal nc-up t))
   (not (satisfiable (add-proof-clause entry-index c new-formula)))
   (not (equal d *deleted-clause*)))
  (equal (evaluate-clause (negate-clause-or-assignment rat-a) a)
         t)
  :hints (("Goal"
           :use main-6
           :restrict
           ((unit-propagation-correct
             ((indices
               (drat-indices
                index
                (mv-nth 2 (maybe-shrink-formula ncls ndel formula 1/3))
                (cddr entry)))
              (formula formula)))))))

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
   vc-success
   (proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (not (equal nc-up t))
   (not (satisfiable (add-proof-clause entry-index c new-formula)))
   (not (equal d *deleted-clause*)))
  (equal (evaluate-clause dp a) t)
  :hints (("Goal" :use main-7)))

(defclaim 9
  ((member nlit d)
   (not (equal (evaluate-clause dp a) t))
   vc-success
   (proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (not (equal nc-up t))
   (not (satisfiable (add-proof-clause entry-index c new-formula))))
  (equal (evaluate-clause dp b) t)
  :hints (("Goal" :use main-8)))

(defclaim nil
  ((member nlit d)
   (not (equal (evaluate-clause dp a) t))
   vc-success
   (proof-entry-p entry)
   (formula-p formula)
   (solution-p a formula)
   (not (equal nc-up t))
   (not (satisfiable (add-proof-clause entry-index c new-formula))))
  nil
  :hints (("Goal" :use (main-8 main-9))))

(defthm sat-drat-claim-2-3
  (mv-let (ncls ndel new-formula)
    (verify-clause formula
                   (access add-step entry :clause)
                   (access add-step entry :rup-indices)
                   (access add-step entry :drat-hints)
                   ncls
                   ndel)
    (declare (ignore ndel))
    (implies (and (member (negate (car (access add-step entry :clause)))
                          (cdr (hons-assoc-equal index
                                                 (formula-fal formula))))
                  (not (equal (evaluate-clause
                               (remove-literal
                                (negate (car (access add-step entry :clause)))
                                (cdr (hons-assoc-equal index (formula-fal formula))))
                               assignment)
                              t))
                  ncls
                  (proof-entry-p entry)
                  (not (proof-entry-deletion-p entry))
                  (formula-p formula)
                  (solution-p assignment formula)
                  (not (equal (unit-propagation formula
                                                (access add-step entry
                                                        :rup-indices)
                                                (negate-clause-or-assignment
                                                 (access add-step entry
                                                         :clause)))
                              t))
                  (not (satisfiable (add-proof-clause
                                     (access add-step entry :index)
                                     (access add-step entry :clause)
                                     new-formula))))
             (equal (evaluate-clause
                     (cdr (hons-assoc-equal index (formula-fal formula)))
                     (flip-literal (car (access add-step entry :clause))
                                   assignment))
                    t)))
  :hints (("Goal" :use main))
  :rule-classes nil)
