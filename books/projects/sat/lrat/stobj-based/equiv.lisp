; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../README.

; This modification of the list-based lrat-checker.lisp uses stobjs to speed up
; the handling of assignments, in particular, evaluation of literals and
; clauses.

(in-package "LRAT")

(include-book "lrat-checker")

(local (include-book "../list-based/soundness"))

(in-theory (disable push-literal
                    negate-clause-or-assignment negate-clause
                    unit-propagation unit-propagation$
                    verify-clause verify-clause$
                    verify-proof-rec verify-proof$-rec
                    verify-proof verify-proof$
                    clausep clausep$
                    formula-p formula-p$))

(local (in-theory (disable nth update-nth)))

(defthm arr-matches-stk-implies-booleanp-alt
  (implies (and (a$p a$)
                (natp i)
                (< i (a$ptr a$)))
           (booleanp (nth (nth i (nth *a$stki* a$))
                          (nth *a$arri* a$))))
  :hints (("Goal"
           :in-theory '(a$p a$arr-length a$p-weak a$ptr a$ptrp natp)
           :use arr-matches-stk-implies-booleanp)))

(defun list-assignment-rec (i a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (natp i)
                              (<= i (a$ptr a$)))))
  (cond ((zp i)
         nil)
        (t (let* ((i (1- i))
                  (var (a$stki i a$))
                  (val (a$arri var a$)))
             (cons (if (equal val nil)
                       (negate var)
                     var)
                   (list-assignment-rec i a$))))))

(defund list-assignment (a$)
  (declare (xargs :stobjs a$
                  :guard (a$p a$)))
  (list-assignment-rec (a$ptr a$) a$))

; Test:
(defthm test-list-assignment
  (equal (with-local-stobj a$
           (mv-let (ast a$)
             (b* ((a$ (initialize-a$ 10 a$))
                  ((mv - a$) (push-literal 3 a$))
                  ((mv - a$) (push-literal -5 a$))
                  ((mv - a$) (push-literal -1 a$))
                  (ast (list-assignment a$)))
               (mv ast a$))
             ast))
         '(-1 -5 3))
  :rule-classes nil)

(defthm list-assignment-rec-update-nth-a$ptr
  (equal (list-assignment-rec i
                              (update-nth *a$ptr* j a$))
         (list-assignment-rec i a$)))

(defthm list-assignment-rec-update-nth-a$stk
  (implies (and (natp i)
                (integerp j)
                (<= i j)
                (equal stk (nth *a$stki* a$)))
           (equal (list-assignment-rec
                   i
                   (update-nth *a$stki*
                               (update-nth j var stk)
                               a$))
                  (list-assignment-rec i a$))))

(defthm list-assignment-rec-update-nth-a$arr
  (implies (and (varp$ var a$)
                (not (find-var-on-stk var ptr a$)))
           (equal
            (list-assignment-rec ptr
                                 (update-nth *a$arri*
                                             (update-nth var val (nth *a$arri* a$))
                                             a$))
            (list-assignment-rec ptr a$)))
  :hints (("Goal" :in-theory (enable list-assignment-rec))))

(defthm list-assignment-update-nth-a$ptr
  (implies (and (a$p a$)
                (force (varp$ var a$))
                (equal ptr (nth *a$ptr* a$))
                (booleanp val)
                (not (find-var-on-stk var ptr a$)))
           (equal (list-assignment
                   (update-nth *a$ptr*
                               (+ 1 ptr)
                               (update-nth
                                *a$stki*
                                (update-nth ptr
                                            var
                                            (nth *a$stki* a$))
                                (update-nth *a$arri*
                                            (update-nth var
                                                        val
                                                        (nth *a$arri* a$))
                                            a$))))
                  (cons (if val var (negate var))
                        (list-assignment a$))))
  :hints (("Goal" :in-theory (enable list-assignment list-assignment-rec))))

(defun find-lst-on-stk (lst a$)
  (declare (xargs :stobjs a$ :verify-guards nil))
  (cond ((atom lst)
         nil)
        (t (or (find-var-on-stk (abs (car lst)) (a$ptr a$) a$)
               (find-lst-on-stk (cdr lst) a$)))))

(defthm find-var-on-stk-update-stk-past-ptr-better
  (implies (and (integerp j)
                (<= i j)
                (equal stk (nth *a$stki* a$)))
           (equal (find-var-on-stk
                   var i
                   (update-nth *a$stki*
                               (update-nth j lit stk)
                               a$))
                  (find-var-on-stk var i a$))))


(defthm find-lst-on-stk-update
  (implies (and (a$p-weak a$)
                (equal ptr (nth *a$ptr* a$))
                (not (member var lst))
                (not (member (negate var) lst))
                (equal stk (nth *a$stki* a$)))
           (equal (find-lst-on-stk
                   lst
                   (update-nth *a$ptr* (+ 1 ptr)
                               (update-nth *a$stki*
                                           (update-nth ptr var stk)
                                           (update-nth *a$arri*
                                                       (update-nth var
                                                                   val
                                                                   (nth *a$arri* a$))
                                                       a$))))
                  (find-lst-on-stk lst a$)))
  :hints (("Goal" :induct (find-lst-on-stk lst a$))))

(defthm a$-implies-a$-weak
  (implies (a$p a$)
           (a$p-weak a$))
  :hints (("Goal" :in-theory (enable a$p))))

(defthm literal-listp$-update-a$ptr
  (equal (literal-listp$ lst (update-nth *a$ptr* ptr a$))
         (literal-listp$ lst a$))
  :hints (("Goal" :in-theory (enable literal-listp$))))

(defthm literal-listp$-update-a$stk
  (equal (literal-listp$ lst (update-nth *a$stki* stk a$))
         (literal-listp$ lst a$))
  :hints (("Goal" :in-theory (enable literal-listp$))))

(defthm literal-listp$-update-a$arr
  (implies (and (natp i)
                (< i (len (nth *a$arri* a$))))
           (equal (literal-listp$ lst
                                  (update-nth *a$arri*
                                              (update-nth i
                                                          val
                                                          (nth *a$arri* a$))
                                              a$))
                  (literal-listp$ lst a$)))
  :hints (("Goal" :in-theory (enable literal-listp$))))

(defthm a$-implies-array-matches-stack
  (implies (a$p a$)
           (arr-matches-stk (len (nth *a$arri* a$)) a$))
  :hints (("Goal" :in-theory (enable a$p))))

; Working towards proof of verify-clause-equiv.

(defthm negate-clause-equiv-0-lemma
  (implies (and (a$p a$)
                (clausep$ clause a$)
                (not (find-lst-on-stk clause a$)))
           (equal (car (negate-clause clause a$))
                  nil))
  :hints (("Goal"
           :induct (negate-clause clause a$)
           :in-theory (enable negate-clause
                              clausep$
                              literal-listp$
                              push-literal))))

(defthm a$ptr-0-implies-not-find-lst-on-stk
  (implies (equal (a$ptr a$) 0)
           (not (find-lst-on-stk clause a$))))

(defthm negate-clause-equiv-0
  (implies (and (a$p a$)
                (= (a$ptr a$) 0)
                (clausep$ clause a$))
           (equal (car (negate-clause clause a$))
                  nil)))

(defthm negate-clause-nil
  (equal (negate-clause nil a$)
         (mv nil a$))
  :hints (("Goal" :in-theory (enable negate-clause))))

; Start proof of unit-propagation-equiv

; Start proof of is-unit-clause-equiv

; Start proof of member-equal-list-assignment

(defthm booleanp-nth-stk
  (implies (and (a$p a$)
                (force (natp i))
                (< i (nth *a$ptr* a$)))
           (booleanp (nth (nth i (nth *a$stki* a$))
                          (nth *a$arri* a$))))
  :rule-classes :type-prescription)

(defthm member-equal-list-assignment-forward
  (implies (and (a$p a$)
                (literalp$ lit a$)
                (<= ptr (nth *a$ptr* a$)))
           (implies (member-equal lit (list-assignment-rec ptr a$))
                    (equal (nth (abs lit) (nth *a$arri* a$))
                           (equal (abs lit) lit))))
  :rule-classes nil)

(defthm member-equal-list-assignment-reverse-1
  (implies (and (literalp$ lit a$)
                (find-var-on-stk (abs lit) ptr a$)
                (equal (nth (abs lit) (nth *a$arri* a$))
                       (< 0 lit)))
           (member-equal lit (list-assignment-rec ptr a$))))

(defthm member-equal-list-assignment-reverse
  (implies (and (a$p a$)
                (literalp$ lit a$))
           (implies (equal (nth (abs lit) (nth *a$arri* a$))
                           (equal (abs lit) lit))
                    (member-equal lit (list-assignment a$))))
  :hints (("Goal" :in-theory (enable list-assignment)))
  :rule-classes nil)

(defthm member-equal-list-assignment
  (implies (and (a$p a$)
                (literalp$ lit a$))
           (iff (member-equal lit (list-assignment a$))
                (equal (nth (abs lit) (nth *a$arri* a$))
                       (equal (abs lit) lit))))
  :hints (("Goal"
           :in-theory (enable list-assignment)
           :use ((:instance member-equal-list-assignment-forward
                            (ptr (nth *a$ptr* a$)))
                 member-equal-list-assignment-reverse))))

(defthm evaluate-clause-equiv
  (implies (and (a$p a$)
                (clausep$ clause a$))
           (equal (evaluate-clause$ clause a$)
                  (evaluate-clause clause (list-assignment a$))))
  :hints (("Goal" :in-theory (enable evaluate-clause evaluate-clause$))))

(defthm is-unit-clause-equiv
  (implies (and (a$p a$)
                (clausep$ clause a$))
           (equal (is-unit-clause$ clause a$)
                  (is-unit-clause clause (list-assignment a$))))
  :hints (("Goal" :in-theory (enable is-unit-clause$ is-unit-clause))))

(defthm list-assignment-push-unit-literal
  (let ((lit (is-unit-clause clause (list-assignment a$))))
    (implies (and (a$p a$)
                  (clausep$ clause a$)
                  lit
                  (not (equal lit t)))
             (equal (list-assignment
                     (mv-nth
                      1
                      (push-literal lit a$)))
                    (cons lit (list-assignment a$)))))
  :hints (("Goal" :in-theory (enable push-literal))))

(in-theory ; for unit-propagation-equiv
 (disable member-equal-list-assignment))

(defthm literalp$-is-unit-clause
  (implies (and (a$p a$)
                (clausep$ clause a$)
                (is-unit-clause$ clause a$)
                (not (equal (is-unit-clause$ clause a$) t)))
           (literalp$ (is-unit-clause clause (list-assignment a$))
                      a$))
  :hints (("Goal"
           :in-theory (disable literalp$-is-unit-clause$)
           :use literalp$-is-unit-clause$)))

(defthm unit-propagation-equiv
  (implies
   (and (a$p a$)
        (formula-p$ formula a$))
   (and (equal (car (unit-propagation$ formula indices a$))
               (equal (unit-propagation formula
                                        indices
                                        (list-assignment a$))
                      t))
        (implies (not (car (unit-propagation$ formula indices a$)))
                 (equal (list-assignment
                         (mv-nth 1 (unit-propagation$ formula indices a$)))
                        (unit-propagation formula indices
                                          (list-assignment a$))))))
  :hints (("Goal"
           :induct t
           :expand ((unit-propagation$ formula indices a$)
                    (unit-propagation formula indices (list-assignment a$)))
           :in-theory (enable unit-propagation unit-propagation$))))

(defthm list-assignment-base
  (implies (equal (nth *a$ptr* a$) 0)
           (equal (list-assignment a$)
                  nil))
  :hints (("Goal" :in-theory (enable list-assignment))))

; Start proof of negate-clause-equiv-1

(defthm negate-clause-equiv-1-lemma
  (implies (and (a$p a$)
                (clausep$ clause a$)
                (not (intersectp-equal clause (list-assignment a$)))
                (not (intersectp-complementary clause (list-assignment a$))))
           (equal (list-assignment (mv-nth 1 (negate-clause clause a$)))
                  (negate-clause-or-assignment-rec clause
                                                   (list-assignment a$))))
  :hints (("Goal" :in-theory (enable negate-clause push-literal clausep$
                                     member-equal-list-assignment literalp$))))

(defthm negate-clause-equiv-1
  (implies (and (a$p a$)
                (= (a$ptr a$) 0)
                (clausep$ clause a$))
           (equal (list-assignment (mv-nth 1 (negate-clause clause a$)))
                  (negate-clause-or-assignment clause)))
  :hints (("Goal" :in-theory (enable negate-clause-or-assignment))))

; Start proof of ratp1-equiv

(defthm rat-assignment-equiv-no-error
  (implies (and (a$p a$)
                (literalp$ nlit a$)
                (clausep$ clause a$)
                (null (car (rat-assignment$ a$ nlit clause))))
           (and (not (equal (rat-assignment$ (list-assignment a$)
                                             nlit
                                             clause)
                            t))
                (equal (list-assignment
                        (mv-nth 1 (rat-assignment$ a$ nlit clause)))
                       (rat-assignment
                        (list-assignment a$) nlit clause))))
  :hints (("Goal" :in-theory (enable rat-assignment$
                                     rat-assignment
                                     push-literal
                                     member-equal-list-assignment
                                     clausep$
                                     ))))

(defthm rat-assignment-equiv-error
  (implies (and (a$p a$)
                (literalp$ nlit a$)
                (clausep$ clause a$))
           (equal (car (rat-assignment$ a$ nlit clause))
                  (equal (rat-assignment
                          (list-assignment a$) nlit clause)
                         t)))
  :hints (("Goal" :in-theory (enable rat-assignment$
                                     rat-assignment
                                     push-literal
                                     member-equal-list-assignment
                                     clausep$
                                     ))))

(defthm a$=-pop-literals-mv-nth-1-rat-assignment$
  (implies (and (a$p a$)
                (clausep$ clause a$))
           (a$= (pop-literals (nth *a$ptr* a$)
                              (mv-nth 1
                                      (rat-assignment$ a$ nlit clause)))
                a$))
  :hints (("Goal" :in-theory (enable pop-literals rat-assignment$))))

(defthm a$=-pop-literals-mv-nth-1-unit-propagation$
  (implies (and (a$p a$)
                (formula-p$ formula a$))
           (a$= (pop-literals (nth *a$ptr* a$)
                              (mv-nth 1
                                      (unit-propagation$ formula indices a$)))
                a$))
  :hints (("Goal" :in-theory (enable pop-literals unit-propagation$))))

(defthm lst=-implies-nth-equal
  (implies (and (lst= ptr x y)
                (integerp ptr)
                (natp i)
                (< i ptr))
           (equal (nth i x)
                  (nth i y))))

(defthm a$=-implies-equal-list-assignment-rec
  (implies (and (a$= a$1 a$2)
                (<= ptr (nth *a$ptr* a$1)))
           (equal (list-assignment-rec ptr a$1) (list-assignment-rec ptr a$2)))
  :hints (("Goal" :in-theory (enable a$=)))
  :rule-classes nil)

(defthm a$=-implies-equal-list-assignment-1
  (implies (a$= a$1 a$2)
           (equal (list-assignment a$1) (list-assignment a$2)))
  :hints (("Goal"
           :in-theory (enable a$= list-assignment)
           :use ((:instance a$=-implies-equal-list-assignment-rec
                            (ptr (nth *a$ptr* a$1))))))
  :rule-classes (:congruence))

(defthm ratp1-equiv
  (implies (and (a$p a$)
                (formula-p$ alist a$)
                (formula-p$ formula a$)
                (literalp$ nlit a$)
                (drat-hint-listp drat-hints))
           (and (equal (car (RATp1$ alist formula nlit drat-hints a$))
                       (RATp1 alist formula nlit drat-hints
                              (list-assignment a$)))
                (a$= (mv-nth 1 (RATp1$ alist formula nlit drat-hints a$))
                     a$)))
  :hints (("Goal"
           :induct (ratp1$ alist formula nlit drat-hints a$)
           :expand ((ratp1$ alist formula nlit drat-hints a$)
                    (ratp1 alist formula
                           nlit drat-hints (list-assignment a$)))
           :in-theory (enable ratp1$ ratp1 formula-p$))))

(defthm verify-clause-equiv
  (implies (force (and (a$p a$)
                       (formula-p$ formula a$)
                       (equal (nth *a$ptr* a$) 0)
                       (integerp ncls)
                       (natp ndel)
                       (not (equal (car add-step) t))
                       (add-step-p add-step)
                       (clausep$ (access add-step add-step :clause) a$)))
           (and (equal (car (verify-clause$ formula add-step ncls ndel a$))
                       (car (verify-clause formula add-step ncls ndel)))
                (equal (mv-nth 1 (verify-clause$ formula add-step ncls ndel a$))
                       (mv-nth 1 (verify-clause formula add-step ncls ndel)))
                (equal (mv-nth 2 (verify-clause$ formula add-step ncls ndel a$))
                       (mv-nth 2 (verify-clause formula add-step ncls ndel)))
                (a$= (mv-nth 3 (verify-clause$ formula add-step ncls ndel a$))
                     a$)))
  :hints (("Goal" :in-theory (enable verify-clause verify-clause$))))

(defthm formula-p$-add-proof-clause
  (implies (force (and (a$p a$)
                       (posp index)
                       (clausep$ clause a$)
                       (formula-p$ formula a$)))
           (formula-p$ (add-proof-clause index clause formula)
                       a$))
  :hints (("Goal" :in-theory (union-theories '(formula-p$ add-proof-clause)
                                             (current-theory :here)))))
(defthm a$p-mv-nth-3-verify-clause$
  (implies (and (a$p a$)
                (formula-p$ formula a$)
                (clausep$ (access add-step add-step :clause) a$))
           (a$p (mv-nth 3 (verify-clause$ formula add-step ncls ndel a$))))
  :hints (("Goal" :in-theory (enable verify-clause$))))

(defthm integerp-car-verify-clause
  (implies (force (integerp ncls))
           (or (integerp (car (verify-clause formula add-step ncls ndel)))
               (equal (car (verify-clause formula add-step ncls ndel))
                      nil)))
  :hints (("Goal" :in-theory (enable verify-clause)))
  :rule-classes :type-prescription)

(defthm natp-mv-nth-1-verify-clause
  (implies (force (natp ndel))
           (or (natp (mv-nth 1 (verify-clause formula add-step ncls ndel)))
               (equal (mv-nth 1 (verify-clause formula add-step ncls ndel))
                      nil)))
  :hints (("Goal" :in-theory (enable verify-clause)))
  :rule-classes :type-prescription)

(defthm natp-mv-nth-1-verify-clause-extra
  (implies (and (natp ndel)
                (car (verify-clause formula add-step ncls ndel)))
           (natp (mv-nth 1 (verify-clause formula add-step ncls ndel))))
  :hints (("Goal" :in-theory (enable verify-clause)))
  :rule-classes :type-prescription)

(in-theory (enable add-step-p))

(defthm a$ptr-0-for-verify-clause$
  (implies (and (a$p a$)
                (equal (nth *a$ptr* a$) 0)
                (formula-p$ formula a$)
                (clausep$ (access add-step add-step :clause) a$)
                (car (verify-clause$ formula add-step ncls ndel a$)))
           (equal (nth *a$ptr*
                       (mv-nth 3 (verify-clause$ formula add-step ncls ndel a$)))
                  0))
  :hints (("Goal" :in-theory (enable verify-clause$))))

(defthm formula-p$-for-verify-clause$
  (implies (and (a$p a$)
                (formula-p$ formula a$)
                (clausep$ (access add-step add-step :clause) a$)
                (car (verify-clause formula add-step ncls ndel)))
           (formula-p$ (mv-nth 2
                               (verify-clause formula add-step ncls ndel))
                       (mv-nth 3
                               (verify-clause$ formula add-step ncls ndel
                                               a$))))
  :hints (("Goal" :in-theory (enable verify-clause verify-clause$))))

(defthm verify-proof-equiv
  (implies (and (formula-p$ formula a$)
                (proofp$ proof a$)
                (a$p a$)
                (equal (nth *a$ptr* a$) 0)
                (integerp ncls)
                (natp ndel))
           (and (equal (car (verify-proof$-rec ncls ndel formula proof a$))
                       (verify-proof-rec ncls ndel formula proof))
                (a$= (mv-nth 1 (verify-proof$-rec ncls ndel formula proof a$))
                     a$)))
  :hints (("Goal"
           :induct (verify-proof$-rec ncls ndel formula proof a$)
           :in-theory (enable verify-proof-rec verify-proof$-rec))))

(defthm equiv-main
  (implies (and (formula-p formula)
                (proofp proof)
                (< 0
                   (proof-max-var proof (formula-max-var formula 0)))
                (car (verify-proof$-rec
                      (len (fast-alist-fork formula nil))
                      0 formula proof
                      (initialize-a$
                       (proof-max-var proof (formula-max-var formula 0))
                       '(0 (nil) (0)))))
                (proof-contradiction-p proof))
           (verify-proof-rec (len (fast-alist-fork formula nil))
                             0 formula proof))
  :hints (("Goal"
           :restrict
           ((verify-proof-equiv
             ((a$ (initialize-a$
                   (proof-max-var proof (formula-max-var formula 0))
                   '(0 (nil) (0))))))))))

(defthm refutation-p-equiv
  (implies (and (formula-p formula)
                (refutation-p$ proof formula))
           (refutation-p proof formula))
  :hints (("Goal" :in-theory (enable verify-proof verify-proof$))))
