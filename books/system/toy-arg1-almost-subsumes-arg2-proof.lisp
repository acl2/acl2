; Copyright (C) 2026, J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; Toy Version of the Claim in arg1-almost-subsumes-arg2

; This file is an exercise to convince ourselves that we have identified
; sufficient conditions to establish that arg1-almost-subsumes-arg2 properly
; detects subsumption.  See that function for an informal argument.  In this
; file we define a toy version of arg1-almost-subsumes-arg2 dealing only with
; propositional clauses and not dealing with ``extra-info'' literals.  We call
; that function s below.

; A literal is either a symbol or the negation of a symbol, where the
; ``negation of symbol'' s is (NOT s).

(defun litp (x)
  (or (symbolp x)
      (and (consp x)
           (eq (car x) 'NOT)
           (consp (cdr x))
           (symbolp (cadr x))
           (null (cddr x)))))

(defun neg-lit (lit)
  (if (eq (car lit) 'NOT) (cadr lit) (list 'NOT lit)))

(defthm litp-neg-lit
  (implies (litp x)
           (litp (neg-lit x))))

(defthm neg-lit-neg-lit
  (implies (litp x)
           (equal (neg-lit (neg-lit x)) x)))

(in-theory (disable litp neg-lit))

; A clause is a true-list of litps.

(defun clausep (c)
  (cond
   ((atom c) (equal c nil))
   (t (and (litp (car c))
           (clausep (cdr c))))))

(defun tautp-cl (c)
  (cond ((endp c) nil)
        ((member (neg-lit (car c)) (cdr c)) t)
        (t (tautp-cl (cdr c)))))

; We next define simplified versions of complementaryp and
; member-equal-+-.  

(defun compp (lit1 lit2)
  (equal (neg-lit lit1) lit2))

; Here we prove that our compp is equivalent to ACL2's complementaryp

(defthm compp-is-complementaryp
  (implies (and (litp lit1)
                (litp lit2))
           (equal (compp lit1 lit2)
                  (or (and (eq (car lit1) 'not) ; complementaryp in ACL2
                           (eq (cadr lit1) lit2))
                      (and (eq (car lit2) 'not)
                           (eq (cadr lit2) lit1)))))
     :hints (("Goal" :in-theory (enable litp neg-lit)))
     :rule-classes nil)

(defthm compp-commutative
  (implies (and (litp lit1)
                (litp lit2))
           (equal (compp lit1 lit2)
                  (compp lit2 lit1))))

; Now we define the simplified member-equal-+-.

(defun memb-+/- (lit c)
  (cond ((endp c) nil)
        ((equal lit (car c)) '+)
        ((compp lit (car c)) '-)
        (t (memb-+/- lit (cdr c)))))

; The following function is a simplified version of arg1-almost-subsumes-arg2
; in which clauses are entirely propositional as defined above and there are no
; ``extra-info'' literals.

(defun a1-almost-subsumes-a2 (arg1 arg2)
  (cond ((endp arg1) 'subsumed)
        (t (let ((sign (memb-+/- (car arg1) arg2)))
             (cond
              ((null sign) nil)
              ((eq sign '+)
               (a1-almost-subsumes-a2 (cdr arg1) arg2))
              ((subsetp-equal (cdr arg1) arg2)
               arg1)
              (t nil))))))

(defthm when-a1-almost-subsumes-a2-returns-subsumed
  (implies (and (clausep arg1)
                (clausep arg2)
                (not (tautp-cl arg1))
                (eq (a1-almost-subsumes-a2 arg1 arg2) 'subsumed))
           (subsetp-equal arg1 arg2)))

(defthm when-a1-almost-subsumes-a2-returns-consp-fact1
  (implies (and (clausep arg1)
                (clausep arg2)
                (not (tautp-cl arg1))
                (consp (a1-almost-subsumes-a2 arg1 arg2)))
           (member (car (a1-almost-subsumes-a2 arg1 arg2)) arg1)))

(defthm when-a1-almost-subsumes-a2-returns-consp-fact2-lemma1
  (IMPLIES (AND (litp lit)
                (MEMB-+/- lit ARG2)
                (NOT (EQUAL (MEMB-+/- lit ARG2) '+)))
           (MEMBER-EQUAL (NEG-LIT lit)
                         ARG2)))

(defthm when-a1-almost-subsumes-a2-returns-consp-fact2
  (implies (and (clausep arg1)
                (clausep arg2)
                (not (tautp-cl arg1))
                (consp (a1-almost-subsumes-a2 arg1 arg2)))
           (member (neg-lit (car (a1-almost-subsumes-a2 arg1 arg2))) arg2)))

; Let'd define the resolvent of two clauses on a lit in the first whose
; negation appears in the second.

(defun resolvent (lit c1 c2)
  (union-equal (remove1-equal lit c1)
               (remove1-equal (neg-lit lit) c2)))

; Ok
(defthm subsetp-equal-union-equal-lemma1
  (IMPLIES (SUBSETP-EQUAL A C)
           (EQUAL (SUBSETP-EQUAL (UNION-EQUAL A B) C)
                  (SUBSETP-EQUAL B C))))

(defthm subsetp-equal-union-equal-lemma2
  (IMPLIES (AND (SUBSETP-EQUAL (UNION-EQUAL a B) C)
                (MEMBER-EQUAL e B))
           (MEMBER-EQUAL e C)))

(defthm subsetp-equal-union-equal-lemma3
  (IMPLIES (SUBSETP-EQUAL (UNION-EQUAL A B) C)
           (SUBSETP-EQUAL A C)))

(defthm subsetp-equal-union-equal
  (equal (subsetp-equal (union-equal a b) c)
         (and (subsetp-equal a c)
              (subsetp-equal b c))))

(defthm subsetp-equal-cons
  (implies (subsetp-equal a b)
           (subsetp-equal a (cons e b))))

(defthm subsetp-equal-reflexive
  (subsetp-equal a a))

(defthm subsetp-equal-cdr
  (subsetp-equal (cdr a) a))

(defthm subsetp-equal-remove1-equal
  (subsetp-equal (remove1-equal e a) a))

; The crux of the argument: if (a1-almost-subsumes-a2 arg1 arg2) returns (lit ...), then
; every element of arg1 up to lit occurs in arg2.

(defun lits-preceding (lit cl)
  (cond ((endp cl) nil)
        ((equal lit (car cl)) nil)
        (t (cons (car cl) (lits-preceding lit (cdr cl))))))

(defthm when-a1-almost-subsumes-a2-returns-cons-fact3-lemma1
  (IMPLIES (EQUAL (MEMB-+/- lit ARG2) '+)
           (MEMBER-EQUAL lit ARG2)))

(defthm when-a1-almost-subsumes-a2-returns-consp-fact3
  (implies (and (clausep arg1)
                (clausep arg2)
                (not (tautp-cl arg1))
                (consp (a1-almost-subsumes-a2 arg1 arg2)))
           (subsetp-equal (lits-preceding
                           (car (a1-almost-subsumes-a2 arg1 arg2))
                           arg1)
                          arg2)))

(defthm when-a1-almost-subsumes-a2-returns-consp-fact4
  (implies (and (clausep arg1)
                (clausep arg2)
                (not (tautp-cl arg1))
                (consp (a1-almost-subsumes-a2 arg1 arg2)))
           (subsetp-equal (cdr (a1-almost-subsumes-a2 arg1 arg2)) arg2)))

(defthm remove1-equal-is-append-lits-preceding-and-rest
  (implies (member-equal lit arg1)
           (equal (remove1-equal lit arg1)
                  (append (lits-preceding lit arg1)
                          (cdr (member-equal lit arg1))))))

(in-theory (disable remove1-equal-is-append-lits-preceding-and-rest))

(defthm when-a1-almost-subsumes-a2-returns-consp-fact5
  (implies (and (clausep arg1)
                (clausep arg2)
                (not (tautp-cl arg1))
                (no-duplicatesp arg1)
                (consp (a1-almost-subsumes-a2 arg1 arg2)))
           (equal (CDR (MEMBER-EQUAL (CAR (a1-almost-subsumes-a2 ARG1 ARG2)) ARG1))
                  (cdr (a1-almost-subsumes-a2 arg1 arg2)))))

(defthm when-a1-almost-subsumes-a2-returns-consp-resolvent-subsumes
  (implies (and (clausep arg1)
                (clausep arg2)
                (not (tautp-cl arg1))
                (no-duplicatesp arg1)
                (consp (a1-almost-subsumes-a2 arg1 arg2)))
           (subsetp-equal (resolvent
                           (car (a1-almost-subsumes-a2 arg1 arg2))
                           arg1 arg2)
                          arg2))
  :hints (("Goal'" :in-theory (enable remove1-equal-is-append-lits-preceding-and-rest))))





