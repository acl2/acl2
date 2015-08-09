; UBDD Library
; Copyright (C) 2008-2011 Warren Hunt and Bob Boyer
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Significantly revised in 2008 by Jared Davis and Sol Swords.
; Now maintained by Centaur Technology.
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/

; deps.lisp - tracking variable dependencies of BDDs

(in-package "ACL2")
(include-book "extra-operations")


;; UBDD-DEPS: Produce a list of Ts and NILs indicating which variables the input
;; BDD depends on.

(defn or-lists (x y)
  (if (atom x)
      y
    (if (atom y) x
      (cons (or (car x) (car y))
            (or-lists (cdr x) (cdr y))))))

(defthm nth-of-or-lists
  (equal (nth n (or-lists x y))
         (or (nth n x) (nth n y))))

(in-theory (disable or-lists))


(defn ubdd-deps (x)
  (if (atom x)
      nil
    (cons (not (hons-equal (car x) (cdr x)))
          (or-lists (ubdd-deps (car x)) (ubdd-deps (cdr x))))))

(memoize 'ubdd-deps :condition '(consp x))

(in-theory (disable ubdd-deps))

(local (defun eval-ubdd-deps-ind (x n env)
         (if (atom x)
             (list n env)
           (if (car env)
               (eval-ubdd-deps-ind (car x) (1- n) (cdr env))
             (eval-ubdd-deps-ind (cdr x) (1- n) (cdr env))))))

(defthm eval-bdd-of-update-when-not-dependent
  (implies (not (nth n (ubdd-deps x)))
           (equal (eval-bdd x (update-nth n v env))
                  (eval-bdd x env)))
  :hints (("goal" :induct (eval-ubdd-deps-ind x n env)
           :in-theory (enable (:i eval-bdd))
           :expand ((:free (env) (eval-bdd x env))
                    (ubdd-deps x)
                    (:free (a b) (nth n (cons a b)))))))

(local (defun bdd-deps-ind (x n)
         (if (zp n)
             x
           (list (bdd-deps-ind (car x) (1- n))
                 (bdd-deps-ind (cdr x) (1- n))))))

(local (defun 2bdd-deps-ind (x y n)
         (if (zp n)
             (list x y)
           (list (2bdd-deps-ind (car x) (car y) (1- n))
                 (2bdd-deps-ind (cdr x) (cdr y) (1- n))))))

(local (defun q-ite-deps-ind (x y z n)
         (declare (xargs :measure (nfix n)))
         (if (zp n)
             (list x y z)
           (list (q-ite-deps-ind (car x)
                                 (if (hons-equal x y) t (qcar y))
                                 (if (hons-equal x z) nil (qcar z))
                                 (1- n))
                 (q-ite-deps-ind (cdr x)
                                 (if (hons-equal x y) t (qcdr y))
                                 (if (hons-equal x z) nil (qcdr z))
                                 (1- n))))))


(local (in-theory (disable equal-of-booleans-rewrite)))

(local (defthm nth-ubdd-deps-of-qcons
         (equal (nth n (ubdd-deps (qcons x y)))
                (if (zp n)
                    (not (equal x y))
                  (nth (1- n) (or-lists (ubdd-deps x) (ubdd-deps y)))))
         :hints(("Goal" :in-theory (enable ubdd-deps)))))

(local (defthm nth-ubdd-deps-of-cons
         (equal (nth n (ubdd-deps (cons x y)))
                (if (zp n)
                    (not (equal x y))
                  (nth (1- n) (or-lists (ubdd-deps x) (ubdd-deps y)))))
         :hints(("Goal" :in-theory (enable ubdd-deps)))))

(local (defthm nth-of-ubdd-deps-when-zp
         (implies (and (syntaxp (symbolp x))
                       (zp n))
                  (equal (nth n (ubdd-deps x))
                         (not (equal (car x) (cdr x)))))
         :hints(("Goal" :in-theory (enable ubdd-deps)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (defthm nth-of-ubdd-deps-when-not-zp
         (implies (and (syntaxp (symbolp x))
                       (not (zp n)))
                  (equal (nth n (ubdd-deps x))
                         (nth (1- n) (or-lists
                                      (ubdd-deps (car x))
                                      (ubdd-deps (cdr x))))))
         :hints(("Goal" :in-theory (enable ubdd-deps)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))


(local (in-theory (disable qcons nth)))

(local (defthm nth-of-nil
         (not (nth n nil))
         :hints(("Goal" :in-theory (enable nth)))))

(local (defthm or-lists-identical
         (equal (or-lists x x)
                x)
         :hints(("Goal" :in-theory (enable or-lists)))))

(defthm ubdd-deps-of-qv
  (equal (ubdd-deps (qv n))
         (update-nth n t nil))
  :hints(("Goal" :in-theory (enable (:i qv))
          :induct (qv n)
          :expand ((qv n)
                   (:free (x y) (ubdd-deps (cons x y)))))))

;; BOZO may also prove that if (nth n (ubdd-deps x)) and (ubddp x), then there
;; exists some env, v under which
;; (eval-bdd x env) != (eval-bdd x (update-nth n v env)).

;; Stronger theorems may be proved provided X is ubddp.  At the moment I'll
;; just prove simple conservative stuff.

(defthm q-not-no-new-deps
  (implies (not (nth n (ubdd-deps x)))
           (not (nth n (ubdd-deps (q-not x)))))
  :hints (("goal" :induct (bdd-deps-ind x n))))


(defthm q-and-no-new-deps
  (implies (and (not (nth n (ubdd-deps x)))
                (not (nth n (ubdd-deps y))))
           (not (nth n (ubdd-deps (q-binary-and x y)))))
  :hints (("goal" :induct (2bdd-deps-ind x y n)
           :in-theory (disable (force))
           :expand ((q-binary-and x y)))))

(defthm q-or-no-new-deps
  (implies (and (not (nth n (ubdd-deps x)))
                (not (nth n (ubdd-deps y))))
           (not (nth n (ubdd-deps (q-binary-or x y)))))
  :hints (("goal" :induct (2bdd-deps-ind x y n)
           :in-theory (disable (force))
           :expand ((q-binary-or x y)))))


(defthm q-xor-no-new-deps
  (implies (and (not (nth n (ubdd-deps x)))
                (not (nth n (ubdd-deps y))))
           (not (nth n (ubdd-deps (q-binary-xor x y)))))
  :hints (("goal" :induct (2bdd-deps-ind x y n)
           :in-theory (disable (force))
           :expand ((q-binary-xor x y)))))

(defthm q-iff-no-new-deps
  (implies (and (not (nth n (ubdd-deps x)))
                (not (nth n (ubdd-deps y))))
           (not (nth n (ubdd-deps (q-binary-iff x y)))))
  :hints (("goal" :induct (2bdd-deps-ind x y n)
           :in-theory (disable (force))
           :expand ((q-binary-iff x y)))))

(defthm ubdd-deps-of-atom
  (implies (not (consp x))
           (equal (ubdd-deps x) nil))
  :hints(("Goal" :in-theory (enable ubdd-deps)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

; Added by Matt K., 9/28/2013, to get around ACL2(hp) error such as:
;   Error:  Not owner of hash table #<HASH-TABLE :TEST EQL size 3/62 #x30200BB9920D>
; David Rager points out (email, 9/28/2013) that "memoization is known
; not to be thread-safe"; Jared Davis says this too.  (Perhaps this will be
; addressed in the future.)
(local (unmemoize 'ubdd-deps))

(defthm q-ite-no-new-deps
  (implies (and (not (nth n (ubdd-deps x)))
                (not (nth n (ubdd-deps y)))
                (not (nth n (ubdd-deps z))))
           (not (nth n (ubdd-deps (q-ite-fn x y z)))))
  :hints (("goal" :induct (q-ite-deps-ind x y z n)
           :in-theory (disable (force))
           :expand ((q-ite-fn x y z)
                    (:free (a b) (nth n (cons a b)))))))


