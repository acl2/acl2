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

; param.lisp -- bdd parameterization

(in-package "ACL2")

(include-book "extra-operations")
(include-book "misc/hons-help2" :dir :system)
(include-book "tools/rulesets" :dir :system)
(local (include-book "std/lists/take" :dir :system))

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable* default-car default-cdr ;; blp-implies-t
                            default-+-2 default-+-1 default-<-2 default-<-1
                            (:ruleset canonicalize-to-q-ite)
                            equal-by-eval-bdds
                            )))

(local (in-theory (enable eval-bdd eval-bdd-list ubddp ubdd-listp
                          q-compose q-compose-list)))

;; -------------------------------------------------------------------
;; Function Definitions
;; -------------------------------------------------------------------

;; find-diff: given two different BDDs, finds a variable assignment
;; that makes their evaulations unequal.
(defn find-diff (a b)
  (declare (xargs :measure (+ (acl2-count a) (acl2-count b))))
  (if (and (atom a) (atom b))
      nil
    (if (hqual (qcdr a) (qcdr b))
        (cons t (find-diff (qcar a) (qcar b)))
      (cons nil (find-diff (qcdr a) (qcdr b))))))

(defn find-diff-of-length (a b n)
  (declare (xargs :measure (nfix n)))
  (if (zp (nfix n))
      nil
    (if (and (atom a) (atom b))
        (cons nil (find-diff-of-length a b (1- n)))
      (if (hqual (qcdr a) (qcdr b))
          (cons t (find-diff-of-length (qcar a) (qcar b) (1- n)))
        (cons nil (find-diff-of-length (qcdr a) (qcdr b) (1- n)))))))

; Regarless of whether
;  x = f(a,b,c),  l = g(p,q), h(p,q), i(p,q),
;  q-compose(f(a,b,c), (g(p,q), h(p,q), i(p,q)) )
;  = f(g(p,q),h(p,q),i(p,q))

(defun head-tail-bind-fn (bindings body)
  (if (atom bindings)
      body
    (let ((b (car bindings)))
    `(mv-let (,(car b) ,(cadr b))
       (if (consp ,(caddr b))
           (mv (car ,(caddr b)) (cdr ,(caddr b)))
         (mv nil nil))
       (declare (ignorable ,(car b) ,(cadr b)))
       ,(head-tail-bind-fn (cdr bindings) body)))))

(defmacro head-tail-bind (bindings body)
  (head-tail-bind-fn bindings body))

;; Makes a list each element of which is (q-ite x yi zi), where yi and
;; zi are the corresponding elements in lists ys and zs.
(defn q-ite-list (x ys zs)
  (declare (xargs :measure (+ (acl2-count ys)
                              (acl2-count zs))))
  (if (and (atom ys) (atom zs))
      nil
    (head-tail-bind
     ((z1 zr zs)
      (y1 yr ys))
     (cons (q-ite x y1 z1)
           (q-ite-list x yr zr)))))


;; QCONSes together corresponding elements of lists L1 and L2.
(defn q-zipper (l1 l2)
  (declare (xargs :measure (+ (len l1) (len l2))))
  (if (and (atom l1) (atom l2))
      nil
    (head-tail-bind
     ((l11 l1r l1)
      (l21 l2r l2))
     (cons (qcons l11 l21)
           (q-zipper l1r l2r)))))

(in-theory (disable q-zipper))

;; Makes a list of N bdd variables starting at START and increasing by
;; BY at each step.
(defn qv-list (start by n)
  (declare (xargs :measure (nfix n)))
  (if (zp (nfix n))
      nil
    (cons (qv (nfix start))
          (qv-list (ec-call (binary-+ by start)) by (1- n)))))

;; Fixes each element in list L to a Boolean.
(defn bfix-list (l)
  (if (atom l)
      nil
    (cons (if (car l) t nil)
          (bfix-list (cdr l)))))


;; Given a BDD X representing some predicate of n variables, makes a
;; list of n BDDs for which 1) any evaluation of the n outputs under
;; the same variable assignment produces a variable assignment that
;; satisfies X, and 2) any variable assignment that satisfies X can be
;; produced by the n BDDs.
;; More precisely, NVARS is the number of variables "used" by X; for
;; 1) above to hold it should be at least (max-depth x) but it can be
;; more.  2) only holds for variable assignments of length NVARS.
(defn q-param (x nvars)
  (cond ((zp (nfix nvars)) nil)
        ((atom x) (qv-list 0 1 nvars))
        ((not (car x))
         (cons nil (q-param (cdr x) (1- nvars))))
        ((not (cdr x))
         (cons t   (q-param (car x) (1- nvars))))
        (t (cons (qv 0)
                 (q-zipper
                  (q-param (car x) (1- nvars))
                  (q-param (cdr x) (1- nvars)))))))



;; Given a BDD X, find an "inverse" for q-param
(defn q-param-inv (x nvars)
  (cond ((zp (nfix nvars)) nil)
        ((atom x) (qv-list 0 1 nvars))
        ((not (car x))
         (let ((x (q-param-inv (cdr x) (1- nvars))))
           (q-zipper x x)))
        ((not (cdr x))
         (let ((x (q-param-inv (car x) (1- nvars))))
           (q-zipper x x)))
        (t (cons (qv 0)
                 (q-zipper (q-param-inv (car x) (1- nvars))
                           (q-param-inv (cdr x) (1- nvars)))))))


(defn max-max-depth (x)
  (if (atom x)
      0
    (max (max-depth (car x))
         (max-max-depth (cdr x)))))


(defn extend-list (a b)
  (declare (xargs :measure (+ (len a) (len b))))
  (if (and (atom a) (atom b))
      a
    (head-tail-bind
     ((a1 ar a)
      (b1 br b))
     (cons a1 (extend-list ar br)))))


(defun ebmde-ind (x l l2)
  (if (atom x)
      (list l l2)
    (list (ebmde-ind (car x) (cdr l) (cdr l2))
          (ebmde-ind (cdr x) (cdr l) (cdr l2)))))

(defthm eval-bdd-max-depth-extend
  (implies (<= (max-depth x) (len l))
           (equal (eval-bdd x (extend-list l l2))
                  (eval-bdd x l)))
  :hints (("goal" :induct (ebmde-ind x l l2)
           :in-theory (e/d (default-car default-cdr max-depth)
                           ()))))


(defthm eval-bdd-list-max-max-depth-extend
  (implies (<= (max-max-depth x) (len l))
           (equal (eval-bdd-list x (extend-list l l2))
                  (eval-bdd-list x l)))
  :hints (("goal" :in-theory (disable ))))


(defthm len-eval-bdd-list
  (equal (len (eval-bdd-list x l))
         (len x)))


;; UBDDP forward-chaining rules
(defthm ubddp-cons-forward-chain
  (implies (and (ubddp x) (consp x))
           (and (ubddp (car x)) (ubddp (cdr x))))
  :rule-classes :forward-chaining)

(defthm ubddp-atom-forward-chain
  (implies (and (ubddp x) (not (consp x)))
           (or (equal x nil) (equal x t)))
  :rule-classes :forward-chaining)

;; -------------------------------------------------------------------

(defthm car-nthcdr
  (equal (car (nthcdr n l))
         (nth n l)))

(defthm nth-implies-consp-nthcdr
  (implies (nth n l)
           (consp (nthcdr n l))))

(defthm cdr-nthcdr
  (equal (nthcdr n (cdr l))
         (cdr (nthcdr n l))))

;; FIND-DIFF always produces a variable assignment which
;; differentiates two BDDs, if they are different:
(defthm eval-bdd-diff
  (implies (and (ubddp a)
                (ubddp b)
                (not (equal a b)))
           (not (equal (eval-bdd a (find-diff a b))
                       (eval-bdd b (find-diff a b)))))
  :hints (("Goal" :induct (find-diff a b))))

;; FIND-DIFF-OF-LENGTH always produces a variable assignment which
;; differentiates two BDDs, if they are different:
(defthm eval-bdd-diff-of-length
  (implies (and (ubddp a)
                (ubddp b)
                (not (equal a b))
                (<= (max-depth a) (nfix n))
                (<= (max-depth b) (nfix n)))
           (not (equal (eval-bdd a (find-diff-of-length a b n))
                       (eval-bdd b (find-diff-of-length a b n)))))
  :hints (("goal" :in-theory (enable max-depth))))

(defthm find-diff-of-length-len
  (equal (len (find-diff-of-length a b n))
         (nfix n)))

;; This is an indirect (but easier than a direct, inductive proof) way
;; of proving identities about BDD operations.  To prove a generic
;; equation of two expressions that produce BDDs, we prove that the
;; eval-bdds of the two expressions are equal under all variable
;; assignments, then use eval-bdd-diff (above) to show that the
;; expressions themselves are equal.
;; (defthm eval-bdd-q-ite-of-q-ite
;;   (implies (and (ubddp a)
;;                 (ubddp b) (ubddp c)
;;                 (ubddp d) (ubddp e))
;;            (equal (eval-bdd (q-ite (q-ite a b c) d e) vals)
;;                   (eval-bdd (q-ite a
;;                                    (q-ite b d e)
;;                                    (q-ite c d e))
;;                             vals))))

;; (defthm q-ite-of-q-ite
;;   (implies (and (ubddp a)
;;                 (ubddp b) (ubddp c)
;;                 (ubddp d) (ubddp e))
;;            (equal (q-ite (q-ite a b c) d e)
;;                   (q-ite a
;;                          (q-ite b d e)
;;                          (q-ite c d e)))))



(defthm q-and-equals-t
  (implies (equal (q-and x y) t)
           (and (implies (ubddp x) (equal x t))
                (implies (ubddp y) (equal y t))))
  :hints (("goal" :in-theory (enable q-and)))
  :rule-classes :forward-chaining)

(defthmd ubddp-q-not-t-implies-not
  (implies (and (ubddp x)
                x)
           (not (equal (q-not x) t)))
  :hints (("goal" :in-theory (enable q-not))))

(defthmd ubddp-q-not-nil-implies-t
  (implies (and (ubddp x)
                (not (q-not x)))
           (equal (equal x t) t))
  :hints (("goal" :in-theory (enable q-not))))

(defthm ubdd-listp-q-ite-list
  (implies (and (ubddp x) (ubdd-listp ys) (ubdd-listp zs))
           (ubdd-listp (q-ite-list x ys zs)))
  :hints (("goal" :induct (q-ite-list x ys zs))))

;; (defthm q-compose-ubddp
;;   (implies (and (ubddp x) (ubdd-listp l))
;;            (ubddp (q-compose x l))))

;; Show that Q-COMPOSE really performs function composition.
(defthm q-compose-to-eval-bdd
  (implies (and (ubddp x) (ubdd-listp l))
           (equal (eval-bdd (q-compose x l) vals)
                  (eval-bdd x (eval-bdd-list l vals)))))

; (add-bdd-fn-pat q-compose)

(defthm q-ite-list-correct
  (implies (and (ubddp x) (ubdd-listp ys) (ubdd-listp zs)
                (equal (len ys) (len zs)))
           (equal (eval-bdd-list (q-ite-list x ys zs) vals)
                  (if (eval-bdd x vals)
                      (eval-bdd-list ys vals)
                    (eval-bdd-list zs vals)))))

;; (if a (f b) (f c)) == (f (if a b c))
(defthm eval-bdd-q-compose-commutes-with-q-ite
  (implies (and (ubddp x) (ubddp y)
                (ubdd-listp l1) (ubdd-listp l2)
                (equal (len l1) (len l2)))
           (equal (eval-bdd (q-ite x
                                   (q-compose y l1)
                                   (q-compose y l2))
                            vals)
                  (eval-bdd (q-compose y (q-ite-list x l1 l2))
                            vals)))
  :hints (("goal" :in-theory (disable q-compose))))

(defthm q-compose-commutes-with-q-ite
  (implies (and (ubddp x) (ubddp y)
                (ubdd-listp l1) (ubdd-listp l2)
                (equal (len l1) (len l2)))
           (equal (q-ite x
                         (q-compose y l1)
                         (q-compose y l2))
                  (q-compose y (q-ite-list x l1 l2))))
  :hints(("Goal" :in-theory (enable equal-by-eval-bdds))))

;; (defthm ubdd-listp-q-compose-list
;;   (implies (and (ubdd-listp ys) (ubdd-listp zs))
;;            (ubdd-listp (q-compose-list ys zs))))

(defthm q-compose-list-correct
  (implies (and (ubdd-listp ys) (ubdd-listp zs))
           (equal (eval-bdd-list (q-compose-list ys zs) vals)
                  (eval-bdd-list ys (eval-bdd-list zs vals)))))


(defthm eval-bdd-q-compose-associative
  (implies (and (ubddp x) (ubdd-listp ys) (ubdd-listp zs))
           (equal (eval-bdd (q-compose (q-compose x ys) zs) vals)
                  (eval-bdd (q-compose x (q-compose-list ys zs))
                            vals))))

(defthm q-compose-associative
  (implies (and (ubddp x) (ubdd-listp ys) (ubdd-listp zs))
           (equal (q-compose (q-compose x ys) zs)
                  (q-compose x (q-compose-list ys zs))))
  :hints(("Goal" :in-theory (enable equal-by-eval-bdds))))


(defthm eval-bdd-depth
  (implies (<= (max-depth x) (len l))
           (equal (eval-bdd x (append l l2))
                  (eval-bdd x l)))
  :hints (("goal" :in-theory (enable max-depth))))

(in-theory (enable q-zipper))

(defthm ubdd-listp-q-zipper
  (implies (and (ubdd-listp l1) (ubdd-listp l2))
           (ubdd-listp (q-zipper l1 l2))))

(defthm len-q-zipper
  (equal (len (q-zipper l1 l2))
         (max (len l1) (len l2))))

(defun nth-q-zipper-ind (n a b)
  (if (zp n)
      (cons a b)
    (head-tail-bind
     ((a1 ar a)
      (b1 br b))
     (nth-q-zipper-ind (1- n) ar br))))

(defthm nth-q-zipper
  (implies (and (<= (nfix n) (len a))
                (<= (nfix n) (len b)))
           (equal (nth n (q-zipper a b))
                  (qcons (nth n a) (nth n b))))
  :hints (("goal" :induct (nth-q-zipper-ind n a b))))

(in-theory (disable q-zipper))


(defun nth-qv-list-ind (m start by n)
  (if (zp m)
      (list start by n)
    (nth-qv-list-ind (1- m) (+ start by) by (1- n))))

(defthm nth-qv-list
  (implies (and (integerp n)
                (integerp m)
                (<= 0 m)
                (< m n)
                (integerp start)
                (<= 0 start)
                (integerp by)
                (<= 0 by))
           (equal (nth m (qv-list start by n))
                  (qv (+ start (* m by)))))
  :hints (("goal" :induct (nth-qv-list-ind m start by n)
           :in-theory (enable qv zp nfix))
          (and (case-match id (((0 1) . &) t))
               '(:expand (qv-list start by n)))))



(defthm eval-bdd-extend-list
  (equal (eval-bdd-list (extend-list a b) vars)
         (extend-list (eval-bdd-list a vars) b)))

(defthm eval-q-zipper
  (equal (eval-bdd-list
          (q-zipper l1 l2)
          vars)
         (if (car vars)
             (eval-bdd-list (extend-list l1 l2) (cdr vars))
           (eval-bdd-list (extend-list l2 l1) (cdr vars))))
  :hints (("goal" :in-theory (enable q-zipper))))


(defthm ubddp-qv-all
  (ubddp (qv n)))

(defthm ubdd-listp-qv-list
  (ubdd-listp (qv-list start by n)))

(defthm len-qv-list
  (equal (len (qv-list start by n))
         (nfix n)))


(defthm max-max-depth-q-zipper-upper-bound
  (implies (and (<= (max-max-depth x) c)
                (<= (max-max-depth y) c))
           (<= (max-max-depth (q-zipper x y))
               (+ 1 c)))
  :hints (("goal" :in-theory (enable q-zipper max-depth)))
  :rule-classes (:rewrite :linear))

(defthm max-depth-qv
  (equal (max-depth (qv n))
         (1+ (nfix n)))
  :hints (("goal" :in-theory (enable max-depth qv))))

(encapsulate nil
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (defthm max-max-depth-qv-list
    (implies (and (natp start) (natp by) (posp n))
             (equal (max-max-depth (qv-list start by n))
                    (+ 1 start (* by (1- n)))))
    :hints (("goal" :in-theory (enable max-depth natp posp))
            ("Subgoal *1/5" :expand (qv-list start by 1))))

  (defthm max-max-depth-make-list-ac
    (equal (max-max-depth (make-list-ac n nil acc))
           (max-max-depth acc)))

  (defthm len-q-param-inv
    (implies (<= (max-depth x) (nfix nvars))
             (<= (max-max-depth (q-param x nvars))
                 (len (q-param-inv x nvars))))
    :hints (("goal" :in-theory (enable max-depth))
            ("Subgoal *1/16"
             :use ((:instance max-max-depth-q-zipper-upper-bound
                              (x (q-param (car x) (1- nvars)))
                              (y (q-param (cdr x) (1- nvars)))
                              (c (len (q-param-inv (car x) (+ -1 nvars)))))
                   (:instance max-max-depth-q-zipper-upper-bound
                              (x (q-param (car x) (1- nvars)))
                              (y (q-param (cdr x) (1- nvars)))
                              (c (len (q-param-inv (cdr x) (+ -1 nvars))))))))
    :rule-classes :linear))


(defthm max-max-depth-q-param
  (<= (max-max-depth (q-param pred n))
      (nfix n))
  :rule-classes (:rewrite :linear))

(defthm max-max-depth-q-param-inv
  (<= (max-max-depth (q-param-inv pred n))
      (nfix n))
  :rule-classes (:rewrite :linear))

(defthm not-eval-bdd-qv-nil
  (not (eval-bdd (qv n) nil)))

(defthm eval-bdd-qv1
  (equal (eval-bdd (qv n) vars)
         (if (nth n vars) t nil)))


(local
 (encapsulate nil
   (local (include-book "arithmetic/top" :dir :system))
   (defthm take-bfix-list
     (equal (take (len vars) (bfix-list vars))
            (bfix-list vars)))))

(defthm bfix-list-bfix-list
  (equal (bfix-list (bfix-list x))
         (bfix-list x)))

(defthm eval-qv-list
  (implies (natp start)
           (equal (eval-bdd-list (qv-list start 1 n)
                                 vars)
                  (bfix-list
                   (take n (nthcdr start vars)))))
  :hints(("Goal" :in-theory (enable take))))

(defthm ubdd-listp-make-list-ac
  (equal (ubdd-listp (make-list-ac n nil acc))
         (ubdd-listp acc)))

(defthm ubdd-listp-q-param
  (ubdd-listp (q-param x depth)))

(defthm len-of-make-list-ac
  (equal (len (make-list-ac n val acc))
         (+ (nfix n) (len acc))))

(defthm len-q-param
  (equal (len (q-param x depth))
         (nfix depth)))

(defun q-param-eval-bdd-ind (x depth vars)
  (if (atom x)
      (cons depth vars)
    (list (q-param-eval-bdd-ind (car x) (1- depth) (cdr vars))
          (q-param-eval-bdd-ind (cdr x) (1- depth) (cdr vars))
          (q-param-eval-bdd-ind (car x) (1- depth) vars)
          (q-param-eval-bdd-ind (cdr x) (1- depth) vars))))

(defthm eval-q-param
  (implies (and (natp depth)
                (<= (max-depth x) depth)
                (ubddp x)
                x)
           (equal (eval-bdd x (eval-bdd-list (q-param x depth) vars))
                  t))
  :hints (("Goal" :induct (q-param-eval-bdd-ind x depth vars)
           :in-theory (enable max-depth))))




(local
 (defthm bfix-list-list-fix
   (equal (bfix-list (list-fix x))
          (bfix-list x))))

;; (defthm eval-q-param-inv
;;   (implies (and (equal (eval-bdd x vars) t)
;;                 (<= (max-depth x) (len vars)))
;;            (equal (eval-bdd-list (q-param x (len vars))
;;                                  (q-param-inv x vars))
;;                   (bfix-list vars)))
;;   :hints (("goal" :induct (q-param-inv x vars))))


(defn eqpib-ind (x vars)
  (cond ((atom vars) x)
        ((atom x) vars)
        ((not (car x))
         (eqpib-ind (cdr x) (cdr vars)))
        ((not (cdr x))
         (eqpib-ind (car x) (cdr vars)))
        (t (list (eqpib-ind (car x) (cdr vars))
                 (eqpib-ind (cdr x) (cdr vars))))))


(defthm extend-list-len
  (implies (<= (len b) (len a))
           (equal (extend-list a b) a)))


(defthm ubdd-listp-q-param-inv
  (ubdd-listp (q-param-inv x nvars)))

(defthm eval-q-param-inv
  (implies (and (equal (eval-bdd x vars) t)
                (<= (max-depth x) (len vars)))
           (equal (eval-bdd-list (q-param x (len vars))
                                 (eval-bdd-list (q-param-inv x (len vars))
                                                vars))
                  (bfix-list vars)))
  :hints (("goal" :induct (eqpib-ind x vars)
           :in-theory (e/d (max-depth)))))

(defthm len-q-param-inv-upper-bound
  (<= (len (q-param-inv x nvars))
      (nfix nvars))
  :rule-classes :linear)

(defthm len-bfix-list
  (equal (len (bfix-list x))
         (len x)))

(defthm compose-q-param-inv
  (implies (and (equal (eval-bdd x vars) t)
                (<= (max-depth x) (len vars)))
           (equal (eval-bdd-list (q-compose-list
                                  (q-param x (len vars))
                                  (q-param-inv x (len vars)))
                                 vars)
                  (bfix-list vars))))

(defthm bfix-list-boolean-list
  (and (boolean-listp (bfix-list x))
       (implies (boolean-listp x)
                (equal (bfix-list x) x))))

;; -------------------------------------------------------------------
;; Theorem 1 from Aagard-Jones-Seger 1999:

;; part 1:
(defthm forall-y-p-of-param-of-y-is-true
  (implies (and p
                (ubddp p)
                (integerp n)
                (<= (max-depth p) n))
           (equal (eval-bdd p
                            (eval-bdd-list (q-param p n)
                                           y))
                  t)))

;; part 2:
(defthm exists-y-such-that-x-is-param-of-y
  (implies (and (equal (eval-bdd p x) t)
                (<= (max-depth p) (len x))
                (boolean-listp x))
           (let ((y (eval-bdd-list (q-param-inv p (len x)) x)))
             (equal (eval-bdd-list (q-param p (len x))
                                   y)
                    x))))
;; -------------------------------------------------------------------

;; part 2 using compose instead of eval:
(defthm x-is-param-of-y-compose-eval
  (implies (and (equal (eval-bdd p x) t)
                (<= (max-depth p) (len x))
                (boolean-listp x))
           (equal (eval-bdd-list (q-compose-list (q-param p (len x))
                                                 (q-param-inv p (len x)))
                                 x)
                  x)))

(memoize 'q-param :condition '(consp x))
(memoize 'q-param-inv :condition '(consp x))
(memoize 'q-compose :condition '(consp x))



;; From-param-space pulls a bdd y in param(p) space back into the original
;; space.  To prove it correct we also define to-param-space.
(defn from-param-space (p y)
  (cond ((atom y) (if y p nil))
        ((atom p) (if p y nil))
        ((eq (car p) nil)
         (let ((x (from-param-space (cdr p) y)))
           (qcons nil x)))
        ((eq (cdr p) nil)
         (let ((x (from-param-space (car p) y)))
           (qcons x nil)))
        (t (qcons (from-param-space (car p) (car y))
                  (from-param-space (cdr p) (cdr y))))))

(memoize 'from-param-space :condition '(or (consp p) (consp y)))

(defn to-param-space (p y)
  (cond ((atom p) y)
        ((atom y) y)
        ((eq (car p) nil)
         (to-param-space (cdr p) (cdr y)))
        ((eq (cdr p) nil)
         (to-param-space (car p) (car y)))
        (t (qcons (to-param-space (car p) (car y))
                  (to-param-space (cdr p) (cdr y))))))

;; [Jared]: tweaking this to only memoize when car&cdr are non-nil, to slightly
;; reduce memo table overhead.

(memoize 'to-param-space :condition '(and (consp p)
                                          (consp y)
                                          (car p)
                                          (cdr p)))



(defthm ubddp-to-param-space
  (implies (ubddp x)
           (ubddp (to-param-space p x))))

(defun param-env (p env)
  (declare (xargs :guard t))
  (cond ((atom p) env)
        ((atom env) nil)
        ((eq (car p) nil) (param-env (cdr p) (cdr env)))
        ((eq (cdr p) nil) (param-env (car p) (cdr env)))
        ((car env) (cons t (param-env (car p) (cdr env))))
        (t       (cons nil (param-env (cdr p) (cdr env))))))

(defthm param-env-to-param-space
  (implies (eval-bdd p env)
           (equal (eval-bdd (to-param-space p x)
                            (param-env p env))
                  (eval-bdd x env)))
  :hints(("Goal" :in-theory (enable eval-bdd to-param-space))))

(defun unparam-env (p env)
  (declare (xargs :guard t))
  (cond ((atom p) env)
        ((eq (car p) nil) (cons nil (unparam-env (cdr p) env)))
        ((eq (cdr p) nil) (cons t (unparam-env (car p) env)))
        (t (mv-let (car cdr) (if (consp env)
                                 (mv (car env) (cdr env))
                               (mv nil nil))
             (cons car (unparam-env (if car (car p) (cdr p))
                                    cdr))))))


(encapsulate
  nil
  (local (defun ind (x p env)
           (if (consp x)
               (if (consp p)
                   (if (car p)
                       (if (cdr p)
                           (if (car env)
                               (ind (car x) (car p) (cdr env))
                             (ind (cdr x) (cdr p) (cdr env)))
                         (ind x (car p) env))
                     (ind x (cdr p) env))
                 x)
             env)))

  (defthm eval-param-env-of-unparam-env
    (equal (eval-bdd x (param-env p (unparam-env p env)))
           (eval-bdd x env))
    :hints (("goal" :induct (ind x p env)
             :in-theory (enable default-car default-cdr))
            (and stable-under-simplificationp
                 '(:expand ((:free (env) (eval-bdd x env))))))))

(defthm eval-with-unparam-env
  (implies (and p (ubddp p))
           (eval-bdd p (unparam-env p env))))


(defun unparam-env-ind (x p env)
  (cond ((atom p) (list x env))
        ((eq (car p) nil) (unparam-env-ind (cdr x) (cdr p) env))
        ((eq (cdr p) nil) (unparam-env-ind (car x) (car p) env))
        (t (unparam-env-ind (if (car env) (car x) (cdr x))
                            (if (car env) (car p) (cdr p))
                            (cdr env)))))

(defthmd unparam-env-to-param-space
  (equal (eval-bdd (to-param-space p x) env)
         (eval-bdd x (unparam-env p env)))
  :hints (("goal" :induct (unparam-env-ind x p env)
           :expand ((:free (env) (eval-bdd x env))
                    (:free (env) (unparam-env p env)))
           :in-theory (enable default-car default-cdr))))

(defthm unparam-env-of-param-env
  (implies (eval-bdd p env)
           (equal (eval-bdd x (unparam-env p (param-env p env)))
                  (eval-bdd x env)))
  :hints (("goal" :use ((:instance param-env-to-param-space)
                        (:instance unparam-env-to-param-space
                         (env (param-env p env)))))))

(defn to-param-space-list (p list)
  (if (atom list)
      nil
    (cons (to-param-space p (car list))
          (to-param-space-list p (cdr list)))))

(defthm eval-bdd-lst-to-param-space-lst
  (implies (eval-bdd p env)
           (equal (eval-bdd-list (to-param-space-list p list)
                                 (param-env p env))
                  (eval-bdd-list list env))))






(defun q-param-to-param-ind (p m n)
  (if (atom p)
      (cons m n)
    (cons (q-param-to-param-ind (car p) (1- m) (1- n))
          (q-param-to-param-ind (cdr p) (1- m) (1- n)))))

(encapsulate nil
  (local (include-book "arithmetic/top-with-meta" :dir :system))

  (defthm nth-make-list-ac-nil
    (equal (nth m (make-list-ac n nil acc))
           (and (<= (nfix n) (nfix m))
                (nth (- (nfix m) (nfix n)) acc)))
    :hints (("goal" :induct (make-list-ac n nil acc)))))

;; TO-PARAM-SPACE of (QV m) is the same as the mth element of Q-PARAM.
(defthm q-param-to-param
 (implies (and (integerp n)
               (integerp m)
               (<= 0 m)
               (< m n)
               (<= (max-depth p) n))
          (equal (nth m (q-param p n))
                 (to-param-space p (qv m))))
 :hints (("goal" :induct (q-param-to-param-ind p m n)
          :in-theory (enable max-depth qv))))

(encapsulate nil
  (local (in-theory (disable equal-by-eval-bdds)))
  (local (defthm q-not-equal-t
           (implies (ubddp x)
                    (equal (equal (q-not x) t)
                           (equal x nil)))
           :hints (("goal" :in-theory (enable q-not)))))
  (local (defthm not-q-not-x
           (implies (ubddp x)
                    (iff (q-not x)
                         (not (equal x t))))
           :hints (("goal" :in-theory (enable q-not)))))
  (local (in-theory (disable q-not-under-iff)))
  ;; NOT commutes over to-param-space:
  (defthm q-not-to-param
    (implies (and p (ubddp p) (ubddp x))
             (equal (q-not (to-param-space p x))
                    (to-param-space p (q-not x))))
    :hints (("goal" :in-theory
             (e/d (q-not) (equal-by-eval-bdds)))
            ("Subgoal *1/9"
             :in-theory (e/d (q-not ubddp-q-not-t-implies-not
                                    ubddp-q-not-nil-implies-t))))))




(encapsulate
 ()
 (local (defthm not-consp-not-nil-implies-t
          (implies (and (not (consp (to-param-space p x)))
                        (ubddp x)
                        (to-param-space p x))
                   (equal (to-param-space p x) t))
          :rule-classes :forward-chaining))

 (defun q-and-to-param-ind (p x y)
   (if (atom p)
       (cons x y)
     (cons (q-and-to-param-ind (car p) (qcar x) (qcar y))
           (q-and-to-param-ind (cdr p) (qcdr x) (qcdr y)))))

 ;; AND commutes over to-param-space:
 (defthm q-and-to-param
   (implies (and (ubddp x) (ubddp y))
            (equal (q-and (to-param-space p x)
                          (to-param-space p y))
                   (to-param-space p (q-and x y))))
   :hints (("goal" :induct (q-and-to-param-ind p x y)
            ;; BOZO: Why do we have to disable force?
            :in-theory (e/d (q-and) (ubddp (force)))))))

(defthm q-ite-in-terms-of-and-and-not
  (implies (and (ubddp x) (ubddp y) (ubddp z))
           (equal (q-ite x y z)
                  (q-not (q-and
                          (q-not (q-and x y))
                          (q-not (q-and (q-not x) z))))))
  :hints(("Goal" :in-theory (enable equal-by-eval-bdds)))
  :rule-classes nil)

;; Using the AND and NOT thms we can prove that all basic BDD operations
;; commute over to-param-space:
(defthm q-ite-to-param
  (implies (and p (ubddp p) (ubddp x) (ubddp y) (ubddp z))
           (equal (q-ite (to-param-space p x)
                         (to-param-space p y)
                         (to-param-space p z))
                  (to-param-space p (q-ite x y z))))
  :hints (("goal"
           :use ((:instance q-ite-in-terms-of-and-and-not)
                 (:instance q-ite-in-terms-of-and-and-not
                            (x (to-param-space p x))
                            (y (to-param-space p y))
                            (z (to-param-space p z)))))))



;; Finally, from-param-space of to-param-space reduces to q-and with the predicate.
(defthm to-from-param-space
  (implies (and (ubddp x) (ubddp p))
           (equal (from-param-space p (to-param-space p x))
                  (q-and p x)))
  :hints (("goal" :induct (to-param-space p x)
           :in-theory (e/d (q-and) (ubddp)))))

(defthm eval-bdd-of-qcons
  (equal (eval-bdd (qcons x y) env)
         (if (car env)
             (eval-bdd x (cdr env))
           (eval-bdd y (cdr env)))))

(defun to-from-ind (p x env)
  (if (consp p)
      (cond ((eq (car p) nil)
             (and (not (car env))
                  (to-from-ind (cdr p) (cdr x) (cdr env))))
            ((eq (cdr p) nil)
             (and (car env)
                  (to-from-ind (car p) (car x) (cdr env))))
            (t (list (to-from-ind (car p) (car x) (cdr env))
                     (to-from-ind (cdr p) (cdr x) (cdr env)))))
    (list p x env)))


(defthm from-param-space-of-qcons
  (implies (and (car p) (cdr p))
           (equal (from-param-space p (qcons x y))
                  (if (atom (qcons x y))
                      (and x p)
                    (qcons (from-param-space (car p) x)
                           (from-param-space (cdr p) y)))))
  :otf-flg t)

(defthm consp-qcons
  (equal (consp (qcons x y))
         (not (and (booleanp x)
                   (equal x y)))))

(defthm to-from-param-space-eval
  (equal (eval-bdd (from-param-space p (to-param-space p x)) env)
         (and (eval-bdd p env)
              (eval-bdd x env)))
  :hints (("goal" :induct (to-from-ind p x env)
           :in-theory (disable qcons))))


(defthm to-param-space-self
  (implies (and (ubddp p) p)
           (equal (to-param-space p p) t))
  :hints(("Goal" :in-theory (enable ubddp))))


(defthm from-to-param-space
  (implies (and (ubddp x) (ubddp p) p)
           (equal (to-param-space p (from-param-space p x))
                  x))
  :hints (("goal" :induct (from-param-space p x)
           :in-theory (e/d (q-and) (ubddp)))))



(defun param-env-ind (x p env)
  (cond ((atom p) (list x env))
        ((eq (car p) nil) (param-env-ind x (cdr p) (cdr env)))
        ((eq (cdr p) nil) (param-env-ind x (car p) (cdr env)))
        ((car env) (cons t (param-env-ind (car x) (car p) (cdr env))))
        (t       (cons nil (param-env-ind (cdr x) (cdr p) (cdr env))))))

(defthm eval-of-from-param-space
  (implies (eval-bdd p env)
           (equal (eval-bdd (from-param-space p x)
                            env)
                  (eval-bdd x (param-env p env))))
  :hints (("goal" :induct (param-env-ind x p env)
           :expand ((from-param-space p x)
                    (unparam-env p env)
                    (:free (env) (eval-bdd x env))
                    (eval-bdd p env)))))
