; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "GL")
(include-book "bfr")
(include-book "bfr-param")
(include-book "bfr-reasoning")
(include-book "std/stobjs/absstobjs" :dir :system)
(include-book "std/stobjs/clone" :dir :system)
(include-book "std/lists/index-of" :dir :system)
(local (include-book "centaur/aig/aig-vars" :dir :system))


;; A CONSTRAINTS structure is just another Boolean function representation.
;; In BDD mode, it is just a BDD.
;; In AIG mode, it is instead a fast alist mapping AIGs to 1, 0, or nil.

;; Its purpose: we want a representation that gives us a quick check that often
;; can tell us whether the represented function implies some other Boolean
;; function or its negation.  For BDD mode this is trivial (though maybe not
;; that cheap).  For AIG mode, we can go through the top-level AND structure to
;; see whether (un-negated) conjuncts are present in the fast alist.





;; (define constraint-alist-has-binding (key val alist)
;;   (if (atom alist)
;;       nil
;;     (if (or (atom (car alist))
;;             (not (equal key (caar alist))))
;;         (constraint-alist-has-binding key val (cdr alist))
;;       (and (cdar alist)
;;            (or (eql (bfix val) (bfix (cdar alist)))
;;                (constraint-alist-has-binding key val (cdr alist))))))
;;   ///
;;   (defthm constraint-alist-has-binding-by-lookup
;;     (implies (and (cdr (hons-assoc-equal key alist))
;;                   (acl2::bit-equiv val (cdr (hons-assoc-equal key alist))))
;;              (constraint-alist-has-binding
;;               key val alist)))

;;   (defthm constraint-alist-has-binding-by-no-lookup
;;     (implies (not (cdr (hons-assoc-equal key alist)))
;;              (not (constraint-alist-has-binding
;;                    key val alist))))

;;   (defthm constraint-alist-has-binding-of-acons
;;     (equal (constraint-alist-has-binding k1 val1 (cons (cons k2 val2) alist))
;;            (if (equal k1 k2)
;;                (and (not (equal val2 nil))
;;                     (or (equal (bfix val1) (bfix val2))
;;                         (constraint-alist-has-binding k1 val1 alist)))
;;              (constraint-alist-has-binding k1 val1 alist))))

;;   (defcong acl2::bit-equiv equal (constraint-alist-has-binding k v alist) 2))

(local (in-theory (disable equal-of-booleans-rewrite
                           acl2::consp-of-car-when-alistp
                           set::double-containment
                           acl2::aig-eval
                           ;;acl2::consp-under-iff-when-true-listp
                           default-car default-cdr)))

(define calist-lookup (x calist)
  :inline t
  (let* ((res (cdr (hons-get x calist))))
    (and res (acl2::bfix res)))
  ///
  (defthm calist-lookup-of-cons
    (equal (calist-lookup k1 (cons pair calist))
           (if (or (atom pair)
                   (not (equal k1 (car pair))))
               (calist-lookup k1 calist)
             (and (cdr pair) (acl2::bfix (cdr pair))))))

  (defthm calist-lookup-of-atom
    (implies (not (consp x))
             (equal (calist-lookup k x) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))

;; (define calist-remassoc (x calist)
;;   (if (atom calist)
;;       nil
;;     (if (and (consp (car calist))
;;              (equal x (caar calist)))
;;         (calist-remassoc x (cdr calist))
;;       (cons (car calist)
;;             (calist-remassoc x (cdr calist)))))

;;   ///
;;   (defthm calist-lookup-of-calist-remassoc
;;     (equal (calist-lookup k1 (calist-remassoc k2 calist))
;;            (if (equal k1 k2)
;;                nil
;;              (calist-lookup k1 calist)))))

;; (local
;;  (acl2::def-universal-equiv alist-set-equiv
;;    :qvars (k)
;;    :equiv-terms ((iff (hons-assoc-equal k x)))))

;; (local (defcong alist-set-equiv iff (hons-assoc-equal k x) 2
;;          :hints(("Goal" :use ((:instance alist-set-equiv-necc
;;                                (y x-equiv)))))))

(define calist-remassocs (x seen)
  (if (atom x)
      nil
    (if (and (consp (car x))
             (not (ec-call (member-equal (caar x) seen))))
        (cons (car x) (calist-remassocs (cdr x) seen))
      (calist-remassocs (cdr x) seen)))
  ///
  (defthm lookup-in-calist-remassocs
    (equal (calist-lookup k (calist-remassocs x seen))
           (and (not (member k seen))
                (calist-lookup k x))))
  (defthm len-of-calist-remassocs
    (<= (len (calist-remassocs x seen)) (len x))
    :rule-classes :linear)

  (defthm calist-remassocs-compose
    (equal (calist-remassocs (calist-remassocs x seen1) seen2)
           (calist-remassocs x (append seen1 seen2))))

  (defcong acl2::set-equiv equal (calist-remassocs x seen) 2))

;; (calist-remassoc (car x)
;;                      (calist-remassocs (cdr x) calist))))


;; ;; Need this lemma a lot here dealing with seen alists...
;; (local
;;  (defthm alist-set-equiv-of-reorder-aconses
;;    (alist-set-equiv (list* (cons a v1) (cons b v2) rest)
;;                     (list* (cons b v2) (cons a v1) rest))
;;    :hints(("Goal" :in-theory (enable alist-set-equiv)))))

;; (local (defcong alist-set-equiv equal (calist-remassocs x seen) 2
;;          :hints(("Goal" :in-theory (enable calist-remassocs)))))


(define shrink-constraint-alist-aux (x seen)
  (if (atom x)
      (prog2$ (fast-alist-free seen) nil)
    (if (and (consp (car x))
             (not (hons-get (caar x) seen)))
        (if (cdar x)
            (hons-acons (caar x) (bfix (cdar x))
                        (shrink-constraint-alist-aux
                         (cdr x) (hons-acons (caar x) t seen)))
          (shrink-constraint-alist-aux (cdr x) (hons-acons (caar x) t seen)))
      (shrink-constraint-alist-aux (cdr x) seen)))
  ///
  (local (defun ind (x seen)
           (declare (xargs :measure (len x)))
           (if (atom x)
               seen
             (list (ind (cdr x) (hons-acons (caar x) t seen))
                   (ind (cdr x) (hons-acons (caar x) t nil))
                   (ind (cdr x) seen))
             ;; (if (and (consp (car x))
             ;;          (not (hons-get (caar x) seen)))
             ;;     (list (ind (cdr x) (hons-acons (caar x) t seen))
             ;;           (ind (cdr x) (hons-acons (caar x) t nil)))
             ;;   (ind (cdr x) seen))
             )))

  (local (defthm calist-remassocs-compose-strong
           (implies (equal y (calist-remassocs x seen1))
                    (equal (calist-remassocs y seen2)
                           (calist-remassocs x (append seen1 seen2))))))

  (local (defthm set-equiv-of-cons-redundant
           (implies (member k x)
                    (acl2::set-equiv (cons k x) x))))

  ;; (local (defthm alist-set-equiv-of-cons-redundant
  ;;          (implies (hons-assoc-equal k seen)
  ;;                   (alist-set-equiv (cons (cons k v) seen) seen))
  ;;          :hints(("Goal" :in-theory (enable alist-set-equiv)))))

  (defthm shrink-constraint-alist-aux-of-seen
    (implies (syntaxp (not (equal seen ''nil)))
             (equal (shrink-constraint-alist-aux x seen)
                    (calist-remassocs
                     (shrink-constraint-alist-aux x nil)
                     (alist-keys seen))))
    :hints(("Goal" :in-theory (enable calist-remassocs alist-keys)
            :expand ((shrink-constraint-alist-aux x nil))
            :induct (ind x seen)))))

(define shrink-constraint-alist (x)
  :measure (len x)
  :verify-guards nil
  (mbe :logic (if (atom x)
                  nil
                (if (consp (car x))
                    (let ((rest (calist-remassocs
                                 (shrink-constraint-alist
                                  (cdr x)) (list (caar x)))))
                      (if (cdar x)
                          (hons-acons (caar x) (bfix (cdar x)) rest)
                        rest))
                  (shrink-constraint-alist (cdr x))))
       :exec (shrink-constraint-alist-aux x nil))
  ///
  (defthm shrink-constraint-alist-aux-redef
    (equal (shrink-constraint-alist-aux x nil)
           (shrink-constraint-alist x))
    :hints(("Goal" :in-theory (enable shrink-constraint-alist-aux
                                      calist-remassocs))))
  (verify-guards shrink-constraint-alist)

  (defthm lookup-in-shrink-constraint-alist
    (equal (calist-lookup k (shrink-constraint-alist x))
           (calist-lookup k x)))

  (local (defthm set-equiv-of-cons-redundant
           (implies (member k seen)
                    (acl2::set-equiv (cons k seen) seen))))

  (local (defthm set-equiv-of-append-to-cons
           (acl2::set-equiv (append seen (list k))
                            (cons k seen))))

  (defthm shrink-constraint-alist-of-calist-remassocs
    (equal (shrink-constraint-alist (calist-remassocs x seen))
           (calist-remassocs (shrink-constraint-alist x) seen))
    :hints (("goal" :induct (shrink-constraint-alist x)
             :expand ((calist-remassocs x seen)
                      (calist-remassocs nil seen)
                      (:free (a b) (calist-remassocs (cons a b) seen))))))

  (defthm shrink-constraint-alist-idempotent
    (equal (shrink-constraint-alist (shrink-constraint-alist x))
           (shrink-constraint-alist x))
    :hints (("goal" :induct (shrink-constraint-alist x)
             :expand ((:free (a b) (shrink-constraint-alist (cons a b))))))))


(define eval-constraint-alist-aux (x seen env)
  (if (atom x)
      (prog2$ (fast-alist-free seen)
              t)
    (if (or (atom (car x))
            (hons-get (caar x) seen))
        (eval-constraint-alist-aux (cdr x) seen env)
      (if (cdar x)
          (and (iff (acl2::aig-eval (caar x) env) (eql (cdar x) 1))
               (eval-constraint-alist-aux (cdr x) (hons-acons (caar x) t seen) env))
        (eval-constraint-alist-aux (cdr x) (hons-acons (caar x) t seen) env))))
  ///

  (local (defun ind (x seen)
           (declare (xargs :measure (len x)))
           (if (atom x)
               seen
             (list (ind (cdr x) seen)
                   (ind (cdr x) (hons-acons (caar x) t seen))
                   (ind (calist-remassocs (cdr x) (alist-keys seen))
                        (hons-acons (caar x) t nil))))))

  (local (defthm set-equiv-of-append-to-cons
           (acl2::set-equiv (append seen (list k))
                            (cons k seen))))

  (defthm eval-constraint-alist-aux-of-seen
    (implies (syntaxp (not (equal seen ''nil)))
             (equal (eval-constraint-alist-aux x seen env)
                    (eval-constraint-alist-aux
                     (calist-remassocs x (alist-keys seen)) nil env)))
    :hints(("Goal" :in-theory (e/d (calist-remassocs))
            :induct (ind x seen)))))

(define eval-constraint-alist (x env)
  :measure (len x)
  :verify-guards nil
  (mbe :logic (if (atom x)
                  t
                (if (consp (car x))
                    (let ((rest (eval-constraint-alist
                                 (calist-remassocs (cdr x)
                                                   (list (caar x)))
                                 env)))
                      (if (cdar x)
                          (and (iff (acl2::aig-eval (caar x) env)
                                    (eql (cdar x) 1))
                               rest)
                        rest))
                  (eval-constraint-alist (cdr x) env)))
       :exec (eval-constraint-alist-aux x nil env))
  ///

  (local (defthm set-equiv-of-cons-redundant
           (implies (member k x)
                    (acl2::set-equiv (cons k x) x))))

  (defthm eval-constraint-alist-aux-redef
    (equal (eval-constraint-alist-aux x nil env)
           (eval-constraint-alist x env))
    :hints(("Goal" :in-theory (enable eval-constraint-alist-aux
                                      calist-remassocs))))

  (verify-guards eval-constraint-alist)


  (defthm eval-constraint-alist-of-shrink-constraint-alist
    (equal (eval-constraint-alist (shrink-constraint-alist x) env)
           (eval-constraint-alist x env))
    :hints(("Goal" :in-theory (enable shrink-constraint-alist)
            :induct (eval-constraint-alist x env)
            :expand ((:free (a b) (eval-constraint-alist (cons a b) env))))))

  (defthm equal-1-of-lookup-when-eval-constraint-alist
    (implies (eval-constraint-alist calist env)
             (equal (equal 1 (calist-lookup x calist))
                    (and (calist-lookup x calist)
                         (acl2::aig-eval x env))))))

(local

; At least two lemmas below, eval-constraint-alist-witness and
; constraint-alist-assume-aig-contradictionp, required this Matt K. mod April
; 2016 for the addition of a type-set-bit for the set {1}.  The improved
; type-prescription rule for calist-lookup$inline made progress in the proof
; that was harmful.  (Technical note: When assume-true-false-rec never used an
; equality (equal term 1) to extend the false-type-alist by subtracting
; *ts-one* from the type of term, we didn't have this problem.  It arose when
; we tweaked that heuristic to allow this extension when term is a variable,
; which was important to do for the sake of bitp-compound-recognizer; see the
; Essay on Strong Handling of *ts-one* in ACL2 source function
; assume-true-false-rec.)

 (in-theory (disable (:t calist-lookup$inline))))

(define eval-constraint-alist-witness (x env)
  :measure (len x)
  (if (atom x)
      t
    (if (consp (car x))
        (let ((rest (eval-constraint-alist-witness
                     (calist-remassocs (cdr x) (list (caar x)))
                     env)))
          (if (cdar x)
              (if (xor (acl2::aig-eval (caar x) env)
                       (eql (cdar x) 1))
                  (caar x)
                rest)
            rest))
      (eval-constraint-alist-witness (cdr x) env)))
  ///
  (defthm eval-constraint-alist-in-terms-of-witness
    (implies (acl2::rewriting-positive-literal `(eval-constraint-alist ,x ,env))
             (equal (eval-constraint-alist x env)
                    (b* ((k (eval-constraint-alist-witness x env)))
                      (or (not (calist-lookup k x))
                          (iff (acl2::aig-eval k env) (equal (calist-lookup k x) 1))))))
    :hints(("Goal" :induct (eval-constraint-alist-witness x env)
            :expand ((eval-constraint-alist x env)
                     (eval-constraint-alist-witness x env))
            :in-theory (disable (:d eval-constraint-alist-witness))))))

;; (defsection constraint-alist-equiv
;;   (acl2::def-universal-equiv constraint-alist-equiv
;;     :qvars (k)
;;     :equiv-terms ((equal (calist-lookup k x))))

;;   (defcong constraint-alist-equiv equal (eval-constraint-alist x env) 1
;;     :hints (("goal" :use ((:instance constraint-alist-equiv-necc
;;                            (k (eval-constraint-alist-witness x env))
;;                            (y x-equiv))
;;                           (:instance constraint-alist-equiv-necc
;;                            (k (eval-constraint-alist-witness x-equiv env))
;;                            (y x-equiv))))))

;;   (defcong constraint-alist-equiv equal (calist-lookup k x) 2
;;     :hints(("Goal" :in-theory (enable constraint-alist-equiv-necc))))


;;   (defthm constraint-alist-equiv-of-shrink-constraint-alist
;;     (constraint-alist-equiv (shrink-constraint-alist x) x)
;;     :hints(("Goal" :in-theory (enable constraint-alist-equiv))))

;;   (defcong constraint-alist-equiv constraint-alist-equiv (cons pair alist) 2
;;     :hints (;; ("goal" :use ((:instance constraint-alist-equiv-necc
;;             ;;                (k (constraint-alist-equiv-witness
;;             ;;                    (cons pair alist) (cons pair alist-equiv)))))
;;             ;;  :in-theory (disable constraint-alist-equiv-necc))
;;             (and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))
;;                    :in-theory (enable constraint-alist-equiv-necc))))))

(define constraint-alist->aig-aux (x seen)
  (if (atom x)
      (prog2$ (fast-alist-free seen) t)
    (if (and (consp (car x))
             (not (hons-get (caar x) seen)))
        (if (cdar x)
            (acl2::aig-and (acl2::aig-iff (caar x) (equal (cdar x) 1))
                           (constraint-alist->aig-aux (cdr x) (hons-acons (caar x) t seen)))
          (constraint-alist->aig-aux (cdr x) (hons-acons (caar x) t seen)))
      (constraint-alist->aig-aux (cdr x) seen)))
  ///

  (local (defun ind (x seen)
           (declare (xargs :measure (len x)))
           (if (atom x)
               seen
             (list (ind (cdr x) seen)
                   (ind (cdr x) (hons-acons (caar x) t seen))
                   (ind (calist-remassocs (cdr x) (alist-keys seen))
                        (hons-acons (caar x) t nil))))))

  (local (defthm set-equiv-of-append-to-cons
           (acl2::set-equiv (append seen (list k))
                            (cons k seen))))

  (defthm constraint-alist->aig-aux-of-seen
    (implies (syntaxp (not (equal seen ''nil)))
             (equal (constraint-alist->aig-aux x seen)
                    (constraint-alist->aig-aux
                     (calist-remassocs x (alist-keys seen)) nil)))
    :hints (("goal" :in-theory (e/d (calist-remassocs))
             :induct (ind x seen)))))

(define constraint-alist->aig (x)
  :measure (len x)
  :verify-guards nil
  (mbe :logic (if (atom x)
                  t
                (if (consp (car x))
                    (let ((rest (constraint-alist->aig
                                 (calist-remassocs (cdr x) (list (caar x))))))
                      (if (cdar x)
                          (acl2::aig-and
                           (acl2::aig-iff (caar x) (eql (cdar x) 1))
                           rest)
                        rest))
                  (constraint-alist->aig (cdr x))))
       :exec (constraint-alist->aig-aux x nil))
  ///
  (defthm constraint-alist->aig-aux-redef
    (equal (constraint-alist->aig-aux x nil)
           (constraint-alist->aig x))
    :hints(("Goal" :in-theory (enable constraint-alist->aig-aux))))

  (verify-guards constraint-alist->aig)

  (local (defthm set-equiv-of-cons-redundant
           (implies (member k x)
                    (acl2::set-equiv (cons k x) x))))

  (defthm constraint-alist->aig-of-shrink-constraint-alist
    (equal (constraint-alist->aig (shrink-constraint-alist x))
           (constraint-alist->aig x))
    :hints(("Goal" :in-theory (enable shrink-constraint-alist)
            :induct (constraint-alist->aig x)
            :expand ((:free (a b) (constraint-alist->aig (cons a b)))))))

  (defthm eval-of-constraint-alist->aig
    (equal (acl2::aig-eval (constraint-alist->aig x) env)
           (eval-constraint-alist x env))
    :hints(("Goal" :in-theory (e/d (eval-constraint-alist
                                    acl2::aig-eval)
                                   (eval-constraint-alist-in-terms-of-witness)))))

  (defthm sets-in-aig-vars-of-aig-iff
    (implies (and (not (set::in v (acl2::aig-vars a)))
                  (not (set::in v (acl2::aig-vars b))))
             (not (set::in v (acl2::aig-vars (acl2::aig-iff a b)))))
    :hints(("Goal" :in-theory (enable acl2::aig-iff
                                      acl2::aig-or))))


  (defthm constraint-alist->aig-of-remove-none
    (equal (constraint-alist->aig (calist-remassocs x nil))
           (constraint-alist->aig x))
    :hints(("Goal" :in-theory (enable calist-remassocs)))))




;; (define constr-alist-depends-on-aux (v x seen)
;;   (if (atom x)
;;       (prog2$ (fast-alist-free seen)
;;               nil)
;;     (if (or (atom (car x))
;;             (hons-get (caar x) seen))
;;         (constr-alist-depends-on-aux v (cdr x) seen)
;;       (if (cdar x)
;;           (or (set::in (nfix v) (acl2::aig-vars (caar x)))
;;               (constr-alist-depends-on-aux v (cdr x) (hons-acons (caar x) t seen)))
;;         (constr-alist-depends-on-aux v (cdr x) (hons-acons (caar x) t seen)))))
;;   ///

;;   (local (defun ind (x seen)
;;            (declare (xargs :measure (len x)))
;;            (if (atom x)
;;                seen
;;              (list (ind (cdr x) seen)
;;                    (ind (cdr x) (hons-acons (caar x) t seen))
;;                    (ind (calist-remassocs (cdr x) (alist-keys seen))
;;                         (hons-acons (caar x) t nil))))))

;;   (local (defthm set-equiv-of-append-to-cons
;;            (acl2::set-equiv (append seen (list k))
;;                             (cons k seen))))

;;   (defthm constr-alist-depends-on-aux-of-seen
;;     (implies (syntaxp (not (equal seen ''nil)))
;;              (equal (constr-alist-depends-on-aux v x seen)
;;                     (constr-alist-depends-on-aux
;;                      v (calist-remassocs x (alist-keys seen)) nil)))
;;     :hints(("Goal" :in-theory (e/d (calist-remassocs))
;;             :induct (ind x seen)))))

(define constr-alist-depends-on (v x)
  :measure (len x)
  :verify-guards nil
  (if (atom x)
      nil
    (if (consp (car x))
        (if (cdar x)
            (or (set::in (aig-var-fix v) (acl2::aig-vars (caar x)))
                (constr-alist-depends-on
                 v (calist-remassocs (cdr x)
                                     (list (caar x)))))
          (constr-alist-depends-on
           v (calist-remassocs (cdr x)
                               (list (caar x)))))
      (constr-alist-depends-on v (cdr x))))
  ///

  (defcong aig-var-equiv equal (constr-alist-depends-on v x) 1)

  (local (defthm set-equiv-of-cons-redundant
           (implies (member k x)
                    (acl2::set-equiv (cons k x) x))))

  ;; (defthm constr-alist-depends-on-aux-redef
  ;;   (equal (constr-alist-depends-on-aux v x nil)
  ;;          (constr-alist-depends-on v x))
  ;;   :hints(("Goal" :in-theory (enable constr-alist-depends-on-aux
  ;;                                     calist-remassocs))))

  ;; (verify-guards constr-alist-depends-on)


  (defthm constr-alist-depends-on-of-shrink-constraint-alist
    (equal (constr-alist-depends-on v (shrink-constraint-alist x))
           (constr-alist-depends-on v x))
    :hints(("Goal" :in-theory (enable shrink-constraint-alist)
            :induct (constr-alist-depends-on v x)
            :expand ((:free (a b) (constr-alist-depends-on v (cons a b)))))))

  (local (defthm aig-eval-of-acons-when-var-not-present
           (implies (not (set::in v (acl2::aig-vars x)))
                    (equal (acl2::aig-eval x (cons (cons v y) env))
                           (acl2::aig-eval x env)))
           :hints(("Goal" :in-theory (enable acl2::aig-eval
                                             acl2::aig-vars)))))

  (defthm constr-alist-depends-on-correct
    (implies (and (not (constr-alist-depends-on (double-rewrite v) x))
                  (acl2::aig-var-p v))
             (equal (eval-constraint-alist x (cons (cons v val) env))
                    (eval-constraint-alist x env)))
    :hints(("Goal" :in-theory (enable eval-constraint-alist))))

  (local (defthm in-aig-vars-of-aig-iff
           (implies (and (not (set::in v (acl2::aig-vars a)))
                         (not (set::in v (acl2::aig-vars b))))
                    (not (set::in v (acl2::aig-vars (acl2::aig-iff a b)))))
           :hints(("Goal" :in-theory (enable acl2::aig-iff
                                             acl2::aig-or)))))

  (defthm dependencies-of-constraint-alist->aig
    (implies (and (not (constr-alist-depends-on (double-rewrite v) x))
                  (acl2::aig-var-p v))
             (not (set::in v
                            (acl2::aig-vars
                             (constraint-alist->aig x)))))
    :hints(("Goal" :in-theory (enable constraint-alist->aig))))

  (defthm constr-alist-depends-on-of-remassocs
    (implies (not (constr-alist-depends-on k x))
             (not (constr-alist-depends-on k (calist-remassocs x seen))))
    :hints(("Goal" :in-theory (enable calist-remassocs)))))


;; Simplify an AIG under a constraint alist.
(define aig-under-constraint-alist (x calist)
  (b* (((when (booleanp x)) x)
       ((mv negp xabs)
        (if (and (not (acl2::aig-atom-p x)) (eq (cdr x) nil))
            ;; negation
            (mv t (car x))
          (mv nil x)))
       (look (calist-lookup xabs calist))
       ((when look)
        (xor (eql 1 look) negp))
       ((when (acl2::aig-atom-p xabs)) x)
       ((when negp) x)
       (car (aig-under-constraint-alist (car xabs) calist))
       ((when (eq car nil)) nil)
       (cdr (aig-under-constraint-alist (cdr xabs) calist))
       ;; BOZO.  The new, smarter AIG-AND algorithm *might* work here if we can come
       ;; up with a suitable measure.  For now, just use the dumb algorithm.
       (newx (acl2::aig-and-dumb car cdr))
       (look (calist-lookup newx calist))
       ((when look) (eql 1 look)))
    newx)
  ///

  (defthm aig-under-constraint-alist-of-shrink-constraint-alist
    (equal (aig-under-constraint-alist x (shrink-constraint-alist calist))
           (aig-under-constraint-alist x calist)))

  ;; (defcong constraint-alist-equiv equal (aig-under-constraint-alist x calist) 2)

  (defthm aig-under-constraint-alist-correct
    (implies (eval-constraint-alist calist env)
             (equal (acl2::aig-eval (aig-under-constraint-alist x calist) env)
                    (acl2::aig-eval x env)))
    :hints(("Goal" :in-theory (enable aig-under-constraint-alist
                                      acl2::aig-eval))))

  (defthm aig-under-constraint-alist-bfr-depends
    (implies (and (bfr-mode)
                  (not (bfr-depends-on k x)))
             (not (bfr-depends-on k (aig-under-constraint-alist x calist))))
    :hints(("Goal" :in-theory (enable bfr-depends-on))))

  (defthm aig-under-constraint-alist-pbfr-depends
    (implies (and (bfr-mode)
                  (not (pbfr-depends-on k p x)))
             (not (pbfr-depends-on k p (aig-under-constraint-alist x calist))))
    :hints(("Goal" :in-theory (enable pbfr-depends-on bfr-from-param-space))))

  (defthm aig-under-constraint-alist-idempotent
    (equal (aig-under-constraint-alist
            (aig-under-constraint-alist x calist) calist)
           (aig-under-constraint-alist x calist))
    :hints (("goal" :induct (aig-under-constraint-alist x calist))
            (and stable-under-simplificationp
                 '(:in-theory (enable acl2::aig-and-dumb)))))

  (defthm aig-under-constraint-alist-of-t-and-nil
    (and (equal (aig-under-constraint-alist t calist) t)
         (equal (aig-under-constraint-alist nil calist) nil))))


;; (define aig-under-constraint-alist (x calist)
;;   ;; look under one top level negation
;;   (b* (((unless (and (consp x) (eq (cdr x) nil)))
;;         (aig-under-constraint-alist-aux x calist))
;;        (neg (aig-under-constraint-alist-aux (car x) calist))
;;         (acl2::aig-not )))
;;     )

;;   ///

;;   (defthm aig-under-constraint-alist-of-shrink-constraint-alist
;;     (equal (aig-under-constraint-alist x (shrink-constraint-alist calist))
;;            (aig-under-constraint-alist x calist)))

;;   ;; (defcong constraint-alist-equiv equal (aig-under-constraint-alist x calist) 2)

;;   (defthm aig-under-constraint-alist-correct
;;     (implies (eval-constraint-alist calist env)
;;              (equal (acl2::aig-eval (aig-under-constraint-alist x calist) env)
;;                     (acl2::aig-eval x env)))
;;     :hints(("Goal" :in-theory (enable aig-under-constraint-alist
;;                                       acl2::aig-eval))))

;;   (local (defthm bfr-depends-on-of-aig-not
;;            (implies (bfr-mode)
;;                     (equal (bfr-depends-on k (acl2::aig-not x))
;;                            (bfr-depends-on k x)))
;;            :hints(("Goal" :in-theory (enable bfr-depends-on)))))

;;   (local (defthm bfr-depends-on-of-negation
;;            (implies (and (bfr-mode) (consp x) (not (cdr x)))
;;                     (equal (bfr-depends-on k (car x))
;;                            (bfr-depends-on k x)))
;;            :hints(("Goal" :in-theory (enable bfr-depends-on)))))

;;   (defthm aig-under-constraint-alist-bfr-depends
;;     (implies (and (bfr-mode)
;;                   (not (bfr-depends-on k x)))
;;              (not (bfr-depends-on k (aig-under-constraint-alist x calist)))))

;;   (defthm aig-under-constraint-alist-pbfr-depends
;;     (implies (and (bfr-mode)
;;                   (not (pbfr-depends-on k p x)))
;;              (not (pbfr-depends-on k p (aig-under-constraint-alist x calist))))
;;     :hints(("Goal" :in-theory (enable pbfr-depends-on bfr-from-param-space))))

;;   (defthm aig-under-constraint-alist-idempotent
;;     (equal (aig-under-constraint-alist
;;             (aig-under-constraint-alist x calist) calist)
;;            (aig-under-constraint-alist x calist))
;;     :hints(("Goal" :in-theory (enable acl2::aig-not))
;;            (and stable-under-simplificationp
;;                 '(:expand ((aig-under-constraint-alist-aux x calist))))))

;;   (defthm aig-under-constraint-alist-of-t-and-nil
;;     (and (equal (aig-under-constraint-alist t calist) t)
;;          (equal (aig-under-constraint-alist nil calist) nil))))




(define constraint-alist-delete-keys (keys calist)
  (if (atom keys)
      calist
    (hons-acons (car keys) nil (constraint-alist-delete-keys (cdr keys) calist)))
  ///
  (local (defthm remassocs-of-shrink-when-no-keys
           (implies (not (consp keys))
                    (equal (calist-remassocs (shrink-constraint-alist x) keys)
                           (shrink-constraint-alist x)))
           :hints(("Goal" :in-theory (enable calist-remassocs shrink-constraint-alist)))))

  (local (defthm calist-remassocs-compose-strong
           (implies (equal y (calist-remassocs x seen1))
                    (equal (calist-remassocs y seen2)
                           (calist-remassocs x (append seen1 seen2))))))

  (defthm shrink-of-constraint-alist-delete-keys
    (equal (shrink-constraint-alist (constraint-alist-delete-keys keys calist))
           (calist-remassocs (shrink-constraint-alist calist) keys))
    :hints(("Goal" :in-theory (enable shrink-constraint-alist calist-remassocs pairlis$)
            :expand ((shrink-constraint-alist calist)
                     (:free (seen) (calist-remassocs calist seen))))))

  ;; (defcong constraint-alist-equiv constraint-alist-equiv
  ;;   (constraint-alist-delete-keys keys calist) 2)

  (defthm lookup-of-constraint-alist-delete-keys
    (equal (calist-lookup k (constraint-alist-delete-keys keys calist))
           (and (not (member k keys))
                (calist-lookup k calist))))

  (defthm constraint-alist-delete-nil
    (equal (constraint-alist-delete-keys nil calist)
           calist)))

(define constraint-alist-assume-aig (x calist keys-acc)
  :returns (mv contradictionp calist num-aconses)
  (b* (((when (booleanp x)) (mv (not x) calist keys-acc))
       ((mv negp xabs)
        (if (and (not (acl2::aig-atom-p x)) (eq (cdr x) nil))
            ;; negation
            (mv t (car x))
          (mv nil x)))
       (look (calist-lookup xabs calist))
       ((when look)
        (if (xor (eql 1 look) negp)
            (mv nil calist keys-acc)
          (mv t calist keys-acc)))
       ((when (acl2::aig-atom-p xabs))
        (mv nil (hons-acons xabs (if negp 0 1) calist) (cons xabs keys-acc)))
       ((when negp) (mv nil (hons-acons xabs 0 calist) (cons xabs keys-acc)))
       ((mv contradictionp1 calist keys-acc) (constraint-alist-assume-aig (car xabs) calist keys-acc))
       ((mv contradictionp2 calist keys-acc) (constraint-alist-assume-aig (cdr xabs) calist keys-acc)))
    (mv (or contradictionp1 contradictionp2) calist keys-acc))
  ///

  (local
   (defun shrink-ind (x calist keys-acc)
     (b* (((when (booleanp x)) keys-acc)
          ((mv negp xabs)
           (if (and (not (acl2::aig-atom-p x)) (eq (cdr x) nil))
               ;; negation
               (mv t (car x))
             (mv nil x)))
          (look (calist-lookup xabs calist))
          ((when look) keys-acc)
          ((when (acl2::aig-atom-p xabs)) keys-acc)
          ((when negp) keys-acc)
          (?ign (shrink-ind (car xabs) calist keys-acc))
          ((mv ?contradictionp1 scalist skeys-acc) (constraint-alist-assume-aig (car xabs) (shrink-constraint-alist calist) keys-acc))
          ((mv ?contradictionp1 calist keys-acc) (constraint-alist-assume-aig (car xabs) calist keys-acc))
          (?ign (shrink-ind (cdr xabs) calist keys-acc)))
       (shrink-ind (cdr xabs) scalist skeys-acc))))

  (local (defthm set-equiv-switch
           (acl2::set-equiv (cons b (cons a lst))
                            (cons a (cons b lst)))
           :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw)))))

  (defthm constraint-alist-assume-aig-of-shrink
    (b* (((mv scontra snew-calist skeys) (constraint-alist-assume-aig
                                          x (shrink-constraint-alist calist) keys-acc))
         ((mv contra new-calist keys) (constraint-alist-assume-aig x calist keys-acc)))
      (and (equal scontra contra)
           (equal (shrink-constraint-alist snew-calist)
                  (shrink-constraint-alist new-calist))
           (equal skeys keys)))
    :hints (("goal" :induct (shrink-ind x calist keys-acc)
             :expand ((:free (a b) (shrink-constraint-alist (cons a b)))))))

  (local (defthm eval-of-calist-remassocs-when-not-present
           (implies (not (calist-lookup k calist))
                    (equal (eval-constraint-alist (calist-remassocs calist (list k))
                                                  env)
                           (eval-constraint-alist calist env)))
           :hints(("Goal" :in-theory (enable eval-constraint-alist
                                             calist-remassocs)
                   :expand ((:free (a b) (eval-constraint-alist (cons a b) env)))))))

  (defthm constraint-alist-assume-aig-remains-false
    (b* (((mv ?contradictionp ?new-calist ?keys-out)
          (constraint-alist-assume-aig x calist keys-in)))
      (implies (not (eval-constraint-alist calist env))
               (not (eval-constraint-alist new-calist env))))
    :hints(("Goal" :in-theory (e/d (eval-constraint-alist)
                                   (eval-constraint-alist-in-terms-of-witness))
            :expand ((:free (a b) (eval-constraint-alist (cons a b) env))
                     ;; (eval-constraint-alist calist env)
                     ;; (:free (seen) (calist-remassocs calist seen))
                     )
            :induct (constraint-alist-assume-aig x calist keys-in))))

  (defthm constraint-alist-assume-aig-correct
    (b* (((mv ?contradictionp ?new-calist ?keys-out)
          (constraint-alist-assume-aig x calist keys-in)))
      (implies (and (eval-constraint-alist calist env)
                    (not contradictionp))
               (equal (eval-constraint-alist new-calist env)
                      (acl2::aig-eval x env))))
    :hints(("Goal" :in-theory (e/d (eval-constraint-alist
                                    acl2::aig-eval)
                                   (eval-constraint-alist-in-terms-of-witness))
            :expand ((:free (a b) (eval-constraint-alist (cons a b) env)))
            :induct (constraint-alist-assume-aig x calist keys-in))))

  (defthm constraint-alist-assume-aig-contradictionp
    (b* (((mv ?contradictionp ?new-calist ?keys-out)
          (constraint-alist-assume-aig x calist keys-in)))
      (implies (and (eval-constraint-alist calist env)
                    (acl2::aig-eval x env))
               (not contradictionp)))
    :hints (("goal"
             :in-theory (enable acl2::aig-eval)
             ;; :in-theory (enable eval-constraint-alist acl2::aig-eval)
            :induct (constraint-alist-assume-aig x calist keys-in))))

  (local (defun ind (calist lst)
           (if (atom calist)
               lst
             (list (ind (cdr calist) lst)
                   (ind (cdr calist) (cons (caar calist) lst))))))

  (local (defthm set-equiv-of-cons-redundant
           (implies (member k x)
                    (acl2::set-equiv (cons k x) x))))

  (defthm remassocs-of-shrink-when-not-present
    (implies (not (calist-lookup k calist))
             (equal (calist-remassocs (shrink-constraint-alist calist)
                                      (cons k lst))
                    (calist-remassocs (shrink-constraint-alist calist)
                                      lst)))
    :hints(("Goal"
            :expand ((shrink-constraint-alist calist)
                     (:free (a b lst) (calist-remassocs (cons a b) lst))
                     (:free (lst) (calist-remassocs nil lst)))
            :induct (ind calist lst))))

  (defthm constraint-alist-delete-keys-of-assume-aig
    (b* (((mv ?contradictionp ?new-calist ?keys-out)
          (constraint-alist-assume-aig x calist keys-in)))
      (equal (calist-remassocs (shrink-constraint-alist new-calist) keys-out)
             (calist-remassocs (shrink-constraint-alist calist) keys-in)))
    :hints(("Goal" :in-theory (enable ;; calist-remassocs
                                      shrink-constraint-alist)
            :expand ((:free (a b lst) (calist-remassocs (cons a b) lst)))
            :induct (constraint-alist-assume-aig x calist keys-in))))


  (defthm dependencies-of-constraint-alist-assume-aig
    (b* (((mv ?contradictionp ?new-calist ?keys-out)
          (constraint-alist-assume-aig x calist keys-in)))
      (implies (and (not (set::in (aig-var-fix k) (acl2::aig-vars x)))
                    (not (constr-alist-depends-on k calist)))
               (not (constr-alist-depends-on k new-calist))))
    :hints(("Goal" :in-theory (e/d ()
                                   ((:d constraint-alist-assume-aig)
                                    acl2::subsetp-car-member
                                    acl2::aig-vars
                                    set::in set::subset set::union))
            :induct (constraint-alist-assume-aig x calist keys-in)
            :expand ((:free (a b)
                      (constr-alist-depends-on k (cons a b)))
                     (acl2::aig-vars x)
                     (constraint-alist-assume-aig x calist keys-in))))))


(define calist-equiv (x y)
  :enabled t
  (equal (shrink-constraint-alist x) (shrink-constraint-alist y))
  ///
  (defequiv calist-equiv)
  (defmacro def-calist-equiv-cong (resequiv call)
    ;; argument N must be x
    (let ((argnum (acl2::index-of 'x call)))
      `(encapsulate nil
         (local (defthm calist-cong-lemma
                  (,resequiv ,(update-nth
                               argnum `(shrink-constraint-alist x) call)
                             ,call)
                  :rule-classes nil))
         (local (in-theory '(calist-equiv)))
         (defcong calist-equiv ,resequiv ,call ,argnum
           :hints (("goal" :use ((:instance calist-cong-lemma)
                                 (:instance calist-cong-lemma
                                  (x x-equiv)))))))))

  (def-calist-equiv-cong equal (calist-lookup k x))
  (def-calist-equiv-cong equal (shrink-constraint-alist x))
  (def-calist-equiv-cong calist-equiv (calist-remassocs x keys))
  (def-calist-equiv-cong equal (eval-constraint-alist x env))
  (def-calist-equiv-cong equal (constraint-alist->aig x))
  (def-calist-equiv-cong equal (aig-under-constraint-alist a x))
  (def-calist-equiv-cong calist-equiv (constraint-alist-delete-keys keys x)))

;; Absstobj representation of pathcond: Concrete representation will include a
;; calist (aig mode) or bdd (bdd mode), and two integers, calist-len and
;; calist-nkeys (only used in aig mode).  The abstract representation will be
;; just a calist kept in normal form with calist-fix (aig mode) or bdd.

;; (defsection calist-fix
;;   (defchoose calist-fix (fix) (x)
;;     (calist-equiv fix x)
;;     :strengthen t)

;;   (defthm calist-fix-fixes
;;     (calist-equiv (calist-fix x) x)
;;     :hints (("goal" :use ((:instance calist-fix (fix x))))))

;;   (defcong calist-equiv equal (calist-fix x) 1
;;     :hints (("goal" :use ((:instance calist-fix (acl2::x1 x-equiv)))))))


(defstobj hyp$c
  (hyp-calist :type t)
  (calist-len :type (integer 0 *) :initially 0)
  (calist-nkeys :type (integer 0 *) :initially 0))

(define maybe-shrink-hyp$c (hyp$c)
  (if (< (* 2 (calist-nkeys hyp$c)) (calist-len hyp$c))
      (b* ((hyp$c (update-hyp-calist (shrink-constraint-alist (hyp-calist hyp$c)) hyp$c)))
        (update-calist-len (calist-nkeys hyp$c) hyp$c))
    hyp$c)
  ///
  (defthm maybe-shrink-hyp$c-preserves-calist-equiv
    (calist-equiv (nth 0 (maybe-shrink-hyp$c hyp$c))
                  (nth 0 hyp$c))))

(define bfr-hyp-equiv (hyp1 hyp2)
  :verify-guards nil
  (bfr-case
   :bdd (equal hyp1 hyp2)
   :aig (calist-equiv hyp1 hyp2))
  ///
  (defequiv bfr-hyp-equiv))

(define bfr-hyp-fix (hyp)
  (bfr-case
   :bdd hyp
   :aig (shrink-constraint-alist hyp))
  ///
  (defcong bfr-hyp-equiv equal (bfr-hyp-fix hyp) 1
    :hints(("Goal" :in-theory (enable bfr-hyp-equiv))))
  (defthm bfr-hyp-equiv-of-bfr-hyp-fix
    (bfr-hyp-equiv (bfr-hyp-fix hyp) hyp)
    :hints(("Goal" :in-theory (enable bfr-hyp-equiv))))

  (defthmd bfr-hyp-equiv-in-terms-of-bfr-hyp-fix
    (equal (bfr-hyp-equiv hyp1 hyp2)
           (equal (bfr-hyp-fix hyp1) (bfr-hyp-fix hyp2)))
    :hints(("Goal" :in-theory (enable bfr-hyp-equiv))))

  (defthm bfr-hyp-fix-idempotent
    (equal (bfr-hyp-fix (bfr-hyp-fix x))
           (bfr-hyp-fix x))))




;; Make-event to automatically introduce the events for the bfr-hyp-fix congruence
(defun hyp-congruences-fn (fn hints pres-hints hyp-fix-hints retval world)
  (declare (xargs :mode :program))
  (b* ((formals (formals fn world))
       (stobjs-out (stobjs-out fn world))
       (preserves-thm (intern-in-package-of-symbol
                       (concatenate 'string (symbol-name fn)
                                    "-PRESERVES-HYP")
                       fn))
       (hyp-fix-thm (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name fn)
                                  "-OF-BFR-HYP-FIX")
                     fn))
       (hyp-var (cond ((member 'hyp formals) 'hyp)
                      ((member 'pathcond formals) 'pathcond)
                      ((member 'hyp$a formals) 'hyp$a)
                      ((member 'constr formals) 'constr)
                      (t (er hard? 'hyp-congruences "~x0 does not appear to take a hyp as an argument~%"))))
       (hyp-var-equiv (intern-in-package-of-symbol
                       (concatenate 'string (symbol-name hyp-var) "-EQUIV")
                       hyp-var))
       (out-idx (or retval (acl2::index-of hyp-var stobjs-out))))
    `(progn
       ,@(and out-idx
              `((defthm ,preserves-thm
                  (equal (mv-nth ,out-idx (,fn . ,formals))
                         (bfr-hyp-fix ,hyp-var))
                  :hints ,(or pres-hints hints))))

       (defthm ,hyp-fix-thm
         (equal (,fn . ,(subst `(bfr-hyp-fix ,hyp-var) hyp-var formals))
                (,fn . ,formals))
         :hints ,(or hyp-fix-hints hints))

       (defcong bfr-hyp-equiv equal (,fn . ,formals) ,(+ 1 (acl2::index-of hyp-var formals))
         :hints (("goal" :in-theory '(bfr-hyp-equiv-in-terms-of-bfr-hyp-fix)
                  :use ((:instance ,hyp-fix-thm)
                        (:instance ,hyp-fix-thm (,hyp-var ,hyp-var-equiv)))))))))


(defmacro def-hyp-congruence (fn &key hints pres-hints hyp-fix-hints retval)
  `(make-event
    (hyp-congruences-fn ',fn ',hints ',pres-hints ',hyp-fix-hints ',retval (w state))))



;; (define bfr-hyp-eval$c (hyp$c env)
;;   (bfr-case
;;    :bdd (acl2::eval-bdd (hyp-calist hyp$c) env)
;;    :aig (eval-constraint-alist (hyp-calist hyp$c) env)))

(define bfr-hyp-eval (hyp env)
  (bfr-case
   :bdd (bfr-eval hyp env)
   :aig (eval-constraint-alist hyp env))
  ///
  (def-hyp-congruence bfr-hyp-eval
    :hints(("Goal" :in-theory (e/d (bfr-hyp-equiv bfr-hyp-fix) (calist-equiv))))))

(define bfr-hyp-init$c (hyp$c)
  (bfr-case
   :bdd (update-hyp-calist t hyp$c)
   :aig (b* ((hyp$c (update-hyp-calist nil hyp$c))
             (hyp$c (update-calist-len 0 hyp$c)))
          (update-calist-nkeys 0 hyp$c))))

(define bfr-constr-init ()
  (bfr-case :bdd t :aig nil)
  ///
  (in-theory (disable (bfr-constr-init)))
  (defthm eval-of-bfr-constr-init
    (equal (bfr-hyp-eval (bfr-constr-init) env) t)
    :hints(("Goal" :in-theory (enable bfr-hyp-eval)))))

(define bfr-hyp-init$a (hyp$a)
  (declare (ignore hyp$a))
  (bfr-case
   :bdd t
   :aig (shrink-constraint-alist nil))
  ///
  (defthm bfr-hyp-init-norm
    (implies (syntaxp (not (Equal hyp$a ''nil)))
             (equal (bfr-hyp-init$a hyp$a)
                    (bfr-hyp-init$a nil))))

  (defthm eval-of-bfr-hyp-init$a
    (equal (bfr-hyp-eval (bfr-hyp-init$a hyp$a) env) t)
    :hints(("Goal" :in-theory (enable bfr-hyp-eval)))))



(define bfr-assume$c (x hyp$c)
  :returns (mv contradictionp new-hyp undo-info)
  (bfr-case
   :bdd (b* ((orig (hyp-calist hyp$c))
             (and (acl2::q-and x orig))
             (hyp$c (update-hyp-calist and hyp$c)))
          (mv (not and) hyp$c orig))
   :aig (b* (((mv contra hyp keys)
              (constraint-alist-assume-aig x (hyp-calist hyp$c) nil))
             (hyp$c (update-hyp-calist hyp hyp$c))
             (nkeys (len keys))
             (hyp$c (update-calist-len (+ nkeys (calist-len hyp$c)) hyp$c))
             (hyp$c (update-calist-nkeys (+ nkeys (calist-nkeys hyp$c)) hyp$c))
             (hyp$c (maybe-shrink-hyp$c hyp$c)))
          (mv contra hyp$c keys))))

(define bfr-constr-assume (x constr)
  :guard-hints (("goal" :in-theory (enable bfr-binary-and)))
  (bfr-case
   :bdd (b* ((and (mbe :logic (bfr-and x constr)
                       :exec (acl2::q-and x constr))))
          (mv (not and) and constr))
   :aig (b* (((mv contra constr keys)
              (constraint-alist-assume-aig x constr nil)))
          (mv contra constr keys)))
  ///

  (defthm bfr-constr-assume-correct ;; contradictionp
    (b* (((mv ?contradictionp ?new-hyp ?undo-info)
          (bfr-constr-assume x hyp)))
      (implies (and (acl2::rewriting-negative-literal
                     `(mv-nth '0 (bfr-constr-assume ,x ,hyp)))
                    (bfr-hyp-eval hyp env))
               (iff contradictionp
                    (and (not (bfr-eval x env))
                         (hide contradictionp)))))
    :hints(("Goal" :in-theory (enable bfr-hyp-eval
                                      bfr-eval
                                      bfr-binary-and))
           (and stable-under-simplificationp
                '(:use ((:instance acl2::eval-bdd-of-q-and
                         (x hyp) (y x) (values env)))
                  :expand ((:free (x) (hide x)))
                  :in-theory (disable acl2::eval-bdd-of-q-and)))))

  (defthm bfr-constr-assume->hyp-correct
    (b* (((mv ?contradictionp ?new-hyp ?undo-info)
          (bfr-constr-assume x hyp)))
      (implies (and (bfr-hyp-eval hyp env)
                    (not contradictionp))
               (equal (bfr-hyp-eval new-hyp env)
                      (bfr-eval x env))))
    :hints(("Goal" :in-theory (enable bfr-hyp-eval
                                      bfr-eval))))

    ;; :hints(("Goal" :in-theory (enable bfr-hyp-eval
    ;;                                   bfr-eval))
    ;;        (and stable-under-simplificationp
    ;;             '(:use ((:instance acl2::eval-bdd-of-q-and
    ;;                      (x hyp) (y x) (values env)))
    ;;               :expand ((:free (x) (hide x)))
    ;;               :in-theory (disable acl2::eval-bdd-of-q-and)))))

  (defthm bfr-constr-assume-false
    (b* (((mv ?contradictionp ?new-hyp ?undo-info)
          (bfr-constr-assume x hyp)))
      (implies (and (acl2::rewriting-positive-literal
                     `(bfr-hyp-eval (mv-nth '1 (bfr-constr-assume ,x ,hyp)) ,env))
                    (bfr-hyp-eval hyp env))
               (equal (bfr-hyp-eval new-hyp env)
                      (or (bfr-eval x env)
                          (hide (bfr-hyp-eval new-hyp env))))))
    :hints (("goal" :expand ((:free (x) (hide x)))
             :in-theory (disable bfr-constr-assume))
            (and stable-under-simplificationp
                 '(:expand nil
                   :cases ((mv-nth 0 (bfr-constr-assume x hyp))))))))

(define bfr-assume$a (x hyp$a)
  (b* (((mv contra constr undo) (bfr-constr-assume x hyp$a)))
    (mv contra (bfr-hyp-fix constr) undo))
  ;; (bfr-case
  ;;  :bdd (b* ((and (acl2::q-and x hyp$a)))
  ;;         (mv (not and) and hyp$a))
  ;;  :aig (b* (((mv contra hyp$a keys)
  ;;             (constraint-alist-assume-aig x hyp$a nil)))
  ;;         (mv contra (shrink-constraint-alist hyp$a) keys)))
  ///
  (def-hyp-congruence bfr-assume$a
    :hints(("Goal" :in-theory (enable bfr-hyp-fix
                                      bfr-constr-assume))))

  (defthm bfr-assume-correct ;; contradictionp
    (b* (((mv ?contradictionp ?new-hyp ?undo-info)
          (bfr-assume$a x hyp)))
      (implies (and (acl2::rewriting-negative-literal
                     `(mv-nth '0 (bfr-assume$a ,x ,hyp)))
                    (bfr-hyp-eval hyp env))
               (iff contradictionp
                    (and (not (bfr-eval x env))
                         (hide contradictionp)))))
    :hints (("goal" :expand ((:free (x) (hide x))))))

  (defthm bfr-assume->hyp-correct
    (b* (((mv ?contradictionp ?new-hyp ?undo-info)
          (bfr-assume$a x hyp)))
      (implies (and (bfr-hyp-eval hyp env)
                    (not contradictionp))
               (equal (bfr-hyp-eval new-hyp env)
                      (bfr-eval x env)))))

    ;; :hints(("Goal" :in-theory (enable bfr-hyp-eval
    ;;                                   bfr-eval))
    ;;        (and stable-under-simplificationp
    ;;             '(:use ((:instance acl2::eval-bdd-of-q-and
    ;;                      (x hyp) (y x) (values env)))
    ;;               :expand ((:free (x) (hide x)))
    ;;               :in-theory (disable acl2::eval-bdd-of-q-and)))))

  (defthm bfr-assume-false
    (b* (((mv ?contradictionp ?new-hyp ?undo-info)
          (bfr-assume$a x hyp)))
      (implies (and (acl2::rewriting-positive-literal
                     `(bfr-hyp-eval (mv-nth '1 (bfr-assume$a ,x ,hyp)) ,env))
                    (bfr-hyp-eval hyp env))
               (equal (bfr-hyp-eval new-hyp env)
                      (or (bfr-eval x env)
                          (hide (bfr-hyp-eval new-hyp env))))))
    :hints (("goal" :expand ((:free (x) (hide x)))))))


(define bfr-unassume$c (hyp$c undo-info)
  (bfr-case
   :bdd (update-hyp-calist undo-info hyp$c) ;; old hyp
   :aig (b* ((hyp (hyp-calist hyp$c))
             (new-hyp (constraint-alist-delete-keys undo-info ;; added keys
                                                    hyp))
             (hyp$c (update-hyp-calist new-hyp hyp$c))
             (nkeys (len undo-info))
             (hyp$c (update-calist-len (+ nkeys (calist-len hyp$c)) hyp$c))
             (hyp$c (update-calist-nkeys (max 0 (- (calist-nkeys hyp$c) nkeys)) hyp$c)))
          (maybe-shrink-hyp$c hyp$c))))

(define bfr-unassume$a (hyp$a undo-info)
  (bfr-case
   :bdd undo-info ;; old hyp
   :aig (shrink-constraint-alist
         (constraint-alist-delete-keys undo-info
                                       hyp$a)))

  ///
  (def-hyp-congruence bfr-unassume$a
    :hints(("Goal" :in-theory (enable bfr-hyp-fix))))

  (local (defthm calist-remassocs-nil-of-true-list
           (implies (alistp x)
                    (equal (calist-remassocs x nil) x))
           :hints(("Goal" :in-theory (enable calist-remassocs)))))

  (local (defthm alistp-of-calist-remassocs
           (implies (alistp x)
                    (alistp (calist-remassocs x seen)))
           :hints(("Goal" :in-theory (enable calist-remassocs)))))

  (local (defthm alistp-of-shrink-constraint-alist
           (alistp (shrink-constraint-alist x))
           :hints(("Goal" :in-theory (enable shrink-constraint-alist)))))

  ;; (local (defthm calist-remassocs-nil-of-shrink
  ;;          (equal (calist-remassocs (shrink-constraint-alist hyp) nil)
  ;;                 (shrink-constraint-alist hyp))
  ;;          :hints(("Goal" :in-theory (enable calist-remassocs)))))

  (defthm bfr-unassume-of-assume
    (b* (((mv ?contradictionp ?new-hyp ?undo-info)
          (bfr-assume$a x hyp)))
      (equal (bfr-unassume$a new-hyp undo-info)
             (bfr-hyp-fix hyp)))
    :hints(("Goal" :in-theory (enable bfr-assume$a
                                      bfr-constr-assume
                                      bfr-hyp-fix)))))

(define hyp-fix$c (x hyp$c)
  (bfr-case
   :bdd (if (not (hyp-calist hyp$c))
            (and x t)
          (let ((and (acl2::q-and x (hyp-calist hyp$c))))
            (if and
                (if (hqual and (hyp-calist hyp$c))
                    t
                  x)
              nil)))
   :aig (aig-under-constraint-alist x (hyp-calist hyp$c))))

(define bfr-constr-fix (x hyp$a)
  (bfr-case
   :bdd (if (not hyp$a)
            (and x t)
          (let ((and (acl2::q-and x hyp$a)))
            (if and
                (if (hqual and hyp$a)
                    t
                  x)
              nil)))
   :aig (aig-under-constraint-alist x hyp$a))
  ///
  (def-hyp-congruence bfr-constr-fix
    :hints(("Goal" :in-theory (e/d (bfr-hyp-equiv bfr-hyp-fix) (calist-equiv)))))

  (defthm bfr-constr-fix-correct
    (implies (bfr-hyp-eval hyp env)
             (equal (bfr-eval (bfr-constr-fix x hyp) env)
                    (bfr-eval x env)))
    :hints(("Goal" :in-theory (enable bfr-hyp-eval bfr-eval))
           (and stable-under-simplificationp
                '(:use ((:instance acl2::eval-bdd-of-q-and
                         (x hyp) (y x) (values env)))
                  :in-theory (disable acl2::eval-bdd-of-q-and)))))

  (defthm bfr-depends-on-of-bfr-constr-fix
    (implies (not (bfr-depends-on k x))
             (not (bfr-depends-on k (bfr-constr-fix x hyp$a)))))

  (defthm pbfr-depends-on-of-bfr-constr-fix
    (implies (not (pbfr-depends-on k p x))
             (not (pbfr-depends-on k p (bfr-constr-fix x hyp$a)))))

  (defthm bfr-constr-fix-idempotent
    (equal (bfr-constr-fix (bfr-constr-fix x hyp) hyp)
           (bfr-constr-fix x hyp)))

  (defthm bfr-constr-fix-of-t-and-nil
    (and (equal (bfr-constr-fix t hyp) t)
         (equal (bfr-constr-fix nil hyp) nil))))

(define bfr-hyp->bfr$c (hyp$c)
  (bfr-case
   :bdd (hyp-calist hyp$c)
   :aig (constraint-alist->aig (hyp-calist hyp$c))))

(define bfr-constr->bfr (hyp$a)
  (bfr-case
   :bdd hyp$a
   :aig (constraint-alist->aig hyp$a))
  ///
  (def-hyp-congruence bfr-constr->bfr
    :hints(("Goal" :in-theory (enable bfr-hyp-fix))))

  (defthm bfr-eval-of-bfr-constr->bfr
    (equal (bfr-eval (bfr-constr->bfr hyp) env)
           (bfr-hyp-eval hyp env))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable bfr-eval bfr-hyp-eval))))))

(define bfr-constr-depends-on (k p hyp$a)
  :verify-guards nil
  (bfr-case
   :bdd (pbfr-depends-on k p hyp$a)
   :aig (constr-alist-depends-on k hyp$a))
  ///
  (def-hyp-congruence bfr-constr-depends-on
    :hints(("Goal" :in-theory (enable bfr-hyp-fix))))

  (defthm bfr-constr-depends-on-correct
    (implies (and (not (bfr-constr-depends-on k p x))
                  (bfr-eval p env)
                  (bfr-eval p (bfr-set-var k v env)))
             (equal (bfr-hyp-eval x (bfr-param-env p (bfr-set-var k v env)))
                    (bfr-hyp-eval x (bfr-param-env p env))))
    :hints(("Goal" :in-theory (enable bfr-hyp-eval))
           (and stable-under-simplificationp
                '(:in-theory (e/d (bfr-eval bfr-set-var
                                            bfr-param-env
                                            bfr-varname-fix)
                                  (nfix))))))

  (defthm bfr-constr-depends-on-of-bfr-constr-assume
    (implies (and (not (bfr-constr-depends-on k p x))
                  (not (pbfr-depends-on k p a)))
             (not (bfr-constr-depends-on
                   k p (mv-nth 1 (bfr-constr-assume a x)))))
    :hints(("Goal" :in-theory (enable bfr-constr-assume
                                      bfr-hyp-fix))
           (and stable-under-simplificationp
                '(:in-theory (enable pbfr-depends-on
                                     bfr-depends-on
                                     bfr-from-param-space
                                     bfr-varname-fix)))))

  (defthm pbfr-depends-on-of-bfr-constr->bfr
    (implies (not (bfr-constr-depends-on k p x))
             (not (pbfr-depends-on k p (bfr-constr->bfr x))))
    :hints(("Goal" :in-theory (enable bfr-constr->bfr))
           (and stable-under-simplificationp
                '(:in-theory (e/d (pbfr-depends-on
                                   bfr-depends-on
                                   bfr-from-param-space
                                   bfr-varname-fix)
                                  (nfix))))))

  (defthm bfr-constr-depends-on-of-bfr-constr-init
    (not (bfr-constr-depends-on k p (bfr-constr-init)))
    :hints(("Goal" :in-theory (enable bfr-constr-init
                                      constr-alist-depends-on)))))


(define create-hyp$a ()
  :enabled t
  (bfr-case
   :bdd nil
   :aig (shrink-constraint-alist nil)))

(define hyp$ap (hyp$a)
  (equal hyp$a (bfr-hyp-fix hyp$a))
  ///
  (defthm bfr-hyp-fix-when-hyp$ap
    (implies (hyp$ap hyp)
             (equal (bfr-hyp-fix hyp) hyp))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))

(defun-nx hyp-corr (hyp$c hyp$a)
  (equal (bfr-hyp-fix (hyp-calist hyp$c)) hyp$a))

(encapsulate nil
  (local (in-theory (e/d (bfr-hyp-fix
                          bfr-hyp-init$c
                          bfr-assume$c
                          bfr-assume$a
                          bfr-binary-and
                          bfr-constr-assume
                          bfr-unassume$c
                          bfr-unassume$a
                          hyp$ap
                          hyp-fix$c
                          bfr-hyp-init$a
                          bfr-constr-fix
                          bfr-hyp->bfr$c
                          bfr-constr->bfr)
                         ((bfr-hyp-fix)
                          ;;acl2::nth-when-zp
                          nth update-nth))))
  (acl2::defabsstobj-events hyp
    :concrete hyp$c
    :recognizer (hyp-p :logic hyp$ap :exec hyp$cp)
    :creator (create-hyp :logic create-hyp$a :exec create-hyp$c)
    :corr-fn hyp-corr
    :exports
    ((bfr-hyp-init :logic bfr-hyp-init$a :exec bfr-hyp-init$c :protect t)
     (bfr-assume :logic bfr-assume$a :exec bfr-assume$c :protect t)
     (bfr-unassume :logic bfr-unassume$a :exec bfr-unassume$c :protect t)
     (hyp-fix :logic bfr-constr-fix :exec hyp-fix$c)
     (bfr-hyp->bfr :logic bfr-constr->bfr :exec bfr-hyp->bfr$c))))


(defmacro lbfr-hyp-fix (hyp)
  `(let* ((,hyp (mbe :logic (non-exec (bfr-hyp-fix ,hyp)) :exec ,hyp)))
     ,hyp))



;; (prove-congruences (bfr-equiv bfr-equiv) hyp-fix)

(define hyp-fixedp (x hyp)
  (hqual (hyp-fix x hyp) x)
  ///
  (def-hyp-congruence hyp-fixedp)

  (defthm hyp-fixedp-of-hyp-fix
    (hyp-fixedp (bfr-constr-fix x hyp) hyp)
    :hints(("Goal" :in-theory (enable hyp-fix))))

  (defthm hyp-fix-of-hyp-fixedp
    (implies (hyp-fixedp x hyp)
             (equal (bfr-constr-fix x hyp) x))))

;; (prove-congruences (bfr-equiv bfr-equiv) hyp-fixedp)

(define true-under-hyp (x hyp)
  (declare (ignorable hyp))
  (eq x t)
  ///
  (def-hyp-congruence true-under-hyp)

  (defthmd true-under-hyp-point
    (implies (and (true-under-hyp x hyp)
                  (hyp-fixedp x hyp)
                  (bfr-hyp-eval hyp v))
             (bfr-eval x v))))

(define false-under-hyp (x hyp)
  (declare (ignorable hyp))
  (eq x nil)
  ///
  (def-hyp-congruence false-under-hyp)

  (defthmd false-under-hyp-point
    (implies (and (false-under-hyp x hyp)
                  (hyp-fixedp x hyp)
                  (bfr-hyp-eval hyp v))
             (not (bfr-eval x v)))))


(defmacro hf (x)
  `(hyp-fix ,x hyp))

(defmacro th (x)
  `(true-under-hyp ,x hyp))

(defmacro fh (x)
  `(false-under-hyp ,x hyp))

(add-untranslate-pattern (true-under-hyp ?x hyp) (th ?x))
(add-untranslate-pattern (false-under-hyp ?x hyp) (fh ?x))
(add-untranslate-pattern (hyp-fix ?x hyp) (hf ?x))


(acl2::defstobj-clone pathcond hyp :suffix "-PATHCOND")

(add-bfr-fn-pat bfr-constr-fix)
