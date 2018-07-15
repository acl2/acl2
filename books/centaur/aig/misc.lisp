; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
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


(in-package "ACL2")

(include-book "aig-base")
(include-book "centaur/misc/equal-sets" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "misc/gentle" :dir :system)
(include-book "misc/hons-help" :dir :system)
(local (include-book "std/alists/alistp" :dir :system))
; (local (include-book "eval-restrict"))

;; (local (in-theory (disable append-of-nil)))


;; BOZO misplaced

(local (defthm true-listp-of-make-fal
         (implies (true-listp name)
                  (true-listp (make-fal al name)))))

(defthm make-fal-is-append
  (implies (alistp x)
           (equal (make-fal x y) (append x y))))

(defthm aig-eval-alist-append
  (equal (aig-eval-alist (append a b) env)
         (append (aig-eval-alist a env)
                 (aig-eval-alist b env))))





;; (defun faig-vars-pat (pat aigs)
;;   (if pat
;;       (if (atom pat)
;;           (list :signal pat
;;                 (aig-vars (car aigs))
;;                 (aig-vars (cdr aigs)))
;;         (cons (faig-vars-pat (car pat) (car aigs))
;;               (faig-vars-pat (cdr pat) (cdr aigs))))
;;     nil))


;; Extracts necessary variable assignments from an AIG by breaking down its
;; top-level AND structure to the negations/variables.  Any such leaf it
;; reaches which is a variable or negation implies an assignment.
(defun aig-extract-assigns (x)
  (declare (xargs :guard t
                  :verify-guards nil))
  (aig-cases
   x
   :true (mv nil nil)
   :false (mv nil nil)
   :var (mv (mbe :logic (set::insert x nil)
                 :exec (list x))
            nil)
   :inv (if (aig-var-p (car x))
            (mv nil (mbe :logic (set::insert (car x) nil)
                         :exec (list (car x))))
          (mv nil nil))
   :and (mv-let (trues1 falses1)
          (aig-extract-assigns (car x))
          (mv-let (trues2 falses2)
            (aig-extract-assigns (cdr x))
            (mv (set::union trues1 trues2)
                (set::union falses1 falses2))))))

(defthm aig-var-listp-aig-extract-assigns
  (mv-let (trues falses)
    (aig-extract-assigns x)
    (and (aig-var-listp trues)
         (aig-var-listp falses))))

(defthm setp-of-aig-extract-assigns
  (b* (((mv trues falses) (aig-extract-assigns x)))
    (and (set::setp trues)
         (set::setp falses))))

(verify-guards aig-extract-assigns
  :hints(("Goal" :in-theory (enable set::insert))))

(memoize 'aig-extract-assigns
         :condition '(and (not (aig-atom-p x)) (cdr x))
         :forget t)

(defthm aig-extract-assigns-member-impl
  (mv-let (trues falses)
    (aig-extract-assigns x)
    (and (implies (and (member-equal v trues)
                       (aig-eval x env))
                  (aig-eval v env))
         (implies (and (member-equal v falses)
                       (aig-eval x env))
                  (not (aig-eval v env)))))
  :rule-classes nil)


(defthm var-eval-extend-env
  (equal (aig-eval x (cons (cons v (aig-eval v env)) env))
         (aig-eval x env))
  :hints(("Goal" :in-theory (enable aig-env-lookup))))

(defthm aig-extract-assigns-extend-alist
  (mv-let (trues falses)
    (aig-extract-assigns x)
    (and (implies (and (member-equal v trues)
                       (aig-eval x env))
                  (equal (aig-eval y (cons (cons v t) env))
                         (aig-eval y env)))
         (implies (and (member-equal v falses)
                       (aig-eval x env))
                  (equal (aig-eval y (cons (cons v nil) env))
                         (aig-eval y env)))))
  :hints (("goal" :do-not-induct t
           :use (aig-extract-assigns-member-impl
                 (:instance var-eval-extend-env
                            (x y)))
           :in-theory (disable var-eval-extend-env))))

(define boolean-val-alistp (x)
  (if (atom x)
      (eq x nil)
    (and (consp (car x)) (booleanp (cdar x))
         (boolean-val-alistp (cdr x))))
  ///
  (defthmd aig-eval-alist-of-boolean-val-alistp
    (implies (boolean-val-alistp x)
             (equal (aig-eval-alist x env) x)))

  (defthm lookup-in-boolean-val-alist
    (implies (boolean-val-alistp x)
             (booleanp (cdr (hons-assoc-equal k x)))))

  (defthm alistp-when-boolean-val-alistp
    (implies (boolean-val-alistp x)
             (alistp x))
    :rule-classes :forward-chaining)

  (defthm boolean-val-alistp-of-append
    (implies (and (boolean-val-alistp x)
                  (boolean-val-alistp y))
             (boolean-val-alistp (append x y)))))

(local (in-theory (enable aig-eval-alist-of-boolean-val-alistp)))

(defun assign-var-list (vars val)
  (declare (xargs :guard t))
  (if (atom vars)
      nil
    (cons (cons (car vars) val)
          (assign-var-list (cdr vars) val))))

(defthm boolean-val-alistp-of-assign-var-list
  (implies (booleanp val)
           (boolean-val-alistp (assign-var-list vars val)))
  :hints(("Goal" :in-theory (enable boolean-val-alistp))))


(local
 (defthm aig-extract-assigns-assign-var-list1
   (mv-let (trues falses)
     (aig-extract-assigns x)
     (implies (aig-eval x env)
              (and (implies
                    (subsetp-equal vars trues)
                    (aig-eval x (append (assign-var-list vars t)
                                        env)))
                   (implies
                    (subsetp-equal vars falses)
                    (aig-eval x (append (assign-var-list vars nil)
                                        env))))))
   :hints ((and stable-under-simplificationp
                '(:induct (len vars) :in-theory (enable subsetp-equal))))
   :otf-flg t))

(defthm aig-extract-assigns-assign-var-list
  (mv-let (trues falses)
    (aig-extract-assigns x)
    (implies (aig-eval x env)
             (and (implies
                   (subsetp-equal vars trues)
                   (equal (aig-eval y (append (assign-var-list vars t)
                                              env))
                          (aig-eval y env)))
                  (implies
                   (subsetp-equal vars falses)
                   (equal (aig-eval y (append (assign-var-list vars nil)
                                              env))
                          (aig-eval y env))))))
  :hints ((and stable-under-simplificationp
               (not (cdr (car id))) ;; not under induction
               '(:induct (len vars) :in-theory (enable subsetp-equal)
                         :do-not-induct t)))
  :otf-flg t)

(defthm aig-extract-assigns-var-list-rw
  (mv-let (trues falses)
    (aig-extract-assigns x)
    (implies (aig-eval x env)
             (and (equal (aig-eval y (append (assign-var-list trues t)
                                             env))
                         (aig-eval y env))
                  (equal (aig-eval y (append (assign-var-list falses nil)
                                             env))
                         (aig-eval y env))))))


(defthm alistp-assign-var-list
  (alistp (assign-var-list vars val)))

(defthm aig-eval-alist-assign-var-list
  (equal (aig-eval-alist (assign-var-list vars val) env)
         (assign-var-list vars (aig-eval val env))))

(in-theory (disable assign-var-list))



(defun aig-extract-assigns-alist (x)
  (declare (xargs :guard t))
  (mv-let (trues falses)
    (aig-extract-assigns x)
    (make-fal (assign-var-list trues t)
              (make-fal (assign-var-list falses nil)
                        nil))))

(defthm boolean-val-alistp-of-aig-extract-assigns-alist
  (boolean-val-alistp (aig-extract-assigns-alist x)))

(local (defthm true-listp-of-aig-extract-assigns-alist
         (true-listp (aig-extract-assigns-alist x))))


(defthm alistp-aig-extract-assigns-alist
  (alistp (aig-extract-assigns-alist x)))

(defthm aig-eval-alist-aig-extract-assigns-alist
  (equal (aig-eval-alist (aig-extract-assigns-alist x) env)
         (aig-extract-assigns-alist x)))

(defthm assign-var-list-lookup
  (equal (hons-assoc-equal k (assign-var-list x v))
         (and (member k x)
              (cons k v)))
  :hints(("Goal" :in-theory (enable assign-var-list hons-assoc-equal member))))

(local (defthm hons-assoc-equal-of-append
         (equal (hons-assoc-equal k (append x y))
                (or (hons-assoc-equal k x)
                    (hons-assoc-equal k y)))))

(defthmd aig-extract-assigns-alist-lookup-boolean
  (booleanp (cdr (hons-assoc-equal k (aig-extract-assigns-alist x))))
  :hints(("Goal" :in-theory (enable aig-extract-assigns-alist)))
  :rule-classes :type-prescription)


(defthm aig-extract-assigns-restrict
;;   (implies (aig-eval x env)
;;            (aig-eval (aig-restrict x (aig-extract-assigns-alist x)) env))
  (implies (aig-eval x env)
           (equal (aig-eval y (append (aig-extract-assigns-alist x) env))
                  (aig-eval y env)))
  :hints (("goal" :do-not-induct t)))





(defun aig-extract-iterated-assigns-alist (x clk)
  (declare (Xargs :measure (nfix clk)
                   :guard (natp clk)))
  (let* ((al (aig-extract-assigns-alist x))
         (newx (aig-restrict x al)))
    (prog2$
     (clear-memoize-table 'aig-restrict)
     (if (or (hons-equal newx x) (zp clk))
         al
       (let* ((more (aig-extract-iterated-assigns-alist newx (1- clk))))
         (make-fal (flush-hons-get-hash-table-link al) more))))))

(defthm boolean-val-alistp-of-aig-extract-iterated-assigns-alist
  (boolean-val-alistp (aig-extract-iterated-assigns-alist x clk)))

(in-theory (disable aig-extract-assigns-alist))

(local (defthm true-listp-of-aig-extract-iterated-assigns-alist
         (true-listp (aig-extract-iterated-assigns-alist x clk))))

(defthm alistp-aig-extract-iterated-assigns
  (alistp (aig-extract-iterated-assigns-alist x clk)))

(defthm aig-eval-alist-extract-iterated-assigns
  (equal (aig-eval-alist (aig-extract-iterated-assigns-alist x clk) env)
         (aig-extract-iterated-assigns-alist x clk)))



(local
 (defun aig-extract-iterated-assigns-restrict-ind (x y clk)
   (declare (Xargs :measure (nfix clk)))
   (let* ((al (aig-extract-assigns-alist x))
          (newx (aig-restrict x al)))
     (if (or (hons-equal newx x) (zp clk))
         (list al y)
       (list (aig-extract-iterated-assigns-restrict-ind newx y (1- clk))
             (aig-extract-iterated-assigns-restrict-ind newx x (1- clk)))))))

(defthm aig-extract-iterated-assigns-restrict
  ;;   (implies (aig-eval x env)
  ;;            (aig-eval (aig-restrict x (aig-extract-iterated-assigns-alist
  ;;                                       x clk))
  ;;                      env))
  (implies (aig-eval x env)
           (equal (aig-eval y (append (aig-extract-iterated-assigns-alist x clk)
                                      env))
                  (aig-eval y env)))
  :hints (("goal" :induct (aig-extract-iterated-assigns-restrict-ind x y clk))))

(defthm aig-extract-iterated-assigns-special-case
  (implies (aig-eval x nil)
           (equal (aig-eval y (aig-extract-iterated-assigns-alist x clk))
                  (aig-eval y nil)))
  :hints (("goal" :use ((:instance aig-extract-iterated-assigns-restrict
                                   (env nil))))))

(defthmd aig-extract-iterated-assigns-alist-lookup-boolean
  (booleanp (cdr (hons-assoc-equal k (aig-extract-iterated-assigns-alist x clk))))
  :rule-classes :type-prescription)


(memoize 'aig-extract-iterated-assigns-alist
         :recursive nil)

(defthmd lookup-in-aig-extract-assigns
  (b* (((mv trues falses) (aig-extract-assigns x)))
    (and (implies (and (member v trues)
                       (aig-eval x env))
                  (aig-env-lookup v env))
         (implies (and (member v falses)
                       (aig-eval x env))
                  (not (aig-env-lookup v env)))))
  :hints(("Goal" :in-theory (enable aig-extract-assigns))))


(defthmd lookup-in-aig-extract-assigns-alist
  (implies (and (hons-assoc-equal v (aig-extract-assigns-alist x))
                (aig-eval x env))
           (iff (aig-env-lookup v env)
                (cdr (hons-assoc-equal v (aig-extract-assigns-alist x)))))
  :hints(("Goal" :in-theory (e/d (aig-extract-assigns-alist)
                                 (aig-env-lookup
                                  lookup-in-aig-extract-assigns))
          :use lookup-in-aig-extract-assigns)))

(defthmd lookup-in-aig-extract-iterated-assigns-alist
  (implies (and (hons-assoc-equal v (aig-extract-iterated-assigns-alist x n))
                (aig-eval x env))
           (iff (aig-env-lookup v env)
                (cdr (hons-assoc-equal v (aig-extract-iterated-assigns-alist x n)))))
  :hints(("Goal" :in-theory (e/d (aig-extract-iterated-assigns-alist
                                  lookup-in-aig-extract-assigns-alist)
                                 (aig-env-lookup))
          :induct (aig-extract-iterated-assigns-alist x n))))

