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
   :var (mv (list x) nil)
   :inv (if (and (atom (car x))
                 (not (booleanp (car x))))
            (mv nil (list (car x)))
          (mv nil nil))
   :and (mv-let (trues1 falses1)
          (aig-extract-assigns (car x))
          (mv-let (trues2 falses2)
            (aig-extract-assigns (cdr x))
            (mv (hons-alphorder-merge trues1 trues2)
                (hons-alphorder-merge falses1 falses2))))))

(defthm atom-listp-aig-extract-assigns
  (mv-let (trues falses)
    (aig-extract-assigns x)
    (and (atom-listp trues)
         (atom-listp falses))))

(verify-guards aig-extract-assigns)

(memoize 'aig-extract-assigns
         :condition '(and (consp x) (cdr x))
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

(defun assign-var-list (vars val)
  (declare (xargs :guard t))
  (if (atom vars)
      nil
    (cons (cons (car vars) val)
          (assign-var-list (cdr vars) val))))

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
  :hints(("Goal" :in-theory (enable aig-extract-iterated-assigns-alist
                                    aig-extract-assigns-alist-lookup-boolean)))
  :rule-classes :type-prescription)


(memoize 'aig-extract-iterated-assigns-alist
         :recursive nil)
