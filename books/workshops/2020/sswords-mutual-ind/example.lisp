; Copyright (C) 2020 Centaur Technology
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


; This contains the examples for the paper
;   "Generating Mutually Inductive Theorems from Concise Descriptions"
; except for the examples dealing with the FGL rewriter, which are located
; in the ACL2 community book
;    centaur/fgl/interp.lisp.

; You may certify this book using "cert.pl example.lisp"
; or you may interactively load it if you first do:
;   (include-book "std/portcullis" :dir :system)


(in-package "STD")

(include-book "tools/flag" :dir :system)
(include-book "std/util/defines" :dir :system)


(defmacro defexample (name &rest events)
  (declare (ignore name))
  `(encapsulate nil
     (local
      (progn . ,events))))

(defevaluator ev-term ev-termlist nil :namedp t)

(in-theory (enable ev-term-of-fncall-args))

(defun ev-alist (x env)
  (if (atom x)
      nil
    (cons (cons (caar x) (ev-term (cdar x) env))
          (ev-alist (cdr x) env))))

(defthm lookup-in-ev-alist
  (implies k
           (equal (assoc-equal k (ev-alist x env))
                  (let ((orig (assoc-equal k x)))
                    (and orig
                         (cons k (ev-term (cdr orig) env)))))))


(defexample subst-term-defun
  (mutual-recursion
   (defun subst-term (x alist)
     (cond ((not x) nil)
           ((symbolp x) ;; variable
            (cdr (assoc-equal x alist)))
           ((atom x) nil) ;; malformed
           ((eq (car x) 'quote) x)
           (t ;; function or lambda call
            (cons (car x)
                  (subst-termlist (cdr x) alist)))))
   (defun subst-termlist (x alist)
     (if (atom x)
         nil
       (cons (subst-term (car x) alist)
             (subst-termlist (cdr x) alist)))))


  (defexample subst-term-custom-method
    (defun subst-term-ind (x)
      (and (consp x)
           (list (subst-term-ind (car x))
                 (subst-term-ind (cdr x)))))

    (defthm ev-term/list-of-subst-term/list
      (and (equal (ev-term (subst-term x alist) env)
                  (ev-term x (ev-alist alist env)))
           (equal (ev-termlist (subst-termlist x alist) env)
                  (ev-termlist x (ev-alist alist env))))
      :hints (("goal" :induct (subst-term-ind x)))))



  (defexample subst-term-flag-method

    (defun subst-term-flag (flag x alist)
      (case flag
        (subst-term
         (cond ((not x) nil)
               ((symbolp x) ;; variable
                (cdr (assoc-equal x alist)))
               ((atom x) nil) ;; malformed
               ((eq (car x) 'quote) x)
               (t ;; function or lambda call
                (cons (car x)
                      (subst-term-flag 'subst-termlist (cdr x) alist)))))
        (t ;; subst-termlist
         (if (atom x)
             nil
           (cons (subst-term-flag 'subst-term (car x) alist)
                 (subst-term-flag 'subst-termlist (cdr x) alist))))))

    (defthm subst-term-flag-equals-subst-term
      (equal (subst-term-flag flag x alist)
             (case flag
               (subst-term
                (subst-term x alist))
               (t
                (subst-termlist x alist)))))

    (defthm ev-term/list-of-subst-term/list-lemma
      (case flag
        (subst-term (equal (ev-term (subst-term x alist) env)
                           (ev-term x (ev-alist alist env))))
        (t ;; subst-termlist
         (equal (ev-termlist (subst-termlist x alist) env)
                (ev-termlist x (ev-alist alist env)))))
      :hints (("goal" :induct (subst-term-flag flag x alist)))
      :rule-classes nil)

    (defthm ev-term-of-subst-term
      (equal (ev-term (subst-term x alist) env)
             (ev-term x (ev-alist alist env)))
      :hints (("goal" :use ((:instance ev-term/list-of-subst-term/list-lemma
                             (flag 'subst-term))))))

    (defthm ev-termlist-of-subst-termlist
      (equal (ev-termlist (subst-termlist x alist) env)
             (ev-termlist x (ev-alist alist env)))
      :hints (("goal" :use ((:instance ev-term/list-of-subst-term/list-lemma
                             (flag 'subst-termlist)))))))


  (defexample subst-term-make-flag

    (flag::make-flag subst-term-flag subst-term)

    (defthm-subst-term-flag
      (defthm ev-term-of-subst-term
        (equal (ev-term (subst-term x alist) env)
               (ev-term x (ev-alist alist env)))
        :flag subst-term)
      (defthm ev-termlist-of-subst-termlist
        (equal (ev-termlist (subst-termlist x alist) env)
               (ev-termlist x (ev-alist alist env)))
        :flag subst-termlist))))


(defund pseudo-term-substp  (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (symbolp (caar x))
         (pseudo-termp (cdar x))
         (pseudo-term-substp (cdr x)))))

(defthm alistp-when-pseudo-term-substp
  (implies (pseudo-term-substp x)
           (alistp x))
  :hints(("Goal" :in-theory (enable pseudo-term-substp))))

(defthm pseudo-termp-lookup-in-pseudo-term-substp
  (implies (pseudo-term-substp x)
           (pseudo-termp (cdr (assoc-equal k x))))
  :hints(("Goal" :in-theory (enable pseudo-term-substp))))

(defthm consp-assoc-equal-iff
  (implies k
           (iff (consp (assoc-equal k x))
                (assoc-equal k x))))

(defthm pseudo-termp-of-cons-car
  (implies (and (pseudo-termp x)
                (consp x)
                (not (equal (car x) 'quote))
                (pseudo-term-listp args)
                (equal (len args) (len (cdr x))))
           (pseudo-termp (cons (car x) args)))
  :hints(("Goal" :expand ((pseudo-termp x)))))


(defexample subst-term-defines
  
  (defines subst-term
    (define subst-term ((x pseudo-termp) (alist pseudo-term-substp))
      :returns (subst)
      (cond ((not x) nil)
            ((symbolp x) ;; variable
             (cdr (assoc-equal x alist)))
            ((atom x) nil) ;; malformed
            ((eq (car x) 'quote) x)
            (t ;; function or lambda call
             (cons (car x)
                   (subst-termlist (cdr x) alist)))))
    (define subst-termlist ((x pseudo-term-listp) (alist pseudo-term-substp))
      :returns (subst)
      (if (atom x)
          nil
        (cons (subst-term (car x) alist)
              (subst-termlist (cdr x) alist))))
    ///

    (defret-mutual ev-term-of-subst-term
      (defret ev-term-of-subst-term
        (equal (ev-term subst env)
               (ev-term x (ev-alist alist env)))
        :fn subst-term)
      (defret ev-termlist-of-subst-termlist
        (equal (ev-termlist subst env)
               (ev-termlist x (ev-alist alist env)))
        :fn subst-termlist))))


;; (defexample term-vars
;;   (mutual-recursion
;;    (defun term-vars-acc (x acc)
;;      (cond ((not x) acc)
;;            ((symbolp x) (add-to-set-eq x acc))
;;            ((atom x) acc)
;;            ((eq (car x) 'quote) acc)
;;            (t (termlist-vars-acc (cdr x) acc))))
;;    (defun termlist-vars-acc (x acc)
;;      (if (atom x)
;;          acc
;;        (termlist-vars-acc (cdr x) (term-vars-acc (car x) acc)))))

;;   (mutual-recursion
;;    (defun term-vars (x)
;;      (cond ((not x) nil)
;;            ((symbolp x) (list x))
;;            ((atom x) nil)
;;            ((eq (car x) 'quote) nil)
;;            (t (termlist-vars (cdr x)))))
;;    (defun termlist-vars (x)
;;      (if (atom x)
;;          nil
;;        (union-eq (termlist-vars (cdr x))
;;                  (term-vars (car x))))))

  

;;   (defthm member-equal-of-union-equal
;;     (iff (member-equal x (union-equal a b))
;;          (or (member-equal x a)
;;              (member-equal x b))))

;;   (defthm union-equal-associative
;;     (equal (union-equal (union-equal a b) c)
;;            (union-equal a (union-equal b c))))

;;   (defexample term-vars-acc-direct

;;     (flag::make-flag term-vars-acc-flag term-vars-acc)

;;     (defthm-term-vars-acc-flag
;;       (defthm term-vars-acc-is-term-vars
;;         (equal (term-vars-acc x acc)
;;                (union-eq (term-vars x) acc))
;;         :hints ('(:expand ((term-vars-acc x acc)
;;                            (term-vars x))))
;;         :flag term-vars-acc)
;;       (defthm termlist-vars-acc-is-termlist-vars
;;         (equal (termlist-vars-acc x acc)
;;                (union-eq (termlist-vars x) acc))
;;         :hints ('(:expand ((termlist-vars-acc x acc)
;;                            (termlist-vars x))))
;;         :flag termlist-vars-acc)))


;;   (defexample term-vars-acc-via-skolem

;;     (flag::make-flag term-vars-flag term-vars)

;;     (defun-sk term-vars-acc-is-term-vars-cond (x)
;;       (forall acc
;;               (equal (term-vars-acc x acc)
;;                      (union-eq (term-vars x) acc)))
;;       :rewrite :direct)

;;     (defun-sk termlist-vars-acc-is-termlist-vars-cond (x)
;;       (forall acc
;;               (equal (termlist-vars-acc x acc)
;;                      (union-eq (termlist-vars x) acc)))
;;       :rewrite :direct)

;;     (in-theory (disable term-vars-acc-is-term-vars-cond
;;                         termlist-vars-acc-is-termlist-vars-cond))
    
;;     (defthm-term-vars-flag
;;       (defthm term-vars-acc-is-term-vars-lemma
;;         (term-vars-acc-is-term-vars-cond x)
;;         :hints ((and stable-under-simplificationp
;;                      `(:expand (,(car (last clause))
;;                                 (term-vars x)
;;                                 (:free (acc) (term-vars-acc x acc))
;;                                 (:free (acc) (term-vars-acc nil acc))))))
;;         :flag term-vars
;;         :rule-classes nil)
;;       (defthm termlist-vars-acc-is-termlist-vars-lemma
;;         (termlist-vars-acc-is-termlist-vars-cond x)
;;         :hints ((and stable-under-simplificationp
;;                      `(:expand (,(car (last clause))
;;                                 (termlist-vars x)
;;                                 (:free (acc) (termlist-vars-acc x acc))))))
;;         :flag termlist-vars
;;         :rule-classes nil))

;;     (defthm term-vars-acc-is-term-vars
;;       (equal (term-vars-acc x acc)
;;              (union-eq (term-vars x) acc))
;;       :hints (("goal" :use term-vars-acc-is-term-vars-lemma)))

;;     (defthm termlist-vars-acc-is-termlist-vars
;;       (equal (termlist-vars-acc x acc)
;;              (union-eq (termlist-vars x) acc))
;;       :hints (("goal" :use termlist-vars-acc-is-termlist-vars-lemma)))))
  


(defexample remove-return-last-calls
  (defevaluator rl-ev rl-ev-list ((return-last x y z)) :namedp t)
  (in-theory (enable rl-ev-of-fncall-args))

  (mutual-recursion
   (defun remove-return-last-term (x)
     (cond ((atom x) x)
           ((eq (car x) 'quote) x)
           ((eq (car x) 'return-last)
            (remove-return-last-term (cadddr x)))
           ((consp (car x))
            ;;lambda
            `((lambda ,(cadar x)
                ,(remove-return-last-term (caddar x)))
               . ,(remove-return-last-termlist (cdr x))))
           (t (cons (car x) (remove-return-last-termlist (cdr x))))))
   (defun remove-return-last-termlist (x)
     (if (atom x)
         nil
       (cons (remove-return-last-term (car x))
             (remove-return-last-termlist (cdr x))))))

  (flag::make-flag remove-return-last-flag remove-return-last-term)

  (defun-sk remove-return-last-term-correct-cond (x)
    (forall env
            (equal (rl-ev (remove-return-last-term x) env)
                   (rl-ev x env)))
    :rewrite :direct)

  (defun-sk remove-return-last-termlist-correct-cond (x)
    (forall env
            (equal (rl-ev-list (remove-return-last-termlist x) env)
                   (rl-ev-list x env)))
    :rewrite :direct)

  (in-theory (disable remove-return-last-termlist-correct-cond
                      remove-return-last-term-correct-cond))

  (local (defthm equal-of-len
           (implies (syntaxp (quotep n))
                    (equal (equal (len x) n)
                           (cond ((eql n 0) (atom x))
                                 ((zp n) nil)
                                 (t (and (consp x)
                                         (equal (len (cdr x)) (1- n)))))))))

  (local (in-theory (disable len)))

  (defthm-remove-return-last-flag
    (defthm remove-return-last-term-correct-lemma
      (remove-return-last-term-correct-cond x)
      :hints ((and stable-under-simplificationp
                   `(:expand (,(car (last clause))
                              ;; (remove-return-last-term x)
                              ))))
      :flag remove-return-last-term
      :rule-classes nil)
    (defthm remove-return-last-termlist-correct-lemma
      (remove-return-last-termlist-correct-cond x)
      :hints ((and stable-under-simplificationp
                   `(:expand (,(car (last clause))
                              ;; (remove-return-last-termlist x)
                              ))))
      :flag remove-return-last-termlist
      :rule-classes nil))

  (defthm remove-return-last-term-correct
    (equal (rl-ev (remove-return-last-term x) env)
           (rl-ev x env))
    :hints (("goal" :use remove-return-last-term-correct-lemma)))

  (defthm remove-return-last-termlist-correct
    (equal (rl-ev-list (remove-return-last-termlist x) env)
           (rl-ev-list x env))
    :hints (("goal" :use remove-return-last-termlist-correct-lemma)))
  )
