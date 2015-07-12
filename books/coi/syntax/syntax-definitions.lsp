; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; syntax-definitions.lisp
;; John D. Powell
;(in-package "SYN")

(error "Is anyone using this?  If so please remove this error.")

;;
;; This file isolates syntax definitions and types. The file currently
;; contains the following ACL2 constructs as they occur in the syntax book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

(defun collect-variables-rec (fn term res)
  (declare (type t fn term res))
  (if (consp term)
      (if (consp (car term))
          (let ((res (collect-variables-rec t (car term) res)))
            (collect-variables-rec nil (cdr term) res))
        (if fn (collect-variables-rec nil (cdr term) res)
          (let ((res (append (if (symbolp (car term)) (list (car term)) nil)
                             res)))
            (collect-variables-rec nil (cdr term) res))))
    res))

(defthm symbol-listp-collect-variables-rec
  (implies
   (symbol-listp res)
   (symbol-listp (collect-variables-rec fn term res)))
  :rule-classes (:type-prescription :rewrite))

(defthm true-listp-collect-variables-rec
  (implies
   (true-listp res)
   (true-listp (collect-variables-rec fn term res)))
  :rule-classes (:type-prescription :rewrite))

(defun join-lists (list1 list2)
  (declare (type t list1 list2))
  (if (and (consp list1)
           (consp list2))
      (cons (list (car list1) (car list2))
            (join-lists (cdr list1) (cdr list2)))
    nil))

;; (defun in-conclusion (term conclusion)
;;   (declare (type t term conclusion))
;;   (if (consp conclusion)
;;       (or (equal term (car conclusion))
;;           (in-conclusion term (cdr conclusion)))
;;     nil))

;; (defun in-conclusion-or-backchain-fn (term mfc state)
;;   (declare (xargs :mode :program)
;;            (ignore state))
;;   (and (or (mfc-ancestors mfc)
;;            (in-conclusion term (mfc-clause mfc)))
;;        (list (cons 'in-conclusion-or-backchain (syn::true)))))

(defun mfc-rw-equiv (term obj equiv mfc state)
  (declare (xargs :mode :program
                  :guard (state-p state)))
  (let ((wrld  (access metafunction-context mfc :wrld))
        (rcnst (access metafunction-context mfc :rcnst)))
    (let ((geneqv (car (geneqv-lst equiv nil
                                   (access rewrite-constant rcnst
                                           :current-enabled-structure)
                                   wrld))))
      (if (and (termp term wrld)
               (member-eq obj '(t nil ?)))
          (mv-let
           (rw ttree)
           (rewrite-entry
            (rewrite term nil 'meta)
            :rdepth (rewrite-stack-limit wrld)
            :type-alist (access metafunction-context mfc :type-alist)
            :geneqv geneqv
            :wrld wrld
            :fnstack (access metafunction-context mfc :fnstack)
            :ancestors (access metafunction-context mfc :ancestors)
            :backchain-limit (access metafunction-context mfc
                                     :backchain-limit)
            :simplify-clause-pot-lst (access metafunction-context mfc
                                             :simplify-clause-pot-lst)
            :rcnst rcnst
            :gstack (access metafunction-context mfc :gstack)
            :ttree nil)
           (declare (ignore ttree))
           rw)
        (prog2$ (cw "***~%!!! mfc-rw-equiv failed wf-test !!!~%***~%")
                term)))))

(defun equiv-binding-fn (equiv term key mfc state)
  (declare (xargs :mode :program)
           (type (satisfies state-p) state))
  (let ((term (acl2::mfc-rw-equiv term 'acl2::? equiv mfc state)))
    (cons (cons key term) nil)))

(mutual-recursion

 (defun enquote-function-call (function)
   (declare (type (satisfies consp) function)
            (xargs :measure (acl2-count function)))
   (mbe :logic (if (consp function)
                   `(cons (quote ,(car function))
                          ,(enquote-function-args (cdr function)))
                 function)
        :exec
        `(cons (quote ,(car function))
               ,(enquote-function-args (cdr function)))))

 (defun enquote-function-args (args)
   (declare (type t args)
            (xargs :measure (acl2-count args)))
   (if (consp args)
       (let ((arg (car args)))
         (if (consp arg)
             `(cons ,(enquote-function-call arg) ,(enquote-function-args (cdr args)))
           `(cons ,(car args)
                  ,(enquote-function-args (cdr args)))))
     'nil))

 )

(defun enquote-term (term)
  (declare (type t term))
  (if (consp term)
      (enquote-function-call term)
    term))

(defun syn::defevaluator-form (evfn evfn-lst fn-args-lst)
  (declare (xargs :mode :program))
  (let* ((clauses (evaluator-clauses evfn evfn-lst fn-args-lst))
         (fns-clauses (defevaluator-form/fns-clauses evfn fn-args-lst))
         (defthms (defevaluator-form/defthms
                    evfn
                    (symbol-name (pack2 evfn '-constraint-))
                    0
                    clauses)))
    `(encapsulate
      (((,evfn * *) => *)
       ((,evfn-lst * *) => *))
      (set-inhibit-warnings "theory")

      ,@(sublis
         (list (cons 'evfn evfn)
               (cons 'evfn-lst evfn-lst)
               (cons 'fns-clauses fns-clauses)
               (cons 'defthms defthms))
         '((local
            (mutual-recursion
             (defun evfn (x a)
               (declare (xargs :verify-guards nil
                               :measure (acl2-count x)
                               :well-founded-relation o<
                               :hints (("goal" :do-not '(preprocess) :in-theory (disable o< acl2-count)))
                               :mode :logic))
               (cond
                ((symbolp x) (and x (cdr (assoc-eq x a))))
                ((atom x) nil)
                ((eq (car x) 'quote) (car (cdr x)))
                ((consp (car x))
                 (evfn (car (cdr (cdr (car x))))
                       (pairlis$ (car (cdr (car x)))
                                 (evfn-lst (cdr x) a))))
                .
                fns-clauses))
             (defun evfn-lst (x-lst a)
               (declare (xargs :measure (acl2-count x-lst)
                               :well-founded-relation o<))
               (cond ((endp x-lst) nil)
                     (t (cons (evfn (car x-lst) a)
                              (evfn-lst (cdr x-lst) a)))))))
           (local (in-theory *defevaluator-form-base-theory*))
           (local (in-theory (enable evfn evfn-lst)))
           (local
            (defthm eval-list-kwote-lst
              (equal (evfn-lst (kwote-lst args) a)
                     (fix-true-list args))))
           . defthms)))))

(defthm o<-acl2-count-car
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CAR x))
               (ACL2-COUNT x))))

(defthm o<-acl2-count-cdr
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CDR x))
               (ACL2-COUNT x))))

(defthm o<-acl2-count-cadr
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CADR x))
               (ACL2-COUNT x))))

(defthm o<-acl2-count-caar
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CAAR x))
               (ACL2-COUNT x))))

(defthm o<-acl2-count-caddr
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CADDR x))
               (ACL2-COUNT x))))

(defthm o<-acl2-count-caadr
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CAaDR x))
               (ACL2-COUNT x))))

(defthm o<-acl2-count-cadar
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CADaR x))
               (ACL2-COUNT x))))

(defthm o<-acl2-count-cadddr
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CADDDR x))
               (ACL2-COUNT x))))

(defthm o<-acl2-count-caaddr
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CAaDDR x))
               (ACL2-COUNT x))))

(defthm o<-acl2-count-cadadr
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CADaDR x))
               (ACL2-COUNT x))))

(defthm o<-acl2-count-caddar
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CADDaR x))
               (ACL2-COUNT x))))

(defthm o<-acl2-count-caddddr
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CADDDR (cdr x)))
               (ACL2-COUNT x))))


(defthm o<-acl2-count-caadddr
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CAaDDR (cdr x)))
               (ACL2-COUNT x))))


(defthm o<-acl2-count-cadaddr
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CADaDR (cdr x)))
               (ACL2-COUNT x))))


(defthm o<-acl2-count-caddadr
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CADDaR (cdr x)))
               (ACL2-COUNT x))))


(defthm o<-acl2-count-cadddar
  (IMPLIES (consp x)
           (O< (ACL2-COUNT (CADDDR (car x)))
               (ACL2-COUNT x))))

(defun quine-body-fn (name body history)
  ``(encapsulate ()
      (defmacro ,,name (name)
        (let ((history (cons (quote ,,name) (quote ,,history))))
          (,,body (quote ,,body))))
      ))

(defun syn::len (n list)
  (declare (type (integer 0 *) n))
  (acl2::if (acl2::consp list)
      (acl2::if (zp n) acl2::nil
        (len (1- n) (acl2::cdr list)))
    (acl2::and (acl2::null list) (= n 0))))

(defthm open-len
  (implies
   (syntaxp (acl2::quotep n))
   (equal (len n list)
          (acl2::if (acl2::consp list)
              (acl2::if (zp n) acl2::nil
                (len (1- n) (acl2::cdr list)))
            (acl2::and (acl2::null list) (= n 0))))))

(defun nth (n l)
  (declare (type (integer 0 *) n))
  (acl2::and (acl2::consp l)
             (acl2::if (zp n)
                 (acl2::car l)
               (nth (+ -1 n) (acl2::cdr l)))))

(defthm open-nth
  (implies
   (syntaxp (acl2::quotep n))
   (equal (nth n l)
          (acl2::and (acl2::consp l)
                     (acl2::if (zp n)
                         (acl2::car l)
                         (nth (+ -1 n) (acl2::cdr l)))))))

(defthm len-implies-true-listp
  (implies
   (len n list)
   (true-listp list))
  :rule-classes (:forward-chaining))

(defthm len-implies-acl2-len
  (implies
   (len n list)
   (equal (acl2::len list) n))
  :rule-classes (:linear :forward-chaining))

(defun syn::consp (term)
  (declare (type t term))
  (acl2::and
   (len 3 term)
   (equal (acl2::car term) 'acl2::cons)))

(defun syn::cons (a b)
  (declare (type t a b))
  `(acl2::cons ,a ,b))

(defun syn::car (term)
  (declare (type (satisfies syn::consp) term))
  (cadr term))

(defun syn::cdr (term)
  (declare (type (satisfies syn::consp) term))
  (caddr term))

(local
 (defthm cons-reconstruction
   (implies
    (syn::consp term)
    (equal (syn::cons (syn::car term) (syn::cdr term))
           term))))

(defun syn::quotep (term)
  (declare (type t term))
  (acl2::and (len 2 term)
             (equal (acl2::car term) 'acl2::quote)))

(defun syn::enquote (term)
  (declare (type t term))
  `(acl2::quote ,term))

(defun syn::dequote (term)
  (declare (type (satisfies syn::quotep) term))
  (cadr term))

(local
 (defthm quote-reconstruction
   (implies
    (syn::quotep term)
    (equal (syn::enquote (syn::dequote term))
           term))))

(defun syn::appendp (term)
  (declare (type t term))
  (acl2::and (syn::len 3 term)
             (equal (acl2::car term) 'binary-append)))

(defun syn::append (x y)
  (declare (type t x y))
  `(acl2::binary-append ,x ,y))

(local
 (defthm append-reconstruction
   (implies
    (syn::appendp term)
    (equal (syn::append (syn::arg 1 term) (syn::arg 2 term))
           term))))

(defun syn::ifp (term)
  (declare (type t term))
  (acl2::and (syn::len 4 term)
             (equal (acl2::car term) 'acl2::if)))

(defun syn::if (a b c)
  (declare (type t a b c))
  `(acl2::if ,a ,b ,c))

(local
 (defthm if-reconstruction
   (implies
    (syn::ifp term)
    (equal (syn::if (syn::arg 1 term) (syn::arg 2 term) (syn::arg 3 term))
           term))))

(defun syn::nil ()
  (declare (xargs :verify-guards t))
  `(syn::quote acl2::nil))

(defun syn::null (x)
  (declare (type t x))
  (equal x (syn::nil)))

(defun syn::true ()
  (declare (xargs :verify-guards t))
  `(syn::quote t))

;; Perhaps this should be weakened to ((cadr x) != nil) ??

(defun syn::truep (x)
  (declare (type t x))
  (acl2::and (acl2::consp x)
             (acl2::equal (acl2::car x) 'quote)
             (acl2::consp (acl2::cdr x))
             (acl2::equal (acl2::cadr x) 't)))

(defun syn::conjoin (x y)
  (declare (type t x y))
  (acl2::cond
   ((acl2::not (acl2::and x y))
    acl2::nil)
   ((syn::truep y)
    x)
   ((syn::truep x)
    y)
   (acl2::t
    (syn::if x y (syn::nil)))))

(defun syn::and-fn (args)
  (declare (type t args))
  (acl2::if (acl2::consp args)
            `(syn::conjoin ,(acl2::car args) ,(syn::and-fn (acl2::cdr args)))
            `(syn::true)))

(defun syn::funcall (fn args term)
  (declare (type (integer 0 *) args))
  (acl2::and (syn::len (1+ args) term)
             (equal (acl2::car term) fn)))

(defun syn::consp-rec (x)
  (declare (type t x))
  (cond
   ((syn::consp x) t)
   ((syn::appendp x)
    (or (syn::consp-rec (syn::arg 1 x))
        (syn::consp-rec (syn::arg 2 x))))
   ((syn::quotep x)
    (acl2::consp (syn::dequote x)))
   (t
    acl2::nil)))

(defthm consp-rec-implies-consp
  (implies
   (syn::consp-rec term)
   (acl2::consp (syn::eval term a))))

(defun free-var-bindings (w1 w2 term)
  (declare (type symbol w1 w2))
  (acl2::let ((list (symbol-fns::collect-variables term)))
    (symbol-fns::join-lists (symbol-fns::map-symbol-list-to-package list w1)
                            (symbol-fns::map-symbol-list-to-package list w2))))

(defthm type-alistp-to-type-alist-entryp
  (implies
   (acl2::and
    (acl2::type-alistp term)
    (acl2::consp term))
   (acl2::type-alist-entryp (acl2::car term)))
  :rule-classes (:forward-chaining))

(defthm type-alist-entryp-implies-pseudo-termp-car
  (implies
   (acl2::type-alist-entryp entry)
   (acl2::pseudo-termp (acl2::car entry)))
  :hints (("goal" :in-theory (enable acl2::type-alist-entryp)))
  :rule-classes (:forward-chaining))

(defthm pseudo-term-listp-from-pseudo-termp
  (implies
   (acl2::and
    (acl2::pseudo-termp term)
    (not (equal (acl2::car term) 'quote)))
   (acl2::pseudo-term-listp (acl2::cdr term)))
  :hints (("goal" :in-theory (enable acl2::pseudo-termp))))

(defthm pseudo-term-listp-of-cdr
  (implies (acl2::pseudo-term-listp x)
           (acl2::pseudo-term-listp (acl2::cdr x)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

(defthm pseudo-term-listp-of-car
  (implies (acl2::pseudo-term-listp x)
           (acl2::pseudo-termp (acl2::car x)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

(defthm pseudo-termp-nth
  (implies
   (acl2::pseudo-term-listp list)
   (acl2::pseudo-termp (syn::nth n list)))
  :hints (("goal" :in-theory (enable acl2::pseudo-term-listp syn::nth))))

(defthm pseudo-termp-nth-from-pseudo-termp
  (implies
   (acl2::and
    (acl2::pseudo-termp term)
    (acl2::consp term)
    (< 0 (nfix n))
    (not (equal (acl2::car term) 'quote)))
   (acl2::pseudo-termp (syn::nth n term)))
  :hints (("goal" :expand (syn::nth n term))))

(defthm pseudo-termp-forward-to-true-listp
  (implies (acl2::and (acl2::pseudo-termp x)
                      (acl2::consp x))
           (acl2::true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable acl2::pseudo-termp))))

(defthm pseudo-termp-of-cons-when-symbolp
 (implies (acl2::and (acl2::symbolp a)
                     (not (equal a 'quote)))
          (equal (acl2::pseudo-termp (acl2::cons a rest))
                 (acl2::pseudo-term-listp rest)))
 :hints (("Goal" :expand  (pseudo-termp (acl2::cons a rest))
          :in-theory (enable acl2::pseudo-termp))))

(defthm pseudo-term-listp-of-cons
  (equal (acl2::pseudo-term-listp (acl2::cons a rest))
         (acl2::and (acl2::pseudo-termp a)
                    (acl2::pseudo-term-listp rest)))
  :hints (("Goal" :in-theory (enable acl2::pseudo-term-listp))))

(defthm pseudo-termp-of-cadr
  (implies (acl2::and (acl2::pseudo-termp term)
                      (not (equal (acl2::car term) 'quote))
                      (acl2::consp term)
                      (acl2::consp (acl2::cdr term)))
           (acl2::pseudo-termp (acl2::cadr term)))
  :hints (("Goal" :expand  (acl2::pseudo-termp term)
           :in-theory (enable acl2::pseudo-termp))))

(defthm iff-conjoin
  (iff (syn::conjoin x y)
       (acl2::and x y))
  :hints (("goal" :in-theory (enable syn::conjoin))))

(defthm pseudo-termp-conjoin
  (implies
   (acl2::and
    (acl2::pseudo-termp x)
    (acl2::pseudo-termp y))
   (acl2::pseudo-termp (syn::conjoin x y))))

(in-theory (disable syn::nth syn::open-nth))
(in-theory (disable syn::conjoin))

(defun syn::alist-binding (alist1 symbol)
  (declare (type symbol symbol))
  (if (and (symbolp alist1)
           (equal (symbol-name alist1) (symbol-name symbol))) nil
    `((,symbol . ,symbol))))

(defun mv-equality-terms (vals fname alist-1 alist args)
  (declare (type (integer 0 *) vals)
           (type (satisfies true-listp) args))
  (if (zp vals) nil
    (let ((vals (1- vals)))
      (let ((term `(equal (val ,vals (,fname ,alist-1 ,@args))
                          (val ,vals (,fname ,alist ,@args)))))
        (cons term
              (mv-equality-terms vals fname alist-1 alist args))))))

(defun equality-terms (vals fname alist-1 alist args)
  (declare (type (integer 0 *) vals)
           (type (satisfies true-listp) args))
  (if (< (nfix vals) 2)
      `(equal (,fname ,alist-1 ,@args)
              (,fname ,alist ,@args))
    `(and ,@(mv-equality-terms vals fname alist-1 alist args))))
