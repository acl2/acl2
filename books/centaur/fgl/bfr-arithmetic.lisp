; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

; cert_param: (non-acl2r)

(in-package "FGL")

(include-book "symbolic-arithmetic")
(include-book "logicman")
(local (include-book "std/util/termhints" :dir :system))

;; AABF-TRUE and AABF-FALSE are just T and NIL for BFR.
(defmacro bfr-true () t)
(defmacro bfr-false () nil)


;; We need to replicate AABF-NEST for BFR/logicman functions.  First define the
;; MANRET binders for base functions.
(def-manret-binder bfr-true :takes-man nil)
(def-manret-binder bfr-false :takes-man nil)
(def-manret-binder bfr-not :returns-man nil)
(def-manret-binder bfr-and)
(def-manret-binder bfr-or)
(def-manret-binder bfr-xor)
(def-manret-binder bfr-iff)
(def-manret-binder bfr-ite)

(mutual-recursion
 (defun bfr-nest-fn (x varnum man acc)
   (declare (Xargs :mode :program))
   (b* (((when (atom x)) (mv x varnum acc))
        (fn (car x))
        ((when (eq fn 'quote)) (mv x varnum acc))
        ((when (eq fn 'not))
         (b* (((mv expr varnum acc) (bfr-nest-fn (second x) varnum man acc)))
           (mv `(bfr-not ,expr ,man) varnum acc)))
        ((when (member fn '(and or xor)))
         (bfr-binary-nestlist-fn (car x) (cdr x) varnum man acc))
        ((when (eq fn 'ite))
         (b* (((mv test varnum acc) (bfr-nest-fn (second x) varnum man acc))
              ((mv then varnum acc) (bfr-nest-fn (third x) varnum man acc))
              ((mv else varnum acc) (bfr-nest-fn (fourth x) varnum man acc))
              (var (intern$ (str::cat "ITE" (str::natstr varnum)) "FGL"))
              (acc (cons `((mv ,var ,man) (bfr-ite ,test ,then ,else ,man)) acc)))
           (mv var (1+ varnum) acc)))
        ((unless (symbolp fn))
         (er hard? 'bfr-nest-fn "Bad function symbol: ~x0~%" (car x))
         (mv nil varnum acc))
        ((when (or (assoc-eq fn acl2::*primitive-formals-and-guards*)
                   (member fn '(list list*))))
         (b* (((mv args varnum acc) (bfr-nestlist-fn (cdr x) varnum man acc)))
           (mv (cons fn args) varnum acc)))
        ((mv args varnum acc) (bfr-nestlist-fn (cdr x) varnum man acc))
        (var (intern$ (str::cat (symbol-name fn) (str::natstr varnum)) "FGL"))
        (acc (cons `((manret ,var ,man) (,fn . ,args)) acc)))
     (mv var (1+ varnum) acc)))

 (defun bfr-nestlist-fn (x varnum man acc)
   (b* (((when (atom x))
         (mv nil varnum acc))
        ((mv first varnum acc) (bfr-nest-fn (car x) varnum man acc))
        ((mv rest varnum acc) (bfr-nestlist-fn (cdr x) varnum man acc)))
     (mv (cons first rest) varnum acc)))

 (defun bfr-binary-nestlist-fn (op x varnum man acc)
   (declare (Xargs :mode :program))
   (b* (((when (atom x))
         (mv (case op
               (and '(bfr-true))
               (t   '(bfr-false)))
             varnum acc))
        ((when (atom (cdr x)))
         (bfr-nest-fn (car x) varnum man acc))
        ((mv first varnum acc) (bfr-nest-fn (car x) varnum man acc))
        ((mv rest varnum acc) (bfr-binary-nestlist-fn op (cdr x) varnum man acc))
        (var (intern$ (str::cat (symbol-name op) (str::natstr varnum)) "FGL"))
        (acc (cons `((mv ,var ,man)
                     (,(case op
                         (and 'bfr-and)
                         (or 'bfr-or)
                         (xor 'bfr-xor))
                      ,first ,rest ,man))
                   acc)))
     (mv var (1+ varnum) acc))))

(defmacro bfr-nest (nest man)
  (b* (((mv res ?varnum acc) (bfr-nest-fn nest 0 man nil)))
    `(b* ,(reverse acc)
       (mv ,res ,man))))

(defmacro bfr-not-depends-on-var (x logicman)
  `(not (bfr-depends-on var ,x ,logicman)))

(defmacro bfr-list-not-depends-on-var (x logicman)
  `(not (bfr-list-depends-on var ,x ,logicman)))

;; (define bfr-integer-length-bound-s (x logicman)
;;   :ignore-ok t  :irrelevant-formals-ok t
;;   :enabled t
;;   :guard-hints (("goal" :in-theory (enable integer-length-bound-s)))
;;   (mbe :logic (non-exec (integer-length-bound-s x logicman))
;;        :exec (max (len x) 1)))

(defmacro bfr-ite-bss (c v1 v0 man)
  `(mbe :logic (bfr-ite-bss-fn ,c ,v1 ,v0 ,man)
        :exec (let ((bfr-ite-bss-test ,c))
                (cond ((eq bfr-ite-bss-test nil)
                       (mv (llist-fix ,v0) ,man))
                      ((eq bfr-ite-bss-test t)
                       (mv (llist-fix ,v1) ,man))
                      (t (bfr-ite-bss-fn-aux bfr-ite-bss-test ,v1 ,v0 ,man))))))

(def-manret-binder bfr-ite-bss)

;; (define bfr-syntactically-true-p (x logicman)
;;   :ignore-ok t :irrelevant-formals-ok t
;;   :returns (true-p booleanp)
;;   (eq x t)
;;   ///
;;   (std::defretd bfr-syntactically-true-p-implies
;;     (implies (bfr-syntactically-true-p x man)
;;              (equal (bfr-eval x env man) t)))

;;   (std::defretd bfr-syntactically-true-p-rewrite
;;     (implies (and (acl2::rewriting-negative-literal `(bfr-syntactically-true-p ,x ,man))
;;                   (bind-free '((env . env)) (env)))
;;              (iff (bfr-syntactically-true-p x man)
;;                   (and (equal (bfr-eval x env man) t)
;;                        (hide (bfr-syntactically-true-p x man)))))
;;     :hints (("goal" :expand ((:free (x) (hide x)))))))

;; (define bfr-syntactically-false-p (x logicman)
;;   :ignore-ok t :irrelevant-formals-ok t
;;   :returns (false-p booleanp)
;;   (eq x nil)
;;   ///
;;   (std::defretd bfr-syntactically-false-p-implies
;;     (implies (bfr-syntactically-false-p x man)
;;              (equal (bfr-eval x env man) nil)))

;;   (std::defretd bfr-syntactically-false-p-rewrite
;;     (implies (and (acl2::rewriting-negative-literal `(bfr-syntactically-false-p ,x ,man))
;;                   (bind-free '((env . env)) (env)))
;;              (iff (bfr-syntactically-false-p x man)
;;                   (and (equal (bfr-eval x env man) nil)
;;                        (hide (bfr-syntactically-false-p x man)))))
;;     :hints (("goal" :expand ((:free (x) (hide x)))))))

;; (define bfr-syntactically-zero-p ((x true-listp))
;;   :returns (result booleanp)
;;   ;; (b* (((mv head tail end) (bfr-first/rest/end x)))
;;   ;;   (and (bfr-syntactically-equal head (bfr-false))
;;   ;;        (or end
;;   ;;            (bfr-syntactically-zero-p tail))))
;;   (if (atom x)
;;       t
;;     (and (eq (car x) nil)
;;          (bfr-syntactically-zero-p (cdr x))))
;;   ///
;;   (std::defretd bfr-syntactically-zero-p-implies
;;     (implies (bfr-syntactically-zero-p x)
;;              (equal (bools->int (bfr-list-eval x env man)) 0))
;;     :hints (("goal" :induct t
;;              :in-theory (enable bools->int bfr-list-eval))))

;;   (std::defretd bfr-syntactically-zero-p-implies-unsigned
;;     (implies (bfr-syntactically-zero-p x)
;;              (equal (bools->uint (bfr-list-eval x env man)) 0))
;;     :hints (("goal" :induct t
;;              :in-theory (enable bools->uint bfr-list-eval)))))

;; (define bfr-syntactically-signext-p ((x true-listp) b)
;;   :returns (result booleanp)
;;   (b* (((mv head tail end) (bfr-first/rest/end x)))
;;     (and (bfr-syntactically-equal head b)
;;          (or end
;;              (bfr-syntactically-signext-p tail b))))
;;   ///
;;   (local (defthm logcons-of-equal-neg-bit
;;            (implies (and (equal x (- b))
;;                          (bitp b))
;;                     (equal (logcons b x) (- b)))))

;;   (std::defretd aabf-syntactically-signext-p-implies
;;     (implies (aabf-syntactically-signext-p x b)
;;              (equal (bools->int (aabflist-eval x env man))
;;                     (endint (aabf-eval b env man))))
;;     :hints (("goal" :induct t
;;              :expand ((:with bools->int-open-once (bools->int (aabflist-eval x env man)))))
;;             '(:use ((:instance aabf-syntactically-equal-implies-equal-aabf-eval-1
;;                      (x (aabf-car x)) (x-equiv b)))
;;               :in-theory (disable aabf-syntactically-equal-implies-equal-aabf-eval-1)))))

(defmacro logicman-extension-plus (x y)
  `(and (logicman-extension-p ,x ,y)
        (equal (bfr-nvars ,x) (bfr-nvars ,y))
        (equal (logicman-get :ipasir ,x) (logicman-get :ipasir ,y))
        (equal (logicman-get :sat-lits ,x) (logicman-get :sat-lits ,y))
        (equal (logicman->refcounts-index ,x) (logicman->refcounts-index ,y))
        (equal (logicman->aignet-refcounts ,x) (logicman->aignet-refcounts ,y))))

(table aabf->bfr-map
       nil
       '((aabf-eval                . gobj-bfr-eval)
         (aabf-p                   . lbfr-p)
         (aabf-pred                . bfr-not-depends-on-var)
         (aabf-true                . bfr-true)
         (aabf-false               . bfr-false)
         (aabf-not                 . bfr-not)
         (aabf-and                 . bfr-and)
         (aabf-or                  . bfr-or)
         (aabf-xor                 . bfr-xor)
         (aabf-iff                 . bfr-iff)
         (aabf-ite                 . bfr-ite)
         (aabf-syntactically-equal . equal)
         (aabf-extension-p         . logicman-extension-plus)
         (aabflist-eval            . gobj-bfr-list-eval)
         (aabflist-p               . lbfr-listp)
         (aabflist-pred            . bfr-list-not-depends-on-var)
         (aabf-nest                . bfr-nest)
         (aabf-ite-bss             . bfr-ite-bss)
         ;; (aabf-syntactically-true-p . bfr-syntactically-true-p)
         ;; (aabf-syntactically-false-p . bfr-syntactically-false-p)
         ;; (aabf-syntactically-zero-p . bfr-syntactically-zero-p)
         ;; (integer-length-bound-s   . bfr-integer-length-bound-s)
         (man                      . logicman))
       :clear)

(table aabf->bfr-functional-substitution
       nil
       '((aabf-eval gobj-bfr-eval-fn)
         (aabf-p (lambda (x man) (bfr-p x (logicman->bfrstate man))))
         (aabf-pred (lambda (x man) (not (bfr-depends-on var x man))))
         (aabf-true (lambda () t))
         (aabf-false (lambda () nil))
         (aabf-not bfr-not-fn)
         (aabf-and bfr-and-fn)
         (aabf-or bfr-or-fn)
         (aabf-xor bfr-xor-fn)
         (aabf-iff bfr-iff-fn)
         (aabf-ite bfr-ite-fn)
         (aabf-syntactically-equal hons-equal)
         (aabf-extension-p (lambda (x y) (logicman-extension-plus x y)))
         (aabflist-eval gobj-bfr-list-eval-fn)
         ;; (aabf-syntactically-true-p bfr-syntactically-true-p)
         ;; (aabf-syntactically-false-p bfr-syntactically-false-p)
         ;; (aabf-syntactically-zero-p bfr-syntactically-zero-p)
         (aabflist-p (lambda (x man) (bfr-listp x (logicman->bfrstate man))))
         (aabflist-pred (lambda (x man) (not (bfr-list-depends-on var x man)))))
       :clear)

(local (defthm bfr-depends-on-of-nil
         (not (bfr-depends-on var nil logicman))
         :hints(("Goal" :in-theory (enable bfr-depends-on bfr->aignet-lit)))))

(local (defthm bfr-depends-on-of-t
         (not (bfr-depends-on var t logicman))
         :hints(("Goal" :in-theory (enable bfr-depends-on bfr->aignet-lit)))))


(local
 (defthm aabf-trivial-thm
   (b* ((orig-man man)
        (notx (aabf-not x man))
        ((mv yxorz man) (aabf-xor y z man))
        ((mv res man) (aabf-and notx yxorz man))
        ;; some junk to include functions in our substitution that we otherwise
        ;; wouldn't
        (?ign (aabflist-eval nil env man))
        (?ign (aabflist-p nil man))
        (?ign (aabflist-pred nil man))
        ;; (?ign (aabf-syntactically-true-p x man))
        ;; (?ign (aabf-syntactically-false-p x man))
        ;; (?ign (aabf-syntactically-zero-p x man))
        )
     (implies (and (aabf-p x orig-man)
                   (aabf-p y orig-man)
                   (aabf-p z orig-man))
              (equal (aabf-eval res env man)
                     (and (not (aabf-eval x env orig-man))
                          (xor (aabf-eval y env orig-man)
                               (aabf-eval z env orig-man))))))
   :rule-classes nil))

(local
 (make-event
  `(defthm logicman-aabf-dependency-functional-instance-ok
     t
     :rule-classes nil
     :hints (("goal" :use ((:functional-instance aabf-trivial-thm
                            . ,(table-alist 'aabf->bfr-functional-substitution (w state))))
              :in-theory (enable gobj-bfr-list-eval bfr-list-depends-on
                                 ;; bfr-syntactically-true-p
                                 ;; bfr-syntactically-false-p
                                 ))))))




(defun symbol-name-subst (old new sym)
  (declare (xargs :guard (and (stringp old)
                              (stringp new)
                              (symbolp sym))))
  (if (str::substrp old (symbol-name sym)) ;; optimization
      (intern-in-package-of-symbol
       (str::strsubst old new (symbol-name sym))
       sym)
    sym))

(defun replace-hints (new-hints args)
  (declare (xargs :mode :program))
  (if (atom args)
      nil
    (if (eq (car args) :hints)
        `(:hints ,new-hints . ,(cddr args))
      (cons (car args) (replace-hints new-hints (cdr args))))))

(defun aabf-theorem-to-bfr (old-name new-name form func-subst world)
  (declare (xargs :mode :program))
  ;; Form is just the args of a DEFTHM form.
  (b* ((thmname (symbol-name-subst "<FN>" (symbol-name old-name) (car form)))
       (new-thmname (symbol-name-subst "AABF" "BFR" (symbol-name-subst (symbol-name old-name)
                                                                       (symbol-name new-name)
                                                                       thmname)))
       (formals (getpropc old-name 'formals t world))
       (body (getpropc old-name 'unnormalized-body nil world))
       (hq-formals (and (not (eq formals t))
                        (pairlis$ (make-list (len formals) :initial-element 'acl2::hq)
                                  (pairlis$ formals nil))))
       (hints `(("goal" :use (:instance (:functional-instance ,thmname . ,func-subst)
                              :extra-bindings-ok
                              (man logicman))
                 :in-theory nil)
                ,@(and body (not (eq formals t))
                       `((acl2::use-termhint
                          `(:expand (,(list ',new-name . ,hq-formals))))))
                ;; (let* ((formals (getpropc ',new-name 'formals t world))
                ;;        (body (getpropc ',new-name 'unnormalized-body nil world))
                ;;        (call (cons ',new-name (subst 'man 'logicman formals))))
                ;;   (and (not (eq formals t)) body
                ;;        `(:expand (,call)
                ;;          ;; :in-theory nil
                ;;          ;;:in-theory '(hons-equal eq eql) ;; (disable ,',new-name)
                ;;          )))
                (and stable-under-simplificationp
                     '(:in-theory (list* 'hons-equal
                                         'default-car
                                         'default-cdr
                                         (theory 'minimal-theory))))
                ;; (and stable-under-simplificationp
                ;;      '(:in-theory (enable)))
                )))
    (cons new-thmname (replace-hints hints (cdr form)))))

(defun aabf-theorems-to-bfr (old-name new-name x func-subst world)
  (declare (xargs :mode :program))
  (cond ((atom x) x)
        ((member-eq (car x) '(defthm defret std::defretd))
         (cons (car x) (aabf-theorem-to-bfr old-name new-name (cdr x) func-subst world)))
        (t (cons-with-hint (aabf-theorems-to-bfr old-name new-name (car x) func-subst world)
                           (aabf-theorems-to-bfr old-name new-name (cdr x) func-subst world)
                           x))))

(defun aabf-guardverif-to-bfr (old-name new-name form func-subst)
  (declare (xargs :mode :program))
  ;; Form is just the args of a DEFTHM form.
  (b* ((hints `(("goal" :use ((:instance (:functional-instance
                                         (:guard-theorem ,old-name)
                                         . ,func-subst)
                              :extra-bindings-ok
                              (man logicman)))))))
    (cons new-name (replace-hints hints (cdr form)))))

(defun aabf-verify-guards-to-bfr (old-name new-name x func-subst)
  (declare (xargs :mode :program))
  (cond ((atom x) x)
        ((eq (car x) 'verify-guards+)
         (cons 'verify-guards+ (aabf-guardverif-to-bfr old-name new-name (cdr x) func-subst)))
        (t (cons-with-hint (aabf-verify-guards-to-bfr old-name new-name (car x) func-subst)
                           (aabf-verify-guards-to-bfr old-name new-name (cdr x) func-subst)
                           x))))
  

(defun aabf-tableops-to-bfr (old-name new-name x)
  (declare (xargs :mode :program))
  (cond ((atom x) x)
        ((eq (car x) 'table)
         ;; Assumes there's only one table event in here.
         (if (eq old-name new-name)
             '(progn)
           `(progn (table aabf->bfr-map ',old-name ',new-name)
                   (table aabf->bfr-functional-substitution
                          ',old-name '(,new-name)))))
        (t (cons-with-hint (aabf-tableops-to-bfr old-name new-name (car x))
                           (aabf-tableops-to-bfr old-name new-name (cdr x))
                           x))))

                           

(defun aabf-form-to-bfr (name form world)
  (declare (xargs :mode :program))
  (b* ((bfr-namestr (str::strsubst "AABF" "BFR" (symbol-name name)))
       (bfr-name (intern$ bfr-namestr "FGL"))
       (subst-alist (table-alist 'aabf->bfr-map world))
       (subst-alist (if (eq bfr-name name)
                        subst-alist
                      (cons (cons name bfr-name)
                            subst-alist)))
       (form (sublis subst-alist form))
       (func-subst (table-alist 'aabf->bfr-functional-substitution world))
       (func-subst (if (eq bfr-name name)
                       func-subst
                     (cons (list name bfr-name)
                           func-subst)))
       (form (aabf-theorems-to-bfr name bfr-name form func-subst world))
       (form (aabf-verify-guards-to-bfr name bfr-name form func-subst)))
    (aabf-tableops-to-bfr name bfr-name form)))


(defun remove-///-stuff (form)
  (if (atom form)
      nil
    (if (eq (car form) '///)
        nil
      (cons-with-hint (car form)
                      (remove-///-stuff (cdr form))
                      form))))

(defun remove-prepwork (form)
  (if (atom form)
      nil
    (if (eq (car form) :prepwork)
        (cddr form)
      (cons-with-hint (car form)
                      (remove-prepwork (cdr form))
                      form))))

(defun defsymbolic-form-to-bfr (name args world)
  (declare (xargs :mode :program))
  (b* ((ctx `(defsymbolic-form-to-bfr ,name))
       ((mv err form)
        (acl2::macroexpand1-cmp `(defsymbolic ,name . ,(remove-///-stuff (remove-prepwork args))) ctx world
                                (default-state-vars nil)))
       ((when err) (er hard? ctx "~x0: ~@1~%" err form)))
    (aabf-form-to-bfr name form world)))

(defmacro defsymbolic-to-bfr-event (name args)
  `(make-event
    (defsymbolic-form-to-bfr ',name ',args (w state))))

(defun defsymbolic-forms-to-bfr (table)
  (declare (xargs :mode :program))
  (if (atom table)
      nil
    (cons `(defsymbolic-to-bfr-event ,(caar table) ,(cdar table))
          (defsymbolic-forms-to-bfr (cdr table)))))


(defun defsymbolic-to-bfr-events (world)
  (declare (xargs :mode :program))
  (cons 'progn (reverse (defsymbolic-forms-to-bfr (table-alist 'defsymbolic-forms world)))))

(defmacro defsymbolic-to-bfr ()
  `(make-event (defsymbolic-to-bfr-events (w state))))

(local (in-theory (disable bools->int-redef)))



(local (in-theory (disable floor logand mod logxor logeqv expt logicman->bfrstate-updater-independence
                           acl2::consp-when-member-equal-of-atom-listp
                           default-+-2 default-+-1 member equal-of-booleans-rewrite
                           not)))

(with-output :off (prove event observation) :summary (time acl2::form)
  (defsymbolic-to-bfr))
