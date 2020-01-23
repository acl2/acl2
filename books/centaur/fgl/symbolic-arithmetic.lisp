; FGL - A Symbolic Simulation Framework for ACL2
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

; cert_param: (non-acl2r)

(in-package "FGL")
(include-book "arith-base")
(include-book "aabf-nest")
;; (local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "arith-lemmas"))
(local (include-book "std/util/termhints" :dir :system))

(local (defthm equal-complexes-rw
         (implies (and (acl2-numberp x)
                       (rationalp a)
                       (rationalp b))
                  (equal (equal (complex a b) x)
                         (and (equal a (realpart x))
                              (equal b (imagpart x)))))
         :hints (("goal" :use ((:instance realpart-imagpart-elim))))))


(defsection symbolic-arithmetic
  :parents (reference)
  :short "Internal operations for computing on symbolic bit vectors."
  :long "<p>Naming convention:</p>
<ul>
<li>B stands for a boolean variable.</li>
<li>S stands for a signed bvec.</li>
<li>U stands for an unsigned bvec.</li>
<li>V stands for a generic bvec where signedness doesn't matter.</li>
<li>N stands for a known natural constant.</li>
</ul>

<p>For instance, @('bfr-ite-bss-fn') has @('bss'), indicating that it's
for computing:</p>

@({
     (ite Boolean Signed-Bvec Signed-Bvec)
})")

(local (xdoc::set-default-parents symbolic-arithmetic))

;;---------------- Misc function definitions and lemmas -------------------

(define int-set-sign ((negp "True if we should set the sign bit to 1.")
                      (i    integerp "The integer to modify."))
  :short "Change the sign bit of an integer to a new value."
  :returns (new-i integerp :rule-classes :type-prescription)
  (let ((i (lifix i)))
    (acl2::logapp (integer-length i) i (if negp -1 0)))
  ///
  (defthm sign-of-int-set-sign
    (iff (< (int-set-sign negp i) 0)
         negp)
    :hints(("Goal" :in-theory (e/d* (int-set-sign)
                                    (acl2::logapp
                                     acl2::ifix-under-int-equiv))))))

(define non-int-fix (x)
  :short "Identity for non-integers; coerces any integers to @('nil')."
  (declare (xargs :guard t))
  (and (not (integerp x))
       x)
  ///
  (defthm non-int-fix-when-non-integer
    (implies (not (integerp x))
             (equal (non-int-fix x) x))
    :hints(("Goal" :in-theory (enable non-int-fix)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))

(define maybe-integer ((i integerp) x intp)
  (if intp
      (ifix i)
    (non-int-fix x))
  ///
  (defthm maybe-integer-t
    (equal (maybe-integer i x t)
           (ifix i))
    :hints(("Goal" :in-theory (enable maybe-integer))))

  (defthm maybe-integer-nil
    (equal (maybe-integer i x nil)
           (non-int-fix x))
    :hints(("Goal" :in-theory (enable maybe-integer)))))

;;-------------------------- DEFSYMBOLIC -----------------------------------

(defun extract-some-keywords
  (legal-kwds ; what keywords the args are allowed to contain
   args       ; args that the user supplied
   kwd-alist  ; accumulator alist of extracted keywords to values
   )
  "Returns (mv kwd-alist other-args other-keywords)"
  (declare (xargs :guard (and (symbol-listp legal-kwds)
                              (no-duplicatesp legal-kwds)
                              (alistp kwd-alist))))
  (b* (((when (atom args))
        (mv kwd-alist nil args))
       (arg1 (first args))
       ((unless (and (keywordp arg1)
                     (consp (cdr args))))
        (b* (((mv kwd-alist other-kws other-args)
              (extract-some-keywords legal-kwds (cdr args) kwd-alist)))
          (mv kwd-alist other-kws (cons arg1 other-args))))
       ((unless (member arg1 legal-kwds))
        (b* (((mv kwd-alist other-kws other-args)
              (extract-some-keywords legal-kwds (cddr args) kwd-alist)))
          (mv kwd-alist (cons arg1 (cons (cadr args) other-kws))
              other-args)))
       (value (second args))
       (kwd-alist (acons arg1 value kwd-alist)))
    (extract-some-keywords legal-kwds (cddr args) kwd-alist)))

(defun defsymbolic-check-formals (x)
  (cond ((atom x) t)
        ((eq (car x) 'man)
         (atom (cdr x)))
        ((and (consp (car x))
              (eql (len (car x)) 2)
              (symbolp (caar x))
              (member (cadar x) '(n i p b u s ru rs)))
         (defsymbolic-check-formals (cdr x)))
        (t (er hard? 'defsymbolic-check-formals
               "Bad formal: ~x0" (car x)))))

(defun defsymbolic-check-returns (x)
  (cond ((atom x) t)
        ((eq (car x) 'new-man) (atom (cdr x)))
        ((and (consp (car x))
              (>= (len (car x)) 2)
              (symbolp (caar x))
              (member (cadar x) '(n i p b u s ru rs))
              (or (member (cadar x) '(n i))
                  (eql (len (car x)) 3)))
         (defsymbolic-check-returns (cdr x)))
        (t (er hard? 'defsymbolic-check-returns
               "Bad return: ~x0" (car x)))))

(defun defsymbolic-formal-vars (x)
  (cond ((atom x) nil)
        ((eq (car x) 'man) '(man))
        (t (cons (caar x)
                 (defsymbolic-formal-vars (cdr x))))))

(defun defsymbolic-formals-pair-with-evals (x)
  (cond ((atom x) nil)
        ((eq (car x) 'man) nil)
        (t (cons (cons (caar x)
                       (case (cadar x)
                         (n `(nfix ,(caar x)))
                         (i `(ifix ,(caar x)))
                         (p `(acl2::pos-fix ,(caar x)))
                         (b `(aabf-eval ,(caar x) env man))
                         (u `(bools->uint (aabflist-eval ,(caar x) env man)))
                         (s `(bools->int (aabflist-eval ,(caar x) env man)))
                         (ru `(bools->uint (aabflist-eval (acl2::rev ,(caar x)) env man)))
                         (rs `(bools->int (aabflist-eval (acl2::rev ,(caar x)) env man)))))
                 (defsymbolic-formals-pair-with-evals (cdr x))))))



(defun defsymbolic-define-formals (x)
  (cond ((atom x) nil)
        ((eq (car x) 'man) '(man))
        (t (cons (case (cadar x)
                   (n `(,(caar x) natp))
                   (i `(,(caar x) integerp))
                   (p `(,(caar x) posp))
                   ((u s ru rs) `(,(caar x) true-listp))
                   (t (caar x)))
                 (defsymbolic-define-formals (cdr x))))))

(defun defsymbolic-guards (x takes-man)
  (cond ((atom x) nil)
        ((eq (car x) 'man) nil)
        (t (append (case (cadar x)
                     ((u s ru rs) (and takes-man
                                      `((aabflist-p ,(caar x) man))))
                     (b (and takes-man
                             `((aabf-p ,(caar x) man)))))
                   (defsymbolic-guards (cdr x) takes-man)))))

(defun defsymbolic-define-returns1 (x)
  (cond ((atom x) nil)
        ((eq (car x) 'new-man) '(new-man))
        (t (cons (case (cadar x)
                   (n `(,(caar x) natp :rule-classes :type-prescription))
                   (i `(,(caar x) integerp :rule-classes :type-prescription))
                   (p `(,(caar x) posp :rule-classes :type-prescription))
                   (b `(,(caar x) t))
                   (t `(,(caar x) true-listp :rule-classes :type-prescription)))
                 (defsymbolic-define-returns1 (cdr x))))))

(defun defsymbolic-define-returns (x)
  (let ((rets (defsymbolic-define-returns1 x)))
    (if (atom (cdr rets))
        (car rets)
      (cons 'mv rets))))

(defun defsymbolic-define-returns1-nothms (x)
  (cond ((atom x) nil)
        ((eq (car x) 'new-man) '(new-man))
        (t (cons (caar x);; (case (cadar x)
                   ;; (n `(,(caar x) natp :rule-classes :type-prescription))
                   ;; (i `(,(caar x) integerp :rule-classes :type-prescription))
                   ;; (p `(,(caar x) posp :rule-classes :type-prescription))
                   ;; (b `(,(caar x) t))
                   ;; (t `(,(caar x) true-listp :rule-classes :type-prescription)))
                 (defsymbolic-define-returns1-nothms (cdr x))))))

(defun defsymbolic-define-returns-nothms (x)
  (let ((rets (defsymbolic-define-returns1-nothms x)))
    (if (atom (cdr rets))
        (car rets)
      (cons 'mv rets))))


(defun defsymbolic-define-return-thms (x)
  (declare (xargs :mode :program))
  (cond ((atom x) nil)
        ((eq (car x) 'new-man) nil)
        ((eq (cadar x) 'b)
         (defsymbolic-define-return-thms (cdr x)))
        (t (cons (let ((pred (case (cadar x)
                               (n 'natp)
                               (i 'integerp)
                               (p 'posp)
                               (t 'true-listp))))
                   `(defret ,(intern$ (str::cat (symbol-name pred) "-OF-<FN>." (symbol-name (caar x))) "FGL")
                      (,pred ,(caar x))
                      :rule-classes :type-prescription
                      :hints nil))
                 (defsymbolic-define-return-thms (cdr x))))))

(defun defsymbolic-spec-term (formal-evals retspec)
  (if (eql (len retspec) 3)
      (sublis formal-evals (third retspec))
    (if (and (eql (len retspec) 5)
             (eq (fourth retspec) :cond))
        `(implies ,(sublis formal-evals (fifth retspec))
                  ,(sublis formal-evals (third retspec)))
      (er hard? 'defsymbolic "bad return-spec: ~x0~%" retspec))))

(defun defsymbolic-return-specs (x formal-evals man)
  (cond ((atom x) nil)
        ((eq (car x) 'new-man) nil)
        (t (append (b* ((spec-term (defsymbolic-spec-term formal-evals (car x))))
                     (case (cadar x)
                       ((n i p) (and (third (car x))
                                     `((equal ,(caar x)
                                              ,spec-term))))
                       (b `((equal (aabf-eval ,(caar x) env ,man)
                                   ,spec-term)))
                       (u `((equal (bools->uint (aabflist-eval ,(caar x) env ,man))
                                   ,spec-term)))
                       (s `((equal (bools->int (aabflist-eval ,(caar x) env ,man))
                                   ,spec-term)))
                       (ru `((equal (bools->uint (aabflist-eval (acl2::rev ,(caar x)) env ,man))
                                    ,spec-term)))
                       (rs `((equal (bools->int (aabflist-eval (acl2::rev ,(caar x)) env ,man))
                                    ,spec-term)))))
                   (defsymbolic-return-specs (cdr x) formal-evals man)))))

(defun defsymbolic-return-vars (x)
  (cond ((atom x) nil)
        ((eq (car x) 'new-man) '(new-man))
        (t (cons (caar x)
                 (defsymbolic-return-vars (cdr x))))))

(defun defsymbolic-aabf-pred (x man)
  (if (atom x)
      nil
    (if (atom (car x))
        nil
      (append (case (cadar x)
                (b `((aabf-pred ,(caar x) ,man)))
                ((u s ru rs) `((aabflist-pred ,(caar x) ,man))))
              (defsymbolic-aabf-pred (cdr x) man)))))

(defun defsymbolic-aabf-p (x man)
  (if (atom x)
      nil
    (if (atom (car x))
        nil
      (append (case (cadar x)
                (b `((aabf-p ,(caar x) ,man)))
                ((u s ru rs) `((aabflist-p ,(caar x) ,man))))
              (defsymbolic-aabf-p (cdr x) man)))))

(defun defsymbolic-fake-stobjs (x)
  (update-nth (1- (len x)) 'man nil))

(defun induct/expand-fn (fn formals free id world)
  (declare (xargs :mode :program))
  (and (not (acl2::access acl2::clause-id id :pool-lst))
       (append (and (recursivep fn t world)
                    `(:induct (,fn . ,formals)))
               `(:expand ((:free ,free (,fn . ,formals)))
                 :in-theory (disable (:d ,fn))))))

(defmacro induct/expand (fn formals free)
  `(induct/expand-fn ',fn ',formals ',free id world))

(defun reproduce-keyword-args (keys kwd-alist)
  (if (atom keys)
      nil
    (let ((look (assoc (car keys) kwd-alist)))
      (if look
          (list* (car keys) (cdr look)
                 (reproduce-keyword-args (cdr keys) kwd-alist))
        (reproduce-keyword-args (cdr keys) kwd-alist)))))

(defun defsymbolic-fn (name args)
  (declare (xargs :mode :program))
  (b* (((mv args post-///) (std::split-/// 'defsymbolic args))
       ((mv pre-post-/// post-///) (std::split-/// 'defsymbolic post-///))
       ((mv kwd-alist other-kws other-args)
        (extract-some-keywords
         '(:spec :returns :correct-hints :type-hints :pred-hints :pres-hints :correct-hyp :abstract :guard-hints
           :already-defined :no-hints :prepwork :enabled :custom :ignore-ok :irrelevant-formals-ok :no-define)
         args nil))
       ((unless (eql (len other-args) 2))
        (er hard? 'defsymbolic-fn "Need formals and body in addition to keyword args"))
       (formals (car other-args))
       (body (cadr other-args))
       ;; (abstractp (std::getarg :abstract nil kwd-alist))
       (returns (cdr (assoc :returns kwd-alist)))
       ((unless (or (consp returns)
                    (cdr (assoc :custom kwd-alist))))
        (er hard? 'defsymbolic-fn "Need a returns list"))
       (returns (if (eq (car returns) 'mv)
                    (cdr returns)
                  (list returns)))
       (- (defsymbolic-check-formals formals))
       (- (and (not (cdr (Assoc :custom kwd-alist)))
               (defsymbolic-check-returns returns)))
       (return-vars (and (not (cdr (assoc :custom kwd-alist)))
                         (defsymbolic-return-vars returns)))
       (formal-vars (defsymbolic-formal-vars formals))
       ((when (intersectp-eq return-vars formal-vars))
        (er hard? 'defsymbolic-fn "Formals and returns overlap"))
       (return-binder (if (atom (cdr return-vars)) (car return-vars) (cons 'mv return-vars)))
       ;; (take-man (member-eq 'man formals))
       (return-man (if (member-eq 'new-man returns) 'new-man 'man))
       (exec-name ;; (if abstractp
        ;;     (intern-in-package-of-symbol
        ;;      (concatenate 'string (symbol-name name) "-EXEC")
        ;;      name)
        name)
       (auto-hint (and (not (std::getarg :no-hints nil kwd-alist))
                       `((induct/expand ,exec-name ,formal-vars nil)))))

    `(progn
       ;; NOTE: We make some assumptions about the forms produced by
       ;; defsymbolic in bfr-arithmetic.lisp (specifically, aabf-form-to-bfr).
       ;;  - There is only one TABLE event (and its CAR is the only occurrence of the symbol TABLE.)
       ;;  - The only hints that should be replaced with functional
       ;;  instantiations are inside DEFTHM events.
       ;;  - The only names that are introduced (and need replacing) are the
       ;;  function name and the theorem names, which occur as DEFTHM events.

       (,@(if (std::getarg :already-defined nil kwd-alist)
              `(defsection ,exec-name
                 (local (in-theory (enable ,exec-name)))
                 ,@(and (not (cdr (assoc :no-define kwd-alist)))
                        `((local (std::set-define-current-function ,exec-name)))))
            `(define ,exec-name ,(defsymbolic-define-formals formals)
               ,@other-kws
               :verify-guards nil
               :guard (and . ,(defsymbolic-guards formals (consp (member-eq 'man formals))))
               ,@(reproduce-keyword-args '(:enabled :irrelevant-formals-ok :ignore-ok)
                                         kwd-alist)
               :returns ,(if (cdr (assoc :custom kwd-alist))
                             (cdr (assoc :returns kwd-alist))
                           (defsymbolic-define-returns-nothms returns))
               :prepwork
               ((def-manret-binder ,name
                  :takes-man ,(consp (member-eq 'man formals))
                  :returns-man ,(consp (member-eq 'new-man returns)))
                . ,(cdr (assoc :prepwork kwd-alist)))

               ,(subst exec-name name body)
               ///))

          ,@pre-post-///

          ,@(and ;; (not (cdr (assoc :enabled kwd-alist)))
                 (not (cdr (assoc :no-define kwd-alist)))
                 `((defret trivial-theorem-about-<fn>
                     (b* ((?ignore (,exec-name . ,formal-vars)))
                       t)
                     :rule-classes nil
                     :hints nil)))

          
          ,@(and (not (cdr (assoc :custom kwd-alist)))
                 `(,@(and (not (std::getarg :already-defined nil kwd-alist))
                          (defsymbolic-define-return-thms returns))
                     (local (in-theory (disable (:d ,exec-name))))

                  ,@(and (member-eq 'new-man returns)
                         `((defret aabf-extension-p-of-<fn>
                             (aabf-extension-p new-man man)
                             :hints (,@auto-hint))
                           (acl2::set-prev-stobjs-correspondence ,name
                                                                 :stobjs-out
                                                                 ,(defsymbolic-fake-stobjs returns)
                                                                 :formals
                                                                 ,formal-vars)))

                  (defthm ,(intern$
                            (concatenate 'string "AABF-P-OF-" (symbol-name exec-name))
                            "FGL")
                    (b* ((,return-binder (,exec-name . ,formal-vars)))
                      (implies (and . ,(defsymbolic-aabf-p formals 'man))
                               (and . ,(defsymbolic-aabf-p returns return-man))))
                    :hints (,@auto-hint
                            . ,(subst exec-name name (cdr (assoc :type-hints kwd-alist)))))

                  (defthm ,(intern$
                            (concatenate 'string "AABF-EVAL-OF-" (symbol-name exec-name))
                            "FGL")
                    (b* ((,return-binder (,exec-name . ,formal-vars)))
                      ,(let* ((concl `(and . ,(defsymbolic-return-specs returns
                                                (defsymbolic-formals-pair-with-evals formals)
                                                return-man)))
                              (correct-hyp (cdr (assoc :correct-hyp kwd-alist)))
                              (aabfp-hyp (defsymbolic-aabf-p formals 'man))
                              (hyps `(and ,@aabfp-hyp . ,(and correct-hyp (list correct-hyp)))))
                         `(implies ,hyps ,concl)))
                    :hints (,@auto-hint
                            . ,(subst exec-name name (cdr (assoc :correct-hints kwd-alist)))))

                  (defthm ,(intern$
                            (concatenate 'string "AABF-PRED-OF-" (symbol-name exec-name))
                            "FGL")
                    (b* ((,return-binder (,exec-name . ,formal-vars)))
                      (implies (and ,@(defsymbolic-aabf-p formals 'man)
                                    . ,(defsymbolic-aabf-pred formals 'man))
                               (and . ,(defsymbolic-aabf-pred returns return-man))))
                    :hints (,@auto-hint
                            . ,(subst exec-name name (cdr (assoc :pred-hints kwd-alist)))))))

          ;; ,@(and (member 'man formals)
          ;;        (not (member 'new-man returns))
          ;;        `((defthmd ,(intern$
          ;;                    (concatenate 'string "AABF-EXTENSION-PRESERVES-" (symbol-name exec-name))
          ;;                    "FGL")
          ;;            (implies (and (bind-aabf-extension new old)
          ;;                          ;; . ,(defsymbolic-aabf-p formals 'old)
          ;;                          )
          ;;                     (equal (,exec-name . ,(subst 'new 'man formal-vars))
          ;;                            (,exec-name . ,(subst 'old 'man formal-vars))))
          ;;            :hints (,@(and (not (std::getarg :no-hints nil kwd-alist))
          ;;                           `((induct/expand ,exec-name ,formal-vars (man))
          ;;                             '(:in-theory (enable* aabf-extension-preserves-rules))))
          ;;                      . ,(subst exec-name name (cdr (assoc :pres-hints kwd-alist)))))
          ;;          (add-to-ruleset! aabf-extension-preserves-rules
          ;;                           ,(intern$
          ;;                             (concatenate 'string "AABF-EXTENSION-PRESERVES-" (symbol-name exec-name))
          ;;                             "FGL"))))
          


          ,@post-///

          (verify-guards+ ,exec-name
            :hints ,(cdr (assoc :guard-hints kwd-alist)))
          
          (table defsymbolic-forms ',name ',args)))))

(defmacro defsymbolic (name &rest args)
  (defsymbolic-fn name args))



(local (in-theory (e/d* (acl2::ihsext-redefs
                         acl2::ihsext-inductions))))

(local (in-theory (disable (force) acl2::logext**
                           acl2::logext-identity
                           truncate)))


(local (defthm aabflist-eval-when-consp
         (implies (consp x)
                  (equal (aabflist-eval x env man)
                         (cons (aabf-eval (car x) env man)
                               (aabflist-eval (cdr x) env man))))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (defthm aabflist-eval-when-atom
         (implies (not (consp x))
                  (equal (aabflist-eval x env man) nil))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (defthm consp-of-aabflist-eval
         (equal (consp (aabflist-eval x env man))
                (consp x))))

(local (defthm bools->int-of-cons-when-consp
         (implies (consp b)
                  (equal (bools->int (cons a b))
                         (intcons a (bools->int b))))
         :hints(("Goal" :in-theory (enable bools->int)))))

(local (defthm bools->int-of-end
         (equal (bools->int (list a))
                (endint a))
         :hints(("Goal" :in-theory (enable bools->int)))))

(local (defthm bools->uint-of-cons
         (equal (bools->uint (cons a b))
                (intcons a (bools->uint b)))
         :hints(("Goal" :in-theory (enable bools->uint)))))

(local (defthm logcar-of-bools->int
         (equal (logcar (bools->int x))
                (bool->bit (car x)))
         :hints(("Goal" :in-theory (enable bools->int)))))

(local (defthm logcdr-of-minus-bit
         (implies (bitp b)
                  (equal (logcdr (- b)) (- b)))
         :hints(("Goal" :in-theory (enable bitp)))))



(local (defthm logcons-bit-minus-bit
         (implies (bitp b)
                  (equal (logcons b (- b))
                         (- b)))
         :hints(("Goal" :in-theory (enable bitp)))))

(local (defthm logcar-of-bools->uint
         (equal (logcar (bools->uint x))
                (bool->bit (car x)))
         :hints(("Goal" :in-theory (enable bools->uint)))))

(defmacro car/cdr (x)
  `(let* ((a ,x))
     (mbe :logic (mv (car a) (cdr a))
          :exec (if (atom a) (mv nil nil) (mv (car a) (cdr a))))))

(defsymbolic aabf-car ((vec s))
  :returns (bit b (intcar vec))
  (if (atom vec)
      (aabf-false)
    (car vec)))

(local (defthm aabf-eval-of-aabf-car-is-car-of-aabflist-eval
         (equal (aabf-eval (aabf-car v) env man)
                (car (aabflist-eval v env man)))
         :hints(("Goal" :in-theory (enable aabf-car)))))

(local (in-theory (disable aabf-eval-of-aabf-car)))

;; (defthm aabf-car-when-consp
;;   (implies (consp v)
;;            (equal (aabf-car v)
;;                   (car v)))
;;   :hints(("Goal" :in-theory (enable aabf-car)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

;; (defthm aabf-car-when-not-consp
;;   (implies (not (consp v))
;;            (equal (aabf-car v)
;;                   (aabf-false)))
;;   :hints(("Goal" :in-theory (enable aabf-car)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

(fty::deffixequiv aabflist-eval :args ((x true-listp)))
(fty::deffixequiv aabflist-p :args ((x true-listp)))
(fty::deffixequiv aabflist-pred :args ((x true-listp)))


(defthm acl2-count-of-true-list-fix
  (<= (acl2-count (true-list-fix x)) (acl2-count x))
  :rule-classes :linear)

(defsymbolic scdr ((v s)) nil
  :returns (cdr s (intcdr v))
  :already-defined t)

(local (in-theory (disable aabf-eval-of-scdr)))

(defsymbolic cdr ((x u)) nil
  :returns (cdr u (intcdr x))
  :no-hints t
  :no-define t
  :already-defined t)

(local (in-theory (disable aabf-eval-of-cdr)))

(local (defthm aabflist-eval-of-cdr-when-s-endp
         (implies (s-endp v)
                  (equal (aabflist-eval (cdr v) env man) nil))
         :hints(("Goal" :in-theory (enable s-endp)))))

(defsymbolic aabf-scons ((b b) (v s))
  :returns (res s (intcons b v))
  (b* ((v (llist-fix v)))
    (if (atom v)
        (if (aabf-syntactically-equal b (aabf-false))
            (list (aabf-false))
          (list b (aabf-false)))
      (if (s-endp v)
          (if (aabf-syntactically-equal b (car v))
              v
            (cons b v))
        (cons b v)))))

;; (defsymbolic aabf-endint ((b b))
;;   :returns (end s (endint b))
;;   (list b))

(defsymbolic aabf-ucons ((b b) (v u))
  :returns (res u (intcons b v))
  (cons b (llist-fix v)))

(Defthm car-of-aabf-ucons
  (equal (car (aabf-ucons b v)) b)
  :hints(("Goal" :in-theory (enable aabf-ucons))))

(Defthm cdr-of-aabf-ucons
  (equal (cdr (aabf-ucons b v)) (llist-fix v))
  :hints(("Goal" :in-theory (enable aabf-ucons))))

(defthm logcons-uint-car-cdr
  (equal (logcons (bool->bit (car v))
                  (bools->uint (cdr v)))
         (bools->uint v))
  :hints(("Goal" :in-theory (enable bools->uint))))

(defthm aabflist-eval-of-scdr
  (equal (aabflist-eval (scdr v) env man)
         (scdr (aabflist-eval v env man)))
  :hints(("Goal" :in-theory (enable scdr))))

(defthm bools->int-redef
  (equal (bools->int x)
         (if (s-endp x)
             (endint (car x))
           (intcons (car x) (bools->int (scdr x)))))
  :hints(("Goal" :in-theory (enable s-endp scdr bools->int)))
  :rule-classes :definition)

(defthmd logcons-sint-car-cdr
  (equal (logcons (bool->bit (car v))
                  (bools->int (scdr v)))
         (bools->int v))
  :hints(("Goal" :in-theory (enable bools->int scdr))))

(defthm aabflist-p-of-nil
  (aabflist-p nil man))

(defthm aabflist-p-when-consp
  (implies (consp x)
           (equal (aabflist-p x man)
                  (and (aabf-p (car x) man)
                       (aabflist-p (cdr x) man))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm aabflist-pred-of-nil
  (aabflist-pred nil man))

(defthm aabflist-pred-when-consp
  (implies (consp x)
           (equal (aabflist-pred x man)
                  (and (aabf-pred (car x) man)
                       (aabflist-pred (cdr x) man))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))


(defthm logcdr-of-bools->int
  (equal (logcdr (bools->int x))
         (bools->int (scdr x)))
  :hints(("Goal" :in-theory (enable scdr bools->int))))

(local (in-theory (disable not-s-endp-compound-recognizer
                           (:type-prescription aabf-scons)
                           aabflist-eval
                           aabflist-p
                           aabflist-pred)))




(defsymbolic aabf-ite-buu-fn-aux ((c b) ;; name c, type b (boolean)
                                 (v1 u) ;; unsigned
                                 (v0 u)
                                 man)
  :returns (mv (vv u (if c v1 v0))
               new-man)
  :abstract nil
  :measure (+ (acl2-count v1) (acl2-count v0))
  (b* (((when (and (atom v1) (atom v0)))
        (mv nil man))
       (v11 (aabf-car v1))
       (v1r (cdr v1))
       (v01 (aabf-car v0))
       (v0r (cdr v0))
       ((mv tail man) (aabf-ite-buu-fn-aux c v1r v0r man))
       ((mv head man) (aabf-ite c v11 v01 man)))
    (mv (aabf-ucons head tail) man)))

(defsymbolic aabf-ite-buu-fn ((c b) ;; name c, type b (boolean)
                             (v1 u) ;; unsigned
                             (v0 u)
                             man)
  :returns (mv (vv u (if c v1 v0))
               new-man)
  (cond ((aabf-syntactically-equal c (aabf-false))
         (mv (llist-fix v0) man))
        ((aabf-syntactically-equal c (aabf-true))
         (mv (llist-fix v1) man))
        (t (aabf-ite-buu-fn-aux c v1 v0 man))))

(defthm aabf-ite-buu-fn-aux-elim
  (implies (and (not (aabf-syntactically-equal c (aabf-false)))
                (not (aabf-syntactically-equal c (aabf-true))))
           (equal (aabf-ite-buu-fn-aux c v1 v0 man)
                  (aabf-ite-buu-fn c v1 v0 man)))
  :hints(("Goal" :in-theory (enable aabf-ite-buu-fn))))

;; limited in use since probably if v1 or v0 are expensive to compute they'll return a man also
(defmacro aabf-ite-buu (c v1 v0 man)
  `(mbe :logic (aabf-ite-buu-fn ,c ,v1 ,v0 ,man)
        :exec (let ((aabf-ite-buu-test ,c))
                (cond ((aabf-syntactically-equal abf-ite-buu-test (aabf-false))
                       (mv (llist-fix ,v0) man))
                      ((aabf-syntactically-equal abf-ite-buu-test (aabf-true))
                       (mv (llist-fix ,v1) man))
                      (t (aabf-ite-buu-fn-aux aabf-ite-buu-test ,v1 ,v0 ,man))))))


(add-macro-alias aabf-ite-buu aabf-ite-buu-fn)

(defsymbolic aabf-first/rest/end ((x s))
  :enabled t
  :custom t
  :guard-hints (("goal" :in-theory (enable aabf-car scdr s-endp)))
  :returns (mv first rest end)
  (mbe :logic (mv (aabf-car x) (scdr x) (s-endp x))
       :exec (cond ((atom x) (mv (aabf-false) x t))
                   ((atom (cdr x)) (mv (car x) x t))
                   (t (mv (car x) (cdr x) nil)))))


;; (defthm bools->int-of-aabflist-eval-when-not-endp
;;   (implies (not (s-endp v))
;;            (equal (bools->int (aabflist-eval v env man))
;;                   (intcons (car (aabflist-eval v env man))
;;                            (bools->int (aabflist-eval (scdr v) env man)))))
;;   :hints(("Goal" :in-theory (enable s-endp scdr))))

(defthm bools->int-of-aabflist-eval-when-endp
  (implies (s-endp v)
           (equal (bools->int (aabflist-eval v env man))
                  (endint (car (aabflist-eval v env man)))))
  :hints(("Goal" :in-theory (enable s-endp aabf-car))))



(defthm aabf-eval-car-of-scons
  (equal (aabf-eval (car (aabf-scons b v)) env man)
         (aabf-eval b env man))
  :hints(("Goal" :in-theory (enable aabf-scons))))

(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

(defsymbolic aabf-ite-bss-fn-aux ((c  b) ;; name c, type b (boolean)
                                 (v1 s) ;; signed
                                 (v0 s)
                                 man)
  :returns (mv (vv s (if c v1 v0)) new-man)
  :measure (+ (acl2-count v1) (acl2-count v0))
  (b* (((mv head1 tail1 end1) (aabf-first/rest/end v1))
       ((mv head0 tail0 end0) (aabf-first/rest/end v0))
       ((when (and end1 end0))
        (b* (((mv ite man) (aabf-ite c head1 head0 man)))
          (mv (list ite) man )))
       ((mv rst man) (aabf-ite-bss-fn-aux c tail1 tail0 man))
       ((mv head man) (aabf-ite c head1 head0 man)))
    (mv (aabf-scons head rst) man)))

(defsymbolic aabf-ite-bss-fn ((c  b) ;; name c, type b (boolean)
                              (v1 s) ;; signed
                              (v0 s)
                              man)
  :returns (mv (vv s (if c v1 v0))
               new-man)
  (cond ((aabf-syntactically-equal c (aabf-false))
         (mv (llist-fix v0) man))
        ((aabf-syntactically-equal c (aabf-true))
         (mv (llist-fix v1) man))
        (t (aabf-ite-bss-fn-aux c v1 v0 man))))

(defthm aabf-ite-bss-fn-aux-elim
  (implies (and (not (aabf-syntactically-equal c (aabf-false)))
                (not (aabf-syntactically-equal c (aabf-true))))
           (equal (aabf-ite-bss-fn-aux c v1 v0 man)
                  (aabf-ite-bss-fn c v1 v0 man)))
  :hints(("Goal" :in-theory (enable aabf-ite-bss-fn))))

(defthm aabf-ite-bss-fn-elim-false
  (implies (aabf-syntactically-equal c (aabf-false))
           (equal (aabf-ite-bss-fn c v1 v0 man)
                  (mv (llist-fix v0) man)))
  :hints(("Goal" :in-theory (enable aabf-ite-bss-fn))))

(defthm aabf-ite-bss-fn-elim-true
  (implies (aabf-syntactically-equal c (aabf-true))
           (equal (aabf-ite-bss-fn c v1 v0 man)
                  (mv (llist-fix v1) man)))
  :hints(("Goal" :in-theory (enable aabf-ite-bss-fn))))


;; limited in use since probably if v1 or v0 are expensive to compute they'll return a man also
(defmacro aabf-ite-bss (c v1 v0 man)
  `(mbe :logic (aabf-ite-bss-fn ,c ,v1 ,v0 ,man)
        :exec (let ((aabf-ite-bss-test ,c))
                (cond ((aabf-syntactically-equal aabf-ite-bss-test (aabf-false))
                       (mv (llist-fix ,v0) ,man))
                      ((aabf-syntactically-equal aabf-ite-bss-test (aabf-true))
                       (mv (llist-fix ,v1) ,man))
                      (t (aabf-ite-bss-fn-aux aabf-ite-bss-test ,v1 ,v0 ,man))))))

(def-manret-binder aabf-ite-bss)

(add-macro-alias aabf-ite-bss aabf-ite-bss-fn)

(local (in-theory (enable* bitops::ihsext-recursive-redefs)))

(defsymbolic aabf-loghead-ns ((n n)  ;; name n, type n (natp)
                             (x s)) ;; name x, type s (signed bvec)
  :returns (xx s (loghead n x))     ;; return name, type (signed bvec), spec
  (b* (((when (zp n))
        (list (aabf-false)))
       ((mv head tail ?end) (aabf-first/rest/end x)))
    (aabf-scons head (aabf-loghead-ns (1- n) tail))))

(defsymbolic aabf-logext-ns ((n p)  ;; name n, type p (posp)
                            (x s)) ;; name x, type s (signed bvec)
  :returns (xx s (acl2::logext n x))     ;; return name, type (signed bvec), spec
  :measure (acl2::pos-fix n)
  (b* ((n (lposfix n))
       ((mv head tail ?end) (aabf-first/rest/end x))
       ((when end) (llist-fix x))
       ((when (eql n 1)) (list head)))
    (aabf-scons head (aabf-logext-ns (1- n) tail))))

(local (defthm logtail-of-minus-bit
         (implies (bitp b)
                  (equal (logtail n (- b))
                         (- b)))
         :hints(("Goal" :in-theory (enable bitp)))))

(defsymbolic aabf-logtail-ns ((place n)
                             (x s))
  :returns (xx s (logtail place x))
  (if (or (zp place) (s-endp x))
      (llist-fix x)
    (aabf-logtail-ns (1- place) (scdr x))))


         

(defthm s-endp-of-aabflist-eval
  (equal (s-endp (aabflist-eval x env man))
         (s-endp x))
  :hints(("Goal" :in-theory (enable s-endp))))

(local (defthm xor-nil
         (and (equal (xor x nil)
                     (bool-fix x))
              (equal (xor nil x)
                     (bool-fix x)))))

(local (defthm xor-t
         (implies x
                  (and (iff (xor x y) (not y))
                       (iff (xor y x) (not y))))))

(local (defcong iff equal (if* a b c) 1))

;; (local (defthm bool->bit-of-and*
;;          (equal (bool->bit (and* x y))
;;                 (b-and x y))))

;; (local (defthm bool->bit-of-or*
;;          (equal (bool->bit (or* x y))
;;                 (b-ior x y))))

;; (local (defthm bool->bit-of-xor
;;          (equal (bool->bit (xor x y))
;;                 (b-xor x y))))
                  
(local (defthm bool->bit-of-xor
         (equal (bool->bit (xor a b))
                (b-xor (bool->bit a) (bool->bit b)))))

(local (defthm bool->bit-of-and*
         (equal (bool->bit (and* a b))
                (b-and (bool->bit a) (bool->bit b)))
         :hints(("Goal" :in-theory (enable and*)))))

(local (defthm bool->bit-of-or*
         (equal (bool->bit (or* a b))
                (b-ior (bool->bit a) (bool->bit b)))
         :hints(("Goal" :in-theory (enable or*)))))

(local (defthm bool->bit-of-if*
         (equal (bool->bit (if* a b c))
                (acl2::b-ite (bool->bit a) (bool->bit b) (bool->bit c)))
         :hints(("Goal" :in-theory (enable if*)))))

(local (in-theory (disable not xor if*)))

(local (in-theory (e/d* (bitops::logxor**) (bitops::logxor$))))

(local (defthm plus-identity-1
         (equal (+ (b-and a b) (b-and c (b-xor a b)))
                (b-ior (b-and a b) (b-and c (b-xor a b))))
         :hints(("Goal" :in-theory (enable b-and b-xor b-ior)))))

(local (defthm plus-identity-2
         (implies (and (bitp a) (bitp b))
                  (equal (+ (- a) (- b) (b-ior (b-and a b) (b-and c (b-xor a b))))
                         (- (acl2::b-ite (b-xor a b) (b-not c) a))))
         :hints(("Goal" :in-theory (enable bitp b-not)))))

(defsymbolic aabf-+-ss ((c b)
                       (v1 s)
                       (v2 s)
                       man)
  :returns (mv (sum s (+ (acl2::bool->bit c) v1 v2))
               new-man)
  :measure (+ (len v1) (len v2))
  (b* (((mv head1 tail1 end1) (aabf-first/rest/end v1))
       ((mv head2 tail2 end2) (aabf-first/rest/end v2))
       ((mv axorb man) (aabf-xor head1 head2 man))
       ((mv s man)     (aabf-xor c axorb man))
       ((when (and end1 end2))
        (b* (((mv last man) (aabf-ite axorb (aabf-not c man) head1 man)))
          (mv (aabf-scons s (list last)) man)))
       ;; BOZO think about this.  Using axorb here seems like a good idea since
       ;; we're already computing it anyway in order to compute S.  However, we
       ;; could instead do something like:
       ;;    (c   (aabf-or  (aabf-and c head1)
       ;;                  (aabf-and c head2)
       ;;                  (aabf-and head1 head2)))
       ;; This wouldn't share the same structure but might result in a simpler
       ;; carry in being delivered to the rest of the sum, which might be a win.
       ;; It's hard to guess whether this would be better or worse, so for now
       ;; we'll just leave it alone...
       ((mv c man) (aabf-nest (or (and c axorb)
                                  (and head1 head2))
                              man))
       ((mv rst man) (aabf-+-ss c tail1 tail2 man)))
    (mv (aabf-scons s rst) man))
  :correct-hints ((and stable-under-simplificationp
                       '(:in-theory (enable bitops::equal-logcons-strong)))))



(defsymbolic aabf-lognot-s ((x s) man)
  :returns (nx s (lognot x))
  (b* (((mv head tail end) (aabf-first/rest/end x))
       ((when end)
        (list (aabf-not head man))))
    (aabf-scons (aabf-not head man)
                (aabf-lognot-s tail man)))
  :correct-hints ((and stable-under-simplificationp
                       '(:in-theory (e/d (bools->int-redef)
                                         (logcons-sint-car-cdr))))))

(defsymbolic aabf-unary-minus-s ((x s) man)
  :returns (mv (ms s (- x)) new-man)
  (aabf-nest (aabf-+-ss (aabf-true) nil (aabf-lognot-s x)) man)
  :correct-hints ('(:in-theory (e/d (lognot) (bitops::lognot$ bitops::lognot**)))))

;; (local (in-theory (e/d  (bitops::logxor$) (bitops::logxor**))))

;; (local (defthmd scdr-when-s-endp-strong
;;          (implies (s-endp x)
;;                   (equal (scdr x) (llist-fix x)))))


(defsymbolic aabf-logxor-ss ((a s)
                             (b s)
                             man)
  :returns (mv (xab s (logxor a b)) new-man)
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (aabf-first/rest/end a))
       ((mv bf br bend) (aabf-first/rest/end b))
       ((mv c man) (aabf-xor af bf man))
       ((when (and aend bend))
        (mv (list c) man)))
    (aabf-nest (aabf-scons c (aabf-logxor-ss ar br)) man))
  :correct-hints ('(:in-theory (e/d ()
                                    (bools->int-redef
                                     logcons-sint-car-cdr bitops::logxor** bitops::logxor$)))
                  (acl2::use-termhint
                   (b* (((when (and (s-endp a) (s-endp b)))
                         '(:in-theory (e/d (bitops::logxor$)
                                           (bitops::logxor**)))))
                     '(:in-theory (e/d (bools->int-redef
                                        bitops::logxor**)
                                       (logcons-sint-car-cdr
                                        ;; scdr-when-s-endp
                                        bitops::logxor$)))))))

(local (defthm bit-gt-0
         (implies (bitp b)
                  (equal (< 0 b)
                         (acl2::bit->bool b)))
         :hints(("Goal" :in-theory (enable bitp)))))

(local (defthm booleanp-car-of-aabflist-eval
         (booleanp (car (aabflist-eval x env man)))
         :hints(("Goal" :in-theory (enable aabflist-eval)))
         :rule-classes :type-prescription))

(local (defthm not-not
         (equal (not (not x))
                (bool-fix x))
         :hints(("Goal" :in-theory (enable bool-fix)))))

(defsymbolic aabf-sign-s ((x s))
  :returns (sign b (< x 0))
  (b* (((mv first rest endp) (aabf-first/rest/end x))
       ((when endp)
        first))
    (aabf-sign-s rest))
  :correct-hints
  ((and stable-under-simplificationp
        '(:in-theory (e/d (bools->int-redef)
                          (logcons-sint-car-cdr))))))

(defsymbolic int->aabflist ((x i))
  :returns (v s x)
  :measure (integer-length x)
  (cond ((zip x) (list (aabf-false)))
        ((eql x -1) (list (aabf-true)))
        (t (cons (if (eql (logcar x) 1) (aabf-true) (aabf-false))
                 (int->aabflist (logcdr x)))))
  ///
  (local (in-theory (disable (int->aabflist))))
  (local (add-default-hints '((and stable-under-simplificationp
                                   '(:expand ((int->aabflist -1)))))))
  ///)

;; (defthm aabf-p-of-car-when-aabflist-p-and-not-endp
;;   (implies (and (aabflist-p x man)
;;                 (not (s-endp x)))
;;            (aabf-p (car x) man))
;;   :hints(("Goal" :in-theory (enable s-endp aabflist-p))))

;; (local (defthmd bools->int-equal-const-when-not-endp
;;          (implies (and (not (s-endp x))
;;                        (syntaxp (quotep i))
;;                        (syntaxp (or (acl2::rewriting-negative-literal-fn
;;                                      `(equal (bools->int ,x) ,i) mfc state)
;;                                     (acl2::rewriting-negative-literal-fn
;;                                      `(equal ,i (bools->int ,x)) mfc state))))
;;                   (iff (equal (bools->int x) i)
;;                        (and (integerp i)
;;                             (iff (car x) (acl2::bit->bool (logcar i)))
;;                             (equal (bools->int (scdr x)) (logcdr i)))))))

;; (local (defthmd bools->int-equal-const-when-endp
;;          (implies (and (s-endp x)
;;                        (syntaxp (quotep i))
;;                        (syntaxp (or (acl2::rewriting-negative-literal-fn
;;                                      `(equal (bools->int ,x) ,i) mfc state)
;;                                     (acl2::rewriting-negative-literal-fn
;;                                      `(equal ,i (bools->int ,x)) mfc state))))
;;                   (iff (equal (bools->int x) i)
;;                        (cond ((equal i 0) (not (car x)))
;;                              ((equal i -1) (car x))
;;                              (t nil))))))

;; (local (defthmd bools->int-equal-const-when-endp
;;          (implies (and (s-endp x)
;;                        (syntaxp (quotep i))
;;                        (syntaxp (or (acl2::rewriting-negative-literal-fn
;;                                      `(equal (bools->int ,x) ,i) mfc state)
;;                                     (acl2::rewriting-negative-literal-fn
;;                                      `(equal ,i (bools->int ,x)) mfc state))))
;;                   (iff (equal (bools->int x) i)
;;                        (cond ((equal i 0) (not (car x)))
;;                              ((equal i -1) (car x))
;;                              (t nil))))))

(defcong iff equal (xor a b) 1)
(defcong iff equal (xor a b) 2)

;; (local (defthm rewrite-equal-boolean-under-iff
;;          (implies (and (booleanp x)
;;                        (iff xx (double-rewrite x)) ;; bind xx
;;                        (booleanp xx)
;;                        (not (syntaxp (equal x xx))))
;;                   (equal (equal x y)
;;                          (equal xx y)))

(defsymbolic aabf-integer-length-s1 ((offset p)
                                     (x s)
                                     man)
  :measure (len x)
  :returns (mv (not-done b (and (not (equal x 0))
                                (not (equal x -1))))
               (ilen s (if (or (equal x 0)
                               (equal x -1))
                           0
                         (+ -1 offset (integer-length x))))
               new-man)
  :guard-hints (("Goal" :in-theory (e/d (aabf-ite-bss-fn)
                                        (aabf-ite-bss-fn-aux-elim))))
  :prepwork ((local (defthm car-when-bools->int-equal
                      (implies (and (equal (bools->int x) i)
                                    (syntaxp (quotep i)))
                               (iff (car x) (acl2::bit->bool (logcar i))))))
             (local (in-theory (disable AABFLIST-EVAL-WHEN-CONSP))))
  ;; :prepwork ((local (defthm aabf-eval-of-car-when-bools->int
  ;;                     (implies (and (equal (bools->int (aabflist-eval x env man)) c)
  ;;                                   (syntaxp (quotep c)))
  ;;                              (equal (aabf-eval (car x) env)
  ;;                                     (equal 1 (logcar c)))))))
  (b* (((mv first rest end) (aabf-first/rest/end x))
       (offset (lposfix offset))
       ((when end)
        (mv (aabf-false) nil man))
       ((mv changed rest-len man)
        (aabf-integer-length-s1 (1+ offset) rest man))
       ((when (aabf-syntactically-equal changed (aabf-true)))
        (mv (aabf-true) rest-len man))
       ((mv change man) (aabf-xor first (aabf-car rest) man))
       ((mv ans man)
        (aabf-nest
         (aabf-ite-bss-fn changed rest-len
                          (aabf-ite-bss-fn change (int->aabflist offset) nil))
         man))
       ((mv full-change man)
        (aabf-nest (aabf-or changed change) man)))
    (mv full-change ans man)))

(defsymbolic aabf-integer-length-s ((x s) man)
  :returns (mv (ilen s (integer-length x)) new-man)
  (b* (((mv ?changed res man) (aabf-integer-length-s1 1 x man)))
    (mv res man)))

(defsymbolic aabf-integer-length-bound-s ((x s) man)
  :ignore-ok t  :irrelevant-formals-ok t
  :custom t
  :returns (bound posp :rule-classes :type-prescription)
  (max (len x) 1)
  /// ///
  (local 
   (defthm s-endp-true-by-len
     (implies (<= (len x) 1)
              (s-endp x))
     :hints(("Goal" :in-theory (enable s-endp)))))
  (defthm aabf-integer-length-bound-s-correct
    (< (integer-length (bools->int (aabflist-eval x env man)))
       (aabf-integer-length-bound-s x man))
    :hints (("goal" :induct (len x)
             :in-theory (e/d (aabf-integer-length-bound-s)
                             ( bools->int-redef bools->int
                                                aabflist-eval-when-consp))
             :expand ((aabflist-eval x env man)
                      (:with bools->int (:free (a b) (bools->int (cons a b)))))))
    :rule-classes :linear))

(defsymbolic aabf-abs-s ((x s) man)
  :returns (mv (xabs s (abs x)) new-man)
  :prepwork ((local (in-theory (enable loghead-of-integer-length-nonneg)))
             (local (defthm loghead-of-abs-2
                      (implies (and (< (integer-length x) (nfix n))
                                    (integerp x)
                                    (< x 0))
                               (equal (loghead n (- x))
                                      (- x)))
                      :hints(("Goal" :induct (loghead n x)
                              :expand ((loghead n (- x)))
                              :in-theory (disable acl2::loghead**))
                             (and stable-under-simplificationp
                                  '(:in-theory (e/d (logcons
                                                     bitops::minus-to-lognot)
                                                    (acl2::loghead**))))))))
  (b* ((bound (aabf-integer-length-bound-s x man))
       (sign (aabf-sign-s x))
       (sign-lst (list sign)))
    (aabf-nest (aabf-loghead-ns bound (aabf-+-ss sign nil (aabf-logxor-ss sign-lst x)))
               man))

  :correct-hints ('(:use (aabf-integer-length-bound-s-correct
                          aabf-eval-of-aabf-sign-s)
                    :in-theory (e/d* (lognot)
                                     (aabf-integer-length-bound-s-correct
                                      aabf-eval-of-aabf-sign-s
                                      bitops::lognot$
                                      acl2::ihsext-redefs)))))

;;(local (in-theory (disable aabflist-eval-when-consp)))

;; (defsymbolic aabf-iff ((x b) (y b) man)
;;   :returns (mv (iff b (iff x y)) new-man)
;;   (aabf-nest (aabf-not (aabf-xor x y)) man))


;; (defsymbolic aabf-=-uu ((a u) (b u) man)
;;   :returns (mv (a=b b (equal a b)) new-man)
;;   :measure (+ (len a) (len b))
;;   (b* (((when (and (atom a) (atom b)))
;;         (mv (aabf-true) man))
;;        (head1 (aabf-car a))
;;        (tail1 (cdr a))
;;        (head2 (aabf-car b))
;;        (tail2 (cdr b))
;;        ((mv first-diff man) (aabf-xor head1 head2 man))
;;        ((mv rest-same man) (aabf-=-uu tail1 tail2 man)))
;;     (aabf-and (aabf-not first-diff man) rest-same man)))

(defsymbolic aabf-=-ss ((a s) (b s) man)
  :returns (mv (a=b b (equal a b)) new-man)
  :measure (+ (len a) (len b))
  (b* (((mv head1 tail1 end1) (aabf-first/rest/end a))
       ((mv head2 tail2 end2) (aabf-first/rest/end b))
       ((when (and end1 end2))
        (aabf-iff head1 head2 man)))
    (aabf-nest (aabf-and (aabf-iff head1 head2)
                         (aabf-=-ss tail1 tail2))
               man))
  :correct-hints ((and stable-under-simplificationp
                       '(:in-theory (enable bitops::equal-logcons-strong)))))

(defsymbolic aabf-*-ss ((v1 s) (v2 s) man)
  :measure (+ (len v1) (len v2))
  :returns (mv (prod s (* v1 v2)) new-man)
  (b* (((mv dig1 rest end1) (aabf-first/rest/end v1))
       ((when end1)
        (aabf-nest (aabf-ite-bss dig1
                                 (aabf-unary-minus-s v2)
                                 nil)
                   man)))
    (aabf-nest (aabf-+-ss (aabf-false)
                          (aabf-ite-bss-fn dig1 v2 nil)
                          (aabf-scons (aabf-false) (aabf-*-ss rest v2)))
               man))
  :correct-hints ('(:in-theory (enable logcons))))

(defsymbolic aabf-syntactically-true-p ((x b) man)
  :ignore-ok t :irrelevant-formals-ok t
  :custom t
  :returns (true-p booleanp)
  (aabf-syntactically-equal x (aabf-true))
  /// ///
  (std::defretd aabf-syntactically-true-p-implies
    (implies (aabf-syntactically-true-p x man)
             (equal (aabf-eval x env man) t)))

  (std::defretd aabf-syntactically-true-p-rewrite
    (implies (and (acl2::rewriting-negative-literal `(aabf-syntactically-true-p ,x ,man))
                  (bind-free '((env . env)) (env)))
             (iff (aabf-syntactically-true-p x man)
                  (and (equal (aabf-eval x env man) t)
                       (hide (aabf-syntactically-true-p x man)))))
    :hints (("goal" :expand ((:free (x) (hide x)))))))

(defsymbolic aabf-syntactically-false-p ((x b) man)
  :ignore-ok t :irrelevant-formals-ok t
  :custom t
  :returns (false-p booleanp)
  (aabf-syntactically-equal x (aabf-false))
  /// ///
  (std::defretd aabf-syntactically-false-p-implies
    (implies (aabf-syntactically-false-p x man)
             (equal (aabf-eval x env man) nil)))

  (std::defretd aabf-syntactically-false-p-rewrite
    (implies (and (acl2::rewriting-negative-literal `(aabf-syntactically-false-p ,x ,man))
                  (bind-free '((env . env)) (env)))
             (iff (aabf-syntactically-false-p x man)
                  (and (equal (aabf-eval x env man) nil)
                       (hide (aabf-syntactically-false-p x man)))))
    :hints (("goal" :expand ((:free (x) (hide x)))))))

(local (in-theory (disable iff)))

(local (in-theory (disable bools->int-redef)))

(defthmd bools->int-open-once
  (equal (bools->int x)
         (intcons (car x)
                  (bools->int (scdr x))))
  :hints(("Goal" :in-theory (enable bools->int scdr)))
  :rule-classes ((:definition :install-body nil
                  :controller-alist ((bools->int t)))))

(defsymbolic aabf-<-=-ss ((a s) (b s) man)
  :measure (+ (len a) (len b))
  :returns (mv (a<b b (< a b))
               (a=b b (= a b))
               new-man)
  :hints (("goal" :in-theory (enable and*)))
  :prepwork ((local (in-theory (disable scdr-when-s-endp))))
  :correct-hints ('(:in-theory (e/d (aabf-syntactically-true-p-rewrite))
                    :do-not-induct t)
                  (acl2::use-termhint
                   (if (and* (s-endp a) (s-endp b))
                       '(:in-theory (enable and* bool->bit))
                     '(:computed-hint-replacement
                       ((and stable-under-simplificationp
                             '(:in-theory (enable and* or* not iff xor)))
                        (and stable-under-simplificationp
                             '(:in-theory (enable bitops::logcons-<-n-strong
                                                  bitops::logcons->-n-strong
                                                  bitops::equal-logcons-strong))))
                       :expand ((:with bools->int-open-once (bools->int (aabflist-eval a env man)))
                                (:with bools->int-open-once (bools->int (aabflist-eval b env man))))))))
  (b* (((mv head1 tail1 end1) (aabf-first/rest/end a))
       ((mv head2 tail2 end2) (aabf-first/rest/end b))
       ((when (and* end1 end2))
        (b* (((mv less man) (aabf-nest (and head1 (not head2)) man))
             ((mv equal man)
              (if (aabf-syntactically-true-p less man)
                  (mv (aabf-false) man)
                (aabf-iff head1 head2 man))))
          (mv less equal man)))
       ((mv rst< rst= man)
        (aabf-<-=-ss tail1 tail2 man))
       ((mv less man) (aabf-nest (or rst< (and rst= head2 (aabf-not head1))) man))
       ((mv equal man)
        (if (aabf-syntactically-true-p less man)
            (mv (aabf-false) man)
          (aabf-nest (aabf-and rst= (aabf-iff head1 head2)) man))))
    (mv less equal man)))

(defsymbolic aabf-syntactically-zero-p ((x s))
  :custom t
  :returns (result booleanp)
  ;; (b* (((mv head tail end) (aabf-first/rest/end x)))
  ;;   (and (aabf-syntactically-equal head (aabf-false))
  ;;        (or end
  ;;            (aabf-syntactically-zero-p tail))))
  (if (atom x)
      t
    (and (aabf-syntactically-equal (car x) (aabf-false))
         (aabf-syntactically-zero-p (cdr x))))
  /// ///
  (std::defretd aabf-syntactically-zero-p-implies
    (implies (aabf-syntactically-zero-p x)
             (equal (bools->int (aabflist-eval x env man)) 0))
    :hints (("goal" :induct t
             :in-theory (enable bools->int aabflist-eval))))

  (std::defretd aabf-syntactically-zero-p-implies-unsigned
    (implies (aabf-syntactically-zero-p x)
             (equal (bools->uint (aabflist-eval x env man)) 0))
    :hints (("goal" :induct t
             :in-theory (enable bools->uint aabflist-eval)))))

(defsymbolic aabf-syntactically-neg1-p ((x s))
  :returns (result booleanp)
  :custom t
  (b* (((mv head tail end) (aabf-first/rest/end x)))
    (and (aabf-syntactically-equal head (aabf-true))
         (or end
             (aabf-syntactically-neg1-p tail))))
  /// ///
  (std::defretd aabf-syntactically-neg1-p-implies
    (implies (aabf-syntactically-neg1-p x)
             (equal (bools->int (aabflist-eval x env man)) -1))
    :hints (("goal" :induct t
             :expand ((:with bools->int-open-once (bools->int (aabflist-eval x env man)))))
            '(:use ((:instance aabf-syntactically-equal-implies-equal-aabf-eval-1
                     (x (aabf-car x)) (x-equiv (aabf-true))))
              :in-theory (disable aabf-syntactically-equal-implies-equal-aabf-eval-1)))))

(defsymbolic aabf-syntactically-signext-p ((x s) (b b))
  :returns (result booleanp)
  :custom t
  (b* (((mv head tail end) (aabf-first/rest/end x)))
    (and (aabf-syntactically-equal head b)
         (or end
             (aabf-syntactically-signext-p tail b))))
  /// ///
  (local (defthm logcons-of-equal-neg-bit
           (implies (and (equal x (- b))
                         (bitp b))
                    (equal (logcons b x) (- b)))))

  (std::defretd aabf-syntactically-signext-p-implies
    (implies (aabf-syntactically-signext-p x b)
             (equal (bools->int (aabflist-eval x env man))
                    (endint (aabf-eval b env man))))
    :hints (("goal" :induct t
             :expand ((:with bools->int-open-once (bools->int (aabflist-eval x env man)))))
            '(:use ((:instance aabf-syntactically-equal-implies-equal-aabf-eval-1
                     (x (aabf-car x)) (x-equiv b)))
              :in-theory (disable aabf-syntactically-equal-implies-equal-aabf-eval-1)))))


                

(defsymbolic aabf-<-ss ((a s) (b s) man)
  :returns (mv (a<b b (< a b)) new-man)
  :correct-hints ('(:in-theory (enable aabf-syntactically-zero-p-implies))
                  (and stable-under-simplificationp
                       '(:in-theory (enable and* or* not)
                         :expand ((:with bools->int-open-once (bools->int (aabflist-eval a env man)))
                                  (:with bools->int-open-once (bools->int (aabflist-eval b env man)))))))
  (b* (((when (aabf-syntactically-zero-p b))
        ;; Special case for (< x 0) -- very common
        (mv (aabf-sign-s a) man))
       ((mv head1 tail1 end1) (aabf-first/rest/end a))
       ((mv head2 tail2 end2) (aabf-first/rest/end b))
       ((when (and* end1 end2))
        (aabf-nest (aabf-and head1 (aabf-not head2)) man))
       ((mv rst< rst= man) (aabf-<-=-ss tail1 tail2 man)))
    (aabf-nest (or rst< (and rst= head2 (aabf-not head1))) man)))


(defsymbolic aabf-signext-nss ((n n)
                               (a s)
                               (sign b))
  :returns (a-app-b s (logapp n a (endint sign)))
  :prepwork ((local (defthm logapp-of-neg-bit
                      (implies (bitp b)
                               (equal (logapp n (- b) (- b))
                                      (- b)))
                      :hints(("Goal" :in-theory (enable bitp))))))
  (b* (((when (or (zp n)
                  (aabf-syntactically-signext-p a sign)))
        (list sign))
       ((mv first rest &) (aabf-first/rest/end a)))
    (aabf-scons first (aabf-signext-nss (1- n) rest sign)))
  :correct-hints ((and stable-under-simplificationp
                       '(:in-theory (enable aabf-syntactically-signext-p-implies)))))

(defsymbolic aabf-logapp-nss-aux ((n n)
                                  (a s)
                                  (b s))
  :returns (a-app-b s (logapp n a b))
  (b* (((when (zp n))
        (llist-fix b))
       ((mv first rest &) (aabf-first/rest/end a)))
    (aabf-scons first (aabf-logapp-nss-aux (1- n) rest b))))

(defsymbolic aabf-logapp-nss ((n n)
                              (a s)
                              (b s))
  :returns (a-app-b s (logapp n a b))
  :prepwork ((local
              (defthm aabf-syntactically-signext-cdr-car
                (implies (aabf-syntactically-signext-p (scdr b) (aabf-car b))
                         (equal (bools->int (aabflist-eval b env man))
                                (endint (aabf-eval (aabf-car b) env man))))
                :hints (("goal" :expand ((:with bools->int-open-once (bools->int (aabflist-eval b env man))))
                         :use ((:instance aabf-syntactically-signext-p-implies
                                (x (scdr b)) (b (aabf-car b)))))))))
  (b* ((b1 (aabf-car b))
       ((when (aabf-syntactically-signext-p (scdr b) b1))
        (aabf-signext-nss n a b1)))
    (aabf-logapp-nss-aux n a b))
  :correct-hints ((and stable-under-simplificationp
                       '(:in-theory (enable aabf-syntactically-signext-p-implies)))))

;; (defsymbolic aabf-logapp-nus-aux ((n n)
;;                              (a u)
;;                              (b s))
;;   :returns (a-app-b s (logapp n a b))
;;   (b* (((when (zp n))
;;         (llist-fix b))
;;        ((mv first rest) (car/cdr a)))
;;     (aabf-scons first (aabf-logapp-nus-aux (1- n) rest b))))

;; (defsymbolic aabf-loghead-nu ((n n)
;;                              (a u))
;;   :returns (head s (loghead n a))
;;   (b* (((when (or (zp n) (atom a))) '(nil))
;;        ((mv first rest) (car/cdr a)))
;;     (aabf-scons first (aabf-loghead-nu (1- n) rest))))

;; (defsymbolic aabf-logapp-nus ((n n)
;;                              (a u)
;;                              (b s))
;;   :returns (a-app-b s (logapp n a b))
;;   :correct-hints ('(:in-theory (enable aabf-syntactically-zero-p-implies)))
;;   (b* (((when (aabf-syntactically-zero-p b))
;;         (aabf-loghead-nu n a)))
;;     (aabf-logapp-nus-aux n a b)))

(defsymbolic aabf-ash-ss ((place p)
                          (n s)
                          (shamt s)
                          man)
  :returns (mv (sh s (ash n (+ -1 place (* place shamt)))) new-man)
  :measure (len shamt)
  :prepwork ((local
              (defthm reverse-distrib-1
                (and (equal (+ n n) (* 2 n))
                     (implies (syntaxp (quotep k))
                              (equal (+ n (* k n)) (* (+ 1 k) n)))
                     (implies (syntaxp (quotep k))
                              (equal (+ (- n) (* k n)) (* (+ -1 k) n)))
                     (implies (syntaxp (quotep k))
                              (equal (+ (- n) (* k n) m) (+ (* (+ -1 k) n) m)))
                     (implies (syntaxp (and (quotep a) (quotep b)))
                              (equal (+ (* a n) (* b n)) (* (+ a b) n)))
                     (equal (+ n n m) (+ (* 2 n) m))
                     (implies (syntaxp (quotep k))
                              (equal (+ n (* k n) m) (+ (* (+ 1 k) n) m)))
                     (implies (syntaxp (and (quotep a) (quotep b)))
                              (equal (+ (* a n) (* b n) m) (+ (* (+ a b) n) m)))
                     (equal (+ n (- (* 2 n)) m)
                            (+ (- n) m))))))
  (b* (((mv shdig shrst shend) (aabf-first/rest/end shamt))
       (place (lposfix place))
       ((when shend)
        (aabf-ite-bss shdig
                      (aabf-logtail-ns 1 n)
                      (aabf-logapp-nss (1- place) nil n)
                      man))
       ((mv rst man) (aabf-ash-ss (* 2 place) n shrst man)))
    (aabf-ite-bss shdig
                  rst
                  (aabf-logtail-ns place rst)
                  man))
  :correct-hints ('(:expand ((:free (b) (logcons b (bools->int (aabflist-eval (scdr shamt) env man))))
                             (aabf-ash-ss place n shamt man)
                             (:with bools->int-open-once
                              (bools->int (aabflist-eval shamt env man))))
                    :in-theory (e/d (logcons)
                                    (acl2::logtail-identity
                                     unsigned-byte-p)))))

(local (defthm if*-identities
         (and (equal (if* nil a b) b)
              (equal (if* t a b) a)
              (equal (if* a b b) b))
         :hints(("Goal" :in-theory (enable if*)))))

(defsymbolic aabf-logbitp-n2v ((place p)
                               (digit u)
                               (n s)
                               man)
  :returns (mv (bit b (logbitp (* place digit) n)) new-man)
  :measure (len digit)
  (b* (((mv first & end) (aabf-first/rest/end n))
       (place (lposfix place))
       ((when (or (atom digit) end))
        (mv first man))
       (digit-bit1 (car digit))
       (digit-rest (cdr digit))
       (nextplace (* 2 place)))
    (aabf-nest
     (aabf-ite digit-bit1
               (aabf-logbitp-n2v nextplace digit-rest (aabf-logtail-ns place n))
               (aabf-logbitp-n2v nextplace digit-rest n))
     man))
  :correct-hints ((and stable-under-simplificationp
                       '(:in-theory (enable logcons acl2::bool->bit)))))

(defsymbolic aabf-logand-ss ((a s)
                             (b s)
                             man)
  :returns (mv (a&b s (logand a b)) new-man)
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (aabf-first/rest/end a))
       ((mv bf br bend) (aabf-first/rest/end b))
       ((when (and aend bend))
        (aabf-nest (list (aabf-and af bf)) man)))
    (aabf-nest
     (aabf-scons (aabf-and af bf)
                 (aabf-logand-ss ar br))
     man))
  :correct-hints
  ((and stable-under-simplificationp
        '(:expand ((:with bools->int-open-once (bools->int (aabflist-eval a env man)))
                   (:with bools->int-open-once (bools->int (aabflist-eval b env man))))))))

(defsymbolic aabf-logior-ss ((a s)
                             (b s)
                             man)
  :returns (mv (a&b s (logior a b)) new-man)
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (aabf-first/rest/end a))
       ((mv bf br bend) (aabf-first/rest/end b))
       ((when (and aend bend))
        (aabf-nest (list (aabf-or af bf)) man)))
    (aabf-nest
     (aabf-scons (aabf-or af bf)
                 (aabf-logior-ss ar br))
     man))
  :correct-hints
  ((and stable-under-simplificationp
        '(:expand ((:with bools->int-open-once (bools->int (aabflist-eval a env man)))
                   (:with bools->int-open-once (bools->int (aabflist-eval b env man))))))))

;; (local (defthmd logeqv**
;;          (equal (logeqv a b)
;;                 (logcons (b-not (b-xor (logcar a) (logcar b)))
;;                          (logeqv (logcdr a) (logcdr b))))
;;          :hints(("Goal" :in-theory (disable bitops::logcdr-natp
;;                                             bitops::logand-with-negated-bitmask
;;                                             bitops::logand-with-bitmask
;;                                             bitops::logcdr-of-logior
;;                                             bitops::logcdr-of-lognot
;;                                             bitops::logand$
;;                                             bitops::logior$)))
;;          :rule-classes ((:definition :controller-alist ((acl2::Binary-logeqv t t))))))

;; (local (in-theory (disable logeqv)))

(local (defthm logeqv-of-logcons
         (equal (logeqv (logcons a1 a2) (logcons b1 b2))
                (logcons (b-not (b-xor a1 b1))
                         (logeqv a2 b2)))
         :hints(("Goal" :in-theory (e/d (b-xor b-not)
                                        (bitops::logcdr-natp
                                         bitops::logand-with-negated-bitmask
                                         bitops::logand-with-bitmask
                                         bitops::logcdr-of-logior
                                         bitops::logcdr-of-lognot
                                         bitops::logand$
                                         bitops::logior$))))))

(local (defthm logeqv-of-neg-bit
         (implies (and (bitp a) (bitp b))
                  (equal (logeqv (- a) (- b))
                         (- (b-not (b-xor a b)))))
         :hints(("Goal" :in-theory (e/d (b-xor b-not)
                                        (bitops::logcdr-natp
                                         bitops::logand-with-negated-bitmask
                                         bitops::logand-with-bitmask
                                         bitops::logcdr-of-logior
                                         bitops::logcdr-of-lognot
                                         bitops::logand$
                                         bitops::logior$))))))

(local (in-theory (disable logeqv)))

(defsymbolic aabf-logeqv-ss ((a s)
                             (b s)
                             man)
  :returns (mv (a=b s (logeqv a b)) new-man)
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (aabf-first/rest/end a))
       ((mv bf br bend) (aabf-first/rest/end b))
       ((mv c man) (aabf-iff af bf man))
       ((when (and aend bend))
        (mv (list c) man)))
    (aabf-nest (aabf-scons c (aabf-logeqv-ss ar br)) man))
  :correct-hints
  ('(:expand ((:with bools->int-open-once (bools->int (aabflist-eval a env man)))
              (:with bools->int-open-once (bools->int (aabflist-eval b env man)))
              (aabf-logeqv-ss a b man)))))



(defsymbolic aabf-floor-ss-aux ((a s)
                                (b s)
                                (not-b s)
                                man)
  :returns (mv (f s (floor a b))
               (m s (mod a b))
               new-man)
  :correct-hyp (and (< 0 (bools->int (aabflist-eval b env man)))
                    (equal (bools->int (aabflist-eval not-b env man))
                           (lognot (bools->int (aabflist-eval b env man)))))
  ;; :guard (equal not-b (aabf-lognot-s b man))
  :prepwork ((local (include-book "ihs/quotient-remainder-lemmas" :dir :system)) ;

             (local
              (encapsulate nil
                (local
                 (progn
                   (defthm floor-between-b-and-2b
                     (implies (and (integerp a)
                                   (integerp b)
                                   (< 0 b)
                                   (<= b a)
                                   (< a (* 2 b)))
                              (equal (floor a b) 1))
                     :hints(("Goal" :in-theory (disable floor acl2::floor-bounded-by-/
                                                        acl2::<-*-/-left)
                             :use ((:instance acl2::floor-bounded-by-/
                                    (x a) (y b))
                                   (:theorem (implies (and (integerp a)
                                                           (integerp b)
                                                           (< 0 b)
                                                           (< a (* 2 b)))
                                                      (< (* a (/ b)) 2)))))
                            (and stable-under-simplificationp
                                 '(:in-theory (disable floor)))))

                   (defthm floor-less-than-b
                     (implies (and (integerp a)
                                   (integerp b)
                                   (< 0 b)
                                   (<= 0 a)
                                   (< a b))
                              (equal (floor a b) 0))
                     :hints(("Goal" :in-theory (disable floor acl2::floor-bounded-by-/
                                                        acl2::<-*-/-left)
                             :use ((:instance acl2::floor-bounded-by-/
                                    (x a) (y b))
                                   (:theorem (implies (and (integerp a)
                                                           (integerp b)
                                                           (< 0 b)
                                                           (< a b))
                                                      (< (* a (/ b)) 1)))))
                            (and stable-under-simplificationp
                                 '(:in-theory (disable floor)))))

                   (defthm mod-between-b-and-2-b
                     (implies (and (integerp a)
                                   (integerp b)
                                   (< 0 b)
                                   (<= b a)
                                   (< a (* 2 b)))
                              (equal (mod a b) (- a b)))
                     :hints(("Goal" :in-theory (e/d (mod)
                                                    (floor acl2::floor-bounded-by-/
                                                           acl2::<-*-/-left))
                             :use ((:instance acl2::floor-bounded-by-/
                                    (x a) (y b))
                                   (:theorem (implies (and (integerp a)
                                                           (integerp b)
                                                           (< 0 b)
                                                           (< a (* 2 b)))
                                                      (< (* a (/ b)) 2)))))
                            (and stable-under-simplificationp
                                 '(:in-theory (disable floor)))))

                   (defthm mod-less-than-b
                     (implies (and (integerp a)
                                   (integerp b)
                                   (< 0 b)
                                   (<= 0 a)
                                   (< a b))
                              (equal (mod a b) a))
                     :hints(("Goal" :in-theory (disable floor acl2::floor-bounded-by-/
                                                        acl2::<-*-/-left)
                             :use ((:instance acl2::floor-bounded-by-/
                                    (x a) (y b))
                                   (:theorem (implies (and (integerp a)
                                                           (integerp b)
                                                           (< 0 b)
                                                           (< a (* 2 b)))
                                                      (< (* a (/ b)) 2)))))
                            (and stable-under-simplificationp
                                 '(:in-theory (disable floor)))))))


                (defthm floor-rewrite-+-bit-*-2-a
                  (implies (and (integerp a) (integerp b)
                                (< 0 b))
                           (equal (floor (logcons c a) b)
                                  (if (<= b (logcons c (mod a b)))
                                      (logcons 1 (floor a b))
                                    (logcons 0 (floor a b)))))
                  :hints(("Goal" :in-theory (e/d* (logcons bfix)
                                                  (floor
                                                   (:rules-of-class
                                                    :generalize :here))
                                                  ((:generalize acl2::mod-bounded-by-modulus))))))


                (defthm mod-rewrite-+-bit-*-2-a
                  (implies (and (integerp a) (integerp b)
                                (< 0 b))
                           (equal (mod (logcons c a) b)
                                  (if (<= b (logcons c (mod a b)))
                                      (+ (- b)
                                         (logcons c (mod a b)))
                                    (logcons c (mod a b)))))
                  :hints (("goal" :in-theory (e/d* (logcons bfix mod)
                                                  (floor
                                                   (:rules-of-class
                                                    :generalize :here))
                                                  ((:generalize acl2::mod-bounded-by-modulus))))))


                (defthm denominator-of-unary-/
                  (implies (and (integerp n) (< 0 n))
                           (equal (denominator (/ n)) n))
                  :hints (("goal" :use ((:instance rational-implies2
                                         (x (/ n)))))))

                (defthm <-1-not-integer-recip
                  (implies (and (integerp n)
                                (< 1 n))
                           (not (integerp (/ n))))
                  :hints (("goal"
                           :use ((:instance denominator-of-unary-/))
                           :in-theory (disable denominator-of-unary-/))))

                (defthm integer-and-integer-recip
                  (implies (and (integerp n)
                                (< 0 n))
                           (equal (integerp (/ n))
                                  (equal n 1))))

                (defthm loghead-of-aabf-integer-length-bound
                  (implies (and (bind-free '((env . env)))
                                (<= 0 (ifix a))
                                (<= (ifix a) (bools->int (aabflist-eval b env man))))
                           (equal (loghead (aabf-integer-length-bound-s b man) a)
                                  (ifix a)))
                  :hints (("goal" :use ((:instance loghead-of-integer-length-nonneg
                                         (n (aabf-integer-length-bound-s b man))
                                         (x a))
                                        (:instance integer-length-lte-by-compare-nonneg
                                         (a a) (b (bools->int (aabflist-eval b env man)))))
                           :in-theory (disable loghead-of-integer-length-nonneg))))

                (defthm logcons-onto-mod-b-bound
                  (implies (and (integerp b)
                                (integerp a)
                                (< 0 b))
                           (< (logcons bit (mod a b)) (* 2 b)))
                  :hints(("Goal" :in-theory (enable logcons)))
                  :rule-classes :linear)))

             (local (defthm +-1-logcons-0
                      (equal (+ 1 (logcons 0 a))
                             (logcons 1 a))
                      :hints(("Goal" :in-theory (enable logcons)))))

             (local (defthm boolean-listp-of-scdr
                      (implies (boolean-listp x)
                               (boolean-listp (scdr x)))
                      :hints(("Goal" :in-theory (enable scdr)))))

             (local (defthm floor-of-negative-bit
                      (implies (and (bitp m)
                                    (posp b))
                               (equal (floor (- m) b) (- m)))
                      :hints(("Goal" :in-theory (enable bitp)))))

             ;; (local (defthm aabflist-eval-of-quoted-boolean-list
             ;;          (implies (and (syntaxp (quotep x))
             ;;                        (boolean-listp x))
             ;;                   (equal (aabflist-eval x env)
             ;;                          (v2i x)))
             ;;          :hints(("Goal" :in-theory (enable bools->int (aabflist-eval v2i)
             ;;                  :expand ((boolean-listp x))
             ;;                  :induct (bools->int (aabflist-eval x env)))))

             (local (in-theory (e/d* ()
                                     (floor
                                      mod
                                      acl2::loghead**
                                      acl2::loghead-identity
                                      bools->int aabflist-eval
                                      ; equal-of-booleans-rewrite
                                      acl2::mod-type
                                      acl2::floor-type-3 acl2::floor-type-1
                                      bitops::logcons-posp-1
                                      bitops::logcons-posp-2
                                      bitops::logcons-negp
                                      acl2::rationalp-mod
                                      (:t floor)
                                      (:t mod)
                                      FLOOR-=-X/Y
                                      acl2::floor-minus)))))
  (b* (((mv first rest endp) (aabf-first/rest/end a))
       ;; (not-b (mbe :logic (aabf-lognot-s b man) :exec not-b))
       )
    (if endp
        (b* ((floor (list first)) ;; (floor  0  b) = 0
             ((mv mod man)
              (aabf-nest (aabf-ite-bss
                          first
                          (aabf-+-ss (aabf-false) (list (aabf-true)) b) ;; (mod -1 b) = b-1 with b > 0
                          nil)
                         man)))
          (mv floor mod man))
      (b* ((bound (aabf-integer-length-bound-s b man))
           ((mv rf rm man)
            (aabf-floor-ss-aux rest b not-b man))
           (rm (aabf-scons first rm))
           ((mv less man) (aabf-<-ss rm b man))
           (floor (aabf-scons (aabf-not less man) rf))
           ((mv mod man)
            (aabf-nest (aabf-ite-bss
                        less rm
                        (aabf-loghead-ns bound
                                         (aabf-+-ss (aabf-true) not-b rm)))
                       man)))
        (mv floor mod man))))
  :correct-hints ('(:expand ((:free (not-b) (aabf-floor-ss-aux a b not-b man))
                             (:free (not-b) (aabf-floor-ss-aux nil b not-b man))
                             (:with bools->int-open-once
                              (bools->int (aabflist-eval a env man)))
                             ;; (:free (a b) (bools->int (aabflist-eval (aabf-scons a b) env))
                             ;; (bools->int (aabflist-eval a env)))
                             ))
                  (and stable-under-simplificationp
                       '(:in-theory (enable lognot)
                         :do-not-induct t))
                  ;; (and stable-under-simplificationp
                  ;;      '(:error t))
                    ))

(defsymbolic aabf-mod-ss-aux ((a s)
                             (b s)
                             (not-b s)
                             man)
  :returns (mv (m s (mod a b)) new-man)
  :correct-hyp (and (< 0 (bools->int (aabflist-eval b env man)))
                    (equal (bools->int (aabflist-eval not-b env man))
                           (lognot (bools->int (aabflist-eval b env man)))))
  ;; :guard (equal not-b (aabf-lognot-s b man))
  :guard-hints ('(:expand ((:free (not-b) (aabf-floor-ss-aux a b not-b man))
                           (:free (a not-b) (aabf-mod-ss-aux a b not-b man)))))
  (mbe :logic (b* (((mv & mod man) (aabf-floor-ss-aux a b not-b man)))
                (mv mod man))
       :exec (b* (((mv first rest endp) (aabf-first/rest/end a))
                  ((when endp)
                   (aabf-nest
                    (aabf-ite-bss
                     first
                     (aabf-+-ss (aabf-false) (list (aabf-true)) b) ;; (mod -1 b) = b-1 with b > 0
                     nil)
                    man))               ;; (mod  0  b) = 0
                  (bound (aabf-integer-length-bound-s b man))
                  ((mv rm man) (aabf-nest (aabf-scons first (aabf-mod-ss-aux rest b not-b)) man)))
               
               (aabf-nest (aabf-ite-bss
                           (aabf-<-ss rm b) rm
                           (aabf-loghead-ns bound
                                            (aabf-+-ss (aabf-true) not-b rm)))
                          man))))

(defsymbolic aabf-sign-abs-not-s ((x s) man)
  :returns (mv (s b (< x 0))
               (a s (abs x))
               (n s (lognot (abs x)))
               new-man)
  (b* (((mv abs man) (aabf-abs-s x man)))
    (mv (aabf-sign-s x)
        abs
        (aabf-lognot-s abs man)
        man)))

(defsymbolic aabf-floor-ss ((a s)
                            (b s)
                            man)
  :returns (mv (f s (floor a b)) new-man)
  :prepwork ((local (in-theory (enable aabf-sign-abs-not-s))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aabf-extension-preserves-aabf-lognot-s))))
  (b* (((mv bsign babs bneg man) (aabf-sign-abs-not-s b man))
       ((mv anorm man) (aabf-nest (aabf-ite-bss bsign (aabf-unary-minus-s a) a) man))
       ((mv f & man) (aabf-floor-ss-aux anorm babs bneg man)))
    (aabf-nest (aabf-ite-bss (aabf-=-ss b nil)
                             nil
                             f)
               man)))

(defsymbolic aabf-mod-ss ((a s)
                          (b s)
                          man)
  :returns (mv (m s (mod a b)) new-man)
  :prepwork ((local (in-theory (enable aabf-sign-abs-not-s))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aabf-extension-preserves-aabf-lognot-s))))
  (b* ((bound (aabf-integer-length-bound-s b man))
       ((mv zero man) (aabf-=-ss b nil man))
       ((when (aabf-syntactically-true-p zero man))
        (mv (llist-fix a) man))
       ((mv bsign babs bneg man) (aabf-sign-abs-not-s b man))
       ((mv anorm man) (aabf-nest (aabf-ite-bss bsign (aabf-unary-minus-s a) a) man))
       ((mv m man) (aabf-mod-ss-aux anorm babs bneg man)))
    (aabf-nest
     (aabf-ite-bss zero a
                   (aabf-logext-ns bound
                                   (aabf-ite-bss bsign (aabf-unary-minus-s m) m)))
     man))
  :correct-hints ((and stable-under-simplificationp
                       '(:in-theory (enable aabf-syntactically-true-p-rewrite)))))

(defsymbolic aabf-truncate-ss ((a s)
                               (b s)
                               man)
  :returns (mv (tr s (truncate a b)) new-man)
  :prepwork ((local (in-theory (enable aabf-sign-abs-not-s))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aabf-extension-preserves-aabf-lognot-s))))
  (b* (((mv zero man) (aabf-=-ss b nil man))
       ((when (aabf-syntactically-true-p zero man))
        (mv nil man))
       ((mv bsign babs bneg man) (aabf-sign-abs-not-s b man))
       ((mv asign aabs & man) (aabf-sign-abs-not-s a man))
       ((mv f & man) (aabf-floor-ss-aux aabs babs bneg man)))
    (aabf-nest
     (aabf-ite-bss zero nil
                   (aabf-ite-bss (aabf-xor bsign asign)
                                 (aabf-unary-minus-s f) f))
     man))
  :correct-hints ((and stable-under-simplificationp
                       '(:in-theory (enable aabf-syntactically-true-p-rewrite)))))

(defsymbolic aabf-rem-ss ((a s)
                          (b s)
                          man)
  :returns (mv (r s (rem a b)) new-man)
  :prepwork ((local (in-theory (disable integer-length-of-between-abs-and-minus-abs
                                        logext-of-integer-length-bound
                                        rem
                                        acl2::integer-length**)))
             (local (in-theory (enable aabf-sign-abs-not-s))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aabf-extension-preserves-aabf-lognot-s))))
  (b* ((bound (aabf-integer-length-bound-s b man))
       ((mv zero man) (aabf-=-ss b nil man))
       ((when (aabf-syntactically-true-p zero man))
        (mv (llist-fix a) man))
       ((mv & babs bneg man) (aabf-sign-abs-not-s b man))
       ((mv asign aabs & man) (aabf-sign-abs-not-s a man))
       ((mv m man) (aabf-mod-ss-aux aabs babs bneg man)))
    (aabf-nest
     (aabf-ite-bss zero a
                   (aabf-logext-ns bound
                                   (aabf-ite-bss asign (aabf-unary-minus-s m) m)))
     man))
  :correct-hints ((and stable-under-simplificationp
                       '(:in-theory (enable aabf-syntactically-true-p-rewrite)))
                  (and stable-under-simplificationp
                       '(:use ((:instance integer-length-of-rem
                                (a (bools->int (aabflist-eval a env man)))
                                (b (bools->int (aabflist-eval b env man)))))
                         :in-theory (e/d (logext-of-integer-length-bound)
                                         (integer-length-of-rem
                                          integer-length-of-mod))))))


;; (define s-take ((n natp) (x true-listp))
;;   (b* (((when (zp n)) (aabf-sterm nil))
;;        ((mv first rest end) (aabf-first/rest/end x))
;;        ((when (and end (eq first nil)))
;;         '(nil)))
;;     (aabf-ucons first (s-take (1- n) rest)))
;;   ///
;;   (defthm deps-of-s-take
;;     (implies (not (paabf-list-depends-on k p x))
;;              (not (paabf-list-depends-on k p (s-take n x)))))


;;   (defthm s-take-correct
;;     (equal (bools->uint (aabflist-eval (s-take n x) env)
;;            (loghead n (bools->int (aabflist-eval x env)))
;;     :hints (("goal" :induct (s-take n x)
;;              :in-theory (enable* acl2::ihsext-recursive-redefs)))))


(defsymbolic aabf-logapp-russ ((n ru)
                               (x s)
                               (y s)
                               man)
  :returns (mv (app s (logapp n x y)) new-man)
  :prepwork ((local (in-theory (enable logcons acl2::rev)))
             
             (local (in-theory (disable acl2::ash**
                                        acl2::logtail-identity
                                        acl2::loghead-identity
                                        acl2::right-shift-to-logtail
                                        bitops::logcdr-of-logtail
                                        acl2::logbitp**
                                        acl2::logtail**
                                        acl2::logapp**)))

             (local (defthm logapp-loghead-logtail
                      (implies (equal z (logapp w1 (logtail w x) y))
                               (equal (logapp w (loghead w x) z)
                                      (logapp (+ (nfix w) (nfix w1)) x y)))
                      :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                                         bitops::ihsext-inductions)))))
             (local (defthm logapp-logapp-logtail
                      (equal (logapp n a (logapp m (logtail n a) b))
                             (logapp (+ (nfix n) (nfix m)) a b))
                      :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                                         bitops::ihsext-inductions)))))

             (local (defthm loghead-of-len-of-aabf-list
                      (implies (<= (len lst) (nfix n))
                               (equal (loghead n (bools->uint (aabflist-eval lst env man)))
                                      (bools->uint (aabflist-eval lst env man))))
                      :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                                         bitops::ihsext-inductions
                                                         (:i nthcdr))
                              :induct (nthcdr n lst)
                              :expand ((bools->uint (aabflist-eval lst env man))
                                       (:free (x) (loghead n x)))))))
             (local (defthm logapp-1-is-plus-ash
                      (equal (logapp n x 1)
                             (+ (ash 1 (nfix n)) (loghead n x)))
                      :hints(("Goal" :in-theory (enable logapp bitops::ash-is-expt-*-x)))))
             (local (defthm bools->uint-aabflist-eval-of-append
                      (Equal (bools->uint (aabflist-eval (append a b) env man))
                             (logapp (len a)
                                     (bools->uint (aabflist-eval a env man))
                                     (bools->uint (aabflist-eval b env man))))
                      :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                                         bitops::ihsext-inductions
                                                         append)))))
             (local (in-theory (disable aabflist-eval-when-consp)))

             (local (defthm aabflist-p-of-append
                      (implies (and (aabflist-p x man)
                                    (aabflist-p y man))
                               (aabflist-p (append x y) man))))

             (local (defthm aabflist-p-of-rev
                      (implies (aabflist-p x man)
                               (aabflist-p (acl2::rev x) man))))
             (local (defthm logapp-of-neg-bit
                      (implies (bitp b)
                               (equal (logapp n (- b) (- b))
                                      (- b)))
                      :hints(("Goal" :in-theory (enable bitp))))))

  (if (atom n)
      (mv (llist-fix y) man)
    (if (b* (((mv x1 & xend) (aabf-first/rest/end x))
             ((mv y1 & yend) (aabf-first/rest/end y)))
          (and xend
               yend
               (aabf-syntactically-equal x1 y1)))
        (mv (llist-fix x) man)
      (b* ((w (ash 1 (len (cdr n))))
           (first-n (car n))
           (rest-n (cdr n))
           ((when (aabf-syntactically-true-p first-n man))
            (aabf-nest
             (aabf-logapp-nss w (aabf-loghead-ns w x)
                              (aabf-logapp-russ rest-n (aabf-logtail-ns w x) y))
             man))
           ((when (aabf-syntactically-false-p first-n man))
            (aabf-logapp-russ (cdr n) x y man)))
        (aabf-nest
         (aabf-ite-bss-fn
          first-n
          (aabf-logapp-nss w (aabf-loghead-ns w x)
                           (aabf-logapp-russ rest-n (aabf-logtail-ns w x) y))
          (aabf-logapp-russ (cdr n) x y))
         man))))
  :correct-hints ((acl2::use-termhint
                   (if (and (s-endp x)
                            (s-endp y)
                            (aabf-syntactically-equal (aabf-car x)
                                                      (aabf-car y)))
                       '(:use ((:instance aabf-syntactically-equal-implies-equal-aabf-eval-1
                                (x (aabf-car x)) (x-equiv (aabf-car y))))
                         :in-theory (disable aabf-syntactically-equal-implies-equal-aabf-eval-1))
                     '(:expand ((aabflist-eval (list (car n)) env man))
                       :in-theory (enable aabf-syntactically-true-p-rewrite
                                          aabf-syntactically-false-p-rewrite))))))
    

;; (defsymbolic aabf-logapp-uss ((w n)
;;                              (n u)
;;                              (x s)
;;                              (y s))
;;   :returns (app s (logapp (* n w) x y))
;;   :prepwork ((local (in-theory (enable logcons)))
;;              (local (defthm logapp-loghead-logtail
;;                       (implies (equal z (logapp w1 (logtail w x) y))
;;                                (equal (logapp w (loghead w x) z)
;;                                       (logapp (+ (nfix w) (nfix w1)) x y)))
;;                       :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
;;                                                          bitops::ihsext-inductions))))))
;;   (if (atom n)
;;       (llist-fix y)
;;     (if (b* (((mv x1 & xend) (aabf-first/rest/end x))
;;              ((mv y1 & yend) (aabf-first/rest/end y)))
;;           (and xend
;;                yend
;;                (equal x1 y1)))
;;         (llist-fix x)
;;       (aabf-ite-bss
;;        (car n)
;;        (aabf-logapp-nus (lnfix w) (s-take w x)
;;                        (aabf-logapp-uss
;;                         (ash (lnfix w) 1) (cdr n) (aabf-logtail-ns w x)
;;                         y))
;;        (aabf-logapp-uss (ash (lnfix w) 1) (cdr n) x y)))))



(local
 (defsection expt-lemmas
   (defthm expt-of-0
     (equal (expt base 0) 1)
     :hints(("Goal" :in-theory (enable expt))))


   (defthm expt-of-*-2
     (implies (natp exp)
              (equal (expt base (* 2 exp))
                     (* (expt base exp)
                        (expt base exp))))
     :hints(("Goal" :in-theory (enable expt))))

   (defthm expt-of-*-4
     (implies (natp exp)
              (equal (expt base (* 4 exp))
                     (* (expt base exp)
                        (expt base exp)
                        (expt base exp)
                        (expt base exp))))
     :hints(("Goal" :in-theory (enable expt))))))


;; (local
;;  (defthm expt-base-decompose
;;    (implies (and (posp exp) (integerp base))
;;             (equal (expt base exp)
;;                    (* (if (eql (logcar exp) 1) base 1)
;;                       (expt (* base base) (logcdr exp)))))
;;    :hints (("goal" :use ((:instance acl2::logcar-logcdr-elim
;;                           (i exp))
;;                          (:instance acl2::exponents-add-for-nonneg-exponents
;;                           (r base) (i (* 2 (logcdr exp))) (j (logcar exp)))
;;                          (:instance acl2::exponents-add-for-nonneg-exponents
;;                           (r base) (i (logcdr exp)) (j (logcdr exp))))
;;             :in-theory (e/d (logcons) (acl2::logcar-logcdr-elim
;;                                        bitops::logcons-destruct
;;                                        acl2::exponents-add-for-nonneg-exponents))))))

;; (define expt-impl ((base integerp)
;;                    (exp natp))
;;   :measure (nfix exp)
;;   (if (mbe :logic (or (zp exp) (zp (logcdr exp)))
;;            :exec (zp (logcdr exp)))
;;       (if (eql (logcar exp) 1) base 1)
;;     (let ((rest (expt-impl (* base base) (logcdr exp))))
;;       (if (eql (logcar exp) 1)
;;           (* base rest)
;;         rest)))
;;   ///

;;   (defthm expt-impl-correct
;;     (implies (and (integerp base) (natp exp))
;;              (equal (expt-impl base exp)
;;                     (expt base exp)))))


;; (define all-nil ((x))
;;   (if (atom x)
;;       t
;;     (and (eq (car x) nil)
;;          (all-nil (cdr x))))
;;   ///
;;   (defthm all-nil-when-atom
;;     (implies (atom x) (all-nil x)))

;;   (defthmd zero-when-all-nil
;;     (implies (all-nil x)
;;              (equal (bools->uint (aabflist-eval x env)) 0))))

;; Note: We don't have a symbolic counterpart for expt yet, but this is used in
;; SV and it could easily be used in FGL as well so we wrote it here.
(defsymbolic aabf-expt-su ((b s)
                           (e u)
                           man)
  :measure (len e)
  :returns (mv (b^e s (expt b e)) new-man)
  :prepwork ((local (defthm not-syntactically-zero-implies-consp
                      (implies (not (aabf-syntactically-zero-p x))
                               (consp x))
                      :hints(("Goal" :in-theory (enable aabf-syntactically-zero-p)))
                      :rule-classes :forward-chaining)))
  (b* (((when (aabf-syntactically-zero-p e))
        (mv (list (aabf-true) (aabf-false)) man))
       ((when (aabf-syntactically-zero-p (cdr e)))
        (aabf-ite-bss-fn (car e) b (list (aabf-true) (aabf-false)) man))
       (car (car e))
       (cdr (cdr e))
       ((mv rest man) (aabf-nest (aabf-expt-su (aabf-*-ss b b) cdr) man)))
    (aabf-nest (aabf-ite-bss car
                             (aabf-*-ss b rest)
                             rest)
               man))
  :correct-hints ('(:in-theory (enable ;;zero-when-all-nil
                                aabf-syntactically-zero-p-implies-unsigned
                                logcons))))



