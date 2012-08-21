
(in-package "GL")

(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic-fns")
(include-book "eval-g-base")
;(include-book "tools/with-arith5-help" :dir :system)
(local (include-book "symbolic-arithmetic"))
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix-logic"))
;(local (allow-arith5-help))

(in-theory (disable (mk-g-concrete)))

(defthm mk-g-concrete-of-atomic-constant
  (implies (and (syntaxp (quotep x))
                (atom x)
                (not (g-keyword-symbolp x)))
           (equal (mk-g-concrete x) x))
  :hints(("Goal" :in-theory (enable mk-g-concrete
                                    concrete-gobjectp
                                    gobject-hierarchy))))

(program)
(defun def-g-unary-concrete-fn (fn number-case boolean-case cons-case
                                   hints world)
  (let ((x (car (wgetprop fn 'formals))))
    `(progn
       (def-g-fn ,fn
         (let ((x ',x)
               (fn ',fn))
           `(if (atom ,x)
                (mk-g-concrete (ec-call (,fn ,x)))
              (pattern-match ,x
                ((g-concrete obj)
                 (mk-g-concrete (ec-call (,fn obj))))
                ((g-ite test then else)
                 (if (zp clk)
                     (g-apply ',fn (list ,x))
                   (g-if test
                         (,gfn then hyp clk)
                         (,gfn else hyp clk))))
                ((g-apply & &) (g-apply ',fn (list ,x)))
                ((g-var &) (g-apply ',fn (list ,x)))
                ((g-number &) ,',number-case)
                ((g-boolean &) ,',boolean-case)
                (& ,',cons-case)))))
       (def-gobjectp-thm ,fn
         :hints `(("goal" :in-theory
                   (e/d ()
                        ((force)
                         (:definition ,gfn)))
                   :induct (,gfn ,',x hyp clk)
                   :expand ((,gfn ,',x hyp clk)))))
       (verify-g-guards
        ,fn
        :hints `(("Goal" :in-theory (Disable ,gfn))))

       (def-g-correct-thm ,fn eval-g-base
         :hints `(("Goal" :in-theory (e/d ((:induction ,gfn)
                                           general-concrete-obj)
                                          ((:definition ,gfn)))
                   :induct (,gfn ,',x hyp clk)
                   :expand ((,gfn ,',x hyp clk)
                            (:with eval-g-base (eval-g-base ,',x env))))
                  . ,',hints)))))

(defmacro def-g-unary-concrete (fn &key number-case boolean-case
                                   cons-case hints)
  `(make-event (def-g-unary-concrete-fn ',fn ',number-case ',boolean-case
                 ',cons-case ',hints(w state))))

(logic)

(def-g-unary-concrete symbol-name
  :number-case ""
  :boolean-case (g-if x "T" "NIL")
  :cons-case "")

(def-g-unary-concrete symbol-package-name
  :number-case ""
  :boolean-case "COMMON-LISP"
  :cons-case ""
  :hints ((and stable-under-simplificationp
               '(:use
                 ((:instance (:type-prescription bfr-eval)
                             (x (g-boolean->bool x))
                             (env (car env))))
                 :in-theory (disable (:type-prescription bfr-eval))))))



(def-g-unary-concrete char-code
  :number-case 0
  :boolean-case 0
  :cons-case 0)

(local
 (defthm pkg-witness-of-non-stringp
   (implies (not (stringp x))
            (equal (pkg-witness x)
                   (pkg-witness "ACL2")))
   :hints (("goal" :use ((:instance
                          symbol-equality
                          (acl2::s1 'acl2::acl2-pkg-witness)
                          (acl2::s2 (pkg-witness x))))))))

(def-g-unary-concrete pkg-witness
  :number-case (mk-g-concrete (pkg-witness "ACL2"))
  :boolean-case (mk-g-concrete (pkg-witness "ACL2"))
  :cons-case (mk-g-concrete (pkg-witness "ACL2")))


(local
 (defthm not-integerp-break-g-number
   (implies (wf-g-numberp x)
            (and (not (integerp (mv-nth 0 (break-g-number x))))
                 (not (integerp (mv-nth 1 (break-g-number x))))
                 (not (integerp (mv-nth 2 (break-g-number x))))
                 (not (integerp (mv-nth 3 (break-g-number x))))))
   :hints(("Goal" :in-theory (enable wf-g-numberp-simpler-def
                                     break-g-number bfr-listp)))))

(def-g-unary-concrete realpart
  :number-case
  (mv-let (rn rd in id)
    (break-g-number (g-number->num x))
    (declare (ignore in id))
    (mk-g-number rn rd))
  :boolean-case 0
  :cons-case 0)

(def-g-unary-concrete imagpart
  :number-case
  (mv-let (rn rd in id)
    (break-g-number (g-number->num x))
    (declare (ignore rn rd))
    (mk-g-number in id))
  :boolean-case 0
  :cons-case 0)


