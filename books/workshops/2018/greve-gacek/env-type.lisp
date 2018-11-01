;; 
;; Copyright (C) 2018, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "varid-type")
(include-book "sets")
(include-book "centaur/fty/deftypes" :dir :system)

;; ------------------------------------------------------------------

(def::type+ bound-value-p (x)
  (declare (xargs :type-name bound-value
                  :type-witness 0))
  (or (rationalp x)
      (integerp x)))

(fty::deffixtype bound-value
  :pred   bound-value-p
  :fix    bound-value-fix
  :equiv  bound-value-equiv
  :define nil
  )

(defthm bound-value-p-implies-rationalp
  (implies
   (bound-value-p x)
   (rationalp x))
  :rule-classes (:forward-chaining))

;; ------------------------------------------------------------------

(def::type+ bound-integer-type-name-p (x)
  (declare (xargs :type-name bound-integer-type-name
                  :type-witness :integerp))
  (equal x :integerp))

(def::type+ bound-rational-type-name-p (x)
  (declare (xargs :type-name bound-rational-type-name
                  :type-witness :rationalp))
  (equal x :rationalp))

;; ------------------------------------------------------------------

(def::type+ bound-type-name-p (x)
  (declare (xargs :type-name bound-type-name
                  :type-witness (bound-integer-type-name-witness)))
  (or (bound-integer-type-name-p x)
      (bound-rational-type-name-p x)))

;; ------------------------------------------------------------------

(fty::defprod binding
  ((varid varid-p)
   (type  bound-type-name-p)
   (value bound-value-p)
   ))

(def::un binding-fix! (x)
  (declare (xargs :signature ((t) binding-p)))
  (with-guard-checking :none (ec-call (binding-fix x))))

(defun binding-equiv! (x y)
  (declare (type t x y))
  (with-guard-checking :none (ec-call (binding-equiv x y))))

(def::und binding-type-witness ()
  (declare (xargs :signature (() binding-p)))
  (binding (varid-witness) :integerp 0))

(in-theory (disable (binding-type-witness)))

(encapsulate
    ()

  (local (in-theory (disable binding-equiv$inline)))

  (local
   (defthmd expand-binding-equiv
     (implies
      (syntaxp (and (symbolp x) (symbolp y)))
      (iff (binding-equiv x y)
           (binding-equiv 
            (binding (binding->varid x)
                     (binding->type x)
                     (binding->value x))
            (binding (binding->varid y)
                     (binding->type y)
                     (binding->value y)))))))
  
  (defthmd binding-equiv-extensionality
    (iff (binding-equiv x y)
         (and (varid-equiv (binding->varid x)
                           (binding->varid y))
              (bound-type-name-equiv (binding->type x)
                                     (binding->type y))
              (bound-value-equiv (binding->value x)
                                 (binding->value y))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (expand-binding-equiv) (BINDING-OF-FIELDS))))))

  )
  
;; ------------------------------------------------------------------

(def::un bound-type-p (type value)
  (declare (xargs :signature ((t t) booleanp)
                  :congruence ((bound-type-name-equiv nil) equal)))
  (let ((type (bound-type-name-fix type)))
    (and (bound-value-p value)
         (if (bound-integer-type-name-p type) (integerp value)
           (rationalp value)))))

(defthm bound-type-p-implies-bound-value-p
  (implies
   (bound-type-p type value)
   (bound-value-p value))
  :rule-classes (:Forward-chaining))

(def::un bound-type-fix (type value)
  (declare (xargs :signature ((t t) (lambda (x) (bound-type-p type x)))
                  :congruence ((bound-type-name-equiv bound-value-equiv) equal)))
  (let ((type (bound-type-name-fix type))
        (value (bound-value-fix value)))
    (if (bound-integer-type-name-p type) (ifix value)
      (rfix value))))

(defthm bound-type-p-bound-type
  (implies
   (bound-type-p type value)
   (equal (bound-type-fix type value)
          value)))

(in-theory (disable bound-type-p))

;; ------------------------------------------------------------------

(defun wf-binding-type-instance ()
  (declare (xargs :guard t))
  (binding (varid-witness) :integerp 0))

;; Here is what I was originally contemplating ..
;;
;; (with-guard-checking nil (ec-call (binding-fix nil)))

(def::type+ wf-binding-p (x)
  (declare (xargs :type-name wf-binding
                  :type-witness (wf-binding-type-instance)
                  :type-equiv wf-binding-equiv
                  :type-type-equiv wf-binding-unfix-equiv
                  :type-fix   wf-binding-fix))
  (and (binding-p x)
       (bound-type-p (binding->type x) (binding->value x))))

;; This would be nice ..
;; (defcong wf-binding-equiv equal (binding->varid x) 1)

(defun wf-binding-type-equiv (x y)
  (declare (type t x y))
  (and (wf-binding-equiv x y)
       (equal (wf-binding-p x) (wf-binding-p y))
       (binding-equiv! x y)))

(defequiv wf-binding-type-equiv)

(defcong wf-binding-type-equiv equal (wf-binding-p x) 1)
(defrefinement wf-binding-type-equiv wf-binding-unfix-equiv
  :hints (("Goal" :in-theory (enable wf-binding-unfix-equiv))))
;;(defrefinement wf-binding-type-equiv wf-binding-equiv)
(defrefinement wf-binding-type-equiv binding-equiv)

(in-theory (disable wf-binding-type-equiv))

;; Sigh ..
;; (skip-proofs
;; (defthm hackalong
;;  (WF-BINDING-P (WF-BINDING-FIX X))))

(fty::deffixtype wf-binding
  :pred   wf-binding-p
  :fix    wf-binding-fix
  :equiv  wf-binding-equiv
  :define nil
  )

;; ------------------------------------------------------------

;; (in-theory (enable DEFFIX_WF-BINDING-EQUIV_EQUAL_WF-BINDING-FIX_TO_WF-BINDING-EQUIV))

;; Yeah .. we may or may not do this .. probably not.
(fty::deflist env
  :elt-type wf-binding
  :pred  env-p
  :fix   env-fix-type
  :equiv env-fix-equiv
  :true-listp t
  )

(defrefinement env-fix-equiv consp-equiv
  :hints (("Goal" :in-theory (enable env-fix-type))))

(defun env-fix-type! (x)
  (declare (type t x))
  (with-guard-checking :none (ec-call (env-fix-type x))))

(defun env-fix-equiv! (x y)
  (declare (type t x y))
  (with-guard-checking :none (ec-call (env-fix-equiv x y))))

;; DAG: Actually, we will never use this, so ..

;; (defun env-fix-equiv (x y)
;;   (declare (type t x y))
;;   (and (iff (env-p x) (env-p y))
;;        (env-fix-equiv! x y)))

;; (defequiv env-fix-equiv)
;; (defcong env-fix-equiv equal (env-p x) 1)
;; (defrefinement env-fix-equiv env-fix-equiv)

;; (defthm env-fix-equiv-env-fix
;;   (and (iff (env-fix-equiv (env-fix x) y)
;;             (and (env-p y)
;;                  (env-fix-equiv x y)))
;;        (iff (env-fix-equiv y (env-fix x))
;;             (and (env-p y)
;;                  (env-fix-equiv x y)))))

;; (in-theory (disable env-fix-equiv))

(defthm open-env-fix-equiv-on-consp
  (implies
   (consp x)
   (iff (env-fix-equiv x y)
        (and (consp y)
             (wf-binding-equiv (car x) (car y))
             (env-fix-equiv (cdr x) (cdr y)))))
  :hints (("Goal" :in-theory (enable env-fix-type))))

(defthm open-env-fix-equiv-on-not-consp
  (implies
   (not (consp x))
   (iff (env-fix-equiv x y)
        (not (consp y))))
  :hints (("Goal" :in-theory (enable env-fix-type))))

(defthm equal-env-fix-to-env-fix-equiv
  (iff (equal (env-fix-type x) y)
       (and (env-p y)
            (env-fix-equiv x y))))

(in-theory (disable env-fix-equiv$inline))

;; (encapsulate
;;  ()

;;  (encapsulate
;;   (((env-fix-equiv-hyps) => *)
;;    ((env-fix-equiv-left) => *)
;;    ((env-fix-equiv-right) => *))

;;   (local (defun env-fix-equiv-hyps () nil))
;;   (local (defun env-fix-equiv-left () nil))
;;   (local (defun env-fix-equiv-right () nil))

;;   (defthm env-fix-equiv-multiplicity-constraint
;;     (implies
;;      (env-fix-equiv-hyps)
;;      (and (equal (len (env-fix-equiv-left)) (len (env-fix-equiv-right)))
;;           (wf-binding-equiv (nth arbitrary-location (env-fix-equiv-left))
;;                             (nth arbitrary-location (env-fix-equiv-right)))))
;;     :rule-classes nil)
;;   )

;;  (local
;;   (defun bad-boy (x y)
;;     (if (and (consp x) (consp y) (wf-binding-equiv (car x) (car y)))
;;         (1+ (bad-boy (cdr x) (cdr y)))
;;       0)))

;;  (local
;;   (defthm env-fix-equiv-reduction
;;     (iff (env-fix-equiv x y)
;;          (and (equal (len x) (len y))
;;               (wf-binding-equiv (nth (bad-boy x y) x)
;;                                 (nth (bad-boy x y) y))))
;;     :hints (("Goal" :induct (bad-boy x y)
;;              :in-theory (disable (:EXECUTABLE-COUNTERPART BINDING-FIX$INLINE))))))
 
;;  (defthm env-fix-equiv-by-multiplicity-driver
;;    (implies (env-fix-equiv-hyps)
;;             (env-fix-equiv (env-fix-equiv-left) (env-fix-equiv-right)))
;;    :rule-classes nil
;;    :hints((and stable-under-simplificationp
;;                '(:use ((:instance
;;                         env-fix-equiv-multiplicity-constraint
;;                         (arbitrary-location (bad-boy (env-fix-equiv-left) (env-fix-equiv-right)))))))))
 
;;  (ADVISER::defadvice ADVISER::env-fix-equiv-by-multiplicity
;;                      (implies (env-fix-equiv-hyps)
;;                               (env-fix-equiv (env-fix-equiv-left) (env-fix-equiv-right)))
;;                      :rule-classes (:pick-a-point :driver env-fix-equiv-by-multiplicity-driver))
 
;;  )

;; ---------------------------------------------------------

;; (def::un env-fix (list)
;;   (declare (xargs :signature ((t) env-p)))
;;   (if (not (consp list)) nil
;;     (cons (binding-fix (car list))
;;           (env-fix (cdr list)))))

;; (defthm len-env-fix
;;   (equal (len (env-fix list))
;;          (len list)))

;; (defthm env-p-env-fix
;;   (implies
;;    (env-p x)
;;    (equal (env-fix x) x)))

;; (defthm consp-env-fix
;;   (equal (consp (env-fix x))
;;          (consp x)))

;; #+joe
;; (defun env-fix-equiv (x y)
;;   (declare (type t x y))
;;   (equal (env-fix x)
;;          (env-fix y)))

;; (include-book "sets")

;; ;; I guess this tells me that we weren't prepared to treat
;; ;; varid-listp as a set.  Perhaps it should have been
;; ;; varid-setp?
;; (def::signature set-insert (varid-p varid-listp) varid-listp
;;   :hints (("Goal" :in-theory (enable set-insert))))

;; (defun location (a list)
;;   (if (not (consp list)) 1
;;     (if (equal a (car list)) 0
;;       (1+ (location a (cdr list))))))

;; (def::un-skd varid-set-equiv (x y)
;;   (forall (a) (and (equal (list::memberp a x)
;;                           (list::memberp a y))
;;                    (varid-type-equiv (nth (location (varid-fix a) x) x) 
;;                                      (nth (location (varid-fix a) y) y)))))



;; (defequiv varid-set-equiv
;;   :hints ((quant::inst?)))

;; (defrefinement varid-set-equiv set-equiv-quant
;;   :hints ((quant::inst?)))


;; ;; location is "nth-equiv"

;; (set-equiv )
;; nth-equiv 
;; (nth-equiv (location a list) list)

;; (defun nth-equiv (a b list))

;; (implies
;;  (set-equiv-quant list1 list2)
;;  (equal (nth (location item list1) list1)
;;         (nth (location item list2) list2)))




;; (defthm nth-insert
;;   (equal (nth a (set-insert b set))
;;          (if (list::memberp b set) (nth a set)
;;            (if (zp a) b (nth (1- (nfix a)) set))))
;;   :hints (("Goal" :do-not-induct t
;;            :in-theory (enable set-insert))))

;; dag

;; (defun varid-set-equiv (x y)
;;   (and (equal (set-size x) (set-size y))

;; (defrefinement 

(def::signature set-insert (varid-p varid-listp) varid-listp
  :hints (("Goal" :in-theory (enable set-insert))))

(def::un env-keys (env)
  (declare (xargs :signature ((t) varid-listp)
                  :congruence ((env-fix-equiv) set-equiv-quant)))
  (if (not (consp env)) nil
    (set-insert (binding->varid (wf-binding-fix (car env)))
                (env-keys (cdr env)))))

(defun env-key-equiv (x y)
  (set-equiv-quant (env-keys x) (env-keys y)))

(defequiv env-key-equiv)

(defcong env-key-equiv set-equiv-quant (env-keys env) 1)

(defrefinement env-fix-equiv env-key-equiv)

;; (in-theory (disable env-key-equiv))

(def::un get-binding (var env)
  (declare (xargs :signature ((t t) wf-binding-p)
                  :congruence ((varid-equiv env-fix-equiv) equal)
                  :measure (len env)))
  (if (not (consp env)) (wf-binding-witness)
    (let ((var (varid-fix var)))
      (let ((binding (wf-binding-fix (car env))))
        (if (varid-equiv var (binding->varid binding))
            binding
          (get-binding var (cdr env)))))))

(def::un-sk env-get-equiv (x y)
  (forall (var) (equal (get-binding var x)
                       (get-binding var y))))

(defequiv env-get-equiv
  :hints ((quant::inst?)))

(defcong env-get-equiv equal (get-binding var x) 2
  :hints ((quant::inst?)))

(defrefinement env-fix-equiv env-get-equiv)

(in-theory (disable env-get-equiv))

(encapsulate
 ()

 (encapsulate
  (((env-get-equiv-hyps) => *)
   ((env-get-equiv-left) => *)
   ((env-get-equiv-right) => *))

  (local (defun env-get-equiv-hyps () nil))
  (local (defun env-get-equiv-left () nil))
  (local (defun env-get-equiv-right () nil))

  (defthm env-get-equiv-multiplicity-constraint
    (implies
     (env-get-equiv-hyps)
     (equal (get-binding arbitrary-varid (env-get-equiv-left))
            (get-binding arbitrary-varid (env-get-equiv-right))))
    :rule-classes nil)
  )

 (defthm env-get-equiv-by-multiplicity-driver
   (implies (env-get-equiv-hyps)
            (env-get-equiv (env-get-equiv-left) (env-get-equiv-right)))
   :rule-classes nil
   :hints((and stable-under-simplificationp
               '(:use ((:instance
                        env-get-equiv-multiplicity-constraint
                        (arbitrary-varid hide)))))))

 (ADVISER::defadvice ADVISER::env-get-equiv-by-multiplicity
   (implies (env-get-equiv-hyps)
            (env-get-equiv (env-get-equiv-left) (env-get-equiv-right)))
   :rule-classes (:pick-a-point :driver env-get-equiv-by-multiplicity-driver))

 )

(defun env-equiv (x y)
  (and (env-get-equiv x y)
       (env-key-equiv x y)))

(defequiv env-equiv)

(defrefinement env-equiv env-get-equiv)
(defrefinement env-equiv env-key-equiv)
(defrefinement env-fix-equiv env-equiv)

;; (in-theory (disable env-equiv))

;;

;; (defequiv env-key-equiv)

;; (defcong env-key-equiv set-equiv-quant (env-keys env) 1)

;; (in-theory (disable env-key-equiv))


;; (equal (get-binding var env)
;;        (if (list::memberp (varid-fix var) (env-keys env))
           

;; (defthm memberp-env-keys-implies-varid-p
;;   (implies
;;    (list::memberp a (env-keys list))
;;    (varid-p a))
;;   :rule-classes (:forward-chaining))

;; - let's see if we can wait on this
;; (def::un env-remove (key list)
;;   (declare (xargs :signature ((t t) env-p)
;;                   :congruence ((varid-equiv nil) equal)))
;;   (if (not (consp list)) nil
;;     (let ((entry (binding-fix (car list))))
;;       (if (varid-equiv key (binding-varid entry))
;;           (env-remove key (cdr list))
;;         (cons entry (env-remove key (cdr list)))))))

;; (defthm memberp-keys-env-remove
;;   (equal (list::memberp a (env-keys (env-remove key list)))
;;          (if (varid-equiv a key) nil
;;            (list::memberp a (env-keys list)))))

;; (defthm env-keys-env-remove
;;   (set-equiv-quant (env-keys (env-remove key env))
;;                    (remove (varid-fix key) (env-keys env))))

;; (defchoose (n) (key env)
;;   (varid-equiv (varid->varid (nth n env)) key))

;; (defchoose (envx) (key env)
;;   (forall (z) (equal (nth z envx)
;;                      (if (equal z (if (pred (choose)) (choice) (len env))) var
;;                        (nth 
  

(def::un set-binding (value env)
  (declare (xargs :signature ((wf-binding-p env-p) env-p)
                  :congruence ((wf-binding-equiv nil) equal)
                  :measure (len env)))
  (let ((value (wf-binding-fix value)))
    (if (not (consp env)) (list value)
      (let ((binding (wf-binding-fix (car env))))
        (if (varid-equiv (binding->varid value) (binding->varid binding))
            (cons value (cdr env))
          (cons binding (set-binding value (cdr env))))))))

(defthm memberp-key-set-binding
  (equal (list::memberp key (env-keys (set-binding v env)))
         (or (equal key (binding->varid (wf-binding-fix v)))
             (list::memberp key (env-keys env))))
  :hints (("Goal" :induct (set-binding v env)
           :in-theory (enable VARID-EQUIV-TO-EQUAL))))

(defthm get-binding-set-binding
  (equal (get-binding a (set-binding v env))
         (let ((v (wf-binding-fix v)))
           (if (varid-equiv a (binding->varid v)) v
             (get-binding a env)))))

(defcong env-equiv env-equiv (set-binding v env) 2
  :hints (("Goal" :do-not-induct t)))

;; (defthm get-binding-env-remove
;;   (equal (get-binding a (env-remove key list))
;;          (if (varid-equiv a key) (default-coeff)
;;            (get-binding a list))))

;; ------------------------------------------------------------

;; (def::un key-count (list)
;;   (declare (xargs :signature ((true-listp) natp)
;;                   :measure (len list)))
;;   (if (not (consp list)) 0
;;     (1+ (key-count (remove-equal (car list) (cdr list))))))

;; (defthm remove-equal-remove-equal
;;   (implies
;;    (syntaxp (good-rewrite-order y x))
;;    (equal (remove-equal x (remove-equal y list))
;;           (remove-equal y (remove-equal x list)))))

;; (defthm key-count-remove-equal
;;   (equal (key-count (remove-equal x list))
;;          (if (list::memberp x list) (1- (key-count list))
;;            (key-count list)))
;;   :hints (("Goal" :expand (:free (a list) (key-count (cons a list))))))

;; (encapsulate
;;     ()

;;   (local
;;    (defthm not-consp-membership-implication
;;      (implies
;;       (not (consp x))
;;       (not (list::memberp a x)))))

;;   (local
;;    (defthm not-consp-implies-set-equiv-nil
;;      (implies
;;       (not (consp x))
;;       (set-equiv-quant x nil))
;;      :rule-classes :forward-chaining))

;;   (local
;;    (defthm consp-implies-memberp-car
;;      (implies
;;       (consp x)
;;       (list::memberp (car x) x))
;;      :rule-classes (:forward-chaining)))

;;   (local
;;    (defthm memberp-forward
;;      (implies
;;       (and
;;        (list::memberp a x)
;;        (set-equiv-quant x y))
;;       (list::memberp a y))
;;      :rule-classes (:forward-chaining)))

;;   (local
;;    (defthm equal-to-iff
;;      (implies
;;       (booleanp x)
;;       (iff (equal x y)
;;            (and (booleanp y)
;;                 (iff x y))))))

;;   (defcong set-equiv-quant equal (consp x) 1
;;     :hints (("Goal" :in-theory (enable equal-to-iff))))
  
;;   )

;; (defun key-count-induction (x y)
;;   (if (and (consp x) (consp y))
;;       (key-count-induction (remove-equal (car x) x)
;;                            (remove-equal (car x) y))
;;     (list x y)))

;; (defcong set-equiv-quant equal (key-count x) 1
;;   :hints (("Goal" :induct (key-count-induction x x-equiv))))

;; ------------------------------------------------------------

(defrefinement env-fix-equiv env-equiv)

(defcong env-equiv env-equiv (env-fix-type x) 1
  :hints ((quant::inst?)))

(defcong env-equiv equal (get-binding a x) 2
  :hints ((quant::inst?)))

(defcong env-equiv set-equiv-quant (env-keys x) 1
  :hints ((quant::inst?)))

;; (defcong env-equiv env-equiv (env-remove key list) 2)

(defthm env-equiv-fix-env-type
  (env-equiv (env-fix-type x) x))

#+joe
(def::fix env-fix env-equiv
  :type env-p
  :type-fix env-fix-type
  )

#+joe
(encapsulate
    ()

  (local
   (defthm env-equiv-set-binding
     (implies
      (syntaxp (symbolp env))
      (env-equiv (set-binding value env)
                 (set-binding value (env-fix env))))
     :hints (("Goal" :in-theory (enable VARID-EQUIV-TO-EQUAL)
              :induct (set-binding value env)))))

  (defcong env-equiv env-equiv (set-binding value env) 2
    :hints (("Goal" :in-theory (e/d (DEFFIX_ENV-EQUIV_ENV-EQUIV_ENV-FIX_REDUCTION) ()))))

  )

;; (in-theory (disable zp-open zp))

;; (encapsulate
;;     ()

;;   (local
;;    (defthmd key-count-cong
;;      (implies
;;       (env-equiv x y)
;;       (equal (key-count (env-keys x))
;;              (key-count (env-keys y))))))
;;   (local
;;    (defthm equal-to-iff
;;      (implies
;;       (booleanp x)
;;       (iff (equal x y)
;;            (and (booleanp y)
;;                 (iff x y))))))

;;   (local
;;    (defthm equal-0-key-count
;;      (iff (equal 0 (key-count x))
;;           (not (consp x)))))

;;   (local
;;    (defthm consp-env-keys
;;      (iff (consp (env-keys x))
;;           (consp x))
;;      :hints (("Goal" :in-theory (enable key-insert)))))

;;   (defcong env-equiv equal (consp x) 1
;;     :hints (("Goal" :in-theory (disable ENV-EQUIV-IMPLIES-SET-EQUIV-QUANT-ENV-KEYS-1)
;;              :use (:instance key-count-cong (y x-equiv)))))

;;   )

;; --------------------------------------------------------

;; (def::und len-bindings (env)
;;   (declare (xargs :signature ((t) natp)
;;                   :congruence ((env-equiv) equal)))
;;   (set-size (env-keys env)))

;; (def::und first-binding (env)
;;   (declare (xargs :signature ((t) binding-p)
;;                   :congruence ((env-equiv) equal)))
;;   (let ((env (env-fix env)))
;;     (if (not (consp env)) (binding-fix nil)
;;       (binding-fix (car env)))))

;; (def::und next-bindings (env)
;;   (declare (xargs :signature ((t) env-fixed-p)
;;                   :congruence ((env-equiv) env-equiv)))
;;   (env-fix (env-remove (binding-varid (first-binding env)) env)))

;; (defthm env-keys-first-binding
;;   (set-equiv-quant (env-keys (next-bindings env))
;;                    (remove-equal (binding-varid (first-binding env)) (env-keys env)))
;;   :hints (("Goal" :do-not-induct t
;;            :in-theory (enable next-bindings))))

;; (encapsulate
;;     ()

;;   (local
;;    (defthm zp-key-count
;;      (equal (zp (key-count x))
;;             (not (consp x)))))
  
;;   (local
;;    (defthm zp-len-bindings-to-consp
;;      (equal (zp (len-bindings env))
;;             (not (consp env)))
;;      :hints (("Goal" :in-theory (enable key-insert len-bindings)))))

;;   (defthm zp-len-bindings
;;     (implies
;;      (zp (len-bindings env))
;;      (set-equiv-quant (env-keys env) nil)))
  
;;   (local
;;    (defthmd consp-implies-memberp-car-helper
;;      (implies
;;       (consp env)
;;       (list::memberp (binding-varid (car env)) (env-keys env)))))

;;   (local
;;    (defthm consp-implies-memberp-car
;;      (implies
;;       (consp env)
;;       (list::memberp (binding-varid (car (env-fix env))) (env-keys env)))
;;      :rule-classes ((:forward-chaining :trigger-terms ((env-fix env))))
;;      :hints (("Goal" :use (:instance consp-implies-memberp-car-helper (env (env-fix env)))))))

;;   (defthm memberp-first-binding
;;     (implies
;;      (not (zp (len-bindings env)))
;;      (list::memberp (binding-varid (first-binding env))
;;                     (env-keys env)))
;;     :hints (("Goal" :in-theory (enable first-binding))))

;;   (defthm len-bindings-decreasing
;;     (implies
;;      (not (zp (len-bindings env)))
;;      (equal (len-bindings (next-bindings env))
;;             (1- (len-bindings env))))
;;     :hints (("Goal" :do-not-induct t
;;              :in-theory (enable len-bindings next-bindings first-binding))))

;;   (local
;;    (defthmd get-binding-first-helper
;;      (implies
;;       (not (zp (len-bindings env)))
;;       (equal (GET-BINDING (BINDING-VARID (FIRST-BINDING ENV)) (env-fix ENV))
;;              (BINDING-VALUE (FIRST-BINDING ENV))))
;;      :hints (("goal" :do-not-induct t
;;               :expand (:Free (a) (GET-BINDING a (env-fix ENV)))
;;               :in-theory (e/d (first-binding)
;;                               (ENV-EQUIV-IMPLIES-EQUAL-GET-BINDING-2))))))
;;   (defthm get-binding-first
;;     (implies
;;      (not (zp (len-bindings env)))
;;      (equal (get-binding (binding-varid (first-binding env)) env)
;;             (binding-value (first-binding env))))
;;     :hints (("goal" :do-not-induct t
;;              :use (:instance get-binding-first-helper (env (env-fix env))))))
  
;;   (defun get-induction (env)
;;     (declare (xargs :measure (len-bindings env)))
;;     (if (zp (len-bindings env)) env
;;       (get-induction (next-bindings env))))
  
;;   (defun alt-get-binding (a env)
;;     (declare (xargs :measure (len-bindings env)))
;;     (if (zp (len-bindings env)) 0
;;       (if (varid-equiv a (binding-varid (first-binding env))) 
;;           (binding-value (first-binding env))
;;         (alt-get-binding a (next-bindings env)))))
  
;;   ;; If a is not equal, then you can ignore the remove.
;;   ;; .. this has been very inelegant :(

;;   (defthm get-binding-definition
;;     (equal (get-binding a (env-fix env))
;;            (alt-get-binding a env))
;;     :hints (("Goal" :in-theory (e/d (first-binding) (ENV-EQUIV-IMPLIES-EQUAL-GET-BINDING-2))
;;              :expand (get-binding a (env-fix env))
;;              :induct (get-induction env))))
  
;;   )

;; (equal (get-binding a (env-fix env))
;;        (get-binding a env))

;; ;; This is your real target ..
;; (implies
;;  (not (varid-equiv a (binding-varid (first-binding env))))
;;  (equal (get-binding a (next-binding env))
;;         (get-binding a (cdr env))))

;; (defthm env-keys-set-binding
;;   (set-equiv-quant (env-keys (set-binding a value env))
;;                    (cons (varid-fix a) (env-keys env))))

;; (defcong env-equiv env-equiv (set-binding b v env) 3)

;; --------------------------------------------------------

;; (defun rest-bindings (env)
;;   (env-fix (cdr (env-fix env))))

;; (defun len-bindings (env)
;;   (len (env-keys env)))

;; (defun key-len (env)

;; (defthm
;;   (implies
;;    (

;; (defthm
;;   (implies
;;    (and
;;     (env-p x)
;;    (iff (equal x y)
;;         (env-equiv x y))

;; DAG -- do we even need these?

#+joe
(defthm env-equiv-implies-set-equiv-env-keys
  (implies
   (env-equiv x y)
   (set-equiv-quant (env-keys x) (env-keys y)))
  :rule-classes (:forward-chaining))

#+joe
(defthm env-equiv-implies-set-equiv-env-keys-rewrite
  (implies
   (and
    (env-equiv x y)
    (syntaxp (good-rewrite-order x y)))
   (set-equiv-quant (env-keys x)
                    (env-keys y))))

