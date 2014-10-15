; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
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
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "utilities")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defun remove-constants (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (if (or (natp (car x))
              (equal (car x) t)
              (equal (car x) nil)
              (equal (car x) 'quote))
          (remove-constants (cdr x))
        (cons (car x) (remove-constants (cdr x))))
    nil))

;; (deflist name formals element
;;   &key negatedp
;;        guard
;;        verify-guards
;;        already-definedp)
;;
;; Examples:
;;   (deflist integer-listp (x) (integerp x))
;;   (deflist tuple-listp (n x) (tuplep n x) :guard (natp n))
;;   (deflist all-subsetp (x super) (subsetp x super))
;;   (deflist nat-free-listp (x) (natp x) :negatedp t)
;;
;; We define a recognizer for a list of elementp's, or, if negatedp is set, a
;; list of non-elementp's.  We expect that element refers to a boolean-valued
;; function.
;;
;; One of the formals must be named x, and this controls which argument
;; receives the list to check.  None of the formals may be named a or y,
;; because we use these names in the theorems we generate.
;;
;; The optional :guard and :verify-guards are given to the defund which we
;; introduce.  I.e., they need to talk about the list recognizer, not the
;; element recognizer.
;;
;; The special :already-definedp keyword can be set if you have already given a
;; definition of the function.  If this is provided, we will only write down
;; the deflist theorems and we will not generate a defun event.  This is
;; sometimes useful when you have mutually recursive functions.
;;
;; The special :value-of-nil keyword can be useful when (elementp nil ...) is
;; always known to be t or nil.  This can produce cleaner theorems.


(defun deflist-fn (name formals element negatedp guard verify-guards already-definedp elementp-of-nil)
  (declare (xargs :mode :program))
  (and (or (ACL2::symbolp name)
           (ACL2::er ACL2::hard 'deflist
                     "Name must be a symbol, but is ~x0.~%" name))
       (or (and (ACL2::symbol-listp formals)
                (uniquep formals)
                (memberp 'x formals))
           (ACL2::er ACL2::hard 'deflist
                     "The formals must be a list of unique symbols which ~
                      contain x, but the formals are ~x0.~%" formals))
       (or (and (not (memberp 'y formals))
                (not (memberp 'a formals)))
           (ACL2::er ACL2::hard 'deflist
                     "As a special restriction, formals may not mention a, n, or ~
                      y, but the formals are ~x0.~%" formals))
       (or (and (ACL2::symbolp (car element))
                (consp element)
                ;; BOZO maybe we don't need to be so strict...
                ;(uniquep (remove-constants (cdr element)))
                ;(subsetp (remove-constants (cdr element)) formals))
                )
           (ACL2::er ACL2::hard 'deflist
                     "The element transformation must be a function applied ~
                      to the formals, but is ~x0.~%" element))
       (or (booleanp negatedp)
           (ACL2::er ACL2::hard 'deflist
                     ":negatedp must be a boolean, but is ~x0.~%"
                     negatedp))
       (or (booleanp verify-guards)
           (ACL2::er ACL2::hard 'deflist
                     ":verify-guards must be a boolean, but is ~x0.~%"
                     verify-guards))
  (let ((elementp (car element))
        (elem-formals (cdr element)))

    `(encapsulate
      ()
      ,@(if already-definedp
            nil
          `((defund ,name (,@formals)
              (declare (xargs :guard ,guard
                              :verify-guards ,verify-guards))
              (if (consp x)
                  (and ,(if negatedp
                            `(not (,elementp ,@(ACL2::subst '(car x) 'x elem-formals)))
                          `(,elementp ,@(ACL2::subst '(car x) 'x elem-formals)))
                       (,name    ,@(ACL2::subst '(cdr x) 'x formals)))
                t))))

      (defthm ,(ACL2::mksym name '-when-not-consp)
        (implies (not (consp x))
                 (equal (,name ,@formals)
                        t))
        :hints(("Goal" :in-theory (enable ,name))))

      (defthm ,(ACL2::mksym name '-of-cons)
        (equal (,name ,@(ACL2::subst '(cons a x) 'x formals))
               (and ,(if negatedp
                         `(not (,elementp ,@(ACL2::subst 'a 'x elem-formals)))
                       `(,elementp ,@(ACL2::subst 'a 'x elem-formals)))
                    (,name ,@formals)))
        :hints(("Goal" :in-theory (enable ,name))))

      (defthm ,(ACL2::mksym 'booleanp-of- name)
        (equal (booleanp (,name ,@formals))
               t)
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym name '-of-list-fix)
        (equal (,name ,@(ACL2::subst '(list-fix x) 'x formals))
               (,name ,@formals))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym name '-of-app)
        (equal (,name ,@(ACL2::subst '(app x y) 'x formals))
               (and (,name ,@formals)
                    (,name ,@(ACL2::subst 'y 'x formals))))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym name '-of-rev)
        (equal (,name ,@(ACL2::subst '(rev x) 'x formals))
               (,name ,@formals))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym elementp '-of-car-when- name)
        (implies (,name ,@formals)
                 (equal (,elementp ,@(ACL2::subst '(car x) 'x elem-formals))
                        ,(cond ((equal elementp-of-nil nil)
                                (if negatedp
                                    ;; If x is a cons, then its car is not an element.
                                    ;; Else its car is nil, which is not an element.
                                    nil
                                  ;; If x is a cons, then its car is an element.
                                  ;; Else its car is nil, which is not an element.
                                  `(consp x)))
                               ((equal elementp-of-nil t)
                                (if negatedp
                                    ;; If x is a cons, then its car is not an element.
                                    ;; Else its car is nil, which is an element.
                                    `(not (consp x))
                                  ;; If x is a cons, then its car is an element.
                                  ;; Else its car is nil, which is an element.
                                  t))
                               ((equal elementp-of-nil :unknown)
                                `(if (consp x)
                                     ,(not negatedp)
                                   (,elementp ,@(ACL2::subst nil 'x elem-formals))))
                               (t
                                (ACL2::er hard '%deflist "Error: elementp-of-nil must be t or nil."))))))

      (defthm ,(ACL2::mksym name '-of-cdr-when- name)
        (implies (,name ,@formals)
                 (equal (,name ,@(ACL2::subst '(cdr x) 'x formals))
                        t)))

      (defthm ,(ACL2::mksym elementp '-when-memberp-of- name)
        (implies (and (,name ,@formals)
                      (memberp a x))
                 (equal (,elementp ,@(ACL2::subst 'a 'x elem-formals))
                        ,(not negatedp)))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym elementp '-when-memberp-of- name '-alt)
        (implies (and (memberp a x)
                      (,name ,@formals))
                 (equal (,elementp ,@(ACL2::subst 'a 'x elem-formals))
                        ,(not negatedp))))

      (defthm ,(ACL2::mksym name '-of-remove-all-when- name)
        (implies (,name ,@formals)
                 (equal (,name ,@(ACL2::subst '(remove-all a x) 'x formals))
                        t))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym name '-of-remove-duplicates)
        (equal (,name ,@(ACL2::subst '(remove-duplicates x) 'x formals))
               (,name ,@formals))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym name '-of-difference-when- name)
        (implies (,name ,@formals)
                 (equal (,name ,@(ACL2::subst '(difference x y) 'x formals))
                        t))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym name '-of-subsetp-when- name)
        (implies (and (,name ,@(ACL2::subst 'y 'x formals))
                      (subsetp x y))
                 (equal (,name ,@formals)
                        t))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym name '-of-subsetp-when- name '-alt)
        (implies (and (subsetp x y)
                      (,name ,@(ACL2::subst 'y 'x formals)))
                 (equal (,name ,@formals)
                        t)))

      (defthm ,(ACL2::mksym name '-of-repeat)
        ;; It's sort of ugly to use y here instead of n, but this way we have
        ;; fewer restrictions on the formals for deflist.
        (equal (,name ,@(ACL2::subst '(repeat a y) 'x formals))
               (or ,(if negatedp
                        `(not (,elementp ,@(ACL2::subst 'a 'x elem-formals)))
                      `(,elementp ,@(ACL2::subst 'a 'x elem-formals)))
                   (zp y)))
        :hints(("Goal" :in-theory (enable repeat))))

      ))))

(defmacro deflist (name formals element
                        &key
                        (negatedp 'nil)
                        (guard 't)
                        (verify-guards 't)
                        (already-definedp 'nil)
                        (elementp-of-nil ':unknown))
  (deflist-fn name formals element negatedp guard verify-guards already-definedp elementp-of-nil))




;; (defprojection &key list element guard verify-guards nil-preservingp already-definedp)
;;
;; Examples.
;;   (defprojection :list (strip-firsts x)
;;                  :element (first x)
;;                  :guard (cons-listp x)
;;                  :nil-preservingp t)
;;
;; We define a projection function which takes the element-transforming
;; function "element" and applies it across a list.  The new function gets the
;; name given to it by list.
;;
;; We also define a tail-recursive variant of this projection function,
;; fast-list$, which we prove is basically equal to the reverse of the list
;; function.
;;
;; If the element-transforming function always produces nil when its x argument
;; is nil, then you should pass :nil-preservingp t, which strengthens certain
;; theorems.

(defun defprojection-fn (list element nil-preservingp already-definedp guard verify-guards)
  (declare (xargs :mode :program))
  (let* ((list-fn   (car list))
         (list-args (cdr list))
         (elem-fn   (car element))
         (elem-args (cdr element))
         (fast-fn   (if (ACL2::has-namespace list-fn)
                        (ACL2::mksym (ACL2::extract-namespace list-fn)
                               '.fast-
                               (ACL2::extract-nonnamespace list-fn)
                               '$)
                      (ACL2::mksym 'fast- list-fn '$))))
    `(encapsulate
      ()
      ,@(if already-definedp
            nil
          `((defund ,list-fn (,@list-args)
              (declare (xargs :guard ,guard
                              :verify-guards ,verify-guards))
              (if (consp x)
                  (cons (,elem-fn ,@(ACL2::subst '(car x) 'x elem-args))
                        (,list-fn ,@(ACL2::subst '(cdr x) 'x list-args)))
                nil))

            (defund ,fast-fn (,@list-args acc)
              (declare (xargs :guard ,(if (equal guard t)
                                          `(true-listp acc)
                                        `(and (true-listp acc)
                                              ,guard))
                              :verify-guards ,verify-guards))
              (if (consp x)
                  (,fast-fn ,@(ACL2::subst '(cdr x) 'x list-args)
                            (cons (,elem-fn ,@(ACL2::subst '(car x) 'x elem-args))
                                  acc))
                acc))))

      (defthm ,(ACL2::mksym list-fn '-when-not-consp)
        (implies (not (consp x))
                 (equal (,list-fn ,@list-args)
                        nil))
        :hints(("Goal" :in-theory (enable ,list-fn))))

      (defthm ,(ACL2::mksym list-fn '-of-cons)
        (equal (,list-fn ,@(ACL2::subst '(cons a x) 'x list-args))
               (cons (,elem-fn ,@(ACL2::subst 'a 'x elem-args))
                     (,list-fn ,@list-args)))
        :hints(("Goal" :in-theory (enable ,list-fn))))

      (defthm ,(ACL2::mksym 'true-listp-of- list-fn)
        (equal (true-listp (,list-fn ,@list-args))
               t)
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym 'len-of- list-fn)
        (equal (len (,list-fn ,@list-args))
               (len x))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym 'consp-of- list-fn)
        (equal (consp (,list-fn ,@list-args))
               (consp x))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym 'car-of- list-fn)
        (equal (car (,list-fn ,@list-args))
               ,(if nil-preservingp
                    `(,elem-fn ,@(ACL2::subst '(car x) 'x elem-args))
                  `(if (consp x)
                       (,elem-fn ,@(ACL2::subst '(car x) 'x elem-args))
                     nil))))

      (defthm ,(ACL2::mksym 'cdr-of- list-fn)
        (equal (cdr (,list-fn ,@list-args))
               (,list-fn ,@(ACL2::subst '(cdr x) 'x list-args))))

      (defthm ,(ACL2::mksym list-fn '-under-iff)
        (iff (,list-fn ,@list-args)
             (consp x))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym list-fn '-of-list-fix)
        (equal (,list-fn ,@(ACL2::subst '(list-fix x) 'x list-args))
               (,list-fn ,@list-args))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym list-fn '-of-app)
        (equal (,list-fn ,@(ACL2::subst '(app x y) 'x list-args))
               (app (,list-fn ,@list-args)
                    (,list-fn ,@(ACL2::subst 'y 'x list-args))))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym list-fn '-of-rev)
        (equal (,list-fn ,@(ACL2::subst '(rev x) 'x list-args))
               (rev (,list-fn ,@list-args)))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym 'firstn-of- list-fn)
        (equal (firstn y (,list-fn ,@list-args))
               (,list-fn ,@(ACL2::subst '(firstn y x) 'x list-args)))
        :hints(("Goal"
                :in-theory (enable firstn)
                :induct (firstn y x))))

      (defthm ,(ACL2::mksym 'restn-of- list-fn)
        (equal (restn y (,list-fn ,@list-args))
               (,list-fn ,@(ACL2::subst '(restn y x) 'x list-args)))
        :hints(("Goal"
                :in-theory (enable restn)
                :induct (restn y x))))

      (defthm ,(ACL2::mksym 'rev-of- list-fn)
        (equal (rev (,list-fn ,@list-args))
               (,list-fn ,@(ACL2::subst '(rev x) 'x list-args))))

      (in-theory (disable ,(ACL2::mksym list-fn '-of-rev)))

      (ACL2::theory-invariant (ACL2::incompatible (:rewrite ,(ACL2::mksym list-fn '-of-rev))
                                                  (:rewrite ,(ACL2::mksym 'rev-of- list-fn))))

      (defthm ,(ACL2::mksym 'memberp-of- elem-fn '-in- list-fn '-when-memberp)
        (implies (memberp a x)
                 (equal (memberp (,elem-fn ,@(ACL2::subst 'a 'x elem-args))
                                 (,list-fn ,@list-args))
                        t))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym 'subsetp-of- list-fn 's-when-subsetp)
        (implies (subsetp x y)
                 (equal (subsetp (,list-fn ,@list-args)
                                 (,list-fn ,@(ACL2::subst 'y 'x list-args)))
                        t))
        :hints(("Goal" :induct (cdr-induction x))))

      ,@(if nil-preservingp
            `((defthm ,(ACL2::mksym 'nth-of- list-fn)
                (equal (nth n (,list-fn ,@list-args))
                       (,elem-fn ,@(ACL2::subst '(nth n x) 'x elem-args)))
                :hints(("Goal"
                        :in-theory (enable nth)
                        :induct (nth n x)))))
          nil)

      ,@(if already-definedp
            nil
          `((defthm ,(ACL2::mksym fast-fn '-removal)
              (implies (force (true-listp acc))
                       (equal (,fast-fn ,@list-args acc)
                              (revappend (,list-fn ,@list-args) acc)))
              :hints(("Goal" :in-theory (enable ,fast-fn))))))

      )))

(ACL2::defmacro defprojection (&key list element nil-preservingp already-definedp
                              (guard 't)
                              (verify-guards 't))
  (declare (xargs :guard (and (ACL2::symbol-listp list)
                              (ACL2::symbol-listp element)
                              (booleanp nil-preservingp)
                              (booleanp verify-guards)
                              (booleanp already-definedp)
                              (consp list)
                              (consp element)
                              (uniquep (cdr list))
                              (let ((element-vars (remove-constants (cdr element))))
                                (and (uniquep element-vars)
                                     (memberp 'x element-vars)
                                     (not (memberp 'a element-vars))
                                     (not (memberp 'y element-vars))
                                     (not (memberp 'acc element-vars))
                                     (subsetp element-vars (cdr list))
                                     (subsetp (cdr list) element-vars))))))
  (defprojection-fn list element nil-preservingp already-definedp guard verify-guards))




;; (defmap &key map key val key-list val-list guard verify-guards)
;;
;; Example:
;;
;; (deflist :list (nat-listp x) :element (natp x))
;; (deflist :list (sym-listp x) :element (symbolp x))
;;
;; (defmap :map (sym-nat-mapp x)
;;         :key (symbolp x)
;;         :val (natp x)
;;         :key-list (sym-listp x)
;;         :val-list (nat-listp x))
;;
;; We define a mapping (alist) from keys to values.  We expect that the key
;; recognizer and value recognizer are boolean-valued functions.  The key
;; recognizer doesn't get a chance to look at the value, and similarly the
;; value recognizer doesn't get to look at the key.

(defun defmap-fn (map key val key-list val-list guard verify-guards val-of-nil)
  (declare (xargs :mode :program))
  (let ((mapp (car map))
        (keyp (car key))
        (valp (car val))
        (key-listp (car key-list))
        (val-listp (car val-list))
        (map-formals (cdr map))
        (key-formals (cdr key))
        (val-formals (cdr val))
        (key-list-formals (cdr key-list))
        (val-list-formals (cdr val-list)))
    `(encapsulate
      ()
      (defund ,mapp (,@map-formals)
        (declare (xargs :guard ,guard
                        :verify-guards ,verify-guards))
        (if (consp x)
            (and (consp (car x))
                 (,keyp ,@(ACL2::subst '(car (car x)) 'x key-formals))
                 (,valp ,@(ACL2::subst '(cdr (car x)) 'x val-formals))
                 (,mapp ,@(ACL2::subst '(cdr x) 'x map-formals)))
          t))

      (defthm ,(ACL2::mksym mapp '-when-not-consp)
        (implies (not (consp x))
                 (equal (,mapp ,@map-formals)
                        t))
        :hints(("Goal" :in-theory (enable ,mapp))))

      (defthm ,(ACL2::mksym mapp '-of-cons)
        (equal (,mapp ,@(ACL2::subst '(cons a x) 'x map-formals))
               (and (consp a)
                    (,keyp ,@(ACL2::subst '(car a) 'x key-formals))
                    (,valp ,@(ACL2::subst '(cdr a) 'x val-formals))
                    (,mapp ,@map-formals)))
        :hints(("Goal" :in-theory (enable ,mapp))))

      (defthm ,(ACL2::mksym 'consp-when-memberp-of- mapp)
        (implies (and (,mapp ,@map-formals)
                      (memberp a x))
                 (equal (consp a)
                        t))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym 'consp-when-memberp-of- mapp '-alt)
        (implies (and (memberp a x)
                      (,mapp ,@map-formals))
                 (equal (consp a)
                        t)))

      (defthm ,(ACL2::mksym keyp '-of-car-when-memberp-of- mapp)
        (implies (and (,mapp ,@map-formals)
                      (memberp a x))
                 (equal (,keyp ,@(ACL2::subst '(car a) 'x key-formals))
                        t))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym keyp '-when-lookup-in- mapp)
        (implies (and (,mapp ,@map-formals)
                      (lookup a x))
                 (equal (,keyp ,@(ACL2::subst 'a 'x key-formals))
                        t))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym valp '-of-cdr-when-memberp-of- mapp)
        (implies (and (,mapp ,@map-formals)
                      (memberp a x))
                 (equal (,valp ,@(ACL2::subst '(cdr a) 'x val-formals))
                        t))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym 'booleanp-of- mapp)
        (equal (booleanp (,mapp ,@map-formals))
               t)
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym mapp '-of-list-fix)
        (equal (,mapp ,@(ACL2::subst '(list-fix x) 'x map-formals))
               (,mapp ,@map-formals))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym mapp '-of-app)
        (equal (,mapp ,@(ACL2::subst '(app x y) 'x map-formals))
               (and (,mapp ,@map-formals)
                    (,mapp ,@(ACL2::subst 'y 'x map-formals))))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym mapp '-of-rev)
        (equal (,mapp ,@(ACL2::subst '(rev x) 'x map-formals))
               (,mapp ,@map-formals))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym mapp '-of-remove-all-when- mapp)
        (implies (,mapp ,@map-formals)
                 (,mapp ,@(ACL2::subst '(remove-all a x) 'x map-formals)))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym mapp '-of-remove-duplicates)
        (equal (,mapp ,@(ACL2::subst '(remove-duplicates x) 'x map-formals))
               (,mapp ,@map-formals))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym mapp '-of-difference-when- mapp)
        (implies (,mapp ,@map-formals)
                 (equal (,mapp ,@(ACL2::subst '(difference x y) 'x map-formals))
                        t))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym mapp '-of-subset-when- mapp)
        (implies (and (,mapp ,@(ACL2::subst 'y 'x map-formals))
                      (subsetp x y))
                 (equal (,mapp ,@map-formals)
                        t))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym mapp '-of-subset-when- mapp '-alt)
        (implies (and (subsetp x y)
                      (,mapp ,@(ACL2::subst 'y 'x map-formals)))
                 (equal (,mapp ,@map-formals)
                        t)))

      ,@(if (not key-list)
            nil
          `((defthm ,(ACL2::mksym key-listp '-of-domain-when- mapp)
              (implies (,mapp ,@map-formals)
                       (equal (,key-listp ,@(ACL2::subst '(domain x) 'x key-list-formals))
                              t))
              :hints(("Goal" :induct (cdr-induction x))))))

      ,@(if (not val-list)
            nil
          `((defthm ,(ACL2::mksym val-listp '-of-range-when- mapp)
              (implies (,mapp ,@map-formals)
                       (equal (,val-listp ,@(ACL2::subst '(range x) 'x val-list-formals))
                              t))
              :hints(("Goal" :induct (cdr-induction x))))))

      (defthm ,(ACL2::mksym 'mapp-when- mapp)
        (implies (,mapp ,@map-formals)
                 (equal (mapp x)
                        t))
        :hints(("Goal" :induct (cdr-induction x))))

      (defthm ,(ACL2::mksym valp '-of-cdr-of-lookup-when- mapp)
        (implies (,mapp ,@map-formals)
                 (equal (,valp ,@(ACL2::subst '(cdr (lookup a x)) 'x val-formals))
                        ,(if val-of-nil
                             't
                           `(if (lookup a x) t nil))))
        :hints(("Goal" :induct (cdr-induction x))))

      ,@(if val-of-nil
            nil
          `((defthm ,(ACL2::mksym 'cdr-of-lookup-under-iff-when- mapp)
              (implies (,mapp ,@map-formals)
                       (iff (cdr (lookup a x))
                            (lookup a x)))
              :hints(("Goal"
                      :in-theory (disable ,(ACL2::mksym valp '-of-cdr-of-lookup-when- mapp))
                      :use ((:instance ,(ACL2::mksym valp '-of-cdr-of-lookup-when- mapp))))))))


      ;;       (defthm ,(ACL2::mksym valp '-of-cdr-of-lookup-when- mapp '-hack)
      ;;         ;; we prove the same rule for cdr, so you can just test the cdr instead
      ;;         ;; of the whole pair, which is sometimes convenient
      ;;         (implies (and (,mapp ,@map-formals)
      ;;                       (cdr (lookup a x)))
      ;;                  (equal (,valp ,@(ACL2::subst '(cdr (lookup a x)) 'x val-formals))
      ;;                         t))
      ;;         :hints(("Goal" :induct (cdr-induction x))))

      )))

(defmacro defmap (&key map key val key-list val-list
                       (guard 't)
                       (verify-guards 't)
                       (val-of-nil 't))
  (declare (xargs :guard (and (ACL2::symbol-listp map)
                              (ACL2::symbol-listp key)
                              (ACL2::symbol-listp val)
                              (ACL2::symbol-listp key-list)
                              (ACL2::symbol-listp val-list)
                              (consp map)
                              (consp key)
                              (consp val)
                              (or (consp key-list) (not key-list))
                              (or (consp val-list) (not val-list))
                              ;; Argument lists must all be unique
                              (uniquep (cdr map))
                              (uniquep (cdr key))
                              (uniquep (cdr val))
                              (uniquep (cdr key-list))
                              (uniquep (cdr val-list))
                              ;; Argument lists must contain only the names in
                              ;; the map formals
                              (subsetp (cdr key) (cdr map))
                              (subsetp (cdr val) (cdr map))
                              (or (not key-list)
                                  (subsetp (cdr key-list) (cdr map)))
                              (or (not val-list)
                                  (subsetp (cdr val-list) (cdr map)))
                              ;; x must be in each argument list
                              ;; a,b must not be found in any argument list
                              (memberp 'x (cdr map))
                              (not (memberp 'a (cdr map)))
                              (not (memberp 'y (cdr map))))))
  (defmap-fn map key val key-list val-list guard verify-guards val-of-nil))

