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
(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic")
(include-book "eval-g-base")

(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))

(local (in-theory (disable acl2::revappend-removal)))

;; ;; This brings if-then-elses up from atoms to the top level of a cons tree.
;; (defun propagate-ites-above-conses (x )
;;   (declare (xargs :guard (gobjectp x)))
;;   (if (general-concretep x)
;;       x
;;     (pattern-match x
;;       ((g-ite test then else)
;;        (g-ite test (propagate-ites-above-conses then)
;;               (propagate-ites-above-conses else)))
;;       ((g-apply & &) x)
;;       ((g-var &) x)
;;       ((g-number &) x)
;;       ((g-boolean &) x)
;;       (& (if (general-concretep (car x))
;;              (cons (car x)
;;                    (propagate-ites-above-conses

(local (in-theory (disable member-eq)))

(defun revappend-concrete (a b)
  (declare (xargs :guard (true-listp a)))
  (if (endp a)
      b
    (revappend-concrete (cdr a)
                        (gl-cons (mk-g-concrete (car a)) b))))

(defthm no-deps-of-revappend-concrete
  (implies (not (gobj-depends-on k p b))
           (not (gobj-depends-on k p (revappend-concrete a b)))))

(local
 (progn
   ;; (defthm gobjectp-revappend-concrete
   ;;   (implies (gobjectp b)
   ;;            (gobjectp (revappend-concrete a b))))

   (defthm revappend-concrete-correct
     (equal (eval-g-base (revappend-concrete a b) env)
            (revappend a (eval-g-base b env)))
     :hints(("Goal" :induct (revappend-concrete a b)
             :in-theory (enable revappend)
             :expand ((eval-g-base (cons (mk-g-concrete (car a)) b) env)))))))


;; (local (defthm len-of-gl-cons
;;          (equal (len (gl-cons a b))
;;                 (+ 1 (len b)))
;;          :hints(("Goal" :in-theory (enable gl-cons)))))

;; (defund g-ite-depth (x)
;;   (cond ((or (atom x) (not (eq (tag x) :g-ite))) 0)
;;         (t (+ 1 (max (g-ite-depth (g-ite->then x))
;;                      (g-ite-depth (g-ite->else x)))))))

;; (defthm g-ite-depth-of-g-ite->then
;;   (implies (eq (tag x) :g-ite)
;;            (< (g-ite-depth (g-ite->then x)) (g-ite-depth x)))
;;   :hints (("goal" :expand ((g-ite-depth x))))
;;   :rule-classes :linear)

;; (defthm g-ite-depth-of-g-ite->else
;;   (implies (eq (tag x) :g-ite)
;;            (< (g-ite-depth (g-ite->else x)) (g-ite-depth x)))
;;   :hints (("goal" :expand ((g-ite-depth x))))
;;   :rule-classes :linear)

;; (defthm g-ite-depth-of-car-of-gl-cons
;;   (equal (g-ite-depth (car (gl-cons a b)))
;;          (g-ite-depth a))
;;   :hints(("Goal" :in-theory (enable g-ite-depth gl-cons))))

(defthm acl2-count-of-gl-cons-ite-then
  (implies (equal (tag a) :g-ite)
           (< (acl2-count (gl-cons (g-ite->then a) b))
              (+ 1 (acl2-count a) (acl2-count b))))
  :hints(("Goal" :in-theory (enable gl-cons tag g-ite->then g-concrete)))
  :rule-classes :linear)

(defthm acl2-count-of-gl-cons-ite-else
  (implies (equal (tag a) :g-ite)
           (< (acl2-count (gl-cons (g-ite->else a) b))
              (+ 1 (acl2-count a) (acl2-count b))))
  :hints(("Goal" :in-theory (enable gl-cons tag g-ite->else g-concrete)))
  :rule-classes :linear)


;; Collect concrete characters onto "pre".
(define coerce-string (x pre hyp)
  :guard (true-listp pre)
  :verify-guards nil
  (b* ((hyp (lbfr-hyp-fix hyp)))
    (replace-g-ifs
     (if (or (general-concretep x) (atom x))
         (gret (mk-g-concrete
                (ec-call (coerce (revappend pre (general-concrete-obj x)) 'string))))
       (pattern-match x
         ((g-ite test then else)
          (g-if (gret test)
                (coerce-string then pre hyp)
                (coerce-string else pre hyp)))
         ((g-apply & &) (gret (g-apply 'coerce (gl-list (revappend-concrete pre x) 'string))))
         ((g-var &) (gret (g-apply 'coerce (gl-list (revappend-concrete pre x) 'string))))
         ((g-integer &)
          (gret (mk-g-concrete
                 (ec-call (coerce (revappend pre nil) 'string)))))
         ((g-boolean &)
          (gret (mk-g-concrete
                 (ec-call (coerce (revappend pre nil) 'string)))))
         ((g-concrete obj)
          ;; Actually taken care of by the first IF.
          (gret (mk-g-concrete
                 (ec-call (coerce (revappend pre obj) 'string)))))
         (& (if (or (general-concretep (car x))
                    (atom (car x)))
                (coerce-string (cdr x) (cons (general-concrete-obj (car x)) pre)
                               hyp)
              (pattern-match (car x)
                ((g-ite test then else)
                 (g-if (gret test)
                       (coerce-string (gl-cons then (cdr x)) pre hyp)
                       (coerce-string (gl-cons else (cdr x)) pre hyp)))
                ((g-apply & &) (gret (g-apply 'coerce (gl-list (revappend-concrete pre x)
                                                               'string))))
                ((g-var &) (gret (g-apply 'coerce (gl-list (revappend-concrete pre x)
                                                           'string))))
                (&
                 (coerce-string (cdr x) (cons (code-char 0) pre) hyp)))))))))
  ///
  (def-hyp-congruence coerce-string)
  (verify-guards coerce-string
    :hints(("Goal" :in-theory (e/d (g-if-fn g-or-fn)
                                   (coerce-string)))))

  (defthm deps-of-coerce-string
    (implies (not (gobj-depends-on k p x))
             (not (gobj-depends-on k p (mv-nth 0 (coerce-string x pre hyp)))))
    :hints (("goal" :induct (coerce-string x pre hyp)
             :expand ((coerce-string x pre hyp))
             :in-theory (disable (:d coerce-string))))))


(local
 (progn
   ;; (defthm gobjectp-coerce-string
   ;;   (implies (and (gobjectp x)
   ;;                 (bfr-p hyp))
   ;;            (gobjectp (coerce-string x pre hyp)))
   ;;   :hints(("Goal" :in-theory (e/d () ((:definition coerce-string)))
   ;;           :induct (coerce-string x pre hyp)
   ;;           :expand ((coerce-string x pre hyp)))))

   (defthmd atom-impl-general-concretep-1
     (implies (not (consp x))
              (general-concretep x))
     :hints(("Goal" :in-theory (enable general-concretep-def)))
     :rule-classes ((:rewrite :backchain-limit-lst 1)))

   ;; (defthm gobjectp-car-cdr-when-cons
   ;;   (implies (and (gobjectp x)
   ;;                 (consp x)
   ;;                 (not (g-ite-p x))
   ;;                 (not (g-apply-p x))
   ;;                 (not (g-var-p x))
   ;;                 (not (g-number-p x))
   ;;                 (not (g-boolean-p x))
   ;;                 (not (g-concrete-p x)))
   ;;            (and (gobjectp (car x))
   ;;                 (gobjectp (cdr x)))))
   ))


(local
 (encapsulate
   nil

   (local
    (progn
      (defthm coerce-non-character-list
        (implies (syntaxp (not (equal (acl2::mfc-rw `(character-listp ,x) t t mfc state) acl2::*t*)))
                 (equal (coerce x 'string)
                        (coerce (make-character-list x) 'string)))
        :hints (("goal" :use (:instance completion-of-coerce
                                        (y 'string)))))

      (defthm make-character-list-character-list
        (character-listp (make-character-list x)))

      (defthm make-character-list-revappend
        (equal (make-character-list (revappend a b))
               (revappend (make-character-list a) (make-character-list b))))

      (defthm revappend-non-character-list-not-character-list
        (implies (not (character-listp x))
                 (not (character-listp (revappend y x)))))

      (defthm revappend-character-lists
        (implies (and (character-listp x)
                      (character-listp y))
                 (character-listp (revappend y x))))))

   (defthm coerce-revappend-atom
     (implies (and (syntaxp (not (equal x ''nil)))
                   (atom x))
              (equal (coerce (revappend y x) 'string)
                     (coerce (revappend y nil) 'string))))))

(local (defthm eval-g-base-general-concrete-obj
         (implies (general-concretep x)
                  (equal (eval-g-base x env)
                         (general-concrete-obj x)))
         :hints (("goal" :expand ((eval-g-base x env)))
                 (and stable-under-simplificationp
                      '(:in-theory (enable general-concretep))))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local
 (encapsulate nil

   (local
    (progn
      (defthmd coerce-non-character-list
        (implies (syntaxp (not (equal (acl2::mfc-rw `(character-listp ,x) t t mfc state) acl2::*t*)))
                 (equal (coerce x 'string)
                        (coerce (make-character-list x) 'string)))
        :hints (("goal" :use (:instance completion-of-coerce
                                        (y 'string)))))

      (defthm make-character-list-character-list
        (character-listp (make-character-list x)))

      (defthm make-character-list-revappend
        (equal (make-character-list (revappend a b))
               (revappend (make-character-list a) (make-character-list b))))

      (defthm revappend-non-character-list-not-character-list
        (implies (not (character-listp x))
                 (not (character-listp (revappend y x)))))

      (defthm revappend-character-lists
        (implies (and (character-listp x)
                      (character-listp y))
                 (character-listp (revappend y x))))))

   (local (defthm coerce-revappend-atom
            (implies (and (syntaxp (not (equal x ''nil)))
                          (atom x))
                     (equal (coerce (revappend y x) 'string)
                            (coerce (revappend y nil) 'string)))
            :hints(("Goal" :in-theory (enable coerce-non-character-list)))))


   (local (defthm coerce-string-non-consp
            (implies (not (consp x))
                     (equal (coerce x 'string)
                            ""))))

   (local (defthm consp-eval-g-base-boolean
            (implies (g-boolean-p x)
                     (not (consp (eval-g-base x env))))
            :hints(("Goal" :in-theory (enable eval-g-base)))))

   (local (defthm consp-eval-g-base-integer
            (implies (g-integer-p x)
                     (not (consp (eval-g-base x env))))
            :hints(("Goal" :in-theory (enable eval-g-base)))))

   (local (defthm general-concrete-obj-atom
            (implies (atom x)
                     (equal (general-concrete-obj x) x))
            :hints(("Goal" :in-theory (enable general-concrete-obj)))))

;;    (local (defthm eval-g-base-not-character-p
;;             (implies (and (gobjectp x)
;;                           (not (general-concretep x))
;;                           (not (g-ite-p x))
;;                           (not (g-apply-p x))
;;                           (not (g-var-p x)))
;;                      (not (characterp (eval-g-base x env))))
;;             :hints(("Goal" :in-theory (enable (:induction eval-g-base)
;;                                               general-concretep-def)
;;                     :induct (eval-g-base x env)
;;                     :expand ((:with eval-g-base (eval-g-base x env)))))))


   (local (defthm eval-g-base-atom
            (implies (not (consp x))
                     (equal (eval-g-base x env) x))
            :hints(("Goal" :in-theory (enable eval-g-base)))
            :rule-classes ((:rewrite :backchain-limit-lst (0)))))



   (defthm coerce-string-correct
     (implies (bfr-hyp-eval hyp (car env))
              (equal (eval-g-base (mv-nth 0 (coerce-string x pre hyp)) env)
                     (coerce (revappend pre (eval-g-base x env)) 'string)))
     :hints(("Goal" :in-theory (e/d* ( general-concrete-obj
                                       concrete-gobjectp-def
                                       eval-g-base-list
                                       general-concretep-def
                                       (:i coerce-string))
                                     ((:definition coerce-string)
                                      member eval-g-base
                                      equal-of-booleans-rewrite
                                      bfr-eval-booleanp
                                      bool-cond-itep-eval
                                      default-car
                                      eval-g-base-alt-def
                                      ))
             :induct (coerce-string x pre hyp)
             :expand ((coerce-string x pre hyp)
                      (:with eval-g-base (eval-g-base x env))))
            (and stable-under-simplificationp
                 '(:in-theory
                   (e/d (coerce-non-character-list
                         general-concrete-obj
                         concrete-gobjectp-def
                         general-concretep-def)
                        ((:definition coerce-string)
                         member eval-g-base
                         equal-of-booleans-rewrite
                         bfr-eval-booleanp
                         bool-cond-itep-eval
                         default-car
                         eval-g-base-alt-def
                         ))
                   :expand ((:with eval-g-base (eval-g-base (car x) env)))))))))

(define coerce-list (x hyp)
  :verify-guards nil
  (b* ((hyp (lbfr-hyp-fix hyp)))
    (if (or (general-concretep x) (atom x))
        (gret (mk-g-concrete
               (ec-call (coerce (general-concrete-obj x) 'list))))
      (pattern-match x
        ((g-ite test then else)
         (g-if-mbe (gret test)
                   (coerce-list then hyp)
                   (coerce-list else hyp)))
        ((g-apply & &) (gret (g-apply 'coerce (gl-list x 'list))))
        ((g-var &) (gret (g-apply 'coerce (gl-list x 'list))))
        (& (gret nil)))))
  ///
  (def-hyp-congruence coerce-list)
  (verify-guards coerce-list
    :hints(("Goal" :in-theory (enable g-if-fn))))

  (defthm deps-of-coerce-list
    (implies (not (gobj-depends-on k p x))
             (not (gobj-depends-on k p (mv-nth 0 (coerce-list x hyp)))))
    :hints (("goal" :induct  (coerce-list x hyp)
             :expand ((coerce-list x hyp))
             :in-theory (disable (:d coerce-list))))))


;; (local
;;  (defthm gobjectp-coerce-list
;;    (implies (and (gobjectp x)
;;                  (bfr-p hyp))
;;             (gobjectp (coerce-list x hyp)))
;;    :hints (("goal" :in-theory (e/d () ((:definition coerce-list)))
;;             :induct (coerce-list x hyp)
;;             :expand ((coerce-list x hyp))))))




(encapsulate nil
  (local (in-theory (disable member-equal)))

  (local (defthm-gobj-flag
           (defthm stringp-eval-g-base
             (implies (and (not (general-concretep x))
                           (not (g-ite-p x))
                           (not (g-apply-p x))
                           (not (g-var-p x)))
                      (not (stringp (eval-g-base x env))))
             :flag gobj)
           :skip-others t
           :hints(("Goal" :in-theory (e/d (general-concretep-def))
                   :expand ((:with eval-g-base (eval-g-base x env)))))))



  (defthm coerce-list-correct
    (implies (and (bfr-hyp-eval hyp (car env)))
             (equal (eval-g-base (mv-nth 0 (coerce-list x hyp)) env)
                    (coerce (eval-g-base x env) 'list)))
    :hints(("Goal" :in-theory (e/d* (; (:ruleset g-correct-lemmas)
                                     eval-g-base-general-concrete-obj
                                     eval-g-base eval-g-base-list
                                     (:i coerce-list))
                                    ((:definition coerce-list)
                                     eval-g-base-alt-def))
            :induct (coerce-list x hyp)
            :expand ((coerce-list x hyp)))
           (and stable-under-simplificationp
                '(:in-theory (enable general-concrete-obj))))))

(in-theory (disable coerce-list coerce-string))

(def-g-fn coerce
  `(if (general-concretep y)
       (if (eq (general-concrete-obj y) 'list)
           (coerce-list x hyp)
         (coerce-string x nil hyp))
     (pattern-match y
       ((g-ite ytest ythen yelse)
        (if (zp clk)
            (gret (g-apply 'coerce (gl-list x y)))
          (g-if (gret ytest)
                (,gfn x ythen hyp clk config bvar-db state)
                (,gfn x yelse hyp clk config bvar-db state))))
       ((g-apply & &)
        (gret (g-apply 'coerce (gl-list x y))))
       ((g-var &)
        (gret (g-apply 'coerce (gl-list x y))))
       (& (coerce-string x nil hyp)))))


;; (def-gobjectp-thm coerce
;;   :hints `(("Goal" :in-theory (disable gobj-fix-when-not-gobjectp
;;                                        hyp-fix-of-hyp-fixedp
;;                                        (:definition ,gfn))
;;             :induct (,gfn x y hyp clk)
;;             :expand ((,gfn x y hyp clk)))))

(verify-g-guards
 coerce
 :hints `(("Goal" :in-theory (disable ,gfn))))

(def-gobj-dependency-thm coerce
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(local
 (defthm-gobj-flag
   (defthm eval-g-base-not-equal-list
     (implies (and (not (general-concretep y))
                   (not (g-ite-p y))
                   (not (g-apply-p y))
                   (not (g-var-p y)))
              (not (equal (eval-g-base y env) 'list)))
     :flag gobj)
   :skip-others t
   :hints(("Goal" :in-theory (e/d (general-concretep-def)
                                  (eval-g-base-alt-def))
           :expand ((:with eval-g-base (eval-g-base y env)))))))



(def-g-correct-thm coerce eval-g-base
  :hints `(("Goal" :in-theory (e/d* (atom-impl-general-concretep-1
                                     eval-g-base)
                                    ((:definition ,gfn)
                                     ; eval-g-base-non-gobjectp

                                     ; eval-g-base-g-concrete
                                     bfr-eval-booleanp
                                     bool-cond-itep-eval
                                     general-boolean-value-correct
                                     ; eval-g-non-keyword-cons
                                     equal-of-booleans-rewrite
                                     ; g-eval-non-consp
                                     ;; general-number-components-ev
                                     hyp-fix-of-hyp-fixedp
                                     ; hyp-and-not-false-test-is-and
                                     default-car default-cdr
                                     (:rules-of-class :type-prescription :here)
                                     ; non-consp-eval-correct
                                     ; eval-g-base-g-apply-p
                                     eval-g-base-alt-def
                                     eval-g-base-not-equal-list))
            :induct ,gcall
            :expand (,gcall))
           (and stable-under-simplificationp
                '(:in-theory (enable general-concrete-obj-correct
                                     eval-g-base-not-equal-list)))))

