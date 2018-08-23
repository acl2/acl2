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
(include-book "glcp-geval")
(include-book "gtype-thms")
(include-book "gtests")
(include-book "general-object-thms")

(local
 (defthmd gl-eval-of-atom
   (implies (atom x)
            (equal (generic-geval x env) x))
   :hints (("goal" :in-theory (enable tag)
            :expand ((generic-geval x env))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(defmacro def-glcp-generic-geval-thm-instance (new-name orig-name &key (rule-classes 'nil rule-classes-p))
  `(acl2::def-functional-instance
     ,new-name ,orig-name
     ((generic-geval-ev glcp-generic-geval-ev)
      (generic-geval-ev-lst glcp-generic-geval-ev-lst)
      (generic-geval glcp-generic-geval)
      (generic-geval-list glcp-generic-geval-list))
     :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                                 glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                                (glcp-generic-geval-apply))
               :expand ((:with glcp-generic-geval (glcp-generic-geval x env))
                        (glcp-generic-geval-list x env))))
     . ,(and rule-classes-p `(:rule-classes ,rule-classes))))


(defsection glcp-generic-geval

  (local (in-theory (enable glcp-generic-geval)))

  (defthm glcp-generic-geval-atom
    (implies (atom x)
             (equal (glcp-generic-geval x env) x))
    :hints(("Goal" :in-theory (enable gl-eval-of-atom)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-glcp-generic-geval-thm-instance
   glcp-generic-geval-mk-g-boolean-correct
   mk-g-boolean-correct)

  (def-glcp-generic-geval-thm-instance
   glcp-generic-geval-mk-g-integer-correct
   mk-g-integer-correct)

  (def-glcp-generic-geval-thm-instance
   glcp-generic-geval-cons
   generic-geval-cons)

  (def-glcp-generic-geval-thm-instance
   glcp-generic-geval-g-apply-p
   generic-geval-g-apply-p)

  (in-theory (disable glcp-generic-geval-g-apply-p))



  (def-glcp-generic-geval-thm-instance
   glcp-generic-geval-mk-g-ite-correct
   mk-g-ite-correct)

  (def-glcp-generic-geval-thm-instance
   glcp-generic-geval-mk-g-concrete-correct
   mk-g-concrete-correct)

  (def-glcp-generic-geval-thm-instance
   glcp-generic-geval-g-concrete-quote-correct
   g-concrete-quote-correct)

  (def-glcp-generic-geval-thm-instance
   glcp-generic-geval-general-concrete-obj-correct
   general-concrete-obj-correct)


  (def-glcp-generic-geval-thm-instance
   glcp-generic-geval-of-gl-cons
   generic-geval-gl-cons)

  (def-glcp-generic-geval-thm-instance
   glcp-generic-geval-g-apply
   generic-geval-g-apply)

  (def-glcp-generic-geval-thm-instance
   glcp-generic-geval-alt-def
   generic-geval-alt-def
   ;; :do-not-induct
   ;;   t
   ;;   :expand ((glcp-generic-geval x env))))
   :rule-classes ((:definition :clique (glcp-generic-geval))))

  (in-theory (disable glcp-generic-geval-alt-def))

  (def-glcp-generic-geval-thm-instance
   glcp-generic-geval-general-consp-car-correct
   general-consp-car-correct)

  (def-glcp-generic-geval-thm-instance
    glcp-generic-geval-general-consp-correct
   general-consp-correct)

  (in-theory (disable glcp-generic-geval-general-consp-correct))

  (def-glcp-generic-geval-thm-instance
    glcp-generic-geval-general-consp-cdr-correct
   general-consp-cdr-correct)

  (def-glcp-generic-geval-thm-instance
   glcp-generic-geval-consp-general-consp
   consp-general-consp)

  (in-theory (disable glcp-generic-geval-general-consp-cdr-correct
                      glcp-generic-geval-general-consp-car-correct
                      glcp-generic-geval-consp-general-consp))


   (def-glcp-generic-geval-thm-instance
    bfr-assume-of-gtests-possibly-true-for-glcp-generic-geval
    bfr-assume-of-gtests-possibly-true)

   (def-glcp-generic-geval-thm-instance
    bfr-assume-of-gtests-possibly-false-for-glcp-generic-geval
    bfr-assume-of-gtests-possibly-false))





(defsection glcp-generic-geval-list

  (local (in-theory (enable glcp-generic-geval-list)))

  (defthm glcp-generic-geval-list-of-cons
    (equal (glcp-generic-geval-list (cons a b) env)
           (cons (glcp-generic-geval a env)
                 (glcp-generic-geval-list b env))))

  (defthm glcp-generic-geval-list-of-atom
    (implies (not (consp x))
             (equal (glcp-generic-geval-list x env) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  ;; (defthm glcp-generic-geval-when-gobj-list
  ;;   (implies (gobj-listp x)
  ;;            (equal (glcp-generic-geval x env)
  ;;                   (glcp-generic-geval-list x env)))
  ;;   :hints (("goal" :induct (gobj-listp x)
  ;;            :in-theory (enable gobj-listp))
  ;;           '(:use ((:instance glcp-generic-geval-of-gl-cons
  ;;                    (x (car x)) (y (cdr x))))
  ;;             :in-theory (enable gl-cons gobj-listp))))

  (defthm glcp-generic-geval-list-of-gl-cons
    (equal (glcp-generic-geval-list (gl-cons x y) env)
           (cons (glcp-generic-geval x env)
                 (glcp-generic-geval-list y env)))
    :hints(("Goal" :in-theory (e/d (gl-cons) (glcp-generic-geval-alt-def
                                              glcp-generic-geval-general-concrete-obj-correct))
            :expand ((:with glcp-generic-geval (glcp-generic-geval x env))
                     (:with glcp-generic-geval (glcp-generic-geval (g-concrete
                                                                    x)
                                                                   env))))))


  (defthm len-of-glcp-generic-geval-list
    (equal (len (glcp-generic-geval-list x env))
           (len x))))
