 ; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "FGL")

(include-book "primitives")
(local (include-book "primitive-lemmas"))
(local (std::add-default-post-define-hook :fix))

(def-gl-formula-checks fast-alist-formula-checks
  (hons-get
   hons-assoc-equal
   hons-equal
   atom
   last
   hons-acons
   fast-alist-fork
   fast-alist-clean
   make-fast-alist))

(local (def-gl-formula-checks-lemmas fast-alist-formula-checks))

(defun formals-subsubsts (formals)
  (declare (xargs :mode :program))
  (if (atom formals)
      nil
    (cons (acl2::make-tmplsubst :atoms `((<formal> . ,(car formals))))
          (formals-subsubsts (cdr formals)))))

(defun def-formula-check-definition-thm-fn (name formula-check wrld)
  (declare (xargs :mode :program))
  (b* ((recursivep (fgetprop name 'recursivep nil wrld))
       (formals (formals name wrld)))
    (acl2::template-subst
     (if recursivep
         '(encapsulate nil
            (local (defthmd fgl-ev-of-<name>-lemma
                     (implies (and (<formula-check> state)
                                   (fgl-ev-meta-extract-global-facts))
                              (equal (fgl-ev '(<name> . <formals>)
                                             (list (:@proj <formals> (cons '<formal> <formal>))))
                                     (<name> . <formals>)))
                     :hints(("Goal" :in-theory (enable <name>)
                             :induct (<name> . <formals>))
                            '(:use ((:instance fgl-ev-meta-extract-formula
                                     (name '<name>)
                                     (a (list (:@proj <formals> (cons '<formal> <formal>))))
                                     (st state)))
                              :in-theory (enable fgl-ev-of-fncall-args)))))
            
            (defthm fgl-ev-of-<name>-when-<formula-check>
              (implies (and (<formula-check> state)
                            (fgl-ev-meta-extract-global-facts))
                       (equal (fgl-ev (list '<name> . <formals>) env)
                              (<name> (:@proj <formals>
                                       (fgl-ev <formal> env)))))
              :hints(("Goal" :use ((:instance fgl-ev-of-<name>-lemma
                                    (:@proj <formals> (<formal> (fgl-ev <formal> env)))))
                      :in-theory (enable fgl-ev-of-fncall-args)))))
       '(defthm fgl-ev-of-<name>-when-<formula-check>
          (implies (and (<formula-check> state)
                        (fgl-ev-meta-extract-global-facts))
                   (equal (fgl-ev (list '<name> . <formals>) env)
                          (<name> (:@proj <formals>
                                     (fgl-ev <formal> env)))))
          :hints(("Goal" :in-theory (enable fgl-ev-of-fncall-args)
                  :use ((:instance fgl-ev-meta-extract-formula
                         (name '<name>)
                         (a (list (:@proj <formals>
                                   (CONS '<formal> (FGL-EV <formal> env)))))
                         (st state)))))))
     :str-alist `(("<NAME>" . ,(symbol-name name))
                  ("<FORMULA-CHECK>" . ,(symbol-name formula-check)))
     :atom-alist `((<name> . ,name)
                   (<formula-check> . ,formula-check)
                   (<formals> . ,formals))
     :subsubsts `((<formals> . ,(formals-subsubsts formals)))
     :pkg-sym formula-check)))

(defmacro def-formula-check-definition-thm (name formula-check)
  `(make-event
    (def-formula-check-definition-thm-fn ',name ',formula-check (w state))))

(def-formula-check-definition-thm atom             fast-alist-formula-checks)
(def-formula-check-definition-thm hons-equal       fast-alist-formula-checks)
(def-formula-check-definition-thm hons-assoc-equal fast-alist-formula-checks)
(def-formula-check-definition-thm hons-get         fast-alist-formula-checks)
(def-formula-check-definition-thm hons-acons       fast-alist-formula-checks)
(def-formula-check-definition-thm fast-alist-fork  fast-alist-formula-checks)
(def-formula-check-definition-thm last             fast-alist-formula-checks)
(def-formula-check-definition-thm fast-alist-clean fast-alist-formula-checks)
(def-formula-check-definition-thm make-fast-alist  fast-alist-formula-checks)


(set-ignore-ok t)

(define gl-keyval-pair-p (x)
  (if (atom x)
      (eq x nil)
    (gl-object-p (cdr x)))
  ///
  (defthm gl-keyval-pair-of-lookup-in-gl-object-alist
    (implies (gl-object-alist-p x)
             (gl-keyval-pair-p (hons-assoc-equal k x)))))

(define fgl-keyval-pair-eval ((x gl-keyval-pair-p) env logicman)
  :verify-guards nil
  (if (atom x)
      nil
    (cons (car x) (fgl-object-eval (cdr x) env logicman)))
  ///
  (defthm lookup-in-fgl-object-alist-eval
    (equal (hons-assoc-equal k (fgl-object-alist-eval x env logicman))
           (fgl-keyval-pair-eval (hons-assoc-equal k x) env logicman))
    :hints(("Goal" :in-theory (enable fgl-object-alist-eval
                                      hons-assoc-equal)
            :induct (hons-assoc-equal k x)
            :expand ((fgl-object-alist-eval k x))))))

(define gl-keyval-pair-to-object ((x gl-keyval-pair-p))
  :guard-hints (("goal" :in-theory (enable gl-keyval-pair-p)))
  :returns (new-x gl-object-p
                  :hints (("goal" :expand ((:free (x y) (gl-object-p (cons x y)))
                                           (gl-object-p (car x)))
                           :in-theory (enable g-concrete g-map-tag-p))))
  (if (atom x)
      nil
    (mk-g-cons (g-concrete (car x))
               (gl-object-fix (cdr x))))
  ///
  ;; (local (defthm kind-of-cons-gl-object
  ;;          (implies (gl-object-p x)
  ;;                   (equal (gl-object-kind (cons x y)) :g-cons))
  ;;          :hints(("Goal" :in-theory (enable gl-object-kind gl-object-p)))))

  (defthm fgl-object-eval-of-gl-keyval-pair-to-object
    (equal (fgl-object-eval (gl-keyval-pair-to-object x) env logicman)
           (fgl-keyval-pair-eval x env logicman))
    :hints(("Goal" :in-theory (enable fgl-keyval-pair-eval
                                      ;; g-cons->car g-cons->cdr
                                      )
            :expand ((:free (x y) (fgl-object-eval (cons x y) env))))))

  (defthm gl-object-bfrlist-of-gl-keyval-pair-to-object
    (implies (not (member v (gl-object-alist-bfrlist x)))
             (not (member v (gl-object-bfrlist
                             (gl-keyval-pair-to-object
                              (hons-assoc-equal k x))))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

(local (defthm fgl-objectlist-eval-when-atom
         (implies (not (consp x))
                  (equal (fgl-objectlist-eval x env) nil))
         :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))))

(def-gl-primitive hons-get (key x)
  (b* (((when (gl-object-case x '(:g-integer :g-boolean)))
        (mv t nil interp-st))
       ((unless (gl-object-case key :g-concrete))
        (mv nil nil interp-st))
       (key (g-concrete->val key)))
    (gl-object-case x
      :g-map (mv t (gl-keyval-pair-to-object (hons-get key x.alist)) interp-st)
      :g-concrete (mv t (g-concrete (hons-get key x.val)) interp-st)
      :otherwise (mv nil nil interp-st)))
  :formula-check fast-alist-formula-checks)

(local (defthm fgl-object-alist-eval-of-atom
         (implies (not (consp x))
                  (equal (fgl-object-alist-eval x env) x))
         :hints(("Goal" :in-theory (enable fgl-object-alist-eval)))))

(def-gl-primitive hons-acons (key val x)
  (b* (((unless (gl-object-case key :g-concrete))
        (mv nil nil interp-st))
       (key (g-concrete->val key)))
    (gl-object-case x
      :g-map (mv t (g-map x.tag (hons-acons key val x.alist)) interp-st)
      :g-concrete (if (atom x.val)
                      (mv t (g-map '(:g-map) (hons-acons key val x.val)) interp-st)
                    (mv nil nil interp-st))
      :otherwise (mv nil nil interp-st)))
  :formula-check fast-alist-formula-checks)

(defthm gl-object-alist-bfrlist-of-fast-alist-fork
  (implies (and (not (member v (gl-object-alist-bfrlist x)))
                (not (member v (gl-object-alist-bfrlist y))))
           (not (member v (gl-object-alist-bfrlist (fast-alist-fork x y))))))

(defthm fgl-keyval-pair-eval-under-iff
  (iff (fgl-keyval-pair-eval x env logicman)
       (consp x))
  :hints(("Goal" :in-theory (enable fgl-keyval-pair-eval))))

(defthm fgl-object-alist-eval-of-fast-alist-fork
  (equal (fgl-object-alist-eval (fast-alist-fork x y) env)
         (fast-alist-fork (fgl-object-alist-eval x env)
                          (fgl-object-alist-eval y env)))
  :hints(("Goal" :in-theory (e/d (fast-alist-fork))
          :induct (fast-alist-fork x y)
          :expand ((fgl-object-alist-eval x env)
                   (:free (a b) (fgl-object-alist-eval (cons a b) env))))))

(def-gl-primitive fast-alist-fork (x y)
  (gl-object-case x
    :g-concrete (if (atom x.val)
                    (mv t y interp-st)
                  (mv nil nil interp-st))
    :g-boolean (mv t y interp-st)
    :g-integer (mv t y interp-st)
    :g-map (if (atom x.alist)
               (mv t y interp-st)
             (gl-object-case y
               :g-concrete (if (atom y.val)
                               (mv t (g-map x.tag (fast-alist-fork x.alist y.val)) interp-st)
                             (mv nil nil interp-st))
               :g-map (mv t (g-map y.tag (fast-alist-fork x.alist y.alist)) interp-st)
               :otherwise (mv nil nil interp-st)))
    :otherwise (mv nil nil interp-st))
  :formula-check fast-alist-formula-checks)


(encapsulate nil
  (local (defthm fgl-object-alist-eval-when-atom
           (implies (not (consp (fgl-object-alist-eval x env)))
                    (equal (fgl-object-alist-eval x env)
                           (if (atom x) x (cdr (last x)))))
           :hints(("Goal" :induct t :expand ((fgl-object-alist-eval x env))))))

  (local (defthm cdr-last-of-fgl-object-alist-eval
           (implies (consp (fgl-object-alist-eval x env))
                    (equal (cdr (last (fgl-object-alist-eval x env)))
                           (cdr (last x))))
           :hints(("Goal" :induct t
                   :expand ((fgl-object-alist-eval x env)))
                  (and stable-under-simplificationp
                       '(:expand ((fgl-object-alist-eval (cdr x) env)))))))

  (def-gl-primitive fast-alist-clean (x)
    (gl-object-case x
      :g-concrete (if (atom x.val)
                      (mv t x interp-st)
                    (mv nil nil interp-st))
      :g-map (mv t (g-map x.tag (fast-alist-clean x.alist)) interp-st)
      :g-integer (mv t x interp-st)
      :g-boolean (mv t x interp-st)
      :otherwise (mv nil nil interp-st))
    :formula-check fast-alist-formula-checks))

(define gl-make-fast-alist-concrete-rec (x)
  :returns (mv ok (new-x gl-object-alist-p))
  (if (atom x)
      (mv t x)
    (if (atom (car x))
        (mv nil nil)
      (b* (((mv ok rest) (gl-make-fast-alist-concrete-rec (cdr x))))
        (if ok
            (mv t (cons (cons (caar x) (g-concrete (cdar x))) rest))
          (mv nil nil)))))
  ///
  (defret fgl-object-alist-eval-of-<fn>
    (implies ok
             (equal (fgl-object-alist-eval new-x env) x)))

  (defret gl-object-alist-bfrlist-of-<fn>
    (equal (gl-object-alist-bfrlist new-x) nil)))
        

(define gl-make-fast-alist-rec ((x gl-object-p))
  :returns (mv ok (new-x gl-object-alist-p))
  :measure (gl-object-count x)
  (gl-object-case x
    :g-concrete (gl-make-fast-alist-concrete-rec x.val)
    :g-map (mv t x.alist)
    :g-cons (b* (((mv rest-ok rest) (gl-make-fast-alist-rec x.cdr))
                 ((unless rest-ok) (mv nil nil)))
              (gl-object-case x.car
                :g-concrete (if (consp x.car.val)
                                (mv t (cons (cons (car x.car.val) (g-concrete (cdr x.car.val))) rest))
                              (mv nil nil))
                :g-cons (gl-object-case x.car.car
                          :g-concrete (mv t (cons (cons x.car.car.val x.car.cdr)
                                                  rest))
                          :otherwise (mv nil nil))
                :otherwise (mv nil nil)))
    :otherwise (mv nil nil))
  ///
  (defret fgl-object-alist-eval-of-<fn>
    (implies ok
             (equal (fgl-object-alist-eval new-x env)
                    (fgl-object-eval x env))))

  (defret gl-object-alist-bfrlist-of-<fn>
    (implies (not (member v (gl-object-bfrlist x)))
             (not (member v (gl-object-alist-bfrlist new-x))))))

(def-gl-primitive make-fast-alist (x)
  (b* (((mv ok alist) (gl-make-fast-alist-rec x))
       ((when ok) (mv t (g-map '(:g-map) alist) interp-st)))
    (mv nil nil interp-st))
  :formula-check fast-alist-formula-checks)


(local (install-gl-primitives falprims))
