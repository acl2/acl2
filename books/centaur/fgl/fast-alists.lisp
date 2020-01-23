 ; FGL - A Symbolic Simulation Framework for ACL2
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
(local (in-theory (disable w)))

(def-formula-checks fast-alist-formula-checks
  (hons-get hons-acons fast-alist-fork fast-alist-clean make-fast-alist))

(set-ignore-ok t)

(define fgl-keyval-pair-p (x)
  (if (atom x)
      (eq x nil)
    (fgl-object-p (cdr x)))
  ///
  (defthm fgl-keyval-pair-of-lookup-in-fgl-object-alist
    (implies (fgl-object-alist-p x)
             (fgl-keyval-pair-p (hons-assoc-equal k x)))))

(define fgl-keyval-pair-eval ((x fgl-keyval-pair-p) env logicman)
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

(define fgl-keyval-pair-to-object ((x fgl-keyval-pair-p))
  :guard-hints (("goal" :in-theory (enable fgl-keyval-pair-p)))
  :returns (new-x fgl-object-p
                  :hints (("goal" :expand ((:free (x y) (fgl-object-p (cons x y)))
                                           (fgl-object-p (car x)))
                           :in-theory (enable g-concrete g-map-tag-p))))
  (if (atom x)
      nil
    (mk-g-cons (g-concrete (car x))
               (fgl-object-fix (cdr x))))
  ///
  ;; (local (defthm kind-of-cons-fgl-object
  ;;          (implies (fgl-object-p x)
  ;;                   (equal (fgl-object-kind (cons x y)) :g-cons))
  ;;          :hints(("Goal" :in-theory (enable fgl-object-kind fgl-object-p)))))

  (defthm fgl-object-eval-of-fgl-keyval-pair-to-object
    (equal (fgl-object-eval (fgl-keyval-pair-to-object x) env logicman)
           (fgl-keyval-pair-eval x env logicman))
    :hints(("Goal" :in-theory (enable fgl-keyval-pair-eval
                                      ;; g-cons->car g-cons->cdr
                                      )
            :expand ((:free (x y) (fgl-object-eval (cons x y) env))))))

  (defthm fgl-object-bfrlist-of-fgl-keyval-pair-to-object
    (implies (not (member v (fgl-object-alist-bfrlist x)))
             (not (member v (fgl-object-bfrlist
                             (fgl-keyval-pair-to-object
                              (hons-assoc-equal k x))))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal)))))


(def-fgl-primitive hons-get (key x)
  (b* (((when (fgl-object-case x '(:g-integer :g-boolean)))
        (mv t nil interp-st))
       ((unless (fgl-object-case key :g-concrete))
        (mv nil nil interp-st))
       (key (g-concrete->val key)))
    (fgl-object-case x
      :g-map (mv t (fgl-keyval-pair-to-object (hons-get key x.alist)) interp-st)
      :g-concrete (mv t (g-concrete (hons-get key x.val)) interp-st)
      :otherwise (mv nil nil interp-st)))
  :formula-check fast-alist-formula-checks)

(local (defthm fgl-object-alist-eval-of-atom
         (implies (not (consp x))
                  (equal (fgl-object-alist-eval x env) x))
         :hints(("Goal" :in-theory (enable fgl-object-alist-eval)))))

(def-fgl-primitive hons-acons (key val x)
  (b* (((unless (fgl-object-case key :g-concrete))
        (mv nil nil interp-st))
       (key (g-concrete->val key)))
    (fgl-object-case x
      :g-map (mv t (g-map x.tag (hons-acons key val x.alist)) interp-st)
      :g-concrete (if (atom x.val)
                      (mv t (g-map '(:g-map) (hons-acons key val x.val)) interp-st)
                    (mv nil nil interp-st))
      :otherwise (mv nil nil interp-st)))
  :formula-check fast-alist-formula-checks)

(defthm fgl-object-alist-bfrlist-of-fast-alist-fork
  (implies (and (not (member v (fgl-object-alist-bfrlist x)))
                (not (member v (fgl-object-alist-bfrlist y))))
           (not (member v (fgl-object-alist-bfrlist (fast-alist-fork x y))))))

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

(def-fgl-primitive fast-alist-fork (x y)
  (fgl-object-case x
    :g-concrete (if (atom x.val)
                    (mv t y interp-st)
                  (mv nil nil interp-st))
    :g-boolean (mv t y interp-st)
    :g-integer (mv t y interp-st)
    :g-map (if (atom x.alist)
               (mv t y interp-st)
             (fgl-object-case y
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

  (def-fgl-primitive fast-alist-clean (x)
    (fgl-object-case x
      :g-concrete (if (atom x.val)
                      (mv t x interp-st)
                    (mv nil nil interp-st))
      :g-map (mv t (g-map x.tag (fast-alist-clean x.alist)) interp-st)
      :g-integer (mv t x interp-st)
      :g-boolean (mv t x interp-st)
      :otherwise (mv nil nil interp-st))
    :formula-check fast-alist-formula-checks))

(define fgl-make-fast-alist-concrete-rec (x)
  :returns (mv ok (new-x fgl-object-alist-p))
  (if (atom x)
      (mv t x)
    (if (atom (car x))
        (mv nil nil)
      (b* (((mv ok rest) (fgl-make-fast-alist-concrete-rec (cdr x))))
        (if ok
            (mv t (cons (cons (caar x) (g-concrete (cdar x))) rest))
          (mv nil nil)))))
  ///
  (defret fgl-object-alist-eval-of-<fn>
    (implies ok
             (equal (fgl-object-alist-eval new-x env) x)))

  (defret fgl-object-alist-bfrlist-of-<fn>
    (equal (fgl-object-alist-bfrlist new-x) nil)))
        

(define fgl-make-fast-alist-rec ((x fgl-object-p))
  :returns (mv ok (new-x fgl-object-alist-p))
  :measure (fgl-object-count x)
  (fgl-object-case x
    :g-concrete (fgl-make-fast-alist-concrete-rec x.val)
    :g-map (mv t x.alist)
    :g-cons (b* (((mv rest-ok rest) (fgl-make-fast-alist-rec x.cdr))
                 ((unless rest-ok) (mv nil nil)))
              (fgl-object-case x.car
                :g-concrete (if (consp x.car.val)
                                (mv t (cons (cons (car x.car.val) (g-concrete (cdr x.car.val))) rest))
                              (mv nil nil))
                :g-cons (fgl-object-case x.car.car
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

  (defret fgl-object-alist-bfrlist-of-<fn>
    (implies (not (member v (fgl-object-bfrlist x)))
             (not (member v (fgl-object-alist-bfrlist new-x))))))

(def-fgl-primitive make-fast-alist (x)
  (b* (((mv ok alist) (fgl-make-fast-alist-rec x))
       ((when ok) (mv t (g-map '(:g-map) (make-fast-alist alist)) interp-st)))
    (mv nil nil interp-st))
  :formula-check fast-alist-formula-checks)


(local (install-fgl-metafns falprims))



(defxdoc fgl-fast-alist-support
  :parents (fgl)
  :short "Support for hash-based fast alists in FGL"
  :long "<p> FGL supports the use of fast alist primitives (see @(see
acl2::fast-alists)) in its rewriter.  However, for accesses and updates to be
fast, the user must ensure the following conditions are met:</p>

<ul>

<li>The keys of the alist are always concrete values.  (The values need not be
concrete.)</li>

<li>The alist must only be used in a single-threaded, imperative-style manner,
just as with ACL2 fast alists.  For example, the following usage will cause a
slow lookup to occur:</li>

@({
 (let* ((al1 (hons-acons 'a 'aa nil))
        (al2 (hons-acons 'b 'bb al1)))
     (hons-get 'a al1))
 })

<li>The alist must not be modified within an @('if') branch and then accessed
outside that branch, unless care is taken to arrange the branch merging such
that the keys of the alist remain concrete.</li>

</ul>

<p>For another approach to fast lookups in alists, see @(see fgl-array-support).</p>"
  )

