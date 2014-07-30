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
(include-book "ite-merge")
(include-book "gtests")
(local (include-book "gtype-thms"))

;; (defun def-g-identity-fn (name top-p)
;;   (b* (;; (gobjectp-thm (intern-in-package-of-symbol
;;        ;;                (concatenate 'string "GOBJECTP-" (symbol-name name))
;;        ;;                'gl::foo))
;;        (geval-thm (intern-in-package-of-symbol
;;                    (concatenate 'string "GEVAL-" (symbol-name name))
;;                    'gl::foo)))
;;     `(progn (defun-inline ,name (x)
;;               (declare (xargs :guard t))
;;               x)
;;             ;; (defthm ,gobjectp-thm
;;             ;;   (equal (gobjectp (,name x))
;;             ;;          ,(if top-p
;;             ;;               `(,name (gobjectp (hide (,name x))))
;;             ;;             '(gobjectp x)))
;;             ;;   :hints (("goal" :expand ((:free (x) (hide x))))))
;;             (defthm ,geval-thm
;;               (equal (generic-geval (,name x) env)
;;                      ,(if top-p
;;                           `(,name (generic-geval (hide (,name x)) env))
;;                         '(generic-geval x env)))
;;               :hints (("goal" :expand ((:free (x) (hide x))))))
;;             (in-theory (disable ,name (:t ,name)
;;                                 (,name))))))

;; (defmacro def-g-identity (name top-p)
;;   (def-g-identity-fn name top-p))


;; (def-g-identity g-if-marker t)
;; (def-g-identity g-or-marker t)
;; (def-g-identity g-test-marker nil)

;; (defun-inline g-hyp-marker (hyp)
;;   (declare (xargs :guard t
;;                   :stobjs hyp))
;;   hyp)

;; (defthm bfr-hyp-eval-g-hyp-marker
;;   (equal (bfr-hyp-eval (g-hyp-marker x) env)
;;          (bfr-hyp-eval x env)))

;; ;; (defthm pbfr-depends-on-of-g-hyp-marker
;; ;;   (equal (pbfr-depends-on n p (g-hyp-marker x))
;; ;;          (pbfr-depends-on n p x)))

;; (in-theory (disable g-hyp-marker (:t g-hyp-marker)
;;                     (g-hyp-marker)))

;; (defthm gtests-g-test-marker
;;   (equal (gtests (g-test-marker x) hyp) (gtests x hyp))
;;   :hints(("Goal" :in-theory (enable g-test-marker))))



(defmacro g-if-exec (test then else)
  `(b* (((mv test-res hyp) ,test)
        ((mv test-true test-unknown test-obj hyp) (gtests test-res hyp))
        ((mv contra1 hyp undo)
         (bfr-assume (bfr-or test-true test-unknown)
                     hyp))
        ((mv then-res hyp) (if contra1
                               (mv nil hyp)
                             ,then))
        (hyp (bfr-unassume hyp undo))
        ((mv contra0 hyp undo)
         (bfr-assume (bfr-or (bfr-not test-true) test-unknown)
                     hyp))
        ((mv else-res hyp) (if contra0
                               (mv nil hyp)
                             ,else))
        (hyp (bfr-unassume hyp undo))
        ((when contra1) (mv else-res hyp))
        ((when contra0) (mv then-res hyp))
        ((mv contra hyp undo) (bfr-assume (bfr-not test-unknown) hyp))
        ((when contra)
         (b* ((hyp (bfr-unassume hyp undo)))
           (mv (mk-g-ite test-obj then-res else-res) hyp)))
        ((mv merge hyp) (gobj-ite-merge test-true then-res else-res hyp))
        (hyp (bfr-unassume hyp undo)))
     (mv (mk-g-bdd-ite test-unknown
                       (mk-g-ite test-obj then-res else-res)
                       merge
                       hyp)
         hyp)))

(defmacro g-or-exec (test else)
  `(b* (((mv test-res hyp) ,test)
        ((mv test-true test-unknown test-obj hyp) (gtests test-res hyp))
        ((mv contra0 hyp undo)
         (bfr-assume (bfr-or (bfr-not test-true) test-unknown) hyp))
        ((mv else-res hyp) (if contra0
                               (mv nil hyp)
                             ,else))
        (hyp (bfr-unassume hyp undo))
        ((when contra0) (mv test-res hyp))
        ((mv contra hyp undo) (bfr-assume (bfr-not test-unknown) hyp))
        ((when contra)
         (b* ((hyp (bfr-unassume hyp undo)))
           (mv (mk-g-ite test-obj test-res else-res) hyp)))
        ((mv merge hyp) (gobj-ite-merge test-true test-res else-res hyp))
        (hyp (bfr-unassume hyp undo)))
     (mv (mk-g-bdd-ite test-unknown
                       (mk-g-ite test-obj test-res else-res)
                       merge
                       hyp)
         hyp)))


(define g-if-fn (test-res then-res else-res hyp)
  :non-executable t
  :verify-guards nil
  (b* ((hyp (bfr-hyp-fix hyp))
       ((mv test-true test-unknown ?test-obj hyp) (gtests test-res hyp))
       ((mv contra1 ?hyp1 ?undo)
        (bfr-assume (bfr-or test-true test-unknown)
                    hyp))
       ((mv contra0 ?hyp0 ?undo)
        (bfr-assume (bfr-or (bfr-not test-true) test-unknown)
                    hyp))
       ((when contra1) (mv (and (not contra0) else-res) hyp))
       ((when contra0) (mv then-res hyp))
       ((mv contra ?hypu ?undo) (bfr-assume (bfr-not test-unknown) hyp))
       ((when contra)
        (mv (mk-g-ite test-obj then-res else-res) hyp))
       ((mv merge ?hypu) (gobj-ite-merge test-true then-res else-res hypu)))
    (mv (mk-g-bdd-ite test-unknown
                      (mk-g-ite test-obj then-res else-res)
                      merge
                      hyp)
        hyp))
  ///

  (def-hyp-congruence g-if-fn :retval 1)

  (defthm g-if-fn-correct
    (implies (bfr-hyp-eval hyp (car env))
             (equal (generic-geval (mv-nth 0 (g-if-fn test then else hyp)) env)
                    (if (generic-geval test env)
                        (generic-geval then env)
                      (generic-geval else env)))))

  (defthm gobj-depends-on-of-g-if-fn
    (implies (and (not (gobj-depends-on k p test-res))
                  (not (gobj-depends-on k p then-res))
                  (not (gobj-depends-on k p else-res)))
             (not (gobj-depends-on k p (mv-nth 0 (g-if-fn test-res then-res else-res hyp)))))))

(define g-or-fn (test-res else-res hyp)
  :non-executable t
  :verify-guards nil
  (b* ((hyp (bfr-hyp-fix hyp))
       ((mv test-true test-unknown ?test-obj hyp) (gtests test-res hyp))
       ((mv contra0 ?hyp0 ?undo)
        (bfr-assume (bfr-or (bfr-not test-true) test-unknown)
                    hyp))
       ((when contra0) (mv test-res hyp))
       ((mv contra ?hypu ?undo) (bfr-assume (bfr-not test-unknown) hyp))
       ((when contra)
        (mv (mk-g-ite test-obj test-res else-res) hyp))
       ((mv merge ?hypu) (gobj-ite-merge test-true test-res else-res hypu)))
    (mv (mk-g-bdd-ite test-unknown
                      (mk-g-ite test-obj test-res else-res)
                      merge
                      hyp)
        hyp))
  ///

  (def-hyp-congruence g-or-fn :retval 1)

  (defthm g-or-fn-correct
    (implies (bfr-hyp-eval hyp (car env))
             (equal (generic-geval (mv-nth 0 (g-or-fn test else hyp)) env)
                    (or (generic-geval test env)
                        (generic-geval else env)))))

  (defthm gobj-depends-on-of-g-or-fn
    (implies (and (not (gobj-depends-on k p test-res))
                  (not (gobj-depends-on k p else-res)))
             (not (gobj-depends-on k p (mv-nth 0 (g-or-fn test-res else-res hyp)))))))



(defmacro g-if (test then else)
  `(non-exec
    (b* (((mv test-res hyp) ,test)
         ((mv test-true test-unknown ?test-obj hyp) (gtests test-res hyp))
         ((mv ?contra1 hyp1 ?undo)
          (bfr-assume (bfr-or test-true test-unknown)
                      hyp))
         ((mv then-res ?hyp1) (let ((hyp hyp1)) ,then))
         ((mv ?contra0 hyp0 ?undo)
          (bfr-assume (bfr-or (bfr-not test-true) test-unknown)
                      hyp))
         ((mv else-res ?hyp0) (let ((hyp hyp0)) ,else)))
      (g-if-fn test-res then-res else-res hyp))))




(defmacro g-or (test else)
  `(non-exec
    (b* (((mv test-res hyp) ,test)
         ((mv test-true test-unknown ?test-obj hyp) (gtests test-res hyp))
         ((mv ?contra0 hyp0 ?undo)
          (bfr-assume (bfr-or (bfr-not test-true) test-unknown)
                      hyp))
         ((mv else-res ?hyp0) (let ((hyp hyp0)) ,else)))
      (g-or-fn test-res else-res hyp))))

(defun body-replace-g-ifs (x)
  `(mbe :logic ,x
        :exec ,(sublis `((g-if . g-if-exec)
                         (g-or . g-or-exec))
                       x)))

(defmacro replace-g-ifs (x)
  (body-replace-g-ifs x))

(defmacro g-if-mbe (test then else)
  `(mbe :logic (g-if ,test ,then ,else)
        :exec (g-if-exec ,test ,then ,else)))

(defmacro g-or-mbe (test else)
  `(mbe :logic (g-or ,test ,else)
        :exec (g-or-exec ,test ,else)))

(defmacro gret (x)
  `(mv ,x hyp))

(acl2::def-b*-binder gret
  :body
  `(b* (((mv ,(car acl2::args) hyp) . ,acl2::forms))
     ,acl2::rest-expr))
