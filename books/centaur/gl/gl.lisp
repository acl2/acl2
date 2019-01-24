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
(include-book "g-logapp")
(include-book "g-ash")
(include-book "g-binary-+")
(include-book "g-cons")
(include-book "g-equal")
(include-book "g-always-equal")
(include-book "g-integer-length")
(include-book "g-lessthan")
(include-book "g-logops")
(include-book "g-logbitp")
(include-book "g-unary--")
(include-book "g-hide")
(include-book "g-predicates")
(include-book "g-binary-mult")
(include-book "g-make-fast-alist")
(include-book "g-truncate")
(include-book "g-unary-concrete")
;; (include-book "g-coerce")
;; (include-book "g-code-char")
;; (include-book "g-intern")
;(include-book "centaur/aig/g-aig-eval" :dir :system)
;(include-book "g-make-fast-alist")

(include-book "gl-misc-defs")
(include-book "eval-f-i-cp")
(include-book "gl-generic-clause-proc")
(include-book "def-gl-clause-proc")
(include-book "gify-thms")
(include-book "auto-bindings")
(include-book "secondary-types")

;;; Matt K., 2/22/13: Sol Swords suggested commenting out the following
;;; include-book form, in order to avoid dependence on ttag :COUNT-BRANCHES-TO
;;; from centaur/aig/bddify.lisp.
; (include-book "bfr-aig-bddify")
(include-book "g-assert")
(include-book "g-concretize")

(include-book "def-gl-rule")

(include-book "doc")
(include-book "tutorial")

(local (include-book "general-object-thms"))
(local (include-book "eval-g-base-help"))

(local (in-theory (enable eval-g-base-non-cons)))
(local (in-theory (disable eval-g-base-alt-def
                           )))
(local (bfr-reasoning-mode t))

(defun mk-xes (n i)
  (declare (xargs :mode :program))
  (if (zp n)
      nil
    (cons (intern$ (str::cat "X" (str::natstr i)) "ACL2")
          (mk-xes (1- n) (1+ i)))))

(mutual-recursion
 (defun dumb-gify-body (x)
   (declare (xargs :mode :program))
   (cond ((atom x) `(mv ,x hyp))
         ((eq (car x) 'quote) `(mv ,x hyp))
         ((eq (car x) 'if)
          `(g-if ,(dumb-gify-body (second x))
                 ,(dumb-gify-body (third x))
                 ,(dumb-gify-body (fourth x))))
         ((consp (car x))
          (b* ((result-exprs (dumb-gify-body-lst (cdr x)))
               (vars (cadr (car x)))
               (body (caddr (car x))))
            `(b* ,(pairlis$
                   (pairlis$ (acl2::replicate (len vars) 'mv)
                             (pairlis$ vars
                                       (pairlis$ (acl2::replicate (len vars) 'hyp)
                                                 nil)))
                   (pairlis$ result-exprs nil))
               ,(dumb-gify-body body))))
         (t (b* ((result-exprs (dumb-gify-body-lst (cdr x)))
                 (vars (mk-xes (len (cdr x)) 0)))
              `(b* ,(pairlis$
                     (pairlis$ (acl2::replicate (len vars) 'mv)
                               (pairlis$ vars
                                         (pairlis$ (acl2::replicate (len vars) 'hyp)
                                                   nil)))
                     (pairlis$ result-exprs nil))
                 (glr ,(car x)
                      ,@vars
                       hyp clk config bvar-db state))))))
 (defun dumb-gify-body-lst (x)
   (if (atom x)
       nil
     (cons (dumb-gify-body (car x))
           (dumb-gify-body-lst (cdr x))))))



(defmacro def-g-simple (name body)
  `(progn (def-g-fn ,name ',(dumb-gify-body body))
          (verify-g-guards ,name)
          (def-gobj-dependency-thm ,name
            :hints`(("Goal" :in-theory (enable ,gfn))))
          (def-g-correct-thm ,name eval-g-base
            :hints`(("Goal" :in-theory (enable ,gfn))))))

;; complex-rationalp is an odd bird since it doesn't have a definition
;; (and hence is included in the list of primitives), but is provably
;; equivalent to (not (equal (imagpart x) 0)).
(def-g-simple complex-rationalp
  (equal 'nil (equal '0 (imagpart x))))

(def-g-simple acl2::bool-fix$inline (if x 't 'nil))

(def-g-simple implies (if (not p) 't (acl2::bool-fix$inline q)))

(def-g-simple eq (equal x y))

(def-g-simple eql (equal x y))

(def-g-simple = (equal x y))

(def-g-simple /= (not (equal x y)))

(def-g-simple null (equal x 'nil))

(def-g-simple atom (not (consp x)))

(def-g-simple endp (not (consp x)))

(def-g-simple zerop (equal x '0))

(def-g-simple plusp (< '0 x))

(def-g-simple minusp (< x '0))

(def-g-simple listp (if (consp x) 't (equal x 'nil)))

; Obsolete, now that prog2$ is defined in terms of return-last:
; (def-g-simple prog2$
;   'y)


(with-output
 :off (prove)
 (def-g-fn hons-assoc-equal
   `(if (zp clk)
        (gret (g-apply 'hons-assoc-equal (list acl2::key acl2::alist)))
      (g-if (glc atom acl2::alist)
            (gret nil)
            (b* (((gret car) (glc car acl2::alist)))
              (g-if (g-if (glc consp car)
                          (b* (((gret caar) (glc car car)))
                            (glc equal acl2::key caar))
                          (gret nil))
                    (gret car)
                    (b* ((clk (1- clk))
                         ((gret cdr) (glc cdr acl2::alist)))
                      (glc hons-assoc-equal acl2::key cdr))))))
   :measure (nfix clk)
   :hyp-hints `(("goal" :induct ,gcall
                 :expand ((:free (hyp) ,gcall))
                 :in-theory (disable (:d ,gfn))))))



(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

(with-output
 :off (prove event)
 (verify-g-guards hons-assoc-equal
                  :hints `(("Goal" :in-theory
                            (disable* ,gfn
                                      mv-nth-cons-meta
                                      set::double-containment
                                      equal-of-booleans-rewrite
                                      bfr-assume-correct
                                      (:rules-of-class :forward-chaining :here)
                                      (:rules-of-class :type-prescription
                                       :here))))))

(local (include-book "centaur/misc/beta-reduce-full" :dir :system))

;; Note: In the gobj dependency theorem for hons-assoc-equal, there are some
;; HIDEs in the induction hyp that need to match HIDEs created by the rewriter,
;; but they seem to sometimes differ in the order of the bindings.  So we beta
;; reduce all HIDE terms with the rule below.
(local (defthm beta-reduce-hides
         #!acl2 (implies (pseudo-termp x)
                         (equal (beta-eval x a)
                                (beta-eval (beta-reduce-full x) a)))
         :rule-classes ((:meta :trigger-fns (hide)))))

(def-gobj-dependency-thm hons-assoc-equal
  :hints `(("goal" :in-theory (e/d ((:i ,gfn))
                                   ((:d ,gfn)))
            :induct ,gcall
            :expand (,gcall))))

(def-g-correct-thm hons-assoc-equal eval-g-base
  :hints `(("goal" :in-theory (e/d ((:i ,gfn))
                                   ((:d ,gfn)))
            :induct ,gcall
            :expand (,gcall
                     (:free (a b) (eval-g-base-list (cons a b) env))
                     (eval-g-base-list nil env)
                     (hons-assoc-equal (eval-g-base acl2::key env)
                                       (eval-g-base acl2::alist env))))))

;; (make-g-world (hons-assoc-equal) geval-basis)



(defun canonical-general-concretep (x)
  (declare (xargs :guard t
                  :verify-guards nil))
  (or (and (concrete-gobjectp x)
           (not (g-keyword-symbolp x)))
      (and (consp x)
           (g-concrete-p x)
           (not (and (concrete-gobjectp (g-concrete->obj x))
                     (not (g-keyword-symbolp (g-concrete->obj x))))))))


(verify-guards canonical-general-concretep
  :hints(("Goal" :in-theory (enable concrete-gobjectp
                                    gobject-hierarchy-lite))))

(local
 (progn
   (defthmd same-g-concrete-p-implies-same
     (implies (and (g-concrete-p x)
                   (g-concrete-p y))
              (equal (equal (g-concrete->obj x)
                            (g-concrete->obj y))
                     (equal x y)))
     :hints(("Goal" :in-theory (enable g-concrete->obj))))

   (defthm generic-geval-of-g-concrete-p
     (implies (g-concrete-p x)
              (equal (generic-geval x env)
                     (g-concrete->obj x)))
     :hints(("Goal" :in-theory (enable generic-geval))))

   (defthmd canonical-eval-canonical-general-concretep
     (implies (and (canonical-general-concretep a)
                   (canonical-general-concretep b))
              (equal (equal (generic-geval a env1)
                            (generic-geval b env2))
                     (equal a b)))
     :hints(("Goal" :in-theory
             (enable same-g-concrete-p-implies-same
                     concrete-gobjectp-def
                     eval-concrete-gobjectp))))))

(defun hons-g-concrete (x)
  (declare (Xargs :guard t))
  (hons :g-concrete x))

(local
 (defthm hons-g-concrete-is-g-concrete
   (equal (hons-g-concrete x)
          (g-concrete x))
   :hints(("Goal" :in-theory (enable g-concrete)))))

(in-theory (disable hons-g-concrete))


(defun canonicalize-general-concrete (x)
  (declare (xargs :guard (general-concretep x)))
  (if (concrete-gobjectp x)
      (if (g-keyword-symbolp x)
          (hons-g-concrete x)
        x)
    (let ((obj (general-concrete-obj x)))
      (if (concrete-gobjectp obj)
          (if (g-keyword-symbolp obj)
              (hons-g-concrete obj)
            obj)
        (hons-g-concrete obj)))))

;; (local (defthm general-concrete-obj-of-car-when-tag
;;          (implies (and (syntaxp (quotep key))
;;                        (not (equal (tag x) :g-concrete))
;;                        (not (equal (tag x) :g-boolean))
;;                        (not (equal (tag x) :g-number))
;;                        (not (equal (tag x) :g-ite))
;;                        (not (equal (tag x) :g-apply))
;;                        (not (equal (tag x) :g-var))
;;                        (g-keyword-symbolp key))
;;                   (not (equal (general-concrete-obj (car x)) key)))
;;          :hints(("Goal" :in-theory (enable g-keyword-symbolp tag)
;;                  :expand ((general-concrete-obj (car x)))))))

;; (local (defthm gobj-depends-on-of-general-concrete-obj
;;          (implies (and (not (gobj-depends-on k p x))
;;                        (general-concretep x))
;;                   (not (gobj-depends-on k p (general-concrete-obj x))))
;;          :hints(("Goal" :in-theory (enable general-concretep
;;                                            general-concrete-obj
;;                                            concrete-gobjectp
;;                                            gobject-hierarchy-lite)
;;                  :induct t
;;                  :expand ((:free (a b)
;;                            (gobj-depends-on k p (cons a b))))))))


(defthm gobj-depends-on-of-canonicalize-general-concrete
  (implies (and (not (gobj-depends-on k p x))
                (general-concretep x))
           (not (gobj-depends-on k p (canonicalize-general-concrete x))))
  :hints(("Goal" :in-theory (enable canonicalize-general-concrete
                                    gobj-depends-on-when-concrete-gobjectp))))


(local
 (progn
   (defthm canonicalize-general-concretep-correct
     (implies (general-concretep x)
              (equal (generic-geval (canonicalize-general-concrete x)
                                    env)
                     (general-concrete-obj x)))
     :hints(("Goal" :in-theory (enable general-concrete-obj-correct
                                       concrete-gobjectp
                                       general-concrete-obj
                                       ;; eval-concrete-gobjectp
                                       )
             :use ((:instance eval-concrete-gobjectp
                              (x (general-concrete-obj x))))
             :expand
             ((:free (x) (general-concrete-obj (g-concrete x)))))))

   (defthm canonical-general-concretep-canonicalize
     (implies (general-concretep x)
              (canonical-general-concretep
               (canonicalize-general-concrete x))))))

(in-theory (disable canonicalize-general-concrete
                    canonical-general-concretep))

;; (defthm canonicalize-general-concrete-canonical
;;   (implies (and (general-concretep x)
;;                 (general-concretep y)
;;                 (equal (generic-geval x env1)
;;                        (generic-geval y env2)))
;;            (



(defun concrete-key-alistp (al)
  (declare (xargs :guard t :verify-guards nil))
  (or (atom al)
      (and (if (atom (car al))
               (not (g-keyword-symbolp (car al)))
             (canonical-general-concretep (caar al)))
           (concrete-key-alistp (cdr al)))))

(verify-guards concrete-key-alistp)

(memoize 'concrete-key-alistp :condition '(consp al))

(local
 (progn
   (in-theory (e/d (eval-g-base)))
   (eval-g-prove-f-i eval-g-base-f-i
                     eval-g-base generic-geval)

   (eval-g-functional-instance
    canonical-eval-canonical-general-concretep
    eval-g-base generic-geval)

   (eval-g-functional-instance
    canonicalize-general-concretep-correct
    eval-g-base generic-geval)

   (eval-g-functional-instance
    generic-geval-cons
    eval-g-base generic-geval)

   (eval-g-functional-instance
    general-concrete-obj-correct
    eval-g-base generic-geval)

   ;; (defthmd not-keyword-symbolp-car-impl
   ;;   (implies (not (g-keyword-symbolp (car x)))
   ;;            (and (not (g-concrete-p x))
   ;;                 (not (g-boolean-p x))
   ;;                 (not (g-number-p x))
   ;;                 (not (g-ite-p x))
   ;;                 (not (g-apply-p x))
   ;;                 (not (g-var-p x))))
   ;;   :hints(("Goal" :in-theory
   ;;           (enable* g-concrete-p g-boolean-p g-number-p
   ;;                    g-ite-p g-apply-p g-var-p
   ;;                    g-keyword-symbolp-def)))
   ;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

   (defthm ev-hons-assoc-equal-when-concrete-key-alistp
     (implies (and (concrete-key-alistp al)
                   (canonical-general-concretep key))
              (equal (eval-g-base
                      (hons-assoc-equal key al)
                      env)
                     (hons-assoc-equal (eval-g-base key env)
                                       (eval-g-base al env))))
     :hints (("goal" :in-theory
              (e/d (; gobjectp-car-impl-not-g-types
                    ; canonical-general-concretep-impl-gobjectp
                    gl-thm::canonical-eval-canonical-general-concretep-for-eval-g-base
                    ; not-keyword-symbolp-car-impl

                    hons-assoc-equal)
                   (canonical-general-concretep
                    general-concretep-def
                    concrete-gobjectp-def
                    eval-g-base
                    bfr-sat-bdd-unsat
                    (:d hons-assoc-equal)
                    ;; gl-thm::general-concrete-obj-correct-gobj-fix-for-eval-g-base
                    ))
              :induct (hons-assoc-equal key al)
              :expand ((:free (key) (hons-assoc-equal key al))))
             (and stable-under-simplificationp
                  '(:expand
                    ((:with eval-g-base (eval-g-base al env))
                     (:with eval-g-base (eval-g-base (car al) env))
                     (:free (key a b) (hons-assoc-equal key (cons a b))))
                    ;;                  :in-theory
                    ;;                  (enable tag g-concrete-p g-concrete->obj)
                    ))))))



;; Jared: changed variable names to match new hons
(def-g-fn hons-acons
  `(if (and (general-concretep acl2::key)
            (concrete-key-alistp acl2::alist))
       (mv (hons-acons (canonicalize-general-concrete acl2::key)
                       acl2::val acl2::alist)
           hyp)
     (b* (((gret pair) (glc cons acl2::key acl2::val)))
       (glc cons pair acl2::alist))))

(verify-g-guards hons-acons)

;; (def-gobjectp-thm hons-acons
;;   :hints `(("goal" :in-theory
;;             (enable canonical-general-concretep-impl-gobjectp))))
(local (defthm cons-of-canonicalize-general-concrete
         (equal (cons (canonicalize-general-concrete x) y)
                (gl-cons (canonicalize-general-concrete x) y))
         :hints(("Goal" :in-theory (enable gl-cons canonicalize-general-concrete)))))


;; (local (in-theory (enable generic-geval-g-concrete
;;                           general-concrete-obj-correct)))

;; (local (defthm general-concrete-obj-g-concrete
;;          (equal (general-concrete-obj (g-concrete x)) x)
;;          :hints(("Goal" :in-theory (enable general-concrete-obj)))))

;;(local (in-theory (enable canonical-general-concretep-impl-gobjectp)))

(def-gobj-dependency-thm hons-acons
  :hints `(("goal" :expand (,gcall))))

(def-g-correct-thm hons-acons eval-g-base
  :hints `(("goal" :expand (,gcall))))


;; Jared: changed hons-get-fn-do-hopy to hons-get for new hons
(def-g-fn hons-get
  `(if (and (general-concretep acl2::key)
            (concrete-key-alistp acl2::alist))
       (mv (hons-get (canonicalize-general-concrete acl2::key) acl2::alist)
           hyp)
     (glc hons-assoc-equal acl2::key acl2::alist)))

(verify-g-guards hons-get)

(def-gobj-dependency-thm hons-get
  :hints `(("Goal"
            :in-theory (e/d (,gfn)))))


(local
 (progn
   (eval-g-functional-instance
    canonicalize-general-concretep-correct
    eval-g-base generic-geval)

   (eval-g-functional-instance
    generic-geval-of-g-concrete-p
    eval-g-base generic-geval)

   (eval-g-functional-instance
    eval-concrete-gobjectp
    eval-g-base generic-geval)))

(def-g-correct-thm hons-get eval-g-base
  :hints`(("Goal" :in-theory (enable ,gfn))))


; Jared Note: removed hons-get-fn-do-not-hopy since it's no longer part
; of hons.  We can add it back if you want it.



;; ;; HONS-GET-FN-DO-NOT-HOPY is a dilemma since we're looking up the G-CONCRETE
;; ;; of the object, which itself is not a HONS.
;; (def-g-fn hons-get-fn-do-not-hopy
;;   `(if (and (general-concretep x)
;;             (concrete-key-alistp l))
;;        (hons-get-fn-do-hopy (canonicalize-general-concrete x)
;;                             l)
;;      (glc hons-assoc-equal x l)))

;; (def-gobjectp-thm hons-get-fn-do-not-hopy)
;; (verify-g-guards hons-get-fn-do-not-hopy)
;; (def-g-correct-thm hons-get-fn-do-not-hopy eval-g-base)

; Jared: changing flush-hons-get-hash-table-link to fast-alist-free

(def-g-fn fast-alist-free
  `(gret (fast-alist-free acl2::alist)))

(verify-g-guards fast-alist-free)
(def-gobj-dependency-thm fast-alist-free
  :hints `(("Goal" :in-theory (enable ,gfn))))
(def-g-correct-thm fast-alist-free eval-g-base
  :hints `(("Goal" :in-theory (enable ,gfn))))



(def-g-fn flush-hons-get-hash-table-link
  `(gret (flush-hons-get-hash-table-link acl2::alist)))

(verify-g-guards flush-hons-get-hash-table-link)
(def-gobj-dependency-thm flush-hons-get-hash-table-link
  :hints `(("Goal" :in-theory (enable ,gfn))))
(def-g-correct-thm flush-hons-get-hash-table-link eval-g-base
  :hints `(("Goal" :in-theory (enable ,gfn))))



(acl2::defevaluator-fast cl-ev cl-ev-lst ((if a b c)) :namedp t)

(defun dumb-clausify (x)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((atom x) (list (list x)))
        ((equal x ''t) nil)
        ((and (eq (car x) 'if)
              (equal (fourth x) ''nil))
         (append (dumb-clausify (second x))
                 (dumb-clausify (third x))))
        (t (list (list x)))))

(acl2::def-join-thms cl-ev)

(defthm dumb-clausify-correct
  (iff (cl-ev (conjoin-clauses (dumb-clausify x)) a)
       (cl-ev x a)))

(defun dumb-clausify-cp (x)
  (declare (xargs :guard (pseudo-term-listp x)))
  (if (or (atom x)
          (consp (cdr x)))
      (list x)
    (dumb-clausify (car x))))

(defthm dumb-clausify-cp-correct
  (implies (and (pseudo-term-listp x)
                (alistp a)
                (cl-ev (conjoin-clauses (dumb-clausify-cp x)) a))
           (cl-ev (disjoin x) a))
  :rule-classes :clause-processor)


(def-gl-clause-processor glcp :output nil)


(defsection gl-bdd-mode
  :parents (modes reference)
  :short "Use BDD-based symbolic simulation in GL."
  :long "<p>This macro produces an event which sets the GL reasoning mode to
use @(see acl2::ubdds).  This is the default form of GL symbolic
simulation.</p>"

  (defmacro gl-bdd-mode ()
    '(progn (acl2::defattach bfr-mode bfr-bdd)
            (acl2::defattach bfr-counterex-mode bfr-counterex-bdd)
            (acl2::defattach
             (bfr-sat bfr-sat-bdd)
             :hints (("goal" :in-theory '(bfr-sat-bdd-unsat))
                     (and stable-under-simplificationp
                          '(:in-theory (enable bfr-sat-bdd)))))
            (acl2::defattach (bfr-vacuity-check
                              bfr-sat)
              :hints (("goal" :use bfr-sat-unsat))))))

;; BDD mode is on by default -- the above defattaches are set up in bfr.lisp
;; and bfr-sat.lisp, respectively.
;; (gl-bdd-mode)

;; Fix for unsigned-byte-p's recursive definition in ihs books
(table acl2::structural-decomp-defs 'unsigned-byte-p 'unsigned-byte-p)




;; Utilities for debugging.
(defun evisc-symbolic-al (x)
  (if (atom x)
      nil
    (if (atom (car x))
        (cons (car x) (evisc-symbolic-al (cdr x)))
      (cons (cons (caar x)
                  (if (general-concretep (cdar x))
                      (general-concrete-obj (cdar x))
                    'acl2::???))
            (evisc-symbolic-al (cdr x))))))

(defmacro trace-gl-interp (&key show-values)
  (declare (xargs :guard (booleanp show-values)))
  `(make-event
    ;; This is pretty hideous.  We need two make-events.  The outer make-event
    ;; just gets the name of the latest interpreter from the world, and
    ;; constructs a trace$ command that has the name literally embedded in it.
    (let* ((fn          (latest-gl-interp))
           (show-values ',show-values)
           (trace-cmd
            `(trace$ (,fn
                      :entry ,(if show-values
                                  '(list (car acl2::arglist)
                                         (evisc-symbolic-al (cadr acl2::arglist)))
                                '(car acl2::arglist))
                      :exit ,(if show-values
                                 '(if (general-concretep (nth 0 acl2::values))
                                      (general-concrete-obj (nth 0 acl2::values))
                                    'acl2::???)
                               '(:fmt ""))))))
      ;; Now, if trace$ was an event, we could just use it as our expansion.
      ;; But it isn't, so instead we expand into an other make-event, where
      ;; we run the trace command and produce a silly value-triple.
      `(make-event
        (mv-let (erp val state)
          ,trace-cmd
          (declare (ignore erp val))
          (value '(value-triple ',fn)))))))

(defmacro break-on-g-apply ()
  "To undo breaking on g-apply, one can call ~c[(untrace$)]"
  `(trace$ (g-apply :entry (prog2$ (acl2::fmt-to-comment-window!
                                    "(g-apply ~x0 ~x1~%"
                                    `((#\0 . ,(car acl2::arglist))
                                      (#\1 . ,(cadr acl2::arglist)))
                                    0
                                    (acl2::evisc-tuple 3 6 nil nil)
                                    nil)
                                   (break$)))))




;; gl-set-allowed-accessors -- add a hook to add-term-bvar$c to complain if we
;; try to add a term that contains an IF or any functions outside of a
;; given set.

(mutual-recursion
 (defun gobj-check-accessors (x fnlist)
   (declare (xargs :guard (symbol-listp fnlist)))
   (if (atom x)
       t
     (case (tag x)
       (:g-boolean t)
       (:g-integer t)
       (:g-concrete t)
       (:g-ite nil)
       (:g-var t)
       (:g-apply (and (member (g-apply->fn x) fnlist)
                      (gobjlist-check-accessors (g-apply->args x) fnlist)))
       (otherwise (and (gobj-check-accessors (car x) fnlist)
                       (gobj-check-accessors (cdr x) fnlist))))))

 (defun gobjlist-check-accessors (x fnlist)
   (declare (xargs :guard (symbol-listp fnlist)))
   (or (atom x)
       (and (gobj-check-accessors (car x) fnlist)
            (gobjlist-check-accessors (cdr x) fnlist)))))

(defun check-bvar-term-accessors (x fnlist)
  (if (gobj-check-accessors x fnlist)
      nil
    (prog2$ (cw "Bad term in add-term-bvar: ~x0~%" (gobj-abstract-top x))
            (break$))))


(defmacro gl-set-allowed-accessors (fns)
  `(trace$ #!gl (add-term-bvar$c
                 :cond (check-bvar-term-accessors x ,fns))))
