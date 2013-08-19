

(in-package "GL")


(include-book "g-logapp")
(include-book "g-ash")
(include-book "g-binary-+")
(include-book "g-cons")
(include-book "g-equal")
(include-book "g-always-equal")
(include-book "g-integer-length")
(include-book "g-lessthan")
(include-book "g-logand")
(include-book "g-logior")
(include-book "g-lognot")
(include-book "g-logbitp")
(include-book "g-unary--")
(include-book "g-hide")
(include-book "g-predicates")
(include-book "g-binary-mult")
(include-book "g-floor")
(include-book "g-make-fast-alist")
(include-book "g-mod")
(include-book "g-truncate")
(include-book "g-rem")
(include-book "g-unary-concrete")
(include-book "g-coerce")
(include-book "g-code-char")
(include-book "g-intern")
;(include-book "centaur/aig/g-aig-eval" :dir :system)
;(include-book "g-make-fast-alist")
;(include-book "g-gl-mbe")

(include-book "gl-misc-defs")
(include-book "eval-f-i-cp")
(include-book "gl-generic-clause-proc")
(include-book "def-gl-clause-proc")
(include-book "gify-thms")
(include-book "gl-misc-doc")
(include-book "auto-bindings")
;;; Matt K., 2/22/13: Sol Swords suggested commenting out the following
;;; include-book form, in order to avoid dependence on ttag :COUNT-BRANCHES-TO
;;; from centaur/aig/bddify.lisp.
; (include-book "bfr-aig-bddify")
(include-book "g-gl-mbe")

(local (include-book "general-object-thms"))
(local (include-book "eval-g-base-help"))

(local (in-theory (enable eval-g-base-non-cons)))
(local (in-theory (disable eval-g-base-alt-def
                           )))
(local (bfr-reasoning-mode t))
(defmacro def-g-simple (name body)
  `(progn (def-g-fn ,name ,body)
          (verify-g-guards ,name)
          (def-gobj-dependency-thm ,name)
          (def-g-correct-thm ,name eval-g-base)))

;; complex-rationalp is an odd bird since it doesn't have a definition
;; (and hence is included in the list of primitives), but is provably
;; equivalent to (not (equal (imagpart x) 0)).
(def-g-simple complex-rationalp
  `(glr equal
        nil
        (glr equal 0 (glr imagpart x hyp clk config bvar-db state) hyp clk config bvar-db state)
        hyp clk config bvar-db state))


(def-g-simple acl2::boolfix
  `(g-if x t nil))

(def-g-simple implies
  `(g-or (glr not p hyp clk config bvar-db state)
         (glr acl2::boolfix q hyp clk config bvar-db state)))

(def-g-simple eq
  `(glr equal x y hyp clk config bvar-db state))

(def-g-simple eql
  `(glr equal x y hyp clk config bvar-db state))

(def-g-simple =
  `(glr equal x y hyp clk config bvar-db state))

(def-g-simple /=
`(glr not (glr equal x y hyp clk config bvar-db state) hyp clk config bvar-db state))

(def-g-simple null
  `(glr equal x nil hyp clk config bvar-db state))

(def-g-simple atom
  `(glr not (glr consp x hyp clk config bvar-db state) hyp clk config bvar-db state))

(def-g-simple endp
  `(glr not (glr consp x hyp clk config bvar-db state) hyp clk config bvar-db state))

(def-g-simple zerop
  `(glr equal x 0 hyp clk config bvar-db state))

(def-g-simple plusp
  `(glr < 0 x hyp clk config bvar-db state))

(def-g-simple minusp
  `(glr < x 0 hyp clk config bvar-db state))

(def-g-simple listp
  `(g-or (glr consp x hyp clk config bvar-db state)
         (glr equal x nil hyp clk config bvar-db state)))

; Obsolete, now that prog2$ is defined in terms of return-last:
; (def-g-simple prog2$
;   'y)


(def-g-fn hons-assoc-equal
  `(if (zp clk)
       (g-apply 'hons-assoc-equal (list acl2::key acl2::alist))
     (g-if (glc atom acl2::alist)
           nil
           (let ((car (glc car acl2::alist)))
             (g-if (g-if (glc consp car)
                         (glc equal acl2::key (glc car car))
                         nil)
                 car
                 (let ((clk (1- clk)))
                   (glc hons-assoc-equal acl2::key (glc cdr acl2::alist)))))))
  :measure (nfix clk))

(verify-g-guards hons-assoc-equal)

(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

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
       (hons-acons (canonicalize-general-concrete acl2::key)
                   acl2::val acl2::alist)
     (glc cons (glc cons acl2::key acl2::val) acl2::alist)))

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

(def-gobj-dependency-thm hons-acons)

(def-g-correct-thm hons-acons eval-g-base)


;; Jared: changed hons-get-fn-do-hopy to hons-get for new hons
(def-g-fn hons-get
  `(if (and (general-concretep acl2::key)
            (concrete-key-alistp acl2::alist))
       (hons-get (canonicalize-general-concrete acl2::key) acl2::alist)
     (glc hons-assoc-equal acl2::key acl2::alist)))

(verify-g-guards hons-get)

(def-gobj-dependency-thm hons-get)


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

(def-g-correct-thm hons-get eval-g-base)


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
  `(fast-alist-free acl2::alist))

(verify-g-guards fast-alist-free)
(def-gobj-dependency-thm fast-alist-free)
(def-g-correct-thm fast-alist-free eval-g-base)



(def-g-fn flush-hons-get-hash-table-link
  `(flush-hons-get-hash-table-link acl2::alist))

(verify-g-guards flush-hons-get-hash-table-link)
(def-gobj-dependency-thm flush-hons-get-hash-table-link)
(def-g-correct-thm flush-hons-get-hash-table-link eval-g-base)



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
use @(see ubdd)s.  This is the default, relatively stable form of GL symbolic
simulation.</p>"

  (defmacro gl-bdd-mode ()
    '(progn (acl2::defattach bfr-mode bfr-bdd)
            (acl2::defattach bfr-counterex-mode bfr-counterex-bdd)
            (acl2::defattach
             (bfr-sat bfr-sat-bdd)
             :hints (("goal" :in-theory '(bfr-sat-bdd-unsat))
                     (and stable-under-simplificationp
                          '(:in-theory (enable bfr-sat-bdd))))))))

;; Default to BDD mode.
(gl-bdd-mode)





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
                                 '(if (general-concretep (nth 2 acl2::values))
                                      (general-concrete-obj (nth 2 acl2::values))
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
  `(trace$ (g-apply :entry (prog2$ (acl2::fmt-to-comment-window!
                                    "(g-apply ~x0 ~x1~%"
                                    `((#\0 . ,(car acl2::arglist))
                                      (#\1 . ,(cadr acl2::arglist)))
                                    0
                                    (acl2::evisc-tuple 3 6 nil nil))
                                   (break$)))))


(defsection gl
  :parents (acl2::proof-automation acl2::hardware-verification)
  :short "A symbolic simulation framework for bit-blasting ACL2 theorems."

  :long "<h3>Introduction</h3>

<p><b>GL</b> is a framework for proving <i>finite</i> ACL2 theorems&mdash;those
which, at least in principle, could be established by exhaustive
testing&mdash;by bit-blasting with a <a
href='http://en.wikipedia.org/wiki/Binary_decision_diagram'>Binary Decision
Diagram</a> (BDD) package or a <a
href='http://en.wikipedia.org/wiki/Boolean_satisfiability_problem'>SAT
solver</a>.</p>

<p>These approaches have much higher capacity than exhaustive testing, and when
they can be used, there are good reasons to prefer them over @(see
acl2::the-method) of traditional, interactive theorem proving.  For instance,
these tools can:</p>

<ul>

<li>Reduce the level of human understanding needed in the initial process of
developing the proof;</li>

<li>Provide clear counterexamples, whereas failed ACL2 proofs can often be
difficult to debug; and</li>

<li>Ease the maintenance of the proof, since after the design changes they can
often find updated proofs without help.</li>

</ul>")



(defsection other-resources
  :parents (gl)
  :short "Additional resources (talks, academic papers, a dissertation) for
learning about GL."

  :long "<p>Besides this @(see xdoc::xdoc) documentation, most GL users will
probably want to be aware of at least the following resources:</p>

<dl>

<dt>Sol Swords and Jared Davis.  <a
href='http://dx.doi.org/10.4204/EPTCS.70.7'>Bit-Blasting ACL2 Theorems</a>.
In ACL2 Workshop 2011.  November, 2011.  EPTCS 70.  Pages 84-102.</dt>

<dd>This is an approachable, user-focused introduction to GL as of 2011, which
also contains many pointers to related work.  It's probably a good idea to read
this first, noting that a few details have changed.  Much of this paper has now
been incorporated into this @(see xdoc::xdoc) documentation.</dd>

<dt>Sol Swords.  <a
href='http://repositories.lib.utexas.edu/handle/2152/ETD-UT-2010-12-2210'>A
Verified Framework for Symbolic Execution in the ACL2 Theorem Prover</a>.
Ph.D. thesis, University of Texas at Austin.  December, 2010.</dt>

<dd>This is the most comprehensive guide to GL's internals.  It covers tricky
topics like the handling of <i>if</i> statements and the details of BDD
parametrization.  It also covers the logical foundations of GL, such as
correctness claims for symbolic counterparts, the introduction of symbolic
interpreters, and the definition and verification of the GL clause processor.
Some topics are now somewhat dated, but it is good general background for
anyone who wants to extend GL.</dd>

<dt>The documentation for @(see acl2::hons-and-memoization).</dt>

<dd>GL makes heavy use of the ACL2(h) extension for hash consing and
memoization.  GL users will likely want to be aware of the basics of ACL2(h),
and of commands like @(see hons-summary), @(see hons-wash), and @(see
acl2::set-max-mem).</dd>

</dl>


<h4>Back-end Solvers</h4>

<dl>

<dt>Jared Davis and Sol Swords.  <a
href='http://dx.doi.org/10.4204/EPTCS.114.8'>Verified AIG Algorithms in
ACL2.</a> In ACL2 Workshop 2013. May, 2013. EPTCS 114.  Pages 95-110.</dt>
<dd>This is a more recent paper that's not especially focused on GL, but which
covers @(see aignet::aignet) and @(see satlink::satlink), which can be used by
GL in its new @(see gl-satlink-mode).  Many problems that are difficult to
solve using @(see acl2::ubdds) can be solved using @(see
satlink::satlink).</dd>

<dt>Sol Swords and Warren A Hunt, Jr.  <a
href='http://dx.doi.org/10.1007/978-3-642-14052-5_30'>A Mechanically Verified
AIG to BDD Conversion Algorithm</a>.  In ITP 2010, LNCS 6172, Springer.  Pages
435-449.</dt>
<dd>This is an older paper about the details of the @('bddify') algorithm that
is used as the engine for @(see gl-aig-bddify-mode).</dd>

</dl>

<h4>GL Applications</h4>

<p>GL has been used at <a href='http://www.centtech.com/'>Centaur
Technology</a> to verify RTL implementations of floating-point addition,
multiplication, and conversion operations, as well as hundreds of bitwise and
arithmetic operations on scalar and packed integers.  Some papers describing
some of this work include:</p>

<ul>

<li>Anna Slobodova, Jared Davis, Sol Swords, and Warren A. Hunt, Jr.  <a
href='http://dx.doi.org/10.1109/MEMCOD.2011.5970515'>A Flexible Formal
Verification Framework for Industrial Scale Validation</a>.  In Memocode 2011,
IEEE.  Pages 89-97.</li>

<li>Warren A. Hunt, Jr., Sol Swords, Jared Davis, and Anna Slobodova.  <i>Use
of Formal Verification at Centaur Technology</i>.  In David Hardin, editor, <a
href='http://dl.acm.org/citation.cfm?id=1841184'>Design and Verification of
Microprocessor Systems for High-Assurance Applications</a>, Pages 65-88.
Springer, 2010.</li>

</ul>

<h4>History</h4>

<p>GL is the successor of Boyer and Hunt's <b>G</b> system, the best
description of which may be found in:</p>

<ul>
<li>Robert S. Boyer and Warren A. Hunt, Jr.  <a
href='http://dx.doi.org/10.1145/1637837.1637840'>Symbolic Simulation in
ACL2</a>.  In ACL2 Workshop 2009, ACM, 2009.  Pages 20-24.</li>
</ul>

<p>The name, GL, its name stands for <i>G in the Logic</i>.  The G system was
written as a raw Lisp extension of the ACL2 kernel, so using it meant trusting
this additional code.  In contrast, GL is implemented as ACL2 books and its
proof procedure is formally verified by ACL2, so the only code we have to trust
besides ACL2 is the ACL2(h) extension that provides @(see
acl2::hons-and-memoization).</p>")


(defsection introduction
  :parents (gl)
  :short "A brief, intuitive explanation of how GL works."

  :long "<p>How does GL work?  You can probably imagine writing a bit-based
encoding of ACL2 objects.  For instance, you might represent an integer with
some structure that contains a 2's-complement list of bits.</p>

<p>GL uses an encoding like this, except that Boolean expressions take the
place of the bits.  We call these structures @(see symbolic-objects).</p>

<p>GL provides a way to effectively compute with symbolic objects; e.g., it can
\"add\" two integers whose bits are expressions, producing a new symbolic
object that represents their sum.  GL can perform similar computations for most
ACL2 primitives.  Building on this capability, it can <b>symbolically
execute</b> terms. The result of a symbolic execution is a new symbolic object
that captures all the possible values the result could take.</p>

<p>Symbolic execution can be used as a <b>proof procedure</b>.  To prove a
theorem, we first symbolically execute its goal formula, then show the
resulting symbolic object cannot represent @('nil').  GL provides a @(see
def-gl-thm) command that makes it easy to prove theorems with this approach.
It handles all the details of working with symbolic objects, and only needs to
be told how to represent the variables in the formula.</p>

<p>Like any automatic procedure, GL has a certain capacity.  But when these
limits are reached, you may be able to increase its capacity by:</p>

<ul>

<li>Optimizing its symbolic execution strategy to use more efficient
definitions (Section \ref{sec:optimization}),</li>

<li>Decomposing difficult problems into easier subgoals using @(see
def-gl-param-thm).</li>

<li>Using a SAT backend (Section \ref{sec:aig-mode}) that outperforms BDDs
on some problems.</li>

</ul>

<p>There are also some good tools and techniques for debugging failed
proofs (Section \ref{sec:debugging}).</p>")



(defxdoc modes
  :parents (gl)
  :short "Documentation about GL modes.  BOZO write something nicer here."
  :long "<p>BOZO and here too.</p>")


(defxdoc reference
  :parents (gl)
  :short "Reference documentation for using GL.")


(defxdoc debugging
  :parents (gl)
  :short "How to debug failed GL proofs.")


(defxdoc optimization
  :parents (gl)
  :short "How to optimize GL's symbolic simulations for faster or
larger-scale proofs.")





(defsection example-1-fast-logcount
  :parents (introduction)
  :short "Basic example of using GL to prove the correctness of a fast
bit-counting routine for 32-bit integers."

  :long "<p>Let's use GL to prove a theorem.  The following C code, from Sean
Anderson <a href='http://graphics.stanford.edu/~seander/bithacks.html'>Bit
Twiddling Hacks</a> page, is a fast way to count how many bits are set in a
32-bit integer.</p>

@({
 v = v - ((v >> 1) & 0x55555555);
 v = (v & 0x33333333) + ((v >> 2) & 0x33333333);
 c = ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;
})

<p>We can model this in ACL2 as follows.  It turns out that using
arbitrary-precision addition and subtraction does not affect the result, but we
must take care to use a 32-bit multiply to match the C code.</p>

<p>BOZO TURN THIS INTO AN EXAMPLE FILE AND USE @@DEF...</p>

@({
 (defun 32* (x y)}
   (logand (* x y) (1- (expt 2 32))))

 (defun fast-logcount-32 (v)
   (let* ((v (- v (logand (ash v -1) #x55555555)))
          (v (+ (logand v #x33333333) (logand (ash v -2) #x33333333))))
     (ash (32* (logand (+ v (ash v -4)) #xF0F0F0F) #x1010101) -24)))
})

<p>We can then use GL to prove @('fast-logcount-32') computes the same
result as ACL2's built-in @('logcount') function for all unsigned 32-bit
inputs.</p>

<p>BOZO USE @@DEF, maybe auto-bindings?</p>

@({
 (def-gl-thm fast-logcount-32-correct
   :hyp   (unsigned-byte-p 32 x)
   :concl (equal (fast-logcount-32 x)
                 (logcount x))
   :g-bindings `((x ,(g-int 0 1 33))))
})

<p>The @(':g-bindings') form is the only help GL needs from the user.  It tells
GL how to construct a symbolic object that can represent every value for @('x')
that satisfies the hypothesis (we explain what it means in later sections).  No
arithmetic books or lemmas are required&mdash;we actually don't even know why
this algorithm works.  The proof completes in 0.09 seconds and results in the
following ACL2 theorem.</p>

@({
 (defthm fast-logcount-32-correct
   (implies (unsigned-byte-p 32 x)
            (equal (fast-logcount-32 x)
                   (logcount x)))
   :hints ((gl-hint ...)))
})

<h3>Comparison with Exhausive Testing</h3>

<p>Why not just use exhaustive testing?  We wrote a fixnum-optimized
exhaustive-testing function that can cover the @('2^32') cases in 143 seconds.
This is slower than GL but still seems reasonable.</p>

<p>On the other hand, exhaustive testing is clearly incapable of scaling to the
64-bit and 128-bit versions of this algorithm, whereas GL completes the proofs
in 0.18 and 0.58 seconds, respectively.</p>

<p>Like exhaustive testing, GL can generate counterexamples to non-theorems.
At first, we didn't realize we needed to use a 32-bit multiply in
@('fast-logcount-32'), and we just used an arbitrary-precision multiply
instead.  The function still worked for test cases like @('0'), @('1')
@('#b111'), and @('#b10111'), but when we tried to prove its correctness, GL
showed us three counterexamples: @('#x80000000'), @('#xFFFFFFFF'), and
@('#x9448C263').  By default, GL generates a first counterexample by setting
bits to 0 wherever possible, a second by setting bits to 1, and a third with
random bit settings.</p>")


(defsection example-2-utf8-decoding
  :parents (introduction)
  :short "Basic example of using GL to prove an inversion property about UTF-8
processing functions."

  :long "<p>In <a href='http://dx.doi.org/10.1145/1217975.1218000'>Reasoning
about File Input in ACL2</a>, Davis used exhaustive testing to prove some
lemmas toward the correctness of UTF-8 processing functions.</p>

<p>The most difficult proof carried out this way was a well-formedness and
inversion property for four-byte UTF-8 sequences, which involved checking
@('2^32') cases.  To see the original proof, look for
@('lemma5-for-utf8-combine4-guard') in:</p>

@({ books/unicode/utf8-decode.lisp })

<p>The original (exhaustive testing) proof takes 67 seconds on our computer.
It involves four testing functions and five lemmas about them; all of this is
straightforward but mundane.  The testing functions are guard-verified and
optimized with @(see mbe) and type declarations for better performance.</p>

<p>We used GL to prove the same property.  The proof completes in 0.17 seconds
and requires no testing functions or supporting lemmas.</p>

@({
   (def-gl-thm lemma-5-by-gl
     :hyp (utf8-combine4-guard x1 x2 x3 x4)
     :concl
     (and
      (uchar? (utf8-combine4 x1 x2 x3 x4))
      (utf8-table35-ok? (utf8-combine4 x1 x2 x3 x4)
                        (list x1 x2 x3 x4))
      (utf8-table36-ok? (utf8-combine4 x1 x2 x3 x4)
                        (list x1 x2 x3 x4))
      (equal (uchar=>utf8 (utf8-combine4 x1 x2 x3 x4))
             (list x1 x2 x3 x4)))
     :rule-classes nil
     :g-bindings `((x1 ,(g-int 0 1 9))
                   (x2 ,(g-int 9 1 9))
                   (x3 ,(g-int 18 1 9))
                   (x4 ,(g-int 27 1 9))))
})")

(defxdoc term-level-reasoning
  :parents (gl optimization)
  :short "GL's term-level proof support"
  :long

  "<p>The traditional way of using GL to prove a theorem is to give a bit-level
description of each variable of the theorem as a shape spec in the :g-bindings
argument of def-gl-thm -- X is a 10-bit integer, Y is a three-entry Boolean
list, etc.  In this mode of operation, the goal is for every function to be
able to symbolically execute and produce a purely bit-level symbolic object as
its output.</p>

<p>This style of reasoning is somewhat restrictive.  ACL2 code is often
written in a way that makes this sort of symbolic execution expensive.  For
example, suppose we want a structure that maps integer keys to values.  For
best execution speed, we might represent this as a stobj array.  For best
ease of reasoning, we might represent it as a record (as in
books/misc/records.lisp), since these have nice, intuitive, hypothesis-free
rules about them.  For symbolic execution performance, on the other hand,
we might decide that a simple alist is the best representation.  But if we've
written the code in one of the other styles, then we'd like to be able to
escape the suboptimal symbolic execution this entails.</p>

<p>We have added features to GL which provide a way around these problems by
allowing for term-level reasoning as well as bit-level:</p>


<ul>

<li>rewrite rules, conditional/unconditional, supporting syntaxp hypotheses</li>

<li>uninterpreted functions</li>

<li>rules for merging IF branches that resolve to term- rather than bit-level
objects</li>

<li>automatic generation of new Boolean variables for IF tests that resolve to
terms rather than bits</li>

</ul>

<p>Warning: These features require careful setup of a rewriting theory with good
normal forms.  It's difficult to debug problems with them.  In many ways
they may not yet be ready for prime time.</p>

<h3>Rewriting</h3>

<p>Elaborating on our memory example, suppose we are trying to prove something
about a program that loads and stores from computed addresses in a 1024-entry
memory of 32-bit unsigned numbers.  For good execution speed when running
concrete simulations, we might represent this memory as a stobj containing a
1024-element array.  However, this doesn't perform well when proving theorems
about this representation using GL, because at each update to a symbolic
address we must modify several (perhaps all) entries in the array
representation: if our update is</p>

@({
  (update-mem <sym_address> <sym_value> <arr>)
})

<p>then at each address i of the array we must store an object representing:</p>

@({
  if (sym_address == i) then sym_value else arr[i].
})

<p>We might do better if we didn't try to compute an explicit interpretation of
the array after each update, but instead simply tracked the updates in
chronological order, as in an alist.  To illustrate how to do this, suppose
that our updater, accessor, and creator functions are, respectively,</p>

<ul>
<li>@('(update-mem addr val mem)')</li>
<li>@('(access-mem addr mem)')</li>
<li>@('(create-mem)')</li>
</ul>

<p>First, tell GL never to open the definitions of these functions:</p>

@({
 (gl::gl-set-uninterpreted update-mem)
 (gl::gl-set-uninterpreted access-mem)
 (gl::gl-set-uninterpreted create-mem)
})

<p>Now, when GL encounters updates, rather than computing a new explicit
symbolic representation for the memory, it will return a term representation,
such as</p>

@({
  (update-mem addr1 val1 (update-mem addr2 val2 (create-mem))).
})

<p>To make this work, we just need to provide rewrite rules so that GL can reason
about accesses:</p>

@({
 (gl::def-gl-rewrite access-of-create
    (equal (access-mem addr (create-mem))
           (and (natp addr) (< addr 1024) 0)))

 (gl::def-gl-rewrite access-of-update
    (equal (access-mem addr (update-mem waddr val mem))
           (if (equal (nfix addr) (nfix waddr))
               val
             (access-mem addr mem))))
})

<h3>Branch Merging</h3>

<p>Suppose that somewhere in our program we have an update as follows:</p>

@({
  (let ((mem (if special-condition
                 (update-mem addr val mem)
               mem)))
      ...)
})

<p>At this point, simulating with just the rules we have above, our proof will
probably fail because a subsequent access of the memory won't be resolved by
the access-of-update rule: we no longer have a term of the form</p>

@({
  (access-mem addr (update-mem waddr val mem))
})

<p>but rather</p>

@({
 (access-mem addr (if cond (update-mem waddr val mem) mem)).
})

<p>We could fix this by introducing a new rule:</p>

@({
 (gl::def-gl-rewrite access-of-if
     (equal (access-mem addr (if c mem1 mem2))
            (if c (access-mem addr mem1) (access-mem addr mem2))))
})

<p>This is probably the easiest solution if ACCESS-MEM is the only important
function that must interact with UPDATE-MEM.  An alternative is to write a rule
that merges the two branches into a single term.  A branch merge rule can
accomplish this:</p>

@({
 (gl::def-gl-branch-merge merge-conditional-update
   (equal (if cond (update-mem addr val mem) mem)
          (update-mem addr (if cond val (access-mem addr mem)) mem)))
})

<p>This isn't necessarily cheap -- in order to apply this rule, we need to find
the previous value of addr in mem, and this symbolic lookup is relatively
expensive, since it may need to traverse all the updates in mem to construct
the symbolic value of the access.</p>


<h3>Term-level shape specifiers</h3>

<p>Traditionally, to do a proof in GL one must supply, for each free variable of
the theorem, a shape specifier, which tells GL how to create a symbolic object
to represent that variable.  After GL finishes the symbolic execution portion
of the proof, the shape specifiers must be shown to be appropriate given the
assumptions about each variable; it therefore generates proof obligations of
the form:</p>

@({
 (implies (<hypotheses> var)
          (shape-spec-obj-in-range <shape-spec> var))
})

<p>These are called coverage obligations.  Shape-spec-obj-in-range says that the
value var is expressible by the given shape-spec; that is, the shape-spec
covers all possible values of var satisfying the hyps.  For example, if the
shape-spec is the :g-number construct for a 10-bit integer, then the
shape-spec-obj-in-range term reduces to:</p>

@({
  (and (integerp var)
       (< var (expt 2 9))
       (<= (- (expt 2 9)) var)).
})

<p>Since the new GL capabilities described above allow manipulation of
term-level symbolic objects, it can be useful to supply term-level shape
specifiers.  This can be done using the G-CALL and G-VAR constructs.</p>

<p>A G-VAR construct is simply a free variable; it can represent any object
whatsoever, so its coverage obligations are trivial.</p>

<p>A G-CALL represents a function call.  It takes three arguments:</p>

<ul>
<li>FN, a function symbol</li>
<li>ARGS, a list of arguments, each (recursively) a shape spec</li>
<li>INV, a 1-argument function symbol or lambda, the inverse function.</li>
</ul>

<p>The symbolic term resulting from this shape spec is simply the application
of FN to the symbolic objects derived from ARGS.  INV is an extra piece of
information that tells us how to prove coverage.</p>

<p>The basic coverage obligation for assigning some variable V a shape spec SS
is that for every possible value of V satisfying the hypotheses, there must be
an environment under which the symbolic object derived from SS evaluates to
that value.  The coverage proof must show that there exists such an
environment.</p>

<p>Providing an inverse function basically says:</p>

<p><box>
   \"If we need (FN ARGS) to evaluate to VAL, then ARGS should be (INV VAL).\"
</box></p>

<p>So to prove that (G-CALL FN ARGS INV) covers VAL, we first prove that ARGS
cover (INV VAL), then that (FN (INV VAL)) equals VAL.  The argument that this
works is:</p>

<ul>

<li>We first prove ARGS covers (INV VAL) -- that is, there exists some
environment E under which the symbolic objects derived from ARGS evaluate
to (INV VAL).</li>

<li>Since (FN (INV VAL)) equals VAL, this same environment E suffices to make
the symbolic object (FN ARGS) evaluate to VAL.</li>

</ul>

<p>Following our memory example above, suppose we want to initially assign our
memory object a symbolic value under which address 1 has been assigned a 10-bit
integer.  Assuming our memory follows the standard record rules, i.e.</p>

@({
  (update-mem addr (access-mem addr mem) mem) = mem,
})

<p>we can represent any such memory as</p>

@({
  (update-mem 1 <some 10-bit integer> <some memory>)
})

<p>Our shape-spec for this will therefore be:</p>

@({
 (g-call 'update-mem
         (list 1
               (g-number (list 0 1 2 3 4 5 6 7 8 9)) ;; 10-bit integer
               (g-var 'mem)) ;; free variable
         <some inverse function!>)
})

<p>What is an appropriate inverse?  The inverse needs to take any memory
satisfying our assumption and generate the list of necessary arguments to
update-mem that fit this template.  The following works:</p>

@({
   (lambda (m) (list 1 (access-mem 1 m) m))
})

<p>because for any value m satisfying our assumptions,</p>

<ul>

<li>the first argument returned is 1, which is covered by our shape-spec 1</li>

<li>the second argument returned will (by the assumption) be a 10-bit integer,
which is covered by our g-number shape-spec</li>

<li>the third argument returned matches our g-var shape-spec since anything at
all is covered by it</li>

<li>the final term we end up with is:
@({
        (update-mem 1 (access-mem 1 m) m)
})
    which (by the record rule above) equals m.</li>

</ul>

<p>GL tries to manage coverage proofs itself, and when using G-CALL constructs
some rules besides the ones it typically uses may be necessary -- for example,
the redundant record update rule used here.  You may add these rules to the
rulesets used for coverage proofs as follows:</p>

@({
 (acl2::add-to-ruleset gl::shape-spec-obj-in-range-backchain
                       redundant-mem-update)
 (acl2::add-to-ruleset gl::shape-spec-obj-in-range-open
                       redundant-mem-update)
})

<p>There are two rulesets because these are used in slightly different phases of
the coverage proof.</p>

<p>This feature has not yet been widely used and the detailed mechanisms
for (e.g.)  adding rules to the coverage strategy are likely to change.</p>


<h3>Automatic Boolean Variable Generation</h3>

<p>GL now has the ability to generate fresh Boolean variables in addition to
the ones existing in the user-provided shape spec.  It does this anytime an IF
condition's value ends up as a term-level object, i.e. a G-APPLY (function
call) or G-VAR (free variable).  The mapping between these term-level objects
and the generated Boolean variables are stored as we symbolically execute and
can be reused if the same condition is encountered again.  Careful use of this
feature can allow GL to work without giving such detailed shape specifiers.</p>

<p>For example, suppose that we don't want to assume anything about our memory
variable, but we know that for any slot we access, we'll only use 5 bits of the
stored value: perhaps our accessors always take (LOGHEAD 5 x) of the slot.  We
can assign a G-VAR object to the memory; that way it can represent any object
at all.  We then want to arrange things so that at every access, we generate 5
new Boolean variables for the integer bits of that access (if we haven't
already done so).  Here is one rule that will accomplish that:</p>

@({
 (gl::def-gl-rewrite loghead-5-of-access-mem
    ;; We don't want this rule to apply to an update-mem term, so this syntaxp
    ;; hyp prevents that.  We also should only apply this if ADDR is a concrete
    ;; object; we'd need a different strategy for symbolic addresses.
    (implies (syntaxp (and (not (and (consp mem)
                                     (gl::g-apply-p mem)
                                     (eq (gl::g-apply->fn mem) 'update-mem)))
                           (gl::general-concrete-p addr)))
              (equal (loghead 5 (access-mem addr mem))
                     (logcons
                      (if (logbitp 0 (access-mem addr mem)) 1 0)
                      (logcons
                       (if (logbitp 1 (access-mem addr mem)) 1 0)
                       (logcons
                        (if (logbitp 2 (access-mem addr mem)) 1 0)
                        (logcons
                         (if (logbitp 3 (access-mem addr mem)) 1 0)
                         (logcons
                          (if (logbitp 4 (access-mem addr mem)) 1 0)
                          0))))))))
})

<p>Performing this rewrite will causes GL to generate a Boolean variable for each
of these LOGBITP terms, because they produce term-level objects that are then
used in IF tests.</p>

<p>Using this strategy makes it harder to generate counterexamples.  In fact, it
is impossible to generally solve the problem of generating counterexamples when
using this strategy.  A satisfying assignment from a SAT solver gives us an
assignment of values to our Boolean variables.  But these Boolean variables
each just correspond to some term, which may be an arbitrary nesting of
functions.  To map this Boolean-level counterexample to an ACL2-level
counterexample, we are then left with finding an assignment for some variables
that makes a series of terms take certain truth values, which is undecidable.
In the next section, we describe a heuristic method for generating
counterexamples that works in practice when applied carefully.</p>

<p>Furthermore, unless this strategy is used with utmost care, it is likely that
proofs will fail due to detection of \"counterexamples\" that are actually
impossible.  For example, we might generate a Boolean variable for (integerp x)
and another one for (logbitp 0 x).  But these two terms are not independent; in
fact, (logbitp 0 x) implies (integerp x).  Currently, GL has no mechanism to
pass this restriction to a SAT solver, so we may find false counterexamples
that violate this constraint. This can't render GL unsound, but may lead to
failed proofs.</p>

<p>The situation described above (where every field is accessed via LOGHEAD and
via concrete address) is a particularly good one for this strategy, since then
all we need to know about each field are its LOGBITPs, which are all
independent.</p>

<h3>Counterexamples with Automatic Boolean Variable Generation</h3>

<p>Our strategy for generating counterexamples when using automatic Boolean
variable generation is to provide rules for manipulating assignments.  For
example:</p>

@({
 (gl::def-glcp-ctrex-rewrite
   ((logbitp n x) t)
   (x (logior (ash 1 n) x)))

 (gl::def-glcp-ctrex-rewrite
   ((logbitp n x) nil)
   (x (logand (lognot (ash 1 n)) x)))
})

<p>These two rules, respectively, say:</p>

<ul>
<li>\"if (logbitp n x) should be T, then assign X = (logior (ash 1 n) x)\"</li>
<li>\"if (logbitp n x) should be NIL, then assign X = (logand (lognot (ash 1 n)) x)\".</li>
</ul>

<p>DEF-GLCP-CTREX-REWRITE can also take a keyword argument :test, which can do
a syntactic check on the variables matched. E.g., we could ensure that N was a
constant in the rules above:</p>

@({
 (gl::def-glcp-ctrex-rewrite
   ((logbitp n x) t)
   (x (logior (ash 1 n) x))
   :test (quotep n))
})

<p>Note that these rules are purely heuristic, have no bearing on the soundness of
GL, and do not require any proofs.  Getting them wrong may cause GL to generate
false counterexamples, however.</p>

<p>Another rule that would be useful in the memory example above:</p>

@({
 (gl::def-glcp-ctrex-rewrite
   ((access-mem addr mem) val)
   (mem (update-mem addr val mem))
   :test (quotep addr))
})")

