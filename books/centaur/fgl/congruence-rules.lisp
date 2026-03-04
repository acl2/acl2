; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(include-book "centaur/meta/congruence" :dir :system)
(include-book "centaur/misc/starlogic" :dir :system)


(local (std::add-default-post-define-hook :fix))

(defprod fgl-congruence-rune
  ((name pseudo-fnsym-p))
  :tag :congruence
  :layout :list)

(fty::deflist fgl-congruence-runelist :elt-type fgl-congruence-rune :true-listp t)

(local (in-theory (disable w)))

(fty::deflist congruence-rulelist :elt-type cmr::congruence-rule :true-listp t)

(defprod fgl-id-congruence-rune
  ((name pseudo-fnsym-p))
  :tag :id-congruence
  :layout :list)

(fty::deflist fgl-id-congruence-runelist :elt-type fgl-id-congruence-rune :true-listp t)

(defprod fgl-id-congruence-rule
  ((fn pseudo-fnsym-p)
   (id-index natp :rule-classes :type-prescription)
   (arity natp :rule-classes :type-prescription))
  :layout :list)

(fty::deflist fgl-id-congruence-rulelist :elt-type fgl-id-congruence-rule :true-listp t)



;; (define fgl-ev-congruence-rulelist-correct-p ((x congruence-rulelist-p))
;;   (if (atom x)
;;       t
;;     (and (fgl-ev-congruence-rule-correct-p (car x))
;;          (fgl-ev-congruence-rulelist-correct-p (cdr x))))
;;   ///
;;   (defthm fgl-ev-congruence-rulelist-correct-p-of-cons
;;     (equal (fgl-ev-congruence-rulelist-correct-p (cons a b))
;;            (and (fgl-ev-congruence-rule-correct-p a)
;;                 (fgl-ev-congruence-rulelist-correct-p b))

(define congruence-rule-from-rune ((rune fgl-congruence-rune-p)
                                   (w plist-worldp))
  :returns (mv errmsg (rule (implies (not errmsg) (cmr::congruence-rule-p rule))))
  (b* ((name (fgl-congruence-rune->name rune))
       (formula (acl2::meta-extract-formula-w name w))
       ((unless (pseudo-termp formula))
        (mv (msg "Bad formula: ~x0" name) nil)))
    (cmr::parse-congruence-rule formula w)))

(define congruence-rules-from-runes ((runes fgl-congruence-runelist-p)
                                     (w plist-worldp))
  :returns (mv errmsg (rules congruence-rulelist-p))
  (b* (((when (atom runes)) (mv nil nil))
       ((mv errmsg1 rule) (congruence-rule-from-rune (car runes) w))
       ((mv errmsg2 rules) (congruence-rules-from-runes (cdr runes) w)))
    (if errmsg1
        (mv errmsg1 rules)
      (mv errmsg2 (cons rule rules)))))











(fty::defmap congruence-rule-table :key-type pseudo-fnsym :val-type congruence-rulelist
  :true-listp t)

(fty::defmap id-congruence-rule-table :key-type pseudo-fnsym :val-type fgl-id-congruence-rulelist :true-listp t)

;; ID congruences -- We want a (first-order) condition that implies the (second-order)
;; following property: for any equivalence relation equiv, (equiv x y) => (equiv (foo z x) (foo z y))
;; (generalized to any arity and argument position).
;; A sufficient condition (proof below) implying this is (for all z, x, y):
;; (or (equal (foo z x) (foo z y))
;;     (equal (foo z x) x)).
;; In many cases we have (equal (foo z x) x) unconditionally, which we recognize separately
;; for convenience.

;; Proof: assuming (equiv x y) and not (equiv (foo z x) (foo z y)), we have
;; (not (equal (foo z x) (foo z y))), therefore (equal (foo z x) x) and (equal
;; (foo z y) y).  Then (not (equiv (foo z x) (foo z y))) reduces to (not (equiv
;; x y)), contradicting our assumption.
(local (in-theory (disable cmr::pseudo-term-var-list->names-when-pseudo-term-listp)))
(local (defthm symbol-listp-when-pseudo-var-list-p
         (implies (pseudo-var-list-p x)
                  (symbol-listp x))))

(local (defthm pseudo-termp-nth
         (implies (pseudo-term-listp x)
                  (pseudo-termp (nth n x)))
         :hints(("Goal" :in-theory (enable pseudo-term-listp nth)))))

(local (defthm pseudo-term-var-nth
         (implies (and (cmr::pseudo-term-var-listp x)
                       (< (nfix n) (len x)))
                  (pseudo-term-case (nth n x) :var))
         :hints(("Goal" :in-theory (enable cmr::pseudo-term-var-listp len nth)))))

;; This recognizes (equal (foo z x) x) (generalized by arity/position), and
;; returns the rule (containing function, arity, position).
(define parse-simple-id-congruence ((x pseudo-termp))
  :returns (mv (rule (iff (fgl-id-congruence-rule-p rule) rule))
               (vars pseudo-term-listp))
  :prepwork ((local (defthm consp-assoc-equal-when-key
                      (implies k
                               (iff (consp (Assoc-equal k x)) (assoc-equal k x))))))
  (pseudo-term-case x
    :fncall (if (and (eq x.fn 'equal)
                     (eql (len x.args) 2))
                (b* ((arg2 (second x.args))
                     (arg2-var
                      (pseudo-term-case arg2
                        :var arg2.name
                        :lambda
                        (pseudo-term-case arg2.body
                          :var (and (equal arg2.body
                                           (cdr (assoc arg2.body.name
                                                       (pairlis$ arg2.formals
                                                                 arg2.args))))
                                    arg2.body.name)
                          :otherwise nil)
                        :otherwise nil))
                     ((unless arg2-var) (mv nil nil))
                     ;; (let ((arg2 (second x.args)))
                     ;;   (pseudo-term-case 
                     ;;   (or (pseudo-term-case (second x.args) :var)
                     ;;     (pseudo-term-case (second x.args) :var)
                     (arg1 (first x.args)))
                  (pseudo-term-case arg1
                    :fncall (b* (((unless (cmr::pseudo-term-var-listp arg1.args)) (mv nil nil))
                                 (vars (cmr::pseudo-term-var-list->names arg1.args))
                                 ((unless (no-duplicatesp-eq vars)) (mv nil nil))
                                 (idx (acl2::index-of arg2-var vars))
                                 ((unless idx) (mv nil nil)))
                              (mv (fgl-id-congruence-rule arg1.fn idx (len vars)) arg1.args))
                    :otherwise (mv nil nil)))
              (mv nil nil))
    :otherwise (mv nil nil))
  ///
  (defret pseudo-term-var-listp-of-<fn>
    (cmr::pseudo-term-var-listp vars)))


(define parse-simple-disjunction ((x pseudo-termp))
  :returns (mv ok (left pseudo-termp) (right pseudo-termp))
  (pseudo-term-case x
    :fncall (case x.fn
              (if
                  (if (or (equal (first x.args)
                                 (second x.args))
                          (equal (second x.args) ''t))
                      (mv t (first x.args) (third x.args))
                    (mv nil nil nil)))
              (implies
               (let ((arg1 (first x.args)))
                 (pseudo-term-case arg1
                   :fncall (if (eq arg1.fn 'not)
                               (mv t (first arg1.args) (second x.args))
                             (mv nil nil nil))
                   :otherwise (mv nil nil nil))))
              (t (mv nil nil nil)))
    :otherwise (mv nil nil nil)))

(define parse-id-congruence-equivalence ((rule fgl-id-congruence-rule-p)
                                         (vars pseudo-term-listp)
                                         (x pseudo-termp))
  :guard (cmr::pseudo-term-var-listp vars)
  :returns (diff-var pseudo-termp)
  (b* (((fgl-id-congruence-rule rule)))
    (pseudo-term-case x
      :fncall (and (eq x.fn 'equal)
                   (b* (((list arg1 arg2) x.args)
                        ((unless (and (pseudo-term-case arg1 :fncall)
                                      (pseudo-term-case arg2 :fncall)))
                         nil)
                        ((pseudo-term-fncall arg1))
                        ((pseudo-term-fncall arg2))
                        ((unless (and (eq arg1.fn rule.fn)
                                      (eq arg2.fn rule.fn)))
                         nil)
                        (vars (pseudo-term-list-fix vars))
                        (diff-args (cond ((mbe :logic (pseudo-term-list-equiv arg1.args vars)
                                               :exec (equal arg1.args vars))
                                          arg2.args)
                                         ((mbe :logic (pseudo-term-list-equiv arg2.args vars)
                                               :exec (equal arg2.args vars))
                                          arg1.args))))
                     (and diff-args
                          (cmr::pseudo-term-var-listp diff-args)
                          (no-duplicatesp-eq (cmr::pseudo-term-var-list->names diff-args))
                          (b* ((diff-var (nth rule.id-index diff-args)))
                            (and (not (member-equal diff-var vars))
                                 (equal (update-nth rule.id-index (nth rule.id-index diff-args) vars)
                                        diff-args)
                                 ;; (fgl-id-congruence-rule-fix rule)
                                 diff-var)))))
      :otherwise nil))
  ///
  (local (defthm len-of-update-nth
           (equal (len (update-nth n v y))
                  (max (len y) (+ 1 (nfix n))))
           :hints(("Goal" :in-theory (enable len update-nth)))))
  (local (defthm len-of-update-nth-free
           (implies (equal x (update-nth n v y))
                    (equal (len x)
                           (max (len y) (+ 1 (nfix n)))))))
  (local (defthm max-when-less
           (implies (and (< x y)
                         (integerp x) (integerp y))
                    (equal (max y (+ 1 x)) y))))
  (local (in-theory (disable max)))
  (defret pseudo-term-kind-of-<fn>
    (b* (((fgl-id-congruence-rule rule)))
      (implies (and diff-var
                    (equal (len vars) rule.arity)
                    (< rule.id-index rule.arity))
               (pseudo-term-case diff-var :var)))))

(define parse-id-congruence-rule ((x pseudo-termp))
  :returns (rule (iff (fgl-id-congruence-rule-p rule) rule))
  (b* (((mv rule ?vars) (parse-simple-id-congruence x))
       ((when rule) rule)
       ((mv ok left right) (parse-simple-disjunction x))
       ((unless ok) nil)
       ((mv rule vars other-term)
        (b* (((mv rule vars) (parse-simple-id-congruence left))
             ((when rule) (mv rule vars right))
             ((mv rule vars) (parse-simple-id-congruence right)))
          (mv rule vars left)))
       ((unless rule) nil)
       (diff-var
        (parse-id-congruence-equivalence rule vars other-term)))
    (and diff-var rule)))

(define check-id-congruence-rune ((rune fgl-id-congruence-rune-p)
                                  (w plist-worldp))
  :returns (mv errmsg (rule (implies (not errmsg) (fgl-id-congruence-rule-p rule))))
  (b* ((rune (fgl-id-congruence-rune-fix rune))
       (name (fgl-id-congruence-rune->name rune))
       (formula (acl2::meta-extract-formula-w name w))
       ((unless (pseudo-termp formula))
        (mv (msg "Formula not pseudo-termp: ~x0" rune) nil))
       (rule (parse-id-congruence-rule formula))
       ((unless rule) (mv (msg "Incorrect form for an identity congruence rule: ~x0" rune) nil)))
    (mv nil rule)))

(define id-congruence-table-from-runes ((runes fgl-id-congruence-runelist-p)
                                        (w plist-worldp))
  :returns (mv errmsg (table id-congruence-rule-table-p))
  (b* (((when (atom runes)) (mv nil nil))
       ((mv errmsg rule) (check-id-congruence-rune (car runes) w))
       ((when errmsg) (mv errmsg nil))
       ((mv errmsg rest) (id-congruence-table-from-runes (cdr runes) w))
       ((when errmsg) (mv errmsg nil))
       ((fgl-id-congruence-rule rule)))
    (mv nil (hons-acons rule.fn (cons rule (cdr (hons-get rule.fn rest))) rest))))
       






(define fgl-congruence-runes ((w plist-worldp))
  (cdr (hons-assoc-equal 'fgl-congruence-rules (table-alist 'fgl-congruence-rules w))))

(defmacro add-fgl-congruence (name)
  (let ((rune (fgl-congruence-rune name)))
    `(progn (local (make-event
                    (b* ((rune ',rune)
                         ((mv errmsg &) (congruence-rule-from-rune rune (w state)))
                         ((when errmsg) (er soft 'add-fgl-congruence
                                            "Couldn't extract a congruence rule from ~x0: ~@1"
                                            rune errmsg)))
                      (value '(value-triple :congruence-rule-ok)))))
            (table fgl-congruence-rules 'fgl-congruence-rules
                   (cons ',rune (fgl-congruence-runes world))))))

(define fgl-id-congruence-runes ((w plist-worldp))
  (cdr (hons-assoc-equal 'fgl-id-congruence-rules (table-alist 'fgl-id-congruence-rules w))))

(defmacro add-fgl-id-congruence (name)
  (let ((rune (fgl-id-congruence-rune name)))
    `(progn (local (make-event
                    (b* ((rune ',rune)
                         ((mv errmsg &) (check-id-congruence-rune rune (w state)))
                         ((when errmsg) (er soft 'add-fgl-id-congruence
                                            "Couldn't extract a id-congruence rule from ~x0: ~@1"
                                            rune errmsg)))
                      (value '(value-triple :id-congruence-rule-ok)))))
            (table fgl-id-congruence-rules 'fgl-id-congruence-rules
                   (cons ',rune (fgl-id-congruence-runes world))))))

(defmacro def-fgl-id-congruence (name call index &rest kwd-args)
  (b* (((unless (and (symbolp name)
                     (symbol-listp call)
                     (consp call)
                     (no-duplicatesp-eq (cdr call))
                     (posp index)
                     (< index (len call))))
        (er hard? 'def-fgl-id-congruence "Malformed args"))
       (arg (nth index call))
       (alt-arg (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name arg) "-EQUIV") (car call))))
    `(progn (defthm ,name
              (or (equal ,call ,arg)
                  (equal ,call ,(update-nth index alt-arg call)))
              :rule-classes nil
              . ,kwd-args)
            (add-fgl-id-congruence ,name))))

(local (defun foo (x) x))
(local (define bar (x) x))
(local (add-fgl-id-congruence foo))
(local (add-fgl-id-congruence bar))
(local (defun baz (x y z) (if x y z)))
(local (def-fgl-id-congruence baz-id-cong-1 (baz x y z) 2))
(local (def-fgl-id-congruence baz-id-cong-2 (baz x y z) 3))


(defxdoc add-fgl-congruence
  :parents (fgl-rewrite-rules)
  :short "Add a congruence rule to FGL's theory"
  :long "<p>See @(see acl2::congruence) for a general discussion of congruence rules.</p>

<p>FGL accepts congruence rules similar to those recognized by ACL2, but only
the \"classic\" variety, not \"patterned\" congruences. This macro takes the
name of a congruence rule and adds it to the list of such rules that will be
consumed by FGL.</p>

<p>See also @(see add-fgl-id-congruence) for an additional kind of rule
appropriate to identity functions.</p>")



(defsection conditional-identity-implies-congruence-propagation
  :parents (add-fgl-id-congruence)
  :short "Proof that the conditional identity property implies the congruence propagation property"
  :long "<p>See @(see add-fgl-id-congruence) for details.</p>
<p>Events:</p>
@(`*conditional-identity-implies-congruence-propagation-events*`)"
  (defconst *conditional-identity-implies-congruence-propagation-events*
   '(progn
      (encapsulate
        (((f * *) => *))

        (local (defun f (p x)
                 (declare (ignore p))
                 x))
        (defthm conditional-identity
          (or (equal (f p x) (f p y))
              (equal (f p x) x))
          :rule-classes nil))

      (encapsulate
        (((eqv * *) => *))

        (local (defun eqv (x y) (equal x y)))
        (defequiv eqv))

      (defthm congruence-propagation
        (implies (eqv x y)
                 (eqv (f p x) (f p y)))
        :hints (("goal" :use ((:instance conditional-identity (y x) (x y))
                              (:instance conditional-identity))))
        :rule-classes nil)))
  (local (make-event *conditional-identity-implies-congruence-propagation-events*)))


(defsection congruence-propagation-implies-conditional-identity
  :parents (add-fgl-id-congruence)
  :short "Proof that the congruence propagation property implies the conditional identity property"
  :long "<p>See @(see add-fgl-id-congruence) for details.</p>
<p>Events:</p>
@(`*congruence-propagation-implies-conditional-identity-events*`)"
  (defconst *congruence-propagation-implies-conditional-identity-events*
    '(progn
       (encapsulate
         (((f * *) => *)
          ((x) => *)
          ((y) => *)
          ((p) => *))

         (local (defun f (p x)
                  (declare (ignore p))
                  (not x)))
         (local (defun x () t))
         (local (defun y () nil))
         (local (defun p () nil))
         (defthm not-conditional-identity
           (not (or (equal (f (p) (x)) (f (p) (y)))
                    (equal (f (p) (x)) (x))))
           :rule-classes nil))

       (defun z ()
         (car (set-difference-equal '(0 1 2) (list (x) (y)))))

       (defthm z-not-x
         (not (equal (z) (x))))

       (defthm z-not-y
         (not (equal (z) (y))))

       (in-theory (disable z (z)))

       (defun eqv (a b)
         (let ((s (cond ((not (equal (f (p) (x)) (y)))
                         (list (x) (y) (f (p) (y))))
                        ((not (equal (f (p) (y)) (x)))
                         (list (x) (y)))
                        ((equal (f (p) (z)) (x))
                         (list (x) (z)))
                        (t (list (y) (z) (f (p) (z)))))))
           (iff (member a s) (member b s))))

       (defun a ()
         (cond ((not (equal (f (p) (x)) (y))) (x))
               ((not (equal (f (p) (y)) (x))) (x))
               ((equal (f (p) (z)) (x)) (x))
               (t (y))))

       (defun b ()
         (cond ((not (equal (f (p) (x)) (y))) (y))
               ((not (equal (f (p) (y)) (x))) (y))
               ((equal (f (p) (z)) (x)) (z))
               (t (z))))

       (defthm not-congruent
         (not (implies (eqv (a) (b))
                       (eqv (f (p) (a)) (f (p) (b)))))
         :hints (("goal" :use not-conditional-identity)))

       (defequiv eqv)))
  (local (make-event *congruence-propagation-implies-conditional-identity-events*)))
     





(defxdoc add-fgl-id-congruence
  :parents (fgl-rewrite-rules)
  :short "Add an identity congruence rule to FGL's theory"
  :long "<h3>Usage:</h3>
@({
 (add-fgl-id-congruence thmname)
 })
<p>where @('thmname') is the name of a theorem of either of the following forms:
@({
 (equal (f x1 ... xi ... xn) xi)
 })
or
@({
 (or (equal (f x1 ... xi ... xn) (f x1 ... yi ... xn))
     (equal (f x1 ... xi ... xn) xi))
 })
where @('f') is some function and @('yi') occurs in the argument list of its
call of @('f') in the same position as argument @('xi') occurs in other
calls. The form of this theorem is justified in the Theory section below.</p>

<p>See also @('def-fgl-id-congruence'), which additionally generates and
attempts to prove the required theorem.</p>

<h3>Function</h3>
<p>When such a theorem is added to FGL's theory, it allows rewriting of the
@('xi') argument position under an equivalence relation whenever we are
rewriting the outer call of @('f') under that equivalence relation. In effect,
it is as if we added the following congruence rule (see @(see
acl2::congruence)) for all equivalences @('eqv'):</p>
@({
 (implies (eqv xi yi)
          (eqv (f x1 ... xi ... xn) (f x1 ... yi ... xn)))
 })

<h3>Theory</h3>
<p>An identity function @('(f x) = x') has the property that for any
equivalence relation @('eqv'),
@({
 (implies (eqv x y)
          (eqv (f x) (f y))),
 })
that is, if we are rewriting a call of @('f') under some equivalence context,
we can rewrite its argument under that same context. (Call this the
congruence propagation property for argument 1 of @('f').)</p>

<p>This isn't only true of identity functions. For example, if @('(g x y z)')
equals @('(if x y z)'), then g has this property for both its second and third
argument, i.e. for any equivalence @('eqv'),
@({
 (implies (eqv y y-equiv)
          (eqv (g x y z) (g x y-equiv z)))
})
and
@({
 (implies (eqv z z-equiv)
          (eqv (g x y z) (g x y z-equiv))), }) that is, if rewriting a call of
 @('g') under some equivalence context, we can rewrite both its second and
 third arguments under that equivalence context.</p>

<p>The first-orderness of ACL2 prevents us from straightforwardly expressing
this property in terms of \"for any equivalence relation\". However, the
following property (call it the conditional identity property) is equivalent to
the congruence propagation property:</p>
@({
 (or (equal (f x) (f y))
     (equal (f x) x))
 })
<p>The proof is in two parts, in sections @(see conditional-identity-implies-congruence-propagation)
and @(see congruence-propagation-implies-conditional-identity). We outline how the proofs work in broad strokes.</p>

<p>In @(see conditional-identity-implies-congruence-propagation)
 a function @('f') is introduced with the sole constraint that it satisfies the conditional identity property on its second argument, then another function @('eqv') is introduced with the sole constraint that it is an equivalence relation. Given these two assumptions, we then show that @('f') satisfies the congruence propagation property with respect to @('eqv').</p>

<p>We take a slightly more roundabout tactic in @(see
congruence-propagation-implies-conditional-identity) in order to avoid stating
the assumption that @('f') satisfies the congruence propagation property for
all possible equivalence relations. Instead, we introduce @('f') with the
constraint that it does not satisfy the congruence propagation property; that
is, for certain arguments (0-ary functions constrained along with @('f')), that
property is untrue. We then define a function @('eqv') in terms of @('f') and
those arguments, showing that it is an equivalence relation and that there are
arguments to @('f') for which the congruence propagation property with respect
to @('eqv') is then violated.</p>")


(defxdoc def-fgl-id-congruence
  :parents (fgl-rewrite-rules)
  :short "Prove and add an identity congruence rule to FGL's theory"
  :long "<p>See @(see add-fgl-id-congruence) for an explanation of identity congruence rules.</p>

<p>Usage:
@({
 (def-fgl-id-congruence thmname (f x1 ... xn) index
   :hints hints)
 })
where @('thmname') is the name of the theorem to be generated, @('f') is some
function, @('x1 ... xn') a duplicate-free list of variables, and @('index') is
the (1-based) index of the identity argument (a positive integer less than or
equal to the arity of @('f'). (The index is 1-based for compatibility with
@(see acl2::defcong).)</p>

<p>This generates a theorem of the following form
@({
 (defthm thmname
   (or (equal (f x1 ... xi ... xn) xi)
       (equal (f x1 ... xi ... xn) (f x1 ... xi-equiv ... xn)))
  :hints hints
  :rule-classes nil)
 })

where @('xi') is the variable in position @('index') of the provided argument
list. After the theorem is admitted the theorem is registered as an identity
congruence for FGL using @(see add-fgl-id-congruence).</p>")

