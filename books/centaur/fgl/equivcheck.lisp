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

(include-book "def-fgl-rewrite")
(include-book "fancy-ev")
(include-book "satlink-sat")
(include-book "ipasir-sat")
(include-book "checks")
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))


(defxdoc advanced-equivalence-checking-with-fgl
  :parents (fgl)
  :short "Some tools for equivalence checking with FGL.")

(local (xdoc::set-default-parents advanced-equivalence-checking-with-fgl))

(define top-level-equal (x y)
  :no-function t
  :short "An alias for EQUAL.  Useful if you want to prove an equality in FGL using a particular strategy."
  :long "<p>Sometimes if you're proving an equivalence of two objects using
FGL/SAT/bitblasting, it's advantageous to use a strategy other than just
checking satisfiability of the negation of the top-level equivalence.  For
example, in proving the correctness of SIMD implementations where you're
proving equivalence of two wide integers composed of packed arithmetic results,
you might want to instead prove each of the lanes separately.  We can use an
FGL rewrite rule to rewrite the top-lvel @('equal') call to an alias that has a
rewriting strategy to solve it with this scheme.  But we don't want to rewrite
all calls of equal this way!  Instead, we suggest an alternate strategy:</p>

<ul>

<li>Locally introduce a rule rewriting @('(top-level-equal x y)') to the
function implementing your special solving strategy -- @(see
solve-lane-by-lane), for example.</li>

<li>Add a hint to your @('def-fgl-thm'): @(':hints ('(:clause-processor
replace-equal-with-top-level-equal))')</li>

</ul>

<p>The hint will replace only the @('equal') call at the top level of your
theorem with @('top-level-equal').</p>"
  :enabled t
  (equal x y))

(defevaluator repl-equal-ev repl-equal-ev-list ((equal x y) (top-level-equal x y)
                                                (if x y z) (implies x y))
  :namedp t)
(local (acl2::def-join-thms repl-equal-ev))
(local (acl2::def-ev-pseudo-term-fty-support repl-equal-ev repl-equal-ev-list))
(local (in-theory (disable pseudo-termp
                           ;; lrat::cdr-last-formula
                           ;; acl2::consp-of-car-when-alistp
                           symbol-listp)))

(define replace-equal-with-top-level-equal-rec ((x pseudo-termp))
  :measure (pseudo-term-count x)
  :returns (new-x pseudo-termp)
  :verify-guards nil
  (pseudo-term-case x
    :fncall (cond ((eq x.fn 'equal) (pseudo-term-fncall 'top-level-equal x.args))
                  ((eq x.fn 'implies) (pseudo-term-fncall
                                       'implies
                                       (list (first x.args)
                                             (replace-equal-with-top-level-equal-rec (second x.args)))))
                  ((eq x.fn 'if) (pseudo-term-fncall
                                  'if
                                  (list (first x.args)
                                        (replace-equal-with-top-level-equal-rec (second x.args))
                                        (replace-equal-with-top-level-equal-rec (third x.args)))))
                  (t (pseudo-term-fix x)))
    :lambda (pseudo-term-lambda
             x.formals
             (replace-equal-with-top-level-equal-rec x.body)
             x.args)
    :otherwise (pseudo-term-fix x))
  ///
  (verify-guards replace-equal-with-top-level-equal-rec)

  (local (defun-sk replace-equal-with-top-level-equal-rec-correct-cond (x)
           (forall a
                   (equal (repl-equal-ev (replace-equal-with-top-level-equal-rec x) a)
                          (repl-equal-ev x a)))
           :rewrite :direct))
  (local (in-theory (disable replace-equal-with-top-level-equal-rec-correct-cond)))

  (local (defthm replace-equal-with-top-level-equal-rec-correct-lemma
           (replace-equal-with-top-level-equal-rec-correct-cond x)
           :hints (("goal" :induct (replace-equal-with-top-level-equal-rec x))
                   (and stable-under-simplificationp
                        `(:expand (,(car (last clause))))))
           :rule-classes nil))
  (defthm replace-equal-with-top-level-equal-rec-correct
    (equal (repl-equal-ev (replace-equal-with-top-level-equal-rec x) a)
           (repl-equal-ev x a))
    :hints (("goal" :use replace-equal-with-top-level-equal-rec-correct-lemma))))




(define replace-equal-with-top-level-equal ((clause pseudo-term-listp))
  :prepwork ((local (defthm pseudo-termp-of-car-last
                      (implies (pseudo-term-listp clause)
                               (pseudo-termp (car (last clause)))))))
  :parents (top-level-equal)
  :short "Clause processor that replaces the final call of @('equal') in a
theorem conclusion with @('top-level-equal')."
  (list (append (butlast clause 1)
                (list (replace-equal-with-top-level-equal-rec (car (last clause))))))
  ///
  (local (defthm repl-equal-ev-of-disjoin-when-car-last
           (implies (repl-equal-ev (car (last clause)) a)
                    (repl-equal-ev (acl2::disjoin clause) a))
           :hints (("goal" :induct (last clause)))))

  (local (include-book "std/lists/butlast" :dir :system))

  (local (defthm repl-equal-ev-of-disjoin-when-butlast
           (implies (repl-equal-ev (acl2::disjoin (butlast clause n)) a)
                    (repl-equal-ev (acl2::disjoin clause) a))
           :hints (("goal" :induct (butlast clause n)
                    :in-theory (disable repl-equal-ev-of-disjoin-when-car-last)))))

  (defthm replace-equal-with-top-level-equal-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (repl-equal-ev (acl2::conjoin-clauses (replace-equal-with-top-level-equal clause)) a))
             (repl-equal-ev (acl2::disjoin clause) a))
    :rule-classes :clause-processor))




(define lookup-previous-stack-frame-binding ((var symbolp) interp-st)
  :prepwork ((local (defthm alistp-when-fgl-object-bindings-p-rw
                      (implies (fgl-object-bindings-p x)
                               (alistp x))
                      :hints(("Goal" :in-theory (enable fgl-object-bindings-p)))))
             (local (defthm fgl-object-p-of-assoc
                      (implies (fgl-object-bindings-p x)
                               (fgl-object-p (cdr (assoc k x)))))))
  :returns (binding fgl-object-p)
  (stobj-let ((stack (interp-st->stack interp-st)))
             (binding)
             (b* ((nframes (stack-frames stack))
                  ((when (< nframes 2)) nil)
                  (minor (stack-nth-frame-minor-bindings 1 0 stack))
                  (minor-look (assoc-eq var minor))
                  ((when minor-look) (cdr minor-look))
                  (major (stack-nth-frame-bindings 1 stack)))
               (cdr (assoc-eq var major)))
             binding)
  ///
  (fancy-ev-add-primitive lookup-previous-stack-frame-binding (symbolp var)))




(local (defthm unsigned-byte-p-forward
         (implies (unsigned-byte-p n x)
                  (and (natp n) (natp x)))
         :rule-classes :forward-chaining))
(local (defthmd logcdr-equal-when-logcar-equal
         (implies (equal (logcar x) (logcar y))
                  (equal (equal (logcdr x) (logcdr y))
                         (equal (ifix x) (ifix y))))
         :hints (("goal" :use ((:instance bitops::logcons-destruct (x x))
                               (:instance bitops::logcons-destruct (x y)))
                  :in-theory (disable bitops::logcons-destruct)))))
(local (defthm logtail-equal-when-loghead-equal
         (implies (equal (loghead width x) (loghead width y))
                  (equal (equal (logtail width x) (logtail width y))
                         (equal (ifix x) (ifix y))))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs
                                            logcdr-equal-when-logcar-equal)))))

(encapsulate
  (((solve-lane-by-lane-config) => * :guard t :formals nil))
  (local (defun solve-lane-by-lane-config nil nil)))


(define solve-lane-by-lane (x y width)
  :short "Equality check that, in FGL, splits an equivalence of SIMD packed integers
          into lane-by-lane equivalence checks."
  :long "<p>The equivalence check of each of the lanes is done using the FGL
SAT config object @('(solve-lane-by-lane-config)'), which is an attachable
function.  Its default attachment uses SATLINK in the default configuration
with transforms.</p>"
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  (equal x y)
  ///
  (disable-definition solve-lane-by-lane)
  
  (def-fgl-rewrite solve-lane-by-lane-impl
    (implies (and (syntaxp (posp width))
                  (check-integerp xintp x)
                  (check-integerp yintp y))
             (equal (solve-lane-by-lane x y width)
                    (if (and (check-int-endp x-endp x)
                             (check-int-endp y-endp y))
                        (equal x y)
                      (b* ((config (syntax-bind config (g-concrete
                                                             (solve-lane-by-lane-config)))))
                        (acl2::and* (fgl-validity-check config
                                                             (equal (loghead width x)
                                                                    (loghead width y)))
                                    (solve-lane-by-lane (logtail width x) (logtail width y) width))))))
    :hints(("Goal" :in-theory (e/d (fgl-sat-check acl2::and*)
                                   (unsigned-byte-p))))))





(define solve-lane-by-lane-masked (x y mask width)
  :parents (fgl-and-ucode)
  :short "Equality check that works around hard SAT/fraiging problems caused by writemasking."
  :long "<p>This addresses a problem that sometimes comes up in proving
correctness of SIMD operations with writemasking.  Suppose an instruction
applies function F to each 32-bit lane of a vector, with writemasking; that is,
the spec for lane i is @('mask[i] ? F(src.lanes32[i]) : dst.lanes32[i]').  Now,
perhaps the implementation applies the same function F, but instead operates on
@('mask[i] ? src.lanes32[i] : 0').  Of course this is OK because when
@('mask[i]') is 0 we don't care what the function computes.  But unfortunately
when we pack the lanes together and try to equivalence check spec versus
implementation, one of our best tools, fraiging (aka SAT sweeping) doesn't
work.  This is because there are no equivalent formulas within the computation
of the function F: each subformula G within F shows up in the spec as
@('G(src.lanes32[i])') but in the implementation as @('G(mask[i] ?
src.lanes32[i] : 0)'), which is obviously not equivalent.</p>

<p>A workaround for this problem is to split the check for each lane into cases
according to @('mask[i]') and propagate that assumption into their formulas.
That is, when @('mask[i]') is assumed true, replace @('mask[i] ?
src.lanes32[i] : 0') with just @('src.lanes32[i]').  FGL has a special function
called @('fgl-pathcond-fix') that can do this: logically it is the
identity function, but under FGL it rewrites the input symbolic object to
assume the current path condition.  That is, for each Boolean formula in the
symbolic object, that formula is simplified by replacing any AIG literals known
to be true (false) under the path condition with 1 (0).  In many cases simply
splitting into cases for each lane's corresponding mask bit, specializing each
equivalence under both cases, produces a formula that is much easier to solve
than the original, especially using fraiging.</p>

<p>Sometimes this may not work; for a somewhat more aggressive strategy, see
@(see solve-lane-by-lane-masked+).</p>
"
  :enabled t
  :ignore-ok t
  :irrelevant-formals-ok t
  (equal x y)
  ///
  (disable-definition solve-lane-by-lane-masked)

  (def-fgl-rewrite solve-lane-by-lane-masked-impl
    (implies (and (syntaxp (posp width))
                  (check-integerp xintp x)
                  (check-integerp yintp y))
             (equal (solve-lane-by-lane-masked x y mask width)
                    (if (and (check-int-endp x-endp x)
                             (check-int-endp y-endp y))
                        (equal x y)
                      (acl2::and*
                       (b* ((lane-equiv (equal (loghead width x)
                                               (loghead width y))))
                         (if (logbitp 0 mask)
                             (fgl-pathcond-fix lane-equiv)
                           (fgl-pathcond-fix lane-equiv)))
                       (solve-lane-by-lane-masked (logtail width x) (logtail width y)
                                                  (logcdr mask) width)))))
    :hints(("Goal" :in-theory (e/d (fgl-sat-check acl2::and*)
                                   (unsigned-byte-p))))))


(encapsulate
  (((solve-lane-by-lane-masked+-config0) => * :guard t :formals nil)
   ((solve-lane-by-lane-masked+-config1) => * :guard t :formals nil))
  (local (defun solve-lane-by-lane-masked+-config0 nil nil))
  (local (defun solve-lane-by-lane-masked+-config1 nil nil)))

(define solve-lane-by-lane-masked+ (x y mask width)
  :parents (fgl-and-ucode)
  :short "Equality check that works around hard SAT/fraiging problems caused by
writemasking, solving each case separately."
  :long "<p>See @(see solve-lane-by-lane-masked) for a general discussion of
the problem this addresses.</p>

<p>The approach of this function differs from that of @(see
solve-lane-by-lane-masked) in that instead of using @('fgl-pathcond-fix')
to try to fold in the mask conditions, this function solves each case as a
separate SAT problem.  The AIGNET observability transform is often useful in
order to make the mask conditions yield comparable internal nodes.</p>

<p>The SAT checks use FGL SAT config objects produced by attachments to the
0-ary functions @('solve-lane-by-lane-masked+-config0') and
@('solve-lane-by-lane-masked+-config1'), which respectively determine how to check when
the mask bit is assumed to be 0 and when the mask bit is assumed 1.  Default
attachments assume that we want to use incremental SAT for the (typically easy)
mask 0 case and monolithic SAT, possibly with AIG simplification transforms,
for the (typically harder) mask 1 case.</p>

<p>Recommended transformations for the mask 1 case can be set up like this:</p>
@({
 (local (include-book \"centaur/ipasir/ipasir-backend\" :dir :system))
 (local (include-book \"centaur/aignet/transforms\" :dir :system))
 (local (defun transforms-config ()
          (declare (Xargs :guard t))
          #!aignet
          (list (make-observability-config)
                (make-balance-config :search-higher-levels t
                                     :search-second-lit t)
                (change-fraig-config *fraig-default-config*
                                     :random-seed-name 'my-random-seed
                                     :ctrex-queue-limit 32
                                     :sim-words 1
                                     :ctrex-force-resim nil
                                     :ipasir-limit 1)
 
                (change-fraig-config *fraig-default-config*
                                     :random-seed-name 'my-random-seed2
                                     :ctrex-queue-limit 32
                                     :ipasir-limit 25))))
 (local (defattach fgl-aignet-transforms-config transforms-config))
})
"
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  (equal x y)
  ///
  (disable-definition solve-lane-by-lane-masked+)
  (local (defthm unsigned-byte-p-forward
           (implies (unsigned-byte-p n x)
                    (and (natp n) (natp x)))
           :rule-classes :forward-chaining))
  (local (defthmd logcdr-equal-when-logcar-equal
           (implies (equal (logcar x) (logcar y))
                    (equal (equal (logcdr x) (logcdr y))
                           (equal (ifix x) (ifix y))))
           :hints (("goal" :use ((:instance bitops::logcons-destruct (x x))
                                 (:instance bitops::logcons-destruct (x y)))
                    :in-theory (disable bitops::logcons-destruct)))))
  (local (defthm logtail-equal-when-loghead-equal
           (implies (equal (loghead width x) (loghead width y))
                    (equal (equal (logtail width x) (logtail width y))
                           (equal (ifix x) (ifix y))))
           :hints(("Goal" :in-theory (enable bitops::ihsext-inductions
                                             bitops::ihsext-recursive-redefs
                                             logcdr-equal-when-logcar-equal)))))
  (def-fgl-rewrite solve-lane-by-lane-masked+-impl
    (implies (and (syntaxp (posp width))
                  (integerp x) (integerp y))
             (equal (solve-lane-by-lane-masked+ x y mask width)
                    (if (and (check-int-endp x-endp x)
                             (check-int-endp y-endp y))
                        (equal x y)
                      (b* ((config0 (syntax-bind config0 (g-concrete
                                                               (solve-lane-by-lane-masked+-config0))))
                           (config1 (syntax-bind config1 (g-concrete
                                                               (solve-lane-by-lane-masked+-config1)))))
                        (acl2::and* (fgl-validity-check config1
                                                             (implies (logbitp 0 mask)
                                                                      (equal (loghead width x)
                                                                             (loghead width y))))
                                    (fgl-validity-check config0
                                                             (implies (not (logbitp 0 mask))
                                                                      (equal (loghead width x)
                                                                             (loghead width y))))
                                    (solve-lane-by-lane-masked+ (logtail width x) (logtail width y)
                                                                (logcdr mask) width))))))
    :hints(("Goal" :in-theory (e/d (fgl-sat-check acl2::and*)
                                   (unsigned-byte-p))))))

(define ipasir-sat-limit100 ()
  (make-fgl-ipasir-config
   :ipasir-callback-limit 100))

(define monolithic-sat-with-transforms ()
  (make-fgl-satlink-monolithic-sat-config :transform t))
  

(defattach
  (solve-lane-by-lane-masked+-config1 monolithic-sat-with-transforms)
  (solve-lane-by-lane-masked+-config0 ipasir-sat-limit100))

(defattach solve-lane-by-lane-config monolithic-sat-with-transforms)






