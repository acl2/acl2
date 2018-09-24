; VL Verilog Toolkit
; Copyright (C) 2008-2015 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../mlib/ctxexprs")
(include-book "../mlib/writer")
(include-book "../mlib/strip")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable (tau-system))))


(defxdoc leftright-check
  :parents (vl-lint)
  :short "Check for strange expressions like @('A [op] A')."

  :long "<p>This is a heuristic for generating warnings, inspired by PVS
Studio.  It has found a few pretty minor things that we were able to clean up,
and also found one interesting copy/paste bug.</p>

<p>We look for identical sub-expressions on the left and right of most binary
operations, for instance @('A | A') and @('A == A').  It is usually pretty
strange to write such an expression, and sometimes these indicate copy/paste
errors.  We do similar checking for the then- and else-branches of @('?:')
operators.</p>

<p>We also look for part-selects that use the same expressions for both
indices, e.g., @('foo[3:3]'), but these are somewhat more common and minor, and
sometimes result from macros or parameterized modules, so we generally think
these are pretty minor and uninteresting.</p>")

(local (xdoc::set-default-parents leftright-check))

(defenum vl-op-ac-p
  (:vl-binary-plus
   ;; We previously included :vl-binary-times here, but after this warning came
   ;; up a few times, we decided that we don't want to warn about A*A.
   ;; :vl-binary-times
   :vl-binary-logand
   :vl-binary-logor
   :vl-binary-bitand
   :vl-binary-bitor
   :vl-binary-xor
   :vl-binary-xnor)
  :short "Recognizes the associative/commutative binary @(see vl-op-p)s.")

(defthm vl-binaryop-p-when-vl-op-ac-p
  (implies (vl-op-ac-p x)
           (vl-binaryop-p x))
  :hints(("Goal" :in-theory (enable vl-op-ac-p))))

;; (defthm vl-op-arity-when-vl-op-ac-p
;;   (implies (vl-op-ac-p x)
;;            (equal (vl-op-arity x) 2))
;;   :hints(("Goal" :in-theory (enable vl-op-ac-p))))

(defthm vl-exprlist-count-of-append
  (equal (vl-exprlist-count (append a b))
         (+ -1 (vl-exprlist-count a)
            (vl-exprlist-count b)))
  :hints(("Goal" :in-theory (enable vl-exprlist-count append))))

(local
 (defthm vl-expr-count-of-binary
   (implies (vl-expr-case x :vl-binary)
            (equal (vl-expr-count x)
                   (+ 5
                      (vl-atts-count (vl-binary->atts x))
                      (vl-expr-count (vl-binary->left x))
                      (vl-expr-count (vl-binary->right x)))))
   :hints (("goal" :expand ((vl-expr-count x))))
   :rule-classes :linear))

(define vl-collect-ac-args
  :short "Collect the nested arguments to an associative/commutative operator."
  ((op vl-binaryop-p "An associative and commutative binary operators.")
   (x  vl-expr-p     "An expression, typically it is an argument to @('op')."))
  :returns (args vl-exprlist-p)
  :guard (vl-op-ac-p op)
  :measure (vl-expr-count x)
  :long "<p>If @('x') is itself an @('op') expression, we recursively collect
up the ac-args of its sub-expressions.  Otherwise we just collect @('x').  For
instance, if @('op') is @('|') and @('x') is:</p>

@({
 (a | (b + c)) | (d & e)
})

<p>Then we return a list with three expressions: @('a'), @('b + c'), and @('d &
e').</p>"
  (b* ((x (vl-expr-fix x)))
    (vl-expr-case x
      :vl-binary
      (if (vl-binaryop-equiv x.op op)
          (append (vl-collect-ac-args op x.left)
                  (vl-collect-ac-args op x.right))
        (list x))
      :otherwise
      (list x)))
  ///
  (defthm vl-exprlist-count-of-collect-ac-args
    (and (<= (vl-exprlist-count (vl-collect-ac-args op x))
             (+ 2 (vl-expr-count x)))
         (implies (vl-expr-case x
                    :vl-binary (vl-binaryop-equiv x.op op)
                    :otherwise nil)
                  (< (vl-exprlist-count (vl-collect-ac-args op x))
                     (vl-expr-count x))))
    :hints(("Goal" :induct (vl-collect-ac-args op x)
            :in-theory (e/d ()
                            ((:d vl-collect-ac-args)
                             (tau-system)))
            :expand ((vl-collect-ac-args op x)
                     (:free (a b) (vl-exprlist-count (cons a b)))))
           (and stable-under-simplificationp
                '(:expand ((vl-expr-count x)))))
    :rule-classes :linear))

(local (defthm hons-duplicated-members-when-no-duplicatesp-equal
         (implies (no-duplicatesp-equal x)
                  (equal (hons-duplicated-members x)
                         nil))
         :hints(("Goal"
                 :do-not-induct t
                 :do-not '(generalize fertilize)
                 :in-theory (disable acl2::member-equal-of-hons-duplicated-members)
                 :use ((:instance acl2::member-equal-of-hons-duplicated-members
                        (acl2::a (car (hons-duplicated-members x)))
                        (acl2::x x)))))))

(local
 ;; Jared FROWN
 (std::deflist vl-exprlist-p (x)
   (vl-expr-p x)
   :true-listp t :elementp-of-nil nil))

(local (defthm vl-exprlist-p-of-hons-duplicated-members
         (implies (vl-exprlist-p x)
                  (vl-exprlist-p (hons-duplicated-members x)))))

(define vl-leftright-exprlist-duplicates ((x vl-exprlist-p))
  :guard (true-listp x)
  :short "Optimized duplicate expression gatherer for leftright checking."
  :long "<p>Originally I just used duplicated-members to check for duplicates.
Profiling revealed that this was expensive.  To speed it up, I made a
benchmark out of some real calls of duplicated-members for leftright checking.
Out of 396,966 calls, 396,945 of them (99.99+%) had no duplicated members.
Furthermore, short lists are extremely common:</p>

<ul>
<li>150,302 of them have only 2 elements (37%)</li>
<li>45,301 of them have only 3 elements (11%)</li>
<li>31,930 of them have only 4 elements (8%)</li>
<li>25,516 of them have only 5 elements (6%)</li>
</ul>

<p>However, there are occasionally very long lists with over 600+ members.
This function is just an optimized alternative to duplicated-members that seems
to perform well on this kind of data set.  We gain significant performance out
of this function by memoizing @(see vl-expr-strip).</p>"
  :enabled t

  (mbe :logic (hons-duplicated-members (vl-exprlist-fix x))
       :exec
       (b* (((when (longer-than-p 25 x))
             (hons-duplicated-members x))
            ;; Short list.
            ((when (no-duplicatesp-equal x))
             nil))
         ;; Not unique, so actually compute it.
         (hons-duplicated-members x))))

;; [Jared] bozo why is this suddenly needed???
(local (defthm true-listp-of-vl-exprlist-strip
         (true-listp (vl-exprlist-strip x))
         :hints(("Goal"
                 :induct (len x)
                 :expand ((vl-exprlist-strip x))
                 :in-theory (enable vl-exprlist-strip)))))

;; BOZO we are repeatedly stripping the expression -- consider not doing that.

(fty::defvisitor-template vl-expr-leftright-template
  ((x      :object)
   (indexy booleanp)
   (ctx    vl-context1-p))
  :returns
  (warnings (:join (append warnings1 warnings)
             :tmp-var warnings1
             :initial nil)
            vl-warninglist-p)

  :type-fns ((vl-expr vl-expr-leftright-check1))

  :prod-fns
  ;; Forcibly set indexy Whenever we descend into an index position
  ((vl-hidindex          (indices vl-exprlist-leftright-check-indices))
   (vl-plusminus         (base vl-expr-leftright-check-index)
                         (width vl-expr-leftright-check-index))
   (vl-range             (msb vl-expr-leftright-check-index)
                         (lsb vl-expr-leftright-check-index))
   (vl-arrayrange-index  (expr vl-expr-leftright-check-index))
   (vl-valuerange-single (expr vl-expr-leftright-check-index))
   (vl-slicesize-expr    (expr vl-expr-leftright-check-index))
   (vl-casttype-size     (size vl-expr-leftright-check-index))
   (vl-index             (indices vl-exprlist-leftright-check-indices))
   (vl-multiconcat       (reps vl-expr-leftright-check-index)))


  :renames ((vl-expr vl-expr-leftright-check-aux))

  :fnname-template <type>-leftright-check)

(local (defthm true-listp-of-vl-exprlist-strip
         (true-listp (vl-exprlist-strip x))
         :hints (("goal" :induct (len x)
                  :expand (vl-exprlist-strip x)))))

(local (in-theory (disable acl2::member-of-cons
                           (:t append))))

(fty::defvisitor vl-expr-leftright
  :type expressions-and-datatypes
  :template vl-expr-leftright-template

  :measure (two-nats-measure :count 0)

  (define vl-exprlist-leftright-check-indices ((x vl-exprlist-p)
                                               (indexy booleanp)
                                               (ctx vl-context1-p))
    :inline t
    :returns (warnings vl-warninglist-p)
    :measure (two-nats-measure (vl-exprlist-count x) 1)
    (declare (ignore indexy))
    (vl-exprlist-leftright-check x t ctx))

  (define vl-expr-leftright-check-index ((x vl-expr-p)
                                         (indexy booleanp)
                                         (ctx vl-context1-p))
    :inline t
    :returns (warnings vl-warninglist-p)
    :measure (two-nats-measure (vl-expr-count x) 2)
    (declare (ignore indexy))
    (vl-expr-leftright-check1 x t ctx))


  (define vl-expr-leftright-check1
    ((x      vl-expr-p
             "Expression we are considering.")
     (indexy booleanp
             "Heuristic info.  We set this to true when we've gone into an
              index-like expression, e.g., the @('3') in @('foo[3]'), the
              replication amount in a multiple concatenation, or similar sorts
              of contexts.  In such a context, we suppress warnings about
              @('A+A'), @('A-A'), and @('A*A'), because they are occasionally
              useful in indexing arithmetic.")
     (ctx    vl-context1-p
             "Context where the expression occurs."))

    :short "Search for strange expressions like @('A [op] A')."
    :long "<p>We search through the expression @('x') for sub-expressions of the
form @('A [op] A'), and generate a warning whenever we find one.  The @('ctx')
is a @(see vl-context1-p) that says where @('x') occurs, for more helpful
warnings.  We also use it to suppress warnings in certain cases.</p>"



    :measure (two-nats-measure (vl-expr-count x) 1)
    ;; :hints(("Goal" :in-theory (disable (force))))))
    :returns (warnings vl-warninglist-p)

    (b* ((ctx (vl-context1-fix ctx))
         (x (vl-expr-fix x)))
      (vl-expr-case x

        :vl-qmark
        (let ((subwarnings (vl-expr-leftright-check-aux x indexy ctx)))
          (if (equal (vl-expr-strip x.then)
                     (vl-expr-strip x.else))
              ;; If we find FOO ? BAR : BAR, that's pretty weird and we should
              ;; warn about it.
              (cons (make-vl-warning
                     :type :vl-warn-leftright
                     :msg "~a0: found an expression of the form FOO ? BAR : BAR, ~
                        which is odd: ~a1."
                     :args (list ctx x)
                     :fatalp nil
                     :fn __function__)
                    subwarnings)
            subwarnings))

        :vl-binary
        (b* (((when (vl-op-ac-p x.op))
              ;; For associative commutative ops, we will be very smart.  We will
              ;; collect up *all* the args and see if there are any duplicates.
              ;; This lets us find things like `foo & bar & baz & foo`, even
              ;; though the occurrences of `foo` are far apart.
              (b* ((subexprs (append (vl-collect-ac-args x.op x.left)
                                     (vl-collect-ac-args x.op x.right)))
                   (subexprs-fix (vl-exprlist-strip subexprs))
                   (dupes        (vl-leftright-exprlist-duplicates subexprs-fix))
                   ((unless dupes)
                    ;; Fine, keep going to check subexpressions.
                    ;; BOZO if we instead recurred on subexprs, we would be able
                    ;; to skip down all the way to the frontier.  We'll have to
                    ;; reason about the count, though.
                    (vl-exprlist-leftright-check subexprs indexy ctx))

                   ;; Even though there are some duplicates, we don't necessarily
                   ;; want to warn.
                   ;;
                   ;; For many operators, e.g., A&A, A|A, etc., it doesn't make
                   ;; sense for there to be duplicates and we definitely want to
                   ;; warn.  However, for the arithmetic operators, things like
                   ;; A+A, A*A may well be sensible.  We'll suppress warnings
                   ;; about them in certain cases...
                   (suppress-p
                    (and
                     (member x.op '(:vl-binary-plus
                                    ;; We no longer consider * anyway
                                    ;; :vl-binary-times
                                    ))
                     (or
                      ;; Index computations, especially those involving
                      ;; parameters, often have duplicate arguments.  For
                      ;; instance, we might want to do something like wire
                      ;; [SIZE+SIZE+1:0] foo = ...; Similarly we can end up with
                      ;; expressions involving things like {SIZE+SIZE+1{bar}}.
                      ;; So don't warn about A+A,A-A,A*A in indexy locations.
                      indexy

                      ;; Another special case is for simple operations involving
                      ;; constants.  If we run into something like this:
                      ;;
                      ;; assign baz = foo[3] ? (bar + ( 3 + 1 )) :
                      ;;              foo[2] ? (bar + ( 2 + 1 )) :
                      ;;              foo[1] ? (bar + ( 1 + 1 )) :  <-- here
                      ;;              foo[0] ? (bar + ( 0 + 1 )) :
                      ;;              bar;
                      ;;
                      ;; Then the logic designer is just trying to make more
                      ;; explicit the components being added together, and we
                      ;; don't want to warn about that.  As a heuristic for
                      ;; suppressing these, we'll try to ignore sums where the
                      ;; terms are literally constants.
                      (vl-exprlist-resolved-p dupes))))

                   ((when suppress-p)
                    ;; Fine, no need to warn here, but keep going into
                    ;; subexpressions.
                    (vl-exprlist-leftright-check subexprs indexy ctx)))

                (cons (make-vl-warning
                       :type :vl-warn-leftright
                       :msg "~a0: found an ~s1 expression with duplicated ~
                           arguments, which is ~s2: ~s3"
                       :args (list ctx
                                   (vl-binaryop-string x.op)
                                   (if (eq x.op :vl-binary-plus)
                                       "somewhat odd (why not use wiring to double it?)"
                                     "odd")
                                   (with-local-ps (vl-pp-exprlist
                                                   ;; Sort the dupes to try to make sure
                                                   ;; that duplicate warnings print the same.
                                                   (mergesort dupes))))
                       :fatalp nil
                       :fn __function__)
                      (vl-exprlist-leftright-check subexprs indexy ctx))))

             (subwarns (vl-expr-leftright-check-aux x indexy ctx))

             ((when (member x.op '(:vl-binary-lt :vl-binary-lte
                                   :vl-binary-gt :vl-binary-gte
                                   :vl-binary-eq :vl-binary-neq
                                   :vl-binary-ceq :vl-binary-cne
                                   :vl-implies :vl-equiv
                                   :vl-binary-wildeq :vl-binary-wildneq
                                   ;; these would be weird because they would be no-ops
                                   :vl-binary-assign
                                   :vl-binary-andassign
                                   :vl-binary-orassign
                                   ;; i think lets not warn for other things like a += a
                                   )))
              ;; If we find something like A < A, or A == A, it is very weird
              ;; and we definitely want to warn about it.
              (b* ((warn-p (equal (vl-expr-strip x.left) (vl-expr-strip x.right)))
                   ((unless warn-p)
                    subwarns))
                (cons (make-vl-warning
                       :type :vl-warn-leftright
                       :msg "~a0: found an expression of the form FOO ~s1 FOO, ~
                           which is odd: ~a2."
                       :args (list ctx (vl-binaryop-string x.op) x)
                       :fatalp nil
                       :fn __function__)
                      subwarns)))

             ((when (member x.op '(:vl-binary-shl :vl-binary-ashl)))
              ;; If we find something like A << A or A <<< A, then that is pretty
              ;; weird and we probably want to warn about it.  The one exception
              ;; that I've come across in practice is that logic designers do
              ;; sometimes write 1 << 1 when they are building bit masks.  So as
              ;; a special case, don't warn about 1 << 1.
              (b* ((warn-p (and (equal (vl-expr-strip x.left) (vl-expr-strip x.right))
                                (not (and (vl-expr-resolved-p x.left)
                                          (equal (vl-resolved->val x.left) 1)))))
                   ((unless warn-p)
                    subwarns))
                (cons (make-vl-warning
                       :type :vl-warn-leftright
                       :msg "~a0: found an expression of the form FOO ~s1 FOO, ~
                           which is odd: ~a2."
                       :args (list ctx (vl-binaryop-string x.op) x)
                       :fatalp nil
                       :fn __function__)
                      subwarns)))

             ((when (member x.op '(:vl-binary-shr :vl-binary-ashr
                                   :vl-binary-div :vl-binary-rem)))
              ;; If we find something like A >> A or A >>> A, then that is pretty
              ;; weird and I think we should warn.  I don't think we really want
              ;; to even tolerate things like 1 >> 1 here, because even that is
              ;; weird.  I think it makes sense to treat division and remainder
              ;; the same way, why would you ever divide or mod something by
              ;; itself?
              (b* ((warn-p (equal (vl-expr-strip x.left) (vl-expr-strip x.right)))
                   ((unless warn-p)
                    subwarns))
                (cons (make-vl-warning
                       :type :vl-warn-leftright
                       :msg "~a0: found an expression of the form FOO ~s1 FOO, ~
                           which is odd: ~a2."
                       :args (list ctx (vl-binaryop-string x.op) x)
                       :fatalp nil
                       :fn __function__)
                      subwarns)))

             ((when (member x.op '(:vl-binary-minus)))
              ;; Minus is pretty special.  I think if we find A-A in an index
              ;; position or being applied to constants, it seems pretty
              ;; reasonable.  Otherwise it seems pretty weird, why would you
              ;; subtract something from itself?
              (b* ((warn-p (and (not indexy)
                                (not (vl-expr-resolved-p x.left))
                                (equal (vl-expr-strip x.left)
                                       (vl-expr-strip x.right))))
                   ((unless warn-p)
                    subwarns))
                (cons (make-vl-warning
                       :type :vl-warn-leftright
                       :msg "~a0: found an expression of the form FOO ~s1 FOO, ~
                           which is odd: ~a2."
                       :args (list ctx (vl-binaryop-string x.op) x)
                       :fatalp nil
                       :fn __function__)
                      subwarns))))

          ;; We won't warn for other operators such as :vl-binary-plusassign
          ;; because a += a is basically reasonable.
          subwarns)

        :otherwise (vl-expr-leftright-check-aux x indexy ctx)))))

(define vl-expr-indexy-via-ctx ((expr vl-expr-p)
                                (ctx  vl-context1-p))
  :returns (indexy booleanp :rule-classes :type-prescription)
  (b* ((elem (vl-context1->elem ctx)))
    (case (tag elem)
      (:vl-vardecl
       ;; Horrible godawful hack to treat the msb/lsb exprs from things like
       ;; `wire [msb:lsb] foo` as indexy to begin with.
       (if (member-equal (vl-expr-fix expr)
                         (vl-datatype-allexprs (vl-vardecl->type elem)))
           t
         nil))
      (:vl-paramdecl
       ;; Similarly horrible hack, treat all expressions from parameters as
       ;; being indexy.
       t)
      (otherwise
       nil))))

(define vl-expr-leftright-check ((x vl-expr-p)
                                 (ctx vl-context1-p))
  :returns (warnings vl-warninglist-p)
  (vl-expr-leftright-check1
   x (vl-expr-indexy-via-ctx x ctx) ctx))


(def-expr-check leftright-check
  :formals (x.expr x.ctx)
  :ctx-included-in-warnings t)

;; (define vl-exprctxalist-leftright-check
;;   :short "@(call vl-exprctxalist-leftright-check) extends @(see
;; vl-expr-leftright-check) across an @(see vl-exprctxalist-p)."
;;   ((x vl-exprctxalist-p))
;;   :measure (len (vl-exprctxalist-fix x))
;;   :returns (warnings vl-warninglist-p)
;;   (b* ((x (vl-exprctxalist-fix x))
;;        ((when (atom x))
;;         nil)
;;        ((cons expr ctx) (car x))
;;        (indexy (vl-expr-indexy-via-ctx expr ctx)))
;;     (append (vl-expr-leftright-check expr indexy ctx)
;;             (vl-exprctxalist-leftright-check (cdr x)))))

;; (define vl-module-leftright-check
;;   :short "@(call vl-module-leftright-check) carries our our @(see
;; leftright-check) on all the expressions in a module, and adds any resulting
;; warnings to the module."
;;   ((x vl-module-p))
;;   :returns (new-x vl-module-p)
;;   (b* ((ctxexprs     (vl-module-ctxexprs x))
;;        (new-warnings (vl-exprctxalist-leftright-check ctxexprs)))
;;     (change-vl-module x
;;                       :warnings (append new-warnings
;;                                         (vl-module->warnings x)))))

;; (defprojection vl-modulelist-leftright-check ((x vl-modulelist-p))
;;   :returns (new-x vl-modulelist-p)
;;   (vl-module-leftright-check x))

;; (define vl-design-leftright-check ((x vl-design-p))
;;   :returns (new-x vl-design-p)
;;   (b* (((vl-design x) x)
;;        (new-mods (vl-modulelist-leftright-check x.mods)))
;;     (clear-memoize-table 'vl-expr-strip)
;;     (change-vl-design x :mods new-mods)))






