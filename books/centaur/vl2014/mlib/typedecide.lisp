; VL 2014 -- VL Verilog Toolkit, 2014 Edition
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

(in-package "VL2014")
(include-book "hid-tools")
(include-book "range-tools")
(include-book "syscalls")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable member-equal-when-member-equal-of-cdr-under-iff
                           acl2::consp-under-iff-when-true-listp)))

(local (in-theory (disable acl2::hons-assoc-equal-of-cons
                           acl2::member-of-cons
                           integerp-when-natp
                           not nfix acl2::zp-open)))
(local (in-theory (disable (tau-system))))






#|

(trace$
 #!vl (vl-index-typedecide
       :entry (list 'vl-index-typedecide
                    (with-local-ps (vl-pp-expr x)))
       :exit (b* (((list warnings-out type) values))
               (list 'vl-index-typedecide
                     (with-local-ps
                       (vl-print-warnings (butlast warnings-out (len warnings))))
                     type))))





|#

(define vl-index-typedecide ((x        vl-expr-p)
                             (ss       vl-scopestack-p)
                             (ctx     vl-context-p "context")
                             (warnings vl-warninglist-p))
  :returns (mv (new-warnings vl-warninglist-p)
               (type vl-maybe-exprtype-p))
  (b* ((x (vl-expr-fix x))
       (?ctx (vl-context-fix ctx))
       ((mv warning datatype) (vl-index-find-type x ss ctx))
       ((when warning)
        (mv (cons (change-vl-warning warning :fatalp t)
                  (vl-warninglist-fix warnings))
            nil))
       ((mv ok errmsg type) (vl-datatype-exprtype datatype))
       ((unless ok)
        (mv (fatal :type :vl-index-typedecide-fail
                   :msg "~a0: Signedness of datatype failed: ~s1"
                   :args (list ctx errmsg))
            nil)))
    (mv (ok) type))
  ///
  (defrule warning-irrelevance-of-vl-index-typedecide
    (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
             (equal (mv-nth 1 (vl-index-typedecide x ss ctx warnings))
                    (mv-nth 1 (vl-index-typedecide x ss nil nil))))))


(define vl-partselect-typedecide ((x        vl-expr-p)
                             (ss       vl-scopestack-p)
                             (ctx     vl-context-p "context")
                             (warnings vl-warninglist-p))
  :guard (not (equal (vl-expr-kind x) :atom))
  :returns (mv (new-warnings vl-warninglist-p)
               (type vl-maybe-exprtype-p))
  (b* ((x (vl-expr-fix x))
       (?ctx (vl-context-fix ctx))
       ((mv warning datatype) (vl-partselect-expr-type x ss ctx))
       ((when warning)
        (mv (cons (change-vl-warning warning :fatalp t)
                  (vl-warninglist-fix warnings))
            nil))
       ((mv ok errmsg type) (vl-datatype-exprtype datatype))
       ((unless ok)
        (mv (fatal :type :vl-partselect-typedecide-fail
                   :msg "~a0: Signedness of datatype failed: ~s1"
                   :args (list ctx errmsg))
            nil)))
    (mv (ok) type))
  ///
  (defrule warning-irrelevance-vl-partselect-typedecide
    (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
             (equal (mv-nth 1 (vl-partselect-typedecide x ss ctx warnings))
                    (mv-nth 1 (vl-partselect-typedecide x ss nil nil))))))


(define vl-atom-typedecide
  :parents (vl-expr-typedecide)
  :short "Effectively computes the \"self-determined\" type of an atom."
  ((x        vl-expr-p)
   (ss vl-scopestack-p)
   (ctx     vl-context-p)
   (warnings vl-warninglist-p))
  :guard (vl-atom-p x)
  :returns (mv (warnings vl-warninglist-p)
               (type (and (vl-maybe-exprtype-p type)
                          (equal (vl-exprtype-p type) (if type t nil)))))

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p>We compute what the type of the atom @('x') would be if it were in a
self-determined location.  Another way to look at this function is as an
extension of \"origtype\" from constint/weirdint atoms to include identifiers
and strings.</p>

<p>The @('type') we return is a @(see vl-maybe-exprtype-p).  Similarly to @(see
vl-atom-selfsize), we might fail and return @('nil') for the type, perhaps
producing some warnings.</p>"

  (b* ((ctx (vl-context-fix ctx))
       (guts (vl-atom->guts x))

       ((when (vl-fast-constint-p guts))
        (mv (ok) (vl-constint->origtype guts)))

       ((when (vl-fast-weirdint-p guts))
        (mv (ok) (vl-weirdint->origtype guts)))

       ((when (vl-fast-string-p guts))
        (mv (ok) :vl-unsigned))

       ((when (eq (tag guts) :vl-extint))
        (mv (ok) :vl-signed))

       ((unless (or (vl-fast-id-p guts)
                    (vl-fast-hidpiece-p guts)))
        ;; Other kinds of atoms don't get a type.

        ;; [Jared] 2015-01-22.  See the analogous comments in vl-atom-selfsize.
        ;; We used to cause warnings here but that is silly and we shouldn't
        ;; warn.

        ;; (mv (warn :type :vl-typedecide-fail
        ;;           :msg "~a0: Couldn't decide signedness of atom: ~a1"
        ;;           :args (list (vl-context-fix ctx) (vl-expr-fix x)))
        ;;     nil)
        (mv (ok) nil)))

    (vl-index-typedecide x ss ctx warnings))

  ///
  (defrule warning-irrelevance-of-vl-atom-typedecide
    (let ((ret1 (vl-atom-typedecide x ss ctx warnings))
          (ret2 (vl-atom-typedecide x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1) (mv-nth 1 ret2))))))




(define vl-funcall-typedecide ((x vl-expr-p)
                               (ss vl-scopestack-p)
                               (ctx vl-context-p)
                               (warnings vl-warninglist-p))
  :guard (and (not (vl-atom-p x))
              (eq (vl-nonatom->op x) :vl-funcall))
  :returns (mv (warnings vl-warninglist-p)
               (type (and (vl-maybe-exprtype-p type)
                          (iff (vl-exprtype-p type) type))))
  (b* ((ctx (vl-context-fix ctx))
       ((vl-nonatom x) (vl-expr-fix x))
       ((unless (and (consp x.args)
                     (vl-fast-atom-p (first x.args))
                     (vl-funname-p (vl-atom->guts (first x.args)))))
        (raise "Programming error: function call without function name: ~x0" x)
        (mv (warn :type :vl-programming-error
                  :msg "~a0: Function call without function name: ~a1"
                  :args (list ctx x))
            nil))
       (fnname (vl-funname->name (vl-atom->guts (first x.args))))
       (decl (vl-scopestack-find-item fnname ss))
       ((unless (and decl (eq (tag decl) :vl-fundecl)))
        (mv (warn :type :vl-function-not-found
                  :msg "~a0: Function not found: ~a1"
                  :args (list ctx x))
            nil))
       ((vl-fundecl decl))
       ((mv ok errmsg type) (vl-datatype-exprtype decl.rettype))
       ((unless ok)
        (mv (fatal :type :vl-funcall-typedecide-fail
                   :msg "~a0: Signedness of datatype failed: ~s1"
                   :args (list ctx errmsg))
            nil)))
    (mv (ok) type))
  ///
  (defrule warning-irrelevance-of-vl-funcall-typedecide
    (let ((ret1 (vl-funcall-typedecide x ss ctx warnings))
          (ret2 (vl-funcall-typedecide x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))))


(define vl-syscall-typedecide ((x vl-expr-p)
                               (ss vl-scopestack-p)
                               (ctx vl-context-p)
                               (warnings vl-warninglist-p))
  :guard (and (not (vl-atom-p x))
              (eq (vl-nonatom->op x) :vl-syscall))
  :returns (mv (warnings vl-warninglist-p)
               (type (and (vl-maybe-exprtype-p type)
                          (iff (vl-exprtype-p type) type))))
  (declare (ignorable ss ctx))
  (b* ((retinfo (vl-syscall->returninfo x))
       ((unless retinfo)
        (mv (ok) nil))
       ((vl-coredatatype-info retinfo))
       ((unless retinfo.size)
        ;; Could be something like void or a real number!
        (mv (ok) nil))
       (signedp (vl-coredatatype-info->default-signedp retinfo)))
    (mv (ok)
        (if signedp :vl-signed :vl-unsigned)))
  ///
  (defrule warning-irrelevance-of-vl-syscall-typedecide
    (let ((ret1 (vl-syscall-typedecide x ss ctx warnings))
          (ret2 (vl-syscall-typedecide x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))))


(deflist vl-maybe-exprtype-list-p (x)
  (vl-maybe-exprtype-p x))


#|

(trace$
 #!vl (vl-expr-typedecide-aux
       :entry (list 'vl-expr-typedecide-aux
                    x (vl-pps-expr x))
       :exit (b* (((list warnings type) values))
               (list 'vl-expr-typedecide-aux
                     type))))

|#

(with-output :off (event)
  :evisc (:gag-mode (evisc-tuple 3 4 nil nil))
  (defines vl-expr-typedecide-aux
    :flag-local nil
    :parents (vl-expr-typedecide)
    :short "Core of computing expression signedness."

    :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p>These are the same arguments as @(see vl-expr-typedecide) except for
@('mode').  You should probably read @(see expression-sizing-minutia) to
understand the valid modes:</p>

<ul>

<li>In @(':probably-wrong') mode, we treat reduction/logical operations as if
they produce signed values when their argument is signed, and we allow the
types of self-determined operands in conditional operators, shifts, and so
forth to affect the resulting expression type.  We do not think this is how
sizing is supposed to be done, but a Verilog implementation that was based on a
reading of the specification might mistakenly do it this way.</li>

<li>In @(':probably-right') mode, we try to behave like other Verilog systems
and ignore the type of self-determined operands when computing the resulting
types of expressions, and we also treat reduction/logical operations as if they
produce unsigned values.</li>

</ul>"

    :prepwork ((local (in-theory (disable acl2::true-listp-member-equal
                                          acl2::consp-member-equal
                                          vl-warninglist-p-when-not-consp
                                          vl-warninglist-p-when-subsetp-equal
                                          cons-equal
                                          acl2::subsetp-member
                                          (:t member-equal)
                                          (:t vl-nonatom->op)
                                          vl-context-fix-when-vl-context-p))))

    (define vl-expr-typedecide-aux ((x        vl-expr-p)
                                    (ss       vl-scopestack-p)
                                    (ctx      vl-context-p)
                                    (warnings vl-warninglist-p)
                                    (mode     (or (eq mode :probably-wrong)
                                                  (eq mode :probably-right))))
      :verify-guards nil
      :returns (mv (warnings vl-warninglist-p)
                   (type     (and (vl-maybe-exprtype-p type)
                                  (equal (vl-exprtype-p type)
                                         (if type t nil)))
                             :hints ('(:in-theory (disable (:d vl-expr-typedecide-aux)
                                                           (:d vl-exprlist-typedecide-aux))
                                       :expand ((:free (mode)
                                                 (vl-expr-typedecide-aux
                                                  x ss ctx warnings mode)))))))
      :measure (vl-expr-count x)
      :flag :expr
      (b* ((x        (vl-expr-fix x))
           (warnings (vl-warninglist-fix warnings))
           (ctx      (vl-context-fix ctx))

           ((when (vl-fast-atom-p x))  (vl-atom-typedecide x ss ctx warnings))
           ((when (vl-indexexpr-p x))  (vl-index-typedecide x ss ctx warnings))

           (op        (vl-nonatom->op x))
           (args      (vl-nonatom->args x))
           ((when (eq op :vl-funcall)) (vl-funcall-typedecide x ss ctx warnings))
           ((when (eq op :vl-syscall)) (vl-syscall-typedecide x ss ctx warnings))
           ((mv warnings arg-types)
            (vl-exprlist-typedecide-aux args ss ctx warnings mode)))

        (case op

          ((:vl-partselect-colon :vl-partselect-pluscolon :vl-partselect-minuscolon
            :vl-select-colon :vl-select-pluscolon :vl-select-minuscolon)
           ;; These are actually always unsigned
           (vl-partselect-typedecide x ss ctx warnings))

          (( ;; From Verilog-2005 5.5.1, bit-selects, part-selects,
            ;; concatenations, and comparisons always produce unsigned results,
            ;; no matter the signedness of their operands.
            :vl-concat :vl-multiconcat
            :vl-binary-eq :vl-binary-neq :vl-binary-ceq :vl-binary-cne
            :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte

            ;; SystemVerilog-2012 extensions: I believe (although it's hard to
            ;; find good evidence in the spec to support this) that these are
            ;; also producing 1-bit unsigned answers.
            :vl-binary-wildneq :vl-binary-wildeq
            )

           (mv warnings :vl-unsigned))

          ((:vl-unary-plus :vl-unary-minus :vl-unary-bitnot)
           ;; From 5.5.1, I believe these fall into the "all other operators"
           ;; rule and just take on the signedness of their argument.
           (mv warnings (first arg-types)))

          ((:vl-unary-lognot :vl-unary-bitand :vl-unary-bitor
            :vl-unary-nand :vl-unary-nor :vl-unary-xor :vl-unary-xnor)
           (cond ((eq mode :probably-right)
                  ;; We believe the result is always unsigned; see "minutia".
                  ;; If we ever decide this is not right, review the rules in
                  ;; oprewrite that introduce concatenations like !a -> {~(|a)}
                  ;; since they are not supposed to change signs.
                  (mv warnings :vl-unsigned))
                 (t
                  ;; Probably-wrong mode: we act like the operand type matters and
                  ;; treat this like a unary plus or minus.
                  (mv warnings (first arg-types)))))

          ((:vl-binary-logand :vl-binary-logor :vl-implies :vl-equiv)
           (cond ((eq mode :probably-right)
                  ;; We believe the result is always unsigned; see "minutia".
                  (mv warnings :vl-unsigned))
                 (t
                  ;; Probably wrong mode: we act like the operand types matter and
                  ;; treat this like a regular binary op.
                  (b* ((type1 (first arg-types))
                       (type2 (second arg-types))
                       (type  (and type1 type2 (vl-exprtype-max type1 type2))))
                    (mv warnings type)))))

          ((:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div :vl-binary-rem
            :vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor)
           ;; Simple context-determined binary ops.
           (b* ((type1 (first arg-types))
                (type2 (second arg-types))
                (type  (and type1 type2 (vl-exprtype-max type1 type2))))
             (mv warnings type)))

          ((:vl-binary-shr :vl-binary-shl :vl-binary-ashr :vl-binary-ashl :vl-binary-power)
           (cond ((eq mode :probably-right)
                  ;; We believe the second op's type does NOT affect the result
                  ;; type; see "minutia"
                  (mv warnings (first arg-types)))
                 (t
                  ;; Probably-wrong mode: we act like the second op's type matters
                  ;; and treat this like a regular binary op.
                  (b* ((type1 (first arg-types))
                       (type2 (second arg-types))
                       (type  (and type1 type2 (vl-exprtype-max type1 type2))))
                    (mv warnings type)))))

          ((:vl-qmark)
           (b* ((type1 (first arg-types))
                (type2 (second arg-types))
                (type3 (third arg-types)))
             (cond ((eq mode :probably-right)
                    ;; We believe the first op's type does NOT affect the result type;
                    ;; see "minutia".
                    (mv warnings (and type1 type2 type3
                                      (vl-exprtype-max type2 type3))))
                   (t
                    ;; Probably-wrong mode: we allow the first op's type to affect the
                    ;; result type.
                    (mv warnings (and type1 type2 type3
                                      (vl-exprtype-max type1 type2 type3)))))))

          ((:vl-stream-left :vl-stream-right
            :vl-stream-left-sized :vl-stream-right-sized)
           (mv (warn :type :vl-untested-sizing-assumptions
                     :msg "~a0: sizing of streaming concatenations is ~
                         experimental and may not be correct."
                     :args (list ctx))
               :vl-unsigned))

          ((;; Should have handled these above.
            :vl-index :vl-bitselect :vl-hid-dot :vl-scope

            ;; BOZO these might not belong here, but it seems like the
            ;; safest place to put them until they're implemented
            :vl-with-index :vl-with-colon :vl-with-pluscolon :vl-with-minuscolon
            :vl-tagged :vl-binary-cast
            :vl-pattern-multi
            :vl-pattern-type
            :vl-pattern-positional
            :vl-pattern-keyvalue
            :vl-keyvalue

            ;; Sizing just shouldn't encounter these
            :vl-unary-preinc :vl-unary-predec :vl-unary-postinc :vl-unary-postdec
            :vl-binary-assign
            :vl-binary-plusassign :vl-binary-minusassign
            :vl-binary-timesassign :vl-binary-divassign :vl-binary-remassign
            :vl-binary-andassign :vl-binary-orassign :vl-binary-xorassign
            :vl-binary-shlassign :vl-binary-shrassign :vl-binary-ashlassign :vl-binary-ashrassign

            :vl-inside :vl-valuerange :vl-valuerangelist
            )
           (mv warnings nil))

          ((:vl-mintypmax)
           ;; I think it makes no sense to try to assign a type to these.
           (mv warnings nil))

          (otherwise
           (mv warnings (impossible))))))

    (define vl-exprlist-typedecide-aux ((x        vl-exprlist-p)
                                        (ss vl-scopestack-p)
                                        (ctx     vl-context-p)
                                        (warnings vl-warninglist-p)
                                        (mode     (or (eq mode :probably-wrong)
                                                      (eq mode :probably-right))))
      :returns (mv (warnings vl-warninglist-p)
                   (types    vl-maybe-exprtype-list-p
                             :hints ('(:in-theory (disable (:d vl-expr-typedecide-aux)
                                                           (:d vl-exprlist-typedecide-aux))
                                       :expand ((vl-exprlist-typedecide-aux
                                                 x ss ctx warnings mode))))))
      :measure (vl-exprlist-count x)
      :flag :list
      (b* (((when (atom x))
            (mv (ok) nil))
           ((mv warnings car-type)
            (vl-expr-typedecide-aux (car x) ss ctx warnings mode))
           ((mv warnings cdr-type)
            (vl-exprlist-typedecide-aux (cdr x) ss ctx warnings mode)))
        (mv warnings (cons car-type cdr-type))))

    ///
    (local (in-theory (disable member-equal-when-member-equal-of-cdr-under-iff
                               vl-warninglist-p-when-subsetp-equal
                               set::double-containment
                               arg1-exists-by-arity
                               default-car
                               default-cdr
                               vl-exprlist-typedecide-aux
                               vl-expr-typedecide-aux)))

    (defrule vl-exprlist-typedecide-aux-of-cons
      (equal (vl-exprlist-typedecide-aux (cons a x) ss ctx warnings mode)
             (b* (((mv warnings car-type)
                   (vl-expr-typedecide-aux a ss ctx warnings mode))
                  ((mv warnings cdr-type)
                   (vl-exprlist-typedecide-aux x ss ctx warnings mode)))
               (mv warnings (cons car-type cdr-type))))
      :hints (("goal" :expand ((:free (mode) (vl-exprlist-typedecide-aux
                                              (cons a x) ss ctx warnings mode))))))

    (defthm-vl-expr-typedecide-aux-flag
      (defthm len-of-vl-exprlist-typedecide-aux
        (equal (len (mv-nth 1 (vl-exprlist-typedecide-aux x ss ctx warnings mode)))
               (len x))
        :hints ('(:expand ((:free (mode) (vl-exprlist-typedecide-aux x ss ctx warnings mode)))))
        :flag :list)
      :skip-others t)

    (defthm-vl-expr-typedecide-aux-flag
      (defthm true-listp-of-vl-exprlist-typedecide-aux
        (true-listp (mv-nth 1 (vl-exprlist-typedecide-aux x ss ctx warnings mode)))
        :rule-classes :type-prescription
        :hints ('(:expand ((:free (mode) (vl-exprlist-typedecide-aux x ss ctx warnings mode)))))
        :flag :list)
      :skip-others t)

    (local (defthm member-equal-when-member-non-intersecting
             (implies (and (syntaxp (quotep x))
                           (member k y)
                           (syntaxp (quotep y))
                           (not (intersectp-equal x y)))
                      (not (member k x)))
             :hints ((set-reasoning))))


    (local (defthm reduce-member-equal-when-not-member
             (implies (and (syntaxp (quotep x))
                           (not (member k y))
                           (syntaxp (quotep y))
                           (intersectp-equal x y))
                      (iff (member k x)
                           (member k (set-difference-equal x y))))
             :hints ((set-reasoning))))
    (local (defthm equal-when-member-non-member
             (implies (and (syntaxp (quotep v))
                           (member k x)
                           (syntaxp (quotep x))
                           (not (member v x)))
                      (not (equal k v)))))
    (local (defthm member-of-singleton
             (iff (member a (cons x nil))
                  (equal a x))
             :hints(("Goal" :in-theory (enable acl2::member-of-cons)))))
    (local (defthm reduce-member-equal-when-not-equal
             (implies (and (syntaxp (quotep x))
                           (not (equal k v))
                           (syntaxp (quotep v))
                           (member v x))
                      (iff (member k x)
                           (member k (remove-equal v x))))
             :hints ((set-reasoning))))
    (verify-guards vl-expr-typedecide-aux
      :hints(("Goal" :in-theory (e/d (vl-nonatom->op-forward
                                      acl2::hons-assoc-equal-iff-member-alist-keys
                                      vl-op-p
                                      vl-ops-table)
                                     (vl-op-p-of-vl-nonatom->op
                                      acl2::alist-keys-member-hons-assoc-equal
                                      (tau-system)))
              :use VL-OP-P-OF-VL-NONATOM->OP)))

    (local
     (defthm-vl-expr-typedecide-aux-flag
       ;; This is pretty subtle.  The induction scheme that the flag function would
       ;; generate if we tried to directly use warnings and NIL isn't right in the
       ;; list case.  We have to generalize this to an arbitrary warnings1 and
       ;; warnings2.  Then, ACL2's induction heuristic is smart enough to get the
       ;; right scheme, but only when we tell it to consider the flag function for
       ;; both warnings1 and warnings2.  Ugh.  This took a long time to figure out.
       (defthm w0
         (let ((ret1 (vl-expr-typedecide-aux x ss ctx warnings1 mode))
               (ret2 (vl-expr-typedecide-aux x ss ctx warnings2 mode)))
           (equal (mv-nth 1 ret1)
                  (mv-nth 1 ret2)))
         :rule-classes nil
         :flag :expr)
       (defthm w1
         (let ((ret1 (vl-exprlist-typedecide-aux x ss ctx warnings1 mode))
               (ret2 (vl-exprlist-typedecide-aux x ss ctx warnings2 mode)))
           (equal (mv-nth 1 ret1)
                  (mv-nth 1 ret2)))
         :rule-classes nil
         :flag :list)
       :hints(("Goal"
               :do-not '(generalize fertilize)
               :induct (and (vl-expr-typedecide-aux-flag flag x ss ctx warnings1 mode)
                            (vl-expr-typedecide-aux-flag flag x ss ctx warnings2 mode))
               :expand ((:free (mode) (vl-expr-typedecide-aux x ss ctx warnings1 mode))
                        (:free (mode) (vl-expr-typedecide-aux x ss ctx warnings2 mode))
                        (:free (mode) (vl-exprlist-typedecide-aux x ss ctx warnings1 mode))
                        (:free (mode) (vl-exprlist-typedecide-aux x ss ctx warnings2 mode)))))))

    (local (defrule warning-irrelevance-of-vl-exprlist-typedecide-aux-tmp
             (let ((ret1 (vl-exprlist-typedecide-aux x ss ctx warnings mode))
                   (ret2 (vl-exprlist-typedecide-aux x ss ctx nil mode)))
               (implies (syntaxp (not (equal warnings ''nil)))
                        (equal (mv-nth 1 ret1)
                               (mv-nth 1 ret2))))
             :use ((:instance w1 (warnings1 warnings) (warnings2 nil)))))

    (local (flag::def-doublevar-induction vl-expr-typedecide-aux-double-ctx
             :orig-fn vl-expr-typedecide-aux-flag
             :old-var ctx :new-var ctx1))

    (deffixequiv-mutual vl-expr-typedecide-aux
      :hints ('(:in-theory (disable (:d vl-expr-typedecide-aux)
                                    (:d vl-exprlist-typedecide-aux)
                                    warning-irrelevance-of-vl-exprlist-typedecide-aux-tmp)
                :expand ((:free (ss ctx warnings mode)
                          (vl-expr-typedecide-aux x ss ctx warnings mode))
                         (:free (mode)
                          (vl-expr-typedecide-aux (vl-expr-fix x) ss ctx warnings mode))
                         (:free (ss ctx warnings mode)
                          (vl-exprlist-typedecide-aux x ss ctx warnings mode))
                         (:free (mode)
                          (vl-exprlist-typedecide-aux (vl-exprlist-fix x) ss ctx warnings mode))))
              (and stable-under-simplificationp
                   '(:expand ((vl-exprlist-fix x))))))



    (local
     (defthm-vl-expr-typedecide-aux-flag
       ;; This is pretty subtle.  The induction scheme that the flag function would
       ;; generate if we tried to directly use warnings and NIL isn't right in the
       ;; list case.  We have to generalize this to an arbitrary warnings1 and
       ;; warnings2.  Then, ACL2's induction heuristic is smart enough to get the
       ;; right scheme, but only when we tell it to consider the flag function for
       ;; both warnings1 and warnings2.  Ugh.  This took a long time to figure out.
       (defthm w2
         (let ((ret1 (vl-expr-typedecide-aux x ss ctx1 warnings mode))
               (ret2 (vl-expr-typedecide-aux x ss ctx2 warnings mode)))
           (equal (mv-nth 1 ret1)
                  (mv-nth 1 ret2)))
         :rule-classes nil
         :flag :expr)
       (defthm w3
         (let ((ret1 (vl-exprlist-typedecide-aux x ss ctx1 warnings mode))
               (ret2 (vl-exprlist-typedecide-aux x ss ctx2 warnings mode)))
           (equal (mv-nth 1 ret1)
                  (mv-nth 1 ret2)))
         :rule-classes nil
         :flag :list)
       :hints(("Goal"
               :do-not '(generalize fertilize)
               :induct (and (vl-expr-typedecide-aux-flag flag x ss ctx1 warnings mode)
                            (vl-expr-typedecide-aux-flag flag x ss ctx2 warnings mode))
               :expand ((:free (mode) (vl-expr-typedecide-aux x ss ctx1 warnings mode))
                        (:free (mode) (vl-expr-typedecide-aux x ss ctx2 warnings mode))
                        (:free (mode) (vl-exprlist-typedecide-aux x ss ctx1 warnings mode))
                        (:free (mode) (vl-exprlist-typedecide-aux x ss ctx2 warnings mode)))))))

    (defrule warning-irrelevance-of-vl-expr-typedecide-aux
      (let ((ret1 (vl-expr-typedecide-aux x ss ctx warnings mode))
            (ret2 (vl-expr-typedecide-aux x ss nil nil mode)))
        (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
                 (equal (mv-nth 1 ret1)
                        (mv-nth 1 ret2))))
      :use ((:instance w0 (warnings1 warnings) (warnings2 nil))
            (:instance w2 (warnings nil) (ctx1 ctx) (ctx2 nil))))



    (defrule warning-irrelevance-of-vl-exprlist-typedecide-aux
      (let ((ret1 (vl-exprlist-typedecide-aux x ss ctx warnings mode))
            (ret2 (vl-exprlist-typedecide-aux x ss nil nil mode)))
        (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
                 (equal (mv-nth 1 ret1)
                        (mv-nth 1 ret2))))
      :use ((:instance w1 (warnings1 warnings) (warnings2 nil))
            (:instance w3 (warnings nil) (ctx1 ctx) (ctx2 nil))))

    (defrule symbolp-of-vl-expr-typedecide-aux
      (symbolp (mv-nth 1 (vl-expr-typedecide-aux x ss ctx warnings mode)))
      :expand ((:free (warnings mode)
                (vl-expr-typedecide-aux x ss ctx warnings mode)))
      :in-theory (enable (tau-system))
      :rule-classes :type-prescription)

    (defrule vl-exprlist-typedecide-aux-when-atom
      (implies (atom x)
               (equal (vl-exprlist-typedecide-aux x ss ctx warnings mode)
                      (mv (ok) nil)))
      :hints (("goal" :expand ((:free (mode) (vl-exprlist-typedecide-aux x ss ctx warnings mode))))))))



(define vl-expr-typedecide
  :parents (vl-expr-size)
  :short "Computation of expression signedness (main routine)."
  ((x        vl-expr-p)
   (ss vl-scopestack-p)
   (ctx     vl-context-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (type     (and (vl-maybe-exprtype-p type)
                              (equal (vl-exprtype-p type) (if type t nil)))))

  :long "<p><b>Warning</b>: this function should typically only be called by
the @(see expression-sizing) transform.</p>

<p>We determine the signedness of an expression.  This function must
<b>only</b> be used on \"top-level\" and self-determined portions of
expressions.  That is, consider an assignment like:</p>

@({
  assign w = {foo + bar, a + b} | (baz + 1) ;
})

<p>Here, it is legitimate to call @('vl-expr-typedecide') to determine the
signs of:</p>

<ul>
 <li>@('foo + bar'), because it is self-determined,</li>
 <li>@('a + b'), because it is self-determined, and</li>
 <li>@('{foo + bar, a + b} | (baz + 1)'), because it is top-level.</li>
</ul>

<p>But it is <b>not</b> legitimate to try to decide the sign of, @('baz + 1')
in isolation, and doing so could yield an nonsensical result.  For instance, if
@('baz') is signed then, by itself, @('baz + 1') looks like a signed addition.
But concatenations are always unsigned, so in the larger context we can see
that this addition is in fact unsigned.</p>

<p>The @('sign') we return is only a @(see vl-maybe-exprtype-p).  We might
return @('nil') for two reasons.  First, there could be some kind of actual
error with the module or the expression, e.g., the use of a wire which is not
declared; in these cases we add fatal @(see warnings).  But we may also
encounter expressions whose type we do not know how to compute (e.g., perhaps
the expression is an unsupported system call).  In such cases we just return
@('nil') for the sign without adding any warnings.</p>"

  (b* ((x    (vl-expr-fix x))
       (ctx (vl-context-fix ctx))
       ((mv warnings right-type) (vl-expr-typedecide-aux x ss ctx warnings :probably-right))
       ((mv warnings wrong-type) (vl-expr-typedecide-aux x ss ctx warnings :probably-wrong))
       (warnings
        (if (eq right-type wrong-type)
            warnings
          (warn :type :vl-warn-vague-spec
                :msg "~a0: expression ~a1 has a type which is not necessarily ~
                      clear according to the discussion in the Verilog-2005 ~
                      standard.  We believe its type should be ~s2, but think ~
                      it would be easy for other Verilog systems to ~
                      mistakenly interpret the expression as ~s3.  To reduce ~
                      any potential confusion, you may wish to rewrite this ~
                      expression to make its signedness unambiguous.  Some ~
                      typical causes of signedness are plain decimal numbers ~
                      like 10, and the use of integer variables instead of ~
                      regs."
                :args (list ctx x right-type wrong-type)))))
    (mv warnings right-type))

  ///
  (defrule warning-irrelevance-of-vl-expr-typedecide
    (let ((ret1 (vl-expr-typedecide x ss ctx warnings))
          (ret2 (vl-expr-typedecide x ss nil nil)))
      (implies (syntaxp (not (and (equal ctx ''nil) (equal warnings ''nil))))
               (equal (mv-nth 1 ret1)
                      (mv-nth 1 ret2))))))
