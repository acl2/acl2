; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "exec-binary-strict-pure-gen")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel ifix-when-integerp
  (implies (integerp x)
           (equal (ifix x)
                  x)))

(defrulel truncate-lemma
  (implies (and (natp a)
                (natp b))
           (and (<= 0
                    (truncate a (expt 2 b)))
                (<= (truncate a (expt 2 b))
                    a)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-binary-strict-pure-rules-generation-ext
  :extension atc-exec-binary-strict-pure-rules-generation

  (define atc-exec-binary-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* ((ops (list (binop-mul)
                    (binop-div)
                    (binop-rem)
                    (binop-add)
                    (binop-sub)
                    (binop-shl)
                    (binop-shr)
                    (binop-lt)
                    (binop-gt)
                    (binop-le)
                    (binop-ge)
                    (binop-eq)
                    (binop-ne)
                    (binop-bitand)
                    (binop-bitxor)
                    (binop-bitior)))
         ((mv names events)
          (atc-exec-binary-rules-gen ops
                                     *nonchar-integer-types**
                                     *nonchar-integer-types**)))
      `(progn
         (defsection atc-exec-binary-strict-pure-rules
           :short "Rules for executing strict pure binary operations."
           :long
           (xdoc::topstring
            (xdoc::p
             "The goal of these rules is to
              rewrite @('(exec-binary-strict-pure op x y)')
              to @('(op-type1-type2 x y)')
              when @('x') has type @('type1'),
              and @('y') has type @('type2').
              We could have a rule for each combination of
              @('op'), @('type1'), and @('type2'),
              but that would lead to 1,600 rules being applicable to
              @('(exec-binary-strict-pure op x y)').
              So we stage the rewriting as follows:")
            (xdoc::ul
             (xdoc::li
              "First, we rewrite @('(exec-binary-strict-pure op x y)')
               to a call @('(exec-binary-strict-pure-of-op x y)'),
               under the hypothesis that @('op') is a specific operator,
               where @('exec-binary-strict-pure-of-op') is one of 16 functions,
               one per binary strict operator.")
             (xdoc::li
              "Next, we rewrite @('(exec-binary-strict-pure-of-op x y)')
               to a call @('(exec-binary-strict-pure-of-op-and-type1 x y)'),
               under the hypothesis that @('x') has type @('type1'),
               where @('exec-binary-strict-pure-of-op-and-type1')
               is one of 10 functions,
               one per supported integer type.")
             (xdoc::li
              "Finally, we rewrite
               @('(exec-binary-strict-pure-of-op-and-type1 x y)')
               to the call @('(op-type1-type2 x y)'),
               under the hypothesis the @('y') has type @('type2'),
               for each of the 10 supported integer types."))
            (xdoc::p
             "Note that the intermediate functions used here
              do not need guard verification."))
           ,@events
           (defval *atc-exec-binary-strict-pure-rules*
             '(,@names
               (:e binop-mul)
               (:e binop-div)
               (:e binop-rem)
               (:e binop-add)
               (:e binop-sub)
               (:e binop-shl)
               (:e binop-shr)
               (:e binop-lt)
               (:e binop-gt)
               (:e binop-le)
               (:e binop-ge)
               (:e binop-eq)
               (:e binop-ne)
               (:e binop-bitand)
               (:e binop-bitxor)
               (:e binop-bitior))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (atc-exec-binary-rules-gen-all))
