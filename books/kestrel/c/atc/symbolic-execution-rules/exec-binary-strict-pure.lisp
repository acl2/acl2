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

(local (include-book "exec-binary-strict-pure-local"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (atc-exec-binary-rules-for-op-gen (binop-mul)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-div)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-rem)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-add)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-sub)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-shl)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-shr)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-lt)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-gt)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-le)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-ge)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-eq)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-ne)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-bitand)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-bitxor)))

(make-event (atc-exec-binary-rules-for-op-gen (binop-bitior)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defsection atc-exec-binary-strict-pure-rules
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
    ,@*atc-exec-mul-events*
    ,@*atc-exec-div-events*
    ,@*atc-exec-rem-events*
    ,@*atc-exec-add-events*
    ,@*atc-exec-sub-events*
    ,@*atc-exec-shl-events*
    ,@*atc-exec-shr-events*
    ,@*atc-exec-lt-events*
    ,@*atc-exec-gt-events*
    ,@*atc-exec-le-events*
    ,@*atc-exec-ge-events*
    ,@*atc-exec-eq-events*
    ,@*atc-exec-ne-events*
    ,@*atc-exec-bitand-events*
    ,@*atc-exec-bitxor-events*
    ,@*atc-exec-bitior-events*
    (defval *atc-exec-binary-strict-pure-rules*
      '(,@*atc-exec-mul-rules*
        ,@*atc-exec-div-rules*
        ,@*atc-exec-rem-rules*
        ,@*atc-exec-add-rules*
        ,@*atc-exec-sub-rules*
        ,@*atc-exec-shl-rules*
        ,@*atc-exec-shr-rules*
        ,@*atc-exec-lt-rules*
        ,@*atc-exec-gt-rules*
        ,@*atc-exec-le-rules*
        ,@*atc-exec-ge-rules*
        ,@*atc-exec-eq-rules*
        ,@*atc-exec-ne-rules*
        ,@*atc-exec-bitand-rules*
        ,@*atc-exec-bitxor-rules*
        ,@*atc-exec-bitior-rules*
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
        (:e binop-bitior)))))
