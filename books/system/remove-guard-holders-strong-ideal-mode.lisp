; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; WARNING!  Do not include this book lightly when you are using ACL2!  It may
; slow down ACL2 significantly.  See comments in
; remove-guard-holders-strong-1.lisp for discussion, especially about how the
; events below are progress towards putting function remove-guard-holders into
; :logic mode.

(in-package "ACL2")

(include-book "remove-guard-holders-strong-1")

(verify-termination translate-declaration-to-guard1-gen
  (declare (xargs :verify-guards nil)))
(verify-termination translate-declaration-to-guard-gen
  (declare (xargs :verify-guards nil)))
(verify-termination type-expressions-from-type-spec
  (declare (xargs :verify-guards nil)))
(verify-termination syntactically-plausible-lambda-objectp1
  (declare (xargs :verify-guards nil)))

(local
 (defthm syntactically-plausible-lambda-objectp1-small
   (< (acl2-count
       (mv-nth 5
               (syntactically-plausible-lambda-objectp1 edcls
                                                        formals
                                                        ignores
                                                        ignorables
                                                        type-exprs
                                                        satisfies-exprs
                                                        guard)))
      (+ 5
         (acl2-count edcls)
         (acl2-count guard)))
   :hints (("Goal" :in-theory (disable type-expressions-from-type-spec)))
   :rule-classes :linear))

(local (in-theory (disable syntactically-plausible-lambda-objectp1
                           type-expressions-from-type-spec
                           translate-declaration-to-guard-gen
                           conjoin
                           conjoin?
                           )))

(verify-termination syntactically-plausible-lambda-objectp
  (declare (xargs :verify-guards nil)))

(verify-termination possibly-dirty-lambda-objectp)

(verify-termination may-contain-dirty-lambda-objectsp
  (declare (xargs :verify-guards nil)))

(verify-termination executable-badge)
(verify-termination expand-all-lambdas)
(verify-termination find-warrant-function-name)

(verify-termination
  (warrants-for-tamep
   (declare (xargs :measure (acl2-count x))))
  (warrants-for-tamep-functionp
   (declare (xargs :measure (acl2-count fn))))
  (warrants-for-suitably-tamep-listp
   (declare (xargs :measure (acl2-count args)))))

(verify-termination
  (executable-tamep
   (declare (xargs :measure (acl2-count x) :verify-guards nil)))
  (executable-tamep-functionp
   (declare (xargs :measure (acl2-count fn) :verify-guards nil)))
  (executable-suitably-tamep-listp
   (declare (xargs :measure (acl2-count args) :verify-guards nil))))

(verify-termination well-formed-lambda-objectp1)
(verify-termination well-formed-lambda-objectp)
