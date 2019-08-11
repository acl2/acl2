; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(verify-termination equal-x-constant) ; and guards

(verify-termination match-tests-and-bindings
  (declare (xargs :verify-guards nil)))

; Start proof for (verify-guards match-tests-and-bindings).

(local
 (defthm symbol-doublet-listp--mv-nth-1-match-tests-and-bindings
   (implies (symbol-doublet-listp bindings)
            (symbol-doublet-listp
             (mv-nth 1 (match-tests-and-bindings x pat tests bindings))))))

(local
 (defthm cdr-assoc-equal-type-for-symbol-doublet-listp
   (implies (symbol-doublet-listp x)
            (or (consp (cdr (assoc-equal pat x)))
                (null (cdr (assoc-equal pat x)))))
   :rule-classes :type-prescription))

(local
 (defthm assoc-equal-type-for-symbol-doublet-listp
   (implies (symbol-doublet-listp x)
            (or (consp (assoc-equal pat x))
                (null (assoc-equal pat x))))
   :rule-classes :type-prescription))

(local
 (defthm symbol-doublet-listp-forward-to-symbol-alistp
   (implies (symbol-doublet-listp bindings)
            (symbol-alistp bindings))
   :rule-classes :forward-chaining))

(local
 (defthm cdr-preserves-character-listp
   (implies (character-listp x)
            (character-listp (cdr x)))))

(verify-guards match-tests-and-bindings)

; Lemma for match-clause guard verification:
(local
 (defthm true-listp-car-match-tests-and-bindings
   (implies (true-listp tests)
            (true-listp (car (match-tests-and-bindings x pat tests bindings))))))

(verify-termination match-clause) ; and guards

(verify-termination match-clause-list) ; and guards

