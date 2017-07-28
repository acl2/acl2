; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "subcor-var")
(local (include-book "tools/flag" :dir :system))
(local (include-book "pseudo-termp-lemmas"))

(verify-termination (remove-guard-holders1
                     (declare (xargs :verify-guards nil))))

(local (make-flag remove-guard-holders1))

(local (defthm equal-len-0-rewrite
         (equal (equal 0 (len x))
                (not (consp x)))))

(local (defthm len-mv-nth-1-remove-guard-holders1-lst
         (equal (len (mv-nth 1 (remove-guard-holders1-lst term)))
                (len term))))

(local (defthm pseudo-termp-car-last
         (implies (pseudo-term-listp term)
                  (pseudo-termp (car (last term))))))

(local (defthm-flag-remove-guard-holders1
         (defthm pseudo-termp-remove-guard-holders1
           (implies (pseudo-termp term)
                    (pseudo-termp
                     (mv-nth 1 (remove-guard-holders1 changedp0 term))))
           :flag remove-guard-holders1)
         (defthm pseudo-term-listp-remove-guard-holders1-lst
           (implies (pseudo-term-listp lst)
                    (pseudo-term-listp
                     (mv-nth 1 (remove-guard-holders1-lst lst))))
           :flag remove-guard-holders1-lst)))

(verify-guards remove-guard-holders1) ; and remove-guard-holders1-lst

(verify-termination remove-guard-holders) ; and guards
