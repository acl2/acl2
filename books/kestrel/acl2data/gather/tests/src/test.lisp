; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; This is adapted from a theorem from :mini-proveall.

(defthm ordered-symbol-alistp-remove1-assoc-eq-test
  (implies (and (ordered-symbol-alistp l)
                (symbolp key)
                (assoc-eq key l))
           (ordered-symbol-alistp (remove1-assoc-eq key l)))
  :hints (("Goal"
           :in-theory (disable ordered-symbol-alistp-remove1-assoc-eq)))
  :rule-classes :forward-chaining)

(defthm app-assoc
  (implies (and (true-listp x)
                (true-listp y)
                (true-listp z))
           (equal (append (append x y) z)
                  (append x y z)))
  :hints (("Goal" :in-theory (disable nth))))
