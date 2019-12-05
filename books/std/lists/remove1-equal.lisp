; Copyright (C) 2019, Regents of the University of Texas
; Written by Mihir Mehta
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Lemmas about remove1-equal

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defsection std/lists/remove1-equal
  :parents (std/lists remove1)
  :short "Lemmas about @(see remove1) available in the @(see std/lists)
  library."

  (defthm len-of-remove1-equal
    (equal (len (remove1-equal x l))
           (if (member-equal x l)
               (- (len l) 1)
             (len l))))

  (defthm assoc-equal-of-remove1-equal
    (implies
     (and (not (equal key1 nil))
          (not (consp (assoc-equal key1 alist))))
     (not (consp (assoc-equal key1 (remove1-equal x alist)))))
    :rule-classes (:rewrite :type-prescription))

  (defthm member-equal-of-remove1-equal
    (implies (not (equal x1 x2))
             (iff (member-equal x1 (remove1-equal x2 l))
                  (member-equal x1 l))))

  (defthm subsetp-equal-of-remove1-equal-left
    (implies (subsetp-equal x y)
             (subsetp-equal (remove1-equal a x) y))))

(in-theory (disable remove1-equal))
