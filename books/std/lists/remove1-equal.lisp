; Copyright (C) 2019, Regents of the University of Texas
; Written by Mihir Mehta
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Lemmas about remove1-equal

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defsection std/lists/remove1-equal
  :parents (std/lists remove1)
  :short "Lemmas about @(see remove1-equal) available in the @(see std/lists)
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
     (not (consp (assoc-equal key1 (remove1-equal x alist)))))))





