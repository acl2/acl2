; ACL2 books on arithmetic
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:
; Matt Kaufmann, Bishop Brock, and John Cowles, with help from Art Flatau
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defsection arithmetic/rational-listp
  :parents (rational-listp)
  :short "Lemmas about @(see rational-listp) available in the
@('arithmetic/rational-listp') book."

  :long "<p>Note: this book is extremely minimal.  You should generally instead
see @(see std/typed-lists/rational-listp).  Note however that this book is part
of a widely-used library of basic arithmetic facts: @('(include-book
\"arithmetic/top\" :dir :system)').</p>"

  (defthm append-preserves-rational-listp
    (implies (true-listp x)
             (equal (rational-listp (append x y))
                    (and (rational-listp x)
                         (rational-listp y)))))

  (defthm rationalp-car-rational-listp
    (implies (and (rational-listp x)
                  x)
             (rationalp (car x)))
    :rule-classes :forward-chaining))
