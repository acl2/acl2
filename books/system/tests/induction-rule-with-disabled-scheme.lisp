; Copyright (C) 2020, Northeastern University
; Written by Pete Manolios
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; [Note from Matt Kaufmann: I added this book with permission from Pete
; Manolios, who sent me the events below in an email 2/12/2020.  It motivated
; the change reported in :doc note-8-3 that no longer requires enabling
; built-in induction runes when an induction rule is applied.  Before that
; change, the final THM failed.]

(in-package "ACL2")

; Version of append
(defun aapp (x y)
  (declare (xargs :guard (and (true-listp x) (true-listp y))))
  (if (endp x)
      y
    (cons (car x) (aapp (cdr x) y))))

; Definition rule to limit aapp expansion
(defthm aapp-definition-rule
  (implies (and (true-listp x)
                (true-listp y))
           (equal (aapp x y)
                  (if (endp x)
                      y
                    (cons (car x) (aapp (cdr x) y)))))
  :rule-classes ((:definition :controller-alist ((aapp t nil)))))

; Induction scheme I want
(defthm aapp-induction t
  :rule-classes
  ((:induction :pattern (aapp x y )
               :condition (and (true-listp x) (true-listp y))
               :scheme (aapp x y))))

; Disable default induction scheme & definition and true-listp
(in-theory (disable (:definition aapp)
                    (:induction aapp)
                    (:induction true-listp)))

; Now, aapp-induction is enabled, so I want to use that induction scheme, but I do not want to enable aapp (the definition rule is enabled) and I don't want to use the default induction scheme either.
(thm (implies (and (true-listp x)
                   (true-listp y))
              (true-listp (aapp x y))))
