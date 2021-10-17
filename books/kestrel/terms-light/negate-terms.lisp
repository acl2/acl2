; Apply negate-term to a list of terms
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "negate-term")
(local (include-book "logic-termp"))

(defund negate-terms (terms)
  (declare (xargs :guard (pseudo-term-listp terms)))
  (if (endp terms)
      nil
    (let ((term (first terms)))
      (cons (negate-term term)
            (negate-terms (rest terms))))))

(defthm pseudo-term-listp-of-negate-terms
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (negate-terms terms)))
  :hints (("Goal" :in-theory (enable negate-terms))))

(defthm logic-term-listp-of-negate-terms
  (implies (and (logic-term-listp terms w)
                (arities-okp '((not . 1)) w))
           (logic-term-listp (negate-terms terms) w))
  :hints (("Goal" :in-theory (enable negate-terms))))
