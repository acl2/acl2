; Extracting conjuncts from a translated term
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Returns a list, the conjunction of whose elements is equivalent to TERM.
;; Preserves the order of the conjuncts, which can matter because an AND is
;; typically equal to its last value, if all values are non-nil.  Does not
;; remove duplicates.  Does not handle negations specially.
;; TODO: Consider having this return the empty list if term is *T*.
(defund get-conjuncts (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (eq 'if (car term)) ; (if x y 'nil) is (and x y)
           (equal *nil* (fourth term)))
      ;; todo: call union-equal?:
      (append (get-conjuncts (second term))
              (get-conjuncts (third term)))
    (list term)))

;ex: (get-conjuncts '(IF (IF X (IF Y Z 'NIL) 'NIL) W 'NIL))

(defthm pseudo-term-listp-of-get-conjuncts
  (implies (pseudo-termp term)
           (pseudo-term-listp (get-conjuncts term)))
  :hints (("Goal" :in-theory (enable get-conjuncts))))
