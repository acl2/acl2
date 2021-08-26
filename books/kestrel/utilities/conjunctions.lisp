; Utilities about conjunctions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; This book contains various utilities relating to conjunctions
;; (represented as ANDs or IF nests).

(include-book "forms")
(include-book "make-and")

;fixme see the built-in function conjoin! that one handles t's and nil's better..
(defun make-conjunction-from-list (lst)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
      *t*
    (if (endp (rest lst))
        (first lst)
      `(if ,(first lst)
           ,(make-conjunction-from-list (rest lst))
         'nil))))

;; Conjoin CONJUNCT to ITEM, adding it as the last conjunct (in case its guard
;; requires ITEM to be true), unless it is already clearly present as a
;; conjunct.  CONJUNCT and ITEM are untranslated terms.
(defund add-conjunct-to-item (conjunct item)
  (declare (xargs :guard t))
  (if (or (equal conjunct *t*)
          (eq conjunct 't))
      ;; Special case (conjoining t has no effect):
      item
    (if (or (equal item *t*)
            (eq item 't))
        ;; Special case (item as just "true"):
        conjunct
      (if (and (call-of 'and item)
               (true-listp item) ;for the guard proof
               )
          ;; Special case (avoid creating a nested AND):
          `(and ,@(fargs item) ,conjunct)
        `(and ,item ,conjunct)))))

;; Returns a list, the conjunction of whose elements is equivalent to TERM.
;; Preserves the order of the conjuncts, which can matter because an AND is
;; typically equal to its last value, if all values are non-nil.  Does not
;; remove duplicates.  Does not handle negations specially.
;; TODO: Consider having this return the empty list if term is *T*.
(defun get-conjuncts (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (eq 'if (car term)) ; (if x y 'nil) is (and x y)
           (equal *nil* (fourth term)))
      (append (get-conjuncts (second term))
              (get-conjuncts (third term)))
    (list term)))

;ex: (get-conjuncts '(IF (IF X (IF Y Z 'NIL) 'NIL) W 'NIL))

(defthm pseudo-term-listp-of-get-conjuncts
  (implies (pseudo-termp term)
           (pseudo-term-listp (get-conjuncts term))))

;; Return a list of terms equivalent (in the sense of IFF -- or perhaps EQUAL?)
;; to the conjunction of TERMS, by flattening (translated) conjunctions (which
;; will be calls to IF).  TODO: Also handle (if x 'nil y).  TODO: Look at
;; get-conjuncts-of-term for an even more aggressive version of this tool (just
;; use that one?).
(defun get-conjuncts-list (terms)
  (declare (xargs :guard (pseudo-term-listp terms)))
  (if (endp terms)
      nil
    (append (get-conjuncts (first terms)) ;todo avoid appending a singleton list here in the common case
            (get-conjuncts-list (rest terms)))))

(defthm pseudo-term-listp-of-get-conjuncts-list
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (get-conjuncts-list terms))))

;test: (get-conjuncts-list '(a b (if c d 'nil) (if (if e f 'nil) (if g h 'nil) 'nil)))
