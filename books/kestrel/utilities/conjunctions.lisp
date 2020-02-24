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

;; conjunct and item are untranslated terms.  The conjunct is conjoined in (at the end) of item.
(defund add-conjunct-to-item (conjunct item)
  (declare (xargs :guard t))
  (if (or (equal conjunct *t*)
          (equal conjunct 't))
      item
    (if (or (equal item *t*)
            (equal item 't))
        conjunct
      (if (and (call-of 'and item)
               (true-listp item) ;for the guard proof
               )
          `(and ,@(fargs item) ,conjunct)
        `(and ,item ,conjunct)))))

;returns a list, the conjunction of whose elements is equivalent (equal or iff?) to hyp
;todo: rename to something like get-conjuncts?
(defun get-conjuncts (hyp)
  (declare (xargs :guard (pseudo-termp hyp)))
  (if (atom hyp)
      (list hyp)
    (if (and (eq 'if (car hyp)) ;(if x y nil) => (and x y)
             (equal *nil* (fourth hyp)))
        (append (get-conjuncts (second hyp))
                (get-conjuncts (third hyp)))
      (list hyp))))

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
