; Utilities about conjunctions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
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
(include-book "kestrel/terms-light/get-conjuncts" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

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

;; Return a list of terms equivalent (in the sense of IFF -- or perhaps EQUAL?)
;; to the conjunction of TERMS, by flattening (translated) conjunctions (which
;; will be calls to IF).  TODO: Also handle (if x 'nil y).  TODO: Look at
;; get-conjuncts-of-term (or even get-conjuncts-of-term2) for an even more
;; aggressive version of this tool (just use that one?).
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
