#|
  Book:      vector-comp-canon
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Lee Pike, Galois Connections, Inc. <leepike@galois.com>
|#

(in-package "ACL2")

(include-book "data-structures/number-list-defuns" :dir :system)

(encapsulate ()

(local (include-book "data-structures/list-defthms" :dir :system))

(defun ascending-sorted (l)
  "Recognize an ascending list of numbers."
  (cond ((endp l) t)
	((endp (cdr l)) t)
	(t (and (equal (car l) (- (cadr l) 1))
		(ascending-sorted (cdr l))))))

(defun nats-listp (lst)
  (and (natural-listp lst)
       (ascending-sorted lst)))

(defthmd nats-list-nth
  (implies (and (nats-listp lst)
		(natp i)
		(< i (len lst)))
	   (equal (nth i lst) (+ i (car lst)))))


)
