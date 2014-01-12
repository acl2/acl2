#|
  Book:    append-defthms-help
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Lee Pike, Galois Connections, Inc. <leepike@galois.com>
|#

(in-package "ACL2")

(include-book "data-structures/list-defuns" :dir :system)

(encapsulate ()

(local (include-book "data-structures/list-defthms" :dir :system))

(defthm append-update-nth
  (implies  (and (natp i)
                 (< i (len hist))
                 (true-listp hist))
            (equal (cons (car (update-nth i a hist))
                         (append (firstn i (cdr (update-nth i a hist))) l))
                   (append (firstn i hist) (cons a l)))))


)
