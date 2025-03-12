; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)

(include-book "binary-tree-defs")
(include-book "heap-order-defs")

(set-induction-depth-limit 0)

(local (include-book "heap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define heap<-all-l
  ((tree binary-tree-p)
   x)
  (declare (xargs :type-prescription (booleanp (heap<-all-l tree x))))
  :parents (binary-tree)
  :short "Check that all members of a tree are @(tsee heap<) some value."
  (or (tree-emptyp tree)
      (and (heap< (tree-head tree) x)
           (heap<-all-l (tree-left tree) x)
           (heap<-all-l (tree-right tree) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fast-nonempty-heapp ((tree binary-tree-p))
  :guard (not (tree-emptyp tree))
  (let ((hash-head (hash (tree-head tree))))
    (declare (type (unsigned-byte 32) hash-head))
    (if (tree-emptyp (tree-left tree))
        (if (tree-emptyp (tree-right tree))
            (mv t hash-head)
          (mv-let (heapp hash-right)
                  (fast-nonempty-heapp (tree-right tree))
            (declare (type (unsigned-byte 32) hash-right))
            (mv (and heapp
                     (heap<-with-hashes (tree-head (tree-right tree))
                                        (tree-head tree)
                                        hash-right
                                        hash-head))
                hash-head)))
      (if (tree-emptyp (tree-right tree))
          (mv-let (heapp hash-left)
                  (fast-nonempty-heapp (tree-left tree))
            (declare (type (unsigned-byte 32) hash-left))
            (mv (and heapp
                     (heap<-with-hashes (tree-head (tree-left tree))
                                        (tree-head tree)
                                        hash-left
                                        hash-head))
                hash-head))
        (mv-let (heapp hash-left)
                (fast-nonempty-heapp (tree-left tree))
          (declare (type (unsigned-byte 32) hash-left))
          (if heapp
              (mv-let (heapp hash-right)
                      (fast-nonempty-heapp (tree-right tree))
                (declare (type (unsigned-byte 32) hash-right))
                (mv (and heapp
                         (heap<-with-hashes (tree-head (tree-left tree))
                                            (tree-head tree)
                                            hash-left
                                            hash-head)
                         (heap<-with-hashes (tree-head (tree-right tree))
                                            (tree-head tree)
                                            hash-right
                                            hash-head))
                    hash-head))
            (mv nil hash-head)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define heapp ((tree binary-tree-p))
  (declare (xargs :type-prescription (booleanp (heapp tree))))
  :parents (binary-tree)
  :short "Check the max heap property."
  (or (tree-emptyp tree)
      (mbe :logic (and (heapp (tree-left tree))
                       (heapp (tree-right tree))
                       (heap<-all-l (tree-left tree)
                                 (tree-head tree))
                       (heap<-all-l (tree-right tree)
                                 (tree-head tree)))
           :exec (b* (((mv heapp -)
                       (fast-nonempty-heapp tree)))
                   heapp))))
