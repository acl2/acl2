
(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)


(defun accumulate-to-each (keys val al)
  (declare (xargs :guard t))
  (if (atom keys)
      al
    (b* ((rest (cdr (hons-get (car keys) al))))
      (accumulate-to-each (cdr keys) val
                          (hons-acons (car keys)
                                      (cons val rest)
                                      al)))))

(defun graph-transpose (edges acc)
  ;; This inverts an alist of keys to lists of values, e.g.,
  ;;    key1 -> (val1 val2)
  ;;    key2 -> (val1 val3)
  ;; And inverts it to produce an alist binding each value to all of the keys
  ;; that include it, e.g.,
  ;;    val1 -> (key1 key2)
  ;;    val2 -> (key1)
  ;;    val3 -> (key2)
  (declare (xargs :guard t))
  (cond ((atom edges)
         (b* ((ret (hons-shrink-alist acc nil)))
           (fast-alist-free acc)
           (fast-alist-free ret)
           ret))
        ((atom (car edges))
         ;; Bad alist convention
         (graph-transpose (cdr edges) acc))
        (t
         (graph-transpose (cdr edges)
                          (accumulate-to-each
                           (cdar edges) (caar edges)
                           acc)))))
