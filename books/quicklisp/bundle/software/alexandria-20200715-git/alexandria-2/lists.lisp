(in-package :alexandria-2)

(defun delete-from-plist* (plist &rest keys)
  "Just like REMOVE-FROM-PLIST, but this version may destructively modify the
provided PLIST.
The second return value is an alist of the removed items, in unspecified order."
  ;; TODO: a plist?
  (declare (optimize speed))
  (loop with head = plist
        with tail = nil   ; a nil tail means an empty result so far
        with kept = ()
        for (key . rest) on plist by #'cddr
        do (assert rest () "Expected a proper plist, got ~S" plist)
           (if (member key keys :test #'eq)
               ;; skip over this pair
               (let ((next (cdr rest)))
                 (push (cons key (car rest))
                       kept)
                 (if tail
                     (setf (cdr tail) next)
                     (setf head next)))
               ;; keep this pair
               (setf tail rest))
        finally (return (values head kept))))
