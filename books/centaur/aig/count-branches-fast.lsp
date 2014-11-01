
#+hons
(progn

  (defparameter *count-branches-to-memo-table*
    (hl-mht))

  (defun count-branches-to (x n)
    (labels
        ((count-branches-to1
          (x)
          (let* ((max (* 2 n))
                 (ar (make-array max))
                 (avrc (cons nil nil))
                 (cnt 0))
            (declare (type (simple-array t (*)) ar)
                     (dynamic-extent ar))
            (labels
                ((outer (x)
                        (labels
                            ((fn (x)
                                 (cond
                                  ((atom x) nil)
                                  ((eq (car x) avrc) nil)
                                  ((eq (car x) (cdr x))
                                   (fn (cdr x)))
                                  (t (setf (aref ar cnt) x)
                                     (setf
                                      (aref ar
                                            (the fixnum (+ 1 cnt)))
                                      (car x))
                                     (setq cnt (the fixnum (+ 2 cnt)))
                                     (if (>= cnt max)
                                         (return-from outer nil))
                                     (fn (car x))
                                     (fn (cdr x))
                                     (rplaca (the cons x) avrc)))))
                          (fn x))))
              (unwind-protect
                  (progn
                    (outer x)
                    (values (if (>= cnt max)
                                nil
                              (floor cnt 2))))
                (loop for i fixnum below cnt by 2 do
                      (rplaca (the cons (aref ar i))
                              (aref ar (the fixnum (+ i 1)))))))))
         (lookup
          (x)
          (when (not *count-branches-to-memo-table*)
            (setq *count-branches-to-memo-table* (hl-mht)))
          (b* (((mv ans present)
                (gethash x *count-branches-to-memo-table*)))
            (if present
                (if (car ans)
                    (if (<= (cdr ans) n)
                        (mv (cdr ans) t)
                      (mv nil t))
                  (if (>= (cdr ans) n)
                      (mv nil t)
                    (mv nil nil)))
              (mv nil nil))))
         (descend
          (x)
          (cond ((atom x) x)
                ((eq (car x) (cdr x))
                 (descend (car x)))
                (t x))))
      (b* ((x (hons-copy x))
           ((mv ans ok)
            (lookup x)))
        (if ok
            ans
          (b* ((dx (descend x))
               ((mv ans ok)
                (lookup dx)))
            (if ok
                ans
              (let* ((ans
                      (count-branches-to1 dx))
                     (mem (if ans (cons t ans) (cons nil n))))
                (setf (gethash x *count-branches-to-memo-table*) mem)
                (setf (gethash dx *count-branches-to-memo-table*) mem)
                ans)))))))

  ;; BOZO really profile this?

  (mf-note-arity 'count-branches-to 2 1)

  (profile-fn 'count-branches-to)

  #+Clozure
  ;; Dirty hack so as to clear the count-branches-to memoize table whenever
  ;; clearing the other memoize tables.  BOZO is this something we need to do?
  (setf (gethash 'count-branches-to *memoize-info-ht*)
        (change memoize-info-ht-entry
                (gethash 'count-branches-to *memoize-info-ht*)
                :tablename '*count-branches-to-memo-table*))
  )
