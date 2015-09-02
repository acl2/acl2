(in-package "ACL2")

(defthm mv-nth-1-second
  (equal (mv-nth 1 x) (second x)))

(defun lookup (e x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        ((and (consp (car x)) (equal e (caar x))) (car x))
        (t (lookup e (cdr x)))))

(defstobj memo-tbl rslt-tbl)

(defthm rslt-tbl-update-rdx
  (equal (rslt-tbl (update-rslt-tbl r mt)) r))

(in-theory (disable rslt-tbl update-rslt-tbl))

(defun lookup-prev-rslt (call memo-tbl)
  (declare (xargs :stobjs memo-tbl))
  (let ((r (lookup call (rslt-tbl memo-tbl))))
    (if (consp r) (mv t (cdr r)) (mv nil nil))))

(defun update-curr-rslt (call rslt memo-tbl)
  (declare (xargs :stobjs memo-tbl))
  (if (consp call)
      (let ((upd (cons (cons call rslt) (rslt-tbl memo-tbl))))
        (update-rslt-tbl upd memo-tbl))
    memo-tbl))

(defmacro previous-rslt (form)
  `(lookup-prev-rslt (list (quote ,(first form)) ,@(rest form)) memo-tbl))

(defmacro update-rslt (form rslt)
  `(update-curr-rslt (list (quote ,(first form)) ,@(rest form)) ,rslt memo-tbl))

(progn
(defun f (x)
  (declare (xargs :guard t))
  x)
(defun h (x)
  (declare (xargs :guard t))
  x)
(defun f-memo (x memo-tbl)
  (declare (xargs :stobjs memo-tbl))
  (mv x memo-tbl))
(defun h-memo (x memo-tbl)
  (declare (xargs :stobjs memo-tbl))
  (mv x memo-tbl))
(defun f-valid (memo-tbl)
  (declare (xargs :stobjs memo-tbl)
           (ignore memo-tbl))
  t)
(defun h-valid (memo-tbl)
  (declare (xargs :stobjs memo-tbl)
           (ignore memo-tbl))
  t)
(defthm f-valid-implies-f-memo
  (implies (f-valid memo-tbl)
           (and (equal (first (f-memo x memo-tbl)) (f x))
                (f-valid (second (f-memo x memo-tbl))))))
(defthm h-valid-implies-h-memo
  (implies (h-valid memo-tbl)
           (and (equal (first (h-memo x memo-tbl)) (h x))
                (h-valid (second (h-memo x memo-tbl))))))

)

;(defun lgc-fn (fn) (symbol-append fn '-lgc))
;(defun memo-fn (fn) (symbol-appen fn '-memo))
;(defun ok1-fn (fn) (symbol-append fn '-ok1))
;(defun ok-fn (fn) (symbol-append fn '-ok))

;;(defmacro defun-memo (name args body)
;;  `(encapsulate
;;    ()

(defun foo-lgc (x)
  (declare (xargs :guard t))
  (f (h x)))

(defun foo-body (x memo-tbl)
  (declare (xargs :stobjs memo-tbl))
  (mv-let (r memo-tbl) (h-memo x memo-tbl) (f-memo r memo-tbl)))

(defun foo-memo (x memo-tbl)
  (declare (xargs :stobjs memo-tbl))
  (mv-let (exists rslt) (previous-rslt (foo x))
    (if exists (mv rslt memo-tbl)
      (mv-let (r memo-tbl) (foo-body x memo-tbl)
        (let ((memo-tbl (update-rslt (foo x) r)))
          (mv r memo-tbl))))))

(defun foo-ok1 (e)
  (declare (xargs :guard t))
  (and (consp e)
       (let ((f (car e)) (r (cdr e)))
         (and (true-listp f)
              (implies (equal (first f) 'foo)
                       (equal (foo-lgc (second f)) r))))))

(defun foo-ok (r)
  (declare (xargs :guard t))
  (or (atom r)
      (and (foo-ok1 (first r))
           (foo-ok (rest r)))))

(defthm foo-ok-lookup
  (implies (and (foo-ok r)
                (consp (lookup (list 'foo x) r)))
           (equal (cdr (lookup (list 'foo x) r))
                  (foo-lgc x))))

(defun foo-valid (memo-tbl)
  (declare (xargs :stobjs memo-tbl))
  (and (foo-ok (rslt-tbl memo-tbl))
       (f-valid memo-tbl)
       (h-valid memo-tbl)))

(defthm foo-ok-h-memo
  (equal (foo-ok (rslt-tbl (second (h-memo x memo-tbl))))
         (foo-ok (rslt-tbl memo-tbl))))

(defthm foo-ok-f-memo
  (equal (foo-ok (rslt-tbl (second (f-memo x memo-tbl))))
         (foo-ok (rslt-tbl memo-tbl))))

(in-theory (disable f h (f) (h)
                    f-memo h-memo (f-memo) (h-memo)
                    f-valid h-valid (f-valid) (h-valid)))

(defthm foo-valid-implies-foo-memo
  (implies (foo-valid memo-tbl)
           (and (equal (first (foo-memo x memo-tbl)) (foo-lgc x))
                (foo-valid (second (foo-memo x memo-tbl))))))

(defexec foo (x)
  (declare (xargs :guard t))
  (mbe :logic (f (h x))
       :exec (with-local-stobj memo-tbl
                 (mv-let (rslt memo-tbl)
                     (foo-body x memo-tbl)
                   rslt))))

