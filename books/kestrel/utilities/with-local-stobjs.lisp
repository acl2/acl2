; A utility to locally bind multiple stobjs
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in with-local-stojs-tests.lisp

(defund with-local-stobjs-fn-aux (stobjs vars term)
  (declare (xargs :guard (and (symbol-listp stobjs)
                              (symbol-listp vars))))
  (if (endp stobjs)
      term
    (let* ((stobj (first stobjs))
           (rest-stobjs (rest stobjs)))
      `(with-local-stobj ,stobj
         ;; May include some vars that are ultimately ignored, but removing them here would
         ;; involve parsing the ignore declares, so we return ignored vars here and put in
         ;; the declares only in the top-level mv-let:
         (mv-let ,(set-difference-equal vars rest-stobjs)
           ,(with-local-stobjs-fn-aux (rest stobjs) vars term)
           ;; Fake body that just returns the values (except the current stobj) up to the next level:
           (mv ,@(set-difference-equal vars stobjs)) ; no mention of STOBJ here
           )))))

(defund with-local-stobjs-fn (stobjs mv-let-form)
  (declare (xargs :guard (and (symbol-listp stobjs)
                              (consp stobjs)
                              (true-listp mv-let-form)
                              (consp mv-let-form)
                              (eq 'mv-let (car mv-let-form))
                              (<= 3 (len (cdr mv-let-form)))
                              (symbol-listp (cadr mv-let-form)))))
  (let* ((mv-let-args (rest mv-let-form))
         (vars (first mv-let-args))
         (term (second mv-let-args))
         (declares (butlast (cddr mv-let-args) 1))
         (body (car (last mv-let-args))))
    `(with-local-stobj ,(first stobjs)
       (mv-let ,(set-difference-eq vars (rest stobjs)) ; None of the other stobjs are returned by the term here, due to inner calls of with-local-stobj
         ;; These all get fake bodies that are just calls of MV:
         ,(with-local-stobjs-fn-aux (rest stobjs) vars term)
         ,@declares
         ,body ; no mention of any stobjs
         ))))

;; Like with-local-stobj except multiple stobjs can be listed.
(defmacro with-local-stobjs (stobjs mv-let-form)
  (with-local-stobjs-fn stobjs mv-let-form))
