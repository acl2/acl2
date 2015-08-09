
(in-package "SAT")
(program)
(set-state-ok t)

(include-book "sat-setup")

(defun lookup-NLA (fn not-found-val $sat)
  (declare (xargs :stobjs $sat))
  (getprop fn 'non-list-argp-list not-found-val 'NLA-table (NLA-table $sat)))

(defun set-NLA (fn NLA $sat)
  (declare (xargs :stobjs $sat))
  (update-NLA-table (putprop fn 'non-list-argp-list NLA (NLA-table $sat))
                    $sat))

(defun lookup-possible-sulfa (fn not-found-val $sat)
  (declare (xargs :stobjs $sat))
  (getprop fn 'possible-sulfa not-found-val 'NLA-table (NLA-table $sat)))

(defun set-possible-sulfa (fn NLA $sat)
  (declare (xargs :stobjs $sat))
  (update-NLA-table (putprop fn 'possible-sulfa NLA (NLA-table $sat))
                    $sat))

(defun lookup-executable (fn not-found-val $sat)
  (declare (xargs :stobjs $sat))
  (getprop fn 'executable not-found-val 'props-world (props-world $sat)))

(defun set-executable (fn val $sat)
  (declare (xargs :stobjs $sat))
  (update-props-world (putprop fn 'executable val (props-world $sat))
                      $sat))

(defun lookup-sat-package (fn not-found-val $sat)
  (declare (xargs :stobjs $sat))
  (getprop fn 'sat-package not-found-val 'props-world (props-world $sat)))

(defun set-sat-package (fn val $sat)
  (declare (xargs :stobjs $sat))
  (update-props-world (putprop fn 'sat-package val (props-world $sat))
                      $sat))

;; (lambda <formals> <body>)
(defun lambda-body (fn)
  (caddr fn))

(defun executable-fnp (fn $sat)
  (declare (xargs :stobjs $sat))
  (lookup-executable fn nil $sat))

(defun measure-vars (fn state)
  (cadr (fn-justification fn state)))

;; Return whether a memory entry exists for the
;; function "fn".  If one does, then there will be
;; an "executable" entry.
(defun need-funcp (fn $sat)
  (declare (xargs :stobjs $sat))
  (or (eq 'not-found (lookup-executable fn 'not-found $sat))
      (eq 'not-found (lookup-possible-sulfa fn 'not-found $sat))))

(mutual-recursion
(defun executable-expr-listp (expr-list ok-fn-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp expr-list)
    t)
   ((not (executable-exprp (car expr-list) ok-fn-list $sat))
    nil)
   (t
    (executable-expr-listp (cdr expr-list) ok-fn-list $sat))))

(defun executable-exprp (expr ok-fn-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((or (atom expr) (quotep expr))
    t)
   ((consp (car expr))
    (and (executable-exprp (lambda-body (car expr)) ok-fn-list $sat)
         (executable-expr-listp (cdr expr) ok-fn-list $sat)))
   ((member (car expr) ok-fn-list)
    (executable-expr-listp (cdr expr) ok-fn-list $sat))
   ((executable-fnp (car expr) $sat)
    (executable-expr-listp (cdr expr) ok-fn-list $sat))
   (t nil)))
)

(defun executable-fn-listp (def-fn-list state)
  (cond
   ((endp def-fn-list)
    t)
   ((constrained-fnp (car def-fn-list) state)
    nil)
   (t
    (executable-fn-listp (cdr def-fn-list) state))))

(defun executable-def-fn-listp (def-fn-list body-list $sat state)
  (declare (xargs :stobjs $sat))
  (and (executable-fn-listp def-fn-list state)
       (executable-expr-listp body-list def-fn-list $sat)))

(defun sat-package-fnp (fn $sat)
  (declare (xargs :stobjs $sat))
  (lookup-sat-package fn 't $sat))

(defun atom-in-sat-packagep (x)
  (if (and (symbolp x)
           (string-equal (symbol-package-name x) "SAT"))
      (prog2$ (cw "SAT package symbol found: ~x0~%" x)
              t)
    nil))

(defun sat-package-constp (expr)
  (cond
   ((atom expr)
    (atom-in-sat-packagep expr))
   (t
    (or (sat-package-constp (car expr))
        (sat-package-constp (cdr expr))))))

(mutual-recursion
(defun sat-package-expr-listp (expr-list ok-fn-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp expr-list)
    nil)
   ((sat-package-exprp (car expr-list) ok-fn-list $sat)
    t)
   (t
    (sat-package-expr-listp (cdr expr-list) ok-fn-list $sat))))

(defun sat-package-exprp (expr ok-fn-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((atom expr)
    (atom-in-sat-packagep expr))
   ((quotep expr)
    (sat-package-constp (unquote expr)))
   ((consp (car expr))
    (or (sat-package-exprp (lambda-body (car expr)) ok-fn-list $sat)
        (sat-package-expr-listp (cdr expr) ok-fn-list $sat)))
   ((member (car expr) ok-fn-list)
    (sat-package-expr-listp (cdr expr) ok-fn-list $sat))
   ((sat-package-fnp (car expr) $sat)
    t)
   (t
    (sat-package-expr-listp (cdr expr) ok-fn-list $sat))))
)

(defun sat-package-fn-listp (def-fn-list)
  (cond
   ((endp def-fn-list)
    nil)
   ((atom-in-sat-packagep (car def-fn-list))
    t)
   (t
    (sat-package-fn-listp (cdr def-fn-list)))))

(defun sat-package-def-fn-listp (def-fn-list body-list $sat)
  (declare (xargs :stobjs $sat))
  (or (sat-package-fn-listp def-fn-list)
      (sat-package-expr-listp body-list def-fn-list $sat)))

(defun tail-rev (x ans)
  (if (endp x)
      ans
    (tail-rev (cdr x) (cons (car x) ans))))

(defun duplicate-help (n x ans)
  (if (zp n)
      ans
    (duplicate-help (1- n) x (cons x ans))))

(defun duplicate (n x) (duplicate-help n x nil))

(mutual-recursion

(defun needed-fn-expr (expr ok-fn-list ans $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((or (atom expr) (quotep expr))
    ans)
   ((and (symbolp (car expr))
         (not (member-eq (car expr) ok-fn-list))
         (not (member-eq (car expr) ans))
         (need-funcp (car expr) $sat))
    (needed-fn-list (cdr expr)
                    (cons (car expr) ok-fn-list)
                    (cons (car expr) ans)
                    $sat))
   ((and (consp (car expr)) (eq 'lambda (caar expr)))
    (needed-fn-list (cdr expr)
                    ok-fn-list
                    (needed-fn-expr (lambda-body (car expr))
                                    ok-fn-list
                                    ans
                                    $sat)
                    $sat))
   ((consp (car expr))
    (er hard 'needed-fn-expr
        "Encountered an ill-formed ACL2 expression: ~x0~%"
        expr))
   (t
    (needed-fn-list (cdr expr) ok-fn-list ans $sat))))

;; Return a list of functions in expr-list that do
;; not have mem entries in $sat and are not in ok-fn-list
(defun needed-fn-list (expr-list ok-fn-list ans $sat)
  (declare (xargs :stobjs $sat))
  (if (endp expr-list)
      ans
    (needed-fn-list (cdr expr-list)
                    ok-fn-list
                    (needed-fn-expr (car expr-list)
                                    ok-fn-list
                                    ans
                                    $sat)
                    $sat)))
)

;; Return the set of mutually recursive functions that
;; includes "fn".
(defun def-fn-list (fn state)
  (let ((rec-list
         (getprop fn
                  'acl2::recursivep
                  nil
                  'acl2::current-acl2-world
                  (w state))))
    (if rec-list rec-list (list fn))))

(defun body-list-help (def-fn-list rev-ans state)
  (if (endp def-fn-list)
      (tail-rev rev-ans nil)
    (body-list-help (cdr def-fn-list)
                    (cons (fn-body! (car def-fn-list) state)
                          rev-ans)
                    state)))

(defun body-list (def-fn-list state)
  (body-list-help def-fn-list nil state))

(defun merge-NLAs-help (changed new-NLA old-NLA rev-ans)
  (cond
   ((endp new-NLA)
    (mv changed (tail-rev rev-ans nil)))
   ((car old-NLA)
    (merge-NLAs-help changed (cdr new-NLA) (cdr old-NLA) (cons t rev-ans)))
   ((car new-NLA)
    (merge-NLAs-help t (cdr new-NLA) (cdr old-NLA) (cons t rev-ans)))
   (t
    (merge-NLAs-help changed (cdr new-NLA) (cdr old-NLA) (cons nil rev-ans)))))

(defun merge-NLAs (changed new-NLA old-NLA)
  (merge-NLAs-help changed new-NLA old-NLA nil))

(defun make-NLA-help (formals NLA-vars rev-ans)
  (cond
   ((endp formals)
    (tail-rev rev-ans nil))
   ((member-eq (car formals) NLA-vars)
    (make-NLA-help (cdr formals) NLA-vars (cons t rev-ans)))
   (t
    (make-NLA-help (cdr formals) NLA-vars (cons nil rev-ans)))))

(defun make-NLA (formals NLA-vars)
  (make-NLA-help formals NLA-vars nil))

(defun add-exec-entries (def-fn-list executable sat-package $sat)
  (declare (xargs :stobjs $sat))
  (if (endp def-fn-list)
      $sat
    (let* (($sat (set-executable (car def-fn-list) executable $sat))
           ($sat (set-sat-package (car def-fn-list) sat-package $sat)))
      (add-exec-entries (cdr def-fn-list) executable sat-package $sat))))

(defun add-possible-SULFA-entries (def-fn-list possible-sulfa $sat)
  (declare (xargs :stobjs $sat))
  (if (endp def-fn-list)
      $sat
    (let (($sat (set-possible-sulfa (car def-fn-list) possible-sulfa $sat)))
      (add-possible-SULFA-entries (cdr def-fn-list) possible-sulfa $sat))))

(mutual-recursion
(defun unbounded-vars (expr bounded-vars ans)
  (cond
   ((and (atom expr)
         (or (member expr bounded-vars)
             (member expr ans)))
    ans)
   ((atom expr)
    (cons expr ans))
   ((quotep expr)
    ans)
   ((consp (car expr))
    ;; ((lambda <formals> <body>) . <args>)
    (let* ((lambda-formals (cadr (car expr)))
           (lambda-body (caddr (car expr)))
           (ans (unbounded-vars lambda-body
                              (append lambda-formals bounded-vars)
                              ans)))
      (unbounded-vars-expr-list (cdr expr) bounded-vars ans)))
   (t
    (unbounded-vars-expr-list (cdr expr) bounded-vars ans))))

(defun unbounded-vars-expr-list (expr-list bounded-vars ans)
  (if (endp expr-list)
      ans
    (unbounded-vars-expr-list (cdr expr-list)
                              bounded-vars
                              (unbounded-vars (car expr-list) bounded-vars ans))))
)

(mutual-recursion

(defun unbounded-NLA-vars-help-args (args NLA bounded-vars ans $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp args)
    ans)
   ((car NLA)
    (unbounded-NLA-vars-help-args (cdr args)
                                  (cdr NLA)
                                  bounded-vars
                                  (unbounded-vars (car args)
                                                  bounded-vars
                                                  ans)
                                  $sat
                                 ))
   (t
    (unbounded-NLA-vars-help-args (cdr args)
                                  (cdr NLA)
                                  bounded-vars
                                  (unbounded-NLA-vars-help (car args)
                                                           bounded-vars
                                                           ans
                                                           $sat)
                                  $sat))))

(defun unbounded-NLA-vars-help (expr bounded-vars ans $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((or (atom expr) (quotep expr))
    ans)
   ((consp (car expr))
    ;; (lambda <formals> <body>)
    (let* ((fn (car expr))
           (formals (cadr fn))
           (body (caddr fn))
           (unbounded-NLA-vars (unbounded-NLA-vars-help
                                body
                                nil
                                nil
                                $sat))
           (NLA (make-NLA formals unbounded-NLA-vars))
           (ans (unbounded-vars-expr-list unbounded-NLA-vars
                                          (append formals bounded-vars)
                                          ans)))
      (unbounded-NLA-vars-help-args (cdr expr) NLA bounded-vars ans $sat)))
   (t
    (let ((NLA (lookup-NLA (car expr) nil $sat)))
      (unbounded-NLA-vars-help-args (cdr expr) NLA bounded-vars ans $sat)))))

)

;; (defun unbounded-NLA-vars-expr-list (expr-list ans $sat)
;;   (declare (xargs :stobjs $sat))
;;   (unbounded-NLA-vars-help-args expr-list nil nil ans $sat))

(defun unbounded-NLA-vars-expr (expr ans $sat)
  (declare (xargs :stobjs $sat))
  (unbounded-NLA-vars-help expr nil ans $sat))

(defun add-bodyless-NLA-entry (fn $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((member-eq fn '(cons car cdr consp if equal))
    (set-NLA fn (duplicate (len (fn-formals fn state)) nil) $sat))
   ((uninterpreted-fnp fn $sat state)
    (set-NLA fn (duplicate (len (fn-formals fn state)) nil) $sat))
   (t
    (set-NLA fn (duplicate (len (fn-formals fn state)) t) $sat))))

(defun add-NLA-entries-fix-help (changed def-fn-list body-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp def-fn-list)
    (mv changed $sat))
   ((uninterpreted-fnp (car def-fn-list) $sat state)
    (let* ((fn (car def-fn-list))
           ($sat (set-NLA fn (duplicate (len (fn-formals fn state)) nil)
                          $sat)))
      (add-NLA-entries-fix-help changed (cdr def-fn-list) (cdr body-list) $sat state)))
   (t
    (let* ((fn (car def-fn-list))
           (unbounded-NLA-vars (unbounded-NLA-vars-expr
                                (car body-list)
                                (measure-vars fn state)
                                $sat))
           (new-NLA (make-NLA (fn-formals fn state) unbounded-NLA-vars))
           (curr-NLA (lookup-NLA fn 'not-found $sat)))
      (if (eq 'not-found curr-NLA)
          (let (($sat (set-NLA fn new-NLA $sat)))
            (add-NLA-entries-fix-help t
                                      (cdr def-fn-list)
                                      (cdr body-list)
                                      $sat
                                      state))
        (mv-let
         (changed NLA)
         (merge-NLAs changed new-NLA curr-NLA)
         (let (($sat (set-NLA fn NLA $sat)))
           (add-NLA-entries-fix-help changed
                                     (cdr def-fn-list)
                                     (cdr body-list)
                                     $sat
                                     state))))))))

(defun add-NLA-entries-fix (def-fn-list body-list $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   (changed $sat)
   (add-NLA-entries-fix-help nil def-fn-list body-list $sat state)
   (if changed
       (add-NLA-entries-fix def-fn-list body-list $sat state)
     $sat)))

(defun add-NLA-entries (def-fn-list body-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((equal '(nil) body-list)
    ;; One primitive
    (add-bodyless-NLA-entry (car def-fn-list) $sat state))
   (t
    (add-NLA-entries-fix def-fn-list body-list $sat state))))


;; Candidate for tail recursive optimization!
(mutual-recursion

(defun possible-SULFA-exprp (expr ok-fn-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((atom expr)
    t)
   ((quotep expr)
    t)
   ((consp (car expr))
    (let* ((fn (car expr))
           (formals (cadr fn))
           (body (caddr fn))
           (args (cdr expr)))
      (cond
       ((possible-SULFA-exprp body ok-fn-list $sat)
        (let* ((unbounded-NLA-vars (unbounded-NLA-vars-help
                                    body
                                    nil
                                    nil
                                    $sat
                                    ))
               (NLA (make-NLA formals unbounded-NLA-vars)))
          (possible-SULFA-expr-listp args NLA ok-fn-list $sat)))
       (t
        nil))))
   ((member (car expr) ok-fn-list)
    (let ((NLA (lookup-NLA (car expr) nil $sat)))
      (possible-SULFA-expr-listp (cdr expr) NLA ok-fn-list $sat)))
   ((lookup-possible-sulfa (car expr) nil $sat)
    (let ((NLA (lookup-NLA (car expr) nil $sat)))
      (possible-SULFA-expr-listp (cdr expr) NLA ok-fn-list $sat)))
   (t
    nil)))

(defun possible-SULFA-expr-listp (expr-list NLA ok-fn-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp expr-list)
    t)
   ((car NLA)
    (and (executable-exprp (car expr-list) ok-fn-list $sat)
         (possible-SULFA-expr-listp (cdr expr-list) (cdr NLA) ok-fn-list
                                    $sat)))
   ((possible-SULFA-exprp (car expr-list) ok-fn-list $sat)
    (possible-SULFA-expr-listp (cdr expr-list) (cdr NLA) ok-fn-list $sat))
   (t
    nil)))
)

(defun possible-SULFA-bodyless-fn-list (fn-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp fn-list)
    t)
   ((uninterpreted-fnp (car fn-list) $sat state)
    (possible-SULFA-bodyless-fn-list (cdr fn-list) $sat state))
   ((constrained-fnp (car fn-list) state)
    nil)
   (t
    (possible-SULFA-bodyless-fn-list (cdr fn-list) $sat state))))

(defun possible-SULFA-def-fn-list (def-fn-list body-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((eq nil (car body-list))
    (possible-SULFA-bodyless-fn-list def-fn-list $sat state))
   (t
    (possible-SULFA-expr-listp body-list nil def-fn-list $sat))))

(defun add-def-fn-mem-entries (def-fn-list body-list $sat state)
  (declare (xargs :stobjs $sat))
  (let* ((executablep (executable-def-fn-listp def-fn-list body-list $sat state))
         (sat-packagep (sat-package-def-fn-listp def-fn-list body-list $sat))
         ($sat (add-exec-entries def-fn-list executablep sat-packagep $sat))
         ($sat (add-NLA-entries def-fn-list body-list $sat state))
         (possible-SULFAp (possible-SULFA-def-fn-list def-fn-list body-list $sat state))
         ($sat (add-possible-SULFA-entries def-fn-list possible-sulfap $sat)))
    $sat))

(defun add-mem-entries (fn-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp fn-list)
    $sat)
   ((not (need-funcp (car fn-list) $sat))
    (add-mem-entries (cdr fn-list) $sat state))
   (t
    (let* ((def-fn-list (def-fn-list (car fn-list) state))
           (body-list (body-list def-fn-list state))
           (needed-lst (needed-fn-list body-list def-fn-list nil $sat)))
      (cond
       ((endp needed-lst)
        ;; We're ready to handle the function's body
        (let (($sat (add-def-fn-mem-entries def-fn-list body-list $sat state)))
          (add-mem-entries (cdr fn-list) $sat state)))
       (t
        ;; We need to handle the needed function's first
        (add-mem-entries (append needed-lst fn-list) $sat state)))))))

;; Determine whether expr and all the expressions in expr-list are in SULFA.
;; Note: I'm returning more than just a Boolean, to help with error messages.
;; I may want to add another return value to say whether all the constrained
;; functions are defstubs---right now I'm assuming that they are and this
;; provides the potential for undecidability.
#|
(defun SULFA-expr-list (expr-list $sat state)
  (declare (xargs :stobjs $sat))
  (let* ((fn-list (needed-fn-list expr-list nil nil $sat))
         ($sat (add-mem-entries fn-list $sat state)))
    (mv (executable-expr-listp expr-list nil $sat)
        (sat-package-expr-listp expr-list nil $sat)
        (unbounded-NLA-vars-expr-list expr-list nil $sat)
        $sat)))
|# ;|

(defun SULFA-exprp (expr $sat state)
  (declare (xargs :stobjs $sat))
  (let* ((fn-list (needed-fn-expr expr nil nil $sat))
         ($sat (add-mem-entries fn-list $sat state))
         (sat-package-symbolsp (sat-package-exprp expr nil $sat)))
    (mv (and (possible-SULFA-exprp expr nil $sat)
             (eq (unbounded-NLA-vars-expr expr nil $sat) nil)
             (not sat-package-symbolsp))
        sat-package-symbolsp
        $sat)))
