; This book provides utilities to answer the followign queries (as requested by
; Warren Hunt) for a given function, fn.  BUT NOTE the following catches:
; encapsulated functions and built-in :program mode functions are all treated
; as primitives, i.e., as not calling any functions; and, attachments (see :DOC
; defattach) are not tracked.  We can probably do better than that if asked,
; though it's a little more work.

; Note that (build-immediate-callers-table state) need only be called whenever
; a relevant function's definition has been added or changed.

;  1.  Return a list of all functions that may be directly called by a
;      function.

; (immediate-ancestors fn state)

;  2.  Return a list of all functions, recursively to ACL2 primitives,
;      that may be called when a given function is called.

; (all-ancestors fn state)

;  3.  Find all functions that may directly call a defined function.

; (build-immediate-callers-table state)
; (immediate-callers fn state)

;  4.  Find all functions that may eventually call a function?

; (build-immediate-callers-table state)
; (immediate-callers fn state)

(in-package "ACL2")

(set-state-ok t)
(program)

(defun immediate-ancestors-w (fn wrld)
  (remove1-eq fn
              (all-fnnames (getprop fn 'unnormalized-body *t*
                                    'current-acl2-world wrld))))

(mutual-recursion

(defun all-ancestors1 (fn acc wrld)
  (let ((imm (immediate-ancestors-w fn wrld)))
    (cond ((subsetp-eq imm acc) acc)
          (t (all-ancestors1-lst imm (union-eq imm acc) wrld)))))

(defun all-ancestors1-lst (x acc wrld)
  (cond ((endp x) acc)
        (t (all-ancestors1-lst (cdr x)
                               (all-ancestors1 (car x) acc wrld)
                               wrld))))
)

(defun all-ancestors-w (fn wrld)
  (let ((imm (immediate-ancestors-w fn wrld)))
    (all-ancestors1-lst imm imm wrld)))

(defun immediate-ancestors (fn state)
  (immediate-ancestors-w fn (w state)))

(defun all-ancestors (fn state)
  (all-ancestors-w fn (w state)))

(defun extend-immediate-callers-table1 (fn imm-ancs acc)
  (cond ((endp imm-ancs) acc)
        (t (extend-immediate-callers-table1
            fn
            (cdr imm-ancs)
            (let* ((anc (car imm-ancs))
                   (old (cdr (hons-get anc acc))))
              (cond ((member-eq fn old) acc)
                    (t (hons-acons anc (cons fn old) acc))))))))

(defun extend-immediate-callers-table (fns wrld acc)
  (cond ((endp fns) acc)
        (t (extend-immediate-callers-table
            (cdr fns)
            wrld
            (extend-immediate-callers-table1
             (car fns)
             (immediate-ancestors-w (car fns) wrld)
             acc)))))

(defun all-defined-fns (wrld acc)
  (cond ((endp wrld) acc)
        ((and (eq (cadar wrld) 'formals)
              (not (eq (cddar wrld) *acl2-property-unbound*)))
         (all-defined-fns (cdr wrld)
                          (cons (caar wrld) acc)))
        (t (all-defined-fns (cdr wrld) acc))))

(defun build-immediate-callers-table (state)
  (let ((wrld (w state)))
    (if (boundp-global 'immediate-callers-table state)
        state
      (f-put-global 'immediate-callers-table
                    (extend-immediate-callers-table
                     (all-defined-fns wrld nil)
                     wrld
                     'immediate-callers-table)
                    state))))

(defun chk-immediate-callers-table (state)
  (or (boundp-global 'immediate-callers-table state)
      (er hard 'immediate-callers
          "Please evaluate ~x0 first."
          '(build-immediate-callers-table state))))

(defun immediate-callers (fn state)
  (prog2$ (chk-immediate-callers-table state)
          (cdr (hons-get fn (f-get-global 'immediate-callers-table state)))))

(mutual-recursion

(defun all-callers1 (fn acc table)
  (let ((imm (cdr (hons-get fn table))))
    (cond ((subsetp-eq imm acc) acc)
          (t (all-callers1-lst imm (union-eq imm acc) table)))))

(defun all-callers1-lst (x acc table)
  (cond ((endp x) acc)
        (t (all-callers1-lst (cdr x)
                             (all-callers1 (car x) acc table)
                             table))))
)

(defun all-callers (fn state)
  (prog2$ (chk-immediate-callers-table state)
          (all-callers1 fn
                        nil
                        (f-get-global 'immediate-callers-table state))))
