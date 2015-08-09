(in-package "ACL2")
(include-book "doc-section")

;Needed to use, but not needed for certification:
;(include-book "defcode" :load-compiled-file :comp :ttags ((defcode)))

(program)
(set-state-ok t)


; return world with last cltl-command global-value replaced with given value
(defun replace-last-cltl-command-wrld (cltl-command wrld)
  (declare (xargs :mode :program))
  (cond ((endp wrld)
         nil)
        ((and (consp (car wrld))
              (eq (caar wrld) 'cltl-command)
              (consp (cdar wrld))
              (eq (cadar wrld) 'global-value))
         (cons
          (list* 'cltl-command 'global-value cltl-command)
          (cdr wrld)))
        (t
         (cons
          (car wrld)
          (replace-last-cltl-command-wrld cltl-command (cdr wrld))))))

(defmacro replace-last-cltl-command (cltl-command)
  `(progn!=touchable
    :fns set-w!
    :loop-only
     (pprogn
      (set-w! (replace-last-cltl-command-wrld
               ,(if (and (consp cltl-command)
                         (symbolp (car cltl-command))
                         (member-eq (car cltl-command)
                                    '(defuns defstobj defpkg defconst defmacro
                                       memoize unmemoize)))
                  `',cltl-command ; needs quoting
                  cltl-command    ; might need evaluation
                  )
               (w state))
              state)
      (value :invisible))))


; return world with last cltl-command global-value removed
(defun remove-last-cltl-command-wrld (wrld)
  (declare (xargs :mode :program))
  (cond ((endp wrld)
         nil)
        ((and (consp (car wrld))
              (eq (caar wrld) 'cltl-command)
              (consp (cdar wrld))
              (eq (cadar wrld) 'global-value))
         (cdr wrld))
        (t
         (cons
          (car wrld)
          (remove-last-cltl-command-wrld (cdr wrld))))))

(defmacro remove-last-cltl-command ()
  '(progn!=touchable
    :fns set-w!
    :loop-only
     (pprogn
      (set-w! (remove-last-cltl-command-wrld (w state)) state)
      (value :invisible))))


; convert (declare (...)) or ((...)) or (...) into (declare (...))
(defun reconstruct-declare-lst (spec)
  (cond ((atom spec) nil)
        ((eq 'declare (car spec))
         (list spec))
        ((consp (car spec))
         (list (cons 'declare spec)))
        (t
         (list (list 'declare spec)))))

; for public use
(defmacro defun-bridge (name
                        ll
                        .(&key (logic '() logic-p)
                               (logic-declare '())
                               (program '() program-p)
                               (program-declare '())
                               (raw '() raw-p)
                               (raw-declare '())
                               (doc '())))

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file hacking-xdoc.lisp.

; ":Doc-Section hacker
;
; define a function with a different low-level definition.~/

; ~bv[]
; General Form:
; (defun-bridge ~i[name] (~i[formals])
;   [:doc ~i[doc-string]]
;   [:loop-declare ~i[loop-decls]]
;   :loop ~i[loop-body]
;   [:raw-declare ~i[raw-decls]]
;   :raw ~i[raw-body])
; ~ev[] ~/
;
; This is much like executing
; ~bv[]
; (defun ~i[name] (~i[formals])
;   ~i[doc-string]
;   (declare (xargs :mode :program))
;   ~i[loop-decls]
;   ~i[loop-body])
; ~ev[]
; in ACL2 and then
; ~bv[]
; (defun ~i[name] (~i[formals])
;   ~i[raw-decls]
;   ~i[raw-body])
; ~ev[]
; in raw Lisp, except that extra checks and bookkeeping make it safer
; than that.
;
; An active ttag is required to use this form (~l[defttag]), because
; it can easily corrupt ACL2 or render it unsound.
; ~/"
  (declare (xargs :guard (and (or (and logic-p program-p (not raw-p))
                                  (and logic-p (not program-p) raw-p)
                                  (and (not logic-p) program-p raw-p))
                              (implies doc
                                       (stringp doc))))
           (ignorable program-p))
  (let*
    ((ignorable-decl-lst
      (and ll `((declare (ignorable . ,ll)))))
     (raw-def-tuple
      `(,name ,ll
        ,@ ignorable-decl-lst
        . ,(if raw-p
             (append (reconstruct-declare-lst raw-declare)
                     (list raw))
             (append (reconstruct-declare-lst program-declare)
                     (list program)))))
     (loop-def
      `(defun ,name
         ,ll
         ,@ (and doc (list doc))
         . ,(if logic-p
              (append
               (list '(declare (xargs :mode :logic)))
               ignorable-decl-lst
               (reconstruct-declare-lst logic-declare)
               (list logic))
              (append
               (list '(declare (xargs :mode :program)))
               ignorable-decl-lst
               (reconstruct-declare-lst program-declare)
               (list program)))))
     (code
      (list loop-def
            (if raw-p
              '(remove-last-cltl-command)
              `(replace-last-cltl-command
                (defuns ,(if logic-p :logic :program) nil
                  ,raw-def-tuple))))))
    `(progn
      (assert-unbound ,name)
      ,@ (if logic-p
           nil
           `((ensure-program-only-flag ,name)))
      (ensure-special-raw-definition-flag ,name)
      (defcode
        :loop ,code
        ,@ (and raw-p
                `(:extend (in-raw-mode (maybe-push-undo-stack 'defun ',name)
                                       (defun . ,raw-def-tuple)
                                       (defun-*1* ,name ,ll (,name . ,ll)))
                  :retract (in-raw-mode (maybe-pop-undo-stack ',name))))
        :compile ((defun . ,raw-def-tuple)
                  . ,(and raw-p `((defun-*1* ,name ,ll (,name . ,ll)))))))))



; tests and stuff:

#|
(include-book
 "defcode" :ttags ((defcode)))
(defttag t)
(defun-bridge foo (x)
  :program x
  :raw (progn (format t "~a~%" x)
              x))

(foo 42)
(set-guard-checking :none)
(foo 42)
(defmacro bar ()
  (foo nil))
(bar)
|#
