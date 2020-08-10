(in-package "ACL2")

; Modification by Matt K. after v4-3: Removed :load-compiled-file :comp, which
; was part of both include-book forms in this file, in support of provisional
; certification.  Presumably the indicate books have already been compiled by
; now, anyhow.

(include-book "hacker") ;was in portcullis

(program)
(set-state-ok t)


; auxiliary stuff:

; check if something is a list of function applications
(defun acl2-hacker::defcode-code-listp (l)
  (or (null l)
      (and (consp l)
           (consp (car l))
           (not (eq 'lambda (caar l))))))

; coerce something to be a LIST of function applications
(defun acl2-hacker::defcode-ensure-code-list (c)
  (if (acl2-hacker::defcode-code-listp c)
    c
    (list c)))


; ***********************************
; beginning of actual dangerous stuff
(defttag defcode)

(include-book "progn-bang-enh" :ttags ((defcode)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; defcode-fn
;
; this is the event code for defcode, that executes any :loop code and
; puts any :extend or :retract code into the world.
;

(progn+touchable :fns install-event
  (defun defcode-fn (loop extend retract state event-form)
    (let* ((loop-lst (acl2-hacker::defcode-ensure-code-list loop))
           (extend-lst (acl2-hacker::defcode-ensure-code-list extend))
           (retract-lst (acl2-hacker::defcode-ensure-code-list retract)))
      (er-progn
       (if loop-lst
         (progn!-fn loop-lst nil state)
         (value nil))
       (if (or extend-lst retract-lst)
         (let* ((event-form (or event-form
                                `(defcode :loop ,loop-lst
                                          :extend ,extend-lst
                                          :retract ,retract-lst)))
                (wrld (w state))
                (wrld (if extend-lst
                        (putprop 'extend-progn! 'global-value extend-lst wrld)
                        wrld))
                (wrld (if retract-lst
                        (putprop 'retract-progn! 'global-value retract-lst wrld)
                        wrld)))
           (install-event ':invisible
                          event-form
                          'defcode
                          0
                          nil
                          nil
                          nil
                          'defcode
                          wrld
                          state))
         (value nil))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; executing code on world changes
;
; these are made as permanent changes so that the rest of defcode can be
; resurrected if an old world is reinstalled.
;

; execute code in (extend-progn! global-value #) triples on world extension
(modify-raw-defun-permanent
 add-trip pre-defcode-add-trip
 (world-name world-key trip status)
 (progn
  (pre-defcode-add-trip world-name world-key trip status)
  (when (and (eq (car trip) 'extend-progn!)
             (eq (cadr trip) 'global-value))
        (mv-let (erp val state)
                (state-global-let*
                 ((inhibit-output-lst
                   (union-eq (@ inhibit-output-lst)
                             (remove 'error *valid-output-names*))))
                 (progn!-fn (cddr trip) nil *the-live-state*))
                (declare (ignore val state))
                (when erp
                      (hard-error 'defcode
                                  "Error returned."
                                  nil))))))

; execute code in (retract-progn! global-value #) triples on world retraction
(modify-raw-defun-permanent
 undo-trip pre-defcode-undo-trip
 (world-name world-key trip)
 (progn
  (pre-defcode-undo-trip world-name world-key trip)
  (when (and (eq (car trip) 'retract-progn!)
             (eq (cadr trip) 'global-value))
        (mv-let (erp val state)
                (state-global-let*
                 ((inhibit-output-lst
                   (union-eq (@ inhibit-output-lst)
                             (remove 'error *valid-output-names*))))
                 (progn!-fn (cddr trip) nil *the-live-state*))
                (declare (ignore val state))
                (when erp
                      (hard-error 'defcode
                                  "Error returned."
                                  nil))))))

; for detecting reentry into set-w
(in-raw-mode
 (defvar *set-w-reentry-protect* nil))

; enforce non-reentry of set-w
(modify-raw-defun-permanent
 set-w pre-defcode-set-w (flag wrld state)
 (declare (special *set-w-reentry-protect*))
 (if *set-w-reentry-protect*
   (hard-error 'defcode
               "Attempt to change world within DEFCODE code."
               nil)
   (let ((*set-w-reentry-protect* t))
     (pre-defcode-set-w flag wrld state))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; defcode macro

(defmacro defcode (&whole event-form &key loop extend retract compile)
  (let ((loop-code-lst
         `((defcode-fn
             ',loop
             ',extend
             ',retract
             state
             ',event-form)))
        (compile-code-lst
         (cond ((atom compile)
                nil)
               ((and (consp compile)
                     (consp (car compile))
                     (not (eq 'lambda (caar compile))))
                compile)
               (t
                (list compile)))))
    (if compile-code-lst
      `(progn!
        (progn! :loop-only .,loop-code-lst)
        (progn! :compile-only .,compile-code-lst))
      `(progn! :loop-only .,loop-code-lst))))

; this copy helpful in case of world resurrection
(defcode
 :extend
 (in-raw-mode
  (defmacro progn! (&rest r)
    (let ((sym (gensym)))
      `(let ((state *the-live-state*)
             (,sym (f-get-global 'acl2-raw-mode-p *the-live-state*)))
         (declare (ignorable state))
         ,@(cond ((not (consp r))
                  (list nil))
                 ((eq (car r) :loop-only)
                  (list nil))
                 ((eq (car r) :compile-only)
                  (cdr r))
                 ((eq (car r) :state-global-bindings)
                  (cddr r))
                 (t r))
         (f-put-global 'acl2-raw-mode-p ,sym state)
         (value nil))))))

; **********************
; end of dangerous stuff
(defttag nil)

; end of required defcode stuff


; tests & stuff:

#|
(defttag defcode)

;(defcode :extend (defun foo (x) (1+ x))) ; should fail

(defcode :extend (cw "==> Hi!~%")
         :retract (cw "==> Bye!~%")
         :compile (format t "==> Yo!~%"))
(u)

(defttag nil)
(progn (defttag t)
       (defcode :extend  (in-raw-mode (format t "==> Hi!~%"))
                :retract (in-raw-mode (format t "==> Bye!~%")))
       (defttag nil))
(u)

;(defcode :extend  (in-raw-mode (format t "==> Hi!~%")))
; should fail without a trust tag

(mini-proveall)
;|#


; misc:

; this was just a convenient place to put this, considering it depends
; on defcode.

; assert that a name is not bound in ACL2, nor as a raw lisp function, macro
; or variable.
(defmacro assert-unbound (&rest names)
  `(defcode
    :loop
    (in-raw-mode
     (dolist (name ',names)
             (when (and (not (f-get-global 'ld-redefinition-action *the-live-state*))
                        (or (getprop name 'absolute-event-number nil
                                     'current-acl2-world (w *the-live-state*))
                            (boundp name)
                            (fboundp name)
                            (macro-function name)))
                   (hard-error 'assert-unbound
                               "Already has an ACL2 or raw Lisp definition: ~x0~%"
                               (list (cons #\0 name))))))))
