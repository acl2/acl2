#|$ACL2s-Preamble$;
(include-book "defcode" :ttags ((defcode)))

(acl2::begin-book t :ttags ((defcode)));$ACL2s-Preamble$|#

(in-package "ACL2")
; cert_param: (non-acl2r)

(program)
(set-state-ok t)


(defun chk-acceptable-redefun (def ctx wrld state)
  (er-let*
   ((tuple (chk-acceptable-defuns (list def) ctx wrld state)))
   (assert$
    (equal (length tuple) 26)
    (let* ((name (car def))
           (new-wrld (nth 18 tuple))
           (old-symbol-class
            (getprop name 'symbol-class 0 'current-acl2-world wrld))
           (new-symbol-class (nth 15 tuple))
           (old-formals
            (getprop name 'formals 0 'current-acl2-world wrld))
           (new-formals
            (getprop name 'formals 0 'current-acl2-world new-wrld))
           (old-stobjs-in
            (getprop name 'stobjs-in 0 'current-acl2-world wrld))
           (new-stobjs-in
            (getprop name 'stobjs-in 0 'current-acl2-world new-wrld))
           (old-stobjs-out
            (getprop name 'stobjs-out 0 'current-acl2-world wrld))
           (new-stobjs-out
            (getprop name 'stobjs-out 0 'current-acl2-world new-wrld)))
      (cond ((eql old-symbol-class 0)
             (er soft ctx "No existing definition: ~x0" name))
            ((nth 19 tuple) ; non-executablep
             (er soft ctx
                 "Please do not redefun a non-executable function.  The ~
                  offending definition is: ~x0."
                 def))
            ((not (eq ':program old-symbol-class))
             (er soft ctx
                 "Old definition should have defun-mode :program.  Sorry."))
            ((not (eq ':program new-symbol-class))
             (er soft ctx
                 "New definition should have defun-mode :program.  Sorry."))
            ((not (equal new-formals old-formals))
             (er soft ctx
                 "Please use the same formal parameter list when redefining. ~
                  Previous formals: ~x0"
                 old-formals))
            ((not (equal new-stobjs-in old-stobjs-in))
             (er soft ctx
                 "New definition should have the same stobjs-in.Previously, ~
                  ~x0.  Specified, ~x1."
                 old-stobjs-in new-stobjs-in))
            ((not (equal new-stobjs-out old-stobjs-out))
             (er soft ctx
                 "New definition should have the same stobjs-out.Previously, ~
                  ~x0.  Specified, ~x1."
                 old-stobjs-out new-stobjs-out))
            (t ; okay
             (value :invisible)))))))


(include-book "rewrite-code")

; this is a safer version of doing defun with redefinition allowed.
;
; only :program mode functions may be used here, because the intent is to
; maintain sound reasoning.
;
; lots of checks are performed and actions are taken to prevent the logic from
; being tainted by the redefinition.
;
(defmacro redefun (name ll &rest decls-and-body)
  (declare (xargs :guard (and (symbolp name)
                              (symbol-listp ll)
                              (consp decls-and-body))))
  (let ((def (list* name ll decls-and-body)))
    `(progn+redef
      (assert-include-defun-matches-certify-defun ,name)
      (defcode
       :loop (er-progn
              (assert-no-special-raw-definition ,name)
              (chk-acceptable-redefun ',def
                                      'redefun
                                      (w state)
                                      state)
              (ensure-program-only-flag ,name)
              (defun . ,def))
       :extend
       (in-raw-mode
        (defun-*1* ,name ,ll
                   (if (f-get-global 'safe-mode *the-live-state*)
                     (throw-raw-ev-fncall (list 'program-only-er ',name
                                                (list . ,ll) 't '(nil) t))
                     (,name . ,ll))))
       :compile
       (defun . ,def)))))


; this uses redefun and our code rewrite stuff (see rewrite-code.lisp,
; especially compute-copy-defun+rewrite) to redefine a :program mode
; function in terms of its existing definition.
;
(defmacro redefun+rewrite (name &rest rewrite-spec)
  (declare (xargs :guard (symbolp name)))
  `(make-event
    (compute-copy-defun+rewrite
     ',name ',name ',rewrite-spec 'redefun state)))


; tests and stuff
#|
(include-book
 "defcode" :ttags ((defcode)))

(defttag t)

(redefun deflabel-fn (name state doc event-form)
         (declare (ignore doc event-form))
         (value name))

(set-guard-checking :none)
(deflabel moo)
(deflabel moo)
|#
