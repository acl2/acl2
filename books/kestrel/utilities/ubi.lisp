; Copyright (C) 2016, Regents of the University of Texas
; Copyright (C) 2022 Kestrel Institute
; Written by Matt Kaufmann
; Supporting Author: Eric Smith (eric.smith@kestrel.edu)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See documentation in ubi-doc.lisp.

(program)

(defun cmds-back-to-boot-strap (wrld acc)

; We accumulate into acc the commands back to, but not including the boot-strap
; world.  At the top level, acc is nil and we return the list of commands since
; the boot-strap, in order.

  (declare (xargs :guard (plist-worldp wrld)))
  (cond ((endp wrld) ; impossible if we started with a post-boot-strap world
         acc)
        ((and (eq (caar wrld) 'command-landmark)
              (eq (cadar wrld) 'global-value))
         (let ((cmd (access-command-tuple-form (cddar wrld))))
           (cond ((and (consp cmd)
                       (member-eq (car cmd) '(exit-boot-strap-mode
                                              reset-prehistory)))
                  acc)
                 (t (cmds-back-to-boot-strap (cdr wrld) (cons cmd acc))))))
        (t (cmds-back-to-boot-strap (cdr wrld) acc))))

(defconst *keeper-cmds*
  '(include-book ; keep the initial segment of include-books
    ;; These things can appear in the world before the include-books (e.g., if
    ;; they are in an acl2-customization file; to prevent :ubi from ever
    ;; undoing anything in your acl2-customzation file, put (reset-prehistory)
    ;; at the end of that file):
    defpkg
    ;; xdoc
    add-include-book-dir
    add-include-book-dir!
    set-in-theory-redundant-okp))

;; Look inside certain wrappers when deciding to keep a command:
(defun unwrap-cmd-for-ubi (cmd)
  (if (not (consp cmd))
      cmd
    (if (eq 'local (car cmd))
        (cadr cmd)
      (if (eq 'with-output (car cmd))
          (car (last cmd))
        cmd))))

(defun initial-keeper-cmds-length (cmds keeper-cmds acc)
  (cond ((endp cmds) acc)
        (t (let* ((cmd0 (car cmds))
                  (cmd (unwrap-cmd-for-ubi cmd0))
                  (keeper-p (and (consp cmd)
                                 (member-eq (car cmd) keeper-cmds))))
             (cond (keeper-p (initial-keeper-cmds-length (cdr cmds)
                                                         keeper-cmds
                                                         (1+ acc)))
                   (t acc))))))

(defun ubi-fn (args state)
  (declare (xargs :guard (symbol-listp args) :stobjs state))
  (let* ((wrld (w state))
         (cmds (cmds-back-to-boot-strap wrld nil))
         (keeper-cmds (union-eq args *keeper-cmds*))
         (len-cmds (length cmds))
         (len-keeper-cmds
          (initial-keeper-cmds-length cmds keeper-cmds 0)))
    (cond ((eql len-cmds len-keeper-cmds)
           (pprogn (fms "There is nothing to undo, since all commands after ~
                         the boot-strap are ~v0 commands.~|"
                        (list (cons #\0 keeper-cmds))
                        *standard-co* state nil)
                   (value :invisible)))
          (t (ubu len-keeper-cmds)))))

;; Args are treated just like the *keeper-cmds*.
(defmacro ubi (&rest args)
  (declare (xargs :guard (symbol-listp args)))
  `(ubi-fn ',args state))
