; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; After loading some ACL2 books -- for example with include-book, ld, or
; rebuild -- invoke the following command to write out a file, tb-file, that
; depends only on the ACL2 "toothbrush" (a relatively small part of ACL2), not
; on all of ACL2.  After loading the toothbrush, tb-file can be compiled and
; loaded in raw Lisp.

; (make-toothbrush "tb-file" fn1 fn2 ...)

; Here fn1, fn2, ... are functions for which, along with their supporters,
; definitions will be written to tb-file.

; Note that include-book forms are ignored when writing out tb-file.  The
; intention is that all source files have already been loaded.

; Search for !! for places to consider making improvements.

; !! We probably are not picking up supporters of SATISFIES type declarations.

(in-package "ACL2")

(defun cons-to-all (a lst-lst)
  (declare (xargs :guard (true-list-listp lst-lst)))
  (cond ((endp lst-lst) nil)
        (t (cons (cons a (car lst-lst))
                 (cons-to-all a (cdr lst-lst))))))

(program)

(defun get-cltl-command (name ctx wrld quiet-p)
  (let ((val
         (scan-to-cltl-command
          (cdr (lookup-world-index 'event
                                   (getprop name 'absolute-event-number
                                            '(:error "See ~
                                                          RECOVER-DEFS-LST.")
                                            'current-acl2-world wrld)
                                   wrld)))))
    (cond
     ((atom val)
      (and (not quiet-p)
           (er hard ctx
               "We failed to find the expected CLTL-COMMAND for the ~
                introduction of ~x0."
               name)))
     (t (case (car val)
          (defuns

; Val is of the form (defuns defun-mode-flg ignorep def1 ... defn).  If
; defun-mode-flg is non-nil then the parent event was (defuns def1 ... defn)
; and the defun-mode was defun-mode-flg.  If defun-mode-flg is nil, the parent
; was an encapsulate, defchoose, or :non-executable.

            (let ((defs (cdddr val)))
              (assert$ defs
                       (cond ((cdr defs)
                              (cons 'mutual-recursion
                                    (cons-to-all 'defun defs)))
                             (t (cons 'defun (car defs)))))))
          (defmacro val)
          (defconst ; (list 'defconst name form val)

; We could use either the form or the value.  We use the form, both in case
; there are side effects as from (prog2$ (cw ...) ...) and because we might
; want to study compilation of the form.

            (butlast val 1))
          (defstobj

; Then val is of the form
; (defstobj name live-var defstobj-raw-init-code raw-defs template ax-defs)
; but we throw most of that away and recover the actual event from name.  The
; raw-Lisp defstobj form will create all subsidiary functions and constants.

            (get-event (cadr val) wrld))
          (t (er hard ctx
                 "Unimplemented command type, ~x0.  See get-cltl-commands."
                 (car val))))))))

; [originally from ~/Dropbox/fh/acl2/patches/fresh-cons/fresh-cons.lisp]

(defmacro extend-with-supporters-er (x &optional msg)
  `(let ((msg ,msg))
     (er hard! ctx
         "Unsupported argument for ~x0: ~x1~@2"
         'extend-with-supporters
         ,x
         (if msg
             (msg "~%Note: ~@0" msg)
           ""))))

(defconst *primitive-macros-evaluating-args-like-functions*

; Most or all of these are from *initial-macros-with-raw-code*.

  '(caar cadr cdar cddr caaar caadr cadar caddr cdaar cdadr cddar cdddr
         caaaar caaadr caadar caaddr cadaar cadadr caddar cadddr cdaaar
         cdaadr cdadar cdaddr cddaar cddadr cdddar cddddr rest make-list
         list or and * logior logxor logand
         search
         logeqv
         concatenate
         > <= >= + - / 1+ 1-
         list*
         append
         first second third fourth fifth
         sixth seventh eighth ninth tenth
         digit-char-p
         member assoc subsetp no-duplicatesp rassoc remove remove-duplicates
         position
         intern
         ))

(defconst *macros-to-expand-in-acl2-loop*

; Most or all of these are from *initial-macros-with-raw-code*.

  '(cond case er let*
         plet por pand pargs spec-mv-let))

(defmacro extend-names (x)
  `(let ((x ,x))
     (cond ((or (member-eq x names)
                (member-eq x seen))
            names)
           (t (cons x names)))))

(defun cl-defined-p (x)
  (declare (ignore x))
  (er hard! 'cl-defined-p
      "We thought that there was a raw Lisp definition of ~x0!"
      'cl-defined-p))

(defttag :make-toothbrush)
(remove-untouchable ev-w t)
(remove-untouchable current-package nil)
(remove-untouchable serialize-character-system nil)
(remove-untouchable serialize-character nil)
(defttag nil)

(defun acl2-package-primitives (lst)
  (cond ((endp lst) nil)
        ((equal (symbol-package-name (caar lst)) "COMMON-LISP")
         (acl2-package-primitives (cdr lst)))
        (t (cons (caar lst)
                 (acl2-package-primitives (cdr lst))))))

(defconst *acl2-package-primitives*
  (acl2-package-primitives *primitive-formals-and-guards*))

(defun assoc-eq-cadr (x alist)
  (declare (xargs :guard (and (symbolp x)
                              (alistp alist)
                              (alistp (strip-cdrs alist)))))
  (cond ((endp alist) nil)
        ((eq x (cadr (car alist))) (car alist))
        (t (assoc-eq-cadr x (cdr alist)))))

(defun get-cltl-body (name ctx wrld)

; We return *nil* rather than nil when the body exists, so as to distinguish
; between a body of nil and no body.

  (let ((form (get-cltl-command name ctx wrld t)))
    (case (car form)
      (mutual-recursion
       (or (car (last (assoc-eq-cadr name (cdr form))))
           *nil*))
      ((defun defconst defmacro)
       (or (car (last form)) ; see comment above about not returning nil
           *nil*))
      (defstobj *nil*)
      (t nil))))

(mutual-recursion

(defun extend-with-supporters (x ctx wrld names seen)

; We extend names with constant, function, and macro names encountered while
; scanning the form x, including macroexpansion.  However, we do not extend
; with names that are members of seen.

; Warning: Keep in sync with translate11.  Here we scan x as through
; translating (mostly, macroexpanding) for execution in raw Lisp, but what we
; return is an extension of names that remains disjoint from seen, collecting
; all function, constant, and macro names encountered.  We are conservative, in
; that we are free to return an error where translate11 would not.

; !! Add state parameter and then replace *initial-logic-fns-with-raw-code*
; with logic-fns-with-raw-code and similarly for program fns and macros.

; !! Possible efficiency enhancement (but would need to think this through, in
; particular for the case of mutual-recursion): collect an alist mapping names
; to definitions instead of names, so that we don't need to look up definitions
; at the end.

  (cond
   ((atom x)
    (let ((vc (legal-variable-or-constant-namep x)))
      (cond ((keywordp x) names)
            ((symbolp x)
             (cond ((or (equal (symbol-package-name x)
                               "COMMON-LISP")
                        (member-eq x *acl2-package-primitives*))
                    names)
                   ((eq vc 'constant)
                    (let ((form (defined-constant x wrld)))
                      (cond (form (extend-names x))
                            (t (extend-with-supporters-er x)))))
                   (t names)))
            (t names))))
   ((consp (car x))

; X is ((lambda (v1 ... vn) body) x1 .. xn).  Translate to LET form as is done
; in translate11.

    (assert$ (and (eq (caar x) 'lambda)
                  (true-listp (car x))
                  (true-listp (cadr (car x)))
                  (true-listp (cdr x))
                  (eql (length (cadr (car x)))
                       (length (cdr x))))
             (extend-with-supporters (list* 'let
                                            (listlis (cadr (car x)) (cdr x))
                                            (cddr (car x)))
                                     ctx wrld names seen)))
   ((eq (car x) 'quote)
    names)
   ((eq (car x) 'mv)
    (extend-with-supporters-lst (cdr x) ctx wrld names seen))
   ((eq (car x) 'mv-let) ; (mv-let vars y ... decls ... z)
    (let ((names
           (extend-with-supporters (caddr x) ctx wrld names seen)))
      (extend-with-supporters (car (last x)) ctx wrld names seen)))
   ((eq (car x) 'let) ; (let vars ... decls ... body)
    (let ((names (extend-with-supporters (car (last x))
                                         ctx wrld names seen)))
      (extend-with-supporters-lst (strip-cadrs (cadr x))
                                  ctx wrld names seen)))
   ((eq (car x) 'with-local-stobj) ; special handling by translate11-call
    (extend-with-supporters (caddr x) ctx wrld names seen))
   ((member-eq (car x)
               `(flet             ; special handling by translate11-flet
                 wormhole-eval    ; special handling by translate11-call
                 ))

; Some functions and macros that one might expect on the list above, such as
; stobj-let and pargs, are macros with raw Lisp code and are ruled out below by
; the *-with-raw-code* tests below.  Others, like with-local-stobj
; and wormhole-eval, we might want to think about handling.

    (extend-with-supporters-er x))

; We omit special treatment for translate-and-test, leaving that to ordinary
; macroexpansion.

   ((getprop (car x) 'macro-body nil 'current-acl2-world wrld)
    (cond
     ((member-eq (car x) *primitive-macros-evaluating-args-like-functions*)
      (extend-with-supporters-lst (cdr x) ctx wrld names seen))
     ((eq (car x) 'the) ; (the type term)
      (extend-with-supporters (caddr x) ctx wrld names seen))
     ((and (member-eq (car x) *initial-macros-with-raw-code*)
           (not (member-eq (car x) *macros-to-expand-in-acl2-loop*)))
      (extend-with-supporters-er
       x
       "This macro has special raw Lisp code.  Consider adding it to ~
        *macros-to-expand-in-acl2-loop*."))
     (t
      (let ((gc-off t) ; reasonable value, e.g., used by certify-book
            (state-vars (default-state-vars nil))
            (macro-name (car x)))
        (mv-let
         (erp alist)
         (bind-macro-args
          (macro-args macro-name wrld)
          x wrld state-vars)

; Here we skip guard-checking, which was presumably done earlier when
; macroexpand1 was called.

         (cond
          (erp (extend-with-supporters-er
                x
                "Error in binding macro-args."))
          (t
           (mv-let
            (erp1 expansion1)
            (ev-w
             (getprop (car x) 'macro-body nil 'current-acl2-world wrld)
             alist wrld
             nil ; user-stobj-alist
             t   ; safe-mode
             gc-off nil nil)
            (cond (erp1 ; presumably impossible
                   (extend-with-supporters-er
                    x
                    (msg "In the attempt to macroexpand the form ~x0, ~
                          evaluation of the macro body caused the following ~
                          error:~|~%~@1"
                         x
                         expansion1)))
                  (t

; We now do the expansion again, without safe-mode this time, in an attempt to
; emulate raw-Lisp macroexpansion.

                   (mv-let
                    (erp2 expansion2)
                    (ev-w
                     (getprop (car x) 'macro-body nil 'current-acl2-world wrld)
                     alist wrld
                     nil ; user-stobj-alist
                     nil ; safe-mode
                     gc-off nil nil)
                    (cond
                     (erp2 ; presumably impossible
                      (extend-with-supporters-er
                       x
                       (msg "In the attempt to macroexpand the form ~x0 with ~
                             safe-mode = nil, evaluation of the macro body ~
                             caused the following error:~|~%~@1"
                            x
                            expansion2)))
                     (t
                      (let ((names
                             (cond ; warning: keep in sync with extend-names
                              ((or (cl-defined-p macro-name)
                                   (member-eq macro-name names)
                                   (member-eq macro-name seen))
                               names)
                              (t
                               (extend-with-supporters
                                (get-cltl-body macro-name ctx wrld)
                                ctx
                                wrld
                                (cons macro-name names)
                                seen)))))
                        (cond ((equal expansion1 expansion2) ; optimization
                               (extend-with-supporters
                                expansion1 ctx wrld names seen))
                              (t
                               (extend-with-supporters-lst
                                (list expansion1 expansion2)
                                ctx wrld names seen)))))))))))))))))
   ((cl-defined-p (car x))
    (extend-with-supporters-lst (cdr x) ctx wrld names seen))
   ((or (member-eq (car x) *initial-program-fns-with-raw-code*)
        (member-eq (car x) *initial-logic-fns-with-raw-code*))
    (extend-with-supporters-er
     x
     (msg "Illegal function call: ~x0 is not fboundp but is in ~x1.  Probably ~
           it is necessary to extend file load-toothbrush.lsp."
          (car x)
          (if (member-eq (car x) *initial-program-fns-with-raw-code*)
              '*initial-program-fns-with-raw-code*
            '*initial-logic-fns-with-raw-code*))))
   (t
    (let* ((fn (car x))
           (body (get-cltl-body fn ctx wrld))
           (names
            (cond             ; warning: keep in sync with extend-names
             ((or (null body) ; e.g. for if, car, unary--, and other primitives
                  (member-eq fn names)
                  (member-eq fn seen))
              names)
             (t (extend-with-supporters body ctx wrld
                                        (cons fn names)
                                        seen)))))
      (extend-with-supporters-lst (cdr x) ctx wrld names seen)))))

(defun extend-with-supporters-lst (x ctx wrld names seen)
  (cond ((endp x) names)
        (t (let ((names (extend-with-supporters (car x) ctx wrld names seen)))
             (extend-with-supporters-lst (cdr x) ctx wrld names seen)))))
)

(defun get-cltl-command-lst-1 (names ctx wrld acc seen)

; Names is a list of function and macro names.  We return a list of definitions
; sufficient for evaluating calls of any name in names (after loading
; load-toothbrush.lsp).

; Invariant: Names has no duplicates and is disjoint from seen, which in turn
; is the list of names introduced by the list of definitions, acc.  In the case
; of defstobj, seen contains just the stobj name.

  (cond
   ((endp names) acc)
   ((or (equal (symbol-package-name (car names))
               "COMMON-LISP")
        (member-eq (car names) *acl2-package-primitives*))
    (get-cltl-command-lst-1 (cdr names) ctx wrld acc seen))
   (t (let* ((form (get-cltl-command (car names) ctx wrld nil)))
        (case (car form)
          (mutual-recursion
           (let ((new-names (strip-cadrs (cdr form))))
             (cond
              ((intersectp-eq new-names seen) ; already handled this mut-rec
               (get-cltl-command-lst-1 (cdr names) ctx wrld acc seen))
              (t (let* ((seen (append new-names seen))
                        (names (extend-with-supporters-lst
                                (strip-last-elements (cdr form))
                                ctx
                                wrld
                                (cdr names)
                                seen)))
                   (get-cltl-command-lst-1 names
                                           ctx
                                           wrld
                                           (cons form acc)
                                           seen))))))
          ((defun defconst defmacro)
           (let* ((new-name (cadr form))
                  (seen (assert$
                         (not (member-eq new-name seen))
                         (cons new-name seen)))
                  (names (extend-with-supporters
                          (car (last form))
                          ctx
                          wrld
                          (cdr names)
                          seen)))
             (get-cltl-command-lst-1 names
                                     ctx
                                     wrld
                                     (cons form acc)
                                     seen)))
          (defstobj
            (let ((st (if (getprop (car names) 'stobj nil 'current-acl2-world
                                   wrld)
                          (car names)
                        (getprop (car names) 'stobj-function nil
                                 'current-acl2-world wrld))))
              (assert$
               st
               (cond
                ((member-eq st seen)
                 (get-cltl-command-lst-1 (cdr names) ctx wrld acc seen))
                (t
                 (get-cltl-command-lst-1
                  (cdr names)
                  ctx
                  wrld
                  (cons form acc)
                  (cons st seen)))))))
          (t (er hard! ctx
                 "~x0 encountered form ~x1, but ~x2 was an unexpected type of ~
                  form."
                 'get-cltl-command-lst-1 form (car form))))))))

(defun sort-cltl-commands (cmds wrld acc)

; Sort the given events so that each event depends only on events earlier in
; the list, not later.

  (cond ((endp cmds)
         (strip-cdrs (merge-sort-car-< acc)))
        (t (sort-cltl-commands
            (cdr cmds)
            wrld
            (cons (cons (let ((name (case-match cmds
                                      ((('mutual-recursion (& name . &)
                                                           . &)
                                        . &)
                                       name)
                                      (& (cadr (car cmds))))))
                          (getprop name 'absolute-event-number
                                   '(:error "Missing absolute-event-number!")
                                   'current-acl2-world wrld))
                        (car cmds))
                  acc)))))

(defun chk-defined-functions (names ctx wrld)
  (cond ((endp names) nil)
        ((and (eq (getprop (car names) 'formals t 'current-acl2-world wrld)
                  t)
              (eq (getprop (car names) 'macro-body t 'current-acl2-world wrld)
                  t))
         (er hard ctx
             "The symbol ~x0 does not name a function or macro defined in ~
              ACL2."
             (car names)))
        (t (chk-defined-functions (cdr names) ctx wrld))))

(defun get-cltl-command-lst (names ctx wrld)

; Names is a list of function and macro names.  We return a list of definitions
; sufficient for evaluating calls of any name in names (after loading
; load-toothbrush.lsp).  The list is sorted, so that earlier events support
; later ones.

  (prog2$
   (chk-defined-functions names ctx wrld)
   (sort-cltl-commands
    (get-cltl-command-lst-1 names ctx wrld nil nil)
    wrld
    nil)))

(defmacro make-toothbrush (filename &rest names)

; Print a "toothbrush" application to filename, in support of all functions and
; macros in the given input list, names.  That file can be loaded after
; starting Lisp and loading load-toothbrush.lsp, at which point the application
; can be run.

  (declare (xargs :guard (and (stringp filename)
                              (symbol-listp names))))
  `(let ((filename ,filename)
         (names ',names))
     (with-print-defaults
      ((current-package "ACL2")
       (serialize-character-system nil)
       (print-pretty t))
      (mv-let
       (channel state)
       (open-output-channel filename :object state)
       (cond
        ((null channel)
         (er soft 'make-toothbrush
             "Unable to open file ~x0 for output."
             filename))
        (t
         (pprogn (print-objects
                  (cons '(in-package "ACL2")
                        (get-cltl-command-lst names 'top (w state)))
                  channel
                  state)
                 (newline channel state)
                 (close-output-channel channel state)
                 (value filename))))))))
