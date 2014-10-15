; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "misc/hons-help2" :dir :system)

;; WHY WE NO LONGER INLINE
;;
;; Until inlining support was added to ACL2 proper, we used the misc/definline
;; book to which supported it via a ttag.  But now that inlining is "properly"
;; supported, ACL2 changes the names of functions into things like foo$inline.
;;
;; I got this mostly working for the ACL2 side of things, e.g., by using the
;; new :e instead of :executable-counterpart, and by patching verify-guards to
;; do a macro dereference.  So as far as the ACL2 stuff goes, this isn't too
;; horrible, although it's still pretty ugly to have to think about this.
;;
;; But when it comes to bootstrapping, the whole $inline versus not $inline
;; thing is a real pain in the ass, because we want to just take the ACL2
;; definitions and turn them into Milawa definitions, but then suddenly our
;; function bodies are no longer calling the "right" functions, etc.
;;
;; Rather than make Milawa's functions have ugly names like nfix$inline, it
;; seems best to just not bother with inlining in ACL2.  This is a somewhat
;; significant speed hit to bootstrapping, but, well, it's ACL2's fault for
;; implementing inlining in this terrible way.
;;
;; (include-book "misc/definline" :dir :system :ttags '(definline))

(include-book "io" :ttags :all)
(include-book "half-translate")


;; Our defun macro.
;;
;; We implement several features not found in the regular defun event.
;;
;;   - If :skip-guards is on the features-list, we strip out all the guards
;;     specified by any function and set verify-guards to nil.
;;
;;   - We disable any :type-prescription rules that are generated.
;;
;;   - We write out a LaTeX file in autodoc/defun-foo.tex which includes
;;     the definition of foo.
;;
;;   - We add an entry to the syntax-defuns table, which is used as part of
;;     the bootstrapping phase.

(defun aux-get-xarg (key x)
  ;; X should be a list of keywords and values given to xargs.  We return the
  ;; pair (key . value), unless key does not occur in xargs in which case we
  ;; return nil.
  (declare (xargs :guard t))
  (if (and (consp x)
           (consp (cdr x)))
      (if (equal (car x) key)
          (cons (first x) (second x))
        (aux-get-xarg key (cddr x)))
    nil))

(defun get-xarg (key x)
  ;; We look for any occurrences of (xargs ...) within x, then look up the key
  ;; in the first occurrence we find.  We return the (key . value) pair if key
  ;; occurs among the xargs, or nil otherwise.
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((equal (car x) 'quote)
         nil)
        ((equal (car x) 'xargs)
         (aux-get-xarg key (cdr x)))
        (t
         (or (get-xarg key (car x))
             (get-xarg key (cdr x))))))

(defun aux-remove-xarg (key x)
  ;; X should be a list of keywords and values given to xargs.  We remove any
  ;; instances of the specified key and its value.
  (declare (xargs :guard t))
  (if (and (consp x)
           (consp (cdr x)))
      (if (equal (car x) key)
          (aux-remove-xarg key (cddr x))
        (cons (first x)
              (cons (second x)
                    (aux-remove-xarg key (cddr x)))))
    nil))

(defun remove-xarg (key x)
  ;; We look for any occurrences of (xargs ...) within x, then remove the
  ;; specified key and its value from these xargs.
  (declare (xargs :guard t))
  (cond ((atom x)
         x)
        ((equal (car x) 'quote)
         x)
        ((equal (car x) 'xargs)
         (cons 'xargs (aux-remove-xarg key (cdr x))))
        (t
         (cons (remove-xarg key (car x))
               (remove-xarg key (cdr x))))))

(defun set-xarg (key value x)
  ;; We look for any occurrences of (xargs ...) within x.  If key occurs among
  ;; these xargs, we erase it.  Then, we add the new key and value.
  (declare (xargs :guard t))
  (cond ((atom x)
         x)
        ((equal (car x) 'quote)
         x)
        ((equal (car x) 'xargs)
         (cons 'xargs (list* key value (aux-remove-xarg key (cdr x)))))
        (t
         (cons (set-xarg key value (car x))
               (set-xarg key value (cdr x))))))

(defun remove-milawa-xargs (x)
  ;; We look for occurrences of (xargs ...) within x and remove any occurrences
  ;; of milawa-specific xargs.
  (declare (xargs :guard t))
  (remove-xarg :export x))

(defun remove-guards (x)
  ;; X should be the arguments given to a defun.  We erase any :guard xargs and
  ;; set :verify-guards to nil.
  (declare (xargs :guard t))
  (set-xarg :verify-guards nil (remove-xarg :guard x)))

(defmacro MILAWA::verify-guards (name &rest args)
  ;; In guard-skipping mode, we ignore any verify-guards events and turn them
  ;; into value-triples (i.e., no-ops).  Otherwise, we just turn them into
  ;; ACL2::verify-guards commands.
  #+skip-guards
  `(value-triple '(ignoring-guards ,name . ,args))
  #-skip-guards
  ;; Fancy make-event stuff to deal with new $inline crap in ACL2 6.2,
  ;; suggested by Matt Kaufmann
  `(make-event
    (let ((fn (deref-macro-name ',name (macro-aliases (w state)))))
      (list* 'verify-guards fn ',args))))



(defun defun-to-latex (defun-args state)
  ;; We write autodoc/defun-foo.tex, so that the definition of foo can be kept
  ;; current in latex documentation.
  (declare (xargs :mode :program :stobjs state))
  (let* ((name     (first defun-args))
         (args     (second defun-args))
         (body     (car (last defun-args)))
         (filename (concatenate 'string "autodoc/defun-"
                                (mangle-filename (string-downcase (symbol-name name)))
                                ".tex")))
    ;; This command changed in v3-5.  We still want to support 3-4, so we check
    ;; for it explicitly.
    (let* ((state #+v3-4 (set-acl2-print-case :downcase)
                  #-v3-4 (set-print-case :downcase state))
           (state (set-fmt-hard-right-margin 80 state))
           (state (set-fmt-soft-right-margin 75 state)))
      (mv-let
       (channel state)
       (open-output-channel$ filename :character state)
       (let ((state (fms "\\begin{acl2}~%~q0~t1$=$~%~q2\\end{acl2}"
                         (list (cons #\0 (cons name args))
                               (cons #\1 2)
                               (cons #\2 body))
                         channel state nil)))
         (close-output-channel channel state))))))

(table milawa 'syntax-defun-entries nil)
(table milawa 'acl2-defun-entries nil)

(defun get-syntax-defun-entries (world)
  (cdr (assoc 'syntax-defun-entries (table-alist 'milawa world))))

(defun get-acl2-defun-entries (world)
  (cdr (assoc 'acl2-defun-entries (table-alist 'milawa world))))

(defun clean-up-body (x)
  ;; When we "export" definitions to Milawa, we strip away a custom ACL2
  ;; things.
  (if (consp x)
      (cond ((and (equal (car x) 'quote)
                  (equal (len x) 2))
             ;; Do not descend into quoted constants
             x)
            ((and (equal (car x) 'ACL2::time$)
                  (equal (len x) 2))
             ;; Simplify (ACL2::time$ x) to x
             (clean-up-body (second x)))
            ((and (equal (car x) 'ACL2::prog2$)
                  (equal (len x) 3))
             ;; Simplify (ACL2::prog2$ x y) to y
             (clean-up-body (third x)))
            ((and (equal (car x) 'ACL2::prog1$)
                  (equal (len x) 3))
             ;; Simplify (ACL2::prog1$ x y) to x
             (clean-up-body (second x)))
            ((equal (car x) 'ACL2::ec-call)
             ;; Simplify (ACL2::ec-call x) to x
             (clean-up-body (second x)))
            ((or (equal (car x) 'ACL2::cw)
                 (equal (car x) 'ACL2::cw!))
             ;; Simplify (ACL2::cw ...) and (ACL2::cw! ...) to nil
             nil)
            ((equal (car x) 'ACL2::hist)
             ;; Simplify (ACL2::hist x y ...) to (ACL2::list x y ...)
             (cons 'ACL2::list
                   (clean-up-body (cdr x))))
            ((and (equal (car x) 'ACL2::hons)
                  (equal (len x) 3))
             ;; Simplify (ACL2::hons x y) to (ACL2::cons x y)
             (list 'ACL2::cons
                   (clean-up-body (second x))
                   (clean-up-body (third x))))
            ((and (or (equal (car x) 'let)
                      (equal (car x) 'let*))
                  (equal (len x) 4)
                  (consp (third x))
                  (equal (car (third x)) 'declare))
             ;; Simplify (let ((blah)) (declare ...) body) to (let ((blah)) body)
             (list (first x)
                   (clean-up-body (second x))
                   (clean-up-body (fourth x))))
            (t
             (cons (clean-up-body (car x))
                   (clean-up-body (cdr x)))))
    x))

(defun defun-to-syntax-table-entry (defun-args state)
  (declare (xargs :mode :program :stobjs state))
  (let ((export (get-xarg :export defun-args))
        (mode   (get-xarg :mode defun-args)))
    (cond ((and (consp export)
                (not (cdr export)))
           ;; Found (:export nil) -- We are to skip this %SYNTAX-DEFUN.
           (mv nil `(value-triple :invisible) state))
          ((and (consp mode)
                (equal (cdr mode) :program))
           ;; Program mode function -- We are to skip this %SYNTAX-DEFUN
           (mv nil `(value-triple :invisible) state))
          (t
           (let* ((name (first defun-args))
                  (args (second defun-args)))
             (mv-let (erp body state)
                     (if (consp export)
                         ;; Found (:export ...) -- We pretend that the
                         ;; function's body is "..." and don't do any cleaning
                         (mv nil (cdr export) state)
                       ;; No (:export ...) -- We use the real body, half-translated
                       ;; and cleaned up.
                       (half-translate (clean-up-body (car (last defun-args))) state))
                     (if erp
                         (mv erp body state)
                       (mv nil
                           `(table milawa 'syntax-defun-entries
                                   (cons '(MILAWA::%syntax-defun ,name ,args ,body)
                                         (get-syntax-defun-entries ACL2::world)))
                           state))))))))

(defun MILAWA::defun-fn (type args)
  (declare (xargs :mode :program))
  ;; In guard-skipping mode, we strip out guards from the xargs and insert an
  ;; explicit :verify-guards nil command.  Otherwise, we just turn them into
  ;; ACL2::defun's and disable any type prescription generated.
  `(encapsulate
    ()
    ;; Submit the defun with or without guards as necessary
    #+skip-guards
    (,type ,@(remove-guards (remove-milawa-xargs args)))
    #-skip-guards
    (,type ,@(remove-milawa-xargs args))
    ;; Disable the type prescription, if one exists
    (make-event
     (let* ((fn ',(car args))
            (props (getprops fn 'current-acl2-world (w state)))
            (symbol-class (cdr (assoc 'symbol-class props))))
       (if (equal symbol-class :program)
           `(value-triple :invisible)
         (prog2$
          (cw "~%Note: Disabling type prescription for ~s0.~%" fn)
          `(in-theory (disable (:t ,fn)))))))
    ;; Write out a LaTeX file for the function
    ;; BOZO disabling this because of stupid fucking OpenMCL .tem file bug ruining all my builds
    (local (make-event ;; (let ((state (defun-to-latex ',args state)))
                         (ACL2::mv nil `(value-triple :invisible) state))) ;; )
    ;; Add the syntax-defun if necessary
    (make-event (defun-to-syntax-table-entry ',args state))
    ;; Add the acl2-defun entry
    (table milawa 'acl2-defun-entries
           (cons ',args (get-acl2-defun-entries world)))))

(defmacro MILAWA::defun (&rest args)
  (MILAWA::defun-fn 'ACL2::defun args))

(defmacro MILAWA::defund (&rest args)
  (MILAWA::defun-fn 'ACL2::defund args))



(ACL2::table milawa 'functions-to-inline nil)

(defun get-functions-to-inline (world)
  (cdr (assoc 'functions-to-inline (ACL2::table-alist 'milawa world))))

(defmacro MILAWA::definline (&rest args)
  ;; Same as defun, but also indicates that the introduced function should be
  ;; inlined.  We haven't yet implemented inlining in ACL2 yet.
  `(ACL2::progn
    ,(MILAWA::defun-fn
      ;; This was formerly 'acl2::definline, but see WHY WE NO LONGER INLINE,
      ;; above.
      'ACL2::defun
      args)
    (ACL2::table milawa 'functions-to-inline
                 (cons ',(first args)
                       (get-functions-to-inline ACL2::world)))))

(defmacro MILAWA::definlined (&rest args)
  ;; Same as defund, but also indicates that the introduced function should be
  ;; inlined.  We haven't implemented inlining in ACL2 yet.
  `(ACL2::progn
    ,(MILAWA::defun-fn
      ;; This was formerly 'acl2::definline, but see WHY WE NO LONGER INLINE,
      ;; above.
      'ACL2::defund
      args)
    (ACL2::table milawa 'functions-to-inline
                 (cons ',(first args)
                       (get-functions-to-inline ACL2::world)))))


(defun create-type-prescriptions (x)
  ;; Given a list of names, we produce a list of (:type-prescription name1),
  ;; ..., (:type-prescription nameN).
  (declare (xargs :guard t))
  (if (consp x)
      (cons (list :t (car x))
            (create-type-prescriptions (cdr x)))
    nil))

(defmacro MILAWA::mutual-recursion (&rest args)
  ;; ACL2::mutual-recursion is messy because ACL2 insists only ACL2::defun(d)s
  ;; appear within it.  We change any MILAWA::defun(d)s to ACL2::defun(d)s.  If
  ;; we are in guard-skipping mode, we also strip out guards and insert
  ;; ":verify-guards nil" as appropriate.
  `(ACL2::progn
    (ACL2::mutual-recursion
     ,@(subst 'ACL2::defun 'MILAWA::defun
              (subst 'ACL2::defund 'MILAWA::defund
                     #+skip-guards
                     (remove-guards args)
                     #-skip-guards
                     args)))
    (make-event
     (if (not ',args)
         `(value-triple :invisible)
       (let* ((names (strip-cadrs ',args))
              (props1 (getprops (car names) 'current-acl2-world (w state)))
              (class1 (cdr (assoc 'symbol-class props1))))
         (if (equal class1 :program)
             ;; ALL functions are program mode.  Nothing to disable.
             `(value-triple :invisible)
           ;; ALL functions are logic mode.  Disable all type prescriptions.
           ;; Defund's are handled by acl2's defund.
           (prog2$
            (cw "~%Note: Disabling type prescriptions for ~&0.~%" names)
            (let ((disables (create-type-prescriptions names)))
              `(in-theory (disable ,@disables))))))))))

