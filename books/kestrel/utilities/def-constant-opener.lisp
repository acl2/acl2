; A tool to open ground applications of functions
;
; Copyright (C) 2018-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains a utility that generates an opener theorem for a function
;; call where the rule fires only when all of the function's arguments are
;; constants.  This can be helpful when the function's executable-counterpart
;; is disabled.  The Axe tool also makes extensive use of def-constant-opener.

;; See also the defopeners tool.  One difference is that defopeners makes a
;; separate rule for each IF branch of the function, whereas
;; def-constant-opener makes a single rule but expects all IF tests to be
;; resolved since all of the arguments are constants.  Another difference is
;; that def-constant-opener can use the untranslated function body -- which is
;; a bit nicer -- since it doesn't have to analyze the body.

;; See also the tool in books/misc/defopener.  That tool also
;; does simplification.

;; See def-constant-opener-tests.lisp for some tests of this utility.

;; TODO: Add support for mutual-recursion.

(include-book "world")
(include-book "kestrel/utilities/user-interface" :dir :system) ;; for control-screen-output
(include-book "pack")
(include-book "my-get-event")
(include-book "defun-forms") ;for get-body-from-event
(include-book "misc/install-not-normalized" :dir :system)

(defun make-quotep-hyps-aux (vars)
  (if (endp vars)
      nil
    (cons `(quotep ,(first vars))
          (make-quotep-hyps-aux (rest vars)))))

(defun make-quotep-hyps (vars)
  (if (endp vars)
      t
    (if (eql 1 (len vars))
        `(quotep ,(first vars))
      `(and ,@(make-quotep-hyps-aux vars)))))

;for non-mut-rec
(defun def-constant-opener-fn (fn disable state)
  (declare (xargs :stobjs state
                  :verify-guards nil
                  :mode :program ;because we call my-get-event
                  ))
  (b* ((fn-event (my-get-event fn (w state)))
       (body (get-body-from-event fn fn-event))
       ;; (body (remove-guard-holders body (w state))) ;why?
       (formals (fn-formals fn (w state)))
       (defthm-variant (if disable 'defthmd 'defthm))
       (not-normalized-theorem-name (install-not-normalized-name fn))
       (constant-opener-name (pack-in-package-of-symbol fn fn '-constant-opener)))
    `(progn
       (encapsulate ()
         (local (install-not-normalized ,fn))
         (,defthm-variant ,constant-opener-name
           (implies (syntaxp ,(make-quotep-hyps formals))
                    (equal (,fn ,@formals)
                           ,body))
           :hints (("Goal" :in-theory '(,not-normalized-theorem-name)))))
       ;; show the name of the generated rule:
       (value-triple ',constant-opener-name))))

;hyps should be a list of terms over the formals of the function (can include syntaxp, etc.)
(defmacro def-constant-opener (fn &key
                                   (disable 'nil)
                                   (verbose 'nil))
  (control-screen-output
   (if (member-eq verbose '(t 't)) t nil) ;verbose
   `(make-event (def-constant-opener-fn ',fn ',disable state))))
