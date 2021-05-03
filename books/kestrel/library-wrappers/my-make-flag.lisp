; A variant of make-flag that may be more robust
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/flag" :dir :system)

;; TODO: Have my-make-flag (or make-flag) put in the :ruler-extenders of the old function by default.

(verify-termination flag::get-formals)
;(verify-guards flag::get-formals) ;todo: have make-flag just call FORMALS

(defun replace-non-members-with-nil (items items-to-keep)
  (declare (xargs :guard (and (symbol-listp items)
                              (symbol-listp items-to-keep))))
  (if (endp items)
      nil
    (let ((item (first items)))
      (cons (if (member-eq item items-to-keep)
                item
              nil)
            (replace-non-members-with-nil (rest items) items-to-keep)))))

(defun termination-theorem-subst-for-my-make-flag (clique-fns merged-formals flag-function-name wrld)
  (declare (xargs :guard (and (symbol-listp clique-fns)
                              (symbol-listp merged-formals))
                  :verify-guards nil ; because this calls flag::get-formals
                  ))
  (if (endp clique-fns)
      nil
    (let* ((fn (first clique-fns))
           (fn-formals (flag::get-formals fn wrld)))
      (cons
       ;; replaces fn by the equivalent call of the flag function:
       ;; example: (pseudo-termp (lambda (x) (flag-pseudo-termp 'pseudo-termp x nil)))
       `(,fn (lambda ,fn-formals (,flag-function-name ',fn ,@(replace-non-members-with-nil merged-formals fn-formals))))
       (termination-theorem-subst-for-my-make-flag (rest clique-fns) merged-formals flag-function-name wrld)))))

(defun my-make-flag-fn (flag-function-name fn body ruler-extenders wrld)
  (declare (xargs :guard (and (symbolp flag-function-name) ; may be :auto
                              (symbolp fn)
                              )
                  :mode :program))
  (let* ((flag-function-name (if (eq :auto flag-function-name)
                                 ;; create the flag function name from the function name:
                                 (packn (list 'flag- fn)) ;(intern-in-package-of-symbol (concatenate 'string "FLAG-" (symbol-name fn)) fn)
                               flag-function-name))
         ;; This stuff is based on what make-flag does:
         (clique-fns (flag::get-clique-members fn wrld))
         (alist (pairlis$ clique-fns clique-fns))
         (merged-formals (flag::merge-formals alist wrld))
         (termination-theorem-subst (termination-theorem-subst-for-my-make-flag clique-fns merged-formals flag-function-name wrld)))
    `(make-flag ,flag-function-name ;; this is optional for make-flag
                ,fn
                :body ,body
                ,@(if (eq :auto ruler-extenders)
                      nil
                    `(:ruler-extenders ,ruler-extenders))
                ;; If the termination theorem mentions the fn or its clique
                ;; members, we need to change it to mention the equivalent call
                ;; of the flag function:
                :hints (("Goal" :use (:instance (:termination-theorem ,fn ,termination-theorem-subst))
                         ;; :in-theory nil ;;too restrictive
                         :in-theory (theory 'minimal-theory) ;;still too restrictive?
                         )))))

;; This is a wrapper around make-flag that attempts to be more robust.  It uses
;; the :termination-theorem of the given function in the :hints supplied to
;; make-flag (to ensure that the proof works without hints).  CAVEAT: Such a
;; proof may be *much* slower than the direct proof done by make-flag.  TODO:
;; Consider how to speed up measure proofs that use existing
;; :termination-theorems.  Matt K suggests using `(:instructions
;; ((:prove-termination ..))) as in
;; kestrel-acl2/transformations/simplify-defun-impl.lisp, but make-flag does
;; not currently accept :instructions.  Once we figure out how to make
;; the proof both fast and robust, consider improving make-flag itself.
(defmacro my-make-flag (fn &key
                           (body 'nil) ;; the :body arg to pass to make-flag
                           (flag-function-name ':auto) ;; to override the default name of the flag-function
                           (ruler-extenders ':auto)
                           )
  `(make-event (my-make-flag-fn ',flag-function-name ',fn ',body ',ruler-extenders (w state))))
