; Making the "becomes theorem"
;
; Copyright (C) 2014-2021 Kestrel Institute
; Copyright (C) 2015, Regents of the University of Texas
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/world" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
;; (include-book "kestrel/typed-lists-light/cons-listp-dollar" :dir :system)
;; (include-book "kestrel/utilities/make-function-calls-on-formals" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "becomes-theorem-names")

;; ;; all the calls of the calls-on-formals should be bound in the function-renaming
;; (defun rename-functions-in-calls (calls-on-formals function-renaming)
;;   (declare (xargs :guard (and (cons-listp$ calls-on-formals)
;;                               (function-renamingp function-renaming))))
;;   (if (endp calls-on-formals)
;;       nil
;;     (let* ((call (first calls-on-formals))
;;            (fn (ffn-symb call))
;;            (new-fn (lookup-eq-safe fn function-renaming))
;;            (new-call (cons new-fn (fargs call))))
;;       (cons new-call
;;             (rename-functions-in-calls (rest calls-on-formals) function-renaming)))))

(defund call-of-any (term fns)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp fns))))
  (and (consp term)
       (member-eq (ffn-symb term) fns)))

(defun calls-in-top-level-equalities (clause fns)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (symbol-listp fns))))
  (if (endp clause)
      nil
    (let ((lit (first clause)))
      (if (not (and (call-of 'equal lit)
                    (equal 2 (len (fargs lit)))))
          (calls-in-top-level-equalities (rest clause) fns)
        ;; it's and equality literal:
        (append (if (call-of-any (farg1 lit) fns) (list (farg1 lit)) nil)
                (if (call-of-any (farg2 lit) fns) (list (farg2 lit)) nil)
                (calls-in-top-level-equalities (rest clause) fns))))))

(defun expand-calls-in-conclusion-equalities (clause target-fns)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (symbol-listp target-fns))))
  (let ((calls-to-expand (calls-in-top-level-equalities clause target-fns)))
    (progn$ ;; (cw "(clause is ~x0.~%  calls to expand are: ~x1)~%" clause calls-to-expand)
            `(:expand (,@calls-to-expand)))))

;; Makes a theorem equating an arbitrary call of FN with a call of NEW-FN on the same arguments.
;; REC is either nil (function is non-recursive), :single, or :mutual.
;; TODO: Improve this to use the $not-normalized rules if indicated for fn and/or new-fn (add options for this)
;; The BASE-THEORY is often (theory 'minimal-theory).
;; TODO: Add support for passing in the becomes theorem name?
;; Note that some args are not used in the :mutual case -- split out that case?
(defun make-becomes-theorem (fn ; name of the old function
                             new-fn ; name of the new function (must have the same params)
                             rec ; nil (for non-recursive), :single, or :mutual
                             thm-enable ;whether the "becomes theorem" should be enabled
                             enables ; rules to always enable in the proof ; drop??
                             base-theory ; ex: '(theory 'minimal-theory) or '(current-theory :here)
                             state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp fn)
                              (symbolp new-fn)
                              (member-eq rec '(nil :single :mutual))
                              (booleanp thm-enable)
                              (true-listp enables))))
  (let ((formals (fn-formals fn (w state)))
        ;; Choose which kind of defthm to use (todo: add support for defun-nx and defund-nx):
        (defthm-variant (if thm-enable 'defthm 'defthmd)))
    `(,defthm-variant ,(becomes-theorem-name fn new-fn)
       (equal (,fn ,@formals)
              (,new-fn ,@formals))
       ,@(if (eq rec :mutual) ;weird format for make-flag hints (todo: switch to putting all the hints at the top-level of the make-flag):
             nil ; hints will be added at the defthm-flag level, not for each defthm
           (if (eq rec :single)
               `(:hints (("Goal" :induct (,fn ,@formals) ; should we induct in the new or old function (old, since we know it is recursive?)?
                          :do-not '(generalize eliminate-destructors)
                          :in-theory (append '((:i ,fn)
                                               ,fn
                                               ,new-fn
                                               ,@enables)
                                             ,base-theory))
                         ;; todo: want to use this, but it breaks extract-subfunction:
                         ;; (and stable-under-simplificationp
                         ;;      (expand-calls-in-conclusion-equalities clause '(,fn ,new-fn)))
                         ))
             ;; non-recursive case:
             `(:hints (("Goal" :in-theory (append '(,fn ,new-fn ,@enables) ,base-theory)
                        :do-not '(generalize eliminate-destructors)
                        :do-not-induct t)))))
       ;; Put in a flag for defthm-flag-xxx if appropriate:
       ,@(and (eq rec :mutual) (list :flag fn)))))

;; Make the "becomes theorems" for the given FNS, using the FUNCTION-RENAMING to get their new names.
;; This is for the mutual-recursion case only.
;; TODO: This could wrap the theorems in a call to defthm-flag-xxx
;; TODO: Args affecting hints should be irrelevant once we move the hints to the defthm-flag
(defun make-becomes-theorems (fns
                              function-renaming
                              thm-enable ; whether all the theorems should be enabled
                              state)
  (declare (xargs :stobjs state :guard (and (symbol-listp fns)
                                            (function-renamingp function-renaming)
                                            (booleanp thm-enable))))
  (if (endp fns)
      nil
    (let ((fn (first fns)))
      (cons (make-becomes-theorem fn (lookup-eq-safe fn function-renaming) :mutual thm-enable nil nil state)
            (make-becomes-theorems (rest fns) function-renaming thm-enable state)))))

;; Wraps the becomes-theorems in a call of defthm-flag-XXX and adds the hints.
(defund make-becomes-defthm-flag (flag-function-name
                                  becomes-theorems
                                  fns
                                  function-renaming
                                  enables
                                  base-theory ; ex: (theory 'minimal-theory) or (current-theory :here)
                                  wrld)
  (declare (xargs :guard (and (symbolp flag-function-name)
                              (true-listp becomes-theorems)
                              (symbol-listp fns)
                              (true-listp enables)
                              (function-renamingp function-renaming)
                              (plist-worldp wrld)))
           (ignore wrld))
  (let* ((new-fns (strip-cdrs function-renaming))
         ;;(old-fn-calls (make-function-calls-on-formals fns wrld))
         ;;(new-fn-calls (rename-functions-in-calls old-fn-calls function-renaming))
         )
    `(,(pack$ 'defthm- flag-function-name) ;; this is the custom tool generated by make-flag
      ,@becomes-theorems
      :hints (("Goal" :in-theory (append '(;;,@fns
                                           ;;,@new-fns
                                           ,@enables
                                           ,(pack$ flag-function-name '-equivalences) ;;gross that make-flag doesn't put in this hint for you? (todo: what is this?)
                                           (:i ,flag-function-name))
                                         ,base-theory)
               :do-not '(generalize eliminate-destructors)
               ;; We can't simply instruct ACL2 to expand calls of these
               ;; functions on their formals, because substitution may replace
               ;; some of the formals
               ;; :expand (,@old-fn-calls ,@new-fn-calls)
               )
              (and stable-under-simplificationp
                   (expand-calls-in-conclusion-equalities clause '(,@fns ,@new-fns)))
              ))))
