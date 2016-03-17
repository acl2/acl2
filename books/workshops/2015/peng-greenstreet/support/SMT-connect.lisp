;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software

;;
;; This file is adapted from :doc define-trusted-clause-processor
;; The dependent files, instead of being in raw Lisp, are in ACL2.
;; That makes me doubt if I really need to do defstub, progn,
;; progn!, and push-untouchable...
;;
;; However, I'm using them right now in case if there are
;; behaviours with those constructs that are not known to me.
;;
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/typed-lists/cons-listp" :dir :system)
(set-state-ok t)
(set-ignore-ok t)

(defstub acl2-my-prove
  (term fn-lst fn-level uninterpreted fname let-expr new-hypo let-hints hypo-hints main-hints smt-config custom-config state)
  (mv t nil nil nil nil nil state))

(program)
(defttag :Smtlink)

(include-book "SMT-py")
(include-book "config")
(include-book "helper")
(value-triple (tshell-ensure))

(progn
; We wrap everything here in a single progn, so that the entire form is
; atomic.  That's important because we want the use of push-untouchable to
; prevent anything besides Smtlink-raw from calling acl2-my-prove.

  (progn!

   (set-raw-mode-on state) ;; conflict with assoc, should use assoc-equal, not assoc-eq
   
   (defun acl2-my-prove (term fn-lst fn-level uninterpreted fname let-expr new-hypo let-hints hypo-hints main-hints smt-config custom-config state)
     (my-prove term fn-lst fn-level uninterpreted fname let-expr new-hypo let-hints hypo-hints main-hints smt-config custom-config state))
   )

  ;; Supported arguments:
  ;; expand - functions : a list of functions to be expanded
  ;;          expansion-level : how many levels to expand a function
  ;; uninterpreted-functions : a list of functions taken as uninterpreted functions after the expansion
  ;; python-file : specify the file name of the python file to write to
  ;; let : specify to replace a sub-expression as a variable
  ;; hypothesis : specify hypotheses about those variables introduces by let-expr
  ;; use - type : hints for type predicates from function expansion
  ;;       hypo : hints for sub-expression hypotheses
  ;;       main : hints for the main clause returned
  (defun Smtlink-arguments (hint)
    (b* ((fn-lst (cadr (assoc ':functions
                              (cadr (assoc ':expand hint)))))
         (fn-level (cadr (assoc ':expansion-level
                                (cadr (assoc ':expand hint)))))
         (uninterpreted (cadr (assoc ':uninterpreted-functions hint)))
         (fname (cadr (assoc ':python-file hint)))
         (let-expr (cadr (assoc ':let hint)))
         (new-hypo (cadr (assoc ':hypothesize hint)))
         (let-hints (cadr (assoc ':let
                                 (cadr (assoc ':use hint)))))
         (hypo-hints (cadr (assoc ':hypo
                                  (cadr (assoc ':use hint)))))
         (main-hints (cadr (assoc ':main
                                  (cadr (assoc ':use hint))))))
        (mv fn-lst fn-level uninterpreted fname let-expr new-hypo let-hints hypo-hints main-hints)
        )
    )

  (defun implies-form (cl state)
    (cond ((and (equal (len cl) 3)
                (equal (car cl) 'implies))
           (mv cl state)) ; an implication
          ((cons-listp cl)
           (b* (((mv erp clause state) (translate (prettyify-clause cl nil (w state)) t nil t nil (w state) state)))
               (mv clause state))) ; a disjunction
          (t (mv (er hard? 'top-level "smtlink: sorry, not sure how to handle this: ~%~q0~%" cl) state)) ; not sure what that is
          ))
  
  (defun Smtlink-raw (cl hint state custom-config)
    (declare (xargs :guard (pseudo-term-listp cl)
                    :mode :program))
    (prog2$ (cw "Original clause(connect): ~x0" cl)
    (b* (((mv fn-lst fn-level uninterpreted fname let-expr new-hypo let-hints hypo-hints main-hints)
          (Smtlink-arguments hint))
         ((mv clause state)
          (implies-form cl state))
         ((mv res expanded-cl type-related-theorem hypo-theorem fn-type-theorem type-or-original state)
          (acl2-my-prove clause fn-lst fn-level uninterpreted fname let-expr new-hypo let-hints hypo-hints main-hints (if custom-config (smt-cnf) (default-smtlink-config)) custom-config state)))
        (if res
            (let ((res-clause (append (append (append (append fn-type-theorem type-related-theorem) (list type-or-original)) hypo-theorem)
                                      (list (append expanded-cl cl))
                                      )))
              (prog2$ (cw "Expanded clause(connect): ~q0 ~% Success!~%" res-clause)
                      (mv nil res-clause state)))
          (prog2$ (cw "~|~%NOTE: Unable to prove goal with ~
                                 my-clause-processor and indicated hint.~|")
                  (mv t (list cl) state))))))

  (defun Smtlink-fn (cl hint state)
    (declare (xargs :guard (pseudo-term-listp cl)
                    :mode :program))
        (Smtlink-raw cl hint state nil))

  (defmacro Smtlink (cl hint)
    `(Smtlink-fn ,cl ,hint state))

  (defun Smtlink-custom-config-fn (cl hint state)
    (declare (xargs :guard (pseudo-term-listp cl)
                    :mode :program))
        (Smtlink-raw cl hint state t))

  (defmacro Smtlink-custom-config (cl hint)
    `(Smtlink-custom-config-fn ,cl ,hint state))

  (push-untouchable acl2-my-prove t)
  )

(define-trusted-clause-processor
  Smtlink-fn
  nil
  :ttag Smtlink)

(define-trusted-clause-processor
  Smtlink-custom-config-fn
  nil
  :ttag Smtlink-custom-config)
