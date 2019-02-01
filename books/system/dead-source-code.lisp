; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, December, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See comments near the end of this file for how to use this tool to remove
; dead code from the ACL2 sources.  If you want to remove dead code from your
; own applications, look instead at community book books/misc/dead-events.lisp.

(in-package "ACL2")

(program)
(set-state-ok t)

(defun simple-translate (x wrld)

; Note that defconst-fn calls defconst-val, which calls
; simple-translate-and-eval, which makes the call (translate x '(nil) nil t ctx
; wrld state).  On the other hand, defthm-fn1 makes the call (translate term t
; t t ctx wrld state), which presumably is more permissive except for requiring
; logic mode.  We use a conservative call of translate-cmp that covers both
; cases.

  (mv-let (erp result)
          (translate-cmp x
                         t                 ; stobjs-out
                         nil               ; logic-modep
                         t                 ; known-stobjs
                         'simple-translate ; ctx
                         wrld
                         (default-state-vars nil
                           :temp-touchable-fns t
                           :temp-touchable-vars t))
          (cond ((and erp result)
                 (er hard! erp
                     "~@0"
                     result))
                (erp (er hard! 'simple-translate
                         "Unexpected erp: ~x0"
                         erp))
                (t result))))

(defun simple-translate-lst (lst wrld)
  (cond ((endp lst) nil)
        (t (cons (simple-translate (car lst) wrld)
                 (simple-translate-lst (cdr lst) wrld)))))

(defun constraint-info-fnnames (fn wrld)
  (mv-let (flg x)
          (constraint-info fn wrld)
          (cond ((null flg)
                 (all-fnnames x))
                ((unknown-constraints-p x)
                 nil)
                (t
                 (all-fnnames-lst x)))))

(defun constraint-info-fnnames-lst (fns wrld)
  (cond ((endp fns) nil)
        (t (union-eq (constraint-info-fnnames (car fns) wrld)
                     (constraint-info-fnnames-lst (cdr fns) wrld)))))

(defun constraint-fnnames (fn wrld)
  (cond ((programp fn wrld)
         (let ((ev (get-event fn wrld)))
           (case (car ev)
             (mutual-recursion
              (all-fnnames-lst (simple-translate-lst
                                (strip-last-elements (cdr ev))
                                wrld)))
             (defun
               (all-fnnames (simple-translate (car (last ev)) wrld)))
             (otherwise (er hard! 'constraint-fnnames
                            "Did not find defun for ~x0"
                            fn)))))
        (t (let ((recp (getprop fn 'recursivep nil 'current-acl2-world wrld)))
             (cond
              ((cdr recp) (constraint-info-fnnames-lst recp wrld))
              (t (constraint-info-fnnames fn wrld)))))))

(defun update-live-names-array-lst (ar fns wrld)
  (cond
   ((endp fns) ar)
   (t (let ((num (getprop (car fns) 'absolute-event-number nil
                          'current-acl2-world wrld)))
        (cond
         ((null num)
          (er hard! 'update-live-names-array-lst
              "No absolute event number found for \"function\" ~x0."
              (car fns)))
         ((aref1 'live-names ar num)
          (update-live-names-array-lst ar (cdr fns) wrld))
         (t (let* ((ar (aset1 'live-names ar num t))
                   (ar (update-live-names-array-lst
                        ar
                        (constraint-fnnames (car fns) wrld)
                        wrld))
                   (ar (update-live-names-array-lst
                        ar
                        (all-fnnames (guard (car fns) nil wrld))
                        wrld)))
              (update-live-names-array-lst ar (cdr fns) wrld))))))))

(defun corollary-fnnames (classes)
  (cond ((endp classes) nil)
        (t (let ((cor (cadr (assoc-keyword :COROLLARY (cdr (car classes))))))
             (cond (cor ; always true?
                    (all-fnnames1 nil
                                  cor
                                  (corollary-fnnames (cdr classes))))
                   (t (corollary-fnnames (cdr classes))))))))

(defun live-names-array-2 (ar name prop val wrld)
  (case prop
    (macro-body
     (let ((macro-fn

; Consider for example set-evisc-tuple, which generates a call of
; set-evisc-tuple-fn.

            (case-match val
              (('cons ('quote fn) &)
               (and (function-symbolp fn wrld)
                    fn))
              (('quote (fn . &))
               (and (function-symbolp fn wrld)
                    fn))
              (& nil)))
           (ar (update-live-names-array-lst
                ar
                (all-fnnames (guard name nil wrld))
                wrld)))
       (update-live-names-array-lst
        ar
        (if macro-fn
            (cons macro-fn (all-fnnames val))
          (all-fnnames val))
        wrld)))
    (theorem
     (update-live-names-array-lst ar (all-fnnames val) wrld))
    (const
     (let* ((ev (get-event name wrld))
            (term (simple-translate (caddr ev) wrld)))
       (update-live-names-array-lst ar (all-fnnames term) wrld)))
    (classes
     (update-live-names-array-lst ar (corollary-fnnames val) wrld))
    (otherwise ar)))

(defun live-names-array-1 (ar tail wrld)
  (cond ((endp tail) ar)
        (t (live-names-array-1
            (live-names-array-2 ar (caar tail) (cadar tail) (cddar tail) wrld)
            (cdr tail)
            wrld))))

; Start code for initializing 'live-names array.

(defun filter-fns (fns wrld acc)
  (cond ((endp fns) acc)
        ((not (function-symbolp (car fns) wrld))
         (filter-fns (cdr fns) wrld acc))
        (t (filter-fns (cdr fns)
                       wrld
                       (cons (car fns) acc)))))

(defun initial-event-defmacros-fns (lst wrld)

; Lst is a tail of *initial-event-defmacros*.  We do this computation because
; ((initial-event-defmacros-fns *initial-event-defmacros*) is not quite a
; subset of (primitive-event-macros-fns *primitive-event-macros*).

  (cond ((endp lst) nil)
        (t (let ((ev (car lst)))
             (case-match ev
               (('defmacro name &
                  ('list ('quote name-fn) . &))
                (cond ((and (function-symbolp name-fn wrld)
                            (eq name-fn
                                (intern (concatenate 'string
                                                     (symbol-name name)
                                                     "-FN")
                                        "ACL2")))
                       (cons name-fn
                             (initial-event-defmacros-fns (cdr lst) wrld)))
                      (t (initial-event-defmacros-fns (cdr lst) wrld))))
               (& (initial-event-defmacros-fns (cdr lst) wrld)))))))

(defun primitive-event-macros-fns (lst wrld)

; Lst is a tail of (primitive-event-macros).

  (cond ((endp lst) nil)
        (t (let ((fn (intern (concatenate 'string
                                          (symbol-name (car lst))
                                          "-FN")
                             "ACL2")))
             (cond ((function-symbolp fn wrld)
                    (cons fn (primitive-event-macros-fns (cdr lst) wrld)))
                   (t (primitive-event-macros-fns (cdr lst) wrld)))))))

(defun fns-with-lemmas (wrld acc)

; With this function we pick up function symbols like weak-linear-lemma-p that
; we might otherwise miss.

  (cond ((endp wrld) acc)
        (t (fns-with-lemmas
            (cdr wrld)
            (let ((trip (car wrld)))
              (cond ((and (eq (cadr trip) 'lemmas)
                          (cddr trip))
                     (cons (car trip) acc))
                    (t acc)))))))

(defun live-names-array-seeds (state)
  (prog2$
   (or (boundp-global 'live-fn-seeds state)
       (er hard 'live-names-array-seeds
           "Need to assign to state global 'live-fn-seeds!"))
   (let ((wrld (w state)))
     (filter-fns *acl2-exports*
                 wrld
                 (append (f-get-global 'live-fn-seeds state)
                         (strip-cars (table-alist 'pc-command-table wrld))
                         (strip-cars (all-attachments wrld))
                         (strip-cdrs (all-attachments wrld))
                         (initial-event-defmacros-fns *initial-event-defmacros*
                                                      wrld)
                         (primitive-event-macros-fns (primitive-event-macros)
                                                     wrld)
                         (fns-with-lemmas wrld nil))))))

(defun initial-live-names-array (wrld state)
  (let* ((size (1+ (max-absolute-event-number wrld)))
         (ar (compress1 'live-names
                        `((:header :dimensions (,size)
                                   :maximum-length ,size
                                   :default nil
                                   :name live-names)))))
    (update-live-names-array-lst ar (live-names-array-seeds state) wrld)))

(defun live-names-array (state)
  (let ((wrld (w state)))
    (live-names-array-1 (initial-live-names-array wrld state) wrld wrld)))

(defun dead-names-1 (ar tail wrld acc)
  (cond ((endp tail) (remove-duplicates acc))
        ((eq (cadr (car tail)) 'formals)
         (let* ((fn (car (car tail)))
                (num (getprop fn 'absolute-event-number nil
                              'current-acl2-world wrld)))
           (dead-names-1 ar
                         (cdr tail)
                         wrld
                         (cond ((aref1 'live-names ar num) acc)
                               (t (cons fn acc))))))
        (t (dead-names-1 ar
                         (cdr tail)
                         wrld
                         acc))))

(defun boot-strap-world (wrld)
  (cond ((null wrld)
         (er hard 'boot-strap-world
             "Didn't find expected command-landmark!"))
        ((let ((trip (car wrld)))
           (and (eq (car trip) 'command-landmark)
                (eq (cadr trip) 'global-value)
                (equal (access-command-tuple-form (cddr trip))
                       '(exit-boot-strap-mode))))
         wrld)
        (t (boot-strap-world (cdr wrld)))))

(defun dead-system-names (state)
  (let ((wrld (w state)))
    (dead-names-1 (live-names-array state) (boot-strap-world wrld) wrld nil)))

; Sample usage:
#||
(defttag t) ; to translate a call of sys-call, for example
(assign live-fn-seeds

; This list contains functions that would otherwise be considered part of the ;
; dead code, even though they should not be. ;

        '(ld-fn
          times-expt-2-16-mod-m31 ; only used by GCL ;
          show-poly-lst ; for system debugging ;
          brr-prompt ; argument of set-ld-prompt ;
          proof-builder-cl-proc
          ext-ancestors-attachments ; called by memoize-fn ;
          tree-occur-eq ; called by #-acl2-loop-only definition
; The following are hidden by wormholes, e.g., ;
; show-accumulated-persistence-phrase is hidden by a call of wormhole in ;
; show-accumulated-persistence.  Maybe we can automate these. ;
          show-accumulated-persistence-phrase
          restore-brr-globals
          push-brr-stack-frame
          put-brr-local-lst
          brr-result
          tilde-@-failure-reason-phrase
          fc-report1
; The following are generated by macro calls in a way that might be difficult
; to capture automatically.
          pop-inhibit-output-lst-stack
          push-inhibit-output-lst-stack
          set-parallel-execution-fn
          ))
(dead-system-names state)
||#

; More work needs to be done to use this tool properly.  As of this writing,
; the above call of dead-system-names returns a list of length 320.  Some
; elements of that list, for example union-eq-cars and
; make-new-goals-from-assumptions, are probably dead code.  But most others
; probably are not; they might be called from functions defined in raw Lisp or
; otherwise have escaped our notice, so far.
