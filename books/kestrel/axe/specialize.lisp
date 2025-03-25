; Specializing functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "evaluator") ; has skip-proofs
(include-book "dagify0")
(include-book "rewriter")
(include-book "kestrel/utilities/ints-in-range" :dir :system)
;(include-book "kestrel/alists-light/lookup" :dir :system)
;(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))

;; todo: move this stuff?:

;fixme keep this list up to date - does it exist elsewhere?
;ffixme some of these (the rotates) can't be translated yet
;fixme sort by frequency or use property lists?
(defconst *bv-and-array-fns*
  (append *bv-and-array-fns-we-can-translate*
          '(leftrotate bvshl bvshr)))

;fixme try to get rid of anything here that's too special purpose?
;should this include everything in the axe-evaluator?
;may not need non-rec fns in this now?
;todo: ensure that these are all functions?
(defconst *other-built-in-fns*
  '(map-reverse-list
    reverse-list
    prefixp ;new!
    if      ;new!
    add-to-end ;Mon Apr  5 18:38:26 2010
    mod        ;Thu Mar  4 21:09:31 2010
    consp      ;new Wed Feb  3 07:49:51 2010
    update-subrange2 ;Sat Jul  3 22:21:29 2010
    cons car cdr nth update-nth len binary-append binary-* repeat < binary-+
    finalcdr
    unary--
    bytes-to-bits
    ;bitlist-to-bv2                   ;fixme?
    true-list-fix boolif ceiling floor group group2 ungroup
    nthcdr take firstn subrange
    myif                 ;newer
    unsigned-byte-p      ;newer
    all-unsigned-byte-p ;new
    all-all-unsigned-byte-p      ;new
    true-listp                     ;new
    all-true-listp                ;new
    items-have-len                 ;new
    map-packword ;ffixme we need a better way to tell prove-with-axe not to generate lemmas for this..
    map-byte-to-bit-list    ;ffixme
    bvchop-list            ;new
;    map-ungroup
    logext
    packbv
    unpackbv
    map-packbv
    map-unpackbv ;ffixme would like this to include all map-xxx functions?
;    map-map-unpackbv
    bv-array-clear-range ;new what else is missing?
    bv-array-clear))

(defconst *built-in-fns*
  (append *other-built-in-fns* *bv-and-array-fns*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;hope this is okay
;todo: something like this exists elsewhere
(defund recursive-functionp (name state)
  (declare (xargs :stobjs state
                  :guard (symbolp name)))
  (let* ((props (getprops name 'current-acl2-world (w state))))
    (if (not (alistp props))
        (hard-error 'recursive-functionp "props must be an alist" nil)
      (bool-fix (lookup-eq 'induction-machine props)))))

(defun list-onto-all (item lst)
  (if (endp lst)
      nil
    (cons (list item (car lst))
          (list-onto-all item (cdr lst)))))

(defun keep-entries (keys alist)
  (if (endp alist)
      nil
    (let* ((entry (car alist))
           (key (car entry)))
      (if (member-equal key keys)
          (cons entry (keep-entries keys (cdr alist)))
        (keep-entries keys (cdr alist))))))

(defund enquote-cdrs (alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      nil
    (acons-fast (car (car alist))
                (kwote (cdr (car alist)))
                (enquote-cdrs (cdr alist)))))

(defthm symbol-alistp-of-enquote-cdrs
  (implies (symbol-alistp alist)
           (symbol-alistp (enquote-cdrs alist)))
  :hints (("Goal" :in-theory (enable symbol-alistp enquote-cdrs))))

(defthm strip-cdrs-of-enquote-cdrs
  (equal (strip-cdrs (enquote-cdrs alist))
         (enquote-list (strip-cdrs alist)))
  :hints (("Goal" :in-theory (enable enquote-cdrs))))

(defthm darg-listp-of-enquote-list
  (darg-listp (enquote-list x))
  :hints (("Goal" :in-theory (enable enquote-list))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;ffixme - this can make the body much bigger - use a dag or lets or something...
;;consider just calling mysublisvarandeval on the body?

(defun remove-vars-not-passed-through (args body-dag formal-slot-alist)
  (if (endp formal-slot-alist)
      nil
    (let* ((entry (car formal-slot-alist))
           (var-name (car entry))
           (formal-slot (cdr entry))
           (actual-arg (nth formal-slot args)))
      (if (and (integerp actual-arg)
               (eq var-name (lookup actual-arg body-dag)))
          (cons entry (remove-vars-not-passed-through args body-dag (cdr formal-slot-alist)))
        (remove-vars-not-passed-through args body-dag (cdr formal-slot-alist))))))

;each recursive call may cause the removal of entries in
;formal-slot-alist (for those vars that are not passed through
;unchanged on the call)
(defun find-vars-passed-through (fn body-dag formal-slot-alist)
  (if (endp body-dag)
      formal-slot-alist
    (let* ((entry (car body-dag))
           (expr (cdr entry))
           )
      (if (or (atom expr)
              (not (eq fn (ffn-symb expr))))
          (find-vars-passed-through fn (cdr body-dag) formal-slot-alist)
        ;;it's a recursive call:
        (find-vars-passed-through fn (cdr body-dag)
                                  (remove-vars-not-passed-through (fargs expr)
                                                                  body-dag
                                                                  formal-slot-alist))))))

;the values of var-constant-alist are already quoted
(defun make-var-replacement-assumptions (vars var-constant-alist)
  (if (endp vars)
      nil
    (let* ((var (car vars))
           (match (lookup-eq-safe (car vars) var-constant-alist)))
      (cons `(equal ,var ,match)
            (make-var-replacement-assumptions (cdr vars) var-constant-alist)))))

(defun remove-list (items lst)
  (if (endp items)
      lst
    (remove-list (cdr items) (remove (car items) lst))))

(defun drop-nths (items numbers-to-drop current)
  (if (endp items)
      nil
    (if (member current numbers-to-drop)
        (drop-nths (cdr items) numbers-to-drop (+ 1 current))
      (cons (car items)
            (drop-nths (cdr items) numbers-to-drop (+ 1 current))))))

;changes the function-name and drops the indicated params from the calls
(defun fixup-recursive-calls (dag function-name new-function-name slots-to-drop)
  (if (endp dag)
      nil
    (let* ((entry (car dag))
           (nodenum (car entry))
           (expr (cdr entry)))
      (if (and (consp expr)
               (eq function-name (ffn-symb expr)))
          ;recursive call:
          (cons `(,nodenum ,new-function-name ,@(drop-nths (fargs expr) slots-to-drop 0))
                (fixup-recursive-calls (cdr dag) function-name new-function-name slots-to-drop))
        (cons entry (fixup-recursive-calls (cdr dag) function-name new-function-name slots-to-drop))))))

;what is the non-2 version?
(defun make-formal-constant-alist2 (formals args)
  (if (endp formals)
      nil
    (let* ((arg (first args)))
      (if (quotep arg)
          (acons (first formals) arg (make-formal-constant-alist2 (cdr formals) (cdr args)))
        (make-formal-constant-alist2 (cdr formals) (cdr args))))))

;; (defun fixup-vars-in-expr-aux (expr)
;;   (if (endp expr)
;;       nil
;;     (cons (if (integerp (car expr))
;;               (pack$ 'fake-var (car expr))
;;             (car expr))
;;           (fixup-vars-in-expr-aux (cdr expr)))))

;; (defun fixup-vars-in-expr (expr)
;;   (if (and (consp expr)
;;            (not (eq 'quote (ffn-symb expr))))
;;       (cons (ffn-symb expr) (fixup-vars-in-expr-aux (fargs expr)))
;;     expr))

;;(mypackn (list (nat-to-string nodenum)))

;; ;use defmap
;; (defun NAT-TO-STRING-LIST (ints)
;;   (if (endp ints)
;;       nil
;;     (cons (nat-to-string (car ints))
;;           (NAT-TO-STRING-LIST (cdr ints)))))

;; (defun dag-to-term-with-lambdas-aux (rev-dag-lst)
;;   (if (endp rev-dag-lst)
;;       'error-in-dag-to-term-with-lambdas-aux
;;     (if (endp (cdr rev-dag-lst))
;;         (let* ((entry (car rev-dag-lst))
;;                (expr (cdr entry)))
;;           (fixup-vars-in-expr expr))
;;       (let* ((entry (car rev-dag-lst))
;;              (nodenum (car entry))
;;              (expr (cdr entry))
;;              (varnames (mypackn-list (cons-onto-all 'fake-var (enlist-all (nat-to-string-list (reverse (ints-in-range 0 nodenum)))))))
;;              )
;;         `((lambda (,@varnames)
;;             ,(dag-to-term-with-lambdas-aux (cdr rev-dag-lst)))
;;            ,(fixup-vars-in-expr expr)
;;            ,@(cdr varnames))))))

;; ;; ;maybe not as good, but it makes a lambda, not a let
;; ;; ;what if the dag is a quotep?
;; ;; ;i guess this binds every subterm in a lambda, even if it is used only once?
;; (defun dag-to-term-with-lambdas (dag-lst)
;;   (dag-to-term-with-lets-aux (reverse dag-lst)))

(defconst *axe-evaluator-executable-counterparts*
  (list-onto-all ':executable-counterpart *axe-evaluator-functions*))

;;function-name must be the name of a defined function
;;returns (mv erp new-function-names new-theorem-names state), perhaps with a new theorem proved in it
;new-function-names and new-theorem-names are each singleton lists or nil
;the cdrs of param-constant-alist are not quoted
;ffixme what measure to use?  the old measure with any constants put in for unchanged formals?
;ffixm handle defuns whose bodies have embedded dags!
(defun specialize-fn (function-name args state)
  (declare (xargs :mode :program :stobjs state))
  (prog2$
   (cw "(Trying to specialize ~x0.~%" (cons function-name args))
   (let ((props (getprops function-name 'current-acl2-world (w state))))
     (if (not props)
         (mv (erp-t)
             (hard-error 'specialize-fn "Can't find a function named ~x0.)" (list (cons #\0 function-name)))
             nil state)
       (b* ((body (lookup-eq 'unnormalized-body props))
            (formals (lookup-eq 'formals props))
            (arity (len formals))
;             (function-call (cons function-name formals))
            ((mv erp body-dag) (dagify-term body)) ;ffixme use a better dagify?
            ((when erp) (mv erp nil nil state))

            (formal-slot-alist (pairlis$ formals (ints-in-range 0 (+ -1 arity))))
            (unchanged-formal-slot-alist (find-vars-passed-through function-name body-dag formal-slot-alist))

            (unchanged-formals (strip-cars unchanged-formal-slot-alist))
            (formal-constant-alist (make-formal-constant-alist2 formals args))
            (constant-formals (strip-cars formal-constant-alist))
            (unchanged-and-constant-formals (intersection-eq unchanged-formals constant-formals))
            (slots-to-drop (lookup-eq-lst unchanged-and-constant-formals unchanged-formal-slot-alist))
            ;;(slots-to-drop (strip-cdrs unchanged-formal-slot-alist))
            (formal-constant-alist (keep-entries unchanged-and-constant-formals formal-constant-alist))
            )
         (if (not unchanged-and-constant-formals)
             (prog2$ (cw "Unable to specialize.)~%")
                     (mv (erp-nil)
                         nil
                         nil
                         state))
           (let ((var-replacement-assumptions (make-var-replacement-assumptions unchanged-and-constant-formals formal-constant-alist)))
;ffixme should we use any rules here?   i guess this resolves ifs when possible at least:
             (mv-let (erp new-body-dag state)
               (quick-simp-dag body-dag
                               :rules nil ;rules!
                               ;;fixme pass in interpreted functions?
                               :assumptions var-replacement-assumptions)
               (if erp
                   (mv erp nil nil state)
                 (let* (
;ffixme what if we specialize the same function in several different ways?
                        (new-function-name (pack$ function-name '-specialized))
                        (new-body-dag (fixup-recursive-calls new-body-dag function-name new-function-name slots-to-drop))

                        (new-body-term (dag-to-term new-body-dag))
;do we need to lift ifs over the lambdas?
;(new-body-term (dag-to-term-with-lambdas new-body-dag)) ;fixme can this blow up?
;(new-body `(dag-val-with-axe-evaluator ',new-body-dag .. ..))                                                          ..

                        (new-formals (remove-list unchanged-and-constant-formals formals))
                        (measure (fn-measure function-name state)) ;slow to redo the getprop..
                        (formal-constant-alist-with-quoted-constants (enquote-cdrs formal-constant-alist))
                        (new-measure (sublis-var-simple-lst formal-constant-alist measure))
                        (defun-event `(skip-proofs
                                       (defun ,new-function-name ,new-formals
                                         (declare (xargs :measure ,new-measure
                                                         ;;we use the same theory as was used to admit the original function
                                                         ;;ffixme what if the original function's termination proof was skipped?
                                                         ;;ffixme using current-theory didn't really work, because it gets the theory when the event was included (which depends on the order of the include-books), not the theory when the event was proved/defined during certify-book
                                                         :normalize nil
                                                         :hints (("Goal" :in-theory (current-theory ',function-name)))))
                                         ,new-body-term)))
                        (defthm-name (pack$ function-name '-becomes- new-function-name))

                        (formals-with-constants (sublis-var-simple-lst formal-constant-alist-with-quoted-constants formals))
                        (defthm `(defthm ,defthm-name
                                   (implies ,(make-conjunction-from-list var-replacement-assumptions)
                                            (equal (,function-name ,@formals)
                                                   (,new-function-name ,@new-formals)))
                                   ;; if we used any rules above, we need to use them in this proof too
                                   :hints (("Goal" :induct (,function-name ,@formals)
                                            :do-not '(generalize eliminate-destructors)
                                            :expand ((,function-name ,@formals-with-constants)
                                                     (,new-function-name ,@new-formals)
                                                     )
                                            :in-theory (union-theories (theory 'minimal-theory)
                                                                       (union-theories
;without this, we had (not (natp 4)) in a proof
                                                                        *axe-evaluator-executable-counterparts*
                                                                        '(,function-name ,new-function-name))))))))
                   (prog2$ (cw "Specializing.  New defun: ~x0~%. Rule: ~x1.~%" defun-event defthm) ;move printing down?
                           (let ((state (submit-events-brief (list defun-event defthm) state)))
                             (prog2$ (cw "Specialzed ~x0.)~%" (cons function-name args))
                                     (mv (erp-nil)
                                         (list new-function-name)
                                         (list `,defthm-name)
                                         state))))))))))))))


;;(specialize-fn 'binary-append '(x '(foo bar)) state)

;;(specialize-fn 'comb2 (acons 'size '8 nil) state)
;;specialize all fns in DAG
;; Returns (mv erp new-function-names new-rule-names state).
;;caller should use the rules to simplify the dag
(defun specialize-fns (dag state)
  (declare (xargs :mode :program :stobjs state))
  (if (endp dag)
      (mv (erp-nil) nil nil state)
    (let* ((entry (car dag))
;           (nodenum (car entry))
           (expr (cdr entry)))
      (if (not (consp expr)) ;it's a variable, so can't specialize
          (specialize-fns (cdr dag) state)
        (let ((fn (ffn-symb expr)))
          (if (and (not (consp (ffn-symb expr))) ;not a lambda
                   (recursive-functionp (ffn-symb expr) state)
                   (not (member-eq (ffn-symb expr) *built-in-fns*)) ;new!
                   )
              ;specialize fn:
              (let* ((args (fargs expr)))
                (mv-let (erp new-function-names new-theorem-names state)
                  (specialize-fn fn args state)
                  (if erp
                      (mv erp nil nil state)
                    (mv-let (erp new-function-names2 new-theorem-names2 state)
                      (specialize-fns (cdr dag) state)
                      (if erp
                          (mv erp nil nil state)
                        (mv (erp-nil)
                            (append new-function-names new-function-names2)
                            (append new-theorem-names new-theorem-names2)
                            state))))))
            ;can't specialize:
            (specialize-fns (cdr dag) state)))))))
