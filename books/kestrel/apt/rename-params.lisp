; Transformation to rename parameters of a function
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Authors: Limei Gilham
;          Eric Smith (eric.smith@kestrel.edu)
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; See tests in rename-params-tests.lisp

(include-book "kestrel/terms-light/rename-vars-in-term" :dir :system)
(include-book "utilities/deftransformation")
(include-book "utilities/function-renamingp")
(include-book "utilities/maybe-verify-guards2")
(include-book "kestrel/std/system/guard-verified-p" :dir :system)
(include-book "utilities/names") ; for INCREMENT-NAME-SUFFIX-SAFE
(include-book "utilities/make-becomes-theorem")
(include-book "utilities/option-parsing")
(include-book "utilities/transformation-prologue")
(include-book "kestrel/utilities/defun-forms" :dir :system)
(include-book "kestrel/utilities/my-get-event" :dir :system)
(include-book "kestrel/utilities/doublets2" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)
(include-book "kestrel/utilities/defining-forms" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "kestrel/utilities/declares1" :dir :system) ; for substitute-measure-in-declares
(include-book "kestrel/utilities/declares" :dir :system) ; for substitute-guard-in-declares
(include-book "kestrel/utilities/directed-untranslate-dollar" :dir :system)
(include-book "kestrel/utilities/verify-guards-dollar" :dir :system)
(include-book "kestrel/terms-light/restore-mv-in-branches" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)
(include-book "misc/install-not-normalized" :dir :system)
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(local (in-theory (disable len)))

;; Union together the formals of all the FNS
(defun formals-of-fns (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (if (endp fns)
      nil
    (union-eq (fn-formals (first fns) wrld)
              (formals-of-fns (rest fns) wrld))))



;; drop these?:

(defthm symbolp-of-cdr-assoc-equal-symbol-symbol-alist
  (implies (and (symbolp x)
                (symbol-symbol-alistp alist)
                (assoc-equal (car l) alist))
           (symbolp (cdr (assoc-equal x alist)))))

(defthm symbol-listp-of-sublis-var-simple-lst
  (implies (and (symbol-listp l)
                (symbol-symbol-alistp alist))
           (symbol-listp (sublis-var-simple-lst alist l)))
  :hints (("Goal" :in-theory (enable sublis-var-simple
                                     sublis-var-simple-lst))))

(defthm pseudo-termp-of-lookup-equal
  (implies (and (symbolp x)
                (symbol-symbol-alistp alist))
           (pseudo-termp (lookup-equal x alist)))
  :hints (("Goal" :in-theory (enable symbol-symbol-alistp))))

;returns a new defun
(defun rename-params-in-defun (fn
                               renaming
                               new-fn fn-event function-renaming rec untranslate state)
  (declare (xargs :stobjs state
                  :mode :program ;because we call untranslate
                  :guard (and (symbolp fn)
                              (fn-definedp fn (w state))
                              (var-renamingp renaming)
                              (function-renamingp function-renaming)
                              (member-eq untranslate '(t nil :nice)))))
  (let* ((wrld (w state))
         (body (fn-body fn t wrld))
         (ubody (get-body-from-event fn fn-event))
         (formals (sublis-var-simple-lst renaming (fn-formals fn wrld)))
         (declares (get-declares-from-event fn fn-event)) ;TODO: Think about all the kinds of declares that get passed through.
         (declares (substitute-measure-in-declares declares renaming state))
         (declares (substitute-guard-in-declares declares renaming))
         (declares (add-verify-guards-nil declares)) ;we will later verify the guards if needed
         (declares (if rec
                       (replace-xarg-in-declares
                        :hints
                        `(("Goal" :in-theory '()
                           :use (:instance (:termination-theorem ,fn) :extra-bindings-ok ,@(alist-to-doublets renaming))))
                        declares)
                     declares))
         (declares ; cheap way to deal with previous ignorable decls
          (cons `(declare (ignorable ,@formals))
                (remove-declares 'ignorable declares)))
         (new-body (rename-vars-in-term renaming body renaming))
         (new-body (rename-fns new-body function-renaming))
         (num-values (num-return-values-of-fn fn wrld))
         (new-body (if (<= 2 num-values)
                       (restore-mv-in-branches new-body num-values (strip-cdrs function-renaming) wrld)
                     new-body))
         (new-body (if (eq nil untranslate)
                       new-body ;TODO clean up macros at least?  clean up mvs too?
                     (if (eq t untranslate)
                         (untranslate new-body nil wrld)
                       (directed-untranslate$ new-body ubody wrld)))))
    `(defun ,new-fn (,@formals)
       ,@declares
       ,new-body)))

;returns the new defuns
(defun rename-params-in-defuns (fns
                                renaming
                                fn-event function-renaming untranslate state)
  (declare (xargs :stobjs state
                  :mode :program ;because we call untranslate
                  :guard (and (symbol-listp fns)
                              (all-fn-definedp fns (w state))
                              (var-renamingp renaming)
                              (function-renamingp function-renaming)
                              (member-eq untranslate '(t nil :nice)))))
  (if (endp fns)
      nil
    (cons (rename-params-in-defun (first fns)
                                  renaming
                                  (lookup-eq-safe (first fns) function-renaming) ;new name for this fn
                                  fn-event
                                  function-renaming :mutual untranslate state)
          (rename-params-in-defuns (rest fns)
                                   renaming
                                   fn-event function-renaming untranslate state))))

  ;; (maybe-verify-guards2 verify-guards ;todo: deprecate maybe-verify-guards2?
  ;;                      new-fn
  ;;                      `(("Goal" :use ( ;; We instantiate the guard theorem according to
  ;;                                      ;; the param renaming:
  ;;                                      (:instance (:guard-theorem ,old-fn nil)
  ;;                                                 :extra-bindings-ok
  ;;                                                 ,@(alist-to-doublets param-renaming))))))

;; Returns an event.
;; Similar to verify-guards-for-defun, but this one takes a param-renaming.
;; This requires the 'becomes theorems' to already exist.
(defun verify-guards-for-rename-params (old-fn new-fn param-renaming function-renaming)
  (declare (xargs :guard (and (symbolp old-fn)
                              (symbolp new-fn)
                              (symbol-alistp param-renaming)
                              (function-renamingp function-renaming))))
  (let ((guard-hints ;;(if (eq :auto guard-hints)
         `(("Goal" :use (:instance (:guard-theorem ,old-fn
                                                   t ; confusingly, this matches the behavior of :guard-simplify nil below
                                                   )
                                   :extra-bindings-ok
                                   ;; account for the renaming:
                                   ,@(alist-to-doublets param-renaming))
            :do-not '(generalize eliminate-destructors) ;;TODO; Turn off more stuff:
            ;; we use the becomes lemma(s):
            :in-theory '(,@(becomes-theorem-names function-renaming)
                         ;; because untranslate can
                         ;; introduce CASE, which will have
                         ;; EQLABLEP guard obligations that
                         ;; may not be in the original
                         ;; function:
                         (:e eqlablep)
                         (:e eqlable-listp) ; not sure whether this is needed, depends on what kinds of CASE untranslate can put in
                         )))
         ;;guard-hints)
         ))
    `(verify-guards$ ,new-fn
                     :hints ,guard-hints
                     :guard-simplify nil ;; avoid simplification based on the current theory
                     )))

;todo: combine with rename-params-event?
(defun rename-params-fn-core (fn new-name
                                 param-renaming-alist
                                 fn-event verify-guards
                                 untranslate
                                 state)
  (declare (xargs :stobjs state
                  :mode :program ;because we call untranslate
                  :guard (and (symbolp fn)
                              ;; (symbolp new-name)
                              (var-renamingp param-renaming-alist)
                              (member-eq verify-guards '(t nil :auto))
                              (fn-definedp fn (w state))
                              (member-eq untranslate '(t nil :nice)))))
  (let ((verify-guards (if (eq :auto verify-guards)
                           (guard-verified-p fn (w state))
                         verify-guards))
        (prologue (transformation-prologue fn (w state))) ;puts in install-not-normalized for fn (and its mutually-recursive partners)
        )
    (if (not (fn-recursivep fn state))
        ;; we are operating on a single, non-recursive function:
        (b* ((new-fn (if (eq :auto new-name) (increment-name-suffix-safe fn state) new-name))
             (function-renaming (acons fn new-fn nil))
             (new-defun (rename-params-in-defun fn param-renaming-alist new-fn fn-event nil nil untranslate state))
             ;; TODO: Can we often avoid adding the :verify-guards t?
             (new-defun-to-export (if verify-guards (add-verify-guards-t-to-defun new-defun) new-defun)) ; no hints to clean up since non-recursive
             (becomes-theorem (make-becomes-theorem fn new-fn nil t nil '(theory 'minimal-theory) state))
             ;; Remove :hints from the theorem before exporting it:
             (becomes-theorem-to-export (clean-up-defthm becomes-theorem))
             )
          `(encapsulate ()
             ,@prologue
             (local ,new-defun) ; has :verify-guards nil
             (local (install-not-normalized ,new-fn))
             (local ,becomes-theorem)
             ,@(and verify-guards `((local ,(verify-guards-for-rename-params fn new-fn param-renaming-alist function-renaming))))
             ,new-defun-to-export
             ,becomes-theorem-to-export))
      (if (fn-singly-recursivep fn state)
          ;;we are operating on a single, recursive function:
          (b* ((new-fn (if (eq :auto new-name) (increment-name-suffix-safe fn state) new-name))
               (function-renaming (acons fn new-fn nil))
               (new-defun (rename-params-in-defun fn
                                                  param-renaming-alist
                                                  new-fn fn-event (acons fn new-fn nil) :single untranslate state)) ;;TODO: restrict the hints in this case..
               (new-defun-to-export (if verify-guards (add-verify-guards-t-to-defun new-defun) new-defun))
               (new-defun-to-export (remove-hints-from-defun new-defun-to-export))
               (becomes-theorem (make-becomes-theorem fn new-fn :single t nil '(theory 'minimal-theory) state))
               ;; Remove :hints from the theorem before exporting it:
               (becomes-theorem-to-export (clean-up-defthm becomes-theorem)))
            `(encapsulate ()
               ,@prologue
               (local ,new-defun)
               (local (install-not-normalized ,new-fn))
               (local ,becomes-theorem)
               ,@(and verify-guards `((local ,(verify-guards-for-rename-params fn new-fn param-renaming-alist function-renaming))))
               ,new-defun-to-export
               ,becomes-theorem-to-export))
        ;; we are operating on a mutually recursive nest of functions:
        (b* ((ctx `(rename-params ,fn))
             (fns (fn-recursive-partners fn state))
             ;; Handle the :new-name arg:
             (new-name-alist ;this is an alist, but some values may be :auto
              (elaborate-mut-rec-option2 new-name :new-name fns ctx))
             (function-renaming (pick-new-names new-name-alist state))
             (new-fn (lookup-eq-safe fn function-renaming))
             (new-defuns (rename-params-in-defuns fns
                                                  param-renaming-alist
                                                  fn-event function-renaming untranslate state))
             (mut-rec `(mutual-recursion ,@new-defuns))
             (flag-function-name (pack$ 'flag- fn))
             (make-flag-form `(make-flag ,flag-function-name ,fn))
             (becomes-theorems
              (make-becomes-theorems fns
                                     function-renaming
                                     t ;todo: thread through a thm-enable argument!
                                     state))
             (becomes-defthm-flag (make-becomes-defthm-flag flag-function-name
                                                            becomes-theorems
                                                            fns
                                                            function-renaming
                                                            nil
                                                            '(theory 'minimal-theory)
                                                            (w state))))
          `(encapsulate ()
             ,@prologue
             ,mut-rec
             (local ,make-flag-form)
             (local ,becomes-defthm-flag)
             ,@(clean-up-defthms becomes-theorems)
             ,@(and verify-guards (list (verify-guards-for-rename-params fn new-fn param-renaming-alist function-renaming)))))))))

;; Returns (mv erp event state).
;; todo: allow different renamings for mutual recursion
(defun rename-params-event (fn param-renaming new-name verify-guards untranslate state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp fn)
                              (member-eq verify-guards '(t nil :auto))
                              (member-eq untranslate '(t nil :nice)))
                  :mode :program)) ;because of the call to my-get-event
  (b* (((when (and (not (symbol-symbol-doubletp param-renaming))
                   (not (symbol-symbol-doubletsp param-renaming))))
        (er hard? 'rename-params-event "The parameter renaming must be either a doublet (list of length 2) of names, or a list of such doublets, but it is ~x0." param-renaming)
        (mv :bad-input nil state))
       ;; Desugar the param-renaming;
       (param-renaming-doublets (if (null param-renaming)
                                    nil
                                  (if (consp (first param-renaming)) ; it's already a list of doublets
                                      param-renaming
                                    ;; Make a single doublet into a singleton list of doublets:
                                    (list param-renaming))))
       (param-renaming-alist (doublets-to-alist param-renaming-doublets))
       (fns (if (fn-mutually-recursivep fn state)
                (fn-recursive-partners fn state) ;includes fn
              (list fn)))
       (existing-formals (formals-of-fns fns (w state)))
       ((when (not (subsetp-eq (strip-cars param-renaming-alist)
                               existing-formals)))
        (er hard? 'rename-params "The renaming, ~x0, includes params that are not among the formals, ~x1, of the function(s)."
            param-renaming-doublets existing-formals)
        (mv t nil state))
       (fn-event (my-get-event fn (w state)))
       (event (rename-params-fn-core fn new-name
                                     param-renaming-alist
                                     fn-event
                                     verify-guards untranslate state)))
    (mv nil event state)))

(deftransformation rename-params
  (fn ;the name of a defined function
   param-renaming ; a doublet or list of doublets
   )
  ((new-name ':auto)
   (verify-guards ':auto)
   (untranslate 't) ;todo: make :nice the default?
   )
  :short "Rename one or more parameters in a function."
  :arg-descriptions
  ((fn "Function to transform")
   (param-renaming "A doublet or list of doublets")
   (new-name "New name to use for the function (if :auto, the transformation generates a name")
   (verify-guards "Whether to verify guards of the new function(s).")
   (untranslate "How to untranslate the function body after changing it.")))
