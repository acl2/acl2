; A drop irrelevant parameters from a function
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; See tests in drop-irrelevant-params-tests.lisp

(include-book "utilities/deftransformation")
(include-book "utilities/make-becomes-theorem")
(include-book "utilities/drop-corresponding-items")
(include-book "utilities/transformation-prologue")
(include-book "utilities/verify-guards-for-defun")
(include-book "utilities/names")
(include-book "utilities/option-parsing")
(include-book "kestrel/utilities/declares" :dir :system)
(include-book "kestrel/utilities/directed-untranslate-dollar" :dir :system)
(include-book "kestrel/utilities/defining-forms" :dir :system)
(include-book "kestrel/utilities/declares1" :dir :system)
(include-book "kestrel/utilities/my-get-event" :dir :system)
(include-book "kestrel/utilities/reconstruct-macros" :dir :system)
(include-book "utilities/defun-variant")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;; TODO: Make the proofs more robust.

;make an alist pairing the fns with their formals
(defun make-fn-formals-alist (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (if (endp fns)
      nil
    (let ((fn (first fns)))
      (acons fn (fn-formals fn wrld) (make-fn-formals-alist (rest fns) wrld)))))

(defun fn-formals-alistp (alist)
  (declare (xargs :guard t))
  (and (symbol-alistp alist)
       (symbol-list-listp (strip-cdrs alist))))

(defthm fn-formals-alistp-of-make-fn-formals-alist
  (implies (symbol-listp fns)
           (fn-formals-alistp (make-fn-formals-alist fns wrld)))
  :hints (("Goal" :in-theory (enable fn-formals-alistp make-fn-formals-alist))))

(defthm pseudo-term-listp-of-drop-corresponding-items
  (implies (pseudo-term-listp items)
           (pseudo-term-listp (drop-corresponding-items items keys keys-to-drop))))

;;TODO: Allow the user to specify which params of *each function* in a mutual
;;recursion are irrelevant (currently the param given is assumed to refer to
;;any param of that name for any function in the nest).


(local (in-theory (disable len)))

;; ;drop?
;; (defthm pseudo-termp-of-nth
;;   (implies (pseudo-term-listp items)
;;            (pseudo-termp (nth n items)))
;;   :hints (("Goal" :in-theory (e/d (nth) (;nth-of-cdr
;;                                          )))))

;commented out due to name clash
;; (defun add-suffix (sym suff)
;;   (pack$ sym suff))

(defun add-suffix-all (syms suff)
  (if (endp syms)
      nil
    (cons (pack$ (first syms) suff)
          (add-suffix-all (rest syms) suff))))

(defun pair-all-keys (keys val)
  (if (endp keys)
      nil
    (acons (first keys) val (pair-all-keys (rest keys) val))))

;; Maps a function name to a list of the formals to drop
(defun params-to-drop-alistp (params-to-drop-alist)
  (declare (xargs :guard t))
  (if (atom params-to-drop-alist)
      (null params-to-drop-alist)
    (let ((entry (first params-to-drop-alist)))
      (and (consp entry)
           (symbolp (car entry))
           (symbol-listp (cdr entry))
           (params-to-drop-alistp (rest params-to-drop-alist))))))

;returns (mv new-formals new-args)
(defun drop-formals-and-args-that-mention-any-var (formals args vars)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp args)
                              (symbol-listp vars))))
  (if (endp formals)
      (mv nil nil)
    (mv-let (rest-formals rest-args)
            (drop-formals-and-args-that-mention-any-var (rest formals) (rest args) vars)
            (if (intersection-eq vars (free-vars-in-term (first args))) ;; if this arg mentions any of the VARS
                ;; drop this formal and arg
                (mv rest-formals rest-args)
              (mv (cons (first formals) rest-formals)
                  (cons (first args) rest-args))))))

(defthm symbol-listp-of-mv-nth-0-of-drop-formals-and-args-that-mention-any-var
  (implies (symbol-listp formals)
           (symbol-listp (mv-nth 0 (drop-formals-and-args-that-mention-any-var formals args vars)))))

(defthm pseudo-term-listp-of-mv-nth-1-of-drop-formals-and-args-that-mention-any-var
  (implies (pseudo-term-listp args)
           (pseudo-term-listp (mv-nth 1 (drop-formals-and-args-that-mention-any-var formals args vars)))))

(defthm true-listp-of-mv-nth-0-of-drop-formals-and-args-that-mention-any-var
  (implies (true-listp formals)
           (true-listp (mv-nth 0 (drop-formals-and-args-that-mention-any-var formals args vars))))
  :rule-classes (:rewrite :type-prescription))

(defthm true-listp-of-mv-nth-1-of-drop-formals-and-args-that-mention-any-var
  (implies (true-listp args)
           (true-listp (mv-nth 1 (drop-formals-and-args-that-mention-any-var formals args vars))))
  :rule-classes (:rewrite :type-prescription))

(defthm len-of-mvnth-1-of-drop-formals-and-args-that-mention-any-var
  (equal (len (mv-nth 1 (drop-formals-and-args-that-mention-any-var formals args vars)))
         (len (mv-nth 0 (drop-formals-and-args-that-mention-any-var formals args vars)))))

(mutual-recursion
 (defun drop-irrelevant-params-in-term (term
                                        params-to-drop-alist ;an alist from function names to lists of params to drop
                                        params-to-drop ;the params to drop for TERM (if a lambda arg is bound to a term containing one of these, we drop the lambda arg)
                                        fn-formals-alist ;an alist from function names to their lists of formals
                                        )
   (declare (xargs :measure (acl2-count term)
                   :guard (and (pseudo-termp term)
                               (fn-formals-alistp fn-formals-alist)
                               (symbol-listp params-to-drop)
                               (params-to-drop-alistp params-to-drop-alist))
                   :verify-guards nil ;; done below
                   ))
   (if (variablep term)
       term
     (if (quotep term)
         term
       ;;it's a function call (maybe a lambda application):
       (let* ((args (drop-irrelevant-params-in-terms (fargs term) params-to-drop-alist params-to-drop fn-formals-alist)) ;process the args first (may waste some time for args that are dropped below)
              (fn (ffn-symb term)))
         (if (consp fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
             (let* ((lambda-formals (second fn))
                    (lambda-body (third fn)))
               (mv-let (new-lambda-formals args)
                 ;; If the params-to-drop are truly irrelevant, than any
                 ;; lambda formal bound to an argument that mentions a
                 ;; param to be dropped must also be irrelevant in the
                 ;; lambda body.  So drop such formals and their
                 ;; corresponding args:
                 (drop-formals-and-args-that-mention-any-var lambda-formals args params-to-drop)
                 (let* ((params-to-drop (set-difference-eq lambda-formals new-lambda-formals)) ;any formals not in the new-lambda-formals got dropped
                        (lambda-body (drop-irrelevant-params-in-term lambda-body params-to-drop-alist params-to-drop fn-formals-alist))) ;;apply recursively to the lambda body
                   `((lambda (,@new-lambda-formals) ,lambda-body) ,@args))))
           ;; regular function call
           (if (assoc-eq fn params-to-drop-alist)
               ;; it's a call of a function whose params are being dropped:
               `(,fn ,@(drop-corresponding-items args (lookup-eq fn fn-formals-alist) (lookup-eq fn params-to-drop-alist)))
             ;;not a lambda application and not a function for which we should drop params, so just rebuild the function call:
             `(,fn ,@args)))))))

 (defun drop-irrelevant-params-in-terms (terms params-to-drop-alist params-to-drop fn-formals-alist)
   (declare (xargs :measure (acl2-count terms)
                   :guard (and (pseudo-term-listp terms)
                               (symbol-listp params-to-drop)
                               (fn-formals-alistp fn-formals-alist)
                               (PARAMS-TO-DROP-ALISTp PARAMS-TO-DROP-ALIST))))
   (if (endp terms)
       nil
     (cons (drop-irrelevant-params-in-term (first terms) params-to-drop-alist params-to-drop fn-formals-alist)
           (drop-irrelevant-params-in-terms (rest terms) params-to-drop-alist params-to-drop fn-formals-alist)))))

(make-flag flag-drop-irrelevant-params-in-term drop-irrelevant-params-in-term)

(defthm len-of-drop-irrelevant-params-in-terms
  (equal (len (drop-irrelevant-params-in-terms terms params-to-drop-alist params-to-drop fn-formals-alist))
         (len terms))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable (:i len) drop-irrelevant-params-in-terms))))

;; (defthm consp-of-drop-irrelevant-params-in-terms
;;   (equal (consp (drop-irrelevant-params-in-terms terms))
;;          (consp terms))
;;   :hints (("Goal" :induct (len terms)
;;            :in-theory (enable len drop-irrelevant-params-in-terms))))

(defthm-flag-drop-irrelevant-params-in-term
  (defthm pseudo-termp-of-drop-irrelevant-params-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (drop-irrelevant-params-in-term term params-to-drop-alist params-to-drop fn-formals-alist)))
    :flag drop-irrelevant-params-in-term)
  (defthm pseudo-term-listp-of-drop-irrelevant-params-in-terms
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (drop-irrelevant-params-in-terms terms params-to-drop-alist params-to-drop fn-formals-alist)))
    :flag drop-irrelevant-params-in-terms))

(verify-guards drop-irrelevant-params-in-term)

;; Returns a new defun.
(defun drop-irrelevant-params-in-defun (fn new-fn fn-event function-renaming params-to-drop-alist fn-formals-alist rec function-disabled measure-hints untranslate state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp fn)
                              (member-eq rec '(nil :single :mutual))
                              (fn-definedp fn (w state))
                              (params-to-drop-alistp params-to-drop-alist)
                              (function-renamingp function-renaming)
                              (t/nil/auto-p function-disabled)
                              (member-eq untranslate '(t nil :macros :nice)))
                  :mode :program ; because we call untranslate
                  ))
  (b* ((wrld (w state))
       (body (fn-body fn t wrld))
       (ubody (get-body-from-event fn fn-event))
       (formals (fn-formals fn wrld))
       (new-formals (set-difference-equal formals (lookup-eq fn params-to-drop-alist)))
       (params-to-drop (assoc-eq fn params-to-drop-alist))
       (declares (get-declares-from-event fn fn-event)) ;TODO: Think about all the kinds of declares that get passed through.
       (declares (add-verify-guards-nil declares)) ;we will later verify the guards if needed
       ;; TODO: This can cause problems when we generate hints for the guard proof (need to instantiate dropped params somehow): Perhaps the user
       ;; could supply such instances (in general, in terms of the other params) with the guard hints.  Or we try to find values of the right type, at least.
       (declares (drop-guard-conjuncts-that-mention-vars-in-declares declares (assoc-eq fn params-to-drop-alist)))
;         (declares (replace-mode-with-program-in-declares declares))
       (declares (fixup-ignores declares new-formals body))
       (measure (and rec (fn-measure fn state)))
       (formals-in-measure (and rec (free-vars-in-term measure)))
       (dropped-params-in-measure (and rec (intersection-eq formals-in-measure params-to-drop))) ;these are bad!
       ((when (and rec dropped-params-in-measure))
        (er hard 'drop-irrelevant-params-in-defun "Measure (~x0) mentions params that are supposed to be irrelevant (~x1)." measure dropped-params-in-measure))
       ((mv explicit-measurep &)
        (get-xarg-from-declares :measure declares))
       (declares (if (or (not rec)
                         explicit-measurep)
                     declares
                   ;; if an explicit measure is missing because ACL2 guessed a measure:
                   (cons `(declare (xargs :measure ,measure)) declares))) ;this gets combined with other xargs below by cleanup-declares
       (declares (if (not rec)
                     declares ; no termination since not recursive
                   ;; single or mutual recursion:
                   (replace-xarg-in-declares
                    :hints
                    (if (eq :auto measure-hints)
                        `(("Goal" :in-theory '()
                           ;; ACL2 automatically replaces the old functions with the new ones in this:
                           :use (:instance (:termination-theorem ,fn))))
                      measure-hints)
                    declares)))
       ;; Fix up the declares of irrelevant formals:
       (old-irrelevant-formals (get-irrelevant-formals-from-declares declares)) ; todo: what if fn was submitted after set-irrelevant-formals-ok?
       (irrelevant-formals (set-difference-eq old-irrelevant-formals params-to-drop))
       (declares (remove-declares 'irrelevant declares))
       (declares (if (consp irrelevant-formals)
                     (add-declare-arg `(declare (irrelevant ,@irrelevant-formals)) declares)
                   declares))

       (defun-variant (defun-variant fn nil ;non-executable
                        function-disabled state))

       (declares (clean-up-declares declares))
       ;;todo: try to do this without translating:
       (new-body (drop-irrelevant-params-in-term body params-to-drop-alist params-to-drop fn-formals-alist))
       (new-body (rename-fns new-body function-renaming))
       (new-body (if (not untranslate)
                     new-body
                   (if (eq :macros untranslate)
                       (reconstruct-macros-in-term new-body)
                     (if (eq :nice untranslate)
                         (directed-untranslate$ new-body ubody wrld)
                       (untranslate new-body nil wrld))))))
    `(,defun-variant ,new-fn (,@new-formals)
       ,@declares ;TODO: What if the guard mentions the dropped param?!
       ,new-body)))

;; Returns the new defuns
(defun drop-irrelevant-params-in-defuns (fns fn-event function-renaming params-to-drop-alist fn-formals-alist rec function-disabled measure-hints untranslate state)
  (declare (xargs :stobjs state
                  :guard (and (symbol-listp fns)
                              (member-eq rec '(nil :single :mutual))
                              (all-fn-definedp fns (w state))
                              (params-to-drop-alistp params-to-drop-alist)
                              (function-renamingp function-renaming)
                              (t/nil/auto-p function-disabled)
                              (member-eq untranslate '(t nil :macros :nice)))
                  :mode :program ; because we call untranslate
                  ))
  (if (endp fns)
      nil
    (cons (drop-irrelevant-params-in-defun (first fns)
                                           (lookup-eq-safe (first fns) function-renaming) ;new name for this fn
                                           fn-event
                                           function-renaming params-to-drop-alist fn-formals-alist rec function-disabled measure-hints untranslate state)
          (drop-irrelevant-params-in-defuns (rest fns) fn-event function-renaming params-to-drop-alist fn-formals-alist rec function-disabled measure-hints untranslate state))))

(local
 (defthm true-listp-of-lookup-equal-when-symbol-list-listp-of-strip-cdrs
   (implies (symbol-list-listp (strip-cdrs params-to-drop-alist))
            (true-listp (lookup-equal fn params-to-drop-alist)))))

;; Build the wrappper function for NEW-FN.
;; The wrapper has the same params as the original function but passes a subset of them to the aux function
(defun drop-irrelevant-params-wrapper (fn new-fn aux-fn params-to-drop-alist state)
  (declare (xargs :guard (and (symbolp fn)
                              (alistp params-to-drop-alist)
                              (symbol-list-listp (strip-cdrs params-to-drop-alist)))
                  :stobjs state))
  (let* ((formals (fn-formals fn (w state)))
         (aux-fn-formals (set-difference-equal formals (lookup-eq fn params-to-drop-alist)))
         (ignored-params (set-difference-eq formals aux-fn-formals)))
    `(defun ,new-fn (,@formals)
       (declare (ignore ,@ignored-params)) ;what if there are none for this member of the nest?
       (,aux-fn ,@aux-fn-formals))))

;; Build the wrappper functions for NEW-FNS.
(defun drop-irrelevant-params-wrappers (fns new-fns aux-fns params-to-drop-alist state)
  (declare (xargs :guard (and (symbol-listp fns)
                              (symbol-listp new-fns)
                              (symbol-listp aux-fns)
                              (alistp params-to-drop-alist)
                              (symbol-list-listp (strip-cdrs params-to-drop-alist)))
                  :stobjs state))
  (if (endp fns)
      nil
    (let* ((fn (first fns))
           (new-fn (first new-fns))
           (aux-fn (first aux-fns)))
      (cons (drop-irrelevant-params-wrapper fn new-fn aux-fn params-to-drop-alist state)
            (drop-irrelevant-params-wrappers (rest fns) (rest new-fns) (rest aux-fns) params-to-drop-alist state)))))

;TTODO think about the non-mut-rec-cases
(defun drop-irrelevant-params-defthm (fn new-fn rec enables params-to-drop-alist theorem-disabled state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp fn)
                              (PARAMS-TO-DROP-ALISTp PARAMS-TO-DROP-ALIST)
                              (member-eq rec '(nil :single :mutual))
                              (true-listp enables)
                              (booleanp theorem-disabled))))
  (let ((formals (fn-formals fn (w state))))
    `(,(if theorem-disabled 'defthmd 'defthm) ,(pack$ fn '-becomes- new-fn) ;TODO: disable the theorem for now
       (equal (,fn ,@formals)
              (,new-fn ,@(set-difference-equal formals (lookup-eq fn params-to-drop-alist))))
       :hints ,(if (eq rec :mutual) ;weird format for make-flag hints:
                   `('(:in-theory (append '(,fn ,new-fn ,@enables) (theory 'minimal-theory))
                                  :do-not '(generalize eliminate-destructors)))
                 (if (eq rec :single)
                     `(("Goal" :induct (,fn ,@formals)
                        :in-theory (append '(,fn ,new-fn ,@enables) (theory 'minimal-theory))
                        :do-not '(generalize eliminate-destructors)))
                   `(("Goal" :in-theory (append '(,fn ,new-fn ,@enables) (theory 'minimal-theory))
                      :do-not '(generalize eliminate-destructors)))))
       ,@(and (eq rec :mutual) (list :flag fn)))))

(defun drop-irrelevant-params-defthms (fns enables-for-each function-renaming rec enables params-to-drop-alist theorem-disabled state)
  (declare (xargs :stobjs state :guard (and (symbol-listp fns)
                                            (params-to-drop-alistp params-to-drop-alist)
                                            (member-eq rec '(nil :single :mutual))
                                            (true-listp enables)
                                            (true-list-listp enables-for-each)
                                            (function-renamingp function-renaming)
                                            (booleanp theorem-disabled))))
  (if (endp fns)
      nil
    (let ((fn (first fns))
          (enables-for-this (first  enables-for-each)))
      (cons (drop-irrelevant-params-defthm fn (lookup-eq-safe fn function-renaming) rec (append enables enables-for-this) params-to-drop-alist theorem-disabled state)
            (drop-irrelevant-params-defthms (rest fns) (rest enables-for-each) function-renaming rec enables params-to-drop-alist theorem-disabled state)))))

;TODO think about cases other than mut-rec
;; Make a theorem equating FN with NEW-FN
;TODO: can we unify this with make-becomes-theorem?
(defun make-becomes-theorem3 (fn new-fn rec enables state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp fn)
                              (member-eq rec '(nil :single :mutual))
                              (true-listp enables))))
  (let ((formals (fn-formals fn (w state))))
    `(defthm ,(pack$ fn '-becomes- new-fn) ;TODO: disable the theorem for now
       (equal (,fn ,@formals)
              (,new-fn ,@formals))
       :hints ,(if (eq rec :mutual)
                   `(("Goal" ;:induct (,fn ,@formals)
                        :in-theory (append '(;,fn
                                             ,new-fn ,@enables) (theory 'minimal-theory))))
                 (if (eq rec :single)
                     `(("Goal" :induct (,fn ,@formals)
                        :in-theory (append '(,fn ,new-fn ,@enables) (theory 'minimal-theory))))
                   `(("Goal" :in-theory (append '(,fn ,new-fn ,@enables) (theory 'minimal-theory))))))
;       ,@(and (eq rec :mutual) (list :flag fn))
       )))

(defun make-becomes-theorem3s (fns enables-for-each function-renaming rec enables state)
  (declare (xargs :stobjs state :guard (and (symbol-listp fns)
                                            (member-eq rec '(nil :single :mutual))
                                            (true-listp enables)
                                            (true-list-listp enables-for-each)
                                            (function-renamingp function-renaming))))
  (if (endp fns)
      nil
    (let ((fn (first fns))
          (enables-for-this (first  enables-for-each))
          )
      (cons (make-becomes-theorem3 fn (lookup-eq-safe fn function-renaming) rec (append enables enables-for-this) state)
            (make-becomes-theorem3s (rest fns) (rest enables-for-each) function-renaming rec enables state)))))

(defun any-guard-mentions-anyp (fns vars wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (symbol-listp vars)
                              (plist-worldp wrld))))
  (if (endp fns)
      nil
    (or (intersection-eq (free-vars-in-term (fn-guard$ (first fns) wrld)) vars)
        (any-guard-mentions-anyp (rest fns) vars wrld))))

(defun guard-hints-for-drop-irrelevant-params (old-fns params-to-drop guard-hints wrld)
  (declare (xargs :guard (and (symbol-listp old-fns)
                              (symbol-listp params-to-drop)
                              (plist-worldp wrld))))
  (if (any-guard-mentions-anyp old-fns params-to-drop wrld)
      (prog2$ (cw "NOTE: Suppressing automatic :guard-hints because the old guard(s) mention one or more of the params to be dropped.")
              nil)
    guard-hints))

(defun drop-irrelevant-params-event (fn param-or-params-to-drop new-name build-wrapper theorem-disabled function-disabled measure-hints verify-guards guard-hints untranslate state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp fn)
                              (booleanp build-wrapper)
                              (booleanp theorem-disabled)
                              (t/nil/auto-p function-disabled)
                              (or (symbolp param-or-params-to-drop)
                                  (symbol-listp param-or-params-to-drop))
                              (fn-definedp fn (w state))
                              (member-eq untranslate '(t nil :macros :nice)))
                  :mode :program))
  (let* ((wrld (w state))
         (fn-event (my-get-event fn wrld))
         (params-to-drop (if (symbolp param-or-params-to-drop) (list param-or-params-to-drop) param-or-params-to-drop))
         (prologue (transformation-prologue fn wrld)) ;puts in install-not-normalized for fn (and its mutually-recursive partners)
         (verify-guards (if (eq :auto verify-guards) (guard-verified-p fn (w state)) verify-guards))
         )
    (if (not (fn-recursivep fn state))
        ;; we are operating on a single, non-recursive function (does it really buy us much in this case?)
        (let* ((new-fn (pick-new-name fn new-name state))
               ;;(new-fn (increment-name-suffix-safe fn state))
               (function-renaming (acons fn new-fn nil))
               (wrapper-fn (pack$ new-fn '-wrapper)) ;todo think about clashes
               (formals (fn-formals fn wrld))
               (params-to-drop-alist (acons fn params-to-drop nil))
               (new-fn-formals (set-difference-eq formals params-to-drop))
               (fn-formals-alist (acons fn formals nil)) ;or just use nil?
               (new-defun (drop-irrelevant-params-in-defun fn new-fn fn-event nil params-to-drop-alist fn-formals-alist nil function-disabled measure-hints untranslate state))
               ;; TODO: Can we often avoid adding the :verify-guards t?
               (new-defun-to-export (if verify-guards (add-verify-guards-t-to-defun new-defun) new-defun)) ; no hints to clean up since non-recursive
               (new-fn-defthm-name (pack$ fn '-becomes- new-fn))
               (new-fn-defthm (drop-irrelevant-params-defthm fn new-fn nil nil params-to-drop-alist theorem-disabled state))
               (guard-hints (guard-hints-for-drop-irrelevant-params (list fn) params-to-drop guard-hints wrld)))
          (mv nil
              `(encapsulate
                 ()
                 ,@prologue
                 (local ,new-defun)
                 (local ,new-fn-defthm)
                 ,@(and verify-guards `((local ,(verify-guards-for-defun fn function-renaming guard-hints))))
                 ,new-defun-to-export
                 ;wrapper stuff:
                 ,@(if build-wrapper nil (list new-fn-defthm)) ;this is the main theorem in the non-wrapper case
                 ;; todo: what should the guard of this be?:
                 ,@(and build-wrapper `((defun ,wrapper-fn (,@formals) (declare (ignore ,@params-to-drop)) (,new-fn ,@new-fn-formals)))) ;TODO call drop-irrelevant-params-wrapper?
                 ,@(and build-wrapper verify-guards `((verify-guards ,wrapper-fn)))
                 ,@(and build-wrapper
                        ;; Make the theorem about the wrapper function:
                        (list (make-becomes-theorem3 fn wrapper-fn nil (list wrapper-fn new-fn-defthm-name) state))))
              state))
      (if (fn-singly-recursivep fn state)
          ;; we are operating on a single, recursive function:
          (let* ((new-fn (pick-new-name fn new-name state))
                 (function-renaming (acons fn new-fn nil))
                 (wrapper-fn (pack$ new-fn '-wrapper)) ;todo think about clashes
                 (formals (fn-formals fn wrld))
                 (params-to-drop-alist (acons fn params-to-drop nil))
                 (new-fn-formals (set-difference-eq formals params-to-drop))
                 (fn-formals-alist (acons fn formals nil))
                 (new-defun (drop-irrelevant-params-in-defun fn new-fn fn-event (acons fn new-fn nil) params-to-drop-alist fn-formals-alist :single function-disabled measure-hints untranslate state)) ;;TODO: restrict the hints in this case..
               ;; TODO: Can we often avoid adding the :verify-guards t?
                 (new-defun-to-export (if verify-guards (add-verify-guards-t-to-defun new-defun) new-defun))
                 (new-defun-to-export (remove-hints-from-defun new-defun-to-export))
                 (new-fn-defthm-name (pack$ fn '-becomes- new-fn))
                 (new-fn-defthm (drop-irrelevant-params-defthm fn
                                                               new-fn
                                                               :single
                                                               nil ; enables
                                                               params-to-drop-alist
                                                               ;; new-fn-defthm-name ;maybe pass this in?
                                                               theorem-disabled
                                                               state))
                 (guard-hints (guard-hints-for-drop-irrelevant-params (list fn) params-to-drop guard-hints wrld)))
            (mv nil
                `(encapsulate
                   ()
                   ,@prologue
                   (local ,new-defun)
                   (local ,new-fn-defthm)
                   ,@(and verify-guards `((local ,(verify-guards-for-defun fn function-renaming guard-hints))))
                   ,new-defun-to-export
                   ;;wrapper stuff:
                   ,@(and (not build-wrapper) (list new-fn-defthm)) ;this is the main theorem in the non-wrapper case
                   ,@(and build-wrapper `((defun ,wrapper-fn (,@formals) (declare (ignore ,@params-to-drop)) (,new-fn ,@new-fn-formals)))) ;TODO call drop-irrelevant-params-wrapper?
                   ,@(and build-wrapper verify-guards `((verify-guards ,wrapper-fn)))
                   ,@(and build-wrapper
                          ;; Make the theorem about the wrapper function:
                          (list (make-becomes-theorem3 fn wrapper-fn nil (list wrapper-fn new-fn-defthm-name) state))))
                state))
        ;; we are operating on a mutually recursive nest of functions: ;TODO: Add support for new-fn here
        (let* ((ctx (cons 'drop-irrelevant-params fn))
               (fns (get-clique fn (w state)))
               ;; Handle the :new-name arg:
               (new-name-alist ;this is an alist, but some values may be :auto
                (elaborate-mut-rec-option2 new-name :new-name fns ctx))
               (function-renaming (pick-new-names new-name-alist state))
               (new-fns (strip-cdrs function-renaming))
               (fn (first fns)) ; why?
               (wrapper-fns (add-suffix-all new-fns '-wrapper)) ;todo think about clashes
               (wrapper-function-renaming (pairlis$ fns wrapper-fns))
;             (wrapper-fn (lookup-eq-safe fn function-renaming))
               ;; (aux-fn (lookup-eq-safe fn aux-function-renaming))
               (params-to-drop-alist (pair-all-keys fns params-to-drop))
               (fn-formals-alist (make-fn-formals-alist fns (w state)))
               (aux-defuns (drop-irrelevant-params-in-defuns fns fn-event function-renaming params-to-drop-alist fn-formals-alist :mutual function-disabled measure-hints untranslate state))
               (wrapper-defuns (drop-irrelevant-params-wrappers fns wrapper-fns new-fns params-to-drop-alist state))
               (mutual-recursion `(mutual-recursion ,@aux-defuns))
               (mutual-recursion-to-export (if verify-guards
                                               (ensure-mutual-recursion-demands-guard-verification mutual-recursion)
                                             mutual-recursion))
               (mutual-recursion-to-export (remove-hints-from-mutual-recursion mutual-recursion-to-export))
               (make-flag-form `(make-flag ,(pack$ 'flag- fn) ,fn))
               (becomes-theorems (drop-irrelevant-params-defthms fns
                                                               (repeat (len fns) nil) ;no individual enables
                                                               function-renaming :mutual (list (pack$ 'flag- fn ;seems to use the last function in the nest?
                                                                                                          '-EQUIVALENCES)) ;;gross that make-flag doesn't put in this hint for you?
                                                               PARAMS-TO-DROP-ALIST
                                                               theorem-disabled
                                                               state))
               (becomes-theorems-to-export (clean-up-defthms becomes-theorems))
               (becomes-defthm-flag `(,(pack$ 'defthm-flag- fn) ;; this is a custom kind of defthm generate by the make-flag
                                      ,@becomes-theorems))
               (guard-hints (guard-hints-for-drop-irrelevant-params fns params-to-drop guard-hints wrld))
               ) ;should we use the new or old fns here?
          (mv nil
              `(encapsulate
                 ()
                 ,@prologue
                 (local ,mutual-recursion) ;contains the aux functions
                 (local ,make-flag-form) ; helps with the proof about mutually recursive functions
                 (local ,becomes-defthm-flag)
                 ,@(and verify-guards `((local ,(verify-guards-for-defun fn function-renaming guard-hints))))
                 ;; Export the new mutual-recursion:
                 ,mutual-recursion-to-export
                 ;; Export the 'becomes' theorems, if we are in the non-wrapper case:
                 ,@(and (not build-wrapper) becomes-theorems-to-export)
                 ;; wrapper stuff:
                 ,@(and build-wrapper wrapper-defuns)
                 ,@(and build-wrapper verify-guards `((verify-guards wrapper-fn)))
                 ,@(and build-wrapper (make-becomes-theorem3s fns (repeat (len fns) nil) wrapper-function-renaming :mutual
                                                              (strip-cadrs becomes-theorems) ;enables
                                                              state)))
              state))))))

(deftransformation drop-irrelevant-params
  (fn
   param-or-params-to-drop
   )
  ((new-name ':auto)
   (build-wrapper 'nil)
   (theorem-disabled 'nil)
   (function-disabled ':auto)
   (measure-hints ':auto)
   (verify-guards ':auto)
   (guard-hints ':auto)
   (untranslate ':macros)
   )
  :short "Removes some irrelevant parameters from a function."
  :description ("An irrelevant parameter is one that is not used in the body of the
function except (perhaps) to calculate new values for the same parameter in
recursive calls."

                "This transform supports dropping multiple irrelevant parameters
simultaneously.  (I suppose all irrelevant parameters can be used to generate
new values for any other irrelevant parameters -- and still be considered
irrelevant).")
  :arg-descriptions
  ((fn "The function to transform (a defined function).")
   (param-or-params-to-drop "The param to drop (a symbol), or a list of such.")
   (new-name "The new name to use, or @(':auto') to have the transformation generate a name.  If the target function is defined in a @('mutual-recursion'), we support @(':map') syntax for the @(':new-name') option.")
   (build-wrapper "Whether to build a wrapper function.")
   (theorem-disabled "Whether to disable the 'becomes theorem'.")
   (function-disabled "Whether to disable the new function.")
     ;(verify-guards "Whether to verify the guards of the new function")
   (measure-hints "Hints to use for the measure/termination proof.")
   (verify-guards "Whether to verify guards of the new function(s).")
   (guard-hints "Hints to use for the guard proof.")
   (untranslate "How to untranslate the function body after changing it.")))
