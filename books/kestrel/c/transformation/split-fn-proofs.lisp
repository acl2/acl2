; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "split-fn")

(include-book "../syntax/langdef-mapping")

(include-book "../atc/symbolic-execution-rules/top")

(include-book "std/system/constant-value" :dir :system)
(include-book "std/system/pseudo-event-form-listp" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book is adapted from simpadd0.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-gen-proof-for-fun (term-old
                                    term-new
                                    (fun c$::identp)
                                    new-fn-name)
  ;; Right now new-fn-name is ignored, but in the future we likely want to use
  ;; it to generate a more target expansion hint
  (declare (ignore new-fn-name))
  :returns (event acl2::pseudo-event-formp)
  (b* ((string (c$::ident->unwrap fun))
       ((unless (stringp string))
        (raise "Misusage error: function name ~x0 is not a string." string)
        '(_))
       (thm-name (acl2::packn-pos (list string '-equivalence) 'c2c))
       (event
        `(defruled ,thm-name
           (let ((trans-old (c$::ldm-transunit ,term-old))
                 (trans-new (c$::ldm-transunit ,term-new)))
             (and (not (mv-nth 0 trans-old))
                  (not (mv-nth 0 trans-new))
                  (equal (c::exec-fun (c::ident ,string)
                                      nil
                                      compst
                                      (c::init-fun-env (mv-nth 1 trans-old))
                                      1000)
                         (c::exec-fun (c::ident ,string)
                                      nil
                                      compst
                                      (c::init-fun-env (mv-nth 1 trans-new))
                                      1000))))
           :enable (c::atc-all-rules
                    c::fun-env-lookup
                    omap::assoc
                    c::exec-fun
                    )
           :disable ((:e c::ident))
           ;; TODO: why is it not sufficient to only expand the new function
           ;; call, without enabling c::exec-fun?
           ;; :expand ((:free (args compst fenv limit)
           ;;                 (c::exec-fun ',new-fn-name args compst fenv limit)))
           )))
    event)
  :guard-hints (("Goal" :in-theory (enable atom-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-gen-proofs-for-transunit
  (term-old
   term-new
   (tunit transunitp)
   new-fn-name)
  :returns (events acl2::pseudo-event-form-listp)
  (split-fn-gen-proofs-for-transunit-loop term-old
                                          term-new
                                          (c$::transunit->decls tunit)
                                          new-fn-name)

  :prepwork
  ((define split-fn-gen-proofs-for-transunit-loop
     (term-old
      term-new
      (extdecls extdecl-listp)
      new-fn-name)
     :returns (events acl2::pseudo-event-form-listp)
     (b* (((when (endp extdecls)) nil)
          (extdecl (car extdecls))
          ((unless (extdecl-case extdecl :fundef))
           (split-fn-gen-proofs-for-transunit-loop term-old
                                                   term-new
                                                   (cdr extdecls)
                                                   new-fn-name))
          (fundef (c$::extdecl-fundef->unwrap extdecl))
          (declor (c$::fundef->declor fundef))
          (fun (c$::declor->ident declor))
          (event (split-fn-gen-proof-for-fun term-old
                                             term-new
                                             fun
                                             new-fn-name))
          (events (split-fn-gen-proofs-for-transunit-loop term-old
                                                          term-new
                                                          (cdr extdecls)
                                                          new-fn-name)))
       (cons event events)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-gen-proofs-for-transunit-ensemble
  ((const-old symbolp)
   (const-new symbolp)
   (tunits-old transunit-ensemblep)
   (tunits-new transunit-ensemblep)
   new-fn-name)
  :returns (events acl2::pseudo-event-form-listp)
  (split-fn-gen-proofs-for-transunit-ensemble-loop
   const-old
   const-new
   (c$::transunit-ensemble->unwrap tunits-old)
   (c$::transunit-ensemble->unwrap tunits-new)
   new-fn-name)

  :prepwork
  ((define split-fn-gen-proofs-for-transunit-ensemble-loop
     ((const-old symbolp)
      (const-new symbolp)
      (tunitmap-old filepath-transunit-mapp)
      (tunitmap-new filepath-transunit-mapp)
      new-fn-name)
     :returns (events acl2::pseudo-event-form-listp)
     (b* (((when (omap::emptyp tunitmap-old)) nil)
          ((when (omap::emptyp tunitmap-new))
           (raise "Internal error: extra translation units ~x0." tunitmap-new))
          ((mv path-old tunit) (omap::head tunitmap-old))
          ((mv path-new &) (omap::head tunitmap-new))
          (term-old `(omap::lookup
                      ',path-old
                      (c$::transunit-ensemble->unwrap ,const-old)))
          (term-new `(omap::lookup
                      ',path-new
                      (c$::transunit-ensemble->unwrap ,const-new)))
          (events (split-fn-gen-proofs-for-transunit term-old
                                                     term-new
                                                     tunit
                                                     new-fn-name))
          (more-events (split-fn-gen-proofs-for-transunit-ensemble-loop
                        const-old
                        const-new
                        (omap::tail tunitmap-old)
                        (omap::tail tunitmap-new)
                        new-fn-name)))
       (append events more-events)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Event macro for transformation.

(define split-fn-macro
  (const-old
   const-new
   target-fn
   new-fn-name
   split-point
   proofs
   (wrld plist-worldp))
  :returns (event acl2::pseudo-event-formp)
  (b* (((unless (symbolp const-old))
        (raise "~x0 must be a symbol." const-old)
        '(_))
       ((unless (symbolp const-new))
        (raise "~x0 must be a symbol." const-new)
        '(_))
       ((unless (identp target-fn))
        (raise "~x0 must be a C identifier." target-fn)
        '(_))
       ((unless (identp new-fn-name))
        (raise "~x0 must be a C identifier." new-fn-name)
        '(_))
       ((unless (natp split-point))
        (raise "~x0 must be a natural number." split-point)
        '(_))
       ((unless (symbolp proofs))
        (raise "~x0 must be a boolean." proofs)
        '(_))
       (tunits-old (acl2::constant-value const-old wrld))
       ((unless (transunit-ensemblep tunits-old))
        (raise "~x0 must be a translation unit ensemble.")
        '(_))
       ((mv er tunits-new)
        (split-fn-transunit-ensemble target-fn
                                     new-fn-name
                                     tunits-old
                                     split-point))
       ((when er)
        (raise "~@0" er)
        '(_))
       (thm-events (and proofs
                        (split-fn-gen-proofs-for-transunit-ensemble const-old
                                                                    const-new
                                                                    tunits-old
                                                                    tunits-new
                                                                    new-fn-name)))
       (const-event `(defconst ,const-new ',tunits-new)))
    `(progn ,const-event ,@thm-events)))

(defmacro split-fn
  (const-old
   const-new
   target-fn
   new-fn-name
   split-point
   &key proofs)
  `(make-event (split-fn-macro ',const-old
                               ',const-new
                               ,target-fn
                               ,new-fn-name
                               ,split-point
                               ,proofs
                               (w state))))
