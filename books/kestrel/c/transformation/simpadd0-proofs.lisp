; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "simpadd0")

(include-book "../syntax/langdef-mapping")
(include-book "../syntax/abstract-syntax-operations")

(include-book "../atc/symbolic-execution-rules/top")

(include-book "kestrel/std/system/constant-value" :dir :system)
(include-book "kestrel/std/system/pseudo-event-form-listp" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Very preliminary proof generation for the simpadd0 transformation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Temporary additional symbolic execution rule.

(defruled c::exec-binary-strict-pure-when-add-alt
  (implies (and (equal c::op (c::binop-add))
                (equal c::y (c::expr-value->value eval))
                (equal c::objdes-y (c::expr-value->object eval))
                (not (equal (c::value-kind c::x) :array))
                (not (equal (c::value-kind c::y) :array))
                (equal c::val (c::add-values c::x c::y))
                (c::valuep c::val))
           (equal (c::exec-binary-strict-pure
                   c::op
                   (c::expr-value c::x c::objdes-x)
                   eval)
                  (c::expr-value c::val nil)))
  :use c::exec-binary-strict-pure-when-add)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate equivalence theorem for a function.

(define simpadd0-gen-proof-for-fun ((term-old "A term.")
                                    (term-new "A term.")
                                    (fun c$::identp))
  :returns (event acl2::pseudo-event-formp)
  (b* ((string (c$::ident->unwrap fun))
       ((unless (stringp string))
        (raise "Misusage error: function name ~x0 is not a string." string)
        '(_))
       (thm-name (acl2::packn-pos (list string '-equivalence) 'c2c))
       (event
        `(defruled ,thm-name
           (equal (c::exec-fun (c::ident ,string)
                               nil
                               compst
                               (c::init-fun-env
                                (mv-nth 1 (c$::ldm-transunit ,term-old)))
                               1000)
                  (c::exec-fun (c::ident ,string)
                               nil
                               compst
                               (c::init-fun-env
                                (mv-nth 1 (c$::ldm-transunit ,term-new)))
                               1000))
           :enable (c::atc-all-rules
                    c::fun-env-lookup
                    omap::assoc
                    c::exec-binary-strict-pure-when-add-alt)
           :disable ((:e c::ident)))))
    event)
  :guard-hints (("Goal" :in-theory (enable atom-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate equivalence theorems for all functions in a translation unit.

(define simpadd0-gen-proofs-for-transunit ((term-old "A term.")
                                           (term-new "A term.")
                                           (tunit transunitp))
  :returns (events acl2::pseudo-event-form-listp)
  (simpadd0-gen-proofs-for-transunit-loop term-old
                                          term-new
                                          (c$::transunit->decls tunit))

  :prepwork
  ((define simpadd0-gen-proofs-for-transunit-loop ((term-old "A term.")
                                                   (term-new "A term.")
                                                   (extdecls extdecl-listp))
     :returns (events acl2::pseudo-event-form-listp)
     (b* (((when (endp extdecls)) nil)
          (extdecl (car extdecls))
          ((unless (extdecl-case extdecl :fundef))
           (simpadd0-gen-proofs-for-transunit-loop term-old
                                                   term-new
                                                   (cdr extdecls)))
          (fundef (c$::extdecl-fundef->unwrap extdecl))
          (declor (c$::fundef->declor fundef))
          (fun (c$::declor->ident declor))
          (event (simpadd0-gen-proof-for-fun term-old
                                             term-new
                                             fun))
          (events (simpadd0-gen-proofs-for-transunit-loop term-old
                                                          term-new
                                                          (cdr extdecls))))
       (cons event events)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate equivalence theorems for all functions in
; a translation unit ensemble.

(define simpadd0-gen-proofs-for-transunit-ensemble
  ((const-old symbolp)
   (const-new symbolp)
   (tunits-old transunit-ensemblep)
   (tunits-new transunit-ensemblep))
  :returns (events acl2::pseudo-event-form-listp)
  (simpadd0-gen-proofs-for-transunit-ensemble-loop
   const-old
   const-new
   (c$::transunit-ensemble->unwrap tunits-old)
   (c$::transunit-ensemble->unwrap tunits-new))

  :prepwork
  ((define simpadd0-gen-proofs-for-transunit-ensemble-loop
     ((const-old symbolp)
      (const-new symbolp)
      (tunitmap-old filepath-transunit-mapp)
      (tunitmap-new filepath-transunit-mapp))
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
          (events (simpadd0-gen-proofs-for-transunit term-old
                                                     term-new
                                                     tunit))
          (more-events (simpadd0-gen-proofs-for-transunit-ensemble-loop
                        const-old
                        const-new
                        (omap::tail tunitmap-old)
                        (omap::tail tunitmap-new))))
       (append events more-events)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Event macro for transformation.

(define simpadd0-fn (const-old const-new proofs (wrld plist-worldp))
  :returns (event acl2::pseudo-event-formp)
  (b* (((unless (symbolp const-old))
        (raise "~x0 must be a symbol." const-old)
        '(_))
       ((unless (symbolp const-new))
        (raise "~x0 must be a symbol." const-new)
        '(_))
       ((unless (symbolp proofs))
        (raise "~x0 must be a boolean." proofs)
        '(_))
       (tunits-old (acl2::constant-value const-old wrld))
       ((unless (transunit-ensemblep tunits-old))
        (raise "~x0 must be a translation unit ensemble.")
        '(_))
       (tunits-new (simpadd0-transunit-ensemble tunits-old))
       (thm-events (and proofs
                        (simpadd0-gen-proofs-for-transunit-ensemble
                         const-old const-new tunits-old tunits-new)))
       (const-event `(defconst ,const-new ',tunits-new)))
    `(progn ,const-event ,@thm-events)))

(defmacro simpadd0 (const-old const-new &key proofs)
  `(make-event (simpadd0-fn ',const-old ',const-new ,proofs (w state))))
