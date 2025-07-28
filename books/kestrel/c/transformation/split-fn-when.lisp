; C Library

;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/utilities/messages" :dir :system)
(include-book "std/system/constant-value" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/disambiguator")
(include-book "../syntax/validator")
(include-book "split-fn")
(include-book "utilities/fresh-ident")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (tau-system))))
(set-induction-depth-limit 0)

(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/system/w" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation split-all-gso
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define block-item-triggerp
  ((item block-itemp)
   (triggers ident-setp))
  (declare (xargs :type-prescription
                  (booleanp (block-item-triggerp item triggers))))
  (block-item-case
   item
   ;; TODO: this should probably recurse down through statement.
   :stmt (stmt-case
           item.unwrap
           :expr (and item.unwrap.expr?
                      (expr-case
                        item.unwrap.expr?
                        :funcall (expr-case
                                   item.unwrap.expr?.fun
                                   :ident (in item.unwrap.expr?.fun.ident
                                              triggers)
                                   :otherwise nil)
                        :otherwise nil))
           :otherwise nil)
   :otherwise nil))

(define block-item-list-try-split-fn-when-loop
  ((items block-item-listp)
   (triggers ident-setp)
   (position natp))
  (declare
   (xargs :type-prescription
          (or (natp (block-item-list-try-split-fn-when-loop items triggers position))
              (equal (block-item-list-try-split-fn-when-loop items triggers position) nil))))
  (cond ((endp items)
         nil)
        ((block-item-triggerp (first items) triggers)
         (mbe :logic (nfix position)
              :exec position))
        (t (block-item-list-try-split-fn-when-loop
             (rest items)
             triggers
             (+ position 1))))
  :guard-hints (("Goal" :in-theory (enable nfix))))

(define block-item-list-try-split-fn-when
  ((items block-item-listp)
   (triggers ident-setp))
  (declare
   (xargs :type-prescription
          (or (natp (block-item-list-try-split-fn-when items triggers))
              (equal (block-item-list-try-split-fn-when items triggers) nil))))
  (if (or (endp items)
          (endp (rest items)))
      nil
    (block-item-list-try-split-fn-when-loop (rest items) triggers 1)))

;; Note: This does *not* split if the trigger is the first statement. This
;; would be a loop.
;; Note: we split right *before* trigger (could be configured for after)
;; Only error on malformed syntax (I think)
(define fundef-try-split-fn-when
  ((fundef fundefp)
   ;; For now, the trigger is a function name.
   (triggers ident-setp)
   ;; To check for name freshness
   (transunits transunit-ensemblep))
  :returns (mv (er? maybe-msgp)
               (fundef1 fundefp)
               (fundef2 fundef-optionp))
  (b* (((reterr) (c$::irr-fundef) nil)
       (fundef (fundef-fix fundef))
       ((fundef fundef) fundef)
       ((declor fundef.declor) fundef.declor))
    (stmt-case
      fundef.body
      :compound
      (b* ((position?
             (block-item-list-try-split-fn-when fundef.body.items triggers))
           ((unless position?)
            (retok fundef nil))
           ((erp fun-name)
            (b* (((reterr) nil))
              (dirdeclor-case
                fundef.declor.direct
                :function-params
                (retok (c$::dirdeclor->ident fundef.declor.direct.declor))
                :function-names
                (retok (c$::dirdeclor->ident fundef.declor.direct.declor))
                :otherwise (retmsg$ "Malformed syntax.")))))
        (split-fn-fundef
          fun-name
          (transunit-ensemble-fresh-ident fun-name transunits)
          fundef
          position?))
      :otherwise (retmsg$ "Malformed syntax."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extdecl-try-split-fn-when
  ((extdecl extdeclp)
   (triggers ident-setp)
   (transunits transunit-ensemblep))
  :returns (mv (er? maybe-msgp)
               (found booleanp :rule-classes :type-prescription)
               (extdecls extdecl-listp))
  (b* (((reterr) nil nil))
    (extdecl-case
      extdecl
      :fundef (b* (((erp fundef1 fundef2)
                    (fundef-try-split-fn-when
                      extdecl.unwrap
                      triggers
                      transunits)))
                (fundef-option-case
                  fundef2
                  :some (retok t (list (extdecl-fundef fundef1)
                                       (extdecl-fundef fundef2.val)))
                  :none (retok nil (list (extdecl-fundef fundef1)))))
      :otherwise (retok nil (list (extdecl-fix extdecl)))))
  ///
  (more-returns
   (extdecls true-listp :rule-classes :type-prescription)))

(define extdecl-list-try-split-fn-when
  ((extdecls extdecl-listp)
   (triggers ident-setp)
   (transunits transunit-ensemblep))
  :returns (mv (er? maybe-msgp)
               (found booleanp :rule-classes :type-prescription)
               (extdecls$ extdecl-listp))
  (b* (((reterr) nil nil)
       ((when (endp extdecls))
        (retok nil nil))
       ((erp found extdecls1)
        (extdecl-try-split-fn-when (first extdecls) triggers transunits))
       ((when found)
        (retok t (append extdecls1 (extdecl-list-fix (rest extdecls)))))
       ((erp found extdecls2)
        (extdecl-list-try-split-fn-when (rest extdecls) triggers transunits)))
    (retok found (append extdecls1 extdecls2)))
  ///
  (more-returns
   (extdecls$ true-listp :rule-classes :type-prescription)))

(define transunit-try-split-fn-when
  ((tunit transunitp)
   (triggers ident-setp)
   (transunits transunit-ensemblep))
  :returns (mv (er? maybe-msgp)
               (found booleanp :rule-classes :type-prescription)
               (tunit$ transunitp))
  (b* (((reterr) nil (c$::irr-transunit))
       ((transunit tunit) tunit)
       ((erp found extdecls)
        (extdecl-list-try-split-fn-when tunit.decls triggers transunits)))
    (retok found
           (make-transunit :decls extdecls :info tunit.info))))

(define filepath-transunit-map-try-split-fn-when
  ((map filepath-transunit-mapp)
   (triggers ident-setp)
   (transunits transunit-ensemblep))
  :returns (mv (er? maybe-msgp)
               (found booleanp :rule-classes :type-prescription)
               (map$ filepath-transunit-mapp))
  (b* (((reterr) nil nil)
       (map (c$::filepath-transunit-map-fix map))
       ((when (omap::emptyp map))
        (retok nil nil))
       ((mv path tunit) (omap::head map))
       ((erp found tunit$)
        (transunit-try-split-fn-when tunit triggers transunits))
       ((when found)
        (retok found
               (omap::update path tunit$ (omap::tail map))))
       ((erp found map$)
        (filepath-transunit-map-try-split-fn-when
          (omap::tail map)
          triggers
          transunits)))
    (retok found
           (omap::update path tunit$ map$)))
  :verify-guards :after-returns)

(define transunit-ensemble-try-split-fn-when
  ((tunits transunit-ensemblep)
   (triggers ident-setp))
  :returns (mv (er? maybe-msgp)
               (found booleanp :rule-classes :type-prescription)
               (tunits$ transunit-ensemblep))
  (b* (((reterr) nil (irr-transunit-ensemble))
       ((transunit-ensemble tunits) tunits)
       ((erp found map)
        (filepath-transunit-map-try-split-fn-when tunits.unwrap
                                                  triggers
                                                  tunits)))
    (retok found (transunit-ensemble map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transunit-ensemble-split-fn-when
  ((tunits transunit-ensemblep)
   (triggers ident-setp))
  :returns (mv (er? maybe-msgp)
               (tunits$ transunit-ensemblep))
  (transunit-ensemble-split-fn-when-loop
    tunits
    triggers
    (acl2::the-fixnat (- (expt 2 acl2::*fixnat-bits*) 1)))

  :prepwork
  ((define transunit-ensemble-split-fn-when-loop
     ((tunits transunit-ensemblep)
      (triggers ident-setp)
      (steps :type #.acl2::*fixnat-type*))
     :returns (mv (er? maybe-msgp)
                  (tunits$ transunit-ensemblep))
     (b* (((reterr) (irr-transunit-ensemble))
          ((when (= 0 (mbe :logic (nfix steps)
                           :exec (acl2::the-fixnat steps))))
           (retmsg$ "Out of steps."))
          ((erp found tunits$)
           (transunit-ensemble-try-split-fn-when tunits triggers))
          ((unless found)
           (retok tunits$)))
       (transunit-ensemble-split-fn-when-loop
         tunits$
         triggers
         (- steps 1)))
     :measure (nfix steps)
     :hints (("Goal" :in-theory (enable nfix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing split-fn-when)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-when-process-inputs
  (const-old
   const-new
   triggers
   (wrld plist-worldp))
  :returns (mv (er? maybe-msgp)
               (tunits (and (transunit-ensemblep tunits)
                            (c$::transunit-ensemble-annop tunits))
                       :hints (("Goal" :in-theory (enable c$::irr-transunit-ensemble))))
               (const-new$ symbolp :rule-classes :type-prescription)
               (triggers string-listp))
  :short "Process the inputs."
  (b* (((reterr) (c$::irr-transunit-ensemble) nil nil)
       ((unless (symbolp const-old))
        (retmsg$ "~x0 must be a symbol" const-old))
       (tunits (acl2::constant-value const-old wrld))
       ((unless (transunit-ensemblep tunits))
        (retmsg$ "~x0 must be a translation unit ensemble." const-old))
       ((unless (c$::transunit-ensemble-annop tunits))
        (retmsg$ "~x0 must be an annotated with validation information." const-old))
       ((unless (symbolp const-new))
        (retmsg$ "~x0 must be a symbol" const-new))
       (triggers (if (stringp triggers)
                     (list triggers)
                   triggers))
       ((unless (string-listp triggers))
        (retmsg$ "~x0 must be a string or string list" triggers))
       ((when (endp triggers))
        (retmsg$ "~x0 must be a list with at least one element" triggers)))
    (retok tunits const-new triggers))
  :guard-hints (("Goal" :in-theory (enable string-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation split-fn-when)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-list-to-ident-set
  ((strings string-listp))
  :returns (idents ident-setp)
  (if (endp strings)
      nil
    (insert (ident (first strings))
            (string-list-to-ident-set (rest strings))))
  :guard-hints (("Goal" :in-theory (enable string-listp)))
  :verify-guards :after-returns)

(define split-fn-when-gen-everything
  ((tunits transunit-ensemblep)
   (const-new symbolp)
   (triggers string-listp))
  :guard (c$::transunit-ensemble-annop tunits)
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :short "Generate all the events."
  (b* (((reterr) '(_))
       ((erp tunits)
        (transunit-ensemble-split-fn-when tunits
                                          (string-list-to-ident-set triggers)))
       (defconst-event
         `(defconst ,const-new
            ',tunits)))
    (retok defconst-event)))

(define split-fn-when-process-inputs-and-gen-everything
  (const-old
   const-new
   triggers
   (wrld plist-worldp))
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp tunits const-new triggers)
        (split-fn-when-process-inputs const-old
                                      const-new
                                      triggers
                                      wrld))
       ((erp event)
        (split-fn-when-gen-everything tunits
                                      const-new
                                      triggers)))
    (retok event)))

(define split-fn-when-fn (const-old
                          const-new
                          triggers
                          (ctx ctxp)
                          state)
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (event pseudo-event-formp)
               state)
  :parents (split-fn-when-implementation)
  :short "Event expansion of @(tsee split-fn-when)."
  (b* (((mv erp event)
        (split-fn-when-process-inputs-and-gen-everything
          const-old
          const-new
          triggers
          (w state)))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

(defmacro split-fn-when
  (const-old
   const-new
   &key
   triggers)
  `(make-event (split-fn-when-fn ',const-old
                                 ',const-new
                                 ',triggers
                                 'split-fn-when
                                 state)))
