; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "statements")
(include-book "ports")      ;; vl-portdecllist-p, vl-portlist-p
(include-book "nets")       ;; vl-assignlist-p, vl-netdecllist-p
(include-book "blockitems") ;; vl-vardecllist-p, vl-eventdecllist-p, vl-paramdecllist-p
(include-book "insts")      ;; vl-modinstlist-p
(include-book "gates")      ;; vl-gateinstlist-p
(include-book "functions")  ;; vl-fundecllist-p
(include-book "../make-implicit-wires")
(include-book "../../mlib/context")  ;; vl-modelement-p, sorting modelements
(include-book "../../mlib/port-tools")  ;; vl-ports-from-portdecls
(local (include-book "../../util/arithmetic"))

(define vl-make-module-by-items

; Our various parsing functions for declarations, assignments, etc., return all
; kinds of different module items.  We initially get all of these different
; kinds of items as a big list.  Then, here, we sort it into buckets by type,
; and turn it into a module.

  ((name     stringp)
   (params   ) ;; BOZO guards and such
   (ports    vl-portlist-p)
   (items    vl-modelementlist-p)
   (atts     vl-atts-p)
   (minloc   vl-location-p)
   (maxloc   vl-location-p)
   (warnings vl-warninglist-p))
  :returns (mod vl-module-p)
  (b* (((mv items warnings) (vl-make-implicit-wires items warnings))
       ((mv item-ports portdecls assigns netdecls vardecls eventdecls paramdecls
            fundecls taskdecls modinsts gateinsts alwayses initials)
        (vl-sort-modelements items nil nil nil nil nil nil nil nil nil nil nil nil nil)))
    (or (not item-ports)
        (raise "There shouldn't be any ports in the items."))
    (make-vl-module :name       name
                    :params     params
                    :ports      ports
                    :portdecls  portdecls
                    :assigns    assigns
                    :netdecls   netdecls
                    :vardecls   vardecls
                    :eventdecls eventdecls
                    :paramdecls paramdecls
                    :fundecls   fundecls
                    :taskdecls  taskdecls
                    :modinsts   modinsts
                    :gateinsts  gateinsts
                    :alwayses   alwayses
                    :initials   initials
                    :atts       atts
                    :minloc     minloc
                    :maxloc     maxloc
                    :warnings   warnings
                    :origname   name
                    :comments   nil
                    )))

(defparser vl-parse-initial-construct (atts)
  :guard (vl-atts-p atts)
  :result (vl-initiallist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (kwd := (vl-match-token :vl-kwd-initial))
        (stmt := (vl-parse-statement))
        (return (list (make-vl-initial :loc (vl-token->loc kwd)
                                       :stmt stmt
                                       :atts atts)))))

(defparser vl-parse-always-construct (atts)
  :guard (vl-atts-p atts)
  :result (vl-alwayslist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (kwd := (vl-match-token :vl-kwd-always))
        (stmt := (vl-parse-statement))
        (return (list (make-vl-always :loc (vl-token->loc kwd)
                                      :stmt stmt
                                      :atts atts)))))




;                           UNIMPLEMENTED PRODUCTIONS
;
; Eventually we may implement some more of these.  For now, we just cause
; an error if any of them is used.
;
; BOZO consider changing some of these to skip tokens until 'endfoo' and issue
; a warning.
;

(defparser vl-parse-specify-block-aux ()
  ;; BOZO this is really not implemented.  We just read until endspecify,
  ;; throwing away any tokens we encounter until it.
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-endspecify)
          (:= (vl-match))
          (return nil))
        (:s= (vl-match-any))
        (:= (vl-parse-specify-block-aux))
        (return nil)))

(defparser vl-parse-specify-block ()
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (if (not (consp tokens))
      (vl-parse-error "Unexpected EOF.")
    (seqw tokens warnings
          (:= (vl-parse-warning :vl-warn-specify
                                (cat "Specify blocks are not yet implemented.  "
                                     "Instead, we are simply ignoring everything "
                                     "until 'endspecify'.")))
          (ret := (vl-parse-specify-block-aux))
          (return ret))))


(defparser vl-parse-generate-region-aux ()
  ;; BOZO this is really not implemented.  We just read until endgenerate,
  ;; throwing away any tokens we encounter until it.
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-endgenerate)
          (:= (vl-match))
          (return nil))
        (:s= (vl-match-any))
        (:= (vl-parse-generate-region-aux))
        (return nil)))

(defparser vl-parse-generate-region ()
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (if (not (consp tokens))
      (vl-parse-error "Unexpected EOF.")
    (seqw tokens warnings
          (:= (vl-parse-warning :vl-warn-generate
                                (cat "Generate regions are not yet implemented.  "
                                     "Instead, we are simply ignoring everything "
                                     "until 'endgenerate'.")))
          (ret := (vl-parse-generate-region-aux))
          (return ret))))

(defparser vl-parse-specparam-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))

(defparser vl-parse-genvar-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (seqw tokens warnings
        (:= (vl-parse-warning :vl-warn-genvar
                              (cat "Genvar declarations are not implemented, we are just skipping this genvar.")))
        (:= (vl-match-token :vl-kwd-genvar))
        (:= (vl-parse-1+-identifiers-separated-by-commas))
        (:= (vl-match-token :vl-semi))
        (return nil)))

(defparser vl-parse-parameter-override (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))

(defparser vl-parse-loop-generate-construct (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))

(defparser vl-parse-conditional-generate-construct (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))







;                                 MODULE ITEMS
;
; Note below that I have flattened out module_or_generate_item_declaration
; below.  Also note that port_declarations also begin with
; {attribute_instance}, so really the only module items that can't have
; attributes are generate_region and specify_block.
;
; module_item ::=                                             ;; STARTS WITH
;    port_declaration ';'                                     ;; a direction
;  | non_port_module_item                                     ;;
;                                                             ;;
; non_port_module_item ::=                                    ;;
;    module_or_generate_item                                  ;;
;  | generate_region                                          ;; 'generate'
;  | specify_block                                            ;; 'specify'
;  | {attribute_instance} parameter_declaration ';'           ;; 'parameter'
;  | {attribute_instance} specparam_declaration               ;; 'specparam'
;                                                             ;;
; module_or_generate_item ::=                                 ;;
;    {attribute_instance} net_declaration                     ;; [see below]
;  | {attribute_instance} reg_declaration                     ;; 'reg'
;  | {attribute_instance} integer_declaration                 ;; 'integer'
;  | {attribute_instance} real_declaration                    ;; 'real'
;  | {attribute_instance} time_declaration                    ;; 'time'
;  | {attribute_instance} realtime_declaration                ;; 'realtime'
;  | {attribute_instance} event_declaration                   ;; 'event'
;  | {attribute_instance} genvar_declaration                  ;; 'genvar'
;  | {attribute_instance} task_declaration                    ;; 'task'
;  | {attribute_instance} function_declaration                ;; 'function'
;  | {attribute_instance} local_parameter_declaration ';'     ;; 'localparam'
;  | {attribute_instance} parameter_override                  ;; 'defparam'
;  | {attribute_instance} continuous_assign                   ;; 'assign'
;  | {attribute_instance} gate_instantiation                  ;; [see below]
;  | {attribute_instance} udp_instantiation                   ;; identifier
;  | {attribute_instance} module_instantiation                ;; identifier
;  | {attribute_instance} initial_construct                   ;; 'initial'
;  | {attribute_instance} always_construct                    ;; 'always'
;  | {attribute_instance} loop_generate_construct             ;; 'for'
;  | {attribute_instance} conditional_generate_construct      ;; 'if' or 'case'
;
; Net declarations begin with a net_type or a trireg.
;
; Gate instantiations begin with one of the many *vl-gate-type-keywords*.

(defconst *vl-netdecltypes-kwds*
  (strip-cars *vl-netdecltypes-kwd-alist*))

(defparser vl-parse-module-or-generate-item (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (b* (((when (atom tokens))
        (vl-parse-error "Unexpected EOF."))
       (type1 (vl-token->type (car tokens)))
       ((when (member type1 *vl-netdecltypes-kwds*))
        (seqw tokens warnings
              ((assigns . decls) := (vl-parse-net-declaration atts))
              ;; Note: this order is important, the decls have to come first
              ;; or we'll try to infer implicit nets from the assigns.
              (return (append decls assigns))))
       ((when (member type1 *vl-gate-type-keywords*))
        (vl-parse-gate-instantiation atts))
       ((when (eq type1 :vl-kwd-genvar))
        (vl-parse-genvar-declaration atts))
       ((when (eq type1 :vl-kwd-task))
        (seqw tokens warnings
              (task := (vl-parse-task-declaration atts))
              (return (list task))))
       ((when (eq type1 :vl-kwd-function))
        (seqw tokens warnings
              (fun := (vl-parse-function-declaration atts))
              (return (list fun))))
       ((when (eq type1 :vl-kwd-localparam))
        (seqw tokens warnings
              ;; Note: non-local parameters not allowed
              (ret := (vl-parse-param-or-localparam-declaration atts '(:vl-kwd-localparam)))
              (:= (vl-match-token :vl-semi))
              (return ret)))
       ((when (eq type1 :vl-kwd-defparam))
        (vl-parse-parameter-override atts))
       ((when (eq type1 :vl-kwd-assign))
        (vl-parse-continuous-assign atts))
       ((when (eq type1 :vl-idtoken))
        (vl-parse-udp-or-module-instantiation atts))
       ((when (eq type1 :vl-kwd-initial))
        (vl-parse-initial-construct atts))
       ((when (eq type1 :vl-kwd-always))
        (vl-parse-always-construct atts))
       ((when (eq type1 :vl-kwd-for))
        (vl-parse-loop-generate-construct atts))
       ((when (or (eq type1 :vl-kwd-if)
                  (eq type1 :vl-kwd-case)))
        (vl-parse-conditional-generate-construct atts))
       ((when (eq type1 :vl-kwd-event))
        ;; BOZO eventually maybe merge this into vardecls?
        (vl-parse-event-declaration atts)))
    ;; BOZO need to switch this for SystemVerilog to cover additional types.
    (case type1
      (:vl-kwd-reg        (vl-parse-reg-declaration atts))
      (:vl-kwd-integer    (vl-parse-integer-declaration atts))
      (:vl-kwd-real       (vl-parse-real-declaration atts))
      (:vl-kwd-time       (vl-parse-time-declaration atts))
      (:vl-kwd-realtime   (vl-parse-realtime-declaration atts))
      (t
       (vl-parse-error "Invalid module or generate item.")))))

(defparser vl-parse-non-port-module-item (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  :hint-chicken-switch t
  (cond ((vl-is-token? :vl-kwd-generate)
         (if atts
             (vl-parse-error "'generate' is not allowed to have attributes.")
           (vl-parse-generate-region)))
        ((vl-is-token? :vl-kwd-specify)
         (if atts
             (vl-parse-error "'specify' is not allowed to have attributes.")
           (vl-parse-specify-block)))
        ((vl-is-token? :vl-kwd-parameter)
         (seqw tokens warnings
               ;; localparams are handled in parse-module-or-generate-item
               (ret := (vl-parse-param-or-localparam-declaration atts '(:vl-kwd-parameter)))
               (:= (vl-match-token :vl-semi))
               (return ret)))
        ((vl-is-token? :vl-kwd-specparam)
         (vl-parse-specparam-declaration atts))
        (t
         (vl-parse-module-or-generate-item atts))))

(defparser vl-parse-module-item ()
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (atts := (vl-parse-0+-attribute-instances))
        (when (vl-is-some-token? *vl-directions-kwds*)
          ((portdecls . netdecls) := (vl-parse-port-declaration-noatts atts))
          (:= (vl-match-token :vl-semi))
          ;; Should be fewer netdecls so this is the better order for the append.
          (return (append netdecls portdecls)))
        (ret := (vl-parse-non-port-module-item atts))
        (return ret)))




; module_parameter_port_list ::= '#' '(' parameter_declaration { ',' parameter_declaration } ')'

(defparser vl-parse-module-parameter-port-list-aux ()
  ;; parameter_declaration { ',' parameter_declaration }
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        ;; No attributes, no localparams allowed.
        (first := (vl-parse-param-or-localparam-declaration nil nil))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-module-parameter-port-list-aux)))
        (return (append first rest))))

(defparser vl-parse-module-parameter-port-list ()
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-pound))
        (:= (vl-match-token :vl-lparen))
        (params := (vl-parse-module-parameter-port-list-aux))
        (:= (vl-match-token :vl-rparen))
        (return params)))



;                                    MODULES
;
; module_declaration ::=
;
;   // I call this "Variant 1"
;
;    {attribute_instance} module_keyword identifier [module_parameter_port_list]
;        list_of_ports ';' {module_item}
;        'endmodule'
;
;
;   // I call this "Variant 2"
;
;  | {attribute_instance} module_keyword identifier [module_parameter_port_list]
;        [list_of_port_declarations] ';' {non_port_module_item}
;        'endmodule'
;
; module_keyword ::= 'module' | 'macromodule'

(defparser vl-parse-module-items-until-endmodule ()
  ;; Look for module items until :vl-kwd-endmodule is encountered.
  ;; Does NOT eat the :vl-kwd-endmodule
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-endmodule)
          (return nil))
        (first := (vl-parse-module-item))
        (rest := (vl-parse-module-items-until-endmodule))
        (return (append first rest))))

(defparser vl-parse-non-port-module-items-until-endmodule ()
  ;; Look for non-port module items until :vl-kwd-endmodule is encountered.
  ;; Does NOT eat the :vl-kwd-endmodule
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-endmodule)
          (return nil))
        (atts := (vl-parse-0+-attribute-instances))
        (first := (vl-parse-non-port-module-item atts))
        (rest := (vl-parse-non-port-module-items-until-endmodule))
        (return (append first rest))))



(defparser vl-parse-module-declaration-variant-1 (atts module_keyword id)
  :guard (and (vl-atts-p atts)
              (vl-token-p module_keyword)
              (vl-idtoken-p id))
  :result (vl-module-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong

; We try to match Variant 1:
;
;    {attribute_instance} module_keyword identifier [module_parameter_port_list]
;        list_of_ports ';' {module_item}
;        'endmodule'
;
; But we assume that
;
;   (1) the attributes, "module" or "macromodule", and the name of this module
;       have already been read, and
;
;   (2) the warnings we're given are initially NIL, so all warnings we come up
;       with until the end of the module 'belong' to this module.

  (seqw tokens warnings
        (when (vl-is-token? :vl-pound)
          (params := (vl-parse-module-parameter-port-list)))
        (when (vl-is-token? :vl-lparen)
          (ports := (vl-parse-list-of-ports)))
        (:= (vl-match-token :vl-semi))
        (items := (vl-parse-module-items-until-endmodule))
        (endkwd := (vl-match-token :vl-kwd-endmodule))

        ;; BOZO SystemVerilog adds various things we don't support yet, but it
        ;; definitely adds "endmodule : name" style endings.
        (when (and (vl-is-token? :vl-colon)
                   (not (eq (vl-loadconfig->edition config) :verilog-2005)))
          (:= (vl-match-token :vl-colon))
          (endname := (vl-match-token :vl-idtoken)))

        (when (and endname
                   (not (equal (vl-idtoken->name id) (vl-idtoken->name endname))))
          (return-raw
           (vl-parse-error
            (cat "Mismatched module/endmodule pair: expected "
                 (vl-idtoken->name id) " but found "
                 (vl-idtoken->name endname)))))

        (return (vl-make-module-by-items (vl-idtoken->name id)
                                         params ports items atts
                                         (vl-token->loc module_keyword)
                                         (vl-token->loc endkwd)
                                         warnings))))


(defparser vl-parse-module-declaration-variant-2 (atts module_keyword id)
  :guard (and (vl-atts-p atts)
              (vl-token-p module_keyword)
              (vl-idtoken-p id))
  :result (vl-module-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong

; This is for Variant 2.
;
;  | {attribute_instance} module_keyword identifier [module_parameter_port_list]
;        [list_of_port_declarations] ';' {non_port_module_item}
;        'endmodule'

  (seqw tokens warnings
        (when (vl-is-token? :vl-pound)
          (params := (vl-parse-module-parameter-port-list)))
        (when (vl-is-token? :vl-lparen)
          ((portdecls . netdecls) := (vl-parse-list-of-port-declarations)))
        (:= (vl-match-token :vl-semi))
        (items := (vl-parse-non-port-module-items-until-endmodule))
        (endkwd := (vl-match-token :vl-kwd-endmodule))

        ;; BOZO SystemVerilog adds various things we don't support yet, but it
        ;; definitely adds ": name" endings:
        (when (and (vl-is-token? :vl-colon)
                   (not (eq (vl-loadconfig->edition config) :verilog-2005)))
          (:= (vl-match-token :vl-colon))
          (endname := (vl-match-token :vl-idtoken)))
        (when (and endname
                   (not (equal (vl-idtoken->name id) (vl-idtoken->name endname))))
          (return-raw
           (vl-parse-error
            (cat "Mismatched module/endmodule pair: expected "
                 (vl-idtoken->name id) " but found "
                 (vl-idtoken->name endname)))))

        (return (vl-make-module-by-items (vl-idtoken->name id)
                                         params
                                         (vl-ports-from-portdecls portdecls)
                                         (append netdecls portdecls items)
                                         atts
                                         (vl-token->loc module_keyword)
                                         (vl-token->loc endkwd)
                                         warnings))))



(defparser vl-parse-module-main (atts module_keyword id)
  :guard (and (vl-atts-p atts)
              (vl-token-p module_keyword)
              (vl-idtoken-p id))
  :result (vl-module-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; Main function to try to parse a module either way.
  (b* (((mv err1 mod v1-tokens &)
        ;; A weird twist is that we want to associate all warnings encountered
        ;; during the parsing of a module with that module as it is created,
        ;; and NOT return them in the global list of warnings.  Because of
        ;; this, we use a fresh warnings accumulator here.
        (vl-parse-module-declaration-variant-1 atts module_keyword id
                                               :tokens tokens
                                               :warnings nil))
       ((unless err1)
        ;; Successfully parsed the module using variant 1.  We return the
        ;; results from variant-1, except that we've already trapped the
        ;; v1-warnings and associated them with mod, so we can just restore the
        ;; previously encountered warnings.
        (mv err1 mod v1-tokens warnings))

       ((mv err2 mod v2-tokens &)
        ;; Similar handling for warnings
        (vl-parse-module-declaration-variant-2 atts module_keyword id
                                               :tokens tokens
                                               :warnings nil))
       ((unless err2)
        ;; Successfully parsed using variant 2.  Similar deal.
        (mv err2 mod v2-tokens warnings))

       ;; If we get this far, we saw "module foo" but were not able to parse
       ;; the rest of this module definiton using either variant.  We need to
       ;; report a parse error.  But which error do we report?  We have two
       ;; errors, one from our Variant-1 attempt to parse the module, and one
       ;; from our Variant-2 attempt.
       ;;
       ;; Well, originally I thought I'd just report both errors, but that was
       ;; a really bad idea.  Why?  Well, imagine a mostly-well-formed module
       ;; that happens to have a parse error far down within it.  Instead of
       ;; getting told, "hey, I was expecting a semicolon after "assign foo =
       ;; bar", the user gets TWO parse errors, one of which properly says
       ;; this, but the other of which says that there's a parse error very
       ;; closely after the module keyword.  (The wrong variant tends to fail
       ;; very quickly because we either hit a list_of_port_declarations or a
       ;; list_of_ports, at which point we get a failure.)  This parse error is
       ;; really hard to understand, because where it occurs the module looks
       ;; perfectly well-formed (under the other variant).
       ;;
       ;; So, as a gross but workable sort of hack, my new approach is simply:
       ;; whichever variant "got farther" was probably the variant that we
       ;; wanted to follow, so we'll just report its parse-error.  Maybe some
       ;; day we'll rework the module parser so that it doesn't use
       ;; backtracking so aggressively.
       ((when (<= (len v1-tokens) (len v2-tokens)))
        ;; Variant 1 got farther (or as far), so use it.
        (mv err1 nil v1-tokens warnings)))
    ;; Variant 2 got farther
    (mv err2 nil v2-tokens warnings)))


(defparser vl-skip-through-endmodule ()
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong

; This is a special function which is used to provide more fault-tolerance in
; module parsing.  Historically, we just advanced the token stream until
; :vl-kwd-endmodule was encountered.  For SystemVerilog, we also capture the
; "endmodule : foo" part and return a proper vl-endinfo-p.

  (seqw tokens warnings
        (unless (vl-is-token? :vl-kwd-endmodule)
          (:s= (vl-match-any))
          (info := (vl-skip-through-endmodule))
          (return info))
        ;; Now we're at endmodule
        (end := (vl-match))
        (unless (and (vl-is-token? :vl-colon)
                     (not (eq (vl-loadconfig->edition config) :verilog-2005)))
          (return (make-vl-endinfo :name nil
                                   :loc (vl-token->loc end))))
        (:= (vl-match))
        (id := (vl-match-token :vl-idtoken))
        (return (make-vl-endinfo :name (vl-idtoken->name id)
                                 :loc (vl-token->loc id)))))


(define vl-make-module-with-parse-error ((name stringp)
                                         (minloc vl-location-p)
                                         (maxloc vl-location-p)
                                         (err)
                                         (tokens vl-tokenlist-p))
  :returns (mod vl-module-p)
  (b* (;; We expect that ERR should be an object suitable for cw-obj, i.e.,
       ;; each should be a cons of a string onto some arguments.  But if this
       ;; is not the case, we handle it here by just making a generic error.
       ((mv msg args)
        (if (and (consp err)
                 (stringp (car err)))
            (mv (car err) (list-fix (cdr err)))
          (mv "Generic error message for modules with parse errors. ~% ~
               Details: ~x0.~%" (list err))))

       (warn1 (make-vl-warning :type :vl-parse-error
                               :msg msg
                               :args args
                               :fatalp t
                               :fn 'vl-make-module-with-parse-error))

       ;; We also generate a second error message to show the remaining part of
       ;; the token stream in each case:
       (warn2 (make-vl-warning :type :vl-parse-error
                               :msg "[[ Remaining ]]: ~s0 ~s1.~%"
                               :args (list (vl-tokenlist->string-with-spaces
                                            (take (min 4 (len tokens))
                                                  (redundant-list-fix tokens)))
                                           (if (> (len tokens) 4) "..." ""))
                               :fatalp t
                               :fn 'vl-make-module-with-parse-error)))

    (make-vl-module :name name
                    :origname name
                    :minloc minloc
                    :maxloc maxloc
                    :warnings (list warn1 warn2))))


(defparser vl-parse-module-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-module-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (kwd := (vl-match-some-token '(:vl-kwd-module :vl-kwd-macromodule)))
        (id  := (vl-match-token :vl-idtoken))
        (return-raw
         (b* (((mv err mod new-tokens &)
               ;; We ignore the warnings because it traps them and associates
               ;; them with the module, anyway.
               (vl-parse-module-main atts kwd id))
              ((unless err)
               ;; Good deal, got the module successfully.
               (mv err mod new-tokens warnings))

              ;; We failed to parse a module but we are going to try to be
              ;; somewhat fault tolerant and "recover" from the error.  The
              ;; general idea is that we should advance until "endmodule."
              ((mv recover-err endinfo recover-tokens recover-warnings)
               (vl-skip-through-endmodule))
              ((when recover-err)
               ;; Failed to even find endmodule, abandon recovery effort.
               (mv err mod new-tokens warnings))

              ;; In the Verilog-2005 days, we could just look for endmodule.
              ;; But now we have to look for endmodule : foo, too.  If the
              ;; name doesn't line up, we'll abandon our recovery effort.
              ((when (and (vl-endinfo->name endinfo)
                          (not (equal (vl-idtoken->name id)
                                      (vl-endinfo->name endinfo)))))
               (mv err mod new-tokens warnings))

              ;; Else, we found endmodule and, if there's a name, it seems
              ;; to line up, so it seems okay to keep going.
              (phony-module
               (vl-make-module-with-parse-error (vl-idtoken->name id)
                                                (vl-token->loc kwd)
                                                (vl-endinfo->loc endinfo)
                                                err new-tokens)))
           ;; Subtle: we act like there's no error, because we're
           ;; recovering from it.  Get it?
           (mv nil phony-module recover-tokens recover-warnings)))))

