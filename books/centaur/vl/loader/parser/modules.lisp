; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "ports")      ;; vl-portdecllist-p, vl-portlist-p
(include-book "elements")
(include-book "timeunits")
(include-book "../../mlib/blocks")
(local (include-book "../../util/arithmetic"))

(define vl-make-module-by-items

; Our various parsing functions for declarations, assignments, etc., return all
; kinds of different module items.  We initially get all of these different
; kinds of items as a big list.  Then, here, we sort it into buckets by type,
; and turn it into a module.

  ((name     stringp               "Name of the module.")
   (imports  vl-importlist-p)
   (params   vl-paramdecllist-p    "Parameters declarations from the #(...) list, if any.")
   (ansi-ports vl-ansi-portdecllist-p "Temporary form of ANSI portdecls")
   (ports    vl-portlist-p         "Ports like (o, a, b).")
   (ansi-p   booleanp              "Was it parsed in the ANSI or non-ANSI style")
   (items    vl-genelementlist-p   "Items from the module's body, i.e., until endmodule.")
   (atts     vl-atts-p)
   (minloc   vl-location-p)
   (maxloc   vl-location-p)
   (warnings vl-warninglist-p))
  :returns (mod vl-module-p)
  (b* (;; (items (append-without-guard (vl-modelementlist->genelements params) items))
       (bad-item (vl-genelementlist-findbad items
                                            '(:vl-generate
                                              ;; :vl-port    -- not allowed, they were parsed separately
                                              :vl-portdecl
                                              :vl-assign
                                              :vl-alias
                                              :vl-vardecl
                                              :vl-paramdecl
                                              :vl-fundecl
                                              :vl-taskdecl
                                              :vl-modinst
                                              :vl-gateinst
                                              :vl-always
                                              :vl-initial
                                              :vl-final
                                              :vl-typedef
                                              :vl-import
                                              ;; :vl-fwdtypedef -- doesn't seem like these should be ok
                                              ;; :vl-modport    -- definitely not ok
                                              :vl-genvar
                                              :vl-assertion
                                              :vl-cassertion
                                              :vl-property
                                              :vl-sequence
                                              :vl-clkdecl
                                              :vl-gclkdecl
                                              :vl-defaultdisable
                                              :vl-dpiimport
                                              :vl-dpiexport
                                              :vl-bind
                                              :vl-class
                                              :vl-covergroup
                                              :vl-elabtask
                                              )))
       (warnings
        (if (not bad-item)
            warnings
          (fatal :type :vl-bad-module-item
                 :msg "~a0: a module may not contain a ~s1."
                 :args (list bad-item (vl-genelement->short-kind-string bad-item)))))

       ((vl-genblob c) (vl-sort-genelements items))
       ;; ((mv warnings c.portdecls c.vardecls)
       ;;  (vl-portdecl-sign c.portdecls c.vardecls warnings))
       )
    (make-vl-module :name        name
                    :params      params ;; Is this even right?
                    :ports       ports
                    :portdecls   c.portdecls
                    :assigns     c.assigns
                    :aliases     c.aliases
                    :vardecls    c.vardecls
                    :paramdecls  (append-without-guard params c.paramdecls)
                    :fundecls    c.fundecls
                    :taskdecls   c.taskdecls
                    :modinsts    c.modinsts
                    :gateinsts   c.gateinsts
                    :alwayses    c.alwayses
                    :initials    c.initials
                    :finals      c.finals
                    :generates   c.generates
                    :genvars     c.genvars
                    :imports     (append-without-guard imports c.imports)
                    :typedefs    c.typedefs
                    :properties  c.properties
                    :sequences   c.sequences
                    :clkdecls    c.clkdecls
                    :gclkdecls   c.gclkdecls
                    :defaultdisables c.defaultdisables
                    :assertions  c.assertions
                    :cassertions c.cassertions
                    :dpiimports  c.dpiimports
                    :dpiexports  c.dpiexports
                    :binds       c.binds
                    :classes     c.classes
                    :covergroups c.covergroups
                    :elabtasks   c.elabtasks
                    :atts        atts
                    :minloc      minloc
                    :maxloc      maxloc
                    :warnings    warnings
                    :origname    name
                    :comments    nil
                    :parse-temps (make-vl-parse-temps
                                  :ansi-p ansi-p
                                  :imports imports
                                  :ansi-ports ansi-ports
                                  :paramports params
                                  :loaditems items)
                    )))


;                                    MODULES
;
; Grammar rules from Verilog-2005:
;
; module_declaration ::=
;    {attribute_instance} module_keyword identifier [module_parameter_port_list]
;        list_of_ports ';' {module_item}
;        'endmodule'
;  | {attribute_instance} module_keyword identifier [module_parameter_port_list]
;        [list_of_port_declarations] ';' {non_port_module_item}
;        'endmodule'
;
; module_keyword ::= 'module' | 'macromodule'

(defparser vl-parse-module-declaration-core (atts module_keyword id)
  :guard (and (vl-atts-p atts)
              (vl-token-p module_keyword)
              (vl-idtoken-p id))
  :result (vl-module-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong

; We handle modules of either ANSI or NON-ANSI variants.
; But we assume that:
;
;   (1) the attributes, "module" or "macromodule", and the name of this module
;       have already been read, and
;
;   (2) the warnings we're given are initially NIL, so all warnings we come up
;       with until the end of the module 'belong' to this module.

  (seq tokstream
       (imports  := (vl-parse-0+-package-import-declarations))
       (params   := (vl-maybe-parse-parameter-port-list))
       (portinfo := (vl-parse-module-port-list-top))
       (:= (vl-match-token :vl-semi))
       ((timeunit . timeprec) := (vl-parse-optional-timeunits-declaration))
       (items := (vl-parse-genelements-until :vl-kwd-endmodule))
       (endkwd := (vl-match-token :vl-kwd-endmodule))
       (:= (vl-parse-endblock-name (vl-idtoken->name id) "module/endmodule"))
       (return-raw
        (b* ((name   (vl-idtoken->name id))
             (minloc (vl-token->loc module_keyword))
             (maxloc (vl-token->loc endkwd))
             (warnings (vl-parsestate->warnings (vl-tokstream->pstate)))
             ((mv ansi-p ansi-portdecls ports)
              (vl-parsed-ports-case portinfo
                :ansi (mv t portinfo.decls nil)
                :nonansi (mv nil nil portinfo.ports)))
             ((when (and ansi-p
                         (vl-genelementlist->portdecls items))) ;; User's fault
              (vl-parse-error "ANSI module cannot have internal port declarations."))
             (module (vl-make-module-by-items name imports params ansi-portdecls ports ansi-p items
                                              atts minloc maxloc warnings))
             (module (if (or timeunit timeprec)
                         (change-vl-module module
                                           :timeunit timeunit
                                           :timeprecision timeprec)
                       module)))
          (mv nil module tokstream)))))

(defparser vl-parse-module-main (atts module_keyword id)
  :guard (and (vl-atts-p atts)
              (vl-token-p module_keyword)
              (vl-idtoken-p id))
  :result (vl-module-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; Main function to try to parse the guts of a module.  A weird twist is that
  ;; we want to associate all warnings encountered during the parsing of a
  ;; module with that module as it is created, and NOT return them in the
  ;; global list of warnings.  Because of this, we use a fresh warnings
  ;; accumulator here.
  (b* ((orig-warnings (vl-parsestate->warnings (vl-tokstream->pstate)))
       (tokstream     (vl-tokstream-update-pstate
                       (change-vl-parsestate (vl-tokstream->pstate) :warnings nil)))
       ((mv err1 mod tokstream)
        (vl-parse-module-declaration-core atts module_keyword id))
       (tokstream (vl-tokstream-update-pstate
                   (change-vl-parsestate (vl-tokstream->pstate) :warnings orig-warnings))))
    (mv err1 mod tokstream)))

(defparser vl-skip-through-endmodule ()
  ;; This is a special function which is used to provide more fault-tolerance
  ;; in module parsing.  Historically, we just advanced the token stream until
  ;; :vl-kwd-endmodule was encountered.  For SystemVerilog, we also capture the
  ;; "endmodule : foo" part and return a proper vl-endinfo-p.
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
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

(define vl-make-module-with-parse-error ((name   stringp)
                                         (minloc vl-location-p)
                                         (maxloc vl-location-p)
                                         (err    vl-warning-p)
                                         (tokens vl-tokenlist-p))
  :returns (mod vl-module-p)
  (b* (;; We also generate a second error message.
       ;;  - This lets us always show the remaining part of the token stream
       ;;    in each case.
       ;;  - It ensures that any module with a parse error always, absolutely,
       ;;    certainly has a fatal warning, even if somehow the real warning
       ;;    isn't marked as fatal.
       (warn2 (make-vl-warning :type :vl-parse-error
                               :msg "[[ Remaining ]]: ~s0 ~s1.~%"
                               :args (list (vl-tokenlist->string-with-spaces
                                            (take (min 4 (len tokens))
                                                  (list-fix tokens)))
                                           (if (> (len tokens) 4) "..." ""))
                               :fatalp t
                               :fn __function__)))
    (make-vl-module :name name
                    :origname name
                    :minloc minloc
                    :maxloc maxloc
                    :warnings (list err warn2))))

(defparser vl-parse-module-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-module-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (kwd := (vl-match-some-token '(:vl-kwd-module :vl-kwd-macromodule)))
        (id  := (vl-match-token :vl-idtoken))
        (return-raw
         (b* ((backup (vl-tokstream-save))
              ((mv err mod tokstream)
               ;; We ignore the warnings because it traps them and associates
               ;; them with the module, anyway.
               (vl-parse-module-main atts kwd id))
              ((unless err)
               ;; Good deal, got the module successfully.
               (mv err mod tokstream))
              (new-tokens (vl-tokstream->tokens))
              (tokstream (vl-tokstream-restore backup))
              ;; We failed to parse a module but we are going to try to be
              ;; somewhat fault tolerant and "recover" from the error.  The
              ;; general idea is that we should advance until "endmodule."
              ((mv recover-err endinfo tokstream)
               (vl-skip-through-endmodule))
              ((when recover-err)
               ;; Failed to even find endmodule, abandon recovery effort.
               (mv err mod tokstream))

              ;; In the Verilog-2005 days, we could just look for endmodule.
              ;; But now we have to look for endmodule : foo, too.  If the
              ;; name doesn't line up, we'll abandon our recovery effort.
              ((when (and (vl-endinfo->name endinfo)
                          (not (equal (vl-idtoken->name id)
                                      (vl-endinfo->name endinfo)))))
               (mv err mod tokstream))

              ;; Else, we found endmodule and, if there's a name, it seems
              ;; to line up, so it seems okay to keep going.
              (phony-module
               (vl-make-module-with-parse-error (vl-idtoken->name id)
                                                (vl-token->loc kwd)
                                                (vl-endinfo->loc endinfo)
                                                err new-tokens)))
           ;; Subtle: we act like there's no error, because we're
           ;; recovering from it.  Get it?
           (mv nil phony-module tokstream)))))

