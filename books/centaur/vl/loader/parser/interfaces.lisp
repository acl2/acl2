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
(include-book "elements")
(include-book "imports")
(include-book "../../mlib/blocks")
(local (include-book "../../util/arithmetic"))


#||

interface_declaration ::=
interface_nonansi_header [ timeunits_declaration ] { interface_item }
endinterface [ : interface_identifier ]
| interface_ansi_header [ timeunits_declaration ] { non_port_interface_item }
endinterface [ : interface_identifier ]
| { attribute_instance } interface interface_identifier ( .* ) ;
[ timeunits_declaration ] { interface_item }
endinterface [ : interface_identifier ]
| extern interface_nonansi_header
| extern interface_ansi_header

interface_nonansi_header ::=
{ attribute_instance } interface [ lifetime ] interface_identifier
{ package_import_declaration } [ parameter_port_list ] list_of_ports ;

interface_ansi_header ::=
{attribute_instance } interface [ lifetime ] interface_identifier
{ package_import_declaration }1 [ parameter_port_list ] [ list_of_port_declarations ] ;

||#

(define vl-make-interface-by-items

; Our various parsing functions for declarations, assignments, etc., return all
; kinds of different interface items.  We initially get all of these different
; kinds of items as a big list.  Then, here, we sort it into buckets by type,
; and turn it into a interface.

  ((name     stringp               "Name of the interface.")
   (params   vl-paramdecllist-p    "Parameters declarations from the #(...) list, if any.")
   (ansi-ports vl-ansi-portdecllist-p "Temporary ANSI portdecl structures")
   (ports    vl-portlist-p         "Non-ANSI Ports like (o, a, b).")
   (ansi-p   booleanp              "Ansi or non-ANSI ports?")
   (items    vl-genelementlist-p   "Items from the interface's body, i.e., until endinterface.")
   (atts     vl-atts-p)
   (minloc   vl-location-p)
   (maxloc   vl-location-p)
   (warnings vl-warninglist-p))
  :returns (mod vl-interface-p)
  (b* ((items (append-without-guard (vl-modelementlist->genelements params)
                                    items))

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
                                              ;; :vl-gateinst -- don't think these are allowed
                                              :vl-always
                                              :vl-initial
                                              :vl-final
                                              :vl-typedef
                                              :vl-import
                                              ;; :vl-fwdtypedef -- bozo? not yet
                                              :vl-modport
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
                                              :vl-letdecl
                                              ;; covergroups?  not sure -- if you add them, add them to the parsetree,
                                              ;; here, below, and remove them from the excluded fields in
                                              ;; *vl-interface/genblob-fields* in mlib/blocks.lisp
                                              :vl-elabtask
                                              )))
       (warnings
        (if (not bad-item)
            warnings
          (fatal :type :vl-bad-interface-item
                 :msg "~a0: an interface may not contain a ~s1."
                 :args (list bad-item (vl-genelement->short-kind-string bad-item)))))

       ((vl-genblob c) (vl-sort-genelements items)))

     (make-vl-interface :name        name
                        :imports     c.imports
                        :ports       ports
                        :portdecls   c.portdecls
                        :modports    c.modports
                        :vardecls    c.vardecls
                        :paramdecls  c.paramdecls
                        :fundecls    c.fundecls
                        :taskdecls   c.taskdecls
                        :typedefs    c.typedefs
                        :dpiimports  c.dpiimports
                        :dpiexports  c.dpiexports
                        :properties  c.properties
                        :sequences   c.sequences
                        :clkdecls    c.clkdecls
                        :gclkdecls   c.gclkdecls
                        :defaultdisables c.defaultdisables
                        :binds       c.binds
                        :classes     c.classes
                        :elabtasks   c.elabtasks
                        :modinsts    c.modinsts
                        :assigns     c.assigns
                        :assertions  c.assertions
                        :cassertions c.cassertions
                        :alwayses    c.alwayses
                        :initials    c.initials
                        :finals      c.finals
                        :generates   c.generates
                        :genvars     c.genvars
                        :atts        atts
                        :minloc      minloc
                        :maxloc      maxloc
                        :warnings    warnings
                        :origname    name
                        :parse-temps (make-vl-parse-temps
                                      :ansi-p ansi-p
                                      :loaditems items
                                      :ansi-ports ansi-ports)
                        :comments    nil)))

(defparser vl-parse-interface-declaration-core (atts interface-kwd name)
  :guard (and (vl-atts-p atts)
              (vl-token-p interface-kwd)
              (vl-idtoken-p name))
  :result (vl-interface-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (imports  := (vl-parse-0+-package-import-declarations)) ;; ignore
       (params   := (vl-maybe-parse-parameter-port-list))
       (portinfo := (vl-parse-module-port-list-top))
       (:= (vl-match-token :vl-semi))
       (items := (vl-parse-genelements-until :vl-kwd-endinterface))
       (endkwd := (vl-match-token :vl-kwd-endinterface))
       (:= (vl-parse-endblock-name (vl-idtoken->name name)
                                   "interface/endinterface"))
       (return-raw
        (b* ((name     (vl-idtoken->name name))
             (minloc   (vl-token->loc interface-kwd))
             (maxloc   (vl-token->loc endkwd))
             (warnings (vl-parsestate->warnings (vl-tokstream->pstate)))
             ((mv ansi-p ansi-portdecls ports)
              (vl-parsed-ports-case portinfo
                :ansi (mv t portinfo.decls nil)
                :nonansi (mv nil nil portinfo.ports)))
             ((when (and ansi-p (vl-genelementlist->portdecls items))) ;; User's fault
              (vl-parse-error "ANSI interface cannot have internal port declarations."))
             (items (append (vl-modelementlist->genelements imports)
                            items))
             (interface (vl-make-interface-by-items name params ansi-portdecls ports ansi-p items
                                              atts minloc maxloc warnings)))
          (mv nil interface tokstream)))))

(defparser vl-parse-interface-main (atts interface-kwd name)
  :guard (and (vl-atts-p atts)
              (vl-token-p interface-kwd)
              (vl-idtoken-p name))
  :result (vl-interface-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; This is all just like vl-parse-module-main.
  (b* ((orig-warnings (vl-parsestate->warnings (vl-tokstream->pstate)))
       (tokstream (vl-tokstream-update-pstate
                   (change-vl-parsestate (vl-tokstream->pstate) :warnings nil)))
       ((mv err1 res tokstream)
        (vl-parse-interface-declaration-core atts interface-kwd name))
       (tokstream (vl-tokstream-update-pstate
                   (change-vl-parsestate (vl-tokstream->pstate) :warnings orig-warnings))))
    (mv err1 res tokstream)))

(defparser vl-skip-through-endinterface ()
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong

; This is a special function which is used to provide more fault-tolerance in
; interface parsing.  Historically, we just advanced the token stream until
; :vl-kwd-endinterface was encountered.  For SystemVerilog, we also capture the
; "endinterface : foo" part and return a proper vl-endinfo-p.

  (seq tokstream
       (unless (vl-is-token? :vl-kwd-endinterface)
         (:s= (vl-match-any))
         (info := (vl-skip-through-endinterface))
         (return info))
       ;; Now we're at endinterface
       (end := (vl-match))
       (unless (and (vl-is-token? :vl-colon)
                    (not (eq (vl-loadconfig->edition config) :verilog-2005)))
         (return (make-vl-endinfo :name nil
                                  :loc (vl-token->loc end))))
       (:= (vl-match))
       (id := (vl-match-token :vl-idtoken))
       (return (make-vl-endinfo :name (vl-idtoken->name id)
                                :loc (vl-token->loc id)))))

(define vl-make-interface-with-parse-error ((name   stringp)
                                            (minloc vl-location-p)
                                            (maxloc vl-location-p)
                                            (err    vl-warning-p)
                                            (tokens vl-tokenlist-p))
  :returns (res vl-interface-p)
  (b* (;; Like vl-make-module-with-parse-error.
       (warn2 (make-vl-warning :type :vl-parse-error
                               :msg "[[ Remaining ]]: ~s0 ~s1.~%"
                               :args (list (vl-tokenlist->string-with-spaces
                                            (take (min 4 (len tokens))
                                                  (list-fix tokens)))
                                           (if (> (len tokens) 4) "..." ""))
                               :fatalp t
                               :fn __function__)))

    (make-vl-interface :name name
                       :origname name
                       :minloc minloc
                       :maxloc maxloc
                       :warnings (list err warn2))))

(defparser vl-parse-interface-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-interface-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (kwd := (vl-match-token :vl-kwd-interface))
       (id  := (vl-match-token :vl-idtoken))
       (return-raw
        (b* ((backup (vl-tokstream-save))
             ((mv err res tokstream)
              ;; We ignore the warnings because it traps them and associates
              ;; them with the interface, anyway.
              (vl-parse-interface-main atts kwd id))
             ((unless err)
              ;; Good deal, got the interface successfully.
              (mv err res tokstream))
             (new-tokens (vl-tokstream->tokens))
             (tokstream (vl-tokstream-restore backup))
             ;; We failed to parse a interface but we are going to try to be
             ;; somewhat fault tolerant and "recover" from the error.  The
             ;; general idea is that we should advance until "endinterface."
             ((mv recover-err endinfo tokstream)
              (vl-skip-through-endinterface))
             ((when recover-err)
              ;; Failed to even find endinterface, abandon recovery effort.
              (mv err res tokstream))

             ;; In the Verilog-2005 days, we could just look for endinterface.
             ;; But now we have to look for endinterface : foo, too.  If the
             ;; name doesn't line up, we'll abandon our recovery effort.
             ((when (and (vl-endinfo->name endinfo)
                         (not (equal (vl-idtoken->name id)
                                     (vl-endinfo->name endinfo)))))
              (mv err res tokstream))

             ;; Else, we found endinterface and, if there's a name, it seems
             ;; to line up, so it seems okay to keep going.
             (phony-interface
              (vl-make-interface-with-parse-error (vl-idtoken->name id)
                                                  (vl-token->loc kwd)
                                                  (vl-endinfo->loc endinfo)
                                                  err new-tokens)))
          ;; Subtle: we act like there's no error, because we're
          ;; recovering from it.  Get it?
          (mv nil phony-interface tokstream)))))
