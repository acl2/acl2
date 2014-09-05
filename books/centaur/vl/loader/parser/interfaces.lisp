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

(define vl-interface-warn-unsupported ((c vl-genelement-collection-p)
                                       (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (b* (((vl-genelement-collection c)))
    (if (or* c.assigns
             c.fundecls
             c.taskdecls
             c.modinsts
             c.gateinsts
             c.alwayss
             c.initials
             c.ports)
        (warn :type :vl-unsupported-interface-item
              :msg "Unsupported interface items: ~&0"
              :args (list (append (and* c.assigns '("continuous assignments"))
                                  (and* c.fundecls '("functions"))
                                  (and* c.taskdecls '("tasks"))
                                  (and* c.modinsts '("module instances"))
                                  (and* c.gateinsts '("gate instances"))
                                  (and* c.alwayss '("always blocks"))
                                  (and* c.initials '("initial blocks"))
                                  (and* c.ports    '("ports")))))
      (vl-warninglist-fix warnings))))

(define vl-make-interface-by-items

; Our various parsing functions for declarations, assignments, etc., return all
; kinds of different interface items.  We initially get all of these different
; kinds of items as a big list.  Then, here, we sort it into buckets by type,
; and turn it into a interface.

  ((name     stringp               "Name of the interface.")
   (params   vl-paramdecllist-p    "Parameters declarations from the #(...) list, if any.")
   (ports    vl-portlist-p         "Ports like (o, a, b).")
   (items    vl-genelementlist-p   "Items from the interface's body, i.e., until endinterface.")
   (atts     vl-atts-p)
   (minloc   vl-location-p)
   (maxloc   vl-location-p)
   (warnings vl-warninglist-p))
  :returns (mod vl-interface-p)
  (b* (((mv items warnings) (vl-make-implicit-wires
                             (append-without-guard (vl-genitemlist->genelements params)
                                                   items)
                             warnings))
       ((vl-genelement-collection c) (vl-sort-genelements items))
       ((mv warnings c.portdecls c.vardecls)
        (vl-portdecl-sign c.portdecls c.vardecls warnings))
       (warnings (vl-interface-warn-unsupported c warnings)))
    ;; BOZO: Warn about other bad elements in c?
    (make-vl-interface :name       name
                       :ports      ports
                       :portdecls  c.portdecls
                       :vardecls   c.vardecls
                       :paramdecls c.paramdecls
                       :modports   c.modports
                       :generates  c.generates
                       :atts       atts
                       :minloc     minloc
                       :maxloc     maxloc
                       :warnings   warnings
                       :origname   name
                       :comments   nil
                       )))


(defparser vl-parse-interface-declaration-ansi (atts)
  :guard (vl-atts-p atts)
  (seq tokstream
       (:= (vl-maybe-parse-lifetime)) ;; ignore
       (name := (vl-match-token :vl-idtoken))
       (:= (vl-parse-0+-package-import-declarations)) ;; ignore
       (when (vl-is-token? :vl-pound)
          (params := (vl-parse-module-parameter-port-list)))
       (when (vl-is-token? :vl-lparen)
         ((portdecls . netdecls) := (vl-parse-list-of-port-declarations)))
       (:= (vl-match-token :vl-semi))
       (items := (vl-parse-0+-genelements))
       (endkwd := (vl-match-token :vl-kwd-endinterface))

       (when (and (vl-is-token? :vl-colon)
                  (not (eq (vl-loadconfig->edition config) :verilog-2005)))
         (:= (vl-match))
         (endname := (vl-match-token :vl-idtoken)))
       (when (and endname
                  (not (equal (vl-idtoken->name name) (vl-idtoken->name endname))))
         (return-raw
          (vl-parse-error "Mismatched interface/endinterface pair")))

       (return-raw
        (b* ((item-portdecls (vl-genelementlist->portdecls items))
             ((when item-portdecls)
              (vl-parse-error "ANSI module contained internal portdecls"))
             (module (vl-make-module-by-items (vl-idtoken->name id)
                                              params
                                              (vl-ports-from-portdecls portdecls)
                                              (append (vl-genitemlist->genelements netdecls)
                                                      (vl-genitemlist->genelements portdecls)
                                                      items)
                                              atts
                                              (vl-token->loc module_keyword)
                                              (vl-token->loc endkwd)
                                              (vl-parsestate->warnings (vl-tokstream->pstate)))))
          (mv nil module tokstream)))
       
       
       


;; NOTE: modports and other interface internals are not yet parsed by this function
(defparser vl-parse-interface-declaration-aux ()
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; Similar to UDPs, but we don't have to check for Verilog-2005 because
  ;; interfaces only exist in SystemVerilog-2012.
  (seq tokstream
        (unless (vl-is-token? :vl-kwd-endinterface)
          (:s= (vl-match-any))
          (info := (vl-parse-interface-declaration-aux))
          (return info))
        (end := (vl-match))
        (unless (vl-is-token? :vl-colon)
          (return (make-vl-endinfo :name nil
                                   :loc (vl-token->loc end))))
        (:= (vl-match))
        (id := (vl-match-token :vl-idtoken))
        (return (make-vl-endinfo :name (vl-idtoken->name id)
                                 :loc (vl-token->loc id)))))

(defparser vl-parse-interface-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-interface-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-kwd-interface))
        (name := (vl-match-token :vl-idtoken))
        (ports := 
        (endinfo := (vl-parse-interface-declaration-aux))
        (when (and (vl-endinfo->name endinfo)
                   (not (equal (vl-idtoken->name name)
                               (vl-endinfo->name endinfo))))
          (return-raw
           (vl-parse-error
            (cat "Mismatched interface/endinterface pair: expected "
                 (vl-idtoken->name name) " but found "
                 (vl-endinfo->name endinfo)))))
        (return
         (make-vl-interface
          :name (vl-idtoken->name name)
          :atts atts
          :warnings (fatal :type :vl-warn-interface
                           :msg "Interfaces are not supported."
                           :args nil
                           :acc nil)
          :minloc (vl-token->loc name)
          :maxloc (vl-endinfo->loc endinfo)))))
