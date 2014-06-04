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
(include-book "modules")
(include-book "error")
(local (include-book "../../util/arithmetic"))

(defxdoc parser
  :parents (loader)
  :short "A parser for a subset of Verilog and SystemVerilog."

  :long "<h3>Introduction</h3>

<p>Our parser is responsible for processing a list of @(see tokens) into our
internal representation of Verilog @(see syntax).  Typically these tokens are
produced by the @(see lexer).  Note that before parsing begins, any whitespace
or comment tokens should be removed from the token list; see for instance @(see
vl-kill-whitespace-and-comments).</p>

<p>We use essentially a manual recursive-descent style parser.  Having the
entire token stream available gives us arbitrary lookahead, and we occasionally
make use of backtracking.</p>

<h3>Scope</h3>

<p>Verilog and SystemVerilog are huge languages, and we can parse only a subset
of these languages.</p>

<p>We can currently support most of the constructs in the Verilog 1364-2005
standard.  Notably, we do not yet support user-defined primitives, generate
statements, specify blocks, specparams, and genvars.  In some cases, the parser
will just skip over unrecognized constructs (adding @(see warnings) when it
does so.)  Depending on what you are doing, this behavior may be actually
appropriate, e.g., skipping specify blocks may be okay if you aren't trying to
deal with low-level timing issues.</p>

<p>We are beginning to work toward supporting SystemVerilog based on the
1800-2012 standard.  But this is preliminary work and you should not yet expect
VL to correctly handle any interesting fragment of SystemVerilog.</p>")

; -----------------------------------------------------------------------------
;
;                           User-Defined Primitives
;
; -----------------------------------------------------------------------------

; BOZO this is really not implemented.  We basically just read until
; endprimitive, throwing away any tokens we encounter until then.

; Verilog-2005 Syntax:
;
; udp_declaration ::=
;
;    {attribute_instance} 'primitive' udp_identifier '(' udp_port_list ')' ';'
;       udp_port_declaration { udp_port_declaration }
;       udp_body
;       'endprimitive'
;
;    {attribute_instance} 'primitive' udp_identifier '(' udp_declaration_port_list ')' ';'
;       udp_body
;       'endprimitive'
;
;
; SystemVerilog-2012 Syntax:
;
;   -- There is a bit more to it, but minimally it adds [ ':' identifier ] after
;      the endprimitive keyword.

; If we're dealing with SystemVerilog-2012, then the endprimitive can be
; followed by the name of the primitive, e,g,:
;
;   primitive foo
;     ...
;   endprimitive : foo
;
; The ending name must match or it's an error, see "Block Names", Section 9.3.4
; of the SystemVerilog-2012 spec.
;
; If we're only doing Verilog-2005, then ending name parts aren't allowed.

(defaggregate vl-endinfo
  :legiblep nil
  ((name maybe-stringp :rule-classes :type-prescription)
   (loc  vl-location-p)))

(defparser vl-parse-udp-declaration-aux ()
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (unless (vl-is-token? :vl-kwd-endprimitive)
          (:s= (vl-match-any))
          (info := (vl-parse-udp-declaration-aux))
          (return info))
        (end := (vl-match))
        (when (or (eq (vl-loadconfig->edition config) :verilog-2005)
                  (not (vl-is-token? :vl-colon)))
          (return (make-vl-endinfo :name nil
                                   :loc (vl-token->loc end))))
        (:= (vl-match))
        (id := (vl-match-token :vl-idtoken))
        (return (make-vl-endinfo :name (vl-idtoken->name id)
                                 :loc (vl-token->loc id)))))

(defparser vl-parse-udp-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-udp-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-kwd-primitive))
        (name := (vl-match-token :vl-idtoken))
        (endinfo := (vl-parse-udp-declaration-aux))
        (when (and (vl-endinfo->name endinfo)
                   (not (equal (vl-idtoken->name name)
                               (vl-endinfo->name endinfo))))
          (return-raw
           (vl-parse-error
            (cat "Mismatched primitive/endprimitive pair: expected "
                 (vl-idtoken->name name) " but found "
                 (vl-endinfo->name endinfo)))))
        (return
         (make-vl-udp
          :name (vl-idtoken->name name)
          :atts atts
          :warnings (fatal :type :vl-warn-primitive
                           :msg "User-defined primitives are not supported."
                           :args nil
                           :acc nil)
          :minloc (vl-token->loc name)
          :maxloc (vl-endinfo->loc endinfo)))))



; -----------------------------------------------------------------------------
;
;                               Configurations
;
; -----------------------------------------------------------------------------
;
; Syntax in Verilog-2005:
;
; config_declaration ::=
;    'config' identifier ';'
;       design_statement
;       { config_rule_statement }
;    'endconfig'
;
; Syntax in SystemVerilog-2012:
;
; config_declaration ::=
;    'config' identifier ';'
;       { local_parameter_declaration ';' }
;       design_statement
;       { config_rule_statement }
;    'endconfig' [':' identifier]

(defparser vl-parse-config-declaration-aux ()
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (unless (vl-is-token? :vl-kwd-endconfig)
          (:s= (vl-match-any))
          (info := (vl-parse-config-declaration-aux))
          (return info))
        (end := (vl-match))
        (when (or (eq (vl-loadconfig->edition config) :verilog-2005)
                  (not (vl-is-token? :vl-colon)))
          (return (make-vl-endinfo :name nil
                                   :loc (vl-token->loc end))))
        (:= (vl-match))
        (id := (vl-match-token :vl-idtoken))
        (return (make-vl-endinfo :name (vl-idtoken->name id)
                                 :loc (vl-token->loc id)))))

(defparser vl-parse-config-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-config-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-kwd-config))
        (name := (vl-match-token :vl-idtoken))
        (endinfo := (vl-parse-config-declaration-aux))
        (when (and (vl-endinfo->name endinfo)
                   (not (equal (vl-idtoken->name name)
                               (vl-endinfo->name endinfo))))
          (return-raw
           (vl-parse-error
            (cat "Mismatched config/endconfig pair: expected "
                 (vl-idtoken->name name) " but found "
                 (vl-endinfo->name endinfo)))))
        (return
         (make-vl-config
          :name (vl-idtoken->name name)
          :atts atts
          :warnings (fatal :type :vl-warn-config
                           :msg "Configs are not supported."
                           :args nil
                           :acc nil)
          :minloc (vl-token->loc name)
          :maxloc (vl-endinfo->loc endinfo)))))



; -----------------------------------------------------------------------------
;
;                                Packages
;
; -----------------------------------------------------------------------------

; BOZO we don't really implement packages yet.

(defparser vl-parse-package-declaration-aux ()
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; Similar to UDPs, but we don't have to check for Verilog-2005 because
  ;; packages only exist in SystemVerilog-2012.
  (seqw tokens warnings
        (unless (vl-is-token? :vl-kwd-endpackage)
          (:s= (vl-match-any))
          (info := (vl-parse-package-declaration-aux))
          (return info))
        (end := (vl-match))
        (unless (vl-is-token? :vl-colon)
          (return (make-vl-endinfo :name nil
                                   :loc (vl-token->loc end))))
        (:= (vl-match))
        (id := (vl-match-token :vl-idtoken))
        (return (make-vl-endinfo :name (vl-idtoken->name id)
                                 :loc (vl-token->loc id)))))

(defparser vl-parse-package-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-package-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-kwd-package))
        (name := (vl-match-token :vl-idtoken))
        (endinfo := (vl-parse-package-declaration-aux))
        (when (and (vl-endinfo->name endinfo)
                   (not (equal (vl-idtoken->name name)
                               (vl-endinfo->name endinfo))))
          (return-raw
           (vl-parse-error
            (cat "Mismatched package/endpackage pair: expected "
                 (vl-idtoken->name name) " but found "
                 (vl-endinfo->name endinfo)))))
        (return
         (make-vl-package
          :name (vl-idtoken->name name)
          :atts atts
          :warnings (fatal :type :vl-warn-package
                           :msg "Packages are not supported."
                           :args nil
                           :acc nil)
          :minloc (vl-token->loc name)
          :maxloc (vl-endinfo->loc endinfo)))))



; -----------------------------------------------------------------------------
;
;                              Interfaces
;
; -----------------------------------------------------------------------------

(defparser vl-parse-interface-declaration-aux ()
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; Similar to UDPs, but we don't have to check for Verilog-2005 because
  ;; interfaces only exist in SystemVerilog-2012.
  (seqw tokens warnings
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
  (seqw tokens warnings
        (:= (vl-match-token :vl-kwd-interface))
        (name := (vl-match-token :vl-idtoken))
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



; -----------------------------------------------------------------------------
;
;                              Programs
;
; -----------------------------------------------------------------------------

(defparser vl-parse-program-declaration-aux ()
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; Similar to UDPs, but we don't have to check for Verilog-2005 because
  ;; programs only exist in SystemVerilog-2012.
  (seqw tokens warnings
        (unless (vl-is-token? :vl-kwd-endprogram)
          (:s= (vl-match-any))
          (info := (vl-parse-program-declaration-aux))
          (return info))
        (end := (vl-match))
        (unless (vl-is-token? :vl-colon)
          (return (make-vl-endinfo :name nil
                                   :loc (vl-token->loc end))))
        (:= (vl-match))
        (id := (vl-match-token :vl-idtoken))
        (return (make-vl-endinfo :name (vl-idtoken->name id)
                                 :loc (vl-token->loc id)))))

(defparser vl-parse-program-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-program-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-kwd-program))
        (name := (vl-match-token :vl-idtoken))
        (endinfo := (vl-parse-program-declaration-aux))
        (when (and (vl-endinfo->name endinfo)
                   (not (equal (vl-idtoken->name name)
                               (vl-endinfo->name endinfo))))
          (return-raw
           (vl-parse-error
            (cat "Mismatched program/endprogram pair: expected "
                 (vl-idtoken->name name) " but found "
                 (vl-endinfo->name endinfo)))))
        (return
         (make-vl-program
          :name (vl-idtoken->name name)
          :atts atts
          :warnings (fatal :type :vl-warn-program
                           :msg "Programs are not supported."
                           :args nil
                           :acc nil)
          :minloc (vl-token->loc name)
          :maxloc (vl-endinfo->loc endinfo)))))



; -----------------------------------------------------------------------------
;
;                              Source Text
;
; -----------------------------------------------------------------------------

; Verilog-2005:
;
; description ::=
;    module_declaration
;  | udp_declaration
;  | config_declaration
;
; SystemVerilog-2012 adds:
;
;  | interface_declaration
;  | program_declaration
;  | package_declaration
;  | {attribute_instance} package_item         <-- not supported yet
;  | {attribute_instance} bind_directive       <-- not supported yet

(defparser vl-parse-description ()
  :result (vl-description-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (atts := (vl-parse-0+-attribute-instances))
        (when (vl-is-token? :vl-kwd-config)
          (cfg := (vl-parse-config-declaration atts))
          (return cfg))
        (when (vl-is-token? :vl-kwd-primitive)
          (udp := (vl-parse-udp-declaration atts))
          (return udp))
        (when (vl-is-some-token? '(:vl-kwd-module :vl-kwd-macromodule))
          (mod := (vl-parse-module-declaration atts))
          (return mod))
        (when (eq (vl-loadconfig->edition config) :verilog-2005)
          ;; Other things aren't supported
          (return-raw
           (vl-parse-error "Expected a module, primitive, or config.")))
        (when (vl-is-token? :vl-kwd-interface)
          (interface := (vl-parse-interface-declaration atts))
          (return interface))
        (when (vl-is-token? :vl-kwd-program)
          (program := (vl-parse-program-declaration atts))
          (return program))
        (when (vl-is-token? :vl-kwd-package)
          (package := (vl-parse-package-declaration atts))
          (return package))
        (return-raw
         (vl-parse-error "Unsupported top-level construct?"))))


; Verilog-2005:
; source_text ::= { description };
;
; SystemVerilog-2012 adds:
; source_text ::= [timeunits_declaration] { description }
;
; But we don't support this timeunit declaration yet.

(defparser vl-parse-source-text ()
  :result (vl-descriptionlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seqw tokens warnings
        (when (atom tokens)
          (return nil))
        (first := (vl-parse-description))
        (rest := (vl-parse-source-text))
        (return (cons first rest))))


(define vl-parse
  :parents (parser)
  :short "Top level parsing function."
  ((tokens   vl-tokenlist-p)
   (warnings vl-warninglist-p)
   (config   vl-loadconfig-p))
  :returns
  (mv (successp)
      (items    vl-descriptionlist-p :hyp :fguard)
      (warnings vl-warninglist-p))
  (b* (((mv err val tokens warnings)
        (vl-parse-source-text))
       ((when err)
        (vl-report-parse-error err tokens)
        (mv nil nil warnings)))
    (mv t val warnings)))
