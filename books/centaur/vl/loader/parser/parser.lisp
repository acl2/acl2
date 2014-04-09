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


(defund udp-p (x)
  (declare (ignore x))
  t)

(defparser vl-parse-udp-declaration-aux ()
  ;; BOZO this is really not implemented.  We just read until endprimitive,
  ;; throwing away any tokens we encounter until then.
  :result (udp-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-endprimitive)
          (:= (vl-match))
          (return nil))
        (:s= (vl-match-any))
        (:= (vl-parse-udp-declaration-aux))
        (return nil)))

(defparser vl-parse-udp-declaration (atts)
  ;; This :result is sloppy and won't be true if we implement udps, but
  ;; it lets vl-parse return a module list.
  :guard (vl-atts-p atts)
  :result (vl-modulelist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignorable atts))
  (if (atom tokens)
      (vl-parse-error "Unexpected EOF.")
    (seqw tokens warnings
          (:= (vl-parse-warning :vl-warn-primitive
                                (cat "User-defined primitive modules are not yet "
                                     "implemented.  We are just ignoring everything "
                                     "until 'endprimitive'.")))
          (:= (vl-parse-udp-declaration-aux))
          (return nil))))

(defparser vl-parse-config-declaration ()
  ;; This :result is sloppy and won't be true if we implement configs, but
  ;; it lets vl-parse return a module list.
  :result (vl-module-p val)
  :fails gracefully
  :count strong
  (vl-unimplemented))






;                                   SOURCE TEXT
;
; source_text ::= { description }
;
; description ::=
;    module_declaration
;  | udp_declaration
;  | config_declaration
;
; config_declaration ::=
;    'config' config_identifier ';'
;       design_statement {config_rule_statement}
;    'endconfig'
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
;       'endprimitive
;
; Every config_declaration begins with 'config'.  Otherwise, we have attributes
; and then a 'module', 'macromodule', or 'primitive' keyword.

(encapsulate
  ()
  (local (in-theory (disable (force))))
  (defparser vl-parse-description ()
    :result (vl-modulelist-p val)
    :resultp-of-nil t
    :true-listp t
    :fails gracefully
    :count strong
    (seqw tokens warnings
          (atts := (vl-parse-0+-attribute-instances))
          (when (vl-is-token? :vl-kwd-config)
            (mod := (vl-parse-config-declaration))
            (return (list mod)))
          (when (vl-is-token? :vl-kwd-primitive)
            (mods := (vl-parse-udp-declaration atts))
            (return mods))
          (mod := (vl-parse-module-declaration atts))
          (return (list mod)))))

(defparser vl-parse-source-text ()
  :result (vl-modulelist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seqw tokens warnings
        (when (atom tokens)
          (return nil))
        (first := (vl-parse-description))
        (rest := (vl-parse-source-text))
        (return (append first rest))))


(define vl-parse
  :parents (parser)
  :short "Top level parsing function."
  ((tokens   vl-tokenlist-p)
   (warnings vl-warninglist-p)
   (config   vl-loadconfig-p))
  :returns
  (mv (successp)
      (modules vl-modulelist-p :hyp :fguard)
      (warnings vl-warninglist-p))
  (b* (((mv err val tokens warnings)
        (vl-parse-source-text))
       ((when err)
        (vl-report-parse-error err tokens)
        (mv nil nil warnings)))
    (mv t val warnings)))
