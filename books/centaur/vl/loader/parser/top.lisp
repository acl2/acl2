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
(include-book "../descriptions")
(include-book "modules")
(include-book "udps")
(include-book "interfaces")
(include-book "packages")
(include-book "programs")
(include-book "configs")
(include-book "imports")
(include-book "std/strings/fast-cat" :dir :system)
(local (include-book "../../util/arithmetic"))

(local (in-theory (disable (tau-system))))

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
;  | {attribute_instance} package_item
;  | {attribute_instance} bind_directive
;  | config_declaration

(defparser vl-parse-top-level-import (atts)
  :guard (and (vl-is-token? :vl-kwd-import)
              (vl-atts-p atts))
  :result (vl-descriptionlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-plausible-start-of-package-import-p)
         (imports := (vl-parse-package-import-declaration atts))
         (return imports))
       ;; Otherwise maybe it's a DPI import.
       (dpiimport := (vl-parse-dpi-import atts))
       (return (list dpiimport))))

(defparser vl-parse-description ()
  ;; Note: we return a list of descriptions because sometimes a 'single'
  ;; construct actually introduces several things.  For instance, an import
  ;; statement like "import foo::bar, foo::baz;" turns into two parsed imports.
  :result (vl-descriptionlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (atts := (vl-parse-0+-attribute-instances))
        (when (atom (vl-tokstream->tokens))
          (return-raw (vl-parse-error "Unexpected EOF.")))

        (when (vl-is-token? :vl-kwd-config)
          ;; In both Verilog and SystemVerilog, config_declaration always
          ;; starts with 'config'
          (cfg := (vl-parse-config-declaration atts))
          (return (list cfg)))

        (when (vl-is-token? :vl-kwd-primitive)
          ;; After attributes, udp_declaration always starts with 'primitive'
          ;; in Verilog, or 'primitive' or 'extern primitive' in SystemVerilog.
          ;; We don't support extern yet.
          (udp := (vl-parse-udp-declaration atts))
          (return (list udp)))

        (when (vl-is-some-token? '(:vl-kwd-module :vl-kwd-macromodule))
          ;; After attributes, modules start with 'module' or 'macromodule' in
          ;; Verilog.  SystemVerilog adds 'extern module' and extern
          ;; macromodule', but we don't support that yet.
          (mod := (vl-parse-module-declaration atts))
          (return (list mod)))

        (when (eq (vl-loadconfig->edition config) :verilog-2005)
          ;; For Verilog-2005 the above is everything that's allowed.
          (return-raw
           (vl-parse-error "Expected a module, primitive, or config.")))

        (when (vl-is-token? :vl-kwd-extern)
          (return-raw
           (vl-parse-error "Not yet implemented: extern")))

        (when (vl-is-token? :vl-kwd-bind)
          ;; bind_directive always starts with 'bind'
          (bind := (vl-parse-bind-directive atts))
          (return (list bind)))

        (when (vl-is-token? :vl-kwd-config)
          ;; config_directive always starts with 'config'
          (return-raw
           (vl-parse-error "Config directives are not implemented.")))

        (when (vl-is-token? :vl-kwd-interface)
          ;; after attribute instances, interface_declaration starts with
          ;; 'interface', or 'extern interface', but we don't support extern
          ;; yet.
          (interface := (vl-parse-interface-declaration atts))
          (return (list interface)))

        (when (vl-is-token? :vl-kwd-program)
          ;; after attribute instances, program_declaration starts with
          ;; 'program' or 'extern program', but we don't support extern yet.
          (program := (vl-parse-program-declaration atts))
          (return (list program)))

        (when (vl-is-token? :vl-kwd-class)
          ;; after attribute instances, class_declaration starts with
          ;; 'class' or 'extern class', but we don't support extern yet.
          (class := (vl-parse-class-declaration atts))
          (return (list class)))

        (when (vl-is-token? :vl-kwd-package)
          ;; after attribute instances, package_declaration starts with
          ;; 'package'.
          (package := (vl-parse-package-declaration atts))
          (return (list package)))

        (when (vl-is-token? :vl-kwd-property)
          ;; BOZO are these supposed to have atts?
          (property := (vl-parse-property-declaration))
          (return (list property)))

        (when (vl-is-token? :vl-kwd-sequence)
          ;; BOZO are these supposed to have atts?
          (sequence := (vl-parse-sequence-declaration))
          (return (list sequence)))

        ;; If we get here, then we must be dealing with a package item.
        ;; There are tons of package items and we don't support them
        ;; all yet.

        ;; package_item ::= package_or_generate_item_declaration
        ;;                | anonymous_program
        ;;                | package_export_declaration
        ;;                | timeunits_declaration
        ;;
        ;; package_or_generate_item_declaration ::= net_declaration
        ;;                                        | data_declaration
        ;;                                        | task_declaration
        ;;                                        | function_declaration
        ;;                                        | checker_declaration
        ;;                                        | dpi_import_export
        ;;                                        | extern_constraint_declaration
        ;;                                        | class_declaration
        ;;                                        | class_constructor_declaration
        ;;                                        | local_parameter_declaration ';'
        ;;                                        | parameter_declaration ';'
        ;;                                        | covergroup_declaration
        ;;                                        | overload_declaration
        ;;                                        | assertion_item_declaration
        ;;                                        | ';'

        (when (vl-is-token? :vl-kwd-task)
          (tasks := (vl-parse-task-declaration atts))
          (return tasks))
        (when (vl-is-token? :vl-kwd-function)
          (fns := (vl-parse-function-declaration atts))
          (return fns))
        (when (vl-is-token? :vl-kwd-import)
          (imports := (vl-parse-top-level-import atts))
          (return imports))
        (when (vl-is-token? :vl-kwd-export)
          (dpiexport := (vl-parse-dpi-export atts))
          (return (list dpiexport)))

        (when (vl-is-some-token? '(:vl-kwd-parameter :vl-kwd-localparam))
          (params := (vl-parse-param-or-localparam-declaration atts '(:vl-kwd-parameter :vl-kwd-localparam)))
          (:= (vl-match-token :vl-semi))
          (return params))
        (when (vl-is-token? :vl-kwd-typedef)
          (typedef := (vl-parse-type-declaration atts))
          (return (list typedef)))
        (when (or (vl-is-token? :vl-kwd-virtual)
                  (vl-is-token? :vl-kwd-class))
          (class := (vl-parse-class-declaration atts))
          (return (list class)))
        (when (vl-is-token? :vl-semi)
          ;; seems to be allowed by commercial implementations
          (:= (vl-parse-warning :vl-warn-unexpected-semicolon "Ignored unexpected semicolon"))
          (:= (vl-match))
          (return nil))
        (return-raw
         (b* ((backup (vl-tokstream-save))
              ((mv err vardecls tokstream)
               (vl-parse-main-data-declaration atts))
              ((unless err)
               (mv err vardecls tokstream))
              (tokstream (vl-tokstream-restore backup)))
           (vl-parse-error "Unsupported top-level construct?")))))


; Verilog-2005:
; source_text ::= { description };
;
; SystemVerilog-2012 adds:
; source_text ::= [timeunits_declaration] { description }
;
; But we don't support this timeunit declaration yet.

(defparser vl-parse-source-text ()
  ;; Note that for proper scoping it's important that this return the
  ;; descriptions in parse order.
  :result (vl-descriptionlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seq tokstream
        (when (atom (vl-tokstream->tokens))
          (return nil))
        (first := (vl-parse-description))
        (rest := (vl-parse-source-text))
        (return (append first rest))))


(define vl-parse
  :parents (parser)
  :short "Top level parsing function."
  ((tokens   vl-tokenlist-p)
   (pstate   vl-parsestate-p)
   (config   vl-loadconfig-p))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (items    vl-descriptionlist-p :hyp :fguard)
      (pstate   vl-parsestate-p))
  (b* (((acl2::local-stobjs tokstream)
        (mv okp val pstate tokstream))
       (tokstream (vl-tokstream-update-tokens tokens))
       (tokstream (vl-tokstream-update-pstate pstate))
       ((mv err items tokstream)
        ;; Note that items are returned in parse order.
        (vl-parse-source-text))
       ((when err)
        ;; Warnings are a little subtle here.  Note that above we installed the
        ;; initial pstate into the tokstream, so any errors that previously
        ;; were in the parse state are still there.  Also any minor warnings
        ;; that we wanted to issue during the main act of parsing have already
        ;; been added.  However, if vl-parse-source-text failed with a
        ;; vl-parse-error, then the final err it produced has NOT yet been
        ;; added to the parse state (because in general we don't want to add
        ;; parse errors as soon as they're encountered, due to backtracking).
        ;; So add it now.
        (b* ((tokstream (vl-tokstream-add-warning err))
             (pstate (vl-tokstream->pstate)))
          (mv nil nil pstate tokstream)))
       ;; Else, no parse error and everything is fine.
       (pstate (vl-tokstream->pstate)))
    (mv t items pstate tokstream)))
