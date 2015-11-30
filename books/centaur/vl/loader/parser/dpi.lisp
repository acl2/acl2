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
(include-book "functions")
(include-book "../lexer/chartypes") ;; for matching c_identifier syntax
(local (include-book "tools/do-not" :dir :system))
(local (include-book "../../util/arithmetic"))
(local (acl2::do-not generalize fertilize))

(defsection parse-dpi-import-export
  :parents (parser)
  :short "Functions for parsing DPI import/export statements.")

(local (xdoc::set-default-parents parse-dpi-import-export))

(define vl-dpi-spec-token-p ((x vl-token-p))
  (and (eq (vl-token->type x) :vl-stringtoken)
         ;; It's not clear whether we should do string expansion here or
         ;; literally require exactly the characters D P I instead of, e.g.,
         ;; their octal/hex encoded string-escape equivalents.  It seems fine
         ;; to just be more permissive and do the expansion.  Surely nobody
         ;; will ever care in practice either way, right?
         (let ((expansion (vl-stringtoken->expansion x)))
           (or (equal expansion "DPI")
               (equal expansion "DPI-C")))))

(define vl-interpret-dpi-spec-token ((x vl-token-p))
  :guard (vl-dpi-spec-token-p x)
  :prepwork ((local (in-theory (enable vl-dpi-spec-token-p))))
  :returns (spec vl-dpispec-p)
  (b* ((expansion (vl-stringtoken->expansion x)))
    (cond ((equal expansion "DPI")   :vl-dpi)
          ((equal expansion "DPI-C") :vl-dpi-c)
          (t
           (progn$ (impossible)
                   :vl-dpi)))))

(define vl-is-dpi-spec-string? (&key (tokstream 'tokstream))
  :short "Check whether the next token is a @('dpi_spec_string')."
  (b* ((tokens (vl-tokstream->tokens)))
    (and (consp tokens)
         (vl-dpi-spec-token-p (car tokens)))))

(defparser vl-parse-dpi-spec-string ()
  :short "Parse @('dpi_spec_string')."
  :long "<p>SystemVerilog-2012:</p>
         @({
              dpi_spec_string ::= '\"DPI-C\"' | '\"DPI\"'
         })"
  :result (vl-dpispec-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :prepwork ((local (in-theory (enable vl-is-dpi-spec-string? vl-match))))
  (seq tokstream
       (when (vl-is-dpi-spec-string?)
         (tok := (vl-match))
         (return (vl-interpret-dpi-spec-token tok)))
       (return-raw
        (vl-parse-error "Expected \"DPI\" or \"DPI-C\"."))))


(define vl-string-matches-c-identifier-p ((x stringp))
  :parents (vl-parse-c-identifier)
  (let ((chars (explode x)))
    (and (consp chars)
         (vl-simple-id-head-p (car chars))
         (vl-simple-id-tail-list-p (cdr chars)))))

(defparser vl-parse-c-identifier ()
  :short "Parse a @('c_identifier') into a string."
  :long "<p>SystemVerilog-2012:</p>
         @({
               c_identifier ::= [a-zA-Z_]{[a-zA-Z0-9_]}
         })"
  :result (stringp val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (id := (vl-match-token :vl-idtoken))
       ;; Now check if it's a valid C identifier token.
       (when (vl-string-matches-c-identifier-p (vl-idtoken->name id))
         (return (vl-idtoken->name id)))
       (return-raw
        (vl-parse-error "Expected a valid c_identifier."))))

(defparser vl-parse-optional-dpi-function-import-property ()
  :short "Parses @('dpi_function_import_property')."
  :long "<p>SystemVerilog-2012:</p>
         @({
               dpi_function_import_property ::= 'context' | 'pure'
         })"
  :result (vl-dpiprop-p val)
  :resultp-of-nil t
  :fails never
  :count strong-on-value
  (seq tokstream
       (when (vl-is-some-token? '(:vl-kwd-context :vl-kwd-pure))
         (prop := (vl-match)))
       (return (and prop
                    (case (vl-token->type prop)
                      (:vl-kwd-context :vl-dpi-context)
                      (:vl-kwd-pure    :vl-dpi-pure))))))

(defparser vl-parse-very-optional-tf-port-list ()
  :short "Parses <tt>[ '(' [tf_port_list] ')' ]</tt>."
  :result (vl-portdecllist-p val)
  :resultp-of-nil t
  :count strong-on-value
  :fails gracefully
  (seq tokstream
       (unless (vl-is-token? :vl-lparen)
         (return nil))
       (:= (vl-match-token :vl-lparen))
       (unless (vl-is-token? :vl-rparen)
         (portdecls := (vl-parse-tf-port-list)))
       (:= (vl-match-token :vl-rparen))
       (return portdecls)))

(define vl-warn-about-deprecated-dpi
  :short "Maybe warn about deprecated DPI imports/exports.  Compatible with
          @(see seq) and styled after @(see vl-parse-warning)."
  ((spec    vl-dpispec-p "The \"DPI\" or \"DPI-C\" ness of a DPI import/export.")
   (name    vl-idtoken-p "Name of the function being imported/exported.")
   (importp booleanp     "Are we importing or exporting?")
   &key (tokstream 'tokstream))
  :returns (mv (errmsg (not errmsg) "Never produces an error.")
               (value  (not value)  "Value is always @('nil').")
               (new-tokstream))
  :long "<p>The SystemVerilog-2012 spec (Section 35.5.4, Page 908) requires
         implementations to generate a compile time warning or error when
         \"DPI\" is used instead of \"DPI-C\".  We create this warning here, if
         necessary.</p>"
  (b* (((unless (vl-dpispec-equiv spec :vl-dpi))
        ;; Not using the deprecated "DPI" api, no need to warn.
        (mv nil nil tokstream))
       (warning (make-vl-warning
                 :type :vl-warn-deprecated-dpi
                 :msg  "At ~a0: ~s1 of ~s2: \"DPI\" is deprecated and should ~
                        be replaced with \"DPI-C\", but note that use of the ~
                        \"DPI-C\" string may require changes in the DPI ~
                        application's C code."
                 :args (list (vl-token->loc name)
                             (if importp "import" "export")
                             (vl-idtoken->name name))
                 :fatalp nil
                 :fn __function__))
       (tokstream (vl-tokstream-add-warning warning)))
    (mv nil nil tokstream))
  ///
  (more-returns
   (new-tokstream (equal (vl-tokstream->tokens :tokstream new-tokstream)
                         (vl-tokstream->tokens))
                  :name vl-tokstream->tokens-of-vl-warn-about-deprecated-dpi)))

(defparser vl-parse-dpi-import (atts)
  :short "Parses everything in @('dpi_import_export') import line."
  :long "<p>SystemVerilog-2012:</p>
         @({
             dpi_import_export ::=
                'import' dpi_spec_string [dpi_function_import_property] [ c_identifier '=' ] dpi_function_proto ';'
              | 'import' dpi_spec_string [dpi_task_import_property]     [ c_identifier '=' ] dpi_task_proto ';'
              | ... export cases ...

             dpi_function_import_property ::= 'context' | 'pure'
             dpi_task_import_property ::= 'context'

             dpi_function_proto ::= function_prototype
             dpi_task_proto     ::= task_prototype

             function_prototype ::= 'function' data_type_or_void function_identifier [ '(' [tf_port_list] ')' ]

             task_prototype ::= 'task' task_identifier [ '(' [tf_port_list] ')' ]
         })

         <p>We assume we've just eaten the @('import') and we're ready to parse
         everything else in @('dpi_import_export').</p>"
  :guard (vl-atts-p atts)
  :result (vl-dpiimport-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-kwd-import))
       (spec := (vl-parse-dpi-spec-string))
       (prop := (vl-parse-optional-dpi-function-import-property))
       (when (vl-is-token? :vl-idtoken)
         (c-name := (vl-parse-c-identifier))
         (:= (vl-match-token :vl-equalsign)))
       (fntask := (vl-match-some-token '(:vl-kwd-function :vl-kwd-task)))
       (when (and (eq (vl-token->type fntask) :vl-kwd-task)
                  (vl-dpiprop-equiv prop :vl-dpi-pure))
         (return-raw (vl-parse-error "Can't declare DPI imported task to be pure.")))
       (when (eq (vl-token->type fntask) :vl-kwd-function)
         (rettype := (vl-parse-datatype-or-void)))
       (name := (vl-match-token :vl-idtoken))
       (:= (vl-warn-about-deprecated-dpi spec name t))
       (portdecls := (vl-parse-very-optional-tf-port-list))
       (:= (vl-match-token :vl-semi))
       (return (make-vl-dpiimport
                :name      (vl-idtoken->name name)
                ;; It appears as though the C/linkage name is inherited from
                ;; the function name when it isn't explicitly provided; see for
                ;; instance the examples in SystemVerilog-2012 Section 35.4.
                :c-name    (or c-name (vl-idtoken->name name))
                :spec      spec
                :prop      prop
                :rettype   rettype
                :portdecls portdecls
                :atts      atts
                :loc       (vl-token->loc name)))))

(defparser vl-parse-dpi-export (atts)
  :short "Parses everything in a @('dpi_import_export') line @('export')."
  :long "<p>SystemVerilog-2012:</p>
         @({
             dpi_import_export ::=
                | 'export' dpi_spec_string [c_identifier '=' ] 'function' function_identifier ';'
                | 'export' dpi_spec_string [c_identifier '=' ] 'task' task_identifier ';'
                | ... import cases ...

             task_identifier ::= identifier
             function_identifier ::= identifier
         })"
  :guard (vl-atts-p atts)
  :result (vl-dpiexport-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-kwd-export))
       (spec := (vl-parse-dpi-spec-string))
       (when (vl-is-token? :vl-idtoken)
         (c-name := (vl-parse-c-identifier))
         (:= (vl-match-token :vl-equalsign)))
       (fntask := (vl-match-some-token '(:vl-kwd-function :vl-kwd-task)))
       (name := (vl-match-token :vl-idtoken))
       (:= (vl-warn-about-deprecated-dpi spec name nil))
       (:= (vl-match-token :vl-semi))
       (return (make-vl-dpiexport
                :name (vl-idtoken->name name)
                ;; It appears as though the C/linkage name is inherited from
                ;; the function name when it isn't explicitly provided; see for
                ;; instance the examples in SystemVerilog-2012 Section 35.4.
                :c-name (or c-name (vl-idtoken->name name))
                :spec   spec
                :fntask (case (vl-token->type fntask)
                          (:vl-kwd-function :vl-dpi-function)
                          (:vl-kwd-task     :vl-dpi-task))
                :atts atts
                :loc (vl-token->loc name)))))

