; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
(include-book "parse-modules")
(local (include-book "../util/arithmetic"))

(defxdoc parser
  :parents (loader)
  :short "Verilog Parser.")

(defparser vl-parse-udp-declaration (atts tokens warnings)
  ;; This :result is sloppy and won't be true if we implement configs, but
  ;; it lets vl-parse return a module list.
  :guard (vl-atts-p atts)
  :result (vl-module-p val)
  :fails gracefully
  :count strong
  (declare (ignorable atts))
  (vl-unimplemented))

(defparser vl-parse-config-declaration (tokens warnings)
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



(DEFMACRO VL-PARSE-RAM-HOOK (ATTS &OPTIONAL (TOKENS 'TOKENS)
                                  (WARNINGS 'WARNINGS))
  (LIST 'VL-PARSE-RAM-HOOK-FN ATTS TOKENS WARNINGS))

(ENCAPSULATE
  (((VL-PARSE-RAM-HOOK-FN * * *)
    => (mv * * * *)
    :formals (atts tokens warnings)
    :guard (and (vl-atts-p atts)
                (vl-warninglist-p warnings)
                (vl-tokenlist-p tokens))))
  (LOCAL (DEFUN VL-PARSE-RAM-HOOK-FN (ATTS TOKENS WARNINGS)
           (DECLARE (IGNORABLE ATTS))
           (MV T NIL TOKENS WARNINGS)))
  (DEFTHM VL-TOKENLIST-P-OF-VL-PARSE-RAM-HOOK
    (IMPLIES
     (FORCE (VL-TOKENLIST-P TOKENS))
     (VL-TOKENLIST-P
      (MV-NTH 2 (VL-PARSE-RAM-HOOK ATTS TOKENS WARNINGS))))
    :RULE-CLASSES ((:REWRITE :BACKCHAIN-LIMIT-LST 0)))
  (DEFTHM VL-WARNINGLIST-P-OF-VL-PARSE-RAM-HOOK
    (IMPLIES
     (FORCE (VL-WARNINGLIST-P WARNINGS))
     (VL-WARNINGLIST-P
      (MV-NTH 3 (VL-PARSE-RAM-HOOK ATTS TOKENS WARNINGS))))
    :RULE-CLASSES ((:REWRITE :BACKCHAIN-LIMIT-LST 0)))
  (DEFTHM VL-PARSE-RAM-HOOK-FAILS-GRACEFULLY
    (IMPLIES
     (MV-NTH 0 (VL-PARSE-RAM-HOOK ATTS TOKENS WARNINGS))
     (NOT (MV-NTH 1 (VL-PARSE-RAM-HOOK ATTS TOKENS WARNINGS)))))
  (DEFTHM VL-PARSE-RAM-HOOK-RESULT
    (IMPLIES
     (AND (FORCE (VL-TOKENLIST-P TOKENS))
          (FORCE (VL-ATTS-P ATTS)))
     (EQUAL
      (VL-MODULE-P
       (MV-NTH 1
               (VL-PARSE-RAM-HOOK ATTS TOKENS WARNINGS)))
      (NOT (MV-NTH 0
                   (VL-PARSE-RAM-HOOK ATTS TOKENS WARNINGS))))))
  (DEFTHM VL-PARSE-RAM-HOOK-COUNT-STRONG
    (AND
     (<= (ACL2-COUNT
          (MV-NTH 2
                  (VL-PARSE-RAM-HOOK ATTS TOKENS WARNINGS)))
         (ACL2-COUNT TOKENS))
     (IMPLIES
      (NOT (MV-NTH 0
                   (VL-PARSE-RAM-HOOK ATTS TOKENS WARNINGS)))
      (< (ACL2-COUNT
          (MV-NTH 2
                  (VL-PARSE-RAM-HOOK ATTS TOKENS WARNINGS)))
         (ACL2-COUNT TOKENS))))
                :RULE-CLASSES ((:REWRITE) (:LINEAR))))

(defparser vl-parse-ram-default-hook (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-module-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (declare (ignorable atts))
  (vl-parse-error "Oops, found VL_RAM but there's no RAM support in this
version of VL.  (For those outside of Centaur: the VL_RAM stuff is very
experimental and is not really ready to be used.  If you are inside of Centaur
and are seeing this message, something is wrong with the vl-parse-ram
override."))

(defattach vl-parse-ram-hook-fn vl-parse-ram-default-hook-fn)

(defparser vl-parse-description (tokens warnings)
  :guard (vl-warninglist-p warnings) ;; BOZO gross!
  :result (vl-module-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (cond ((not (consp tokens))
         (vl-parse-error "Unexpected EOF."))
        ((vl-is-token? :vl-kwd-config)
         (vl-parse-config-declaration))
        (t
         (mv-let (erp atts tokens warnings)
                 (vl-parse-0+-attribute-instances)
                 (if erp
                     (mv erp atts tokens warnings)
                   (cond ((vl-is-token? :vl-kwd-primitive)
                          (vl-parse-udp-declaration atts))
                         ((vl-is-token? :vl-kwd-vl_ram)
                          (vl-parse-ram-hook atts))
                         (t
                          (vl-parse-module-declaration atts))))))))

(defparser vl-parse-source-text (tokens warnings)
  :guard (vl-warninglist-p warnings) ;; BOZO gross!
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
        (return (cons first rest))))



(defund vl-parse (tokens warnings)
  "Returns (MV SUCCESSP MODULELIST WARNINGS)"
  (declare (xargs :guard (and (vl-tokenlist-p tokens)
                              (vl-warninglist-p warnings))))
  (b* (((mv err val tokens warnings)
        (vl-parse-source-text tokens warnings))
       ((when err)
        (vl-report-parse-error err tokens)
        (mv nil nil warnings)))
    (mv t val warnings)))

(defthm vl-modulelist-p-of-vl-parse
  (implies (and (force (vl-tokenlist-p tokens))
                (force (vl-warninglist-p warnings)))
           (vl-modulelist-p (mv-nth 1 (vl-parse tokens warnings))))
  :hints(("Goal" :in-theory (enable vl-parse))))

(defthm vl-warninglist-p-of-vl-parse
  (implies (force (vl-warninglist-p warnings))
           (vl-warninglist-p (mv-nth 2 (vl-parse tokens warnings))))
  :hints(("Goal" :in-theory (enable vl-parse))))

