; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../language/dynamic-semantics")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-obj-declon-rules
  :short "Rules for @(tsee exec-block-item)."

  (defruled exec-obj-declon-open
    (implies (and (syntaxp (quotep declon))
                  (not (zp limit))
                  (equal var+scspec+tyname+init
                         (obj-declon-to-ident+scspec+tyname+init declon))
                  (equal var (mv-nth 0 var+scspec+tyname+init))
                  (equal scspec (mv-nth 1 var+scspec+tyname+init))
                  (equal tyname (mv-nth 2 var+scspec+tyname+init))
                  (equal init (mv-nth 3 var+scspec+tyname+init))
                  (scspecseq-case scspec :none)
                  init
                  (equal type (tyname-to-type tyname))
                  (not (type-case type :array))
                  (equal ival+compst1
                         (exec-initer init compst fenv (1- limit)))
                  (equal ival (mv-nth 0 ival+compst1))
                  (equal compst1 (mv-nth 1 ival+compst1))
                  (init-valuep ival)
                  (equal val (init-value-to-value type ival))
                  (valuep val)
                  (equal compst2 (create-var var val compst1))
                  (compustatep compst2))
             (equal (exec-obj-declon declon compst fenv limit)
                    compst2))
    :enable exec-obj-declon)

  (defval *atc-exec-obj-declon-rules*
    '(exec-obj-declon-open
      (:e obj-declon-to-ident+scspec+tyname+init)
      (:e scspecseq-kind))))
