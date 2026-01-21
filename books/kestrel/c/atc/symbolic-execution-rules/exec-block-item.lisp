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

(defsection atc-exec-block-item-rules
  :short "Rules for @(tsee exec-block-item)."

  (defruled exec-block-item-when-declon
    (implies (and (syntaxp (quotep item))
                  (equal (block-item-kind item) :declon)
                  (equal declon (block-item-declon->get item))
                  (not (zp limit))
                  (equal compst1
                         (exec-obj-declon declon compst fenv (1- limit)))
                  (compustatep compst1))
             (equal (exec-block-item item compst fenv limit)
                    (mv (stmt-value-none) compst1)))
    :enable exec-block-item)

  (defruled exec-block-item-when-stmt
    (implies (and (syntaxp (quotep item))
                  (equal (block-item-kind item) :stmt)
                  (not (zp limit)))
             (equal (exec-block-item item compst fenv limit)
                    (exec-stmt (block-item-stmt->get item)
                               compst
                               fenv
                               (1- limit))))
    :enable exec-block-item)

  (defval *atc-exec-block-item-rules*
    '(exec-block-item-when-declon
      exec-block-item-when-stmt
      (:e block-item-kind)
      (:e block-item-declon->get)
      (:e block-item-stmt->get)
      return-type-of-init-value-single)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-block-item-list-rules
  :short "Rules for @(tsee exec-block-item-list)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first two rules should be obvious in purpose.")
   (xdoc::p
    "The remaining rules are for the modular proofs.
     In the modular proofs, there is a need to compose
     the execution of some block items
     with the execution of some subsequent block items.
     That is, given a modular theorem for the first chunk of blocks,
     and a modular theorem for the second chunk of blocks,
     we need to generate a modular theorem for the concatenated chunks.")
   (xdoc::p
    "Thus, unsurprisingly, we need a theorem about
     @(tsee exec-block-item-list) applied to an @(tsee append) of block items,
     which is proved using a custom induction scheme.")
   (xdoc::p
    "However, this theorem is not directly applicable in modular proofs.
     This is because the concatenate block items come as a quoted constant,
     not as an @(tsee append) of the two chunks.
     Thus, in the modular proofs, we generate rules of a different form,
     as needed for each case (we always know the sizes of the two chunks).
     To support the generation of proofs for these custom rules,
     here we put two rules about lists that we need in those proofs."))

  (defruled exec-block-item-list-of-nil
    (implies (and (not (zp limit))
                  (compustatep compst))
             (equal (exec-block-item-list nil compst fenv limit)
                    (mv (stmt-value-none) compst)))
    :enable exec-block-item-list)

  (defruled exec-block-item-list-when-consp
    (implies (and (syntaxp (quotep items))
                  (consp items)
                  (not (zp limit))
                  (equal sval+compst1
                         (exec-block-item (car items) compst fenv (1- limit)))
                  (equal sval (mv-nth 0 sval+compst1))
                  (stmt-valuep sval)
                  (equal compst1 (mv-nth 1 sval+compst1)))
             (equal (exec-block-item-list items compst fenv limit)
                    (if (equal (stmt-value-kind sval) :return)
                        (mv sval compst1)
                      (exec-block-item-list (cdr items)
                                            compst1
                                            fenv
                                            (1- limit)))))
    :enable exec-block-item-list)

  (defruled exec-block-item-list-of-append
    (equal (exec-block-item-list (append items1 items2) compst fenv limit)
           (b* (((mv sval compst)
                 (exec-block-item-list items1 compst fenv limit))
                ((when (errorp sval)) (mv sval compst))
                ((when (stmt-value-case sval :return)) (mv sval compst)))
             (exec-block-item-list items2 compst fenv (- limit (len items1)))))
    :induct (ind items1 compst fenv limit)
    :enable (exec-block-item-list
             stmt-valuep-when-stmt-value-resultp-and-not-errorp
             len
             fix)
    :prep-lemmas
    ((defun ind (items compst fenv limit)
       (b* (((when (zp limit)) nil)
            ((when (endp items)) nil)
            ((mv sval compst)
             (exec-block-item (car items) compst fenv (1- limit)))
            ((when (errorp sval)) nil)
            ((when (stmt-value-case sval :return)) nil))
         (ind (cdr items) compst fenv (1- limit))))))

  (defruled append-of-take-and-nthcdr
    (implies (<= (nfix n) (len x))
             (equal (append (take n x) (nthcdr n x))
                    x))
    :induct t
    :enable (take nthcdr nfix len))

  (defruled len-of-take
    (equal (len (take n x))
           (nfix n)))

  (defval *atc-exec-block-item-list-rules*
    '(exec-block-item-list-of-nil
      exec-block-item-list-when-consp)))
