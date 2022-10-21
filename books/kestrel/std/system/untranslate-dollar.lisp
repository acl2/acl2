; Standard System Library
;
; Copyright (C) 2022 ForrestHunt, Inc.
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Matt Kaufmann (matthew.j.kaufmann@gmail.com)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection untranslate$
  :parents (std/system/term-transformations)
  :short "A logic-mode guard-verified version of @(tsee untranslate)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a @(see logic) mode version of the function,
     @('untranslate').  See @(see untranslate), but note
     that instead of @('(untranslate term iff-flg wrld)')
     one calls @('(untranslate$ term iff-flg state)'); that
     is, the @(see world) has been replaced by @(see state).")
   (xdoc::p
    "The untranslation operated by this utility does not
     make any use of the @(tsee
     user-defined-functions-table): neither the
     untranslate-preprocess capability nor wholesale
     replacement of untranslate.  (Technical Note:
     @('Untranslate$) calls @('untranslate1') instead of
     @(tsee untranslate), using a @('preprocess-fn')
     argument of @('nil') to avoid certain hard errors.)")
   (xdoc::p
    "If the call to @('untranslate1') causes a hard error,
     so does @('untranslate$');
     this is achieved by passing @('nil')
     as the @('hard-error-returns-nilp') argument of @(tsee magic-ev-fncall).
     If the @(tsee magic-ev-fncall) fails,
     we also stop with a hard error."))

  (defund untranslate$ (term iff-flg state)
    (declare (xargs :stobjs state
                    :guard (pseudo-termp term)))
    (let* ((wrld (w state))
           (tbl (untrans-table wrld))
           (fn ; (untranslate-preprocess-fn wrld)

; The use of magic-ev-fncall for untranslate1, below, causes untranslate1 to be
; run in safe-mode (see "Additional Notes" in :DOC magic-ev-fncall).  This can
; lead to unfortunate errors.  In particular, if if you first evaluate
; (include-book "xdoc/init" :dir :system) and you bind fn here to
; (untranslate-preprocess-fn wrld), perhaps using magic-ev-fncall (or with an
; appropriate ec-call used in the body of that function), then the untranslate1
; call below will cause a hard error because of a "program-only" function.

            nil))
      (mv-let
          (erp val)
          (magic-ev-fncall 'untranslate1
                           (list term iff-flg tbl fn wrld)
                           state
                           nil
                           t)
        (if erp ; probably rare
            (er hard? 'untranslate$ "~@0" val)
          val)))))
