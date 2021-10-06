; A utility to macroexpand a form one step
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/system/macro-namep" :dir :system)
(include-book "magic-macroexpand")

(local
 (in-theory (disable boundp-global1 plist-worldp)))

;move
;gen?
(defthm bound-global1-when-state-p1
  (implies (and (state-p1 state)
                (member-eq sym '(safe-mode do-expressionp ld-skip-proofsp temp-touchable-vars parallel-execution-enabled boot-strap-flg guard-checking-on temp-touchable-fns)) ;(member-eq sym *initial-global-table*)
                )
           (boundp-global1 sym state))
  :hints (("Goal" :in-theory (enable state-p1 boundp-global1))))

;; Macroexpand the top-level macro in FORM (i.e., perform just one step of
;; expansion). FORM should be a call of a macro.  Returns (mv erp val).
(defund magic-macroexpand1$ (form ctx world state)
  (declare (xargs :guard (and (consp form)
                              (true-listp form)
                              ;; (symbolp (car form))
                              (plist-worldp world)
                              (macro-namep (car form) world)
                              (pseudo-termp (fgetprop (car form) 'guard *t* world)) ;why?
                              )
                  :stobjs state))
  (magic-macroexpand1 form
                      (getpropc (car form) 'macro-body nil world)
                      ctx
                      world
                      (default-state-vars t)
                      state))

(defthm magic-macroexpand1$-normalize-context
  (implies (syntaxp (not (equal context ''fake-context)))
           (equal (mv-nth 1 (magic-macroexpand1$ term context world state))
                  (mv-nth 1 (magic-macroexpand1$ term 'fake-context world state))))
  :hints (("Goal" :in-theory (enable magic-macroexpand1$))))
