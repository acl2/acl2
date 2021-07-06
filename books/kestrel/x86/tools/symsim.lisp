; Symbolic simulation of x86 code (not using Axe)
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; A wrapper around symsim from books/misc/expander.  This handles
;; errors and has a return signature that works with
;; defconst-computed.

(include-book "misc/expander" :dir :system)

;Returns (mv new-term runes state).
(defun symsim$-fn (term hyps enables state)
  (declare (xargs :stobjs state
                  :mode :program))
  (mv-let (erp res state)
    (acl2::symsim-fn term hyps
                     t   ;=simplify-hyps-p
                     `(("Goal" :expand :lambdas  ;TODO: This may no longer be necessary
                        :in-theory (enable ,@enables)
                        ))
                     nil ;=prove-assumptions
                     nil ;=inhibit-output
                     t   ;=print-flg
                     (w state)
                     state)
    (if erp
        (mv (er hard 'symsim$ "Error in symsim.")
            nil
            state)
      (if (not (eql 1 (len res)))
          (mv (er hard 'symsim$ "symsim returned multiple results.") ;what does that mean?
              nil
              state)
        (let* ((res (first res))
               (runes (car res)) ;do these include runes used to simplify the assumptions?
               ;; (hyps (cadr res))
               (new-term (caddr res))
               ;; (assumptions (cdddr res)) ;how do these differ from the "hyps"?  perhaps these are from forcing
               )
          (mv new-term runes state))))))

;Returns (mv new-term state).
(defun symsim$-fn2 (term hyps enables state)
  (declare (xargs :stobjs state
                  :mode :program))
  (mv-let (new-term runes state)
    (symsim$-fn term hyps enables state)
    (declare (ignore runes))
    (mv new-term state)))

; Version of symsim that just returns the new term.  Returns (mv new-term state).
;TODO: Try defmacroq
(defmacro symsim$ (term hyps &key (enables 'nil))
  `(symsim$-fn2 ',term ,hyps ,enables state))
