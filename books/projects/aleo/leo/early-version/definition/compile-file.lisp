; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "compiler")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :open-output-channel!)

(define compile ((code-path stringp)
                 (input-path stringp)
                 (output-path stringp)
                 (curve curvep)
                 state)
  :returns (mv erp val state)
  :mode :program
  :parents (compiler)
  :short "Compile a Leo program with a Leo input file,
          generating a Leo output file."
  (b* (((er outlines) (compile-file-and-input-file-to-lines code-path
                                                            input-path
                                                            curve
                                                            state)))
    (state-global-let*
     ((fmt-soft-right-margin 1000000 set-fmt-soft-right-margin)
      (fmt-hard-right-margin 1000000 set-fmt-hard-right-margin))
     (b* (((mv channel state)
           (open-output-channel! output-path :character state))
          (state (pprinted-lines-to-channel outlines channel state))
          (state (close-output-channel channel state)))
       (mv nil nil state)))))

(defttag nil)
