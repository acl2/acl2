; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "../../language/parse-yul-file")

(include-book "../../../transformations/dead-code-eliminator")

; (depends-on "conditional_break.yul")
; (depends-on "conditional_break.yul.expected")
; (depends-on "early_break.yul")
; (depends-on "early_break.yul.expected")
; (depends-on "early_continue.yul")
; (depends-on "early_continue.yul.expected")
; (depends-on "early_leave.yul")
; (depends-on "early_leave.yul.expected")

;; Test the formalized deadCodeEliminator transformation
;; for the ( .yul , .yul.expected ) pairs in this directory.

(defmacro assert-before-and-after-dead-code-eliminator (before-filename after-filename)
  `(assert-event
    (b* (((mv in-block out-block state)
          (PARSE-YUL-OPTIMIZER-PAIR ,before-filename ,after-filename state))
         ((when (or (resulterrp in-block) (resulterrp out-block)))
          (mv nil nil state)) )
      (if (equal (BLOCK-DEAD in-block) out-block)
          (mv nil t state)
        (mv nil nil state)))
    :stobjs-out :auto))

(assert-before-and-after-dead-code-eliminator "conditional_break.yul" "conditional_break.yul.expected")
(assert-before-and-after-dead-code-eliminator "early_break.yul" "early_break.yul.expected")
(assert-before-and-after-dead-code-eliminator "early_continue.yul" "early_continue.yul.expected")
(assert-before-and-after-dead-code-eliminator "early_leave.yul" "early_leave.yul.expected")
