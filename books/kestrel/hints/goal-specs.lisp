; Utilities about hints and goal-specs
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund hint-has-goal-specp (hint target-goal-spec)
  (declare (xargs :guard (and (stringp target-goal-spec)
                              (standard-string-p target-goal-spec))))
  (and (consp hint) ; if not, it's a computed hint function
       (let ((goal-spec (car hint)))
         (and (stringp goal-spec) ; if not, we've got a computed hint
              (if (standard-string-p goal-spec) ; lets us call string-equal
                  t
                (er hard? 'hint-has-goal-specp "Unexpected goal spec: ~x0." goal-spec))
              ;; case-insensitive:
              (string-equal goal-spec target-goal-spec)))))

(defthm hint-has-goal-specp-forward-to-consp
  (implies (hint-has-goal-specp hint target-goal-spec)
           (consp hint))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hint-has-goal-specp))))

;; Gets the hint-keyword-value-list (e.g., (:use XXX :in-theory YYY)) for the
;; given goal-spec (e.g., "Goal").
(defund hint-keyword-value-list-for-goal-spec (goal-spec hints)
  (declare (xargs :guard (and (stringp goal-spec)
                              (standard-string-p goal-spec)
                              (true-listp hints))))
  (if (endp hints)
      nil
    (let ((hint (first hints)))
      (if (hint-has-goal-specp hint goal-spec)
          (cdr hint) ; everything but the goal-spec
        (hint-keyword-value-list-for-goal-spec goal-spec (rest hints))))))
