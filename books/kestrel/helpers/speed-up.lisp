; A utility that suggests ways to speed up a theorem
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See improve-book for a tool that applies this tool to an entire book or set
;; of books (along with suggesting other improvements).

(include-book "kestrel/utilities/prove-dollar-nice" :dir :system)
(include-book "kestrel/utilities/theory-hints" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system)
(include-book "kestrel/utilities/runes" :dir :system)

;; Returns (mv erp provedp elapsed-time state)
;move
(defun prove$-nice-with-time (term
                              hints
                              instructions
                              otf-flg
                              time-limit ; warning: not portable!
                              step-limit
                              state)
  (declare (xargs :guard (and (booleanp otf-flg)
                              (or (and (rationalp time-limit)
                                       (<= 0 time-limit))
                                  (null time-limit))
                              (or (natp step-limit)
                                  (null step-limit)))
                  :mode :program
                  :stobjs state))
  ;; Record the start time:
  (mv-let (start-time state)
    (acl2::get-real-time state)
    (mv-let (erp provedp state)
      (prove$-nice-fn term hints instructions otf-flg time-limit step-limit state)
      ;; Record the end time:
      (mv-let (end-time state)
        (acl2::get-real-time state)
        (if erp
            (mv erp nil nil state)
          (mv nil provedp (- end-time start-time) state))))))

;; in seconds
(defconst *minimum-time-savings-to-report* 1/10)

;; Returns state.
(defun try-to-drop-rules (rules body hints otf-flg time-to-beat state)
  (declare (xargs :guard (and (true-listp rules)
                              (rationalp time-to-beat))
                  :mode :program
                  :stobjs state))
  (if (endp rules)
      state
    (let ((rule-to-drop (first rules)))
      (mv-let (erp provedp time state)
        (prove$-nice-with-time body
                               (disable-items-in-hints hints (list rule-to-drop))
                               nil ; instructions
                               otf-flg
                               time-to-beat ; time-limit ; warning: not portable!
                               nil          ; step-limit
                               state)
        (if erp
            (prog2$ (er hard? 'try-to-drop-rules "Error trying to disable ~x0." rule-to-drop)
                    state)
          (progn$ (and provedp
                       (if (< time time-to-beat)
                           (let* ((savings (- time-to-beat time))
                                  (percent-saved (floor (* 100 (/ savings time-to-beat)) 1)))
                             (if (<= *minimum-time-savings-to-report* savings)
                                 (progn$ (cw "  (Speedup: disable ~x0 to save " rule-to-drop)
                                         (print-to-hundredths savings)
                                         (cw " of ")
                                         (print-to-hundredths time-to-beat)
                                         (cw " seconds (~x0%))~%" percent-saved))
                               (progn$ ;; (cw "  (Minimal speedup: disable ~x0 to save " rule-to-drop)
                                       ;; (print-to-hundredths savings)
                                       ;; (cw " of ")
                                       ;; (print-to-hundredths time-to-beat)
                                       ;; (cw " seconds (~x0%))~%" percent-saved)
                                       )))
                         (progn$ ;; (cw "  (Slower: disable ~x0: " rule-to-drop)
                                 ;; (print-to-hundredths time)
                                 ;; (cw " vs ")
                                 ;; (print-to-hundredths time-to-beat)
                                 ;; (cw " seconds)~%")
                                 )))
                  (try-to-drop-rules (rest rules) body hints otf-flg time-to-beat state)))))))

;; Prints suggested ways to speed up a theorem.  EVENT should be a defthm (or a variant, like defthmd).
;; Returns (mv erp state).
(defun try-to-speed-up-defthm-fn (event state)
  (declare (xargs :mode :program
                  :stobjs state))
  (let* (;;(defthm-variant (first event))
         (defthm-args (rest event))
         (name (first defthm-args))
         (body (second defthm-args))
         (keyword-value-list (rest (rest defthm-args)))
         (hintsp (assoc-keyword :hints keyword-value-list))
         (hints (cadr hintsp))
         (otf-flgp (assoc-keyword :otf-flg keyword-value-list))
         (otf-flg (cdr otf-flgp))
         (instructionsp (assoc-keyword :instructions keyword-value-list)))
    (if instructionsp
        (progn$ ;; (cw "Not trying to speed up ~x0 because it uses :instructions." name) ; todo: elsewhere, could try to prove without instructions
                (mv nil state))
      ;; Record the start time:
      (mv-let (start-time state)
        (acl2::get-real-time state)
        ;; Do the proof and time it:
        (mv-let (erp provedp state)
          (prove$-nice-fn body
                          hints
                          nil
                          otf-flg
                          nil ; time-limit
                          nil ; step-limit
                          state)
          ;; Record the end time:
          (mv-let (end-time state)
            (acl2::get-real-time state)
            (if erp
                (mv erp state)
              (if (not provedp)
                  (prog2$ (er hard? 'try-to-speed-up-defthm "~x0 was expected to prove, but it failed." name)
                          (mv :failed state))
                (let* ((elapsed-time (- end-time start-time)))
                  (if (< elapsed-time 1/100)
                      (progn$ ;; (cw "(Not trying to speed up ~x0 because it only takes " name)
                              ;; (print-to-hundredths elapsed-time)
                              ;; (cw " seconds)~%")
                              (mv nil state))
                    ;; Get the list of runes used in the proof:
                    (let* ((runes-used (get-event-data 'rules state))
                           (state (try-to-drop-rules (drop-fake-runes runes-used) body hints otf-flg elapsed-time state)))
                      (mv nil state))))))))))))

(defmacro speed-up-defthm (event)
  `(try-to-speed-up-defthm-fn ',event state))
