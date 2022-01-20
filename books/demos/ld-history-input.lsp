; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(+ 3 4)

(ld-history state) ; raw form of history; note there is a single entry

(cw "Next we'll see how to get the components of a ld-history entry.~|")

(with-output :off event ; avoid discrepant output between ACL2 and ACL2(r)
(defun show-ld-history-entry (n state)
; Display the top ld-history entry by returning a user-friendly list.
  (declare (xargs :stobjs state
                  :guard (and (natp n) ; 0-based position in ld-history
                              (f-boundp-global 'ld-history state))))
  (let ((ld-history (@ ld-history)))
    (and (true-listp ld-history) ; for guard verification
         (< n (len ld-history))
         (let ((entry (nth n (ld-history state))))
           (and
            (weak-ld-history-entry-p entry) ; for guard verification
            (list (list :input (ld-history-entry-input entry))
                  (list :error-flg (ld-history-entry-error-flg entry))
                  (list :stobjs-out (ld-history-entry-stobjs-out entry))
                  (list :value (ld-history-entry-value entry))
                  (list :user-data (ld-history-entry-user-data entry))))))))
)

(* 4 5)

(assert-event
 (equal (show-ld-history-entry 0 state)
        '((:INPUT (* 4 5))
          (:ERROR-FLG NIL)
          (:STOBJS-OUT (NIL))
          (:VALUE 20)
          (:USER-DATA NIL))))

(car 3)

(assert-event
 (equal (show-ld-history-entry 0 state)
        '((:INPUT (CAR 3))
          (:ERROR-FLG T)
          (:STOBJS-OUT NIL)
          (:VALUE NIL)
          (:USER-DATA NIL))))

(assert-event
; replaced entry for preceding command
 (equal (show-ld-history-entry 0 state)
        '((:INPUT (SHOW-LD-HISTORY-ENTRY 0 STATE))
          (:ERROR-FLG NIL)
          (:STOBJS-OUT (NIL))
          (:VALUE ((:INPUT (CAR 3))
                   (:ERROR-FLG T)
                   (:STOBJS-OUT NIL)
                   (:VALUE NIL)
                   (:USER-DATA NIL)))
          (:USER-DATA NIL))))

(defun foo (x) (cons x x)) ; returns (mv nil foo state)

(assert-event
 (equal (show-ld-history-entry 0 state)
        '((:INPUT (DEFUN FOO (X) (CONS X X)))
          (:ERROR-FLG NIL)
          (:STOBJS-OUT (NIL NIL STATE))
          (:VALUE (NIL FOO REPLACED-STATE))
          (:USER-DATA NIL))))

(adjust-ld-history nil state) ; no change -- already in single-entry mode

(adjust-ld-history t state) ; change to multiple-entry mode

(assert-event (= (length (ld-history state))
                 2))

(make-list 7)

(assert-event (= (length (ld-history state))
                 4))

(assert-event (equal (show-ld-history-entry 1 state)
                     '((:INPUT (MAKE-LIST 7))
                       (:ERROR-FLG NIL)
                       (:STOBJS-OUT (NIL))
                       (:VALUE (NIL NIL NIL NIL NIL NIL NIL))
                       (:USER-DATA NIL))))

(assert-event (= (length (ld-history state))
                 6))

(adjust-ld-history -2 state) ; length 7 down to length 5

(assert-event (= (length (ld-history state))
                 6))

(adjust-ld-history 1 state) ; length 1, soon 2; still multiple-entry mode

(assert-event (= (length (ld-history state))
                 2))

(defun f1 (x)
  (declare (xargs :mode :program))
  (car x))

(ld
; No command is recorded for (f1 7) because of the raw Lisp error.
; But a command is recorded for h and then for the enclosing LD.
 '((f1 7) (defun h (x) x))
 :ld-error-action :continue)

(assert-event
 (equal (list (show-ld-history-entry 0 state)
              (show-ld-history-entry 1 state)
              (show-ld-history-entry 2 state))
        '(((:INPUT (LD '((F1 7) (DEFUN H (X) X))
                       :LD-ERROR-ACTION :CONTINUE))
           (:ERROR-FLG NIL)
           (:STOBJS-OUT (NIL NIL STATE))
           (:VALUE (NIL :EOF REPLACED-STATE))
           (:USER-DATA NIL))
          ((:INPUT (DEFUN H (X) X))
           (:ERROR-FLG NIL)
           (:STOBJS-OUT (NIL NIL STATE))
           (:VALUE (NIL H REPLACED-STATE))
           (:USER-DATA NIL))
          ((:INPUT (DEFUN F1 (X)
                     (DECLARE (XARGS :MODE :PROGRAM))
                     (CAR X)))
           (:ERROR-FLG NIL)
           (:STOBJS-OUT (NIL NIL STATE))
           (:VALUE (NIL F1 REPLACED-STATE))
           (:USER-DATA NIL)))))

(car '(7))

(make-event (er-progn (ld '((defun g (x) x)))
                      (value '(value-triple 17))))

(assert-event
; Check that entries aren't saved in the ld-history for commands issues during
; make-event expansion.
 (equal (list (show-ld-history-entry 0 state)
              (show-ld-history-entry 1 state))
        '(((:INPUT (MAKE-EVENT (ER-PROGN (LD '((DEFUN G (X) X)))
                                         (VALUE '(VALUE-TRIPLE 17)))))
           (:ERROR-FLG NIL)
           (:STOBJS-OUT (NIL NIL STATE))
           (:VALUE (NIL 17 REPLACED-STATE))
           (:USER-DATA NIL))
          ((:INPUT (CAR '(7)))
           (:ERROR-FLG NIL)
           (:STOBJS-OUT (NIL))
           (:VALUE 7)
           (:USER-DATA NIL)))))
