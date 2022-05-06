; Copyright (C) 2021, ForrestHunt, Inc.
; Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; For more tests of stobj-let, see also the community books file and directory
; system/tests/nested-stobj-tests.lisp and
; system/tests/abstract-stobj-nesting/.

(defstobj sub1 sub1-fld)
(defstobj sub2 sub2-fld :congruent-to sub1)
(defstobj top1 (top1-fld :type sub1) :renaming ((update-top1-fld !top1-fld)))

; Error: bad implicit updater for producer variable
(defun f1 (x top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((sub1 (top1-fld top1)))
   (sub1)
   (update-sub1-fld x sub1)
   top1))

; Error: bad explicit updater for producer variable
(defun f1 (x top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((sub1 (top1-fld top1) update-top1-fld))
   (sub1)
   (update-sub1-fld x sub1)
   top1))

; Error: bad explicit updater for non-producer variable
(defun f1 (top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((sub1 (top1-fld top1) update-top1-fld))
   (val)
   (sub1-fld sub1)
   val))

; No error, even though implicit updater is wrong, because it doesn't
; correspond to a producer variable.
(defun f1 (top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((sub1 (top1-fld top1)))
   (val)
   (sub1-fld sub1)
   val))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Here are a few random examples of using stobjs that have
;;; hash-table fields with stobj value types.  This might
;;; not be an appropriate place for other typed hash-table,
;;; fields or for successes rather than just errors (as
;;; suggested by the filename) but it's convenient to put
;;; such tests here, too.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj st1 (ht1 :type (hash-table eq 70 t)))

(assert-event (equal (ht1-get 'a st1) nil))

(ht1-put 'a 17 st1)

(assert-event (equal (ht1-get 'a st1) 17))

; Guard vioation
(ht1-get 3 st1)

; Fails: need :initially
(defstobj st2 (ht2 :type (hash-table eq nil integer)))

; Fails: the test = is not supported (though it could be)
(defstobj st2 (ht2 :type (hash-table = nil integer) :initially 0))

(defstobj st2 (ht2 :type (hash-table eq nil integer) :initially 0))

; :Initially provides the default value:
(assert-event (equal (ht2-get 'a st2) 0))

; Fails: 'b does not evaluate to an integer.
(ht2-put 'a 'b st2)

; Value is still 0 because 'a is still not a key of ht2.
(assert-event (mv-let (val boundp)
                (ht2-get? 'a st2)
                (and (equal val 0)
                     (equal boundp nil))))

(ht2-put 'a 17 st2)

(assert-event (equal (ht2-get 'a st2) 17))

(assert-event (mv-let (val boundp)
                (ht2-get? 'a st2)
                (and (equal val 17)
                     (equal boundp t))))

(defstobj st3 (ht3 :type (hash-table eq nil integer) :initially 0)
  :congruent-to st2)

(ht2-put 'a 23 st3)

(assert-event (equal (ht2-get 'a st3) 23))

(ht2-clear st3)

(assert-event (equal (ht2-get 'a st3) 0))

; Fails: :initially is not allowed for stobj element type.
(defstobj st4 (ht4 :type (hash-table eq nil sub1) :initially nil))

(defstobj st4 (ht4 :type (hash-table eq nil sub1)))

; Fails: Need to use stobj-let.
(ht4-get 'a st4)

; Fails: Type violation (17 is not of type sub1; actually stobj type expected)
(ht4-put 'a 17 st4)

; Fails: guard verification requires (symbolp key).
(defun update-sub1-fld-in-ht4 (key val st4)
  (declare (xargs :guard t
                  :stobjs st4))
  (stobj-let
   ((sub1 (ht4-get key st4))) ; bindings
   (sub1)                     ; producer variable(s)
   (update-sub1-fld val sub1) ; producer
   st4))

(defun update-sub1-fld-in-ht4 (key val st4)
  (declare (xargs :guard (symbolp key)
                  :stobjs st4))
  (stobj-let
   ((sub1 (ht4-get key st4))) ; bindings
   (sub1)                     ; producer variable(s)
   (update-sub1-fld val sub1) ; producer
   st4))

; Fails: Illegal index, key (because it's a producer variable)
(defun read-sub1-fld-in-ht4 (key st4)
  (declare (xargs :guard (symbolp key)
                  :stobjs st4))
  (stobj-let
   ((sub1 (ht4-get key st4))) ; bindings
   (key)                      ; producer variable(s)
   (sub1-fld sub1)            ; producer
   key))

; Fails: Index is not a symbol
(defun read-sub1-fld-in-ht4 (key st4)
  (declare (xargs :guard t
                  :stobjs st4))
  (stobj-let
   ((sub1 (ht4-get (and (symbolp key) key) st4))) ; bindings
   (f)                                            ; producer variable(s)
   (sub1-fld sub1)                                ; producer
   f))

(defun read-sub1-fld-in-ht4 (key st4)
  (declare (xargs :guard (symbolp key)
                  :stobjs st4))
  (stobj-let
   ((sub1 (ht4-get key st4))) ; bindings
   (f)                        ; producer variable(s)
   (sub1-fld sub1)                 ; producer
   f))

(assert-event (equal (read-sub1-fld-in-ht4 'a st4) nil))

(update-sub1-fld-in-ht4 'b 10 st4)

(assert-event (equal (read-sub1-fld-in-ht4 'b st4) 10))

(defun swap-sub1-flds-in-ht4 (key1 key2 st4)
  (declare (xargs :guard (and (symbolp key1)
                              (symbolp key2)
                              (not (eq key1 key2)))
                  :stobjs st4))
  (stobj-let
   ((sub1 (ht4-get key1 st4))
    (sub2 (ht4-get key2 st4)))
   (sub1 sub2)
   (swap-stobjs sub1 sub2)
   st4))

(swap-sub1-flds-in-ht4 'a 'b st4)

(assert-event (equal (read-sub1-fld-in-ht4 'a st4) 10))
(assert-event (equal (read-sub1-fld-in-ht4 'b st4) nil))
