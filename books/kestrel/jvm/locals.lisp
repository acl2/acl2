; Local variables in stack frames
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "operand-stacks") ;for pop-operand and pop-long
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/utilities/myif" :dir :system)

;move
(defthm count-slots-in-types-of-reverse-list
  (equal (count-slots-in-types (acl2::reverse-list parameter-types))
         (count-slots-in-types parameter-types))
  :hints (("Goal" :in-theory (enable count-slots-in-types))))

;;;
;;; local variables
;;;

; We represent the locals as a list but use separate functions to access and
; update them (so we can fine-tune and restrict the rules used, which are
; fairly simple).

(defund nth-local (n locals)
  (declare (xargs :guard (true-listp locals))
           (type (integer 0 *) n))
  (acl2::nth n locals))

(defund update-nth-local (n val locals)
  (declare (xargs :guard (true-listp locals))
           (type (integer 0 *) n))
  (acl2::update-nth n val locals))

(defthm true-listp-of-update-nth-local
  (implies (true-listp locals)
           (true-listp (update-nth-local n val locals)))
  :hints (("Goal" :in-theory (enable update-nth-local))))

(defthm nth-local-of-update-nth-local-same
  (equal (nth-local n (update-nth-local n val locals))
         val)
  :hints (("Goal" :in-theory (enable nth-local update-nth-local))))

(defthm nth-local-of-update-nth-local-diff
  (implies (and (not (equal n1 n2))
                (natp n1)
                (natp n2))
           (equal (nth-local n1 (update-nth-local n2 val locals))
                  (nth-local n1 locals)))
  :hints (("Goal" :in-theory (enable nth-local update-nth-local))))

(defthmd update-nth-local-of-update-nth-local-diff
  (implies (and (syntaxp (quotep i1))
                (syntaxp (quotep i2))
;                (< i1 len)
                (< i2 i1)
                (natp i1)
                (natp i2)
 ;               (natp len)
   ;             (true-listp l)
  ;              (equal len (len l))
                )
           (equal (update-nth-local i1 v1 (update-nth-local i2 v2 l))
                  (update-nth-local i2 v2 (update-nth-local i1 v1 l))))
  :hints (("Goal"
           :in-theory (enable update-nth-local ;LIST::UPDATE-NTH-UPDATE-NTH-DIFF
                              ))))

(defthm update-nth-local-of-update-nth-local-same
  (implies (natp i)
           (equal (update-nth-local i v1 (update-nth-local i v2 l))
                  (update-nth-local i v1 l)))
  :hints (("Goal" :in-theory (enable update-nth-local))))


;; Special case for pushing a MYIF into a component of a local.
(defthm myif-of-update-nth-local-same
  (equal (myif test
               (update-nth-local n val1 locals1)
               (update-nth-local n val2 locals2))
         (update-nth-local n
                           (myif test val1 val2)
                           (myif test locals1 locals2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm nth-local-of-myif
  (equal (nth-local n (myif test tp ep))
         (myif test
               (nth-local n tp)
               (nth-local n ep)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm update-nth-local-of-nth-local-same
  (implies (and (natp n)
                (< n (len locals)))
           (equal (update-nth-local n (nth-local n locals) locals)
                  locals))
  :hints (("Goal" :in-theory (enable update-nth-local nth-local))))

;; General rule for pushing a MYIF into a component of a local.
(defthm myif-of-update-nth-local-arg2
  (implies (and (natp n)
                (< n (len locals2)))
           (equal (myif test
                        (update-nth-local n val locals1)
                        locals2)
                  (update-nth-local n
                                    (myif test val (nth-local n locals2))
                                    (myif test locals1 locals2))))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-of-update-nth-local-arg1
  (implies (and (natp n)
                (< n (len locals1)))
           (equal (myif test
                        locals1
                        (update-nth-local n val locals2))
                  (update-nth-local n
                                    (myif test (nth-local n locals1) val)
                                    (myif test locals1 locals2))))
  :hints (("Goal" :in-theory (enable myif))))

;; Needed to relieve the hyps of myif-of-update-nth-local-arg2.
(defthm len-of-update-nth-local
  (implies (and (natp n)
                (< n (len locals)))
           (equal (len (update-nth-local n val locals))
                  (len locals)))
  :hints (("Goal" :in-theory (enable update-nth-local))))


;; todo: keep this disabled
;; TODO: Use the parameter-types to make this type-correct?
(defund uninitialized-locals (n)
  (declare (xargs :guard (natp n)))
  (acl2::repeat n
                nil  ;;:uninitialized-local ; todo: put this back
                ))

(defthm type-slot-count-when-not-2
  (implies (and (not (equal 2 (type-slot-count type)))
                (typep type))
           (equal (type-slot-count type)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable type-slot-count))))

;;;
;;; initialize-locals-aux
;;;

;; Initialize locals, from index current-slotnum down to 0 with values from the
;; stack, with the top value going at index current-slotnum (or current-slotnum
;; - 1 if it's a long/double).
(defun initialize-locals-aux (current-slotnum
                              rev-parameter-types ;last param comes first, which is the shallowest stack item
                              stack locals)
  (declare (xargs :guard (and (operand-stackp stack)
                              (all-typep rev-parameter-types)
                              (true-listp rev-parameter-types)
                              (integerp current-slotnum)
                              (= (+ 1 current-slotnum)
                                 (count-slots-in-types rev-parameter-types))
                              (<= (count-slots-in-types rev-parameter-types) (operand-stack-size stack))
                              (true-listp locals))
                  :guard-hints (("Goal" :expand (COUNT-SLOTS-IN-TYPES REV-PARAMETER-TYPES)))))
  (if (endp rev-parameter-types)
      locals
    (let ((type (first rev-parameter-types)))
      (if (= 2 (type-slot-count type)) ;long or double
          (initialize-locals-aux (- current-slotnum 2) ;we've used 2 slots
                                 (rest rev-parameter-types)
                                 (pop-long stack)
                                 (update-nth-local (- current-slotnum 1) ;longs and doubles take two slots but are stored in the lower slot - todo: define an update-nth-local-long?
                                                   (top-long stack)
                                                   locals))
        (initialize-locals-aux (- current-slotnum 1)
                               (rest rev-parameter-types)
                               (pop-operand stack)
                               (update-nth-local current-slotnum
                                                 (top-operand stack)
                                                 locals))))))

(acl2::defopeners initialize-locals-aux)

;The top operand on the stack comes last in the list of locals. This
;does the right thing for longs/doubles (stored in the lower of two
;stack operands), which get stored in the first of the two locals
;representing the long/double.)  So we don't need to call pop-long and
;top-long here (and it would not be practical to do so).
;; TODO: Actually, we could use the parameter-types here?
;; TODO: Disable prove rules about nth-local of this
(defun initialize-locals (parameter-types ; includes a type for "this", if appropriate. these come in order, with "this" first.
                          stack)
  (declare (xargs :guard (and (operand-stackp stack)
                              (all-typep parameter-types)
                              (true-listp parameter-types)
                              (<= (count-slots-in-types parameter-types) (operand-stack-size stack)))))
  (let ((local-slots (count-slots-in-types parameter-types)))
    (initialize-locals-aux (- local-slots 1)
                           (acl2::reverse-list parameter-types)
                           stack
                           (uninitialized-locals local-slots))))
