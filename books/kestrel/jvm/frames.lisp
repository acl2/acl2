; Call stack frames
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Note: Portions of this file may be taken from books/models/jvm/m5.  See the
; LICENSE file and authorship information there as well.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "ads")
(include-book "operand-stacks")
(include-book "kestrel/jvm/methods" :dir :system)
(include-book "kestrel/utilities/myif" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))

(defund maybe-addressp (item)
  (declare (xargs :guard t))
  (or (acl2::addressp item)
      (equal nil item)))

(defun no-locked-object ()
  (declare (xargs :guard t))
  nil)

;; We store the method-info in the frame for speed.  It should always be the
;; same as the method-info stored in the class table, but I suppose we don't
;; know that a priori.

;fixme uncomment things below and flesh out
(defund framep (frame)
  (declare (xargs :guard t))
  (and (true-listp frame)
       (equal (len frame) 6)
       (pcp (nth 0 frame)) ;the pc (fixme also must point to an instruction within the program)
       (true-listp (nth 1 frame)) ; todo: what else to say about the locals?
       (operand-stackp (nth 2 frame)) ; todo: what else to say about the operand stack?
       (maybe-addressp (nth 3 frame)) ;the locked-object
       (method-infop (nth 4 frame))
       (method-designatorp (nth 5 frame))))

;Now includes the class name and method name (and descriptor) of the method being invoked (nice to have this info in the trace and for debugging):
(defund make-frame (pc     ;; program counter
                    locals ;; the values of the local variables (do some take two slots?)
                    stack ;;operand stack
                    locked-object ;; the object that was locked if this is a synchronized method, otherwise nil
                    ;; These things should be read-only during the execution of the method:
                    method-info ;;a method-infop (includes static flag, syn flag, program, exception table, etc.)
                    method-designator ; this info isn't used for much (fixme think through the calls of (cur-xxx... ) below. update: now is used by invokespecial!
                    )
  (declare (type t pc locals stack locked-object method-info method-designator))
  (list pc locals stack locked-object method-info method-designator))

(defthm framep-of-make-frame
  (equal (framep (make-frame pc locals stack locked-object method-info method-designator))
         (and (pcp pc)
              (true-listp locals)
              (operand-stackp stack)
              (maybe-addressp locked-object)
              (method-infop method-info)
              (method-designatorp method-designator)))
  :hints (("Goal" :in-theory (enable framep make-frame))))

(defthm equal-of-make-frame-and-make-frame
  (equal (equal (make-frame pc1 locals1 stack1 locked-object1 method-info1 method-designator1)
                (make-frame pc2 locals2 stack2 locked-object2 method-info2 method-designator2))
         (and (equal pc1 pc2)
              (equal locals1 locals2)
              (equal stack1 stack2)
              (equal method-info1 method-info2)
              (equal locked-object1 locked-object2)
              (equal method-designator1 method-designator2)))
  :hints (("Goal" :in-theory (enable make-frame))))

(defund pc                (frame) (declare (xargs :guard (framep frame) :guard-hints (("Goal" :in-theory (enable framep))))) (nth 0 frame))
(defund locals            (frame) (declare (xargs :guard (framep frame) :guard-hints (("Goal" :in-theory (enable framep))))) (nth 1 frame))
(defund stack             (frame) (declare (xargs :guard (framep frame) :guard-hints (("Goal" :in-theory (enable framep))))) (nth 2 frame))
(defund locked-object     (frame) (declare (xargs :guard (framep frame) :guard-hints (("Goal" :in-theory (enable framep))))) (nth 3 frame))
(defund method-info       (frame) (declare (xargs :guard (framep frame) :guard-hints (("Goal" :in-theory (enable framep))))) (nth 4 frame))
(defund method-designator (frame) (declare (xargs :guard (framep frame) :guard-hints (("Goal" :in-theory (enable framep))))) (nth 5 frame))

(defund cur-class-name        (frame) (declare (xargs :guard (framep frame) :guard-hints (("Goal" :in-theory (enable framep method-designatorp method-designator))))) (first  (method-designator frame)))
(defund cur-method-name       (frame) (declare (xargs :guard (framep frame) :guard-hints (("Goal" :in-theory (enable framep method-designatorp method-designator))))) (second (method-designator frame)))
(defund cur-method-descriptor (frame) (declare (xargs :guard (framep frame) :guard-hints (("Goal" :in-theory (enable framep method-designatorp method-designator))))) (third  (method-designator frame)))

(defthm pc-of-make-frame
  (equal (pc (make-frame pc l s locked-object method-info method-designator))
         pc)
  :hints (("Goal" :in-theory (enable make-frame pc))))

(defthm locals-of-make-frame
  (equal (locals (make-frame pc l s locked-object method-info method-designator))
         l)
  :hints (("Goal" :in-theory (enable make-frame locals))))

(defthm stack-of-make-frame
  (equal (stack (make-frame pc l s locked-object method-info method-designator))
         s)
  :hints (("Goal" :in-theory (enable make-frame stack))))

(defthm method-info-of-make-frame
  (equal (method-info (make-frame pc l s locked-object method-info method-designator))
         method-info)
  :hints (("Goal" :in-theory (enable make-frame method-info))))

(defthm locked-object-of-make-frame
  (equal (locked-object (make-frame pc l s locked-object method-info method-designator))
         locked-object)
  :hints (("Goal" :in-theory (enable make-frame locked-object method-info))))

(defthm myif-of-make-frame
  (equal (myif test
               (make-frame pc1 locals1 stack1 locked-object1 method-info1 method-designator1)
               (make-frame pc2 locals2 stack2 locked-object2 method-info2 method-designator2))
         (make-frame (myif test pc1 pc2)
                         (myif test locals1 locals2)
                         (myif test stack1 stack2)
                         (myif test locked-object1 locked-object2)
                         (myif test method-info1 method-info2)
                         (myif test method-designator1 method-designator2)))
  :hints (("Goal" :in-theory (enable myif ))))

(defthm method-designatorp-of-method-designator
  (implies (framep frame)
           (method-designatorp (method-designator frame)))
  :hints (("Goal" :in-theory (enable framep method-designator))))

(defthm method-infop-of-method-info
  (implies (framep frame)
           (method-infop (method-info frame)))
  :hints (("Goal" :in-theory (enable framep method-info))))

(defthm maybe-addressp-of-locked-object
  (implies (framep frame)
           (maybe-addressp (locked-object frame)))
  :hints (("Goal" :in-theory (enable framep locked-object))))

(defthm pcp-of-pc
  (implies (framep frame)
           (PCP (PC frame)))
  :hints (("Goal" :in-theory (enable framep pc))))

(defthm operand-stackp-of-stack
  (implies (framep frame)
           (operand-stackp (stack frame)))
  :hints (("Goal" :in-theory (enable framep stack))))

(defthm method-designator-of-make-frame
  (equal (method-designator (make-frame pc l s locked-object method-info method-designator))
         method-designator)
    :hints (("Goal" :in-theory (enable make-frame method-designator))))

(defthm len-of-make-frame
  (equal (len (make-frame pc locals stack locked-object method-info method-designator))
         6)
  :hints (("Goal" :in-theory (enable make-frame))))

;(defthmd true-listp-when-framep

(defthm true-listp-of-locals
  (implies (framep frame)
           (true-listp (locals frame)))
  :hints (("Goal" :in-theory (enable framep locals))))

;gross?
(defthm make-frame-equal-rewrite-2
  (equal (equal frame (make-frame pc locals stack locked-object method-info method-designator))
         (and (true-listp frame)
              (equal 6 (len frame))
              (equal (pc frame) pc)
              (equal (locals frame) locals)
              (equal (stack frame) stack)
              (equal (locked-object frame) locked-object)
              (equal (method-info frame) method-info)
              (equal (method-designator frame) method-designator)))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (make-frame framep pc locals stack method-info locked-object
                                       method-designator
                                       ;;acl2::consp-cdr
                                       ACL2::CAR-BECOMES-NTH-OF-0
                                       acl2::nth-of-cdr
                                       ;;acl2::CDR-OF-CDR-BECOMES-NTHCDR
                                       )
                           (len nth)))))
