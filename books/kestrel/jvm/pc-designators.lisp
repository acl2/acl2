; Indicating code locations within collections of classes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ;todo: use jvm package?

(include-book "execution-common") ;for th

;;;
;;; pc-designatorp
;;;

;; A pc-designator designates a particular program location within a collection of
;; classes.  It is a tuple of the class name, the method name, the method descriptor,
;; and the program counter.
;; Example: ("com.foo.bar.ClassName" "methodname" "(I)I" 20)
(defun pc-designatorp (des)
  (declare (xargs :guard t))
  (and (true-listp des)
       (eql 4 (len des))
       (jvm::class-namep (first des))
       (jvm::method-namep (second des))
       (jvm::method-descriptorp (third des))
       (jvm::pcp (fourth des))))

(defund make-pc-designator (class-name method-name method-descriptor pc)
  (declare (xargs :guard (and (jvm::class-namep class-name)
                              (jvm::method-namep method-name)
                              (jvm::method-descriptorp method-descriptor)
                              (jvm::pcp pc))))
  (list class-name method-name method-descriptor pc))

;an accessor
(defund pc-designator-pc (pc-designator)
  (declare (xargs :guard (pc-designatorp pc-designator)))
  (fourth pc-designator))

(defthm rationalp-of-pc-designator-pc
  (implies (pc-designatorp pc-designator)
           (rationalp (pc-designator-pc pc-designator)))
  :hints (("Goal" :in-theory (enable pc-designator-pc pc-designatorp))))

;;;
;;; get-pc-designator-from-frame
;;;

(defun get-pc-designator-from-frame (frame)
  (declare (xargs :guard (jvm::framep frame)))
  (make-pc-designator (jvm::cur-class-name frame)
                      (jvm::cur-method-name frame)
                      (jvm::cur-method-descriptor frame)
                      (jvm::pc frame)))

;; ;; Just look at the top frame
;; (defun get-pc-designator-from-call-stack (call-stack)
;;   (declare (xargs :guard (and (jvm::call-stackp call-stack)
;;                               (all-framep call-stack) ;drop someday
;;                               )
;;                   :hints (("Goal" :in-theory (enable JVM::POP-FRAME JVM::EMPTY-CALL-STACKP))) ;todo
;;                   ))
;;   (if (jvm::empty-call-stackp call-stack)
;;       nil ;error
;;     (get-pc-designator-from-frame (jvm::top-frame call-stack))))

;;;
;;; get-pc-designator-from-state
;;;

;; Used to tell whether the state is at a loop header.
(defun get-pc-designator-from-state (s)
  (get-pc-designator-from-frame (jvm::thread-top-frame (th) s)))
