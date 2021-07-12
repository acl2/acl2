; Mote symbolic execution machinery
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "symbolic-execution-common")
(include-book "pc-designators")
(include-book "misc/defp" :dir :system) ;drop?
(local (include-book "kestrel/lists-light/len" :dir :system))

;; Only used by the loop lifter?

;;;
;;; get-pc-designator-stack-from-call-stack
;;;

(defund get-pc-designator-stack-from-call-stack (call-stack)
  (declare (xargs :guard (and (jvm::call-stackp call-stack)
                              (all-framep call-stack) ;drop someday
                              )
                  :measure (jvm::call-stack-size call-stack)))
  (if (jvm::empty-call-stackp call-stack)
      nil ;error
    (cons (get-pc-designator-from-frame (jvm::top-frame call-stack))
          (get-pc-designator-stack-from-call-stack (jvm::pop-frame call-stack)))))

(defthm consp-of-get-pc-designator-stack-from-call-stack
  (equal (consp (get-pc-designator-stack-from-call-stack call-stack))
         (not (jvm::empty-call-stackp call-stack)))
  :hints (("Goal" :in-theory (enable get-pc-designator-stack-from-call-stack))))

(defthm len-of-get-pc-designator-stack-from-call-stack
  (equal (len (get-pc-designator-stack-from-call-stack call-stack))
         (jvm::call-stack-size call-stack))
  :hints (("Goal" :in-theory (e/d (get-pc-designator-stack-from-call-stack)
                                  (;get-pc-designator-stack-from-call-stack-of-pop-frame ;looped?
                                   )))))

(defthmd get-pc-designator-stack-from-call-stack-of-pop-frame
  (equal (get-pc-designator-stack-from-call-stack (jvm::pop-frame call-stack))
         (cdr (get-pc-designator-stack-from-call-stack call-stack)))
  :hints (("Goal" :in-theory (enable get-pc-designator-stack-from-call-stack jvm::call-stack-size jvm::pop-frame))))

(defthmd get-pc-designator-stack-from-call-stack-of-push-frame
  (equal (get-pc-designator-stack-from-call-stack (jvm::push-frame frame call-stack))
         (cons (get-pc-designator-from-frame frame)
               (get-pc-designator-stack-from-call-stack call-stack)))
  :hints (("Goal" :in-theory (enable get-pc-designator-stack-from-call-stack
                                     jvm::empty-call-stackp
                                     jvm::call-stack-size))))

;;;
;;; pc-designator-stack-of-state
;;;

(defun pc-designator-stack-of-state (s)
  ;; (declare (xargs :guard (and (jvm::jvm-statep s)
  ;;                             (jvm::bound-in-alistp (th)
  ;;                                                   (jvm::thread-table s)))))
  (get-pc-designator-stack-from-call-stack (jvm::binding (th) (jvm::thread-table s))))

;;
;; step-state-with-pc-designator-stack
;;

;;  If the state has the stack of pc-designator-stack we are looking for, step it.  Otherwise, do nothing.
(defund step-state-with-pc-designator-stack (pc-designator-stack s)
  (if (equal pc-designator-stack (pc-designator-stack-of-state s))
      (jvm::step (th) s)
    s))

;; We always push step-state-with-pc-designator-stack to the leaves of the nest.
(defthm step-state-with-pc-designator-stack-of-myif
  (equal (step-state-with-pc-designator-stack pc-designator-stack (myif test s1 s2))
         (myif test
               (step-state-with-pc-designator-stack pc-designator-stack s1)
               (step-state-with-pc-designator-stack pc-designator-stack s2)))
  :hints (("Goal" :in-theory (enable myif))))

;; We could perhaps combine these next two, perhaps with a non-splitting IF in the RHS (only resolvable if the test is a constant?)

;; Only applies when S is a make-state.
(defthm step-state-with-pc-designator-stack-becomes-step
  (implies (and (syntaxp (call-of 'jvm::make-state s))
                (equal pc-designator-stack (pc-designator-stack-of-state s)))
           (equal (step-state-with-pc-designator-stack pc-designator-stack s)
                  (jvm::step (th) s)))
  :hints (("Goal" :in-theory (enable step-state-with-pc-designator-stack))))

;; Only applies when S is a make-state.
(defthm step-state-with-pc-designator-stack-does-nothing
  (implies (and (syntaxp (call-of 'jvm::make-state s))
                (not (equal pc-designator-stack (pc-designator-stack-of-state s))))
           (equal (step-state-with-pc-designator-stack pc-designator-stack s)
                  s))
  :hints (("Goal" :in-theory (enable step-state-with-pc-designator-stack))))

;move some of these:

;see also NOT-EQUAL-WHEN-LENS-DIFFER
;; (defthm not-equal-of-cons-and-cons-when-lens-differ
;;   (implies (not (equal (len x) (len y)))
;;            (not (equal (cons a x) (cons b y)))))

;; used by the lifter
(defthm not-equal-of-cons-and-cons-when-lens-differ
  (implies (not (equal (len x) (len y)))
           (not (equal (cons a x) (cons b y)))))

;drop?
;; (defthm not-empty-call-stackp-when-<-of-len
;;   (implies (and (< k (len call-stack))
;;                 (natp k))
;;            (not (jvm::empty-call-stackp call-stack)))
;;   :hints (("Goal" :in-theory (enable jvm::empty-call-stackp jvm::call-stack-size))))

;; (defthm not-empty-call-stackp-when-<-of-call-stack-size
;;   (implies (and (< k (jvm::call-stack-size call-stack))
;;                 (natp k))
;;            (not (jvm::empty-call-stackp call-stack)))
;;   :hints (("Goal" :in-theory (enable jvm::empty-call-stackp))))

;; This is really more general
(defthm not-equal-of-zero-and-call-stack-size-<-of-call-stack-size
  (implies (and (< k (jvm::call-stack-size call-stack))
                (natp k))
           (not (equal 0 (jvm::call-stack-size call-stack))))
  :hints (("Goal" :in-theory (enable jvm::empty-call-stackp))))

;; (defthm len-of-pop-frame
;;   (implies (not (jvm::empty-call-stackp call-stack))
;;            (equal (len (jvm::pop-frame call-stack))
;;                   (+ -1 (len call-stack))))
;;   :hints (("Goal" :in-theory (enable jvm::pop-frame
;;                                      jvm::empty-call-stackp))))
