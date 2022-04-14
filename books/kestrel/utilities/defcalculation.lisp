; A simple tool to support calculational-style proofs
;
; Copyright (C) 2016-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A simple tool to support calculational-style proofs (currently, chaining
;; together equality steps).

;; TODO: Does something like this already exist?  See J's DFT tool in books/misc/dft.lisp.
;; TODO: Add support for < and <=
;; TODO: Add support for rule classes
;; TODO: Decide what the syntax should be (steps in a list, or flat?), especially when < and <= become supported.

(include-book "kestrel/utilities/pack" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "split-keyword-args")

(defun defcalculation-steps (current steps base-name prev-step-count orig assumptions)
  (if (endp steps)
      nil
    (let* ((step (first steps))
           (term (cadr step)) ;strip off the equal (TODO: handle < and <=
           (keyword-alist (cddr step))
           (hints (assoc-keyword :hints keyword-alist))
           (this-step-num (+ 1 prev-step-count))
           (this-step-theorem (pack$ base-name '-step- this-step-num))
           (this-chain-theorem (pack$ base-name '-chain- this-step-num))
           (prev-chain-theorem (if (zp prev-step-count)
                                   nil
                                 (pack$ base-name '-chain- prev-step-count)))
           (thms `(;; TODO: Add support for hints
                   (defthm ,this-step-theorem
                     (implies (and ,@assumptions)
                              (equal ,current
                                     ,term))
                     ,@hints
                     :rule-classes nil)
                   (defthm ,this-chain-theorem
                     (implies (and ,@assumptions)
                              (equal ,orig
                                     ,term))
                     :hints (("Goal" :use (,@(and prev-chain-theorem
                                                  `((:instance ,prev-chain-theorem)))
                                           (:instance ,this-step-theorem))
                              :in-theory nil))
                     :rule-classes nil))))
      (append thms
              (defcalculation-steps term (rest steps) base-name (+ 1 prev-step-count) orig assumptions)))))



;assumes all steps are equalities
(defun defcalculation-fn (name args)
  (b* (;; Split the args into start, steps, and options:
       ((mv start-and-steps keyword-alist)
        (split-keyword-args args))
       (assumptions (cadr (assoc-keyword :assumptions keyword-alist)))
       ;; TODO: Check that there is a start and at least 1 step
       ;; TODO: Check the format of the steps
       (start (first start-and-steps))
       (steps (rest start-and-steps))
;TODO suppress implies in the events if no assumptions
       (step-events (defcalculation-steps start steps (pack$ name '-calculation) 0 start assumptions)))
    `(progn ,@step-events
            (defthm ,name
              (implies (and ,@assumptions)
                       (equal ,start
                              ;;get last step and strip off =
                              ,(cadr (car (last steps)))))
;              :rule-classes nil
              :hints (("Goal" :use (:instance ,(pack$ name '-calculation '-chain- (len steps)))))))))

(defmacro defcalculation (name &rest args)
  `(make-event (defcalculation-fn ',name ',args)))
