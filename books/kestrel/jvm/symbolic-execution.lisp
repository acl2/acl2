; Symbolic execution using run-until-return and run-until-return-from-stack-height
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

;BBOZO think about this stuff

;FIXME: verify-guards !

;move these?

;fixme pull most of this into a function and prove that that function returns a well-formed state?
;fixme better way to catch the return value from the bottommost frame?
;fixme maybe the dummy frame is not needed anymore?
;todo: pass in th
(defun build-make-state-for-method (method-name
                                    method-descriptor ; a string
                                    method-info
                                    locals
                                    class-name ;todo: put this before the locals?
                                    heap class-table initial-static-field-map initialized-classes pc intern-table)
  (declare (xargs :guard (and (jvm::method-namep method-name)
                              (jvm::method-descriptorp method-descriptor)
                              (jvm::method-infop method-info)
                              (jvm::class-namep class-name)
                              (pseudo-termp locals)
                              (pseudo-termp heap)
                              (pseudo-termp class-table)
                              (pseudo-termp initial-static-field-map)
                              (pseudo-termp initialized-classes)
                              (natp pc)
                              (pseudo-termp intern-table))))
  (let* ((staticp (jvm::method-staticp method-info))
         (inst (if staticp :invokestatic :invokevirtual)))
    `(jvm::make-state
      (jvm::bind (th)
                 (jvm::push-frame (jvm::make-frame ',pc
                                                    ,locals
                                                    ',(jvm::empty-operand-stack)
                                                    ',(jvm::no-locked-object) ;ffixme
                                                    ',method-info ;we quote the method info
                                                    ',(jvm::make-method-designator class-name method-name method-descriptor))
                                   (jvm::push-frame ;this is used only for catching the result and knowing how much to increment the PC upon return (but the invoke instruction is kind of fake here - we just use invokevirtual)
                                    (jvm::make-frame '0
                                                     frame2-locals
                                                     frame2-operand-stack
                                                     frame2-locked-object ;ffixme
                                                     ;;fake program, so that return sees the invoke:
                                                     (acons ':program '((0 ,inst :fake-for-build-make-state-for-method :fake-for-build-make-state-for-method :fake-for-build-make-state-for-method 0 :fake)) frame2-method-info)
                                                     frame2-method-designator
                                                     )
                                    call-stack))
                 'nil ;fixme use empty-thread-table?
                 )
      ,heap
      ,class-table
      initial-heapref-table
      initial-monitor-table
      ,initial-static-field-map
      ,initialized-classes
      ,intern-table)))

;todo: transition everything to use build-run-term-for-method2 instead of this (but some axe examples need to be updated to call unroll-java-code)
(defun build-run-term-for-method ( ;method-name TODO: add back these parameters
                                  ;;method-descriptor ; a string
                                  method-info locals class-name heap class-table initialized-classes)
  (declare (xargs :guard (and  (jvm::method-infop method-info)
                               (jvm::class-namep class-name)
                               (pseudo-termp locals)
                              (pseudo-termp heap)
                              (pseudo-termp class-table)
                              (pseudo-termp initialized-classes))))
  `(run-until-return ,(build-make-state-for-method "FAKE" ;ffffixme: a fake method-name
                                                   "()V" ;ffffixme: a fake method-descriptor
                                                   method-info locals class-name heap class-table
                                                   *nil* ;fixme this is the initial-static-field-map ;fixme, avoid setting this to nil, now that interned strings are not here?
                                                   initialized-classes '0
;*nil* ;don't ignore errors (fixme this was wrong, so the var nil was introduced into the term!)
                                                   '(jvm::empty-intern-table) ;fixme. generalize this (may need an invariant that addresses of interned strings really hold the correct string objects):
                                                   )))

;fixme convert everything to use this?
(defun build-run-term-for-method2 (method-name
                                   method-descriptor ; a string
                                   method-info
                                   locals
                                   class-name ;todo put this before the locals
                                   heap class-table initial-static-field-map initialized-classes intern-table)
  (declare (xargs :guard (and (jvm::method-namep method-name)
                              (jvm::method-descriptorp method-descriptor)
                              (jvm::method-infop method-info)
                              (jvm::class-namep class-name)
                              (pseudo-termp locals)
                              (pseudo-termp heap)
                              (pseudo-termp class-table)
                              (pseudo-termp initial-static-field-map)
                              (pseudo-termp initialized-classes)
                              (pseudo-termp intern-table))))
  `(run-until-return ,(build-make-state-for-method method-name
                                                   method-descriptor ; a string
                                                   method-info locals class-name heap class-table
                                                   initial-static-field-map
                                                   initialized-classes '0
                                                   ;;*nil* ;don't ignore errors (fixme this was wrong, so the var nil was introduced into the term!)
                                                   intern-table
                                                   )))

(defun build-run-n-steps-term-for-method (steps
                                          method-name
                                          method-descriptor ; a string
                                          method-info
                                          locals
                                          class-name
                                          heap
                                          class-table
                                          initial-static-field-map
                                          initialized-classes
                                          intern-table)
  (declare (xargs :guard (and (natp steps)
                              (jvm::method-namep method-name)
                              (jvm::method-descriptorp method-descriptor)
                              (jvm::class-namep class-name)
                              (jvm::method-infop method-info)
                              (pseudo-termp locals)
                              (pseudo-termp heap)
                              (pseudo-termp class-table)
                              (pseudo-termp initial-static-field-map)
                              (pseudo-termp initialized-classes)
                              (pseudo-termp intern-table))))
  `(jvm::run-n-steps ',steps ,(build-make-state-for-method method-name
                                                           method-descriptor ; a string
                                                           method-info locals class-name heap class-table
                                                           initial-static-field-map
                                                           initialized-classes '0
;*nil* ;don't ignore errors (fixme this was wrong, so the var nil was introduced into the term!)
                                                           intern-table
                                                           )))

;;;
;;; step-state-with-pc-and-call-stack-height
;;;

;deprecate in favor of checking the whole call stack?
(defund step-state-with-pc-and-call-stack-height (pc call-stack-height s)
  (if (and (equal pc (jvm::pc (jvm::thread-top-frame (th) s)))
           (equal call-stack-height (jvm::call-stack-size (jvm::call-stack (th) s))))
      (jvm::step (th) s)
    s))

;; We always push step-state-with-pc-and-call-stack-height to the leaves of the nest.
(defthm step-state-with-pc-and-call-stack-height-of-myif
  (equal (step-state-with-pc-and-call-stack-height pc call-stack-height (myif test s1 s2))
         (myif test
               (step-state-with-pc-and-call-stack-height pc call-stack-height s1)
               (step-state-with-pc-and-call-stack-height pc call-stack-height s2)))
  :hints (("Goal" :in-theory (enable myif))))

;; Only applies when S is a make-state.
(defthm step-state-with-pc-and-call-stack-height-becomes-step
  (implies (and (syntaxp (call-of 'jvm::make-state s))
                (equal pc (jvm::pc (jvm::thread-top-frame (th) s)))
                (equal call-stack-height
                       (jvm::call-stack-size (jvm::call-stack (th) s))))
           (equal (step-state-with-pc-and-call-stack-height pc call-stack-height s)
                  (jvm::step (th) s)))
  :hints (("Goal" :in-theory (enable step-state-with-pc-and-call-stack-height))))

;; Only applies when S is a make-state.
(defthm step-state-with-pc-and-call-stack-height-does-nothing-1
  (implies (and (syntaxp (call-of 'jvm::make-state s))
                (not (equal pc (jvm::pc (jvm::thread-top-frame (th) s)))))
           (equal (step-state-with-pc-and-call-stack-height pc call-stack-height s)
                  s))
  :hints (("Goal" :in-theory (enable step-state-with-pc-and-call-stack-height))))

;; Only applies when S is a make-state.
(defthm step-state-with-pc-and-call-stack-height-does-nothing-2
  (implies (and (syntaxp (call-of 'jvm::make-state s))
                (not (equal call-stack-height
                            (jvm::call-stack-size (jvm::call-stack (th) s)))))
           (equal (step-state-with-pc-and-call-stack-height pc call-stack-height s)
                  s))
  :hints (("Goal" :in-theory (enable step-state-with-pc-and-call-stack-height))))
