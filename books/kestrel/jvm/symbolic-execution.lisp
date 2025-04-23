; Symbolic execution using run-until-return and run-until-return-from-stack-height
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "symbolic-execution-common")

;BBOZO think about this stuff

;move these?

;fixme pull most of this into a function and prove that that function returns a well-formed state?
;fixme better way to catch the return value from the bottommost frame?
;fixme maybe the dummy frame is not needed anymore?
;todo: pass in th
(defund build-make-state-for-method (class-name
                                     method-name
                                     method-descriptor ; a string
                                     method-info
                                     locals
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

(defthm pseudo-termp-of-build-make-state-for-method
  (implies (and (jvm::method-namep method-name)
                (jvm::method-descriptorp method-descriptor)
                (jvm::method-infop method-info)
                (jvm::class-namep class-name)
                (pseudo-termp locals)
                (pseudo-termp heap)
                (pseudo-termp class-table)
                (pseudo-termp initial-static-field-map)
                (pseudo-termp initialized-classes)
                (natp pc)
                (pseudo-termp intern-table))
           (pseudo-termp (build-make-state-for-method class-name
                                                      method-name
                                                      method-descriptor
                                                      method-info
                                                      locals
                                                      heap class-table initial-static-field-map initialized-classes pc intern-table)))
  :hints (("Goal" :in-theory (enable build-make-state-for-method))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: transition everything to use build-run-term-for-method2 instead of this (but some axe examples need to be updated to call unroll-java-code)
(defund build-run-term-for-method ( ;method-name TODO: add back these parameters
                                  ;;method-descriptor ; a string
                                  method-info locals class-name heap class-table initialized-classes)
  (declare (xargs :guard (and (jvm::method-infop method-info)
                              (jvm::class-namep class-name)
                              (pseudo-termp locals)
                              (pseudo-termp heap)
                              (pseudo-termp class-table)
                              (pseudo-termp initialized-classes))))
  `(run-until-return ,(build-make-state-for-method class-name
                                                   "FAKE" ;ffffixme: a fake method-name
                                                   "()V" ;ffffixme: a fake method-descriptor
                                                   method-info locals heap class-table
                                                   *nil* ;fixme this is the initial-static-field-map ;fixme, avoid setting this to nil, now that interned strings are not here?
                                                   initialized-classes '0
;*nil* ;don't ignore errors (fixme this was wrong, so the var nil was introduced into the term!)
                                                   '(jvm::empty-intern-table) ;fixme. generalize this (may need an invariant that addresses of interned strings really hold the correct string objects):
                                                   )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;fixme convert everything to use this?
(defund build-run-term-for-method2 (method-name
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
  `(run-until-return ,(build-make-state-for-method class-name
                                                   method-name
                                                   method-descriptor ; a string
                                                   method-info locals heap class-table
                                                   initial-static-field-map
                                                   initialized-classes '0
                                                   ;;*nil* ;don't ignore errors (fixme this was wrong, so the var nil was introduced into the term!)
                                                   intern-table
                                                   )))

(defthm pseudo-termp-of-build-run-term-for-method2
  (implies (and (jvm::method-namep method-name)
                (jvm::method-descriptorp method-descriptor)
                (jvm::method-infop method-info)
                (jvm::class-namep class-name)
                (pseudo-termp locals)
                (pseudo-termp heap)
                (pseudo-termp class-table)
                (pseudo-termp initial-static-field-map)
                (pseudo-termp initialized-classes)
                (pseudo-termp intern-table))
           (pseudo-termp (build-run-term-for-method2 method-name method-descriptor method-info locals class-name heap class-table initial-static-field-map initialized-classes intern-table)))
  :hints (("Goal" :in-theory (enable build-run-term-for-method2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund build-run-n-steps-term-for-method (steps
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
  `(jvm::run-n-steps ',steps ,(build-make-state-for-method class-name
                                                           method-name
                                                           method-descriptor ; a string
                                                           method-info locals heap class-table
                                                           initial-static-field-map
                                                           initialized-classes '0
;*nil* ;don't ignore errors (fixme this was wrong, so the var nil was introduced into the term!)
                                                           intern-table
                                                           )))

(defthm pseudo-termp-of-build-run-n-steps-term-for-method
  (implies (and (natp steps)
                (jvm::method-namep method-name)
                (jvm::method-descriptorp method-descriptor)
                (jvm::class-namep class-name)
                (jvm::method-infop method-info)
                (pseudo-termp locals)
                (pseudo-termp heap)
                (pseudo-termp class-table)
                (pseudo-termp initial-static-field-map)
                (pseudo-termp initialized-classes)
                (pseudo-termp intern-table))
           (pseudo-termp (build-run-n-steps-term-for-method steps
                                                            method-name
                                                            method-descriptor
                                                            method-info
                                                            locals
                                                            class-name
                                                            heap
                                                            class-table
                                                            initial-static-field-map
                                                            initialized-classes
                                                            intern-table)))
  :hints (("Goal" :in-theory (enable build-run-n-steps-term-for-method))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;; throw exception cannot increase the call stack size (it may decrease it while looking for a handler).
;move
(defthmd <=-of-call-stack-size-of-binding-of-thread-table-of-throw-exception
  (<= (jvm::call-stack-size (jvm::binding th (jvm::thread-table (jvm::throw-exception objectref objectref-class th s))))
      (jvm::call-stack-size (jvm::binding th (jvm::thread-table s))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (jvm::throw-exception) (jvm::step-opener)))))

;guard to require enough frames?
(defund jvm::popn-frames (n stack)
  (declare (xargs :guard (and (natp n) (jvm::call-stackp stack))))
  (if (zp n)
      stack
    (jvm::popn-frames (+ -1 n) (jvm::pop-frame stack))))

(defthm popn-frames-of-0
  (equal (jvm::popn-frames 0 stack)
         stack)
  :hints (("Goal" :in-theory (enable jvm::popn-frames))))

(defthm popn-frames-opener
  (implies (and (syntaxp (quotep n))
                (posp n))
           (equal (jvm::popn-frames n stack)
                  (jvm::popn-frames (+ -1 n) (jvm::pop-frame stack))))
  :hints (("Goal" :in-theory (enable jvm::popn-frames))))

(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;;todo: call-stack vs jvm::call-stack

;;like throw-exception but with n added
(local
 (defun ind-throw-exception (n objectref objectref-class th s)
   (declare (xargs :measure (jvm::call-stack-size (jvm::call-stack th s))))
   (if (jvm::empty-call-stackp (jvm::call-stack th s))
       (list n objectref objectref-class th s) ;fake
     (let* ((frame (jvm::thread-top-frame th s))
            (pc (jvm::pc frame))
            (method-info (jvm::method-info frame))
            (exception-table (jvm::exception-table method-info))
            (class-table (jvm::class-table s))
            (exception-handler-pc (jvm::find-exception-handler exception-table pc objectref-class class-table)))
       (if exception-handler-pc
           (jvm::modify th s
                        :pc exception-handler-pc
                        :stack (jvm::push-operand objectref (jvm::empty-operand-stack)))
         ;; No exception handler found in this method, so pop the frame and rethrow:
         (if (jvm::locked-object frame)
             ;; There is an object to be unlocked (fixme, does all this apply to frames below the first one?)
             (let ((locked-object (jvm::addressfix (jvm::locked-object frame)))) ;drop the addressfix...
               (if (not (jvm::thread-owns-monitorp th locked-object (jvm::monitor-table s)))
                   ;; todo: call obtain-and-throw-exception here?
                   (jvm::error-state (list jvm::*IllegalMonitorStateException* :athrow) s)
                 (let ((s (jvm::modify th s
                                       :call-stack (jvm::pop-frame (jvm::call-stack th s))
                                       :monitor-table (jvm::decrement-mcount (jvm::addressfix (jvm::locked-object frame)) (jvm::monitor-table s)))))
                   (ind-throw-exception (+ -1 n) objectref objectref-class th s))))
           (let* ((s (jvm::modify th s
                                  :call-stack (jvm::pop-frame (jvm::call-stack th s)))))
             (ind-throw-exception (+ -1 n) objectref objectref-class th s))))))))

(local
 (defthm step-state-with-pc-and-call-stack-height-of-throw-exception-helper
   (implies (and
             (<= call-stack-size (jvm::call-stack-size (jvm::binding (th) (jvm::thread-table s))))
             (posp call-stack-size)
             (equal diff (- (jvm::call-stack-size (jvm::binding (th) (jvm::thread-table s))) call-stack-size))
             ;; We are being asked to step a state at a height that does
             ;; correspond to a real frame but whose PC is not among the
             ;; exception handlers in the frame at that height (the places where
             ;; throw-exception might leave the state):
             (not (member-equal pc (jvm::exception-handler-targets
                                    (lookup-equal :exception-table (jvm::method-info
                                                                    (jvm::top-frame
                                                                     (jvm::popn-frames diff
                                                                                       (jvm::binding (th)
                                                                                                     (jvm::thread-table s))))))))))
            (equal (step-state-with-pc-and-call-stack-height pc call-stack-size (jvm::throw-exception objectref objectref-class (th) s))
                   (jvm::throw-exception objectref objectref-class (th) s)))
   :hints (("Goal" :induct (ind-throw-exception diff objectref objectref-class (th) s)
            :expand ((jvm::throw-exception objectref objectref-class (th) s))
            :in-theory (e/d (jvm::throw-exception step-state-with-pc-and-call-stack-height <=-of-call-stack-size-of-binding-of-thread-table-of-throw-exception
                                                  jvm::popn-frames)
                            (true-listp jvm::thread-owns-monitorp jvm::step-opener))))))

;drop?
(local
 (defthm step-state-with-pc-and-call-stack-height-of-throw-exception-helper-2
   (implies (and
             (< (jvm::call-stack-size (jvm::binding (th) (jvm::thread-table s))) call-stack-size)
             (posp call-stack-size))
            (equal (step-state-with-pc-and-call-stack-height pc call-stack-size (jvm::throw-exception objectref objectref-class (th) s))
                   (jvm::throw-exception objectref objectref-class (th) s)))
   :hints (("Goal" ; :induct (ind-throw-exception diff objectref objectref-class (th) s)
            :expand ((jvm::throw-exception objectref objectref-class (th) s))
            :in-theory (e/d (jvm::throw-exception step-state-with-pc-and-call-stack-height <=-of-call-stack-size-of-binding-of-thread-table-of-throw-exception
                                                  jvm::popn-frames)
                            (true-listp jvm::thread-owns-monitorp jvm::step-opener))))))

(defthm step-state-with-pc-and-call-stack-height-of-throw-exception
  (implies (and (posp call-stack-size)
                ;; Either we are being asked to step a state in a frame that
                ;; would be above the current top frame, or we are being asked
                ;; to step a state at a height that does correspond to a real
                ;; frame BUT with a PC that is not among the exception handlers
                ;; (where throw-exception might leave the state):
                (or (< (jvm::call-stack-size (jvm::binding (th) (jvm::thread-table s))) call-stack-size)
                    (not (member-equal pc (jvm::exception-handler-targets
                                           (lookup-equal :exception-table (jvm::method-info
                                                                           (jvm::top-frame
                                                                            (jvm::popn-frames (- (jvm::call-stack-size (jvm::binding (th) (jvm::thread-table s))) call-stack-size)
                                                                                              (jvm::binding (th)
                                                                                                            (jvm::thread-table s)))))))))))
           (equal (step-state-with-pc-and-call-stack-height pc call-stack-size (jvm::throw-exception objectref objectref-class (th) s))
                  (jvm::throw-exception objectref objectref-class (th) s)))
  :hints (("Goal" :use (:instance step-state-with-pc-and-call-stack-height-of-throw-exception-helper
                                  (diff (- (jvm::call-stack-size (jvm::binding (th) (jvm::thread-table s))) call-stack-size))))))

;; Helps prevent large nests of step-state-with-pc-and-call-stack-height around exception states.
(defthm step-state-with-pc-and-call-stack-height-of-obtain-and-throw-exception
  (implies (and (and (posp call-stack-size)
                     ;; Either we are being asked to step a state in a frame that
                     ;; would be above the current top frame, or we are being asked
                     ;; to step a state at a height that does correspond to a real
                     ;; frame BUT with a PC that is not among the exception handlers
                     ;; (where throw-exception might leave the state):
                     ;; should be easy to resolve:
                     (or (< (jvm::call-stack-size (jvm::binding (th) (jvm::thread-table s))) call-stack-size)
                         (not (member-equal pc (jvm::exception-handler-targets
                                                (lookup-equal :exception-table (jvm::method-info
                                                                                (jvm::top-frame
                                                                                 (jvm::popn-frames (- (jvm::call-stack-size (jvm::binding (th) (jvm::thread-table s)))
                                                                                                      call-stack-size)
                                                                                                   (jvm::binding (th)
                                                                                                                 (jvm::thread-table s)))))))))))
                (jvm::class-namep exception-class-name) ; drop?
                )
           (equal (step-state-with-pc-and-call-stack-height pc call-stack-size (jvm::obtain-and-throw-exception exception-class-name debug-info (th) s))
                  (jvm::obtain-and-throw-exception exception-class-name debug-info (th) s)))
  :hints (("Goal" :in-theory (enable jvm::obtain-and-throw-exception))))
