; A formal model of the JVM
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Note: Portions of this directory may be taken from books/models/jvm/m5.  See the
; LICENSE file and authorship information there as well.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "states")
(local (include-book "kestrel/sequences/defforall" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/bv/bvchop" :dir :system))

;Eric made major modifications to the book m5.lisp by J Strother Moore, George Porter, Robert Krug, and Hanbing Liu

;one improvement: less stuff computed at runtime when we know it statically (e.g., the length of an instruction, the initial values of array elements, etc.)
;the heap is now a map
;heap addresses (refs) are now just integers, not things like: (ref -1)
;heap uses the getfield/setfield interface
;static fields are no longer stored in the heap (led to aliasing issues) but rather a separate component of the state
;the next-adr function is guaranteed to return a fresh address
;new class file parser
;most values stored as unsigned bit vectors - large library of lemmas about bit-vectors available
;improvements on  ;SET-ELEMENT-AT? probably lots of other stuff at this level of detail
;now checks for some exceptions

;FIXME Finish adding support for floating-point (see floats.lisp and floats2.lisp).
;FIXME the stuff relating to threads and locks in this book may be wrong / out-of-date
;FIXME add real exception throwing in lots of places (check for null lots of places, etc.)

;TODO: Add and verify guards.

;fixme: for things like IADD, make sure the bit patterns are the same regardless of whether the operands are signed or unsigned

(defthm class-name-listp-of-reverse-list
  (equal (class-name-listp (acl2::reverse-list x))
         (class-name-listp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable class-name-listp acl2::reverse-list true-list-fix))))


(in-theory (disable true-listp)) ; prevent inductions

(defthm jvm-instruction-okayp-when-framep-helper
  (implies (framep frame)
           (jvm-instruction-okayp (lookup-equal (pc frame) (method-program (method-info frame)))
                                  (pc frame)
                                  (strip-cars (method-program (method-info frame)))))
  :hints (("Goal" :in-theory (enable framep method-infop method-info method-programp method-program pc pcp))))

;Get the instruction at the current PC.
(defun current-inst (th s)
   (declare (xargs :guard (and (thread-designatorp th)
                               (jvm-statep s)
                               (bound-in-alistp th (thread-table s))
                               (call-stack-non-emptyp th s))))
  (let ((top-frame (thread-top-frame th s)))
    (lookup (pc top-frame) (method-program (method-info top-frame)))))

(defthm jvm-instruction-okayp-helper
  (implies (and (jvm-statep s)
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th)
                (call-stack-non-emptyp th s))
           (jvm-instruction-okayp (current-inst th s)
                                  (pc (top-frame (binding th (thread-table s))))
                                  (strip-cars (method-program (method-info (top-frame (binding th (thread-table s)))))))))

(defthm memberp-of-pc-and-strip-cars-of-method-program-of-method-info
  (implies (framep frame)
           (memberp (pc frame) (strip-cars (method-program (method-info frame)))))
  :hints (("Goal" :in-theory (enable framep pc method-info))))

;memberp version ; todo
(defthmd method-programp-key-property-2
  (implies (and (method-programp program)
                (memberp pc (strip-cars program))
                (not (member-equal (instruction-opcode (lookup-eq pc program)) *program-enders*)))
           (memberp (+ pc (inst-len (lookup-eq pc program)))
                    (strip-cars program)))
  :hints (("Goal" :use (:instance method-programp-key-property)
                  :in-theory (disable method-programp-key-property))))

;; allows k to be a constant
(defthmd method-programp-key-property-2-alt
  (implies (and (equal k (inst-len (lookup-eq pc program)))
                (method-programp program)
                (memberp pc (strip-cars program))
                (not (member-equal (instruction-opcode (lookup-eq pc program)) *program-enders*)))
           (memberp (+ k pc) (strip-cars program)))
  :hints (("Goal" :use (method-programp-key-property-2)
                  :in-theory (disable method-programp-key-property-2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable true-listp))) ; prevent induction

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The modify macro

(defun suppliedp (key args)
  (declare (xargs :guard (and (keywordp key)
                              (keyword-value-listp args))))
  (cond ((endp args) nil)
        ((eq key (first args)) t)
        (t (suppliedp key (cddr args)))))

;call assoc-keyword in this? they're not quite the same.
(defun actual (key args)
  (declare (xargs :guard (keyword-value-listp args)
                  :guard-hints (("Goal" :in-theory (enable keyword-value-listp)))))
  (cond ((endp args) nil)
        ((eq key (car args)) (cadr args))
        (t (actual key (cddr args)))))

(defun extract-keywords (args)
  (declare (xargs :guard (keyword-value-listp args))) ;fixme check for supported keys
  (if (endp args)
      nil
    (cons (first args)
          (extract-keywords (rest (rest args))))))

;; Build a term representing the modification of state-term S, where TH is a
;; term representing the thread whose data is being modified (if any).
(defmacro modify (th s &rest args)
  (declare (xargs :guard (and (keyword-value-listp args)
                              (let ((keywords (extract-keywords args)))
                                (and (acl2::subsetp-eq
                                      keywords
                                      ;; all the allowed keywords:
                                      '(;; components of a frame:
                                        :pc
                                        :locals
                                        :stack
                                        ;; :locked-object
                                        ;; :method-info
                                        ;; :method-designator
                                        :call-stack ; replace the whole call-stack
                                        :thread-table ; replace the whole thread-table (used in another file)
                                        ;; other top-level state components:
                                        :heap
                                        ;; :class-table
                                        :heapref-table
                                        :monitor-table
                                        :static-field-map
                                        :initialized-classes ; todo, elsewhere called initialized-class-names
                                        :intern-table))
                                     ;; Can't both replace the entire call-stack and part of the top-frame:
                                     (not (and (member-eq :call-stack keywords)
                                               (intersection-eq keywords
                                                                '(:pc :locals :stack :locked-object))))
                                     ;; Can't both replace the entire thread-table and part of the top-frame:
                                     (not (and (member-eq :thread-table keywords)
                                               (intersection-eq keywords
                                                                '(:pc :locals :stack :locked-object))))'
                                     ;; Can't both replace the entire thread-table and call-stack:
                                     (not (and (member-eq :thread-table keywords)
                                               (member-eq :call-stack keywords))))))))
  `(make-state
    ;; the thread table:
    ,(if (suppliedp :thread-table args)
         (actual :thread-table args) ; replacing the entire thread-table
       (if (suppliedp :call-stack args)
           ;; replacing the entire call stack for thread TH:
           `(bind ,th ,(actual :call-stack args) (thread-table ,s))
         (if (or (suppliedp :pc args)
                 (suppliedp :locals args)
                 (suppliedp :stack args)
                 ;; (suppliedp :locked-object args)
                 (suppliedp :call-stack args)
                 ;; (suppliedp :method-info args) ;do we need this?
                 ;; (suppliedp :sync-flag args)
                 ;; (suppliedp :cur-class-name args)
                 )
             ;; replacing info in the top-frame of the call-stack for thread TH:
             `(bind ,th (push-frame
                         (make-frame
                          ,(if (suppliedp :pc args)
                               (actual :pc args)
                             `(pc (thread-top-frame ,th ,s)))
                          ,(if (suppliedp :locals args)
                               (actual :locals args)
                             `(locals (thread-top-frame ,th ,s)))
                          ,(if (suppliedp :stack args)
                               (actual :stack args)
                             `(stack (thread-top-frame ,th ,s)))
                          (locked-object (thread-top-frame ,th ,s))
                          (method-info (thread-top-frame ,th ,s))
                          (method-designator (thread-top-frame ,th ,s)))
                         (pop-frame (call-stack ,th ,s)))
                    (thread-table ,s))
           ;; no change to the thread table:
           `(thread-table ,s))))

    ;; the heap:
    ,(if (suppliedp :heap args)
         (actual :heap args)
       `(heap ,s))

    ;; ;;the class-table (rarely used):
    ;; (if (suppliedp :class-table args)
    ;;     (actual :class-table args)
    ;;   (list 'class-table s))
    (class-table ,s)

    ;; the heapref-table:
    ,(if (suppliedp :heapref-table args)
         (actual :heapref-table args)
       `(heapref-table ,s))

    ;;the monitor-table:
    ,(if (suppliedp :monitor-table args)
         (actual :monitor-table args)
       `(monitor-table ,s))

    ;; the static-field-map:
    ,(if (suppliedp :static-field-map args)
         (actual :static-field-map args)
       `(static-field-map ,s))

    ;; the initialized-classes:
    ,(if (suppliedp :initialized-classes args)
         (actual :initialized-classes args)
       `(initialized-classes ,s))

    ;; the intern-table:
    ,(if (suppliedp :intern-table args)
         (actual :intern-table args)
       `(intern-table ,s))))


;; ;This will be used to make the simulation stop in its tracks if it can't rule
;; ;out the exception (rather than splitting into exception and non-exception cases). - not true any more?
;; ;deprecate?
;; (defmacro possible-exception (test exceptionstate regularstate)
;;   `(if ,test ,exceptionstate ,regularstate))

;; (defthm possible-exception-when-no-exception
;;   (equal (possible-exception nil exceptionstate regularstate)
;;          regularstate)
;;   :hints (("Goal" :in-theory (enable possible-exception))))

;; (defthm possible-exception-when-exception
;;   (equal (possible-exception t exceptionstate regularstate)
;;          exceptionstate)
;;   :hints (("Goal" :in-theory (enable possible-exception))))

(defund get-from-field-from-exception-table-entry (exception-table-entry)
  (declare (xargs :guard (exception-table-entryp exception-table-entry)))
  (first exception-table-entry))

(defund get-to-field-from-exception-table-entry (exception-table-entry)
  (declare (xargs :guard (exception-table-entryp exception-table-entry)))
  (second exception-table-entry))

(defund get-target-field-from-exception-table-entry (exception-table-entry)
  (declare (xargs :guard (exception-table-entryp exception-table-entry)))
  (third exception-table-entry))

(defund get-type-field-from-exception-table-entry (exception-table-entry)
  (declare (xargs :guard (exception-table-entryp exception-table-entry)))
  (fourth exception-table-entry))

(defthm pcp-of-get-from-field-from-exception-table-entry
  (implies (exception-table-entryp exception-table-entry)
           (pcp (get-from-field-from-exception-table-entry exception-table-entry)))
  :hints (("Goal" :in-theory (enable exception-table-entryp get-from-field-from-exception-table-entry))))

(defthm pcp-of-get-to-field-from-exception-table-entry
  (implies (exception-table-entryp exception-table-entry)
           (pcp (get-to-field-from-exception-table-entry exception-table-entry)))
  :hints (("Goal" :in-theory (enable exception-table-entryp get-to-field-from-exception-table-entry))))

(defthm pcp-of-get-target-field-from-exception-table-entry
  (implies (exception-table-entryp exception-table-entry)
           (pcp (get-target-field-from-exception-table-entry exception-table-entry)))
  :hints (("Goal" :in-theory (enable exception-table-entryp get-target-field-from-exception-table-entry))))

(defthm class-namep-of-get-type-field-from-exception-table-entry
  (implies (and (exception-table-entryp exception-table-entry)
                (not (equal :any (get-type-field-from-exception-table-entry exception-table-entry))))
           (class-namep (get-type-field-from-exception-table-entry exception-table-entry)))
  :hints (("Goal" :in-theory (enable exception-table-entryp get-type-field-from-exception-table-entry))))


; find an exception handler for an exception that was thrown at location PC.
; returns the pc to jump to, or nil if no suitable handler is found.
(defund find-exception-handler (exception-table pc objectref-class class-table)
  (declare (xargs :guard (and (class-tablep class-table)
                              (class-namep objectref-class)
                              (pcp pc)
                              (exception-tablep exception-table))
                  :guard-hints (("Goal" :in-theory (enable exception-tablep)))))
  (if (endp exception-table)
      nil ;failure
    (let* ((entry (first exception-table))
           (from (get-from-field-from-exception-table-entry entry))
           (to (get-to-field-from-exception-table-entry entry))
           (type (get-type-field-from-exception-table-entry entry)))
      (if (and (pc<= from pc)
               (pc< pc to)
               (or (eq :any type)
                   (sub-class-or-same-classp objectref-class type class-table)))
          (get-target-field-from-exception-table-entry entry)
        (find-exception-handler (rest exception-table) pc objectref-class class-table)))))

(defthm exception-tablep-of-cdr
  (implies (exception-tablep exception-table)
           (exception-tablep (cdr exception-table)))
  :hints (("Goal" :in-theory (enable exception-tablep))))

(defthm pcp-of-find-exception-handler
  (implies (exception-tablep exception-table)
           (iff (pcp (find-exception-handler exception-table pc objectref-class class-table))
                (find-exception-handler exception-table pc objectref-class class-table)))
  :hints (("Goal" :in-theory (enable exception-tablep find-exception-handler))))

;move
(defund current-program (th s)
  (declare (xargs :guard (and (thread-designatorp th)
                              (jvm-statep s)
                              (bound-in-alistp th (thread-table s))
                              (call-stack-non-emptyp th s)
                              )
                  :guard-hints (("Goal" :in-theory (enable alistp-when-method-infop)))))
  (method-program (method-info (top-frame (binding th (thread-table s))))))

(defthm method-programp-of-current-program
  (implies (and (thread-designatorp th)
                (jvm-statep s)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                ;(not (method-nativep (method-info (top-frame (binding th (thread-table s))))))
                ;(not (method-abstractp (method-info (top-frame (binding th (thread-table s))))))
                )
           (method-programp (current-program th s)))
  :hints (("Goal" :in-theory (enable current-program))))

;move
(defthm memberp-of-0-and-strip-cars-when-method-programp
  (implies (method-programp program)
           (memberp 0 (strip-cars program)))
  :hints (("Goal" :in-theory (enable method-programp strip-cars method-programp-aux))))

;; Returns a state (possibly an error-state)
(defund throw-exception (objectref objectref-class th s)
  (declare (xargs :guard (and (jvm-statep s)
                              (thread-designatorp th)
                              (bound-in-alistp th (thread-table s))
                              (class-namep objectref-class))
                  :measure (call-stack-size (call-stack th s))
                  :guard-hints (("Goal" :in-theory (enable current-program)))))
  (if (empty-call-stackp (call-stack th s))
      (error-state (list "Uncaught exception." objectref objectref-class) s) ;ffixme the thread should exit.  other threads may continue?
    (let* ((frame (thread-top-frame th s))
           (pc (pc frame))
           (method-info (method-info frame))
           (exception-table (exception-table method-info))
           (class-table (class-table s))
           (exception-handler-pc (find-exception-handler exception-table pc objectref-class class-table)))
      (if exception-handler-pc
          (if (member exception-handler-pc (strip-cars (current-program th s)))
              (modify th s
                      :pc exception-handler-pc
                      :stack (push-operand objectref (empty-operand-stack)))
            (error-state (list "Bad exception handler PC" exception-handler-pc) s))
        ;; No exception handler found in this method, so pop the frame and rethrow:
        (if (locked-object frame)
            ;; There is an object to be unlocked (fixme, does all this apply to frames below the first one?)
            (let ((locked-object (addressfix (locked-object frame)))) ;drop the addressfix...
              (if (not (thread-owns-monitorp th locked-object (monitor-table s)))
                  ;; todo: call obtain-and-throw-exception here?
                  (error-state (list *IllegalMonitorStateException* :athrow) s)
                (let ((s (modify th s
                                 :call-stack (pop-frame (call-stack th s))
                                 :monitor-table (decrement-mcount (addressfix (locked-object frame)) (monitor-table s)))))
                  (throw-exception objectref objectref-class th s))))
          (let* ((s (modify th s
                            :call-stack (pop-frame (call-stack th s)))))
            (throw-exception objectref objectref-class th s)))))))

(defthm jvm-statep-of-throw-exception
  (implies (and (jvm-statep s)
                (bound-in-alistp th (thread-table s))
                ;; (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (throw-exception objectref objectref-class th s)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :cases ((call-stack-non-emptyp th s))
                  :in-theory (enable current-program throw-exception))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: collect the exception table stuff
(defund exception-handler-targets (exception-table)
  (declare (xargs :guard (exception-tablep exception-table)
                  :guard-hints (("Goal" :in-theory (enable exception-tablep)))))
  (if (endp exception-table)
      nil
    (cons (get-target-field-from-exception-table-entry (first exception-table))
          (exception-handler-targets (rest exception-table)))))

(defthm memberp-of-find-exception-handler-and-exception-handler-targets
  (implies (find-exception-handler exception-table pc objectref-class class-table)
           (memberp (find-exception-handler exception-table pc objectref-class class-table)
                    (exception-handler-targets exception-table)))
  :hints (("Goal" :in-theory (enable find-exception-handler exception-handler-targets))))



;; This stub returns a new object where all we know after the
;; operation is the class of the allocated object.  It is used in
;; instructions, such as AALOAD, where the JVM spec specifies that an
;; exception must be thrown but does not specify any details, such as
;; the values of the fields, which constructor should be called,
;; whether a pre-existing exception object can be reused, etc.
;; TODO: Is not knowing whether the object is new going to mess up the heap numbering?

(encapsulate
 (((obtain-an-object * *) => (mv * *)))
 ;; Returns the address of the object and a new state in which the
 ;; object is guaranteed to be allocated and have the correct class.
 ;; Note that the definition is local.
 (local (defun obtain-an-object (class-name s)
          (let* ((heap (heap s))
                 (class-table (class-table s))
                 (new-address (acl2::new-ad (acl2::rkeys heap)))
                 (heap (acl2::init-ref-in-heap new-address class-name class-table heap))
                 ;bozo use modify
                 (s (make-state (thread-table s) heap (class-table s) (heapref-table s) (monitor-table s) (static-field-map s) (initialized-classes s) (intern-table s))))
            (mv new-address s))))

 (defthm bound-in-heap-of-obtain-an-object
   (implies (class-namep class-name)
            (acl2::bound-in-heap (mv-nth 0 (obtain-an-object class-name s))
                                 (heap (mv-nth 1 (obtain-an-object class-name s))))))

 ;todo: think about this:
 (defthm thread-table-of-obtain-an-object
   (implies (class-namep class-name)
            (equal (thread-table (mv-nth 1 (obtain-an-object class-name s)))
                   (thread-table s))))

 (defthm get-class-of-obtain-an-object
   (implies (class-namep class-name)
            (equal (acl2::get-class (mv-nth 0 (obtain-an-object class-name s))
                                    (heap (mv-nth 1 (obtain-an-object class-name s))))
                   class-name)))

 (defthm jvm-statep-of-mv-nth-1-of-obtain-an-object
   (implies (and (jvm-statep s)
                 (class-namep class-name)
                 (bound-to-a-non-interfacep class-name (class-table s)) ;(set::in class-name (acl2::rkeys (class-table s)))
                 (class-tablep (class-table s))
;                 (not (class-decl-interfacep (get-class-info class-name (class-table s)))) ;can't be an interface ';fixme abstract out this pattern
                 )
            (jvm-statep (mv-nth 1 (obtain-an-object class-name s))))
   :hints (("Goal" :in-theory (e/d (;jvm-statep
                                    ;HEAPREF-TABLE ;why
                                    ;intern-table
                                    ;heap
                                    obtain-an-object
                                    IS-AN-INTERFACEP BOUND-TO-A-NON-INTERFACEP ; todo
                                    ) (true-listp))))))

;fixme hack for jvm-statep-of-do-inst while we decide whether to open mv-nth
;; (defthm jvm-statep-of-obtain-an-object-nth-version
;;    (implies (and (jvm-statep s)
;;                  (class-namep class-name)
;;                  ;(set::in class-name (acl2::rkeys (class-table s)))
;;                  (bound-to-a-non-interfacep class-name (class-table s))
;;                  (class-tablep (class-table s))
;;                  ;(not (class-decl-interfacep (get-class-info class-name (class-table s)))) ;can't be an interface ';fixme abstract out this pattern
;;                  )
;;             (jvm-statep (nth 1 (obtain-an-object class-name s))))
;;    :hints (("Goal" :use (:instance jvm-statep-of-obtain-an-object)
;;             :in-theory (e/d (ACL2::MV-NTH-BECOMES-NTH) (jvm-statep-of-obtain-an-object)))))

;; (defthm thread-table-of-obtain-an-object-nth-version
;;   (implies (class-namep class-name)
;;            (equal (thread-table (nth 1 (obtain-an-object class-name s)))
;;                   (thread-table s)))
;;   :hints (("Goal" :use (:instance thread-table-of-obtain-an-object)
;;             :in-theory (e/d (ACL2::MV-NTH-BECOMES-NTH) (thread-table-of-obtain-an-object)))))

(defund obtain-and-throw-exception (exception-class-name debug-info th s)
  (declare (ignore debug-info)
           (xargs :guard (and (jvm-statep s)
                              (class-namep exception-class-name)
                              (thread-designatorp th)
                              (bound-to-a-non-interfacep exception-class-name (class-table s))
                              (bound-in-alistp th (thread-table s)))))
  (mv-let (exception-object s)
    (obtain-an-object exception-class-name s)
    (throw-exception exception-object exception-class-name th s)))

(defthm jvm-statep-of-obtain-and-throw-exception
  (implies (and (jvm-statep s)
                (thread-designatorp th)
                (bound-to-a-non-interfacep exception-class-name (class-table s))
                (bound-in-alistp th (thread-table s)))
           (jvm-statep (obtain-and-throw-exception exception-class-name debug-info th s)))
  :hints (("Goal" :in-theory (enable obtain-and-throw-exception))))

;;;
;;; resolve-class
;;;

;; Returns either nil (no error), a string (the name of an exception to throw),
;; or a cons (an indication of an error).  Currently, we never use the string
;; case.
(defund resolve-non-array-class (class-name class-table)
  (declare (xargs :guard (and (class-or-interface-namep class-name)
                              (class-tablep class-table))))
  (if (bound-in-class-tablep class-name class-table)
      nil ; no error
    (cons :error-looking-up-class class-name)))

(defthmd bound-in-class-tablep-when-not-resolve-non-array-class
  (implies (not (resolve-non-array-class class-name class-table))
           (bound-in-class-tablep class-name class-table))
  :hints (("Goal" :in-theory (enable resolve-non-array-class))))

;; Returns either nil (no error), a string (the name of an exception to throw),
;; or a cons (an indication of an error).  Currently, we never use the string
;; case.
;; TODO: Flesh this out according to 5.4.3.1
;; TODO: Can this return a name other than class-name?
(defund resolve-class (type class-table)
  (declare (xargs :guard (and (reference-typep type)
                              (class-tablep class-table))))
  (if (array-typep type)
      (if (reference-typep (get-array-component-type type))
          ;; array of references (need to check the element type, if a
          ;; reference type, is in the class table):
          (resolve-class (get-array-component-type type) class-table)
        ;; array of primitives (do nothing for now)
        nil ;no error
        )
    ;; must be a class or interface name:
    (resolve-non-array-class type class-table)))

;trivial for now
(defthm class-namep-of-resolve-class
  (equal (class-namep (resolve-class class-name class-table))
         ;; the normal form:
         (stringp (resolve-class class-name class-table)))
  :hints (("Goal" :in-theory (enable resolve-class resolve-non-array-class))))

;trivial (for now)
(defthm bound-to-a-non-interfacep-of-resolve-class
  (implies (and (stringp (resolve-class class-name class-table))
                ;; (class-tablep class-table)
                )
           (bound-to-a-non-interfacep (resolve-class class-name class-table) class-table))
  :hints (("Goal" :in-theory (enable resolve-class))))

;; Returns (mv foundp class-name).  Find the first of the CLASS-NAMES that
;; has a method with the given METHOD-ID.
;; TODO: Need to handle signature polymorphic methods.
(defund resolve-method-step-2-aux (method-id class-names class-table)
  (declare (xargs :guard (and (true-listp class-names)
                              (class-name-listp class-names)
                              (class-tablep class-table)
                              (all-bound-to-a-non-interfacep class-names class-table))))
  (if (endp class-names)
      (mv nil nil) ;; not found
    (let ((class-name (first class-names)))
      (if (lookup-equal method-id (class-decl-methods (get-class-info class-name class-table)))
          (mv t class-name)
        (resolve-method-step-2-aux method-id (rest class-names) class-table)))))

(defthm resolve-method-step-2-aux-type
  (implies (and (mv-nth 0 (resolve-method-step-2-aux method-id class-names class-table))
                (all-bound-to-a-non-interfacep class-names class-table))
           (and (bound-in-class-tablep (mv-nth 1 (resolve-method-step-2-aux method-id class-names class-table))
                                       class-table)
                ;'not in normal form:
                (bound-to-a-non-interfacep (mv-nth 1 (resolve-method-step-2-aux method-id class-names class-table))
                                           class-table)))
  :hints (("Goal" :in-theory (enable RESOLVE-METHOD-STEP-2-AUX))))

;; Returns (mv foundp class-name).  Find the first of the CLASS-NAMES that
;; has a method with the given METHOD-ID.
;; TODO: Handle signature polymorphic methods.
(defund resolve-method-step-2 (class-name method-name method-descriptor class-table)
  (declare (xargs :guard (and (class-namep class-name)
                              (method-namep method-name)
                              (method-descriptorp method-descriptor)
                              (class-tablep class-table)
                              (bound-in-class-tablep class-name class-table)
                              (not (is-an-interfacep class-name class-table)))
                  :guard-hints (("Goal" :in-theory (enable IS-AN-INTERFACEP BOUND-TO-A-NON-INTERFACEP))) ;todo
                  ))
  (resolve-method-step-2-aux (cons method-name method-descriptor)
                             ;; we search the given class and then its superclasses
                             (cons class-name (get-superclasses class-name class-table))
                             class-table))

(defthm resolve-method-step-2-type
  (implies (and (mv-nth 0 (resolve-method-step-2 class-name method-name method-descriptor class-table))
;                (class-namep class-name)
                (bound-to-a-non-interfacep class-name class-table)
                (class-tablep class-table))
           (and (bound-in-class-tablep (mv-nth 1 (resolve-method-step-2 class-name method-name method-descriptor class-table))
                                       class-table)
                (bound-to-a-non-interfacep (mv-nth 1 (resolve-method-step-2 class-name method-name method-descriptor class-table))
                                           class-table)))
  :hints (("Goal" :in-theory (e/d (resolve-method-step-2) (bound-to-a-non-interfacep)))))

;; Returns (mv erp class-name-of-resolved-method) where ERP is either nil (no
;; error), a string (the name of an exception to throw), or a cons (an
;; indication of an error).  If ERP is non-nil, class-name-of-resolved-method
;; is meaningless.  See 5.4.3.3 (Method Resoution).
;todo: flesh this out
(defund resolve-class-method (method-name method-descriptor c class-table)
  (declare (xargs :guard (and (method-namep method-name)
                              (method-descriptorp method-descriptor)
                              (class-namep c) ;todo: could this be an array class?
                              (class-tablep class-table))
                  :guard-hints (("Goal" :in-theory (enable bound-in-class-tablep-when-not-resolve-non-array-class
                                                           IS-AN-INTERFACEP ;todo
                                                           )))))
  (let ((erp (resolve-non-array-class c class-table)))
    (if erp
        (mv erp nil)
      (if (is-an-interfacep c class-table)
          (mv *IncompatibleClassChangeError* nil)
        (mv-let (foundp class-name)
          (resolve-method-step-2 c method-name method-descriptor class-table)
          (if foundp
              (mv nil class-name)
            (mv (list :unsupported-case 'resolve-class-method) nil)))))))

;; Returns (mv erp class-name-of-resolved-method) where ERP is either nil (no
;; error), a string (the name of an exception to throw), or a cons (an
;; indication of an error).  If ERP is non-nil, class-name-of-resolved-method
;; is meaningless.  See 5.4.3.4 (Interface Method Resoution).
(defund resolve-interface-method (method-name method-descriptor c class-table)
  (declare (xargs :guard (and (method-namep method-name)
                              (method-descriptorp method-descriptor)
                              (class-or-interface-namep c)
                              (class-tablep class-table)))
           (ignore method-name method-descriptor))
  (let ((erp (resolve-non-array-class c class-table)))
    (if erp
        (mv erp nil)
      (mv nil c) ;todo: flesh this out
      )))

;; Returns (mv erp class-name-of-resolved-method) where ERP is either nil (no
;; error), a string (the name of an exception to throw), or a cons (an
;; indication of an error).  If ERP is non-nil, class-name-of-resolved-method
;; is meaningless.  See 5.4.3.4 (Interface Method Resoution).
(defund resolve-method (method-name method-descriptor c interfacep class-table)
  (declare (xargs :guard (and (method-namep method-name)
                              (method-descriptorp method-descriptor)
                              (class-or-interface-namep c)
                              (booleanp interfacep)
                              (class-tablep class-table))))
  (if interfacep
      (resolve-interface-method method-name method-descriptor c class-table)
    (resolve-class-method method-name method-descriptor c class-table)))

(defthm resolve-method-type
  (implies (and (not (mv-nth 0 (resolve-method method-name method-descriptor c interfacep class-table)))
                (bound-to-a-non-interfacep c class-table)
                (class-tablep class-table))
           (and (bound-in-class-tablep (mv-nth 1 (resolve-method method-name method-descriptor c interfacep class-table))
                                       class-table)
                (bound-to-a-non-interfacep (mv-nth 1 (resolve-method method-name method-descriptor c interfacep class-table))
                                           class-table)))
  :hints (("Goal" :in-theory (e/d (resolve-method resolve-interface-method resolve-class-method)
                                  (bound-to-a-non-interfacep)))))

(defthm class-namep-of-mv-nth-0-of-resolve-method
  (equal (class-namep (mv-nth 0 (resolve-method method-name method-descriptor c interfacep class-table)))
         (stringp (mv-nth 0 (resolve-method method-name method-descriptor c interfacep class-table)))))

(defthm bound-to-a-non-interfacep-of-mv-nth-0-of-resolve-method
  (implies (and (stringp (mv-nth 0 (resolve-method method-name method-descriptor c interfacep class-table)))
                (class-tablep class-table)
                )
           (bound-to-a-non-interfacep (mv-nth 0 (resolve-method method-name method-descriptor c interfacep class-table)) class-table))
  :hints (("Goal" :in-theory (enable resolve-method resolve-interface-method resolve-class-method class-tablep))))

;; If method resolution succeeds, we know the class returned is bound.
(defthm bound-in-class-tablep-of-mv-nth-1-of-resolve-method
  (implies (and (not (mv-nth 0 (resolve-method method-name method-descriptor c interfacep class-table)))
                (class-tablep class-table)
                )
           (bound-in-class-tablep (mv-nth 1 (resolve-method method-name method-descriptor c interfacep class-table)) class-table))
  :hints (("Goal" :in-theory (enable resolve-method resolve-interface-method resolve-class-method class-tablep
                                     bound-in-class-tablep-when-not-resolve-non-array-class
                                     BOUND-TO-A-NON-INTERFACEP ;todo
                                     is-an-interfacep-intro
                                     ))))

;; If method resolution succeeds, we know the class passed in is bound.
(defthm bound-in-class-tablep-when-mv-nth-0-of-resolve-method
  (implies (and (not (mv-nth 0 (resolve-method method-name method-descriptor c interfacep class-table)))
                (class-tablep class-table))
           (bound-in-class-tablep c class-table))
  :hints (("Goal" :in-theory (enable resolve-method resolve-interface-method resolve-class-method class-tablep
                                     bound-in-class-tablep-when-not-resolve-non-array-class))))

(defthm class-namep-when-mv-nth-0-of-resolve-method
  (implies (and (not (mv-nth 0 (resolve-method method-name method-descriptor c interfacep class-table)))
                (class-tablep class-table))
           (class-namep c))
  :hints (("Goal" :use (:instance bound-in-class-tablep-when-mv-nth-0-of-resolve-method)
           :in-theory (disable bound-in-class-tablep-when-mv-nth-0-of-resolve-method))))

;; If method resolution failed, we know the exception class returned is bound.
(defthm bound-in-class-tablep-of-mv-nth-0-of-resolve-method
  (implies (and (stringp (mv-nth 0 (resolve-method method-name method-descriptor c interfacep class-table)))
                (class-tablep class-table)
                )
           (bound-in-class-tablep (mv-nth 0 (resolve-method method-name method-descriptor c interfacep class-table))
                                  class-table))
  :hints (("Goal" :in-theory (enable resolve-method resolve-interface-method resolve-class-method class-tablep
                                     bound-in-class-tablep-when-not-resolve-non-array-class))))

; This is just the identity on its first argument, but it prevents loops in symbolic execution
(defund failed-to-enter-monitor-wrapper (s debug-info)
  (declare (xargs :guard t) (ignore debug-info))
  s)

; =============================================================================
; JVM INSTRUCTIONS BEGIN HERE
; =============================================================================

;; (:tableswitch default-offset low high jump-offsets inst-len)
(defund execute-TABLESWITCH (inst th s)
  (let* ((default (farg1 inst))
         (low (farg2 inst))
         (high (farg3 inst))
         (jump-offsets (farg4 inst)) ;there are high-low+1 of these
         (index (top-operand (stack (thread-top-frame th s))))
         (offset (if (or (< index low)
                         (> index high))
                     default
                   (nth (- index low) jump-offsets)))
         (new-pc (+ offset (pc (thread-top-frame th s)))))
    (if (not (natp new-pc))
        (error-state (list "Bad PC after tableswitch." new-pc) s)
      (if (not (memberp new-pc (strip-cars (method-program (method-info (thread-top-frame th s))))))
          (error-state (list "Bad PC after tableswitch." new-pc) s)
        (modify th s
                :pc new-pc
                :stack (pop-operand (stack (thread-top-frame th s))))))))

(defthm jvm-statep-of-execute-tableswitch
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :tableswitch)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-TABLESWITCH inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-TABLESWITCH
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defun execute-ATHROW (th s)
  (let* ((frame (thread-top-frame th s))
         (stack (stack frame))
         (objectref (top-operand stack))
         (heap (heap s))
         (objectref-class (acl2::get-class objectref heap)))
    (if (null-refp objectref)
        (obtain-and-throw-exception *NullPointerException* (list :athrow objectref) th s)
      (throw-exception objectref objectref-class th s))))

;; (:NOP)
;do nothing (except advance the PC of course)
(defun execute-NOP (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))))

;operand stack manipulations:

;; (:POP)
(defun execute-POP (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (pop-operand (stack (thread-top-frame th s)))))

;; (:POP2)
(defun execute-POP2 (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (pop-operand (pop-operand (stack (thread-top-frame th s))))))

;; (DUP)
; Since longs and doubles are not "category 1" computational types, we don't
; have to worry about them for this instruction.
(defun execute-DUP (th s)
  (let ((value (top-operand (stack (thread-top-frame th s)))))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand value (stack (thread-top-frame th s))))))

;; (DUP_X1)
;Again, we don't have to worry about longs or doubles.
(defun execute-DUP_X1 (th s)
  (let* ((val1 (top-operand (stack (thread-top-frame th s))))
         (val2 (top-operand (pop-operand (stack (thread-top-frame th s))))))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand val1 (push-operand val2 (push-operand val1 (pop-operand (pop-operand (stack (thread-top-frame th s))))))))))

;; (DUP_X2)
;if val2 and val3 together represent a long or double, this works as well
(defun execute-DUP_X2 (th s)
  (let* ((val1 (top-operand (stack (thread-top-frame th s))))
         (val2 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (val3 (top-operand (pop-operand (pop-operand (stack (thread-top-frame th s))))))
         (stack_prime (pop-operand (pop-operand (pop-operand (stack (thread-top-frame th s)))))))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand val1
                                 (push-operand val2
                                               (push-operand val3
                                                             (push-operand val1 stack_prime)))))))

;this works okay if value1 and value2 together represent a long/double
;fixme do we have rules for mixing the double stack ops with two single stack ops?
(defun execute-DUP2 (th s)
  (let* ((val1 (top-operand (stack (thread-top-frame th s))))
         (val2 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (stack_prime (pop-operand (pop-operand (stack (thread-top-frame th s))))))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand val1
                         (push-operand val2
                               (push-operand val1
                                     (push-operand val2 stack_prime)))))))

;seems to work okay, even for longs/doubles
(defun execute-DUP2_X1 (th s)
  (let* ((val1 (top-operand (stack (thread-top-frame th s))))
         (val2 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (val3 (top-operand (popn-operands 2 (stack (thread-top-frame th s)))))
         (stack_prime (popn-operands 3 (stack (thread-top-frame th s)))))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand val1
                         (push-operand val2
                               (push-operand val3
                                     (push-operand val1
                                           (push-operand val2 stack_prime))))))))

;seems to work okay, even for longs/doubles
(defun execute-DUP2_X2 (th s)
  (let* ((val1 (top-operand (stack (thread-top-frame th s))))
         (val2 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (val3 (top-operand (popn-operands 2 (stack (thread-top-frame th s)))))
         (val4 (top-operand (popn-operands 3 (stack (thread-top-frame th s)))))
         (stack_prime (popn-operands 4 (stack (thread-top-frame th s)))))
    (modify th s
              :pc (+ 1 ;(inst-length inst)
                     (pc (thread-top-frame th s)))
              :stack (push-operand val1
                       (push-operand val2
                         (push-operand val3
                           (push-operand val4
                             (push-operand val1
                               (push-operand val2 stack_prime)))))))))

; (SWAP)
(defun execute-SWAP (th s)
  (let* ((val1 (top-operand (stack (thread-top-frame th s))))
         (val2 (top-operand (pop-operand (stack (thread-top-frame th s))))))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand val2
                         (push-operand val1
                               (pop-operand (pop-operand (stack (thread-top-frame th s)))))))))

;; Instructions that push constants:

; (ACONST_NULL)
(defun execute-ACONST_NULL (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (acl2::null-ref)
                               (stack (thread-top-frame th s)))))


;n is 0, 1, or 2
(defun execute-FCONST_X (n th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (make-regular-float :pos n) ;;TODO: If this is 0.0, should we assume a positive 0?  I think so, since the spec sometimes does talk about -0.0.
                               (stack (thread-top-frame th s)))))

;n is 0 or 1
(defun execute-DCONST_X (n th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long (make-regular-double :pos n) ;;TODO: If this is 0.0, should we assume a positive 0?
                            (stack (thread-top-frame th s)))))


; These seven instructions push integer constants and are all modeled by execute-ICONST_X:
; (ICONST_M1) push "minus one"
; (ICONST_0)
; (ICONST_1)
; (ICONST_2)
; (ICONST_3)
; (ICONST_4)
; (ICONST_5)
;the extra n parameter has the constant (currently a signed-value - fixme maybe change that)
(defun execute-ICONST_X (th s n)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (encode-signed n)
                       (stack (thread-top-frame th s)))))

; These two instructions push long constants are all all modeled by execute-LCONST_X:
; (LCONST_0)
; (LCONST_1)

;the extra n parameter has the constant
;since the constant can't be negative, we don't have to worry about signed/unsigned representations
(defun execute-LCONST_X (th s n)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long n (stack (thread-top-frame th s)))))

;;Instructions that push immediate data

; (BIPUSH value) - value is an 8-bit signed-byte (currently)
(defun execute-BIPUSH (inst th s)
  (modify th s
          :pc (+ 2 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (bvsx 32 8 (farg1 inst)) ;do this bvsx during parsing?
                       (stack (thread-top-frame th s)))))

; (SIPUSH value) - value is a 16-bit signed-byte (currently)
(defun execute-SIPUSH (inst th s)
  (modify th s
          :pc (+ 3 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (bvsx 32 16 (farg1 inst)) ;do this bvsx during parsing?
                       (stack (thread-top-frame th s)))))

;; Loading and storing references

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (ALOAD localslotnum inst-len) Instruction - load a reference from the locals
(defund execute-ALOAD (inst th s)
  (let ((inst-len (farg2 inst)))
    (modify th s
            :pc (+ inst-len
                   (pc (thread-top-frame th s)))
            :stack (push-operand (nth-local (farg1 inst)
                                            (locals (thread-top-frame th s)))
                                 (stack (thread-top-frame th s))))))

;; checks the inst-len
(local
 (defthmd load-helper-1
   (implies (and (member-equal (instruction-opcode (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s)))))))
                               '(:aload :astore :dload :dstore :fload :fstore :iload :istore :lload :lstore :ret))
                 ;(instructionp (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s)))))))
                 (jvm-instruction-okayp (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s))))))
                                        (pc (top-frame (binding th (thread-table s))))
                                        ;; valid-pcs
                                        (strip-cars (method-program (method-info (top-frame (binding th (thread-table s))))))))
            (pcp (+ (pc (top-frame (binding th (thread-table s))))
                    (caddr (lookup-equal (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s))))))))))
   :hints (("Goal" :in-theory (enable jvm-instruction-okayp valid-pcp)))))

(local
 (defthmd load-helper-3
   (implies (and (member-equal (instruction-opcode (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s)))))))
                               '(:aload :astore :dload :dstore :fload :fstore :iload :istore :lload :lstore :ret))
                 (jvm-instruction-okayp (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s))))))
                                        (pc (top-frame (binding th (thread-table s))))
                                        ;; valid-pcs
                                        (strip-cars (method-program (method-info (top-frame (binding th (thread-table s))))))))
            (memberp (+ (pc (top-frame (binding th (thread-table s))))
                        (caddr (lookup-equal (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s))))))))
                     (strip-cars (method-program (method-info (top-frame (binding th (thread-table s))))))))
   :hints (("Goal" :in-theory (enable jvm-instruction-okayp valid-pcp)))))

(defthm jvm-statep-of-execute-aload
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :aload)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-ALOAD inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-ALOAD
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp
                            load-helper-1
                            load-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; (ALOAD_X) Instruction - load a reference from the locals
;                         covers ALOAD_{0, 1, 2, 3}
;TODO put the argument first (also elsewhere)?
(defun execute-ALOAD_X (th s n)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (nth-local n (locals (thread-top-frame th s)))
                       (stack (thread-top-frame th s)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (ASTORE index inst-len)
;TODO - combine with ASTORE_X ?
(defund execute-ASTORE (inst th s)
  (let ((index (farg1 inst))
        (inst-len (farg2 inst))
        (objectref (top-operand (stack (thread-top-frame th s)))))
    (modify th s
            :pc (+ inst-len (pc (thread-top-frame th s)))
            :locals (update-nth-local index objectref (locals (thread-top-frame th s)))
            :stack (pop-operand (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-astore
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :astore)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-ASTORE inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-ASTORE
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp
                            load-helper-1
                            load-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; -----------------------------------------------------------------------------
; (ASTORE_X) Instruction - store a reference into the locals
;                          covers ASTORE_{0, 1, 2, 3}

(defun execute-ASTORE_X (th s n)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :locals (update-nth-local n
                                     (top-operand (stack (thread-top-frame th s)))
                                     (locals (thread-top-frame th s)))
          :stack (pop-operand (stack (thread-top-frame th s)))))

;; Instructions for arrays


; (ANEWARRAY component-type)
;currently no need to resolve the component type, i guess??
;compare to execute-newarray?
(defun execute-ANEWARRAY (inst th s)
  (let* ((component-type (farg1 inst))
         (count (top-operand (stack (thread-top-frame th s))))
         (heap (heap s))
         (erp (resolve-class component-type (class-table s))))
    (if erp
        (if (stringp erp)
            (obtain-and-throw-exception erp (list "ERROR IN ANEWARRAY: Failed to resolve class." :debug-info component-type) th s)
          (error-state erp s))
      (if (acl2::sbvlt 32 count 0)
          (obtain-and-throw-exception *NegativeArraySizeException* (list :anewarray (decode-signed count)) th s)
        (let ((vals (acl2::repeat (decode-signed-non-neg count) (acl2::null-ref)))) ;;arrays of refs are initialized to contain NULLs
          (mv-let (arrayref heap)
            (build-new-array vals component-type heap)
            (modify th s
                    :pc (+ 3 ;(inst-length inst)
                           (pc (thread-top-frame th s)))
                    :stack (push-operand arrayref (pop-operand (stack (thread-top-frame th s))))
                    :heap heap)))))))

;(AALOAD)
;; Load from array of references
(defun execute-AALOAD (th s)
  (let* ((frame (thread-top-frame th s))
         (stack (stack frame)))
    (let ((index (top-operand stack))
          (arrayref (top-operand (pop-operand stack))))
      (if (null-refp arrayref)
          (obtain-and-throw-exception *NullPointerException* (list :aaload arrayref) th s)
        (let ((contents (acl2::array-contents arrayref (heap s))))
          (if (or (acl2::sbvlt 32 index 0)
                  (acl2::sbvge 32 index (len contents)))
              (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :aaload (decode-signed index) arrayref) th s)
            (modify th s
                    :pc (+ 1 ;(inst-length inst)
                           (pc frame))
                    :stack (push-operand (nth (decode-signed-non-neg index) contents) ;use something better than nth here?
                                         (pop-operand (pop-operand stack))))))))))

;(AASTORE)
;; Store into array of references
(defun execute-AASTORE (th s)
  (let ((stack (stack (thread-top-frame th s))))
    ;; not a let*:
    (let ((value (top-operand stack))
          (index (top-operand (pop-operand stack)))
          (arrayref (top-operand (pop-operand (pop-operand stack)))))
      (if (null-refp arrayref)
          (obtain-and-throw-exception *NullPointerException* (list :aastore arrayref) th s)
        (let ((old-array-contents (acl2::get-field arrayref (acl2::array-contents-pair) (heap s))))
          (if (or (acl2::sbvlt 32 index 0) ;FFIXME CRUD the "or" here (or maybe the >=) can cause case splitting
                  (acl2::sbvge 32 index (array-length arrayref (heap s)))) ;todo: use (len old-array-contents) here?
              (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :aastore (decode-signed index) arrayref) th s)
            ;;FFFIXME check for and throw ArrayStoreException if necessary
            (modify th s
                    :pc (+ 1 ;(inst-length inst)
                           (pc (thread-top-frame th s)))
                    :stack (pop-operand (pop-operand (pop-operand (stack (thread-top-frame th s)))))
                    :heap (acl2::set-field (addressfix arrayref) ;why?
                                           (acl2::array-contents-pair)
                                           ;;ffixme can we do anything better than update-nth?
                                           (update-nth (decode-signed-non-neg index) value old-array-contents)
                                           (heap s)))))))))

; (NEWARRAY element-type)
;fixme does this correctly initialize the fields of class Object?  does array have any other superclasses?
;this is only for arrays whose elements are primitive types
(defun execute-NEWARRAY (inst th s)
  (let* ((component-type (farg1 inst))
         (count (top-operand (stack (thread-top-frame th s))))
         (heap (heap s)))
    (if (acl2::sbvlt 32 count 0)
        (obtain-and-throw-exception *NegativeArraySizeException* (list :newarray (decode-signed count)) th s)
      (let ((vals (initial-array-contents component-type (decode-signed-non-neg count))))
        (mv-let (arrayref heap)
                (build-new-array vals component-type heap) ;call build-new-array-with-default?
                (modify th s
                        :pc (+ 2 ;(inst-length inst)
                               (pc (thread-top-frame th s)))
                        :stack (push-operand arrayref
                                             (pop-operand (stack (thread-top-frame th s))))
                        :heap heap))))))

;;;
;;; any-less-than-zero
;;;

(defun any-less-than-zero (vals)
  (declare (xargs :guard (and (true-listp vals)
                              (acl2::all-unsigned-byte-p 32 vals))))
  (if (endp vals)
      nil
    (or (acl2::sbvlt 32 (first vals) 0)
        (any-less-than-zero (rest vals)))))

(defthm any-less-than-zero-of-reverse-list
  (equal (any-less-than-zero (acl2::reverse-list vals))
         (any-less-than-zero vals))
  :hints (("Goal" :in-theory (enable ACL2::REVERSE-LIST any-less-than-zero))))

;needed?
(defthm any-less-than-zero-of-true-list-fix
  (equal (any-less-than-zero (acl2::true-list-fix vals))
         (any-less-than-zero vals))
  :hints (("Goal" :in-theory (enable any-less-than-zero true-list-fix))))

(defthm any-less-than-zero-of-cons
  (equal (any-less-than-zero (cons val vals))
         (or (acl2::sbvlt 32 val 0)
             (any-less-than-zero vals)))
  :hints (("Goal" :in-theory (enable any-less-than-zero))))

(defthm any-less-than-zero-of-nil
  (equal (any-less-than-zero nil)
         nil)
  :hints (("Goal" :in-theory (enable any-less-than-zero))))

;drop?
(defthm any-less-than-zero-of-empty-operand-stack
  (equal (any-less-than-zero (empty-operand-stack))
         nil)
  :hints (("Goal" :in-theory (enable any-less-than-zero empty-operand-stack))))


;false is represented by 0:
(defun false ()
  (declare (xargs :guard t))
  0)

;true is represented by 1:
(defun true ()
  (declare (xargs :guard t))
  1)



; (MULTIANEWARRAY arrayclassname number-of-dimensions)
;number-of-dimensions must be >= 1.
;todo: compare what this does to makemultiarray
(defun execute-MULTIANEWARRAY (inst th s)
  (let* ((arraytype (farg1 inst)) ;ex: '(:ARRAY (:ARRAY :INT)) ;this is not the component type but rather the type of the entire array being created
         (ndimensions (farg2 inst))
         (counts (acl2::reverse-list (topn-operands ndimensions (stack (thread-top-frame th s)))))
         (erp (resolve-class arraytype (class-table s))))
    (if erp
        (if (stringp erp)
            (obtain-and-throw-exception erp (list "ERROR IN MULTIANEWARRAY: Failed to resolve class." :debug-info arraytype) th s)
          (error-state erp s))
      (if (any-less-than-zero counts)
          (obtain-and-throw-exception *NegativeArraySizeException* (list :MULTIANEWARRAY counts) th s)
        (mv-let (arrayref heap)
          (build-multi-dim-array counts arraytype (heap s))
          (modify th s
                  :pc (+ 4 ;(inst-length inst)
                         (pc (thread-top-frame th s)))
                  :stack (push-operand arrayref
                                       (popn-operands ndimensions (stack (thread-top-frame th s))))
                  :heap heap))))))

;fixme for the return instructions, what if we are returning from the
;main method (so there is no stack frame below the one being popped
;off)?

;;We are trying the approach of having the return instructions
;;increment the PC past the corresponding invoke instruction.  So
;;while a subroutine is executing, the caller's PC is still at the invoke
;;instruction.  This can help simplify the handling of exceptions
;;(and may help us formulate invariants about every frame but the top
;;one on the call stack having the PC at an invoke instruction).

;; Unless we enable this for reasoning we'll need various rules about how it affects other state components
(defund move-past-invoke-instruction (th s)
  (declare (xargs :guard (jvm-statep s) ;todo: add to this and verify it
                  :verify-guards nil))
  (modify th s :pc (+ (len-of-invoke-instruction (instruction-opcode (current-inst th s)))
                      (pc (thread-top-frame th s)))))

(defthm jvm-statep-of-move-past-invoke-instruction
  (implies (and (jvm-statep s)
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th)
                (member-equal (instruction-opcode (current-inst th s))
                              '(:invokevirtual :invokestatic :invokespecial :invokeinterface :ldc_w :ldc))
                (call-stack-non-emptyp th s))
           (jvm-statep (move-past-invoke-instruction th s)))
  :hints (("Goal" :in-theory (e/d (move-past-invoke-instruction len-of-invoke-instruction
                                                                method-programp-key-property-2-alt
                                                                inst-len
                                                                ;;acl2::memberp-of-cons
                                                                memberp)
                                  (natp
                                   method-program ; todo
                                   )))))

(local (include-book "kestrel/arithmetic-light/types" :dir :system)) ; move up

;; ;; Unless we enable this for reasoning we'll need various rules about how it affects other state components
;; (defund move-past-instruction (th s)
;;   (declare (xargs :guard (and (jvm-statep s) ;todo: add to this and verify it
;;                               (bound-in-alistp th (thread-table s))
;;                               (thread-designatorp th)
;;                               (call-stack-non-emptyp th s))
;;                   :verify-guards nil ; todo
;;                   :guard-hints (("Goal" :in-theory (enable acl2::acl2-numberp-when-natp ; or use a specialized function to advance the PC
;;                                                            )))))
;;   (modify th s :pc (+ (inst-len (current-inst th s)) (pc (thread-top-frame th s)))))

;; (defthm jvm-statep-of-move-past-instruction
;;   (implies (and (jvm-statep s)
;;                 (bound-in-alistp th (thread-table s))
;;                 (thread-designatorp th)
;;                 (call-stack-non-emptyp th s))
;;            (jvm-statep (move-past-instruction th s)))
;;   :hints (("Goal" :in-theory (e/d (move-past-instruction
;;                                    method-programp-key-property-2-alt
;;                                    method-programp-key-property-2
;;                                    ;inst-len
;;                                    ;;acl2::memberp-of-cons
;;                                    memberp)
;;                                   (natp
;;                                    method-program ; todo
;;                                    )))))

;; ;; special case for program = current program
;; (defthmd method-programp-key-property-2-alt-special
;;   (implies (and (equal k (inst-len (lookup-eq pc (method-program (method-info (top-frame (binding th (thread-table s))))))))
;;                 (method-programp (method-program (method-info (top-frame (binding th (thread-table s)))))) ; drop?
;;                 (memberp pc (strip-cars (method-program (method-info (top-frame (binding th (thread-table s)))))))
;;                 (not (member-equal (instruction-opcode (lookup-eq pc (method-program (method-info (top-frame (binding th (thread-table s))))))) '(:ret :return))))
;;            (memberp (+ k pc) (strip-cars (method-program (method-info (top-frame (binding th (thread-table s))))))))
;;   :hints (("Goal" :use (:instance method-programp-key-property-2-alt
;;                                   (program (method-program (method-info (top-frame (binding th (thread-table s))))))))))

(defthm len-of-invoke-instruction-helper
  (implies (and (framep frame)
                (member-eq (instruction-opcode (lookup-equal (pc frame) (method-program (method-info frame))))
                           '(:invokevirtual :invokestatic :invokespecial :invokeinterface
                             ;; :ldc :ldc_w ; why?
                             )))
           (memberp (+ (pc frame)
                       (len-of-invoke-instruction (instruction-opcode (lookup-equal (pc frame) (method-program (method-info frame))))))
                    (strip-cars (method-program (method-info frame)))))
  :hints (("Goal" :in-theory (enable framep len-of-invoke-instruction memberp method-infop method-info method-program pc inst-len)
                  :do-not-induct t
                  :use (:instance method-programp-key-property-2
                                  (program (method-program (method-info frame)))
                                  (pc (pc frame))))))

;fixme do we call this too much?  only need to call this when returning from a void method?
(defun no-explicit-invokep (th s)
  ;; (declare (xargs :guard (and (thread-designatorp th)
  ;;                             (jvm-statep s)
  ;;                             (bound-in-alistp th (thread-table s))
  ;;                             (not (empty-call-stackp (call-stack th s))))))
  (or (equal "<clinit>" (cur-method-name (thread-top-frame th s)))
      (equal "DUMMY-METHOD-TO-BUILD-CLASS-OBJECT" (cur-method-name (thread-top-frame th s)))))

(defund void-return-core (th s)
  ;; (declare (xargs :guard (and (jvm-statep s)
  ;;                             )))
  (let ((no-explicit-invokep (no-explicit-invokep th s))
        (s (modify th s :call-stack (pop-frame (call-stack th s)))))
    (if (empty-call-stackp (call-stack th s))
        ;;if we are returning from the bottommost frame, there is no caller frame in which to advance the pc. fixme think about what to do
        ;;fixme unschedule the thread?
        (prog2$ (cw "Popping off bottom frame.~%")
                s)
      ;; move the pc past the invoke instruction in the caller:
      ;; exception: if we are returning from a <clinit>, there is no explicit invoke instruction that called this method, so don't advance the pc.
      (if no-explicit-invokep
          s
        ;; (move-past-instruction th s) ; can't use this because the inst may be a program-ender
        (if (memberp (instruction-opcode (current-inst th s)) '(:invokevirtual :invokestatic :invokespecial :invokeinterface :ldc_w :ldc))
            (move-past-invoke-instruction th s)
          s ;(error-state :bad-void-return s) ; todo: put this back, but need more hyps for the loop-lifter
          )))))

(defthm jvm-statep-of-void-return-core
  (implies (and (jvm-statep s)
                (thread-designatorp th)
                (bound-in-alistp th (thread-table s)))
           (jvm-statep (void-return-core th s)))
  :hints (("Goal" :in-theory (enable void-return-core))))

; (RETURN) Instruction - Void Return
;fixme pass in the inst to each execute-returnXXX function?
;fixme all the synchronization and locking stuff may be out-of-date
(defund execute-RETURN (th s)
  (let* ((frame (thread-top-frame th s))
         (syncp (method-synchronizedp (method-info frame))))
    (if syncp
        (let ((monitor-table (monitor-table s))
              (object-to-unlock (addressfix (locked-object frame))))
          (if (null-refp object-to-unlock)
              (obtain-and-throw-exception *nullpointerexception* (list :return object-to-unlock) th s)
            (if (not (thread-owns-monitorp th object-to-unlock monitor-table))
                (if (bound-to-a-non-interfacep *illegalmonitorstateexception* (class-table s))
                    (obtain-and-throw-exception *illegalmonitorstateexception* (list :return object-to-unlock) th s)
                  (error-state :bad-binding-for-illegalmonitorstateexception s))
              ;;fixme think about structured locking.
              (let* ((s (modify th s :monitor-table (decrement-mcount object-to-unlock monitor-table))))
                (void-return-core th s)))))
      (void-return-core th s))))

(defthm jvm-statep-of-execute-return
  (implies (and (jvm-statep s)
;                (equal inst (current-inst th s))
 ;               (equal (instruction-opcode inst) :return)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-return th s)))
  :hints (("Goal" :in-theory (e/d (execute-return
                                   ;;jvm-statep-def ; todo
                                   current-program ; todo
                                   move-past-invoke-instruction)
                                  (method-program ; todo
                                   )))))

;used for IRETURN, ARETURN, etc.
(defund return-core (val th s)
  (let ((no-explicit-invokep (no-explicit-invokep th s))
        (s (modify th s :call-stack (pop-frame (call-stack th s)))))
    (if (empty-call-stackp (call-stack th s))
        ;;if we are returning from the bottommost frame, there is no caller to catch the value.  fixme think about what to do.
        ;;fixme unschedule the thread?
        (prog2$ (cw "Executing bottom frame.")
                s)
      (let ((s (modify th s :stack (push-operand val (stack (thread-top-frame th s))))))
        (if no-explicit-invokep
            s
          ;; (move-past-instruction th s)
          (if (memberp (instruction-opcode (current-inst th s)) '(:invokevirtual :invokestatic :invokespecial :invokeinterface :ldc_w :ldc))
              (move-past-invoke-instruction th s)
            s ;(error-state :bad-return s) ; todo: put this back, but need more hyps for the loop-lifter
            )
          )))))

(defthm jvm-statep-of-return-core
  (implies (and (jvm-statep s)
                (thread-designatorp th)
                (bound-in-alistp th (thread-table s))
                ;; (memberp (instruction-opcode (lookup-equal (pc (top-frame (pop-frame (binding th (thread-table s)))))
                ;;                                            (method-program (method-info (top-frame (pop-frame (binding th (thread-table s))))))))
                ;;          '(:invokevirtual :invokestatic
                ;;            :invokespecial :invokeinterface
                ;;            :ldc_w :ldc))
                )
           (jvm-statep (return-core val th s)))
  :hints (("Goal" :in-theory (e/d (return-core)))))

;; (ARETURN) instruction: Return reference from method
(defund execute-ARETURN (th s)
  (let* ((frame (thread-top-frame th s))
         (objectref (top-operand (stack frame))) ;; the reference to return
         (syncp (method-synchronizedp (method-info frame))))
    (if syncp
        (let ((monitor-table (monitor-table s))
              (object-to-unlock (addressfix (locked-object frame))))
          ;;fixme call attempt-to-exit-monitor (here and elsewhere):
          (if (null-refp object-to-unlock)
              (obtain-and-throw-exception *NullPointerException* (list :areturn object-to-unlock) th s)
            (if (not (thread-owns-monitorp th object-to-unlock monitor-table))
                (if (bound-to-a-non-interfacep *illegalmonitorstateexception* (class-table s))
                    (obtain-and-throw-exception *IllegalMonitorStateException* (list :areturn object-to-unlock) th s)
                  (error-state :bad-binding-for-illegalmonitorstateexception s))
              ;;FIXME Think about structured locking.
              (let ((s (modify th s :monitor-table (decrement-mcount object-to-unlock monitor-table))))
                (return-core objectref th s)))))
      (return-core objectref th s))))

(defthm jvm-statep-of-execute-areturn
  (implies (and (jvm-statep s)
;                (equal inst (current-inst th s))
 ;               (equal (instruction-opcode inst) :areturn)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-areturn th s)))
  :hints (("Goal" :in-theory (e/d (execute-areturn
                                   ;;jvm-statep-def ; todo
                                   current-program ; todo
                                   move-past-invoke-instruction)
                                  (method-program ; todo
                                   )))))

; (IRETURN) Instruction - return an int
;fixme do all of the non-void return functions have essentially the same definition?
(defund execute-IRETURN (th s)
  (let* ((frame (thread-top-frame th s))
         (val (top-operand (stack frame))) ;the value to return
         (syncp (method-synchronizedp (method-info frame))))
    (if syncp
        (let ((monitor-table (monitor-table s))
              (object-to-unlock (addressfix (locked-object frame))))
          (if (null-refp object-to-unlock)
              (obtain-and-throw-exception *nullpointerexception* (list :ireturn object-to-unlock) th s)
            (if (not (thread-owns-monitorp th object-to-unlock monitor-table))
                (if (bound-to-a-non-interfacep *illegalmonitorstateexception* (class-table s))
                    (obtain-and-throw-exception *illegalmonitorstateexception* (list :ireturn object-to-unlock) th s)
                  (error-state :bad-binding-for-illegalmonitorstateexception s))
              ;;fixme think about structured locking.
              (let* ((s (modify th s :monitor-table (decrement-mcount object-to-unlock monitor-table))))
                (return-core val th s)))))
      (return-core val th s))))

(defthm jvm-statep-of-execute-ireturn
  (implies (and (jvm-statep s)
;                (equal inst (current-inst th s))
 ;               (equal (instruction-opcode inst) :ireturn)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-ireturn th s)))
  :hints (("Goal" :in-theory (e/d (execute-ireturn
                                   ;;jvm-statep-def ; todo
                                   current-program ; todo
                                   move-past-invoke-instruction)
                                  (method-program ; todo
                                   )))))

; (FRETURN) Instruction - return a float
(defund execute-FRETURN (th s)
  (let* ((frame (thread-top-frame th s))
         (val (top-operand (stack frame))) ;the value to return
         (syncp (method-synchronizedp (method-info frame))))
    (if syncp
        (let ((monitor-table (monitor-table s))
              (object-to-unlock (addressfix (locked-object frame))))
          (if (null-refp object-to-unlock)
              (obtain-and-throw-exception *nullpointerexception* (list :freturn object-to-unlock) th s)
            (if (not (thread-owns-monitorp th object-to-unlock monitor-table))
                (if (bound-to-a-non-interfacep *illegalmonitorstateexception* (class-table s))
                    (obtain-and-throw-exception *illegalmonitorstateexception* (list :freturn object-to-unlock) th s)
                  (error-state :bad-binding-for-illegalmonitorstateexception s))
              ;;fixme think about structured locking.
              (let* ((s (modify th s :monitor-table (decrement-mcount object-to-unlock monitor-table))))
                (return-core val th s)))))
      (return-core val th s))))

(defthm jvm-statep-of-execute-freturn
  (implies (and (jvm-statep s)
;                (equal inst (current-inst th s))
 ;               (equal (instruction-opcode inst) :freturn)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-freturn th s)))
  :hints (("Goal" :in-theory (e/d (execute-fRETurn
                                   ;;jvm-statep-def ; todo
                                   current-program ; todo
                                   move-past-invoke-instruction)
                                  (method-program ; todo
                                   )))))

;; used for LRETURN and DRETURN.
;move up
(defund return-core-long (val th s)
  (let ((no-explicit-invokep (no-explicit-invokep th s))
        (s (modify th s :call-stack (pop-frame (call-stack th s)))))
    (if (empty-call-stackp (call-stack th s))
        ;;if we are returning from the bottommost frame, there is no caller to catch the value.  fixme think about what to do.
        ;;fixme unschedule the thread?
        (prog2$ (cw "Executing bottom frame.")
                s)
      (let ((s (modify th s :stack (push-long val (stack (thread-top-frame th s))))) ;note the push-long here
            )
        (if no-explicit-invokep
            s
          ;; (move-past-instruction th s)
          (if (memberp (instruction-opcode (current-inst th s)) '(:invokevirtual :invokestatic :invokespecial :invokeinterface :ldc_w :ldc))
              (move-past-invoke-instruction th s)
            s ;(error-state :bad-return-long s) ; todo: put this back, but need more hyps for the loop-lifter
            )
          )))))

(defthm jvm-statep-of-return-core-long
  (implies (and (jvm-statep s)
                (thread-designatorp th)
                (bound-in-alistp th (thread-table s))
                ;; (memberp (instruction-opcode (lookup-equal (pc (top-frame (pop-frame (binding th (thread-table s)))))
                ;;                                            (method-program (method-info (top-frame (pop-frame (binding th (thread-table s))))))))
                ;;          '(:invokevirtual :invokestatic
                ;;            :invokespecial :invokeinterface
                ;;            :ldc_w :ldc))
                )
           (jvm-statep (return-core-long val th s)))
  :hints (("Goal" :in-theory (e/d (return-core-long)))))

; (LRETURN) - return a long
(defund execute-LRETURN (th s)
  (let* ((frame (thread-top-frame th s))
         (val (top-long (stack frame))) ; the value to return
         (syncp (method-synchronizedp (method-info frame))))
    (if syncp
        (let ((monitor-table (monitor-table s))
              (object-to-unlock (addressfix (locked-object frame))))
          (if (null-refp object-to-unlock)
              (obtain-and-throw-exception *NullPointerException* (list :lreturn object-to-unlock) th s)
            (if (not (thread-owns-monitorp th object-to-unlock monitor-table))
                (if (bound-to-a-non-interfacep *illegalmonitorstateexception* (class-table s))
                    (obtain-and-throw-exception *IllegalMonitorStateException* (list :lreturn object-to-unlock) th s)
                  (error-state :bad-binding-for-illegalmonitorstateexception s))
              ;;FIXME Think about structured locking.
              (let* ((s (modify th s :monitor-table (decrement-mcount object-to-unlock monitor-table))))
                (return-core-long val th s)))))
      (return-core-long val th s))))

(defthm jvm-statep-of-execute-lreturn
  (implies (and (jvm-statep s)
;                (equal inst (current-inst th s))
 ;               (equal (instruction-opcode inst) :lreturn)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-lreturn th s)))
  :hints (("Goal" :in-theory (e/d (execute-lreturn
                                   ;;jvm-statep-def ; todo
                                   current-program ; todo
                                   move-past-invoke-instruction)
                                  (method-program ; todo
                                   )))))

; (DRETURN) - return a double
(defund execute-DRETURN (th s)
  (let* ((frame (thread-top-frame th s))
         (val (top-long (stack frame))) ; the value to return
         (syncp (method-synchronizedp (method-info frame))))
    (if syncp
        (let ((monitor-table (monitor-table s))
              (object-to-unlock (addressfix (locked-object frame))))
          (if (null-refp object-to-unlock)
              (obtain-and-throw-exception *NullPointerException* (list :lreturn object-to-unlock) th s)
            (if (not (thread-owns-monitorp th object-to-unlock monitor-table))
                (if (bound-to-a-non-interfacep *illegalmonitorstateexception* (class-table s))
                    (obtain-and-throw-exception *IllegalMonitorStateException* (list :lreturn object-to-unlock) th s)
                  (error-state :bad-binding-for-illegalmonitorstateexception s))
              ;;FIXME Think about structured locking.
              (let* ((s (modify th s :monitor-table (decrement-mcount object-to-unlock monitor-table))))
                (return-core-long val th s)))))
      (return-core-long val th s))))

(defthm jvm-statep-of-execute-dreturn
  (implies (and (jvm-statep s)
;                (equal inst (current-inst th s))
 ;               (equal (instruction-opcode inst) :dreturn)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-dreturn th s)))
  :hints (("Goal" :in-theory (e/d (execute-dreturn
                                   ;;jvm-statep-def ; todo
                                   current-program ; todo
                                   move-past-invoke-instruction)
                                  (method-program ; todo
                                   )))))

; -----------------------------------------------------------------------------
; (ARRAYLENGTH)

(defun execute-ARRAYLENGTH (th s)
  (let* ((arrayref (top-operand (stack (thread-top-frame th s))))
         ;;maybe the encode-unsigned is unecessary (can an array be longer than the max 32-bit int?)
         (length ;(encode-unsigned
          (array-length arrayref (heap s))
          ;)
          ))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand length ;had an nfix here..
                         (pop-operand (stack (thread-top-frame th s)))))))

; (BALOAD)

;; (defund byte-or-bit-fix-val (value type)
;;   (declare (type integer value))
;;   (if (equal type :boolean)
;;       (bvchop 1 value)
;;     (bvsx 32 8 value)))

;; (defthm byte-or-bit-fix-val-when-type-is-boolean
;;   (equal (byte-or-bit-fix-val value :boolean)
;;          (bvchop 1 value))
;;   :hints (("Goal" :in-theory (enable byte-or-bit-fix-val))))

;; (defthm byte-or-bit-fix-val-when-type-is-byte
;;   (equal (byte-or-bit-fix-val value :byte)
;;          (bvsx 32 8 value))
;;   :hints (("Goal" :in-theory (enable byte-or-bit-fix-val))))

;; (defthm byte-or-bit-fix-val-of-0
;;   (equal (byte-or-bit-fix-val 0 type)
;;          0) :hints (("Goal" :in-theory (enable byte-or-bit-fix-val))))

;; (defthm byte-or-bit-fix-val-of-byte-or-bit-fix-val-same-type
;;   (equal (byte-or-bit-fix-val (byte-or-bit-fix-val val type) type)
;;          (byte-or-bit-fix-val val type))
;;   :hints (("Goal" :in-theory (e/d (byte-or-bit-fix-val bvsx) (bvchop-bvchop)))))

;; (defun execute-baload (th s)
;;   (let* ((index (top-operand (stack (thread-top-frame th s))))
;;          (arrayref (top-operand (pop-operand (stack (thread-top-frame th s))))))
;;     (if (null-refp arrayref)
;;         (obtain-and-throw-exception *NullPointerException* (list :baload arrayref) th s)
;;       (let* ((array-object (g arrayref (heap s)))
;; ; Here we intentionally break the get-field/set-field abstraction to avoid wasting time looking up arrayref in heap again below: - yuck!? Perhaps make and use a "get-fields" operator?
;;              (contents (g (acl2::array-contents-pair) array-object)) ;;(acl2::array-contents arrayref (heap s))
;;              (len (len contents)))
;;         (if (or (acl2::sbvlt 32 index 0)
;;                 (acl2::sbvge 32 index len))
;;             (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :baload (decode-signed index) len arrayref) th s)
;;           (modify th s ;fixme this call to modify may generate inefficient stuff?
;;                   :pc (+ 1 ;(inst-length inst)
;;                          (pc (thread-top-frame th s)))
;;                   :stack (push-operand (encode-unsigned
;;                                 (byte-or-bit-fix-val (acl2::bv-array-read 8 len (decode-signed-non-neg index) contents) ;use 1 as the size in the boolean case?
;;                                                      (get-array-component-type (G (acl2::class-pair) array-object))))
;;                                (pop-operand (pop-operand (stack (thread-top-frame th s)))))))))))

;; This instruction can load values that are bytes or Java booleans (0 or 1).
;; We avoid splitting into cases depending on the type of the array elements.
;; An alternative would be to use a bv-array of 1-bit BVs for the boolean
;; case, which would make it a bit more obvious that the value read fits in 1
;; bit.
(defun execute-baload (th s)
  (let* ((frame (thread-top-frame th s))
         (stack (stack frame)))
    (let ((index (top-operand stack))
          (arrayref (top-operand (pop-operand stack))))
      (if (null-refp arrayref)
          (obtain-and-throw-exception *NullPointerException* (list :baload arrayref) th s)
        (let* ((contents (acl2::array-contents arrayref (heap s)))
               (len (len contents)))
          (if (or (acl2::sbvlt 32 index 0)
                  (acl2::sbvge 32 index len))
              (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :baload (decode-signed index) len arrayref) th s)
            (modify th s ;fixme this call to modify may generate inefficient stuff?
                    :pc (+ 1 ;(inst-length inst)
                           (pc frame))
                    ;; The bvsx will do nothing if value is a boolean (0 or 1):
                    :stack (push-operand (bvsx 32 8 (acl2::bv-array-read 8 len (decode-signed-non-neg index) contents))
                                         (pop-operand (pop-operand stack))))))))))


;; ;; (:BASTORE) This instruction is used for both byte arrays and boolean arrays.
;; ;; We'll use 1-bit BVs (and arrays of 1-bit BVs) in the boolean case, since the
;; ;; values can only ever be 0 or 1 (see 2.3.4).  Alternatively, we could just
;; ;; use 8-bit BVs and trust that the values will always be either 0 or 1.
;; (defun execute-BASTORE (th s)
;;   (let* ((value (top-operand (stack (thread-top-frame th s))))
;;          (index (top-operand (pop-operand (stack (thread-top-frame th s)))))
;;          (arrayref (top-operand (pop-operand (pop-operand (stack (thread-top-frame th s)))))))
;;     (if (null-refp arrayref)
;;         (obtain-and-throw-exception *NullPointerException* (list :bastore arrayref) th s)
;;       (let* ((old-array-contents (acl2::get-field arrayref (acl2::array-contents-pair) (heap s)))
;;              ;; must be either :byte or :boolean :
;;              (type (get-array-component-type (acl2::get-class arrayref (heap s))))
;;              (element (if (eq type :byte)
;;                           (bvchop 8 value)
;;                         ;; boolean case:
;;                         (bvchop 1 value)))
;;              (index (decode-signed-non-neg index))
;;              (len (array-length arrayref (heap s)))
;;              (array-contents (acl2::bv-array-write (if (eq type :byte) 8 1)
;;                                                    len
;;                                                    index
;;                                                    element old-array-contents)))
;;         (if (acl2::sbvlt 32 index 0)
;;             (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :bastore (decode-signed index) arrayref) th s)
;;           (if (acl2::sbvlt 32 index len)
;;               ;;normal case:
;;               (modify th s
;;                       :pc (+ 1 ;(inst-length inst)
;;                              (pc (thread-top-frame th s)))
;;                       :stack (pop-operand (pop-operand (pop-operand (stack (thread-top-frame th s)))))
;;                       :heap (acl2::set-field (addressfix arrayref)
;;                                              (acl2::array-contents-pair)
;;                                              array-contents
;;                                              (heap s)))
;;             ;;index too big:
;;             (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :bastore (decode-signed index) arrayref) th s)))))))

;; (:BASTORE) This instruction is used for both byte arrays and boolean arrays.
;; Let's try just using 8-bit BVs and trusting that the values will always be
;; either 0 or 1.  This prevents splitting on the type of the array element.
(defun execute-BASTORE (th s)
  (let* ((top-frame (thread-top-frame th s))
         (stack (stack top-frame)))
    (let ((value (top-operand stack))
          (index (top-operand (pop-operand stack)))
          (arrayref (top-operand (pop-operand (pop-operand stack)))))
      (if (null-refp arrayref)
          (obtain-and-throw-exception *NullPointerException* (list :bastore arrayref) th s)
        (if (acl2::sbvlt 32 index 0)
            (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :bastore (decode-signed index) arrayref) th s)
          (let ((len (array-length arrayref (heap s)))) ;todo: get the contents and then get the len from that
            (if (acl2::sbvlt 32 index len)
                ;;normal case:
                (modify th s
                        :pc (+ 1 ;(inst-length inst)
                               (pc top-frame))
                        :stack (pop-operand (pop-operand (pop-operand stack)))
                        :heap (acl2::set-field (addressfix arrayref)
                                               (acl2::array-contents-pair)
                                               (acl2::bv-array-write 8
                                                                     len
                                                                     index ;; (decode-signed-non-neg index) currently a no-op
                                                                     (bvchop 8 value)
                                                                     (acl2::get-field arrayref (acl2::array-contents-pair) (heap s)))
                                               (heap s)))
              ;;index too big:
              (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :bastore (decode-signed index) arrayref) th s))))))))


; (CALOAD)
(defun execute-CALOAD (th s)
  (let* ((index (top-operand (stack (thread-top-frame th s))))
         (arrayref (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (heap (heap s))
         (contents (acl2::get-field arrayref (acl2::array-contents-pair) heap))
         (len (len contents)))
    (if (null-refp arrayref)
        (obtain-and-throw-exception *NullPointerException* (list :caload arrayref) th s)
      (if (or (acl2::sbvlt 32 index 0)
              (acl2::sbvge 32 index len))
          (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :caload (decode-signed index) arrayref) th s)
        (let ((value ;;the zero extension to an int has no effect
               (acl2::bv-array-read 16 len (decode-signed-non-neg index) contents)))
          (modify th s
                  :pc (+ 1 ;(inst-length inst)
                         (pc (thread-top-frame th s)))
                  :stack (push-operand value
                               (pop-operand (pop-operand (stack (thread-top-frame th s)))))))))))

; (CASTORE)
(defun execute-CASTORE (th s)
  (let* ((frame (thread-top-frame th s))
         (stack (stack frame))
         (value (bvchop 16 (top-operand stack))) ;could drop the bvchop
         (index (top-operand (pop-operand stack)))
         (arrayref (top-operand (pop-operand (pop-operand stack))))
         (heap (heap s))
         (old-array-contents (acl2::get-field arrayref (acl2::array-contents-pair) heap))
         (len (len old-array-contents)))
    (if (null-refp arrayref)
        (obtain-and-throw-exception *NullPointerException* (list :castore arrayref) th s)
      (if (or (acl2::sbvlt 32 index 0)
              (acl2::sbvge 32 index len))
          (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :castore (decode-signed index) arrayref) th s)
        (modify th s
                :pc (+ 1 ;(inst-length inst)
                       (pc frame))
                :stack (pop-operand (pop-operand (pop-operand stack)))
                :heap (acl2::set-field (addressfix arrayref)
                                       (acl2::array-contents-pair)
                                       (acl2::bv-array-write 16 len (decode-signed-non-neg index)
                                                             value old-array-contents)
                                       heap))))))

(defun in-same-packagep (class-name1 class-name2)
  (declare (xargs :guard (and (class-namep class-name1)
                              (class-namep class-name2))))
  (equal (extract-package-name-from-class-name class-name1)
         (extract-package-name-from-class-name class-name2)))

;; Check whether field R, declared in class (or interface?) C (in a symbolic
;; reference that contains a symbolic reference to class T-CLASS), is
;; accessible to class or interface D. See 5.4.4 "Access Control".
(defund field-accessiblep (r c t-class d class-table)
  (declare (xargs :guard (and (field-infop r)
                              (class-namep c) ;todo: allow interfaces?
                              (class-namep t-class) ;todo: allow interfaces? (can't call this t because that means "true")
                              (class-namep d)      ;todo: allow interfaces
                              (class-tablep class-table)
                              (bound-in-class-tablep c class-table))))
  (let* ((public-flag (field-publicp r))
         (protected-flag (field-protectedp r))
         (private-flag (field-privatep r))
         (static-flag (field-staticp r))
         (default-access (not (or public-flag protected-flag private-flag))))
    (or public-flag
        (and protected-flag
             (is-a-classp c class-table)
             (sub-class-or-same-classp d c class-table)
             (implies (not static-flag)
                      (or (sub-class-or-same-classp t-class d class-table)
                          (superclassp t-class d class-table))))
        (and (or protected-flag
                 default-access)
             (and (is-a-classp c class-table)
                  (in-same-packagep c d)))
        (and private-flag
             ;;todo: perform the nestmate test
             (equal c d)))))

;; ;where is this used?
;; (defforall all-non-interfaces (class-name class-table)
;;   (not (class-decl-interfacep (get-class-info class-name class-table)))
;;   :fixed (class-table))


;;; Field Lookup, part of Field Resolution

;;fixme: does this take class names or interface names, or what?

;FIXME, without the counter CTR, the termination of this seems to be depend on there not being cycles of inheritance in the class table..
;also, this search may be inefficient, perhaps querying the same interfaces many times?
(mutual-recursion
 ;; Returns the name of the class that contains the field, or nil if lookup fails.
 ;;FIXME flesh this out (see 5.4.3.2 Field Resolution of the jvm spec)
 ;;FIXME handle interfaces?
 ;;FIXME should we use the field descriptor too (can we have 2 fields with different descriptors?)
 ;;FFIXME do this resolution for all ops that access fields
 (defund lookup-field (field-id c class-table ctr)
   (declare (xargs :measure (+ 1 (nfix ctr))
                   :guard  (and (natp ctr)
                                (class-namep c)
                                (class-tablep class-table)
                                (bound-in-class-tablep c class-table))))
   (if (zp ctr)
       nil ;bozo throw an error - gross to even do it this way
     ;;check this class (or interface):
     (if (not (mbt (bound-in-class-tablep c class-table))) ; todo: drop?
         nil ;todo: pring a message or throw an error!
       (let* ((class-info (get-class-info c class-table))
              (static-field-ids (get-field-ids (class-decl-static-fields class-info)))
              (non-static-field-ids (get-field-ids (class-decl-non-static-fields class-info))))
         (if (or (member-equal field-id static-field-ids)
                 (member-equal field-id non-static-field-ids))
             c ; lookup succeeds
           ;;check the direct superinterfaces:
           (let* ((interface-names (class-decl-interfaces class-info)) ;these are the direct superinterfaces only
                  (match (lookup-field-lst field-id interface-names class-table (+ -1 (nfix ctr)))))
             (if match
                 match
               ;;resolve in the super class (if any)
               (if (or (is-an-interfacep c class-table) ;(class-decl-interfacep class-info) ;an interface doesn't have a superclass
                       (equal "java.lang.Object" c)) ;TODO: Could check for a superclass of :none
                   nil                               ; field lookup fails
                 (let* ((superclass (get-superclass c class-table))) ;fixme optimize to reuse the class-info
                   (lookup-field field-id superclass class-table (+ -1 (nfix ctr))))))))))))

 (defund lookup-field-lst (field-id class-or-interface-names class-table ctr)
   (declare (xargs :measure (+ 1 (nfix ctr))
                   :guard (and (natp ctr)
                               (true-listp class-or-interface-names)
                               (CLASS-NAME-LISTP CLASS-OR-INTERFACE-NAMES)
                               (class-tablep class-table)
                               (all-bound-in-class-tablep class-or-interface-names class-table))))
   (if (zp ctr)
       nil ;bozo throw an error - gross to even do it this way
     (if (atom class-or-interface-names)
         nil
       (let ((match (lookup-field field-id (car class-or-interface-names) class-table (+ -1 (nfix ctr)))))
         (or match
             (lookup-field-lst field-id (cdr class-or-interface-names) class-table (+ -1 (nfix ctr)))))))))

;; TODO: Prove that resolve field always returns a class-namep (or an error)

;;TODO: try this instead:
;(acl2::defopeners lookup-field-lst)
(defthm lookup-field-lst-opener
  (implies (and (not (zp ctr))
                (not (endp class-or-interface-names)))
           (equal (lookup-field-lst field-id class-or-interface-names class-table ctr)
                  (let ((match (lookup-field field-id (car class-or-interface-names) class-table (+ -1 (nfix ctr)))))
                    (or match
                        (lookup-field-lst field-id (cdr class-or-interface-names) class-table (+ -1 (nfix ctr)))))))
  :hints (("Goal" :in-theory (enable lookup-field-lst))))

(defthm lookup-field-lst-base
  (implies (endp class-or-interface-names)
           (equal (lookup-field-lst field-id class-or-interface-names class-table ctr)
                  nil))
  :hints (("Goal" :in-theory (enable lookup-field-lst))))

;(in-theory (disable CLASS-DECL-NON-STATIC-FIELDS CLASS-DECL-STATIC-FIELDS))

(acl2::make-flag lookup-field)

;; (thm
;;  (implies (and (class-tablep CLASS-TABLE)
;;                (NOT (EQUAL "java.lang.Object" C)))
;;           (CLASS-NAMEP (GET-SUPERCLASS C CLASS-TABLE)))
;;  :hints (("Goal" :in-theory (enable class-tablep GET-SUPERCLASS))))

(defthm-flag-lookup-field
 (defthm class-namep-of-lookup-field
   (implies (and (lookup-field field-id c class-table ctr)
                 (class-tablep class-table)
                 (class-namep c))
            (class-namep (lookup-field field-id c class-table ctr)))
   :flag lookup-field)
 (defthm class-namep-of-lookup-field-lst
   (implies (and (lookup-field-lst field-id class-or-interface-names class-table ctr)
                 (class-tablep class-table)
                 (class-name-listp class-or-interface-names))
            (class-namep (lookup-field-lst field-id class-or-interface-names class-table ctr)))
   :flag lookup-field-lst)
 :hints (("Goal" :in-theory (enable lookup-field lookup-field-lst)
          :do-not '(generalize eliminate-destructors))))

(defthm-flag-lookup-field
 (defthm class-infop-of-lookup-field
   (implies (and (lookup-field field-id c class-table ctr)
                 (class-tablep class-table)
                 (class-namep c))
            (class-infop (get-class-info (lookup-field field-id c class-table ctr) class-table)
                         (lookup-field field-id c class-table ctr)))
   :flag lookup-field)
 (defthm class-infop-of-lookup-field-lst
   (implies (and (lookup-field-lst field-id class-or-interface-names class-table ctr)
                 (class-tablep class-table)
                 (class-name-listp class-or-interface-names))
            (class-infop (get-class-info (lookup-field-lst field-id class-or-interface-names class-table ctr) class-table)
                         (lookup-field-lst field-id class-or-interface-names class-table ctr)))
   :flag lookup-field-lst)
 :hints (("Goal" :in-theory (enable lookup-field lookup-field-lst)
          :do-not '(generalize eliminate-destructors))))

(defthm-flag-lookup-field
 (defthm bound-in-class-tablep-of-lookup-field
   (implies (and (lookup-field field-id c class-table ctr)
                 (class-tablep class-table)
                 (class-namep c))
            (bound-in-class-tablep (lookup-field field-id c class-table ctr) class-table))
   :flag lookup-field)
 (defthm bound-in-class-tablep-of-lookup-field-lst
   (implies (and (lookup-field-lst field-id class-or-interface-names class-table ctr)
                 (class-tablep class-table)
                 (class-name-listp class-or-interface-names))
            (bound-in-class-tablep (lookup-field-lst field-id class-or-interface-names class-table ctr) class-table))
   :flag lookup-field-lst)
 :hints (("Goal" :in-theory (enable lookup-field lookup-field-lst BOUND-IN-CLASS-TABLEP)
          :do-not '(generalize eliminate-destructors))))

;move to alists-light
(defthm assoc-EQUAL-of-car-of-car
 (equal (assoc-EQUAL (CAR (CAR alist)) alist)
        (car alist))
 :hints (("Goal" :in-theory (enable assoc-EQUAL))))

;; (defthm lookup-EQUAL-of-car-of-car
;;  (equal (LOOKUP-EQUAL (CAR (CAR alist)) alist)
;;         (cdr (car alist)))
;;  :hints (("Goal" :in-theory (enable LOOKUP-EQUAL))))

;; (thm
;;  (implies (field-info-alistp field-info-alist)
;;           (implies (memberp field-id (get-field-ids field-info-alist))
;;                    (lookup-equal field-id field-info-alist)))
;;  :hints (("Goal" :in-theory (enable get-field-ids field-info-alistp all-keys-bound-to-field-infosp memberp strip-cars))))

;the field-id must be in either the static-fields or the non-static-fields of the class
;; (defthm-flag-lookup-field
;;  (defthm LOOKUP-EQUAL-of-g-of-static-fields-of-lookup-field
;;    (implies (and (lookup-field field-id c class-table ctr)
;;                  (class-tablep class-table)
;;                  (class-namep c)
;;                  (NOT (assoc-EQUAL FIELD-ID (class-decl-non-static-fields (get-class-info (lookup-field field-id c class-table ctr) CLASS-TABLE)))))
;;             (LOOKUP-EQUAL FIELD-ID (class-decl-static-fields (get-class-info (lookup-field field-id c class-table ctr) CLASS-TABLE))))
;;    :flag lookup-field)
;;  (defthm LOOKUP-EQUAL-of-g-of-static-fields-of-lookup-field-lst
;;    (implies (and (lookup-field-lst field-id class-or-interface-names class-table ctr)
;;                  (class-tablep class-table)
;;                  (class-name-listp class-or-interface-names)
;;                  (NOT (assoc-EQUAL FIELD-ID (class-decl-non-static-fields (get-class-info (lookup-field-lst field-id class-or-interface-names class-table ctr) CLASS-TABLE)))))
;;             (LOOKUP-EQUAL FIELD-ID (class-decl-static-fields (get-class-info (lookup-field-lst field-id class-or-interface-names class-table ctr) CLASS-TABLE))))
;;    :flag lookup-field-lst)
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors))))



;; (thm
;;  (implies (LOOKUP-FIELD FIELD-ID CLASS-OR-INTERFACE-NAME CLASS-TABLE count)
;;           (CLASS-INFOP (get-class-info (LOOKUP-FIELD FIELD-ID CLASS-OR-INTERFACE-NAME CLASS-TABLE count) CLASS-TABLE)
;;                        (LOOKUP-FIELD FIELD-ID CLASS-OR-INTERFACE-NAME CLASS-TABLE count))))

(defthm field-infop-of-lookup-equal-gen
  (implies (and; (assoc-equal field-id field-info-alist)
                (field-info-alistp field-info-alist))
           (field-infop (lookup-equal field-id field-info-alist)))
  :hints (("Goal" :in-theory (enable field-info-alistp lookup-equal assoc-equal))))

(defthm field-infop-of-cdr-of-assoc-equal-gen
  (implies (and; (assoc-equal field-id field-info-alist)
                (field-info-alistp field-info-alist))
           (field-infop (cdr (acl2::assoc-equal field-id field-info-alist))))
  :hints (("Goal" :in-theory (enable field-info-alistp assoc-equal))))

;;; Field Resolution

;; The field-id should be among the fields or static-fields of the class-info.
(defun get-field-info (field-id class-info)
  (declare (xargs :guard (and (field-idp field-id)
                              (class-infop0 class-info))))
  (let* ((non-static-fields (class-decl-non-static-fields class-info))
         (static-fields (class-decl-static-fields class-info))
         (non-static-res (assoc-equal field-id non-static-fields)) ;nil is a valid field-infop, so we must check assoc-equal instead of lookup-equal
         )
    (if non-static-res
        (cdr non-static-res)
      (lookup-equal field-id static-fields))))

;Returns (mv erp class-name-of-resolved-field) where ERP, if non-nil, is a
;string (name of an exception to throw) or a cons (indicating an error) and the
;other return value is meaningless.  FIXME: Don't use the counter,
;but I guess it ensures termination (maybe initialize the counter to the number
;of classes in the class table? and similarly for other counters).  See 5.4.3.2
;(Field Resolution).
(defund resolve-field (field-id c d class-table)
  (declare (xargs :guard (and (field-idp field-id)
                              (class-tablep class-table)
                              (class-namep c) ;todo: use this instead: (class-or-interface-namep c) ;can this every be an array class?
                              (class-namep d) ;can this be an interface?
                              (bound-in-class-tablep c class-table))
                  :guard-hints (("Goal" :in-theory (enable alistp-when-field-info-alistp)))))
  (let ((erp (resolve-non-array-class c class-table)))
    (if erp
        (mv erp nil)
      (let ((lookup-result (lookup-field field-id c class-table 10000000)))
        (if (not lookup-result)
            ;; lookup failed:
            (mv *NoSuchFieldError* nil)
          ;; lookup-result is the name of the class that declares the resolved field
          (let* ((class-info (get-class-info lookup-result class-table))
                 (field-info (get-field-info field-id class-info)))
            ;; Apply access control:
            (if (not (field-accessiblep field-info lookup-result c d class-table))
                (mv *IllegalAccessError* nil)
              ;; Note: We do not currently deal with loading constraints in this model.
              ;; Field resolution succeeded:
              (mv nil lookup-result))))))))

(defthm class-namep-of-mv-nth-1-of-resolve-field
  (implies (and (not (mv-nth 0 (resolve-field field-id c d class-table)))
                (class-tablep class-table)
                (class-namep c))
           (class-namep (mv-nth 1 (resolve-field field-id c d class-table))))
  :hints (("Goal" :in-theory (enable resolve-field))))

;; TODO: Consider not separating the static from the non-static fields in the class info?
;Test whether field-id is a static field in the indicated class
(defun field-is-staticp (field-id class-name class-table)
  (declare (xargs :guard (and (field-idp field-id)
                              (class-namep class-name)
                              (class-tablep class-table)
                              (bound-in-class-tablep class-name class-table)
                              )))
  (let* ((class-info (get-class-info class-name class-table))
         (static-field-ids (get-field-ids (class-decl-static-fields class-info))))
    (member-equal field-id static-field-ids)))

;; (:GETFIELD <class-name> <field-id> <long-flag>)
(defun execute-GETFIELD (inst th s)
  (declare (xargs :guard (and (jvm-statep s)
                              (thread-designatorp th)
                              (bound-in-alistp th (thread-table s))
                              (jvm-instruction-okayp inst (pc (thread-top-frame th s)) (strip-cars (method-program (method-info (thread-top-frame th s)))))
                              (equal (car inst) :getfield)
                              (not (empty-call-stackp (binding th (thread-table s)))))
                  :guard-hints (("Goal" :in-theory (enable jvm-instruction-okayp)))
                  :verify-guards nil ;todo
                  ))
  (let ((class-name (farg1 inst)) ;this class-name may not be the class or interface that declared the field ;; cannot be an array class (checked in get-info-from-srf)
        (field-id (farg2 inst))
        (class-table (class-table s))
        (frame (thread-top-frame th s)))
    (mv-let (erp class-name-of-resolved-field)
      (resolve-field field-id class-name (cur-class-name frame) class-table)
      (if erp
          (if (stringp erp)
              (obtain-and-throw-exception erp (list "ERROR in GETFIELD: Failed to resolve field." :debug-info field-id class-name (cur-class-name frame)) th s)
            (error-state erp s))
        (if (field-is-staticp field-id class-name-of-resolved-field class-table)
            (obtain-and-throw-exception *IncompatibleClassChangeError* (list "ERROR in GETFIELD: field should not be static" field-id) th s)
          (let* ((operand-stack (stack frame))
                 (objectref (top-operand operand-stack)))
            (if (null-refp objectref)
                (obtain-and-throw-exception *NullPointerException* (list "ERROR in GETFIELD: object is null." objectref) th s)
              (let* ((value (acl2::get-field objectref (cons class-name-of-resolved-field field-id) (heap s)))
                     (field-type (field-id-type field-id))
                     ;; chars and booleans were truncated by putfield and do
                     ;; not need to be sign extended.
                     (value (if (eq :byte field-type)
                                (bvsx 32 8 value)
                              (if (eq :short field-type)
                                  (bvsx 32 16 value)
                                value))))
                (modify th s
                        :pc (+ 3 ;(inst-length inst)
                               (pc frame))
                        :stack (if (farg3 inst) ;;long-flag
                                   (push-long value
                                              (pop-operand operand-stack))
                                 (push-operand value
                                               (pop-operand operand-stack))))))))))))

;now returns a state, not a heap
;fixme now only used by the decompiler... change it and get rid of this
(defun setstaticfield (class-name field-id value s)
  (make-state (thread-table        s) ;bozo use modify
              (heap                s)
              (class-table         s)
              (heapref-table       s)
              (monitor-table       s)
              (set-static-field class-name field-id value (static-field-map s))
              (initialized-classes s)
              (intern-table s)))

;;TODO: Maybe "initialize" is not the right name for this:
;;TODO: Do we need to handle the ConstantValue attribute of fields here?
(defun initialize-static-fields (field-info-alist class-name static-field-map)
  (declare (xargs :guard (and (field-info-alistp field-info-alist)
                              (class-namep class-name)
                              (static-field-mapp static-field-map))
                  :guard-hints (("Goal" :in-theory (enable field-info-alistp)))))
  (if (endp field-info-alist)
      static-field-map
    (let* ((entry (first field-info-alist))
           (field-id (car entry))
           ;; (field-info (cdr entry))
           (field-type (field-id-type field-id))
           ;; (field-name (field-id-name field-id))
           (default-value (acl2::default-value field-type))
           (static-field-map (set-static-field class-name field-id default-value static-field-map)))
      (initialize-static-fields (rest field-info-alist) class-name static-field-map))))

(defthm static-field-mapp-of-initialize-static-fields
  (implies (static-field-mapp static-field-map)
           (static-field-mapp (initialize-static-fields field-info-alist class-name static-field-map))))

(defconst *dummy-program-to-build-class-object*
  '(;; operand stack: (empty)
    ;; Build the new Class object:
    (0 :NEW "java.lang.Class")
    ;; stack: (bottom) new-ad (top)
    ;; For now, we pass NULL as the class loader:
    (3 :ACONST_NULL)
    ;; stack: (bottom) new-ad NULL (top)
    ;; Run the constructor of the new Class object:
    (4 :invokespecial "java.lang.Class" "<init>" "(Ljava/lang/ClassLoader;)V" ("java.lang.ClassLoader") nil)
    ;; stack: (empty)
    (7 :RETURN) ;void return
    ))

;; Just a check:
(defthm dummy-program-to-build-class-object-okay
  (method-programp *dummy-program-to-build-class-object*)
  :rule-classes nil)

(defconst *dummy-method-to-build-class-object*
  (make-dummy-method-info *dummy-program-to-build-class-object*))

; Push a frame so that we are poised to run *dummy-method-to-build-class-object*.
;; It will run, and eventually get popped off, at which time execution will again be at this instruction, but the class object will have been built.
(defun push-frame-to-build-class-object (class-name th s)
  (declare (xargs :guard (and (jvm-statep s)
                              (thread-designatorp th)
                              (class-namep class-name)
                              (bound-in-alistp th (thread-table s)))
;                  :verify-guards nil
                  ))
  (let ((class-object-ad (acl2::new-ad (acl2::rkeys (heap s)))) ;the dummy method will start by allocating this addres
         )
    (modify th s
            ;; the next time this is checked, there will be a binding for this class
            :heapref-table
            (acons class-name class-object-ad (heapref-table s))
            ;; TODO: should we (do we?) initialize the fields of the object to
            ;; their default values (e.g., 0) right here (the jvm spec
            ;; includes this as part of "preparation")
            :call-stack
            ;; Push a frame for the dummy method that will call the constructor for java.lang.Class
            (push-frame (make-frame 0   ;starting pc
                                    nil ; Pass no args
                                    (empty-operand-stack)
                                    (no-locked-object) ;ffixme
                                    *dummy-method-to-build-class-object*
                                    (make-method-designator "DUMMY-CLASS" "DUMMY-METHOD-TO-BUILD-CLASS-OBJECT" "()V"))
                        (call-stack th s)))))


(in-theory (disable method-abstractp method-nativep)) ; todo move!

;; We leave this disabled and prove an opener for the case when the class-to-initialize is a constant.
(defund invoke-static-initializer-for-class (initialized-classes th s class-to-initialize)
  ;; check whether the class to be initialized has a <clinit> method
  (let* ((class-to-initialize-info (get-class-info class-to-initialize (class-table s)))
         (class-to-initialize-methods (class-decl-methods class-to-initialize-info))
         (class-to-initialize-static-fields (class-decl-static-fields class-to-initialize-info)) ;a map from names to descriptors
         (static-initializer-method (lookup-equal '("<clinit>" . "()V") class-to-initialize-methods))
         ;; Initialize the static fields to their default values:
         (static-field-map (initialize-static-fields class-to-initialize-static-fields class-to-initialize (static-field-map s)))
         (s (modify th s :static-field-map static-field-map))
         ;; Build an object of class Class for this class, if needed (ugh, this would make run mutually recursive with all this stuff):
         )
      ;; Now, if there is a <clinit> method, run it:
    (if static-initializer-method ;fixme can we avoid this if?  when can a class not have a clinit method?
        (if (or (method-abstractp static-initializer-method)
                (method-nativep static-initializer-method))
            (error-state (list "Bad static initializer" static-initializer-method) s)

          ;; we make a state poised to run the <clinit>
          ;; we do not change the PC of the underlying frame, so control will return to this same instruction when the frame is popped
          (modify th s
;really we should initialize the fields of the class to their default values (e.g., 0) right here (the jvm spec includes this as part of "preparation")
;which precedes initilization...
;bbozo we should probably build a class object right now
;bbozo what else do we need to do here?
                  :call-stack
                  (push-frame (make-frame 0 ;starting pc
                                          nil ; A <clinit> method can never have parameters (JVM spec, section 2.9)
                                          (empty-operand-stack)
                                          (no-locked-object) ;ffixme
                                          static-initializer-method ;(g :program static-initializer-method)
                                          (make-method-designator class-to-initialize ;bozo think about field resolution
                                                                  "<clinit>"
                                                                  "()V"))
                              (call-stack th s))
                  ;;we mark the class as initialized (at least, as having its initialization started so we don't try to do it again)
                  :initialized-classes (cons class-to-initialize initialized-classes)))
        ;; If the class has no static initializer method, we just mark it as initialized:
        ;;no changes to the PC, but on the next step, this instruction will find that the class is initialized and will execute normally
        (modify th s
                :initialized-classes (cons class-to-initialize initialized-classes)))))

(defthm jvm-statep-of-invoke-static-initializer-for-class
  (implies (and (class-namep class-to-initialize)
                (jvm-statep s)
                (bound-in-class-tablep class-to-initialize (class-table s))
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th)
;              (not (memberp class-name (initialized-clases s)))
                (class-name-listp initialized-classes)
                )
           (jvm-statep (invoke-static-initializer-for-class initialized-classes th s class-to-initialize)))
  :hints (("Goal" :in-theory (e/d (invoke-static-initializer-for-class)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We leave this disabled and prove an opener for the case when the class-name and superclasses are constants.
(defund invoke-static-initializer-for-next-class-helper (class-name superclass-names th s)
;  (declare (xargs :guard (and (class-namep class-name))))
  (let* ((all-classes (cons class-name superclass-names))
         (classes-in-order (acl2::reverse-list all-classes)) ;we start with the "oldest" ancestor class
         ;; we know that at least one class will need to be initialized
         ;; the one to be inititalized on this iteration will be the oldest ancestor class
         (initialized-classes (initialized-classes s))
         (class-to-initialize (acl2::first-non-member classes-in-order initialized-classes))
         (dummy (cw "~%Initializing class ~s0.~%" class-to-initialize)))
    (declare (ignore dummy))
    (invoke-static-initializer-for-class initialized-classes th s class-to-initialize)))

;move
(defthm class-namep-of-first-non-member
  (implies (and (class-name-listp items)
                (not (ACL2::SUBSETP-EQ items items-to-exclude))) ;ensures it finds an item
           (class-namep (acl2::first-non-member items items-to-exclude)))
  :hints (("Goal" :in-theory (enable ;class-name-listp
                              ))))


(defthm all-bound-in-class-tablep-of-reverse-list
  (equal (all-bound-in-class-tablep (acl2::reverse-list x) class-table)
         (all-bound-in-class-tablep x class-table))
  :hints (("Goal" :in-theory (enable all-bound-in-class-tablep))))

(defthm bound-in-class-tablep-of-first-non-member
  (implies (and (all-bound-in-class-tablep class-names class-table)
                (acl2::first-non-member class-names class-names-to-exclude))
           (bound-in-class-tablep (acl2::first-non-member class-names class-names-to-exclude) class-table))
  :hints (("Goal" :in-theory (enable all-bound-in-class-tablep))))

(defthm first-non-member-iff
  (implies (class-name-listp items)
           (iff (acl2::first-non-member items items-to-exclude)
                (not (acl2::subsetp-equal items items-to-exclude))))
  :hints (("Goal" :in-theory (enable acl2::subsetp-equal))))

(defthm subsetp-equal-of-reverse-list
  (equal (acl2::subsetp-equal (acl2::reverse-list x) y)
         (acl2::subsetp-equal x y))
  :hints (("Goal" :in-theory (enable acl2::subsetp-equal))))

(defthm jvm-statep-of-invoke-static-initializer-for-next-class-helper
  (implies (and (class-namep class-name)
                (class-name-listp superclass-names)
                (all-bound-in-class-tablep superclass-names (class-table s))
                (jvm-statep s)
                (bound-in-class-tablep class-name (class-table s))
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th)
                (not (memberp class-name (initialized-classes s))))
           (jvm-statep (invoke-static-initializer-for-next-class-helper class-name superclass-names th s)))
  :hints (("Goal" :in-theory (enable invoke-static-initializer-for-next-class-helper))))

;; Initialize at least one class, either CLASS-NAME or one of its superclasses.
;; We leave this disabled and prove an opener for the case when the class-name is a constant.
(defund invoke-static-initializer-for-next-class (class-name th s)
  (invoke-static-initializer-for-next-class-helper class-name
                                                   (get-superclasses class-name (class-table s))
                                                   th
                                                   s))

(defthm jvm-statep-of-invoke-static-initializer-for-next-class
  (implies (and (class-namep class-name)
                (jvm-statep s)
                (bound-in-class-tablep class-name (class-table s))
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th)
                (not (memberp class-name (initialized-classes s))))
           (jvm-statep (invoke-static-initializer-for-next-class class-name th s)))
  :hints (("Goal" :in-theory (enable invoke-static-initializer-for-next-class))))

;; (:GETSTATIC class-name field-id long-flag)
(defun execute-GETSTATIC (inst th s)
  (let* ((class-name (farg1 inst)) ;this class-name may not be the class or interface that declared the field (todo: what if this is an array class?  same for putstatic)
         (field-id (farg2 inst))
         (class-table (class-table s))
         (frame (thread-top-frame th s))
         (current-class-name (cur-class-name frame)))
    (mv-let (erp class-name-of-resolved-field)
      (resolve-field field-id class-name current-class-name class-table)
      (if erp
          (if (stringp erp)
              (obtain-and-throw-exception erp (list "ERROR IN GETSTATIC: Failed to resolve field." :debug-info field-id class-name current-class-name) th s)
            (error-state erp s))
        ;; (if (not (class-namep class-name-of-resolved-field)) ;can this happen? is this needed for guard proofs?
        ;;     (error-state (list 'Invalid-field-name 'execute-GETFIELD field-id class-name) s)
        (if (and (not (field-is-staticp field-id class-name-of-resolved-field class-table))
                 (not (is-an-interfacep class-name-of-resolved-field class-table)))
            (obtain-and-throw-exception *IncompatibleClassChangeError* (list "Error: field should be static" field-id) th s)
          (let ((initialized-classes (initialized-classes s)))
            (if (memberp class-name-of-resolved-field initialized-classes)
                ;; If the class has been initialized, do the normal thing:
                (let* ((long-flag (farg3 inst))
                       (field-value (get-static-field class-name-of-resolved-field field-id (static-field-map s))))
                  ;; Something like this check may be needed if we ever skip
                  ;; <clinit> methods with code that we cannot handle.
                  ;; However, this requires additional loop invariants about
                  ;; static fields being initialized...
                  ;; (if (not field-value)
                  ;;     (error-state (list 'nil-value-for-static-field--may-be-unitialized class-name field-id 'execute-GETSTATIC) s)
                  (modify th s
                          :pc (+ 3 ;(inst-length inst)
                                 (pc (thread-top-frame th s)))
                          :stack (if long-flag
                                     (push-long field-value (stack (thread-top-frame th s)))
                                   (push-operand field-value (stack (thread-top-frame th s)))))
;)
                  )
              ;; otherwise, we first need to initialize at least one class (this leaves us back at the PC of the getstatic instruction)
              (invoke-static-initializer-for-next-class class-name-of-resolved-field th s))))))))

;old:
;; (defun execute-GETSTATIC (inst th s)
;;   (let* ((class-name (farg1 inst))
;;          (field-name (farg2 inst))
;;          (long-flag (farg3 inst))
;; ;(class-decl-heapref (get-class-info class-name (class-table s)))
;; ;         (class-ref (g class-name (heapref-table s)))
;; ;        (field-value (acl2::get-field class-ref (cons "java.lang.Class" field-name) (heap s)))
;;          (field-value (get-static-field class-name field-name (static-field-map s)))
;;          )
;;     (modify th s
;;             :pc (+ (inst-length inst) (pc (thread-top-frame th s)))
;;             :stack (if long-flag
;;                        (push-operand 0 (push-operand field-value (stack (thread-top-frame th s))))
;;                      (push-operand field-value (stack (thread-top-frame th s)))))))

;fixme could combine these?

;; (:GOTO branch-offset)
;; branch-offset is a signed 16-bit offset
(defund execute-GOTO (inst th s)
  (let ((branch-offset (farg1 inst)))
    (modify th s
            :pc (+ branch-offset (pc (thread-top-frame th s))))))

;; add polarity?
;(acl2::defopeners jvm-instruction-okayp :hyps ((equal (instruction-opcode inst) keyword) (syntaxp (quotep keyword))))


;; (local
;;  (defthm goto-helper-1
;;    (implies (and (equal (instruction-opcode inst) :goto)
;;                  (pcp pc)
;;                  (instructionp inst))
;;             (pcp (+ (cadr ; farg1
;;                      inst)
;;                     pc)))
;;    :hints (("Goal" :in-theory (enable instructionp valid-pcp instruction-opcode instruction-argsp pcp)))))

;; this one is more complex because the property depends on the PC
(local
 (defthm goto-helper-1
   (implies (and (member-equal (instruction-opcode (current-inst th s)) '(:goto :jsr :goto_w :jsr_w))
                 (jvm-instruction-okayp (current-inst th s)
                                        (pc (top-frame (binding th (thread-table s))))
                                        ;; valid-pcs
                                        (strip-cars (method-program (method-info (top-frame (binding th (thread-table s))))))))
            (pcp (+ (cadr (current-inst th s))
                    (pc (top-frame (binding th (thread-table s)))))))
   :hints (("Goal" :in-theory (enable jvm-instruction-okayp valid-pcp)))))

;move!
(defthmd memberp-constant-opener
  (implies (syntaxp (quotep x))
           (equal (memberp a x)
                  (if (not (consp x))
                      nil
                    (or (equal a (car x))
                        (memberp a (cdr x)))))))

(local
 (defthm goto-helper-2
   (implies (and (member-equal (instruction-opcode inst) '(:goto :jsr :goto_w :jsr_w))
                 (jvm-instruction-okayp inst pc valid-pcs))
            (memberp (+ (cadr inst) pc) valid-pcs))
   :hints (("Goal" :in-theory (enable jvm-instruction-okayp valid-pcp memberp-constant-opener)))))

(defthm jvm-statep-of-execute-goto
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :goto)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-GOTO inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-GOTO method-programp-key-property-2-alt valid-pcp)
                           (method-program current-inst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (:GOTO_W branch-offset)
;; branch-offset is a signed 32-bit offset
(defund execute-GOTO_W (inst th s)
  (let ((branch-offset (farg1 inst)))
    (modify th s
            :pc (+ branch-offset (pc (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-goto_w
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :goto_w)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-GOTO_W inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-GOTO_W method-programp-key-property-2-alt valid-pcp)
                           (method-program current-inst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (:I2B)
(defun execute-I2B (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand ;(byte-fix (top-operand (stack (thread-top-frame th s))))
                  (bvsx 32 8 (bvchop 8 (top-operand (stack (thread-top-frame th s)))))
                  (pop-operand (stack (thread-top-frame th s))))))

;; (:I2C)
(defun execute-I2C (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (bvchop 16 (top-operand (stack (thread-top-frame th s)))) ;zero-extending to an int isn't needed
                       (pop-operand (stack (thread-top-frame th s))))))

;; (:I2L)
(defun execute-I2L (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long (bvsx 64 32 (top-operand (stack (thread-top-frame th s)))) ;wrap the top??
                            (pop-operand (stack (thread-top-frame th s))))))

;; (:I2S) Instruction
(defun execute-I2S (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (bvsx 32 16 (bvchop 16 (top-operand (stack (thread-top-frame th s)))))
                       (pop-operand (stack (thread-top-frame th s))))))

;;
;; math operations on ints:
;;

; (ISUB)
;fixme make sure the bit patterns are the same regardless of whether the operands are signed or unsigned
(defun execute-ISUB (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (bvminus 32
                                      (top-operand (pop-operand (stack (thread-top-frame th s))))
                                      (top-operand (stack (thread-top-frame th s))))
                       (pop-operand (pop-operand (stack (thread-top-frame th s)))))))

; (IMUL)
;fixme make sure the bit patterns are the same regardless of whether the operands are signed or unsigned
(defun execute-IMUL (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (bvmult 32
                                     (top-operand (pop-operand (stack (thread-top-frame th s))))
                                     (top-operand (stack (thread-top-frame th s))))
                       (pop-operand (pop-operand (stack (thread-top-frame th s)))))))

; (IADD)
(defun execute-IADD (th s)
  ;; (declare (xargs :guard (and (jvm-statep s)
  ;;                             (thread-designatorp th)
  ;;                             (bound-in-alistp th (thread-table s))
  ;;                             (not (equal 0 (call-stack-size (binding th (thread-table s)))))
  ;;                             )))
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (bvplus 32
                                       (top-operand (pop-operand (stack (thread-top-frame th s))))
                                       (top-operand (stack (thread-top-frame th s))))
                               (pop-operand (pop-operand (stack (thread-top-frame th s)))))))

; (INEG)
;; Note: Because of the way the JVM represents 2's complement ints, the negation of the most negative int is itself.
(defun execute-INEG (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (bvminus 32 0 (top-operand (stack (thread-top-frame th s)))) ;no need to decode arg?
                       (pop-operand (stack (thread-top-frame th s))))))

;; Test for the "special case" for IDIV:
(assert-event (equal (acl2::sbvdiv 32 *min-signed-int32* -1) *min-signed-int32*))

;; (:IDIV)
;; ;FIXME is this correct? seems okay...
;; (defund idiv (n d)
;;   (int-fix (truncate n d)))
;FIXME handle overflow case!
;fixme prove properties from JVM spec -- see ../bv/bv-tests.lisp
(defun execute-IDIV (th s)
  (let* ((value1 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (value2 (top-operand (stack (thread-top-frame th s)))) ;the divisor
         (result (acl2::sbvdiv 32 value1 value2)))
    (if (eql 0 value2) ; todo: use =
        (obtain-and-throw-exception *ArithmeticException* (list :idiv value1 value2) th s)
      (modify th s
              :pc (+ 1 ;(inst-length inst)
                     (pc (thread-top-frame th s)))
              :stack (push-operand result
                                   (pop-operand (pop-operand (stack (thread-top-frame th s)))))))))

; (IAND)
(defun execute-IAND (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (bvand 32
                                    (top-operand (pop-operand (stack (thread-top-frame th s))))
                                    (top-operand (stack (thread-top-frame th s))))
                       (pop-operand (pop-operand (stack (thread-top-frame th s)))))))

; (IOR)
(defun execute-IOR (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (bvor 32
                                   (top-operand (pop-operand (stack (thread-top-frame th s))))
                                   (top-operand (stack (thread-top-frame th s))))
                       (pop-operand (pop-operand (stack (thread-top-frame th s)))))))

; (IXOR)
(defun execute-IXOR (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (bvxor 32
                                    (top-operand (pop-operand (stack (thread-top-frame th s))))
                                    (top-operand (stack (thread-top-frame th s))))
                       (pop-operand (pop-operand (stack (thread-top-frame th s)))))))

;;bozo could abstract out (pop-operand stack) too
;;bbozo some redundancy between call-stack and top-frame

; (IALOAD)
(defun execute-iaload (th s)
  (let ((top-frame (thread-top-frame th s)))
    (let ((stack (stack top-frame))
          (heap (heap s)))
      (let ((index (top-operand stack))
            (arrayref (top-operand (pop-operand stack))))
        (if (null-refp arrayref)
            (obtain-and-throw-exception *NullPointerException* (list :iaload arrayref) th s)
          (let* ((contents (acl2::get-field arrayref (acl2::array-contents-pair) heap))
                 (len (len contents)))
            (if (or (acl2::sbvlt 32 index 0) ;bbozo crud the "or" here (or maybe the >=) can cause case splitting
                    (acl2::sbvge 32 index len))
                (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :iaload (decode-signed index) arrayref) th s)
; FFIXME the modify macro seems inefficient - its expansion often contains many mentions of things like (thread-top-frame TH S)
;also, it doesn't use vars bound by enclosing lets (often we will have bound (thread-top-frame TH S) already in the function...)
              ;;                               (modify th s
              ;;                                       :pc (+ (inst-length inst) (pc top-frame))
              ;;                                       :stack (push-operand (acl2::bv-array-read 32 len index contents)
              ;;                                                    (pop-operand (pop-operand stack))))
              (MAKE-STATE
               (BIND
                TH
                (PUSH-frame (MAKE-FRAME (BINARY-+ 1 ;(INST-LENGTH INST)
                                                  (PC TOP-FRAME))
                                        (LOCALS top-frame)
                                        (PUSH-operand (ACL2::BV-ARRAY-READ 32 LEN
                                                                           (decode-signed-non-neg index)
                                                                           CONTENTS)
                                                      (POP-OPERAND (POP-OPERAND STACK)))
                                        (locked-object top-frame)
                                        (method-info top-frame)
                                        (method-designator top-frame))
                            (POP-frame (CALL-STACK TH S)))
                (THREAD-TABLE S))
               heap
               (CLASS-TABLE S)
               (HEAPREF-TABLE S)
               (monitor-TABLE S)
               (STATIC-FIELD-MAP S)
               (initialized-classes s)
               (intern-table s)))))))))



;old:
;; (defun execute-IALOAD (inst th s)
;;   (let* ((index (top-operand (stack (thread-top-frame th s))))
;;          (arrayref (top-operand (pop-operand (stack (thread-top-frame th s)))))
;;          ;;(array (my-deref arrayref (heap s)))
;;          ;;FIXME should we intfix the value?  not logically necessary, but might help in the proofs?
;;          (value (array-element32 arrayref index (heap s)))
;;          )
;;     (possible-exception (or (< index 0) ;FFIXME CRUD the "or" here (or maybe the >=) can cause case splitting
;;                             (>= index (array-length arrayref (heap s))))
;;                         (error-state (list 'ArrayIndexOutOfBoundsException 'IALOAD index arrayref) s)
;;                         (modify th s
;;                                 :pc (+ (inst-length inst) (pc (thread-top-frame th s)))
;;                                 :stack (push-operand value ;(element-at index array)
;;                                              (pop-operand (pop-operand (stack (thread-top-frame th s)))))))))

;; ;use lets? maybe i don't need this anymore?
;; (defthm execute-IALOAD-rewrite
;;   (implies (and (>= (top-operand (stack (thread-top-frame th s))) 0)
;;                 (< (top-operand (stack (thread-top-frame th s)))
;;                    (array-length (top-operand (pop-operand (stack (thread-top-frame th s)))) (heap s))))
;;            (equal (execute-IALOAD inst th s)
;;                   (modify th s
;;                           :pc (+ (inst-length inst) (pc (thread-top-frame th s)))
;;                           :stack (push-operand (array-element32 (top-operand (pop-operand (stack (thread-top-frame th s))))
;;                                                         (top-operand (stack (thread-top-frame th s)))
;;                                                         (heap s))
;;                                        (pop-operand (pop-operand (stack (thread-top-frame th s))))))))
;;   :hints (("Goal" :in-theory (disable INST-LENGTH))))

; (IASTORE)
(defun execute-IASTORE (th s)
;;;TODO: put in let instead of let* when possible - some of these bindings can be done in parallel
  (let* ((value (top-operand (stack (thread-top-frame th s))))
         (index (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (arrayref (top-operand (pop-operand (pop-operand (stack (thread-top-frame th s)))))))
    (if (null-refp arrayref)
        (obtain-and-throw-exception *NullPointerException* (list :iastore arrayref) th s)
      (let* ((old-array-contents (acl2::get-field arrayref (acl2::array-contents-pair) (heap s)))
             (len (len old-array-contents)))
        (if (or (acl2::sbvlt 32 index 0)
                (acl2::sbvge 32 index len))
            (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :iastore (decode-signed index) arrayref) th s)
          (modify th s
                  :pc (+ 1 ;(inst-length inst)
                         (pc (thread-top-frame th s)))
                  :stack (pop-operand (pop-operand (pop-operand (stack (thread-top-frame th s)))))
                  :heap (acl2::set-field (addressfix arrayref) ;why the addressfix here?  should we do it in more places?
                                         (acl2::array-contents-pair)
                                         (acl2::bv-array-write 32 len
                                                               (decode-signed-non-neg index)
                                                               value old-array-contents)
                                         (heap s))))))))

;;;
;;; pc-if
;;;

(defund pc-if (test pc1 pc2)
  (declare (xargs :guard t))
  (if test pc1 pc2))

(defthm pc-if-when-test-is-constant
  (implies (syntaxp (quotep test))
           (equal (pc-if test pc1 pc2)
                  ;; the IF should always be resolved:
                  (if test pc1 pc2)))
  :hints (("Goal" :in-theory (enable pc-if))))

(defthm pcp-of-pc-if
  (equal (pcp (pc-if test x y))
         (if test
             (pcp x)
           (pcp y)))
  :hints (("Goal" :in-theory (enable pc-if))))

;; TODO: these branch instructions now take signed offsets, not PCs to jump to,
;; but we could resolve the target ahead of time and just store the pc to jump
;; to.  Actually, perhaps we could always resolve the new PC values statically.

(local
 (defthmd if-helper-1
   (implies (and (member-equal (instruction-opcode (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s)))))))
                               '(:if_acmpeq :if_acmpne
                                 :if_icmpeq :if_icmpne :if_icmplt :if_icmpge :if_icmpgt :if_icmple
                                 :ifeq :ifne :iflt :ifge :ifgt :ifle
                                 :ifnull :ifnonnull))
                 (jvm-instruction-okayp (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s))))))
                                        (pc (top-frame (binding th (thread-table s))))
                                        ;; valid-pcs
                                        (strip-cars (method-program (method-info (top-frame (binding th (thread-table s))))))))
            (pcp (+ (pc (top-frame (binding th (thread-table s))))
                    (cadr (lookup-equal (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s))))))))))
   :hints (("Goal" :in-theory (enable jvm-instruction-okayp valid-pcp)))))

(local
 (defthmd if-helper-3
   (implies (and (member-equal (instruction-opcode (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s)))))))
                               '(:if_acmpeq :if_acmpne
                                 :if_icmpeq :if_icmpne :if_icmplt :if_icmpge :if_icmpgt :if_icmple
                                 :ifeq :ifne :iflt :ifge :ifgt :ifle
                                 :ifnull :ifnonnull))
                 (jvm-instruction-okayp (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s))))))
                                        (pc (top-frame (binding th (thread-table s))))
                                        ;; valid-pcs
                                        (strip-cars (method-program (method-info (top-frame (binding th (thread-table s))))))))
            (memberp (+ (pc (top-frame (binding th (thread-table s))))
                        (cadr (lookup-equal (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s))))))))
                     (strip-cars (method-program (method-info (top-frame (binding th (thread-table s))))))))
   :hints (("Goal" :in-theory (enable jvm-instruction-okayp valid-pcp)))))

(local
 (defthmd if-helper-2
   (implies (and (member-equal (instruction-opcode inst)
                               '(:if_acmpeq :if_acmpne
                                 :if_icmpeq :if_icmpne :if_icmplt :if_icmpge :if_icmpgt :if_icmple
                                 :ifeq :ifne :iflt :ifge :ifgt :ifle
                                 :ifnull :ifnonnull))
                 (jvm-instruction-okayp inst pc valid-pcs))
            (memberp (+ (farg1 inst) pc) valid-pcs))
   :hints (("Goal" :in-theory (enable jvm-instruction-okayp valid-pcp)))))

; (IF_ACMPEQ signed-offset)
;fixme should these have the if lifted above the make-state?
(defund execute-IF_ACMPEQ (inst th s)
  (modify th s
          :pc (pc-if (equal (top-operand (pop-operand (stack (thread-top-frame th s))))
                           (top-operand (stack (thread-top-frame th s))))
                    (+ (farg1 inst) (pc (thread-top-frame th s)))
                    (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s))))
          :stack (pop-operand (pop-operand (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-IF_ACMPEQ
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :IF_ACMPEQ)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-IF_ACMPEQ inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-IF_ACMPEQ
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IF_ACMPNE signed-offset)
(defund execute-IF_ACMPNE (inst th s)
  (modify th s
          :pc (pc-if (equal (top-operand (pop-operand (stack (thread-top-frame th s))))
                           (top-operand (stack (thread-top-frame th s))))
                    (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s)))
                    (+ (farg1 inst) (pc (thread-top-frame th s))))
          :stack (pop-operand (pop-operand (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-IF_ACMPNE
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :IF_ACMPNE)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-IF_ACMPNE inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-IF_ACMPNE
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IF_ICMPEQ signed-offset)
(defund execute-IF_ICMPEQ (inst th s)
  (modify th s
          :pc (pc-if (equal (top-operand (pop-operand (stack (thread-top-frame th s))))
                           (top-operand (stack (thread-top-frame th s))))
                    (+ (farg1 inst) (pc (thread-top-frame th s)))
                    (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s))))
          :stack (pop-operand (pop-operand (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-IF_ICMPEQ
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :IF_ICMPEQ)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-IF_ICMPEQ inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-IF_ICMPEQ
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IF_ICMPGE signed-offset)
(defund execute-IF_ICMPGE (inst th s)
  (modify th s
          :pc (pc-if (acl2::sbvlt 32
                                 (top-operand (pop-operand (stack (thread-top-frame th s))))
                                 (top-operand (stack (thread-top-frame th s))))
                    (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s)))
                    (+ (farg1 inst) (pc (thread-top-frame th s))))
          :stack (pop-operand (pop-operand (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-IF_ICMPGE
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :IF_ICMPGE)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-IF_ICMPGE inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-IF_ICMPGE
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IF_ICMPGT signed-offset)
(defund execute-IF_ICMPGT (inst th s)
  (modify th s
          :pc (pc-if (acl2::sbvlt 32
                                 (top-operand (stack (thread-top-frame th s)))
                                 (top-operand (pop-operand (stack (thread-top-frame th s)))))
                    (+ (farg1 inst) (pc (thread-top-frame th s)))
                    (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s))))
          :stack (pop-operand (pop-operand (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-IF_ICMPGT
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :IF_ICMPGT)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-IF_ICMPGT inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-IF_ICMPGT
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IF_ICMPLT signed-offset)
(defund execute-IF_ICMPLT (inst th s)
  (modify th s
          :pc (pc-if (acl2::sbvlt 32
                                 (top-operand (pop-operand (stack (thread-top-frame th s))))
                                 (top-operand (stack (thread-top-frame th s))))
                    (+ (farg1 inst) (pc (thread-top-frame th s)))
                    (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s))))
          :stack (pop-operand (pop-operand (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-IF_ICMPLT
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :IF_ICMPLT)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-IF_ICMPLT inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-IF_ICMPLT
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IF_ICMPLE signed-offset)
(defund execute-IF_ICMPLE (inst th s)
  (modify th s
          :pc (pc-if (acl2::sbvlt 32
                                 (top-operand (stack (thread-top-frame th s)))
                                 (top-operand (pop-operand (stack (thread-top-frame th s)))))
                    (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s)))
                    (+ (farg1 inst) (pc (thread-top-frame th s))))
          :stack (pop-operand (pop-operand (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-IF_ICMPLE
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :IF_ICMPLE)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-IF_ICMPLE inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-IF_ICMPLE
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IF_ICMPNE signed-offset)
(defund execute-IF_ICMPNE (inst th s)
  (modify th s
          :pc (pc-if (equal (top-operand (pop-operand (stack (thread-top-frame th s))))
                           (top-operand (stack (thread-top-frame th s))))
                    (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s)))
                    (+ (farg1 inst) (pc (thread-top-frame th s))))
          :stack (pop-operand (pop-operand (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-IF_ICMPNE
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :IF_ICMPNE)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-IF_ICMPNE inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-IF_ICMPNE
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IFEQ signed-offset)
(defund execute-IFEQ (inst th s)
  (modify th s
          :pc (pc-if (equal (top-operand (stack (thread-top-frame th s)))
                           0)
                    (+ (farg1 inst) (pc (thread-top-frame th s)))
                    (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s))))
          :stack (pop-operand (stack (thread-top-frame th s)))))

(defthm jvm-statep-of-execute-ifeq
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :ifeq)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-ifeq inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-ifeq
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IFGE signed-offset)
;(using sbvle or sbvge here would expand to a term with a not, which expands to an if, so i just used sbvlt)
(defund execute-IFGE (inst th s)
  (modify th s
          :pc (pc-if (acl2::sbvlt 32 (top-operand (stack (thread-top-frame th s))) 0)
                    (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s)))
                    (+ (farg1 inst) (pc (thread-top-frame th s))))
          :stack (pop-operand (stack (thread-top-frame th s)))))

(defthm jvm-statep-of-execute-ifge
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :ifge)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-ifge inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-ifge
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IFGT signed-offset)
(defund execute-IFGT (inst th s)
  (modify th s
          :pc (pc-if (acl2::sbvlt 32 0 (top-operand (stack (thread-top-frame th s))))
                    (+ (farg1 inst) (pc (thread-top-frame th s)))
                    (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s))))
          :stack (pop-operand (stack (thread-top-frame th s)))))

(defthm jvm-statep-of-execute-ifgt
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :ifgt)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-ifgt inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-ifgt
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IFLE signed-offset)
(defund execute-IFLE (inst th s)
  (modify th s
          :pc (pc-if (acl2::sbvlt 32 0 (top-operand (stack (thread-top-frame th s))))
                    (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s)))
                    (+ (farg1 inst) (pc (thread-top-frame th s))))
          :stack (pop-operand (stack (thread-top-frame th s)))))

(defthm jvm-statep-of-execute-ifle
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :ifle)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-ifle inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-ifle
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IFLT signed-offset)
(defund execute-IFLT (inst th s)
  (modify th s
          :pc (pc-if (acl2::sbvlt 32 (top-operand (stack (thread-top-frame th s))) 0)
                    (+ (farg1 inst) (pc (thread-top-frame th s)))
                    (+ 3;(inst-length inst)
                       (pc (thread-top-frame th s))))
          :stack (pop-operand (stack (thread-top-frame th s)))))

(defthm jvm-statep-of-execute-iflt
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :iflt)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-iflt inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-iflt
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IFNE signed-offset)
(defund execute-IFNE (inst th s)
  (modify th s
          :pc (pc-if (equal 0 (top-operand (stack (thread-top-frame th s))))
                    (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s)))
                    (+ (farg1 inst) (pc (thread-top-frame th s))))
          :stack (pop-operand (stack (thread-top-frame th s)))))

(defthm jvm-statep-of-execute-ifne
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :ifne)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-ifne inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-ifne
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IFNONNULL signed-offset)
(defund execute-IFNONNULL (inst th s)
  (modify th s
          :pc (pc-if (acl2::null-refp (top-operand (stack (thread-top-frame th s))))
                    (+ 3;(inst-length inst)
                       (pc (thread-top-frame th s)))
                    (+ (farg1 inst) (pc (thread-top-frame th s))))
          :stack (pop-operand (stack (thread-top-frame th s)))))

(defthm jvm-statep-of-execute-ifnonnull
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :ifnonnull)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-ifnonnull inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-ifnonnull
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            If-helper-1
                            IF-helper-2
                            IF-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (IFNULL signed-offset)
(defund execute-IFNULL (inst th s)
  (modify th s
          :pc (pc-if (acl2::null-refp (top-operand (stack (thread-top-frame th s))))
                    (+ (farg1 inst) (pc (thread-top-frame th s)))
                    (+ 3;(inst-length inst)
                       (pc (thread-top-frame th s))))
          :stack (pop-operand (stack (thread-top-frame th s)))))

(defthm jvm-statep-of-execute-ifnull
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :ifnull)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-IFNULL inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-IFNULL
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp pc-if
                            if-helper-1
                            if-helper-2
                            if-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthmd iinc-helper-1
   (implies (and (member-equal (instruction-opcode (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s)))))))
                               '(:iinc))
                 ;(instructionp (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s)))))))
                 (jvm-instruction-okayp (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s))))))
                                        (pc (top-frame (binding th (thread-table s))))
                                        ;; valid-pcs
                                        (strip-cars (method-program (method-info (top-frame (binding th (thread-table s))))))))
            (pcp (+ (pc (top-frame (binding th (thread-table s))))
                    (cadddr (lookup-equal (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s))))))))))
   :hints (("Goal" :in-theory (enable jvm-instruction-okayp valid-pcp)))))

(local
 (defthmd iinc-helper-3
   (implies (and (member-equal (instruction-opcode (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s)))))))
                               '(:iinc))
                 (jvm-instruction-okayp (lookup (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s))))))
                                        (pc (top-frame (binding th (thread-table s))))
                                        ;; valid-pcs
                                        (strip-cars (method-program (method-info (top-frame (binding th (thread-table s))))))))
            (memberp (+ (pc (top-frame (binding th (thread-table s))))
                        (cadddr (lookup-equal (pc (top-frame (binding th (thread-table s)))) (method-program (method-info (top-frame (binding th (thread-table s))))))))
                     (strip-cars (method-program (method-info (top-frame (binding th (thread-table s))))))))
   :hints (("Goal" :in-theory (enable jvm-instruction-okayp valid-pcp)))))


; (IINC localslotnum signed-const) - where const is a signed 8-bit or 16-bit quantity (depending on whether WIDE preceded the iinc)
;simplify the body?  we didn't have the bvsx before
;fixme think about the bvsx
(defund execute-IINC (inst th s)
  (let ((inst-length (farg3 inst))) ;depends on whether the instruction was preceded by WIDE
    (modify th s
            :pc (+ inst-length
                   (pc (thread-top-frame th s)))
            :locals (update-nth-local (farg1 inst)
                                      (bvplus 32
;                                              (bvsx 32 8 - the bvxs wouldn't work for a 16-bit increment amount
                                                    (farg2 inst) ;the increment amount
;)
                                                    (nth-local (farg1 inst)
                                                               (locals (thread-top-frame th s))))
                                      (locals (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-iinc
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :iinc)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-IINC inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-IINC
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp
                            iinc-helper-1
                            iinc-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (:ILOAD local-slot-num inst-len) Instruction - Push a local onto the stack
(defund execute-ILOAD (inst th s)
  (let ((inst-len (farg2 inst))) ;length can vary because of WIDE
    (modify th s
            :pc (+ inst-len
                   (pc (thread-top-frame th s)))
            :stack (push-operand (nth-local (farg1 inst)
                                            (locals (thread-top-frame th s)))
                                 (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-iload
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :iload)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-ILOAD inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-ILOAD
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp
                            load-helper-1
                            load-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; -----------------------------------------------------------------------------
; (ILOAD_X) Instruction - Push a local onto the stack
;                         covers ILOAD_{0, 1, 2, 3}

(defun execute-ILOAD_X (th s n)
  (let ((frame (thread-top-frame th s)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc frame))
            :stack (push-operand (nth-local n (locals frame))
                                 (stack frame)))))


; -----------------------------------------------------------------------------
; (INSTANCEOF reference-type) Instruction

;; Test whether one type implements (can be cast to, or is an instance of) another.
;; Kept disabled to prevent case splits, but there is an opener rule.
(defund type-implementsp (type-s type-t class-table)
  ;; todo:
  ;; (declare (xargs :guard (and (reference-typep type-s)
  ;;                             (reference-typep type-t)
  ;;                             (class-tablep class-table)
  ;;                             (implies (class-or-interface-namep type-s)
  ;;                                      (bound-in-class-tablep type-s class-table))
  ;;                             (implies (class-or-interface-namep type-t)
  ;;                                      (bound-in-class-tablep type-t class-table)))))
  (if (class-or-interface-namep type-s)
      (if (is-a-classp type-s class-table)
          ;; S is an ordinary (non-array) class:
          (if (or (is-a-classp type-t class-table)
                  (array-typep type-t))
              ;; T is a class type:
              (or (equal type-s type-t)
                  (acl2::bool-fix (member-equal type-t (get-superclasses type-s class-table))))
            ;; T is an interface type:
            (class-implements-interfacep type-s type-t class-table))
        ;; S is an interface type:
        (if (or (is-a-classp type-t class-table)
                (array-typep type-t))
            ;; T is a class type:
            (equal type-t "java.lang.Object")
          ;; T is an interface type:
          (or (equal type-t type-s)
              (acl2::bool-fix (member-equal type-t (get-superinterfaces (list type-s) class-table))))))
    ;; S is an array type:
    (let ((s-component-type (get-array-component-type type-s)))
      (if (class-or-interface-namep type-t)
          (if (is-a-classp type-t class-table)
              ;; T is a (non-array) class type:
              (equal type-t "java.lang.Object")
            ;; T is an interface type:
            (acl2::bool-fix (member-equal type-t '("java.lang.Object" "java.lang.Cloneable" "java.io.Serializable"))))
        ;; T is an array type:
        (let ((t-component-type (get-array-component-type type-t)))
          (or (and (primitive-typep s-component-type)
                   (equal s-component-type t-component-type))
              (and (reference-typep s-component-type)
                   (reference-typep t-component-type)
                   (type-implementsp s-component-type t-component-type class-table))))))))

(defthm type-implementsp-of-same
  (implies (reference-typep type)
           (type-implementsp type type class-table))
  :hints (("Goal" :expand (TYPE-IMPLEMENTSP (GET-ARRAY-COMPONENT-TYPE TYPE)
                                           (GET-ARRAY-COMPONENT-TYPE TYPE)
                                           CLASS-TABLE)
           :in-theory (e/d (type-implementsp reference-typep)
                           (primitive-typep
                            is-array-typep)))))

(defun execute-INSTANCEOF (inst th s)
  (let ((objectref (top-operand (stack (thread-top-frame th s)))))
    (if (null-refp objectref)
        ;; Push a result of 0:
        (modify th s
                :pc (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s)))
                :stack (push-operand 0 (pop-operand (stack (thread-top-frame th s)))))
      (let* ((class-table (class-table s))
             (type-t (farg1 inst)) ;resolution can't change the name?
             (erp (resolve-class type-t class-table)))
        (if erp
            (if (stringp erp)
                (obtain-and-throw-exception erp (list "ERROR IN INSTANCEOF: Failed to resolve class." :debug-info type-t) th s)
              (error-state erp s))
          (let* ((heap (heap s))
                 (type-s (acl2::get-class objectref heap)))
            (modify th s
                    :pc (+ 3 ;(inst-length inst)
                           (pc (thread-top-frame th s)))
                    :stack (push-operand (if (type-implementsp type-s type-t class-table)
                                             1
                                           0)
                                         (pop-operand (stack (thread-top-frame th s)))))))))))

;; (CHECKCAST reference-type)
(defun execute-CHECKCAST (inst th s)
  (let ((objectref (top-operand (stack (thread-top-frame th s)))))
    (if (null-refp objectref)
        ;; note that the operand stack does not change:
        (modify th s
                :pc (+ 3 ;(inst-length inst)
                       (pc (thread-top-frame th s))))
      (let* ((class-table (class-table s))
             (type-t (farg1 inst)) ;resolution can't change the name?
             (erp (resolve-class type-t class-table)))
        (if erp
            (if (stringp erp)
                (obtain-and-throw-exception erp (list "ERROR IN CHECKCAST: Failed to resolve class." :debug-info type-t) th s)
              (error-state erp s))
          (let* ((heap (heap s))
                 (type-s (acl2::get-class objectref heap)))
            (if (type-implementsp type-s type-t class-table)
                (modify th s
                        :pc (+ 3 ;(inst-length inst)
                               (pc (thread-top-frame th s)))
                        ;; note that the operand stack does not change
                        )
              (error-state
               (list "CHECKCAST exception (or unsupported case for CHECKCAST)"
                     type-s
                     type-t
                     ;;(array-classp type-s)
                     ;;(get-superclasses type-s class-table)
                     )
               s))))))))


; (:IREM)
;; (defund irem (n d)
;;   (int-fix (- n (* (truncate n d) d))))
;FIXME check that sbvrem computes value1 - (value1 / value2) * value2 as required
;FIXME check the special case of most negative int and -1
;FIXME prove the purported properties in the spec
(defun execute-IREM (th s)
  (let* ((value1 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (value2 (top-operand (stack (thread-top-frame th s)))) ;the divisor
         (result (acl2::sbvrem 32 value1 value2)))
    (if (eql 0 value2) ; todo: use =
        (obtain-and-throw-exception *ArithmeticException* (list :irem value1 value2) th s)
      (modify th s
              :pc (+ 1 ;(inst-length inst)
                     (pc (thread-top-frame th s)))
              :stack (push-operand result
                                   (pop-operand (pop-operand (stack (thread-top-frame th s)))))))))

; -----------------------------------------------------------------------------
; (ISHL) Instruction

(defun execute-ISHL (th s)
  (let* ((top-frame (thread-top-frame th s))
         (stack (stack top-frame))
         (value1 (top-operand (pop-operand stack)))
         (value2 (top-operand stack))
         (shift-amount (bvchop 5 value2))
         (result (bvshl 32 value1 shift-amount)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc top-frame))
            :stack (push-operand result
                         (pop-operand (pop-operand stack))))))

; -----------------------------------------------------------------------------
; (LSHL) Instruction

(defun execute-LSHL (th s)
  (let* ((top-frame (thread-top-frame th s))
         (stack (stack top-frame))
         ;;bozo these lets slow down the rewriting?
         (value2 (top-operand stack))
         (value1 (top-long (pop-operand stack)))
         (shift-amount (bvchop 6 value2))
         (result (bvshl 64 value1 shift-amount)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc top-frame))
            :stack (push-long result (pop-long (pop-operand stack))))))

; -----------------------------------------------------------------------------
; (ISHR) Instruction

(defun ishr32 (value1 value2)
  (declare (xargs :guard (and (unsigned-byte-p 32 value1)
                              (unsigned-byte-p 32 value2))))
  (bvashr 32 value1 (bvchop 5 value2)))

(defun execute-ISHR (th s)
  (let* ((value2 (top-operand (stack (thread-top-frame th s))))
         (value1 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (result (ishr32 value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand result
                         (pop-operand (pop-operand (stack (thread-top-frame th s))))))))

; -----------------------------------------------------------------------------
; (LSHR) Instruction

(defun ishr64 (value1 value2)
  (declare (xargs :guard (and (unsigned-byte-p 64 value1)
                              (unsigned-byte-p 64 value2))))
  (bvashr 64 value1 (bvchop 6 value2)))

(defun execute-LSHR (th s)
  (let* ((value2 (top-operand (stack (thread-top-frame th s))))
         (value1 (top-long (pop-operand (stack (thread-top-frame th s)))))
         (result (ishr64 value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-long result
                              ;; does M5 do 4 pops here (seems wrong)?
                              (pop-long (pop-operand (stack (thread-top-frame th s))))))))

; -----------------------------------------------------------------------------
; (IUSHR) Instruction

(defun execute-IUSHR (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (bvshr 32
                                  (top-operand (pop-operand (stack (thread-top-frame th s)))) ;; value1
                                  (bvchop 5
                                                 (top-operand (stack (thread-top-frame th s))) ;; value2
                                                 ))
                       (pop-operand (pop-operand (stack (thread-top-frame th s)))))))

; -----------------------------------------------------------------------------
; (LUSHR) Instruction

(defun execute-LUSHR (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long (bvshr 64
                                       (top-long (pop-operand (stack (thread-top-frame th s)))) ;; value1
                                       (bvchop 6
                                                      (top-operand (stack (thread-top-frame th s))) ;; value2
                                                      ))
                            (pop-long (pop-operand (stack (thread-top-frame th s)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (ISTORE localslotnum inst-len)  - store an int into the locals
(defund execute-ISTORE (inst th s)
  (let ((inst-len (farg2 inst)))
    (modify th s
            :pc (+ inst-len
                   (pc (thread-top-frame th s)))
            :locals (update-nth-local (farg1 inst)
                                      (top-operand (stack (thread-top-frame th s)))
                                      (locals (thread-top-frame th s)))
            :stack (pop-operand (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-istore
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :istore)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-ISTORE inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-ISTORE
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp
                            load-helper-1
                            load-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; -----------------------------------------------------------------------------
; (ISTORE_X) Instruction - store an int into the locals
;                          covers ISTORE_{0, 1, 2, 3}

(defun execute-ISTORE_X (th s n)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :locals (update-nth-local n
                                     (top-operand (stack (thread-top-frame th s)))
                                     (locals (thread-top-frame th s)))
          :stack (pop-operand (stack (thread-top-frame th s)))))


;; Subroutines and the ReturnAddress type:
;; Previously, the ReturnAddress was represented by a value of the form (list 'RETURNADDRESS <pc>).  Now it is just the integer <pc>.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (JSR signed-offset16)
(defund execute-JSR (inst th s)
  (let* ((offset (farg1 inst))
         (pc (pc (thread-top-frame th s)))
         ;; address of the next instruction:
         (return-address (+ 3 ;(inst-length inst)
                            pc)))
    (modify th s
            :pc (+ pc offset)
            :stack (push-operand return-address
                                 (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-jsr
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :jsr)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-JSR inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-JSR method-programp-key-property-2-alt valid-pcp)
                           (method-program current-inst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (JSR_W signed-offset32)
(defund execute-JSR_W (inst th s)
  (let* ((offset (farg1 inst))
         (pc (pc (thread-top-frame th s)))
         ;; address of the next instruction:
         (return-address (+ 5 ; because this is the wide version
                            pc)))
    (modify th s
            :pc (+ pc offset)
            :stack (push-operand return-address
                                 (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-jsr_w
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :jsr_w)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-JSR_W inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-JSR_W method-programp-key-property-2-alt valid-pcp)
                           (method-program current-inst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (RET localslotnum)
(defund execute-RET (inst th s)
;doesn't use the inst-len stored in the instruction...
  (let* ((localnum (farg1 inst))
         (return-address (nth-local localnum (locals (thread-top-frame th s)))))
    (if (not (pcp return-address))
        (error-state (list "Bad return address" return-address) s)
      (if (not (member return-address (strip-cars (current-program th s))))
          (error-state (list "Bad return address" return-address) s)
        (modify th s :pc return-address)))))

(defthm jvm-statep-of-execute-ret
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :ret)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-RET inst th s)))
  :hints (("Goal"
                  :in-theory (e/d (execute-RET
                                   ;;jvm-statep-def ; todo
                                   current-program ; todo
                                   )
                                  (method-program ; todo
                                   )))))

;FFFIXME add lots of checks for exceptions
;see http://java.sun.com/j2se/1.4.2/docs/api/java/lang/System.html#arraycopy(java.lang.Object,%20int,%20java.lang.Object,%20int,%20int)
(defun execute-java.lang.System.arraycopy (th s)
  (let* ((op-stack (stack (thread-top-frame th s)))
         (heap (heap s))
         (src (top-operand (popn-operands 4 op-stack)))
         (srcpos (top-operand (popn-operands 3 op-stack))) ;an int
         (dest (top-operand (popn-operands 2 op-stack)))
         (destpos (top-operand (pop-operand op-stack))) ;an int
         (length (top-operand op-stack)) ;an int, the number of elements copied
         )
    (if (null-refp dest)
        (prog2$ (cw "ERROR: Trying to call arraycopy with a NULL dest.")
                (obtain-and-throw-exception *NullPointerException* 'arraycopy th s))
      (if (null-refp src)
          (prog2$ (cw "ERROR: Trying to call arraycopy with a NULL src.")
                  (obtain-and-throw-exception *NullPointerException* 'arraycopy th s))
        ;;ffixme check that src and dest point to okay things.  Do these 5 checks:
        ;; The src argument refers to an object that is not an array.
        ;; The dest argument refers to an object that is not an array.
        ;; The src argument and dest argument refer to arrays whose component types are different primitive types.
        ;; The src argument refers to an array with a primitive component type and the dest argument refers to an array with a reference component type.
        ;; The src argument refers to an array with a reference component type and the dest argument refers to an array with a primitive component type.
        (if (or (acl2::sbvlt 32 srcpos 0)
                (acl2::sbvlt 32 destpos 0)
                (acl2::sbvlt 32 length 0))
            (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list 'arraycopy (decode-signed srcpos) (decode-signed destpos) (decode-signed length) src dest) th s) ;ffixme this should actually be an IndexOutOfBoundsException?  add that to the list of built-in classes?
          (let* ((src-contents (acl2::get-field src (acl2::array-contents-pair) heap))
                 (dest-contents (acl2::get-field dest (acl2::array-contents-pair) heap))
                 (src-length (len src-contents)) ;a usb31
                 (dest-length (len dest-contents))) ;a usb31
            ;; We use BVMINUS here to prevent overflow when adding
            ;; srcPos+length and destPos+length.  The difference is the number
            ;; of elements that can be safely copied.
            (if (or (acl2::sbvlt 32 (bvminus 32 src-length srcpos) length)
                    (acl2::sbvlt 32 (bvminus 32 dest-length destpos) length))
                (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list 'arraycopy src (decode-signed srcpos) dest (decode-signed destpos) (decode-signed length)) th s) ;ffixme this should actually be an IndexOutOfBoundsException?  add that to the list of built-in classes?
              ;;fixme more checks here
              (modify th s
                      :pc (+ 3 ;the length of the invokestatic instruction
                             (pc (thread-top-frame th s)))
                      :stack (popn-operands 5 (stack (thread-top-frame th s)))
                      :heap (acl2::set-field (addressfix dest)
                                             (acl2::array-contents-pair)
                                             ;;i saw a case where it was tricky to recover the length of this:
                                             ;;also, what do we know about the return type?
                                             (acl2::update-subrange2 dest-length
                                                                     (decode-signed-non-neg destpos)
                                                                     ;;use bvplus 32 here?
                                                                     (+ (decode-signed-non-neg destpos) (decode-signed-non-neg length) -1)
                                                                     ;;TODO: Do the math using ACL2 integers and prove equivalent:
                                                                     ;try:(decode-signed (bvplus 32 destpos (bvplus 32 length -1))) ;todo: fix the -1
                                                                     (acl2::subrange (decode-signed-non-neg srcpos)
                                                                                     ;;use bvplus31?
                                                                                     (+ (decode-signed-non-neg srcpos) (decode-signed-non-neg length) -1)
                                                                                     ;;TODO: Do the math using ACL2 integers and prove equivalent:
                                                                                     ;;try: (bvplus 32 srcpos (bvplus 32 length -1)) ;todo: fix the -1
                                                                                     src-contents)
                                                                     dest-contents)
                                             heap)))))))))

(defund is-java.lang.System.arraycopy (obj-class-name method-name descriptor)
  (declare (xargs :guard t))
  (and (equal obj-class-name "java.lang.System")
       (equal method-name "arraycopy")
       (equal descriptor
;           ((:REFERENCE "java.lang.Object") acl2::INT (:REFERENCE "java.lang.Object") acl2::INT acl2::INT)
;now we need a descriptor:
              "(Ljava/lang/Object;ILjava/lang/Object;II)V"
              )))

;; Our model of the native method java.lang.Float.floatToRawIntBits
;; The current instruction in S is the invoke
(defund execute-java.lang.Float.floatToRawIntBits (th s)
  (let* ((s (move-past-invoke-instruction th s))) ;; Move past the invokestatic instruction
    (modify th s
            :stack (push-operand (acl2::float-to-bits (top-operand (stack (thread-top-frame th s))))
                                 (pop-operand (stack (thread-top-frame th s)))))))

(defund is-java.lang.Float.floatToRawIntBits (obj-class-name method-name descriptor)
  (declare (xargs :guard t))
  (and (equal obj-class-name "java.lang.Float")
       (equal method-name "floatToRawIntBits")
       (equal descriptor "(F)I")))

;; Our model of the native method java.lang.Float.intBitsToFloat
;; The current instruction in S is the invoke
(defund execute-java.lang.Float.intBitsToFloat (th s)
  (let* ((s (move-past-invoke-instruction th s))) ;; Move past the invokestatic instruction
    (modify th s
            :stack (push-operand (acl2::parse-float (top-operand (stack (thread-top-frame th s))))
                                 (pop-operand (stack (thread-top-frame th s)))))))

(defund is-java.lang.Float.intBitsToFloat (obj-class-name method-name descriptor)
  (declare (xargs :guard t))
  (and (equal obj-class-name "java.lang.Float")
       (equal method-name "intBitsToFloat")
       (equal descriptor "(I)F")))

;;the method is static
;; the signature is "(Ljava/lang/String;)Ljava/lang/Class;"
;; TODO: If the class object needs to be built, this doesn't finish the execution; it just pushes the frame.
(defund execute-java.lang.Class.getPrimitiveClass (th s)
  (declare (xargs :guard (and (jvm-statep s))
                  :verify-guards nil))
  (let* ((op-stack (stack (thread-top-frame th s)))
         (string-ref (top-operand op-stack))
         (heap (heap s))
         ;; The String object has a backing array called value (this assumes that String is defined that way!):
         (char-array-ref (acl2::get-field string-ref (cons "java.lang.String" (make-field-id "value" '(:array :char))) heap))
         ;; Get the characters
         (java-chars (acl2::array-contents char-array-ref heap))
         (string (char-list-to-string java-chars)) ;this will be something like "int" ; todo: call java-chars-to-string here
         (heapref-table (heapref-table s))
         (class-object (get-class-object string heapref-table))) ;todo: think "int" here vs "java.lang.Integer".  can also be void...
    (if (not class-object) ;test whether the class object needs to be built
        (push-frame-to-build-class-object string th s)
      ;; The class object already exists...
      (let* ((s (move-past-invoke-instruction th s))) ;; Move past the invokestatic instruction:
        (modify th s :stack (push-operand class-object (pop-operand op-stack)))))))

(defthm jvm-statep-of-execute-java.lang.class.getPrimitiveClass
  (implies (and (jvm-statep s)
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th)
                (not (empty-call-stackp (binding th (thread-table s))))
                (member-equal (instruction-opcode (current-inst th s)) '(:invokevirtual :invokestatic :invokespecial :invokeinterface)))
           (jvm-statep (execute-java.lang.class.getPrimitiveClass th s)))
  :hints (("Goal" :in-theory (e/d (execute-java.lang.class.getPrimitiveClass
                                   class-namep ;fixme breaks the abstraction
                                   move-past-invoke-instruction)
                                  (acons)))))

;; Our model of the native method java.lang.Object.getClass
;; The current instruction in S is the invoke
;; TODO: If the class object needs to be built, this doesn't finish the execution; it just pushes the frame.
(defund execute-java.lang.Object.getClass (th s)
  (let* ((op-stack (stack (thread-top-frame th s)))
         (this (top-operand op-stack))
         (heap (heap s))
         ;; Get the class of the object on which this method is invoked...
         (class-name (acl2::get-class this heap)))
    (if (not (class-namep class-name)) ;todo drop this check if it is implied by jvm-statep
        (error-state (list "Invalid class name when calling getClass" class-name) s)
      (let* ((heapref-table (heapref-table s))
             ;; and return the corresponding Class object:
             (class-object (get-class-object class-name heapref-table)))
        (if (not class-object) ;test whether the class object needs to be built
            (push-frame-to-build-class-object class-name th s)
          ;; The class object already exists...
          (let* ((s (move-past-invoke-instruction th s))) ;; Move past the invokevirtual instruction
            (modify th s :stack (push-operand class-object (pop-operand op-stack)))))))))

(defthm jvm-statep-of-execute-java.lang.object.getclass
  (implies (and (jvm-statep s)
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th)
                (not (empty-call-stackp (binding th (thread-table s))))
                (member-equal (instruction-opcode (current-inst th s)) '(:invokevirtual :invokestatic :invokespecial :invokeinterface)))
           (jvm-statep (execute-java.lang.object.getclass th s)))
  :hints (("Goal" :in-theory (e/d (execute-java.lang.object.getclass move-past-invoke-instruction) (acons)))))

(defund is-java.lang.Object.getClass (obj-class-name method-name descriptor)
  (declare (xargs :guard t))
  (and (equal obj-class-name "java.lang.Object")
       (equal method-name "getClass")
       (equal descriptor "()Ljava/lang/Class;")))

;s is at the invokestatic instruction
(defun execute-model-static-boolean-method (formal-slot-count return-value th s)
  (declare (xargs :guard (jvm-statep s)
                  :verify-guards nil))
  (let* ((op-stack (stack (thread-top-frame th s)))
         ;; Pop off the operands to the method being modeled and push on the given return-value:
         ;; todo call pop-items-off-stack here:
         (s (modify th s :stack (push-operand return-value (popn-operands formal-slot-count op-stack))))
         ;; Move past the invokestatic instruction:
         (s (move-past-invoke-instruction th s)))
    s))

(defun map-make-method-designator (triples)
  (if (endp triples)
      nil
    (let ((triple (first triples)))
      (cons (make-method-designator (first triple)
                                    (second triple)
                                    (third triple))
            (map-make-method-designator (rest triples))))))

;; todo: do we actually record these?
(defconst *native-api-methods-to-record-and-skip*
  (map-make-method-designator
   '(("java.lang.Object" "registerNatives" "()V")
     ("java.lang.Class" "registerNatives" "()V"))))

(defun lookup-method-in-class-table (method-designator class-table)
  (declare (xargs :guard (and (method-designatorp method-designator)
                              (class-tablep class-table))
                  :guard-hints (("Goal" :in-theory (enable class-tablep class-tablep0 method-designatorp)))))
  (let* ((class-name (first method-designator))
         (method-name (second method-designator))
         (method-descriptor (third method-designator)))
    (if (not (bound-in-class-tablep class-name class-table)) ;ttodo: think about this case
        nil
      (let ((class-info (get-class-info class-name class-table)))
        (and class-info ;drop?
             (let* ((methods (class-decl-methods class-info)))
               (and methods
                    (let ((possible-method-info (lookup-equal (cons method-name method-descriptor) methods)))
                      possible-method-info))))))))

(defun unknown-stack-value-defattach ()
  (declare (xargs :guard t))
  :unknown-stack-value)

;TODO: would be better to have this take a counter or state, so that we can't prove that different unknown values are equal:
(defstub unknown-stack-value () => *)
;making the executable:
;(defun unknown-stack-value () :unknown-stack-value) ;fixme think about this..

;(defattach unknown-stack-value unknown-stack-value-defattach) ;to support execution


;TODO: What if a class needs to be initialized?
;TTODO: handle the other invokes this way as well
;pass in the method-designator?
(defund skip-invokestatic-instruction (class-name method-name descriptor formal-slot-count th s)
  ;; Skip past a call to invokestatic, because the called method doesn't do anything important
  (let* (;(class-name (farg1 inst)) ;the actual method may come from a superclass ; fixme - So why is this even in the class file?
         ;(method-name (farg2 inst))
         ;(descriptor (farg3 inst))
         ;(formal-slot-count (count-slots-in-types (farg4 inst)))
         (class-table (class-table s))
         (method-info (lookup-method-in-class-table (make-method-designator class-name method-name descriptor) class-table)) ;todo inefficient to make and then break up the method designator
         (return-type (lookup-eq :return-type method-info))
         ;;move past the invoke instruction and pop off the operands
         (s (modify th s
                         :pc (+ 3 ;(inst-length inst)
                                (pc (thread-top-frame th s)))
                         ;; todo: call pop-items-off-stack here:
                         :stack (popn-operands formal-slot-count
                                               (stack (thread-top-frame th s)))))
         (stack (stack (thread-top-frame th s)))
         ;; maybe push on an unknown return value:
         (s (modify th s
                         :stack (if (eq :void return-type)
                                    stack
                                  (if (or (member-eq return-type *one-slot-types*)
                                          (class-namep return-type)
                                          (eq :array (car return-type)))
                                      (push-operand (unknown-stack-value) stack)
                                    (if (member-eq return-type *two-slot-types*)
                                        (push-long (unknown-stack-value) stack)
                                      (er hard 'skip-invokestatic-instruction "Unknown return type: ~x0." return-type)))))))
    s))

;delete:
;longs and doubles count as two
;; ;bozo see count-slots-in-params which i guess does more error checking
;; (defun count-slots-in-signature (signature)
;;   (declare (xargs :guard (true-listp signature)))
;;   (if (endp signature)
;;       0
;;     (let ((item (car signature)))
;;       (if (member-equal item '(acl2::long acl2::double)) ;FFIXME am i right about double? FFIXME switch to keywords for the field types
;;           (+ 2 (count-slots-in-signature (cdr signature)))
;;         (+ 1 (count-slots-in-signature (cdr signature)))))))

;; Returns a method-info/class-name pair, or nil.
(defun lookup-method-in-class-info (method-id class-name class-info)
  (declare (xargs :guard (and (method-idp method-id)
                              (class-namep class-name)
                              (class-infop class-info class-name))))
  (let* ((methods (class-decl-methods class-info))
         (possible-method-info (lookup-equal method-id methods)))
    (if possible-method-info
        (cons possible-method-info class-name)
      nil)))

(defthm method-infop-of-car-of-lookup-method-in-class-info
  (implies (and (lookup-method-in-class-info method-id class-name class-info)
                ;; (method-idp method-id)
                (class-namep class-name)
                (class-infop class-info class-name))
           (method-infop (car (lookup-method-in-class-info method-id class-name class-info))))
  :hints (("Goal" :in-theory (enable lookup-method-in-class-info))))

(defthm class-namep-of-cdr-of-lookup-method-in-class-info
  (implies (and (lookup-method-in-class-info method-id class-name class-info)
                ;; (method-idp method-id)
                (class-namep class-name)
                (class-infop class-info class-name))
           (class-namep (cdr (lookup-method-in-class-info method-id class-name class-info))))
  :hints (("Goal" :in-theory (enable lookup-method-in-class-info))))

;returns a method-info/class-name pair, or nil
(defund lookup-method-in-classes (method-id class-names class-table)
  (declare (xargs :guard (and (method-idp method-id)
                              (true-listp class-names)
                              (class-name-listp class-names)
                              (class-tablep class-table)
                              (all-bound-in-class-tablep class-names class-table))))
  (if (endp class-names)
      nil
    (or (lookup-method-in-class-info method-id
                                     (first class-names)
                                     (get-class-info (first class-names) class-table))
        (lookup-method-in-classes method-id (rest class-names) class-table))))

(defthm method-infop-of-car-of-lookup-method-in-classes
  (implies (and (lookup-method-in-classes method-id class-names class-table)
                ;; (method-idp method-id)
                ;; (class-name-listp class-names)
                (class-tablep class-table)
                (all-bound-in-class-tablep class-names class-table))
           (method-infop (car (lookup-method-in-classes method-id class-names class-table))))
  :hints (("Goal" :in-theory (enable lookup-method-in-classes))))

(defthm class-namep-of-cdr-of-lookup-method-in-classes
  (implies (and (lookup-method-in-classes method-id class-names class-table)
                ;; (method-idp method-id)
                ;; (class-name-listp class-names)
                (class-tablep class-table)
                (all-bound-in-class-tablep class-names class-table))
           (class-namep (cdr (lookup-method-in-classes method-id class-names class-table))))
  :hints (("Goal" :in-theory (enable lookup-method-in-classes))))

;; This is (or should be, once we fix it) the "Method Resolution" described in the JVM spec:
;returns a method-info/class-name pair, or nil
;;the match (method name and descriptor) must be exact.
;;we are just checking for overridden/inherited methods
;;the compiler seems to do the heavy lifting of sorting out overloaded methods
;TTODO: Propagate this error to the caller.
;TODO: maybe us MBE to suppress the message during proofs (or disable (:executable-counterpart cw)
;; TTODO: What if class-name is a (parsed) array class name?
(defund lookup-method (class-name method-name descriptor class-table)
  (declare (xargs :guard (and (class-namep class-name)
                              (class-tablep class-table)
                              (method-namep method-name)
                              (method-descriptorp descriptor)
                              (bound-in-class-tablep class-name class-table)
                              (not (is-an-interfacep class-name class-table)))))
  (let ((method-or-nil (lookup-method-in-classes (cons method-name descriptor)
                                                 ;;we search the given class and then its superclasses (fixme what about interfaces?)
                                                 (cons class-name (get-superclasses class-name class-table))
                                                 class-table)))
    (if method-or-nil
        method-or-nil
      (prog2$ (cw "ERROR: Failed to look up method ~s0.~s1~%" class-name method-name)
              nil))))

(defthm method-infop-of-car-of-lookup-method
  (implies (and (lookup-method class-name method-name descriptor class-table)
                (class-namep class-name)
                (class-tablep class-table)
                ;; (method-namep method-name)
                (method-descriptorp descriptor)
                (bound-in-class-tablep class-name class-table)
                ;; (not (is-an-interfacep class-name class-table))
                )
           (method-infop (car (lookup-method class-name method-name descriptor class-table))))
  :hints (("Goal" :in-theory (enable lookup-method))))

(defthm class-namep-of-cdr-of-lookup-method
  (implies (and (lookup-method class-name method-name descriptor class-table)
                (class-namep class-name)
                (class-tablep class-table)
                ;; (method-namep method-name)
                (method-descriptorp descriptor)
                (bound-in-class-tablep class-name class-table)
                ;; (not (is-an-interfacep class-name class-table))
                )
           (class-namep (cdr (lookup-method class-name method-name descriptor class-table))))
  :hints (("Goal" :in-theory (enable lookup-method))))

;; TODO: Update this.
;; Returns (mv erp closest-method-info class-name) where ERP is either nil (no
;; error), a string (the name of an exception to throw), or a cons (an
;; indication of an error).  If ERP is non-nil, the other return values
;; are meaningless.
(defund lookup-method-for-invokespecial-aux (class-name
                                             method-name
                                             method-descriptor
                                             class-table
                                             count ;for termination
                                             )
  (declare (xargs :measure (nfix (+ 1 count))
                  :guard (and (class-tablep class-table)
                              (class-namep class-name)
                              (bound-in-class-tablep class-name class-table)
                              (not (is-an-interfacep class-name class-table))))
           (type (integer 0 *) count))
  (if (zp count) ;to ensure termination
      ;;(error-looking-up-method-for-invokespecial class-name method-name method-descriptor class-table)
      (mv (list "ERROR in INVOKESPECIAL.  Lookup ran out of classes." :debug-info class-name) ;error
          nil nil)
    (if (not (mbt (bound-in-class-tablep class-name class-table))) ;todo avoid this check?
        (mv (list "ERROR in INVOKESPECIAL.  Class not found." :debug-info class-name) ;error
            nil nil)
      (let* ((c-class-info (get-class-info class-name class-table)) ;fixme use something more specific than g, something that requires the class to be bound in the class-table
             (c-methods (class-decl-methods c-class-info))
             (possible-method-info (lookup-equal (cons method-name method-descriptor) c-methods)))
        (if possible-method-info
            (mv nil ;no error
                possible-method-info
                class-name)
          (let ((c-superclass (get-superclass class-name class-table)))
            (if (eq :none c-superclass)
                (mv (list "ERROR in INVOKESPECIAL.  Class has no super class." :debug-info class-name) ;error
                    nil nil)
              ;;(error-looking-up-method-for-invokespecial class-name method-name method-descriptor class-table)
              ;;todo: should be an AbstractMethodError
              (lookup-method-for-invokespecial-aux c-superclass
                                                   method-name
                                                   method-descriptor
                                                   class-table
                                                   (+ -1 count)))))))))

(defthm method-infop-of-mv-nth-1-of-lookup-method-for-invokespecial-aux
  (implies (and (class-tablep class-table)
                ;; no error:
                (not (mv-nth 0 (lookup-method-for-invokespecial-aux class-name
                                                                 method-name
                                                                 method-descriptor
                                                                 class-table
                                                                 count))))
           (method-infop (mv-nth 1 (lookup-method-for-invokespecial-aux class-name
                                                                     method-name
                                                                     method-descriptor
                                                                     class-table
                                                                     count))))
  :hints (("Goal" :in-theory (enable lookup-method-for-invokespecial-aux))))

(defthm class-namep-of-mv-nth-2-of-lookup-method-for-invokespecial-aux
  (implies (and (class-tablep class-table)
                (class-namep class-name)
                (bound-in-class-tablep class-name class-table)
                ;; no error:
                (not (mv-nth 0 (lookup-method-for-invokespecial-aux class-name method-name method-descriptor class-table count))))
           (class-namep (mv-nth 2 (lookup-method-for-invokespecial-aux class-name method-name method-descriptor class-table count))))
  :hints (("Goal" :in-theory (enable lookup-method-for-invokespecial-aux))))

(defthm bound-in-class-tablep-of-mv-nth-2-of-lookup-method-for-invokespecial-aux
  (implies (and (not (mv-nth 0 (lookup-method-for-invokespecial-aux class-name method-name method-descriptor class-table count)))
                (class-tablep class-table)
                (class-namep class-name)
                (bound-in-class-tablep class-name class-table))
           (bound-in-class-tablep (mv-nth 2 (lookup-method-for-invokespecial-aux class-name method-name method-descriptor class-table count))
                                  class-table))
  :hints (("Goal" :in-theory (enable lookup-method-for-invokespecial-aux class-tablep))))

(defthm bound-to-a-non-interfacep-of-mv-nth-2-of-lookup-method-for-invokespecial-aux
  (implies (and (not (mv-nth 0 (lookup-method-for-invokespecial-aux class-name method-name method-descriptor class-table count)))
                (class-tablep class-table)
                (class-namep class-name)
                (bound-in-class-tablep class-name class-table)
                (bound-to-a-non-interfacep class-name class-table))
           (bound-to-a-non-interfacep (mv-nth 2 (lookup-method-for-invokespecial-aux class-name method-name method-descriptor class-table count))
                                      class-table))
  :hints (("Goal" :in-theory (e/d (lookup-method-for-invokespecial-aux) (true-listp)))))

(defconst *dummy-class-name* "DUMMY-CLASS") ;todo: eventually use a keyword, but then this can't appear in a method-designator

;inst is an invokespecial instruction.
;; Returns (mv erp closest-method-info class-name) where ERP is either nil (no
;; error), a string (the name of an exception to throw), or a cons (an
;; indication of an error).  If ERP is non-nil, the other return values
;; are meaningless.
(defund lookup-method-for-invokespecial (inst th s)
  (let ((class-name (farg1 inst))
        (method-name (farg2 inst))
        (descriptor (farg3 inst))
        (interfacep (farg5 inst))
        (class-table (class-table s)))
    (mv-let (erp class-name-of-resolved-method)
      (resolve-method method-name descriptor class-name interfacep class-table)
      (declare (ignore class-name-of-resolved-method)) ;todo
      (if erp
          (mv erp nil nil)
        (let* ((frame (thread-top-frame th s))
               (current-class-name (cur-class-name frame)))
          (if (and (not (equal current-class-name *dummy-class-name*))
                   (not (bound-in-class-tablep current-class-name class-table)))
              (mv (list :unbound-class current-class-name) nil nil)
            (let ((c (if (and (not (equal current-class-name *dummy-class-name*))
                              (not (equal "<init>" method-name)) ;todo: more checks! see the docs
                              (bound-to-a-non-interfacep class-name class-table)
                              (superclassp class-name current-class-name class-table)
                              (member-eq :acc_super (class-decl-access-flags (get-class-info current-class-name class-table))) ;; assuming "the class file" refers to the current class
                              )
                         (get-superclass current-class-name class-table) ; current-class-name can't be java.lang.Object because above we check that class-name is its superclass
                       class-name)))
              ;;fixme - do we do the right thing here?
              (lookup-method-for-invokespecial-aux c
                                                   method-name descriptor class-table
                                                   (+ 1 (len (get-superclasses c class-table))) ;sufficient to ensure we handle all the super classes.
                                                   ))))))))

(defthm method-infop-of-mv-nth-1-of-lookup-method-for-invokespecial
  (implies (and (jvm-statep s)
                ;; no error:
                (not (mv-nth 0 (lookup-method-for-invokespecial inst th s))))
           (method-infop (mv-nth 1 (lookup-method-for-invokespecial inst th s))))
  :hints (("Goal" :in-theory (enable lookup-method-for-invokespecial))))

(defthm class-namep-of-mv-nth-2-of-lookup-method-for-invokespecial
  (implies (and (jvm-statep s)
                ;; no error:
                (not (mv-nth 0 (lookup-method-for-invokespecial inst th s))))
           (class-namep (mv-nth 2 (lookup-method-for-invokespecial inst th s))))
  :hints (("Goal" :cases ((equal '"java.lang.Object"
                                 (cur-class-name (top-frame (binding th (thread-table s))))))
           :in-theory (enable lookup-method-for-invokespecial))))

;; If an exception class is returned, it is bound.
(defthm bound-in-class-tablep-of-mv-nth-2-of-lookup-method-for-invokespecial
  (implies (and (jvm-statep s)
                ;; no error:
                (not (mv-nth 0 (lookup-method-for-invokespecial inst th s))))
           (bound-in-class-tablep (mv-nth 2 (lookup-method-for-invokespecial inst th s)) (class-table s)))
  :hints (("Goal" :cases ((equal '"java.lang.Object"
                                 (cur-class-name (top-frame (binding th (thread-table s))))))
           :in-theory (enable lookup-method-for-invokespecial))))

;; ;; If an exception class is returned (can't currently happen), it is bound.
;; (defthm bound-in-class-tablep-of-mv-nth-0-of-lookup-method-for-invokespecial
;;   (implies (and (class-namep (mv-nth 0 (lookup-method-for-invokespecial inst th s)))
;;                 (jvm-statep s))
;;            (bound-in-class-tablep (mv-nth 0 (lookup-method-for-invokespecial inst th s))
;;                                   (class-table s)))
;;   :hints (("Goal" :in-theory (enable lookup-method-for-invokespecial))))

;; ;; If an exception class is returned (can't currently happen), it is bound to a class.
;; (defthm bound-to-a-non-interfacep-of-mv-nth-0-of-lookup-method-for-invokespecial
;;   (implies (and (class-namep (mv-nth 0 (lookup-method-for-invokespecial inst th s)))
;;                 (jvm-statep s)
;;                 )
;;            (bound-to-a-non-interfacep (mv-nth 0 (lookup-method-for-invokespecial inst th s))
;;                                       (class-table s)))
;;   :hints (("Goal" :in-theory (e/d (lookup-method-for-invokespecial) (bound-to-a-non-interfacep)))))

; (:INVOKESPECIAL <class-name> <method-name> <method-descriptor> <param-types> <interfacep>)
;; This should remain closed unless we can resolve the method
(defund execute-invokespecial-helper (closest-method-info actual-class-name s th inst)
  (let* ((class-name (farg1 inst)) ;this is what the spec calls the resolved class name?
         (method-name (farg2 inst)) ;this is what the spec calls the resolved method name?
         (descriptor (farg3 inst))
         (parameter-types (farg4 inst))
         ;; (interfacep (farg5 inst))
         (frame (thread-top-frame th s))
         (stack (stack frame))
         (stack-without-params (pop-items-off-stack parameter-types stack))
         (objectref (top-operand stack-without-params))
         ;;fixme - do we do the right thing here?
         ;;(prog (method-program closest-method-info))
         (s1 (modify th s
                     ;; we now do this in the return:
                     ;; :pc (+ 3 ;(inst-length inst)
                     ;;        (pc (thread-top-frame th s)))
                     :stack (pop-operand stack-without-params)))
;(tThread (rrefToThread objectref (thread-table s)))
         )
    (cond
      ((not (acl2::addressp objectref))
       (error-state (list "INVOKESPECIAL with non-reference" objectref) s))
     ((method-nativep closest-method-info)
      (cond ;((equal method-name "start") (modify tThread s1 :status :SCHEDULED)) ;fixme put these back?
;((equal method-name "stop") (modify tThread s1 :status :UNSCHEDULED))
       (t (error-state (list "INVOKESPECIAL is trying to execute an unsupported native method" class-name (cons method-name descriptor)) s)
          ;;s
          )))
     ((method-synchronizedp closest-method-info)
      (mv-let (successp new-monitor-table)
        (attempt-to-enter-monitor th (addressfix objectref) (monitor-table s))
        (if successp
            (modify th s1
                    :call-stack
                    (push-frame (make-frame 0
                                            (initialize-locals (cons actual-class-name parameter-types)
                                                               stack)
                                            (empty-operand-stack)
                                            objectref
                                            closest-method-info
                                            (make-method-designator actual-class-name ;(farg1 inst)
                                                                    method-name descriptor))
                                (call-stack th s1))
                    :monitor-table new-monitor-table)
          ;; failed to enter monitor, so the thread blocks:
          (failed-to-enter-monitor-wrapper s closest-method-info) ;(error-state "method-sync but object not lockable" s)
          )))
     (t
      (modify th s1
              :call-stack
              (push-frame (make-frame 0
                                      (initialize-locals (cons actual-class-name parameter-types)
                                                         stack)
                                      (empty-operand-stack)
                                      (no-locked-object)
                                      closest-method-info
                                      (make-method-designator actual-class-name ;(farg1 inst)
                                                              method-name descriptor))
                          (call-stack th s1)))))))

;FIXME make sure this is right
;FFFIXME does this set the current class in the make-frame right?
(defund execute-INVOKESPECIAL (inst th s)
  (mv-let
      (erp closest-method-info actual-class-name)
      (lookup-method-for-invokespecial inst th s)
    (if erp
        (if (and (class-namep erp)
                 (bound-to-a-non-interfacep erp (class-table s)) ; todo: what if not?
                 )
            (obtain-and-throw-exception erp (list "ERROR IN INVOKESPECIAL: Failed to resolve method." :debug-info inst) th s)
          (error-state erp s))
      (if (method-abstractp closest-method-info) ; todo: prove this can't happen
          (error-state `(:invokespecial-abstract-method ,closest-method-info) s)
        (execute-invokespecial-helper closest-method-info actual-class-name s th inst)))))

(defthm memberp-of-pc-and-strip-cars-of-method-program-of-method-info
  (implies (framep frame) ; move
           (memberp (pc frame)
                    (strip-cars (method-program (method-info frame)))))
  :hints (("Goal" :in-theory (enable framep pc method-info))))

(defthm jvm-statep-of-execute-invokespecial
  (implies (and (jvm-statep s)
                (call-stack-non-emptyp th s)
                (equal (instruction-opcode inst) :invokespecial)
                (instructionp inst)
                (jvm-instruction-okayp inst (pc (thread-top-frame th s)) (strip-cars (method-program (method-info (thread-top-frame th s)))))
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th))
           (jvm-statep (execute-invokespecial inst th s)))
  :hints (("Goal" :in-theory (enable execute-invokespecial
                                     execute-invokespecial-helper ; todo: disable less stuff here
                                     obtain-and-throw-exception
                                     failed-to-enter-monitor-wrapper
                                     jvm-instruction-okayp
                                     instructionp-redef
                                     instruction-args
                                     instruction-argsp))))


; (:INVOKESTATIC class-name method-name method-descriptor formal-slot-count)

;; We'll keep this from opening if we can't resolve the class
(defund execute-INVOKESTATIC-helper (;CLASS-NAME
                                     parameter-types
                                     FORMAL-SLOT-COUNT S TH DESCRIPTOR METHOD-NAME ACTUAL-CLASS-NAME METHOD-INFO)
  (if (method-nativep method-info)
      (let ((method-designator (make-method-designator actual-class-name method-name descriptor)))
        (cond
         ;;which class-name to use here? ;should we do this before we look up the method?
         ;;checks for the native method java.lang.System.arraycopy
         ((is-java.lang.System.arraycopy actual-class-name method-name descriptor)
          (execute-java.lang.System.arraycopy th s))
         ((is-java.lang.Object.getClass actual-class-name method-name descriptor)
          (execute-java.lang.Object.getClass th s))
         ((is-java.lang.Float.floatToRawIntBits actual-class-name method-name descriptor)
          (execute-java.lang.Float.floatToRawIntBits th s))
         ((is-java.lang.Float.intBitsToFloat actual-class-name method-name descriptor)
          (execute-java.lang.Float.intBitsToFloat th s))

         ;; TODO: What if some of these native methods are synchronized?
         ((equal (list actual-class-name method-name descriptor)
                 '("java.lang.Class" "desiredAssertionStatus0" "(Ljava/lang/Class;)Z"))
          (execute-model-static-boolean-method FORMAL-SLOT-COUNT (false) th s))
         ((equal (list actual-class-name method-name descriptor)
                 '("java.lang.Class" "getPrimitiveClass" "(Ljava/lang/String;)Ljava/lang/Class;"))
          (execute-java.lang.Class.getPrimitiveClass th s))

         ((member-equal method-designator *native-api-methods-to-record-and-skip*)
          (prog2$ (cw "Note: Skipping unsupported native method: ~x0.~%" method-designator)
                  ;; this recomputes formal-slot-count, etc.?
                  (skip-invokestatic-instruction actual-class-name method-name descriptor formal-slot-count th s)))
         (t (prog2$ (cw "ERROR: INVOKESTATIC is trying to execute unsupported native method ~s0.~s1 in method ~s2.~s3.~%"
                        actual-class-name method-name (cur-class-name (thread-top-frame th s)) (cur-method-name (thread-top-frame th s)))
                    (error-state (list :unsupported-native-method actual-class-name method-name descriptor) s)))))
    (let* (;(prog (method-program method-info))
           ;;fixme s1 is not used in all branches below
           (s1 (modify th s
                       ;; we now do this in the return:
                       ;; :pc (+ 3 ;(inst-length inst)
                       ;;        (pc (thread-top-frame th s)))
                       :stack (pop-items-off-stack parameter-types (stack (thread-top-frame th s))))))

      (cond
       ((not method-info) ;ffixme check for empty program?
        (error-state (concatenate 'string "ERROR: Could not find info for method: " method-name) s))

       ;; We are invoking a synchronized static method, so we
       ;; attempt to enter the monitor of the Class object
       ;; corresponding to the class of this method:
       ((method-synchronizedp method-info)
        (if (not (class-namep actual-class-name))
            (error-state (list "Bad class name in invokestatic." actual-class-name) s) ;todo: can we drop this?
          (let ((class-object (get-class-object actual-class-name (heapref-table s)))) ;ffixme what if it's not there? add an invariant that it's always there (if we've initialized the class?)
            (if (not class-object)
                (push-frame-to-build-class-object actual-class-name th s)
              ;; (prog2$ (cw "ERROR: No match found for class ~s0 in heapref-table." actual-class-name)
              ;;           (error-state (list :no-match-in-heapref-table) s))
              (mv-let (successp new-monitor-table)
                (attempt-to-enter-monitor th (addressfix class-object) (monitor-table s))
                (if successp
                    (modify th s1
                            :call-stack
                            (push-frame (make-frame 0
                                                    (initialize-locals parameter-types (stack (thread-top-frame th s)))
                                                    (empty-operand-stack)
                                                    class-object
                                                    method-info
                                                    (make-method-designator actual-class-name method-name descriptor))
                                        (call-stack th s1))
                            :monitor-table new-monitor-table)
                  ;; failed to enter monitor, so the thread blocks: fixme: print a message?
                  (failed-to-enter-monitor-wrapper s method-info) ;(error-state "method-sync but object not lockable" s)
                  ))))))

       ;;combine this and the sync case just above (but note the difference in the locked object).
       (t
        (modify th s1
                :call-stack
                (push-frame (make-frame 0
                                        (initialize-locals parameter-types (stack (thread-top-frame th s)))
                                        (empty-operand-stack)
                                        (no-locked-object)
                                        method-info
                                        (make-method-designator actual-class-name method-name descriptor))
                            (call-stack th s1))))))))

;FFFIXME: See AC's notes on this (and other instructions)!!
;FFFIXME does this set the current class in the make-frame right?
;FIXME i've seen this invoke native methods (e.g., in |*java.lang.Integer.<clinit>-()V-CODE*|)
(defun execute-INVOKESTATIC (inst th s)
  (let ((class-name (farg1 inst))
        (method-name (farg2 inst))
        (descriptor (farg3 inst))
        (parameter-types (farg4 inst))
        (interfacep (farg5 inst))
        (class-table (class-table s)))
    (mv-let (erp class-name-of-resolved-method)
        (resolve-method method-name descriptor class-name interfacep class-table)
      (declare (ignore class-name-of-resolved-method)) ;todo
      (if erp
          (if (stringp erp)
              (obtain-and-throw-exception erp (list "ERROR IN INVOKESTATIC: Failed to resolve method." :debug-info class-name) th s)
            (error-state erp s))
        (let (;;FIXME check this procedure.  this is different from the "resolution", for which we do nothing, in invokevirtual
              ;;i guess this could be done at link time
              (closest-method-and-class-name (lookup-method class-name method-name descriptor (class-table s)))
              )
          (if (not (bound-in-class-tablep class-name (class-table s))) ;todo: is this implied by the test below (if so, drop this check)
              (error-state (list 'class-not-in-class-table class-name 'execute-INVOKESTATIC) s) ;todo: unify this checks with the other checks done elsewhere before field resolution
            (if (not closest-method-and-class-name) ;TODO: Really more different errors can be thrown during Method Resolution
                (error-state (list "ERROR IN INVOKESTATIC: No closest method found." class-name method-name descriptor)
                             s)
              (let ((method-info (car closest-method-and-class-name))
                    (actual-class-name (cdr closest-method-and-class-name)))
                (if (method-abstractp method-info) ; todo: prove this can't happen
                    (error-state `(:invokestatic-abstract-method ,method-info) s)
                  (if (not (method-staticp method-info))
                      (obtain-and-throw-exception *IncompatibleClassChangeError* (list "ERROR: invokestatic called on non-static method ~x0.~x1~x2" actual-class-name method-name descriptor) th s)
                    (if (memberp class-name (initialized-classes s))
                        ;; If the class has been initialized, do the normal thing:
                        (execute-invokestatic-helper parameter-types
                                                     (count-slots-in-types parameter-types) ; (longs and doubles take two slots)
                                                     s th descriptor method-name actual-class-name method-info)
                      ;; otherwise, we first need to initialize at least one class:
                      (invoke-static-initializer-for-next-class class-name th s))))))))))))

(defthm jvm-statep-of-execute-invokestatic
  (implies (and (jvm-statep s)
                (call-stack-non-emptyp th s)
                (equal (instruction-opcode inst) :invokestatic)
                (equal inst (current-inst th s)) ; for the theorem about getclass ; todo think about this
                (instructionp inst)
                (jvm-instruction-okayp inst (pc (thread-top-frame th s)) (strip-cars (method-program (method-info (thread-top-frame th s)))))
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th))
           (jvm-statep (execute-invokestatic inst th s)))
  :hints (("Goal" :in-theory (enable execute-invokestatic
                                     execute-invokestatic-helper
                                     obtain-and-throw-exception
                                     throw-exception
                                     failed-to-enter-monitor-wrapper
                                     ;;todo:
                                     execute-java.lang.float.floattorawintbits
                                     execute-java.lang.float.intbitstofloat
                                     skip-invokestatic-instruction
                                     ;;obtain-an-object
                                     jvm-instruction-okayp
                                     maybe-addressp
                                     move-past-invoke-instruction
                                     method-programp-key-property-2-alt
                                     inst-len ;careful
                                     instructionp-redef
                                     instruction-args
                                     instruction-argsp))))

;inst is an invokevirtual instruction.
;inst has the form (invokeXXX class-name method-name descriptor formal-slot-count)
;returns (mv erp class-name dont-invoke) ;dont-invoke means the JVM model has special handling for this method
;called by the Android model.
;fixme: this is repetitive
;todo: this is out of sync with execute-invokevirtual
(defun lookup-method-for-invokevirtual (inst th s)
  (declare (xargs :guard (and (jvm-statep s)
                              (invokevirtual-instructionp inst))
                  :verify-guards nil
                  ))
  (let* (;(class-name (farg1 inst)) ;the actual method may come from a superclass ; fixme - So why is this even in the class file?
         (method-name (farg2 inst))
         (descriptor (farg3 inst))
         (parameter-types (farg4 inst))
         (obj-ref (top-operand (pop-items-off-stack parameter-types (stack (thread-top-frame th s))))))
    (if (null-refp obj-ref)
        (prog2$ (cw "ERROR: Trying to execute invokevirtual for method ~x0 on a null object." method-name)
                (mv t nil nil))
      (let* ((obj-type (acl2::get-class obj-ref (heap s))))
        (if (is-array-typep obj-type)
            (if (and (equal method-name "clone")
                     (equal descriptor "()Ljava/lang/Object;")) ;;fixme pass through calls to other methods of class Object (clone is the only overridden method)
                (mv nil nil t)
              (prog2$ (cw "ERROR: Calling :invokevirtual on an array object with an unknown method")
                      (mv t nil nil)))
          (let* (;;this is the method lookup precedure described in the spec for invokevirtual
                 ;;(do we do anything that corresponds to "resolution" as described in the spec?)
                 (closest-method-and-class-name (lookup-method obj-type
                                                               method-name
                                                               descriptor
                                                               (class-table s))))
            (mv nil ;no errors
                (cdr closest-method-and-class-name)
                nil)))))))

;Executes an invokevirtual on a clone() method of an array class.
;Method signature is:  "()Ljava/lang/Object;"
(defun execute-array-clone (component-type array-ad th s)
  (let* ((heap (heap s))
         (vals (acl2::array-contents array-ad heap)))
    (mv-let (new-ad heap)
            (build-new-array vals component-type heap)
            (modify th s
                    :pc (+ 3 ;(inst-length inst) ;step over the invoke instruction
                           (pc (thread-top-frame th s)))
                    :stack (push-operand new-ad (stack (thread-top-frame th s)))
                    :heap heap))))

;we should only open this when closest-method-and-class-name is a constant.
;fixme think about the use of method-name here!
(defund execute-invokevirtual-helper (parameter-types method-name descriptor
                                                      ;;formal-slot-count
                                                      objectref method-info class-name
                                                  th s)
  (let* (;longs and doubles take two slots
         (closest-method method-info)
         (actual-class-name class-name)
;         (prog (method-program closest-method))
         (s1 (modify th s
                     ;; we now do this in the return:
                     ;; :pc (+ 3 ;(inst-length inst)
                     ;;        (pc (thread-top-frame th s)))
                     :stack (pop-operand ;pop the object whose method is being invoked
                             (pop-items-off-stack parameter-types
                                                  (stack (thread-top-frame th s)))))))
    (cond
     ((method-staticp closest-method)
      (obtain-and-throw-exception *IncompatibleClassChangeError* (list "ERROR: invokevirtual called on static method ~x0.~x1~x2" class-name method-name descriptor) th s))
     ;; Handle invoking a native method:
     ((method-nativep closest-method)
      (let (;(tThread (rrefToThread objectref (thread-table s)))
            )
        (cond ;; ((equal method-name "start") ;fixme check class name too?   ;fixme put these back?
              ;;  (modify tThread s1 :status :SCHEDULED))
              ;; ((equal method-name "stop") ;fixme check class name too?
              ;;  (modify tThread s1 :status :UNSCHEDULED))
              (t ;s
               ;;I hope this is okay. -Eric
               (error-state (list 'error-unknown-native-method-found-when-executing-invokevirtual-in-state method-name closest-method s) s)
               ))))
     ;; Handle invoking synchronized method (FIXME can a method be both native and synchronized?)
     ((method-synchronizedp closest-method)
      (mv-let (successp new-monitor-table)
              (attempt-to-enter-monitor th (addressfix objectref) (monitor-table s))
              (if successp
                  (modify th s1
                          :call-stack
                          (push-frame (make-frame 0
                                            (initialize-locals (cons actual-class-name parameter-types) (stack (thread-top-frame th s)))
                                            (empty-operand-stack)
                                            objectref
                                            closest-method
                                            (make-method-designator actual-class-name ;;class-name
                                                                    method-name descriptor))
                                (call-stack th s1))
                          :monitor-table new-monitor-table)
                ;; failed to enter monitor, so the thread blocks: ;fixme print a message?
                (failed-to-enter-monitor-wrapper s closest-method) ;(error-state (list 'tried-to-call-invokevirtual-on-a-sync-method-with-non-lockable-object-i-think-thats-an-error s) s)
                )))
     ;; The usual case:
     (t (modify th s1
                :call-stack
                (push-frame (make-frame 0
                                  (initialize-locals (cons actual-class-name parameter-types) (stack (thread-top-frame th s)))
                                  (empty-operand-stack)
                                  (no-locked-object)
                                  closest-method
                                  (make-method-designator actual-class-name ;;class-name
                                                          method-name descriptor))
                      (call-stack th s1)))))))

; (:INVOKEVIRTUAL class-name method-name method-descriptor parameter-types)
;this should stay enabled, to expose the -helper
;; TODO: Call resolve-method.
;; TODO: Don't let this open if we can't resolve the type.
(defund execute-invokevirtual (inst th s)
  (let* (;(class-name (farg1 inst)) ;the actual method may come from a superclass ; fixme - So why is this even in the class file?
         (method-name (farg2 inst))
         (descriptor (farg3 inst))
         (parameter-types (farg4 inst))
         (formal-slot-count (count-slots-in-types parameter-types))
         (stack (stack (thread-top-frame th s)))
         (stack-size (operand-stack-size stack))
         (min-stack-size (+ 1 formal-slot-count)) ;one for the "this" object
         )
    (if (< stack-size min-stack-size)
        (error-state (list :invokevirtual-called-with-stack-too-small :actual stack-size :min min-stack-size) s)
      (let* ((obj-ref (top-operand (pop-items-off-stack parameter-types stack))))
        (if (not (acl2::addressp obj-ref))
            (error-state (list "INVOKEVIRTUAL with non-reference" obj-ref) s)
          (if (null-refp obj-ref)
              (prog2$ (cw "ERROR: Trying to execute invokevirtual on a null object.")
                      (obtain-and-throw-exception *NullPointerException* inst th s))
            (let* ((obj-type (acl2::get-class obj-ref (heap s))))
              (if (is-array-typep obj-type)
                  (if (and (equal method-name "clone")
                           (equal descriptor "()Ljava/lang/Object;")) ;;fixme pass through calls to other methods of class Object (clone is the only overridden method)
                      (execute-array-clone (get-array-component-type obj-type) obj-ref th s)
                    (error-state (list "ERROR: Calling :invokevirtual on an array object with an unknown method" method-name obj-ref obj-type) s))
                (if (not (class-namep obj-type))
                    (error-state (list "ERROR: Calling :invokevirtual: unexpected class name:" obj-ref) s)
                  (if (not (bound-in-class-tablep obj-type (class-table s)))
                      (error-state (list "ERROR: Class not bound in class-table:" obj-ref (class-table s)) s)
                    (let* (;;this is the method lookup precedure described in the spec for invokevirtual
                           ;;(do we do anything that corresponds to "resolution" as described in the spec?)
                           (closest-method-and-class-name (lookup-method obj-type
                                                                         method-name
                                                                         descriptor
                                                                         (class-table s))))
                      (if (not closest-method-and-class-name)
                          (error-state (list "ERROR IN INVOKEVIRTUAL: No closest method found." obj-type method-name descriptor)
                                       s)
                        (let* ((closest-method-info (car closest-method-and-class-name))
                               (class-name (cdr closest-method-and-class-name)))
                          (if (method-abstractp closest-method-info) ; todo: prove this can't happen
                              (error-state `(:invokevirtual-abstract-method ,closest-method-info) s)
                            (execute-invokevirtual-helper parameter-types
                                                          method-name
                                                          descriptor
                                                          ;; formal-slot-count
                                                          obj-ref
                                                          closest-method-info
                                                          class-name
                                                          th s)))))))))))))))

(defthm jvm-statep-of-execute-invokevirtual
  (implies (and (jvm-statep s)
                (call-stack-non-emptyp th s)
                (equal (instruction-opcode inst) :invokevirtual)
                (equal inst (current-inst th s)) ; todo think about this
                (instructionp inst)
                (jvm-instruction-okayp inst (pc (thread-top-frame th s)) (strip-cars (method-program (method-info (thread-top-frame th s)))))
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th))
           (jvm-statep (execute-invokevirtual inst th s)))
  :hints (("Goal" :in-theory (enable execute-invokevirtual
                                     execute-invokevirtual-helper
                                     obtain-and-throw-exception
                                     throw-exception
                                     failed-to-enter-monitor-wrapper
                                     jvm-instruction-okayp
                                     maybe-addressp
                                     method-programp-key-property-2-alt
                                     inst-len
                                     instructionp-redef
                                     instruction-args
                                     instruction-argsp))))

; (:INVOKEINTERFACE <class-name> <method-name> <method-descriptor> <formal-slot-count>)
;FFIXME recently added. check this over
;FFFIXME does this set the current class in the make-frame right?
;; TODO: Call resolve-method.
(defund execute-INVOKEINTERFACE (inst th s)
  (let* (;(class-name (farg1 inst))
         (method-name (farg2 inst))
         (descriptor (farg3 inst))
         (parameter-types (farg4 inst))
;         (formal-slot-count (count-slots-in-types parameter-types))
         (obj-ref (top-operand (pop-items-off-stack parameter-types (stack (thread-top-frame th s))))))
    (if (null-refp obj-ref)
        (obtain-and-throw-exception *NullPointerException* inst th s)
      (if (not (acl2::addressp obj-ref))
          (error-state (list "INVOKEINTERFACE with non-reference" obj-ref) s)
        (let* ((obj-class-name (acl2::get-class obj-ref (heap s))))
          (if (not (class-namep obj-class-name))
              (error-state (list "INVOKEINTERFACE with non-class" obj-class-name) s)
            (if (not (bound-in-class-tablep obj-class-name (class-table s)))
                (error-state (list "ERROR: Class not bound in class-table:" obj-class-name (class-table s)) s)
              (let* (;(obj-class-name (class-name-of-ref obj-ref (heap s)))
                     (closest-method-and-class-name
                      (lookup-method obj-class-name
                                     method-name
                                     descriptor ;signature
                                     (class-table s))))
                (if (not closest-method-and-class-name)
                    (error-state (list "ERROR IN INVOKEINTERFACE: No closest method found." obj-class-name method-name descriptor)
                                 s)
                  (let* ((closest-method (car closest-method-and-class-name))
                         (actual-class-name (cdr closest-method-and-class-name)))
                    (if (method-abstractp closest-method) ; todo: prove this can't happen
                        (error-state `(:invokeinterface-abstract-method ,closest-method) s)
                      (let (; (prog (method-program closest-method))
                         (s1 (modify th s
                                     ;; we now do this in the return:
                                     ;; :pc (+ 5 ;(inst-length inst)
                                     ;;        (pc (thread-top-frame th s)))
                                     :stack (pop-operand
                                             (pop-items-off-stack parameter-types (stack (thread-top-frame th s))))))
;(tThread (rrefToThread obj-ref (thread-table s)))
                         )
                    (cond
                      ((method-nativep closest-method)
                       (cond ;; ((equal method-name "start")  ;fixme put these back?
                         ;;  (modify tThread s1 :status :SCHEDULED))
                         ;; ((equal method-name "stop")
                         ;;  (modify tThread s1
                         ;;          :status :UNSCHEDULED))
                         (t ;s
;I hope this is okay. -Eric
                          (error-state (list 'error-unknown-native-method-found-when-executing-invokeinterface-in-state method-name closest-method s) s)
                          )))
                      ((method-synchronizedp closest-method)
                       (mv-let (successp new-monitor-table)
                           (attempt-to-enter-monitor th (addressfix obj-ref) (monitor-table s))
                         (if successp
                             (modify th s1
                                     :call-stack
                                     (push-frame (make-frame 0
                                                             (initialize-locals (cons actual-class-name parameter-types)
                                                                                (stack (thread-top-frame th s)))
                                                             (empty-operand-stack)
                                                             obj-ref
                                                             closest-method
                                                             (make-method-designator
                                                              actual-class-name method-name descriptor))
                                                 (call-stack th s1))
                                     :monitor-table new-monitor-table)
                           ;; failed to enter monitor, so the thread blocks: ;fixme: print a message
                           (failed-to-enter-monitor-wrapper s closest-method) ;(error-state (list 'tried-to-call-invokeinterface-on-a-sync-method-with-non-lockable-object-i-think-thats-an-error s) s)
                           )))
                      (t
                       (modify th s1
                               :call-stack
                               (push-frame (make-frame 0
                                                       (initialize-locals (cons actual-class-name parameter-types)
                                                                          (stack (thread-top-frame th s)))
                                                       (empty-operand-stack)
                                                       (no-locked-object)
                                                       closest-method
                                                       (make-method-designator
                                                        actual-class-name method-name descriptor))
                                           (call-stack th s1)))))))))))))))))


(defthm jvm-statep-of-execute-invokeinterface
  (implies (and (jvm-statep s)
                (call-stack-non-emptyp th s)
                (equal (instruction-opcode inst) :invokeinterface)
                (instructionp inst)
                (jvm-instruction-okayp inst (pc (thread-top-frame th s)) (strip-cars (method-program (method-info (thread-top-frame th s)))))
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th))
           (jvm-statep (execute-invokeinterface inst th s)))
  :hints (("Goal" :in-theory (enable execute-invokeinterface
                                     obtain-and-throw-exception
                                     failed-to-enter-monitor-wrapper
                                     jvm-instruction-okayp
                                     instructionp-redef
                                     instruction-args
                                     instruction-argsp))))

; -----------------------------------------------------------------------------
; (L2I) Instruction - long to int narrowing conversion

(defun execute-L2I (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (bvchop 32 (top-long (stack (thread-top-frame th s))))
                       (pop-long (stack (thread-top-frame th s))))))

; -----------------------------------------------------------------------------
; (LADD) Instruction - Add two longs from the top of the stack

;no need to decode the longs?
(defun execute-LADD (th s)
  (let* ((frame (thread-top-frame th s))
         (value1 (top-long (stack frame)))
         (value2 (top-long (pop-long (stack frame)))))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc frame))
            :stack (push-long (bvplus 64 value1 value2)
                              (pop-long (pop-long (stack frame)))))))

; -----------------------------------------------------------------------------
; (LALOAD) Instruction

(defun execute-LALOAD (th s)
  (let* ((index (top-operand (stack (thread-top-frame th s))))
         (arrayref (top-operand (pop-operand (stack (thread-top-frame th s))))))
    (if (null-refp arrayref)
        (obtain-and-throw-exception *NullPointerException* (list :laload arrayref) th s)
      (let* ((heap (heap s))
             (contents (acl2::array-contents arrayref heap))
             (len (len contents)))
        (if (or (acl2::sbvlt 32 index 0)
                (acl2::sbvge 32 index len))
            (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :laload (decode-signed index) arrayref) th s)
          (modify th s
                  :pc (+ 1 ;(inst-length inst)
                         (pc (thread-top-frame th s)))
                  :stack (push-long (acl2::bv-array-read 64
                                                         len
                                                         (decode-signed-non-neg index)
                                                         contents)
                                    (pop-operand (pop-operand (stack (thread-top-frame th s)))))))))))

;; (LAND)
(defun execute-LAND (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long (bvand 64
                                         (top-long (pop-long (stack (thread-top-frame th s))))
                                         (top-long (stack (thread-top-frame th s))))
                            (pop-long (pop-long (stack (thread-top-frame th s)))))))

;; (LASTORE)
(defun execute-LASTORE (th s)
  (let* ((value (top-long (stack (thread-top-frame th s))))
         (index (top-operand (pop-long (stack (thread-top-frame th s)))))
         (arrayref (top-operand (pop-operand (pop-long (stack (thread-top-frame th s)))))))
    (if (null-refp arrayref)
        (obtain-and-throw-exception *NullPointerException* (list :lastore arrayref) th s)
      (let* ((heap (heap s))
             (old-array-contents (acl2::array-contents arrayref heap))
             (len (len old-array-contents)))
        (if (or (acl2::sbvlt 32 index 0)
                (acl2::sbvge 32 index len))
            (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :LASTORE (decode-signed index) arrayref) th s)
          (modify th s
                  :pc (+ 1 ;(inst-length inst)
                         (pc (thread-top-frame th s)))
                  :stack (pop-operand (pop-operand (pop-long (stack (thread-top-frame th s)))))
                  :heap
                  (acl2::set-field (addressfix arrayref)
                                   (acl2::array-contents-pair)
                                   (acl2::bv-array-write 64
                                                         len
                                                         (decode-signed-non-neg index)
                                                         value old-array-contents)
                                   (heap s))))))))

;; (:LCMP)
(defun execute-LCMP (th s)
  (let* ((frame (thread-top-frame th s))
         (stack (stack frame))
         (value2 (top-long stack))
         (value1 (top-long (pop-long stack)))
         (result (if (acl2::sbvlt 64 value2 value1)
                     (encode-signed 1) ;; value1 greater
                   (if (equal value1 value2)
                       (encode-signed 0)
                     ;; value1 less:
                     (encode-signed -1)))))
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc frame))
          :stack (push-operand result
                               (pop-long (pop-long stack))))))

;for now, we are storing the intern table as a dummy static field of java.lang.String
;the table maps strings (FIXME what about unicode) to heap refs representing objects in class java.lang.String
;for now, we are assuming that all strings have already been interned.. - is that okay?
;FIXME i guess STRING here is currently an acl2 string, but it should probably be changed to support unicode?
;FIXME is this different from what calling the intern native method should do?
;FIXME don't pass in the class table
;returns (mv string-ref new-heap intern-table)
;this can be awkward to reason about - if we don't know whether a string has already been interned, then the simulation will split into cases, and the heap numbering will be different in each case..
(defund intern-string (string s)
     (declare (xargs :guard (and (stringp string)
                                 (jvm-statep s))
                     :guard-hints (("Goal" :in-theory (e/d (IS-AN-INTERFACEP ;todo
                                                            ) (CLASS-DECL-ACCESS-FLAGS))))
                     ))
  (let* ((intern-table (intern-table s))
         ;(looked-up-string (g string intern-table)) ;will be a heap reference (a natural) or nil if the string isn't in the table
         )
    (if (string-has-been-internedp string intern-table) ;fixme bad to split on this if?
        ;; if the string already has a corresponding heap reference, we just return that reference
        (mv (get-interned-string string intern-table) (heap s) (intern-table s))
      ;;otherwise, we build a string object (FFIXME do this right!), add it to the static field map (now the intern-table??), and return a reference to it
      (let* ((heap (heap s))
             (class-table (class-table s))
             (dom (acl2::rkeys heap))
             (ad1 (acl2::new-ad dom))       ;address of the char array
             (ad2 (acl2::nth-new-ad 2 dom)) ;address of the String object
             ;; first we make an array of chars for the value field of the String object
             ;; FIXME what about calling Object's constructor?  does this handle everything:?
             ;;(heap (acl2::set-field ad2 '("java.lang.String" .  "contents") string heap)) ;FIXME fixup to use unicode ;FIXME do we need this, given that we have the char array?  Shouldn't we store the string characters in the char array?!

             (chars (string-to-char-list string)) ;might unicode cause chars to have a different length than string?
             ;; Build and populate the character array that backs the string (FIXME Where in the spec does it mandate that this is how strings are to be represented?):
             (heap (initialize-one-dim-array ad1 :char chars heap)) ;fixme call build-new-array?

             ;; Build the string object:
             (heap (acl2::init-ref-in-heap ad2 "java.lang.String" class-table heap))
;this tries to mimic what the java code for Java.lang.String.<init> with no args does (can we somehow just call that code?)
             (heap (acl2::set-field ad2 (cons "java.lang.String" (make-field-id "offset" :int)) 0 heap))
             (heap (acl2::set-field ad2 (cons "java.lang.String" (make-field-id "count" :int)) (len chars) heap))
             (heap (acl2::set-field ad2 (cons "java.lang.String" (make-field-id "value" '(:array :char))) ad1 heap))
             (intern-table (set-interned-string string ad2 intern-table)))
        (mv ad2
            heap
            intern-table)))))

(defthm heapp-of-mv-nth-1-of-intern-string
  (implies (and (jvm-statep s)
                (bound-in-class-tablep '"java.lang.String" (class-table s))
                (not (is-an-interfacep "java.lang.String" (class-table s)))
                (stringp string))
           (heapp (mv-nth 1 (intern-string string s))))
  :hints (("Goal" :in-theory (enable intern-string))))

(defthm intern-tablep-of-mv-nth-2-of-intern-string
  (implies (and (jvm-statep s)
                (stringp string))
           (intern-tablep (mv-nth 2 (intern-string string s))))
  :hints (("Goal" :use (:instance INTERN-TABLEP-OF-INTERN-TABLE)
           :in-theory (e/d (intern-string intern-tablep) (INTERN-TABLEP-OF-INTERN-TABLE)))))


;; the gen-init-bindings can't give a field named :special-data
(defthm intern-table-okp-after-intern-string
  (implies (and (intern-table-okp (intern-table s) (heap s))
                ;(jvm-statep s)
;                (bound-in-class-tablep "java.lang.String" (class-table s)) ;add to jvm-statep? or drop?
;                (not (class-decl-interfacep (get-class-info "java.lang.String" (class-table s)))) ;add to jvm-statep? or drop (change class-infop to require that interfaces not have superclasses)
                )
           (intern-table-okp (mv-nth 2 (intern-string string s))
                             (mv-nth 1 (intern-string string s))))
  :hints (("Goal" :in-theory (e/d (intern-table-okp
                                   intern-string
                                   acl2::init-ref-in-heap
                                   acl2::set-fields)
                                  (string-has-been-internedp
                                   string-to-char-list
                                   get-superclasses)))))

;;     (if looked-up-string ;if the string is already in the table
;;         (mv looked-up-string heap)
;;       (let* ((new-intern-table (s string ref intern-table))
;; careful! setstaticfield now returns a new state
;;              (new-heap (setstaticfield "java.lang.String" *dummy-field-for-intern-table* new-intern-table s))

;;              ;allocate an address and build the string object... yikes!  should we call a constructor of class string?
;;              (new-address (acl2::new-ad (acl2::rkeys heap)))
;;              (new-heap (acl2::init-ref-in-heap
;;                         new-address
;;                         class-name
;;                         class-table
;;                         heap)))
;;         (mv ref new-heap)))))

(defthm intern-string-opener-when-not-present
  (implies (not (string-has-been-internedp string (intern-table s)))
           (equal (intern-string string s)
;  (declare (xargs :guard (stringp string)))
      (let* ((heap (heap s))
             (class-table (class-table s))
             (dom (acl2::rkeys heap))
             (ad1 (acl2::new-ad dom))       ;address of the char array
             (ad2 (acl2::nth-new-ad 2 dom)) ;address of the String object
             ;; first we make an array of chars for the value field of the String object
             ;; FIXME what about calling Object's constructor?  does this handle everything:?
             ;;(heap (acl2::set-field ad2 '("java.lang.String" .  "contents") string heap)) ;FIXME fixup to use unicode ;FIXME do we need this, given that we have the char array?  Shouldn't we store the string characters in the char array?!

             (chars (string-to-char-list string)) ;might unicode cause chars to have a different length than string?
             ;; Build and populate the character array that backs the string (FIXME Where in the spec does it mandate that this is how strings are to be represented?):
             (heap (initialize-one-dim-array ad1 :char chars heap))

             ;; Build the string object:
             (heap (acl2::init-ref-in-heap ad2 "java.lang.String" class-table heap))
;this tries to mimic what the java code for Java.lang.String.<init> with no args does (can we somehow just call that code?)
             (heap (acl2::set-field ad2 (cons "java.lang.String" (make-field-id "offset" :int)) 0 heap))
             (heap (acl2::set-field ad2 (cons "java.lang.String" (make-field-id "count" :int)) (len chars) heap))
             (heap (acl2::set-field ad2 (cons "java.lang.String" (make-field-id "value" '(:array :char))) ad1 heap))
             (intern-table (set-interned-string string ad2 (intern-table s))))
        (mv ad2
            heap
            intern-table))))
  :hints (("Goal" :in-theory (union-theories '(intern-string) (theory 'minimal-theory)))))

(defthm get-field-of-mv-nth-1-of-intern-string-irrel
  (implies (set::in ad (acl2::rkeys (heap s)))
           (equal (acl2::get-field ad pair (mv-nth 1 (intern-string string s)))
                  (acl2::get-field ad pair (heap s))))
  :hints (("Goal" :in-theory (enable intern-string))))


; this is used for the following two instructions:
; (LDC tagged-value)
; (LDC_W tagged-value)
; where the tagged-value contains a BV32, a java-floatp, a string, or class-namep
;wide-flag indicates whether the instruction is LDC_W or LDC.  the only difference is the amount the PC should be advanced (3 or 2 bytes, resp.).
(defun execute-LDC (inst th s wide-flag)
  ;; (declare (xargs :guard (and (INSTRUCTIONP inst)
  ;;                             (jvm-statep s))))
  (let* ((tagged-value (farg1 inst))
         (tag (car tagged-value))
         (value (cdr tagged-value))
         (inst-length (if wide-flag 3 2)))
    (case tag ;should always be able to decide which case applies, since the value comes from the class file
      (:string (if (not (bound-in-class-tablep '"java.lang.String" (CLASS-TABLE S)))
                   (error-state "Trying to intern a string in LDC or LDC_W, but the String class is not present in the class table." s)
                 (if (is-an-interfacep "java.lang.String" (CLASS-TABLE S))
                     (error-state "Trying to intern a string, but String is an interface (should be a class)." s)
                   (if (not (stringp value)) ; todo: drop?
                       (error-state "Bad :string constant." s)
                     (mv-let (ref new-heap new-intern-table)
                       (intern-string value s)
                       (modify th s
                               :intern-table new-intern-table
                               :heap new-heap
                               :pc (+ inst-length
                                      (pc (thread-top-frame th s)))
                               :stack (push-operand ref (stack (thread-top-frame th s)))))))))
      (:class (let* ((class-name value))
                (if (not (class-namep class-name)) ; todo: drop?
                    (error-state "Bad :class constant." s)
                  (let ((erp (resolve-class class-name (class-table s))))
                    (if erp
                        (if (stringp erp)
                            (obtain-and-throw-exception erp (list "ERROR IN LDC or LDC_W: Failed to resolve class." :debug-info class-name) th s)
                          (error-state erp s))
                      (let* ((heapref-table (heapref-table s))
                             (class-object-ref (get-class-object class-name heapref-table)))
                        (if (not class-object-ref)
                            (push-frame-to-build-class-object class-name th s)
;(error-state (list "No class object in heapref-table for class:" class-name) s)
                          (modify th s :pc (+ inst-length
                                              (pc (thread-top-frame th s)))
                                  :stack (push-operand class-object-ref (stack (thread-top-frame th s)))))))))))
      (:float (modify th s
                      :pc (+ inst-length
                             (pc (thread-top-frame th s)))
                      :stack (push-operand value
                                           (stack (thread-top-frame th s)))))
      (otherwise ;; It's an int
       ;; TODO: Handle the case of a method or method handle?!  does the parser handle that?
       (modify th s
               :pc (+ inst-length
                      (pc (thread-top-frame th s)))
               :stack (push-operand (encode-unsigned value) ;new
                                    (stack (thread-top-frame th s))))))))

; (LDC2_W tagged-value), where tagged-value contains a BV64 or a java-doublep
(defun execute-LDC2_W (inst th s)
  (let* ((tagged-value (farg1 inst))
         (tag (car tagged-value))
         (value (cdr tagged-value)))
    (case tag
      (:double (modify th s
                       :pc (+ 3 ;(inst-length inst)
                              (pc (thread-top-frame th s)))
                       :stack (push-long value
                                         (stack (thread-top-frame th s)))))
      (otherwise ;; It's a long
       ;; it's a regular BV representing a long:
       (modify th s
               :pc (+ 3 ;(inst-length inst)
                      (pc (thread-top-frame th s)))
               :stack (push-long (encode-unsigned-long value) ;new
                                 (stack (thread-top-frame th s))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (LSTORE index inst-len). Store long into local variable.  We store the entire
;; long at the lower of the two indices (index and index+1).
(defund execute-LSTORE (inst th s)
  (let ((index (farg1 inst))
        (inst-len (farg2 inst)))
    (modify th s
            :pc (+ inst-len
                   (pc (thread-top-frame th s)))
            :locals (update-nth-local index
                                      (top-long (stack (thread-top-frame th s)))
                                      (locals (thread-top-frame th s)))
            :stack (pop-long (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-lstore
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :lstore)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-LSTORE inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-LSTORE
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp
                            load-helper-1
                            load-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;This covers the following four instructions:
; (LSTORE_0)
; (LSTORE_1)
; (LSTORE_2)
; (LSTORE_3)
;store a long into the locals
(defun execute-LSTORE_X (th s n)
  (modify th s
          :pc (+ 1 (pc (thread-top-frame th s)))
          :locals (update-nth-local n
                                    (top-long (stack (thread-top-frame th s)))
                                    (locals (thread-top-frame th s)))
          :stack (pop-long (stack (thread-top-frame th s)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (LLOAD localslotnum inst-len) Push a long local onto the stack
;longs take up 2 slots, but the value is stored entirely in the lower-numbered slot - fixme - are we consistent about this?
(defund execute-LLOAD (inst th s)
  (let ((inst-len (farg2 inst)))
    (modify th s
            :pc (+ inst-len
                   (pc (thread-top-frame th s)))
            :stack (push-long (nth-local (farg1 inst)
                                         (locals (thread-top-frame th s)))
                              (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-lload
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :lload)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-LLOAD inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-LLOAD
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp
                            load-helper-1
                            load-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;This covers the following four instructions:
; (LLOAD_0)
; (LLOAD_1)
; (LLOAD_2)
; (LLOAD_3)
; Push a long local onto the stack
;n is the local slot number
(defun execute-LLOAD_X (th s n)
  (modify th s
          :pc (+ 1 (pc (thread-top-frame th s)))
          :stack (push-long (nth-local n (locals (thread-top-frame th s)))
                            (stack (thread-top-frame th s)))))

;; Test for the "special case" for LDIV:
(assert-event (equal (acl2::sbvdiv 64 *min-signed-int64* -1) *min-signed-int64*))

;; (:LDIV)
;fixme is the division exactly right?
;fixme handle overflow case
;fixme prove putative proeprties from spec
(defun execute-LDIV (th s)
  (let* ((value1 (top-long (pop-long (stack (thread-top-frame th s)))))
         (value2 (top-long (stack (thread-top-frame th s)))) ;the divisor
         (result (acl2::sbvdiv 64 value1 value2)))
    (if (eql 0 value2) ; todo: use =
        (obtain-and-throw-exception *ArithmeticException* (list :ldiv value1 value2) th s)
      (modify th s
              :pc (+ 1 ;(inst-length inst)
                     (pc (thread-top-frame th s)))
              :stack (push-long result (pop-long (pop-long (stack (thread-top-frame th s)))))))))

; (LMUL)
(defun execute-LMUL (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long (bvmult 64
                                          (top-long (pop-long (stack (thread-top-frame th s))))
                                          (top-long (stack (thread-top-frame th s))))
                            (pop-long (pop-long (stack (thread-top-frame th s)))))))


; (LNEG) Instruction
; Because of the way the JVM represents 2's complement ints, the negation of the most negative int is itself
(defun execute-LNEG (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long (bvminus 64 0 (top-long (stack (thread-top-frame th s))))
                            (pop-long (stack (thread-top-frame th s))))))


; (LOR)
(defun execute-LOR (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long (bvor 64
                                        (top-long (stack (thread-top-frame th s)))
                                        (top-long (pop-long (stack (thread-top-frame th s)))))
                            (pop-long (pop-long (stack (thread-top-frame th s)))))))


; (LREM)
;fixme is the result right?
(defun execute-LREM (th s)
  (let* ((value1 (top-long (pop-long (stack (thread-top-frame th s)))))
         (value2 (top-long (stack (thread-top-frame th s)))) ;the divisor
         (result (acl2::sbvrem 64 value1 value2)))
    (if (eql 0 value2) ; todo: use =
        (obtain-and-throw-exception *ArithmeticException* (list :lrem value1 value2) th s)
      (modify th s
              :pc (+ 1 ;(inst-length inst)
                     (pc (thread-top-frame th s)))
              :stack (push-long result
                                (pop-long (pop-long (stack (thread-top-frame th s)))))))))

; (LSUB)
(defun execute-LSUB (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long (bvminus 64
                                           (top-long (pop-long (stack (thread-top-frame th s))))
                                           (top-long (stack (thread-top-frame th s))))
                            (pop-long (pop-long (stack (thread-top-frame th s)))))))

; (LXOR)
(defun execute-LXOR (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long (bvxor 64
                                         (top-long (stack (thread-top-frame th s)))
                                         (top-long (pop-long (stack (thread-top-frame th s)))))
                            (pop-long (pop-long (stack (thread-top-frame th s)))))))


; (MONITORENTER)
(defun execute-MONITORENTER (th s)
  (let ((objectref (top-operand (stack (thread-top-frame th s)))))
    (if (null-refp objectref)
        (obtain-and-throw-exception *NullPointerException* (list :monitorenter) th s)
      (mv-let (successp new-monitor-table)
              (attempt-to-enter-monitor th (addressfix objectref) (monitor-table s))
              (if successp
                  (modify th s
                          :pc (+ 1 ;(inst-length inst)
                                 (pc (thread-top-frame th s)))
                          :monitor-table new-monitor-table
                          :stack (pop-operand (stack (thread-top-frame th s))))
                ;; failed to enter monitor, so the thread blocks:
                (failed-to-enter-monitor-wrapper s nil))))))

; (MONITOREXIT)
(defun execute-MONITOREXIT (th s)
  (let ((objectref (top-operand (stack (thread-top-frame th s))))
        (monitor-table (monitor-table s))
        )
    (mv-let (error-message monitor-table)
            (attempt-to-exit-monitor th objectref monitor-table)
            (if error-message
                (error-state error-message s) ;fixme throw a real exception here
              (modify th s
                      :pc (+ 1 ;(inst-length inst)
                             (pc (thread-top-frame th s)))
                      :stack (pop-operand (stack (thread-top-frame th s)))
                      :monitor-table monitor-table)))))

; (NEW class-name)
(defun execute-NEW (inst th s)
  (let* ((type (farg1 inst)) ; could be an interface or an array
         (class-table (class-table s))
         (heap (heap s))
         (erp (resolve-class type class-table))) ;todo: specialize to non-array types (see check below)
    (if erp
        (if (stringp erp)
            (obtain-and-throw-exception erp (list "ERROR IN NEW: Failed to resolve class." :debug-info type) th s)
          (error-state erp s))
      (if (array-typep type)
          (error-state (list "Trying to call NEW, but the type given is an array class." type) s)
        (if (not (class-namep type))
            (error-state (list "Trying to build a new object, but the class given is not a valid class name." type) s)
          (if (not (is-a-classp type class-table))
              (error-state (list "Trying to build a new object but the type is not a class." type) s)
            ;; (if (not (non-array-classp type class-table))
            ;;     (error-state (list "Trying to build a new object, but the class given is not a non-array class." type) s)
            (let* ((initialized-classes (initialized-classes s)))
              (if (not (memberp type initialized-classes))
                  ;; We first need to initialize at least one class:
                  (invoke-static-initializer-for-next-class type th s)
                ;; Otherwise, do the normal thing:
                (let* ((class-table (class-table s))
                       (new-address (acl2::new-ad (acl2::rkeys heap)))
                       (new-heap (acl2::init-ref-in-heap new-address
                                                         type
                                                         class-table
                                                         heap))
                       (s1 (modify th s
                                   :pc (+ 3 ;(inst-length inst)
                                          (pc (thread-top-frame th s)))
                                   :stack (push-operand new-address
                                                        (stack (thread-top-frame th s)))
                                   :heap new-heap)))
                  (if (thread-classp type class-table)
                      (error-state "We don't yet handle threads." s)
                    ;;FIXME implement this: Get a new thread-id, make the thread object (storing that thread-id in a fake field), and call the run method on the new object
                    ;; (modify nil s1
                    ;;         :thread-table
                    ;;         (addto-tt
                    ;;          (push
                    ;;           (make-frame 0
                    ;;                       (list new-address)
                    ;;                       (empty-operand-stack)
                    ;;                       (method-program (lookup-method type "run" nil ;FFFIXME check this nil - fix to use descriptor!
                    ;;                                                      class-table))
                    ;;                       :UNLOCKED
                    ;;                       (make-method-designator type  "run" 'fake-descriptor-for-run-method  ;;bozo fix
                    ;;           nil)
                    ;;          :UNSCHEDULED
                    ;;          new-address
                    ;;          (thread-table s1)))
                    s1))))))))))

;; (:PUTFIELD <class-name> <field-id> <long-flag>)
;TODO: Handle all the checks and the value set conversion.
(defun execute-PUTFIELD (inst th s)
  (let ((class-name (farg1 inst)) ;this class-name may not be the class or interface that declared the field ;; cannot be an array class (checked in get-info-from-srf)
        (field-id (farg2 inst))
        (class-table (class-table s))
        (frame (thread-top-frame th s)))
    (if (not (and (class-namep class-name)
                  (field-idp field-id)))
        (error-state "In putfield, a bad class name or field name was given." s) ;currently needed for the proof of jvm-statep-of-do-inst. todo: remove it?
      (mv-let (erp class-name-of-resolved-field)
        (resolve-field field-id class-name (cur-class-name frame) class-table)
        (if erp
            (if (stringp erp)
                (obtain-and-throw-exception erp (list "ERROR IN PUTFIELD: Failed to resolve field." :debug-info field-id class-name (cur-class-name frame)) th s)
              (error-state erp s))
          (if (field-is-staticp field-id class-name-of-resolved-field class-table)
              (obtain-and-throw-exception *IncompatibleClassChangeError* (list "ERROR in PUTFIELD: field should not be static" field-id) th s)
            ;; TODO: Add checks if the field is final...
            (let* ((long-flag (farg3 inst))
                   (stack (stack frame))
                   (objectref (if long-flag
                                  (top-operand (pop-long stack))
                                (top-operand (pop-operand stack)))))
              (if (null-refp objectref)
                  (obtain-and-throw-exception *NullPointerException* (list inst objectref th s) th s)
                (let* ((value (if long-flag
                                  (top-long stack)
                                (top-operand stack)))
                       (field-type (field-id-type field-id))
                       ;; Truncate the value stored.  The JVM spec dictates
                       ;; this for booleans but is silent about the other
                       ;; types.  The actual JVM seems to do it.  We emailed
                       ;; Oracle to ask.  Values will be sign extended if
                       ;; appropriate when read back out with getfield.
                       (value (if (eq :boolean field-type)
                                  (bvchop 1 value)
                                (if (eq :byte field-type)
                                    (bvchop 8 value)
                                  (if (or (eq :short field-type)
                                          (eq :char field-type))
                                      (bvchop 16 value)
                                    value)))))
                  (modify th s
                          :pc (+ 3 ;(inst-length inst)
                                 (pc frame))
                          :stack (if long-flag
                                     (pop-operand (pop-long stack))
                                   (pop-operand (pop-operand stack)))
                          :heap (acl2::set-field (addressfix objectref) ;handle this better (here and elsewhere)?  maybe with a defensive approach that throws an error if ref is not an address.
                                                 (cons class-name-of-resolved-field field-id)
                                                 value
                                                 (heap s))))))))))))

; (PUTSTATIC class-name field-id long-flag)
(defun execute-PUTSTATIC (inst th s)
  (let* ((class-name (farg1 inst)) ;this class-name may not be the class or interface that declared the field
         (field-id (farg2 inst))
         (class-table (class-table s))
         (frame (thread-top-frame th s))
         (current-class-name (cur-class-name frame)))
    (if (not (class-namep class-name)) ;todo: or copy what getstatic does...
        (error-state (list "Bad class name in PUTSTATIC instruction." inst) s)
      (mv-let (erp class-name-of-resolved-field)
        (resolve-field field-id class-name current-class-name class-table)
        (if erp
            (if (stringp erp)
                (obtain-and-throw-exception erp (list "ERROR IN PUTSTATIC: Failed to resolve field." :debug-info field-id class-name current-class-name) th s)
              (error-state erp s))
          (if (and (not (field-is-staticp field-id class-name-of-resolved-field class-table))
                   (not (is-an-interfacep class-name-of-resolved-field class-table)))
              (obtain-and-throw-exception *IncompatibleClassChangeError* (list "Error: field should be static" field-id) th s)
            (let ((initialized-classes (initialized-classes s)))
              (if (memberp class-name-of-resolved-field initialized-classes)
                  ;; If the class has been initialized, do the normal thing:
                  (let* ((stack (stack (thread-top-frame th s)))
                         (long-flag (farg3 inst))
                         (value (if long-flag
                                    (top-long stack)
                                  (top-operand stack))))
                    (modify th s
                            :static-field-map (set-static-field class-name-of-resolved-field field-id value (static-field-map s))
                            :pc (+ 3 ;(inst-length inst)
                                   (pc (thread-top-frame th s)))
                            :stack (if long-flag
                                       (pop-long stack)
                                     (pop-operand stack))))
                ;; otherwise, we first need to initialize at least one class
                (invoke-static-initializer-for-next-class class-name-of-resolved-field th s)))))))))

; (SALOAD)
(defun execute-SALOAD (th s)
  (let* ((index (top-operand (stack (thread-top-frame th s))))
         (arrayref (top-operand (pop-operand (stack (thread-top-frame th s))))))
    (if (null-refp arrayref)
        (obtain-and-throw-exception *NullPointerException* (list :saload arrayref) th s)
      (let* ((heap (heap s))
             (contents (acl2::array-contents arrayref heap))
             (len (len contents)))
        (if (or (acl2::sbvlt 32 index 0) ;should I use boolor in places like this to avoid replication of terms? or a version of boolor that always gets opened?
                (acl2::sbvge 32 index len))
            (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :SALOAD (decode-signed index) arrayref) th s)
          (modify th s
                  :pc (+ 1 ;(inst-length inst)
                         (pc (thread-top-frame th s)))
                  :stack (push-operand (bvsx 32 16 (acl2::bv-array-read 16 len
                                                                      (decode-signed-non-neg index)
                                                                      contents))
                               (pop-operand (pop-operand (stack (thread-top-frame th s)))))))))))

; (SASTORE)
(defun execute-SASTORE (th s)
  (let* ((value (bvchop 16 (top-operand (stack (thread-top-frame th s))))) ;truncate int to short
         (index (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (arrayref (top-operand (pop-operand (pop-operand (stack (thread-top-frame th s)))))))
    (if (null-refp arrayref)
        (obtain-and-throw-exception *NullPointerException* (list :sastore arrayref) th s)
      (let* ((heap (heap s))
             (old-array-contents (acl2::array-contents arrayref heap))
             (len (len old-array-contents)))
        (if (or (acl2::sbvlt 32 index 0)
                (acl2::sbvge 32 index len))
            (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :SASTORE (decode-signed index) arrayref) th s)
          (modify th s
                  :pc (+ 1 ;(inst-length inst)
                         (pc (thread-top-frame th s)))
                  :stack (pop-operand (pop-operand (pop-operand (stack (thread-top-frame th s)))))
                  :heap
                  (acl2::set-field (addressfix arrayref)
                                   (acl2::array-contents-pair)
                                   (acl2::bv-array-write 16 len (decode-signed-non-neg index) value old-array-contents)
                                   (heap s))))))))

;; The program is just an alist from byte-offsets to instructions.  (I think M5 was different (programs were just sequences of instructions).  M5 had a function index-into-program which would repeatedly call inst-length, but that was slow and also wouldn't work with instrs preceded by wide (you can't tell from the translated instr whether it was preceded by wide).)

;; (thm
;;  (IMPLIES (AND (BOUND-IN-ALISTP TH (THREAD-TABLE S))
;;                (JVM-STATEP S)
;; ;               (THREAD-DESIGNATORP TH)
;;                )
;;           (FRAMEP (TOP-OPERAND (GET-CALL-STACK (BINDING TH (THREAD-TABLE S)))))))

;; (thm
;;  (IMPLIES (AND (BOUND-IN-ALISTP TH (THREAD-TABLE S))
;;                (JVM-STATEP S)
;; ;               (THREAD-DESIGNATORP TH)
;;                )
;;           (method-programp (PROGRAM (TOP-OPERAND (GET-CALL-STACK (BINDING TH (THREAD-TABLE S)))))))
;;  :hints (("Goal" :in-theory (enable JVM-STATEP THREAD-TABLEP))))

(defun execute-D2F (th s)
  (let* ((value (top-long (stack (thread-top-frame th s))))
         (result (d2f value)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand result
                                 (pop-long (stack (thread-top-frame th s)))))))

(defun execute-D2I (th s)
  (let* ((value (top-long (stack (thread-top-frame th s))))
         (result (d2i value)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand result
                                 (pop-long (stack (thread-top-frame th s)))))))

(defun execute-D2L (th s)
  (let* ((value (top-long (stack (thread-top-frame th s))))
         (result (d2l value)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-long result
                              (pop-long (stack (thread-top-frame th s)))))))


;;TTTODO: Flesh these out
(defstub float-add (x y) t)
(defstub float-div (x y) t)
(defstub float-sub (x y) t)
(defstub float-rem (x y) t)
(defstub float-neg (x) t)

(defstub double-add (x y) t)
(defstub double-mul (x y) t)
(defstub double-div (x y) t)
(defstub double-sub (x y) t)
(defstub double-rem (x y) t)
(defstub double-neg (x) t)

; (FADD)
(defun execute-FADD (th s)
  (let* ((value2 (top-operand (stack (thread-top-frame th s))))
         (value1 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (result (float-add value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand result
                                 (pop-operand (pop-operand (stack (thread-top-frame th s))))))))

; (FMUL)
(defun execute-FMUL (th s)
  (let* ((value2 (top-operand (stack (thread-top-frame th s))))
         (value1 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (result (fmul value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand result
                                 (pop-operand (pop-operand (stack (thread-top-frame th s))))))))

; (FDIV)
(defun execute-FDIV (th s)
  (let* ((value2 (top-operand (stack (thread-top-frame th s))))
         (value1 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (result (float-div value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand result
                                 (pop-operand (pop-operand (stack (thread-top-frame th s))))))))


; (FREM)
(defun execute-FREM (th s)
  (let* ((value2 (top-operand (stack (thread-top-frame th s))))
         (value1 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (result (float-rem value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand result
                                 (pop-operand (pop-operand (stack (thread-top-frame th s))))))))

; (FSUB)
(defun execute-FSUB (th s)
  (let* ((value2 (top-operand (stack (thread-top-frame th s))))
         (value1 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (result (float-sub value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand result
                                 (pop-operand (pop-operand (stack (thread-top-frame th s))))))))

; (DADD)
(defun execute-DADD (th s)
  (let* ((value2 (top-long (stack (thread-top-frame th s))))
         (value1 (top-long (pop-long (stack (thread-top-frame th s)))))
         (result (double-add value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-long result
                                 (pop-long (pop-long (stack (thread-top-frame th s))))))))

; (DMUL)
(defun execute-DMUL (th s)
  (let* ((value2 (top-long (stack (thread-top-frame th s))))
         (value1 (top-long (pop-long (stack (thread-top-frame th s)))))
         (result (double-mul value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-long result
                                 (pop-long (pop-long (stack (thread-top-frame th s))))))))

; (DDIV)
(defun execute-DDIV (th s)
  (let* ((value2 (top-long (stack (thread-top-frame th s))))
         (value1 (top-long (pop-long (stack (thread-top-frame th s)))))
         (result (double-div value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-long result
                                 (pop-long (pop-long (stack (thread-top-frame th s))))))))

; (DREM)
(defun execute-DREM (th s)
  (let* ((value2 (top-long (stack (thread-top-frame th s))))
         (value1 (top-long (pop-long (stack (thread-top-frame th s)))))
         (result (double-rem value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-long result
                                 (pop-long (pop-long (stack (thread-top-frame th s))))))))

; (DSUB)
(defun execute-DSUB (th s)
  (let* ((value2 (top-long (stack (thread-top-frame th s))))
         (value1 (top-long (pop-long (stack (thread-top-frame th s)))))
         (result (double-sub value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-long result
                                 (pop-long (pop-long (stack (thread-top-frame th s))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(FLOAD localslotnum inst-len)
;identical to ILOAD
(defund execute-FLOAD (inst th s)
  (let ((inst-len (farg2 inst))) ;length can vary because of WIDE
    (modify th s
            :pc (+ inst-len
                   (pc (thread-top-frame th s)))
            :stack (push-operand (nth-local (farg1 inst)
                                            (locals (thread-top-frame th s)))
                                 (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-fload
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :fload)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-FLOAD inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-FLOAD
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp
                            load-helper-1
                            load-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;same as ILOAD_X
(defun execute-FLOAD_X (th s n)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (nth-local n (locals (thread-top-frame th s)))
                               (stack (thread-top-frame th s)))))

; (DLOAD index inst-len). Load double from local variable.
;longs take up 2 slots, but the value is stored entirely in the lower-numbered slot - fixme - are we consistent about this?
;identical to LLOAD?
(defund execute-DLOAD (inst th s)
  (let ((inst-len (farg2 inst)))
    (modify th s
            :pc (+ inst-len
                   (pc (thread-top-frame th s)))
            :stack (push-long (nth-local (farg1 inst)
                                         (locals (thread-top-frame th s)))
                              (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-dload
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :dload)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-DLOAD inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-DLOAD
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp
                            load-helper-1
                            load-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;same as LLOAD_X
(defun execute-DLOAD_X (th s n)
  (modify th s
          :pc (+ 1 (pc (thread-top-frame th s)))
          :stack (push-long (nth-local n (locals (thread-top-frame th s)))
                            (stack (thread-top-frame th s)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (FSTORE localslotnum inst-len)  - store an int into the locals
;same as ISTORE
(defund execute-FSTORE (inst th s)
  (let ((inst-len (farg2 inst)))
    (modify th s
            :pc (+ inst-len
                   (pc (thread-top-frame th s)))
            :locals (update-nth-local (farg1 inst)
                                      (top-operand (stack (thread-top-frame th s)))
                                      (locals (thread-top-frame th s)))
            :stack (pop-operand (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-fstore
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :fstore)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-FSTORE inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-FSTORE
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp
                            load-helper-1
                            load-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;same as ISTORE_X
(defun execute-FSTORE_X (th s n)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :locals (update-nth-local n
                                     (top-operand (stack (thread-top-frame th s)))
                                     (locals (thread-top-frame th s)))
          :stack (pop-operand (stack (thread-top-frame th s)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (DSTORE local-slot-num inst-len)
; store a double into the locals
;same as LSTORE
(defund execute-DSTORE (inst th s)
  (let ((index (farg1 inst))
        (inst-len (farg2 inst)))
    (modify th s
            :pc (+ inst-len
                   (pc (thread-top-frame th s)))
            :locals (update-nth-local index
                                      (top-long (stack (thread-top-frame th s)))
                                      (locals (thread-top-frame th s)))
            :stack (pop-long (stack (thread-top-frame th s))))))

(defthm jvm-statep-of-execute-dstore
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :dstore)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-DSTORE inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-DSTORE
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp
                            load-helper-1
                            load-helper-3
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;This covers the following four instructions:
; (DSTORE_0)
; (DSTORE_1)
; (DSTORE_2)
; (DSTORE_3)
;store a double into the locals
;same as LSTORE_X
(defun execute-DSTORE_X (th s n)
  (modify th s
          :pc (+ 1 (pc (thread-top-frame th s)))
          :locals (update-nth-local n
                                    (top-long (stack (thread-top-frame th s)))
                                    (locals (thread-top-frame th s)))
          :stack (pop-long (stack (thread-top-frame th s)))))

; (FNEG)
(defun execute-FNEG (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (float-neg (top-operand (stack (thread-top-frame th s))))
                               (pop-operand (stack (thread-top-frame th s))))))

; (DNEG) Instruction
(defun execute-DNEG (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long (double-neg (top-long (stack (thread-top-frame th s))))
                            (pop-long (stack (thread-top-frame th s))))))

;(FALOAD) - load from array of floats
;TODO: Eventualy the nth might be a bv-array-read
(defun execute-faload (th s)
  (let* ((frame (thread-top-frame th s))
         (stack (stack frame))
         (index (top-operand stack))
         (arrayref (top-operand (pop-operand stack)))
         (contents (acl2::array-contents arrayref (heap s)))
         (len (len contents)))
    (if (null-refp arrayref)
        (obtain-and-throw-exception *NullPointerException* (list :faload arrayref) th s)
      (if (or (acl2::sbvlt 32 index 0)
              (acl2::sbvge 32 index len))
          (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :faload (decode-signed index) arrayref) th s)
        (modify th s
                :pc (+ 1 ;(inst-length inst)
                       (pc frame))
                :stack (push-operand (nth (decode-signed-non-neg index) contents) ;use something better than nth here?
                                     (pop-operand (pop-operand stack))))))))

;(DALOAD) - load from array of doubles
;TODO: Eventualy the nth might be a bv-array-read
(defun execute-daload (th s)
  (let* ((frame (thread-top-frame th s))
         (stack (stack frame))
         (index (top-operand stack))
         (arrayref (top-operand (pop-operand stack)))
         (contents (acl2::array-contents arrayref (heap s)))
         (len (len contents)))
    (if (null-refp arrayref)
        (obtain-and-throw-exception *NullPointerException* (list :faload arrayref) th s)
      (if (or (acl2::sbvlt 32 index 0)
              (acl2::sbvge 32 index len))
          (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :faload (decode-signed index) arrayref) th s)
        (modify th s
                :pc (+ 1 ;(inst-length inst)
                       (pc frame))
                :stack (push-long (nth (decode-signed-non-neg index) contents) ;use something better than nth here?
                                  (pop-operand (pop-operand stack))))))))

;(FASTORE)
;; Store into array of floats
;TODO: Eventualy the update-nth might be a bv-array-write
;TODO: What about value set conversion?
(defun execute-FASTORE (th s)
  (let* ((value (top-operand (stack (thread-top-frame th s))))
         (index (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (arrayref (top-operand (pop-operand (pop-operand (stack (thread-top-frame th s))))))
         (old-array-contents (acl2::get-field arrayref (acl2::array-contents-pair) (heap s))))
    (if (null-refp arrayref)
        (obtain-and-throw-exception *NullPointerException* (list :fastore arrayref) th s)
      (if (or (acl2::sbvlt 32 index 0) ;FFIXME CRUD the "or" here (or maybe the >=) can cause case splitting
              (acl2::sbvge 32 index (array-length arrayref (heap s))))
          (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :fastore (decode-signed index) arrayref) th s)
        (modify th s
                :pc (+ 1 ;(inst-length inst)
                       (pc (thread-top-frame th s)))
                :stack (pop-operand (pop-operand (pop-operand (stack (thread-top-frame th s)))))
                :heap (acl2::set-field (addressfix arrayref)
                                       (acl2::array-contents-pair)
                                       ;;ffixme can we do anything better than update-nth?
                                       (update-nth (decode-signed-non-neg index) value old-array-contents)
                                       (heap s)))))))


;(DASTORE)
;; Store into array of doubles
;TODO: Eventualy the update-nth might be a bv-array-write
;TODO: What about value set conversion?
(defun execute-DASTORE (th s)
  (let* ((value (top-long (stack (thread-top-frame th s))))
         (index (top-operand (pop-long (stack (thread-top-frame th s)))))
         (arrayref (top-operand (pop-operand (pop-long (stack (thread-top-frame th s))))))
         (old-array-contents (acl2::get-field arrayref (acl2::array-contents-pair) (heap s))))
    (if (null-refp arrayref)
        (obtain-and-throw-exception *NullPointerException* (list :dastore arrayref) th s)
      (if (or (acl2::sbvlt 32 index 0) ;FFIXME CRUD the "or" here (or maybe the >=) can cause case splitting
              (acl2::sbvge 32 index (array-length arrayref (heap s))))
          (obtain-and-throw-exception *ArrayIndexOutOfBoundsException* (list :dastore (decode-signed index) arrayref) th s)
        (modify th s
                :pc (+ 1 ;(inst-length inst)
                       (pc (thread-top-frame th s)))
                :stack (pop-operand (pop-operand (pop-long (stack (thread-top-frame th s)))))
                :heap (acl2::set-field (addressfix arrayref)
                                       (acl2::array-contents-pair)
                                       ;;ffixme can we do anything better than update-nth?
                                       (update-nth (decode-signed-non-neg index) value old-array-contents)
                                       (heap s)))))))

;; TODO: Flesh out these stubs:

(defstub f2i (float) t)
(defstub f2d (float) t)
(defstub f2l (float) t)

(defstub i2d (int) t)


(defstub l2d (int) t)
(defstub l2f (int) t)

(defun execute-F2I (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (f2i (top-operand (stack (thread-top-frame th s))))
                               (pop-operand (stack (thread-top-frame th s))))))

(defun execute-F2D (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long (f2d (top-operand (stack (thread-top-frame th s))))
                            (pop-operand (stack (thread-top-frame th s))))))

(defun execute-F2L (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long (f2l (top-operand (stack (thread-top-frame th s))))
                            (pop-operand (stack (thread-top-frame th s))))))

(defun execute-I2F (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-operand (i2f (top-operand (stack (thread-top-frame th s))))
                               (pop-operand (stack (thread-top-frame th s))))))

(defun execute-I2D (th s)
  (modify th s
          :pc (+ 1 ;(inst-length inst)
                 (pc (thread-top-frame th s)))
          :stack (push-long (i2d (top-operand (stack (thread-top-frame th s))))
                            (pop-operand (stack (thread-top-frame th s))))))

(defun execute-L2D (th s)
  (let* ((value (top-long (stack (thread-top-frame th s))))
         (result (l2d value)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-long result
                              (pop-long (stack (thread-top-frame th s)))))))

(defun execute-L2F (th s)
  (let* ((value (top-long (stack (thread-top-frame th s))))
         (result (l2f value)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand result
                                 (pop-long (stack (thread-top-frame th s)))))))

;returns an int (1, 0, or -1 [encoded as a BV]) to indicate the result of the comparison
(defun fcmpg (value1 value2)
  (declare (xargs :guard (and (java-floatp value1)
                              (java-floatp value2))))
  (if (float> value1 value2)
      1
    (if (float= value1 value2)
        0
      (if (float< value1 value2)
          (encode-signed -1)
        ;; at least one value is NaN:
        1))))

;returns an int (1, 0, or -1 [encoded as a BV]) to indicate the result of the comparison
(defun fcmpl (value1 value2)
  (declare (xargs :guard (and (java-floatp value1)
                              (java-floatp value2))))
  (if (float> value1 value2)
      1
    (if (float= value1 value2)
        0
      (if (float< value1 value2)
          (encode-signed -1)
        ;; at least one value is NaN:
        (encode-signed -1)))))

;returns an int (1, 0, or -1 [encoded as a BV]) to indicate the result of the comparison
(defun dcmpg (value1 value2)
  (declare (xargs :guard (and (java-doublep value1)
                              (java-doublep value2))))
  (if (double> value1 value2)
      1
    (if (double= value1 value2)
        0
      (if (double< value1 value2)
          (encode-signed -1)
        ;; at least one value is NaN:
        1))))

;returns an int (1, 0, or -1 [encoded as a BV]) to indicate the result of the comparison
(defun dcmpl (value1 value2)
  (declare (xargs :guard (and (java-doublep value1)
                              (java-doublep value2))))
  (if (double> value1 value2)
      1
    (if (double= value1 value2)
        0
      (if (double< value1 value2)
          (encode-signed -1)
        ;; at least one value is NaN:
        (encode-signed -1)))))

; (FCMPG)
(defun execute-FCMPG (th s)
  (let* ((value2 (top-operand (stack (thread-top-frame th s))))
         (value1 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (result (fcmpg value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand result
                                 (pop-operand (pop-operand (stack (thread-top-frame th s))))))))

; (FCMPL)
(defun execute-FCMPL (th s)
  (let* ((value2 (top-operand (stack (thread-top-frame th s))))
         (value1 (top-operand (pop-operand (stack (thread-top-frame th s)))))
         (result (fcmpl value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand result
                                 (pop-operand (pop-operand (stack (thread-top-frame th s))))))))

; (DCMPG)
(defun execute-DCMPG (th s)
  (let* ((value2 (top-long (stack (thread-top-frame th s))))
         (value1 (top-long (pop-long (stack (thread-top-frame th s)))))
         (result (dcmpg value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand result
                                 (pop-long (pop-long (stack (thread-top-frame th s))))))))

; (DCMPL)
(defun execute-DCMPL (th s)
  (let* ((value2 (top-long (stack (thread-top-frame th s))))
         (value1 (top-long (pop-long (stack (thread-top-frame th s)))))
         (result (dcmpl value1 value2)))
    (modify th s
            :pc (+ 1 ;(inst-length inst)
                   (pc (thread-top-frame th s)))
            :stack (push-operand result
                                 (pop-long (pop-long (stack (thread-top-frame th s))))))))

(defun match-offset-pairsp (pairs)
  (declare (xargs :guard t))
  (if (atom pairs)
      (null pairs)
    (let* ((pair (first pairs)))
      (and (consp pair)
           (let ((match (car pair))
                 (offset (cdr pair)))
             (and (signed-byte-p 32 match)
                  (signed-byte-p 32 offset)
                  (match-offset-pairsp (rest pairs))))))))

;returns nil if not found
(defun lookup-offset-for-match (key pairs)
  (declare (xargs :guard (and (signed-byte-p 32 key)
                              (match-offset-pairsp pairs))))
  (lookup key pairs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (LOOKUPSWITCH <default-value> <match-offset-pairs>)
;todo: test this
(defund execute-LOOKUPSWITCH (inst th s)
  (let* ((default-value (farg1 inst))
         (match-offset-pairs (farg2 inst))
         (key (decode-signed (top-operand (stack (thread-top-frame th s))))) ;todo: think about the decode-signed
         (match (lookup-offset-for-match key match-offset-pairs))
         (offset (if match match default-value))
         (new-pc (+ offset (pc (thread-top-frame th s))))
         )
    (if (not (natp new-pc)) ; todo: strengthen to check that is's a valid PC in this method
        (error-state (list "Bad PC after lookupswitch." new-pc) s)
      (if (not (memberp new-pc (strip-cars (method-program (method-info (thread-top-frame th s))))))
          (error-state (list "Bad PC after lookupswitch." new-pc) s)
        (modify th s
                :pc new-pc
                :stack (pop-operand (stack (thread-top-frame th s))))))))

(defthm jvm-statep-of-execute-lookupswitch
  (implies (and (jvm-statep s)
                (equal inst (current-inst th s))
                (equal (instruction-opcode inst) :lookupswitch)
                (bound-in-alistp th (thread-table s))
                (call-stack-non-emptyp th s)
                (thread-designatorp th))
           (jvm-statep (execute-LOOKUPSWITCH inst th s)))
  :hints (("Goal"
           :in-theory (e/d (execute-LOOKUPSWITCH
                            method-programp-key-property-2-alt ;method-programp-key-property-2-alt-special
                            valid-pcp
                            inst-len)
                           (method-program ;current-inst
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;order the cases, or will we use one rule per opcode instead of opening this up? better to use rules, so this doesn't split into cases when the code is not known
(defund do-inst (op-code inst th s)
  (case op-code
    (:AALOAD         (execute-AALOAD th s))
    (:AASTORE        (execute-AASTORE th s))
    (:ACONST_NULL    (execute-ACONST_NULL th s))
    (:ALOAD          (execute-ALOAD inst th s))
    (:ALOAD_0        (execute-ALOAD_X th s 0))
    (:ALOAD_1        (execute-ALOAD_X th s 1))
    (:ALOAD_2        (execute-ALOAD_X th s 2))
    (:ALOAD_3        (execute-ALOAD_X th s 3))
    (:ANEWARRAY      (execute-ANEWARRAY inst th s))
    (:ARETURN        (execute-ARETURN th s))
    (:ARRAYLENGTH    (execute-ARRAYLENGTH th s))
    (:ASTORE         (execute-ASTORE inst th s))
    (:ASTORE_0       (execute-ASTORE_X th s 0))
    (:ASTORE_1       (execute-ASTORE_X th s 1))
    (:ASTORE_2       (execute-ASTORE_X th s 2))
    (:ASTORE_3       (execute-ASTORE_X th s 3))
    (:ATHROW         (execute-ATHROW th s))
    (:BALOAD         (execute-BALOAD th s))
    (:BASTORE        (execute-BASTORE th s))
    (:BIPUSH         (execute-BIPUSH inst th s))
    (:CALOAD         (execute-CALOAD th s))
    (:CASTORE        (execute-CASTORE th s))
    (:CHECKCAST      (execute-CHECKCAST inst th s)) ;new
    (:D2F            (execute-D2F th s))
    (:D2I            (execute-D2I th s))
    (:D2L            (execute-D2L th s))
    (:DADD           (execute-DADD th s))
    (:DALOAD         (execute-DALOAD th s))
    (:DASTORE        (execute-DASTORE th s))
    (:DCMPG          (execute-DCMPG th s))
    (:DCMPL          (execute-DCMPL th s))
    (:DCONST_0       (execute-DCONST_X 0 th s))
    (:DCONST_1       (execute-DCONST_X 1 th s))
    (:DDIV           (execute-DDIV th s))
    (:DLOAD          (execute-DLOAD inst th s))
    (:DLOAD_0        (execute-DLOAD_X th s 0))
    (:DLOAD_1        (execute-DLOAD_X th s 1))
    (:DLOAD_2        (execute-DLOAD_X th s 2))
    (:DLOAD_3        (execute-DLOAD_X th s 3))
    (:DMUL           (execute-DMUL th s))
    (:DNEG           (execute-DNEG th s))
    (:DREM           (execute-DREM th s))
    (:DRETURN        (execute-DRETURN th s))
    (:DSTORE         (execute-DSTORE inst th s))
    (:DSTORE_0       (execute-DSTORE_X th s 0))
    (:DSTORE_1       (execute-DSTORE_X th s 1))
    (:DSTORE_2       (execute-DSTORE_X th s 2))
    (:DSTORE_3       (execute-DSTORE_X th s 3))
    (:DSUB           (execute-DSUB th s))
    (:DUP            (execute-DUP th s))
    (:DUP_X1         (execute-DUP_X1 th s))
    (:DUP_X2         (execute-DUP_X2 th s))
    (:DUP2           (execute-DUP2 th s))
    (:DUP2_X1        (execute-DUP2_X1 th s))
    (:DUP2_X2        (execute-DUP2_X2 th s))
    (:F2D            (execute-F2D th s))
    (:F2I            (execute-F2I th s))
    (:F2L            (execute-F2L th s))
    (:FADD           (execute-FADD th s))
    (:FALOAD         (execute-FALOAD th s))
    (:FASTORE        (execute-FASTORE th s))
    (:FCMPG          (execute-FCMPG th s))
    (:FCMPL          (execute-FCMPL th s))
    (:FCONST_0       (execute-FCONST_X 0 th s))
    (:FCONST_1       (execute-FCONST_X 1 th s))
    (:FCONST_2       (execute-FCONST_X 2 th s))
    (:FDIV           (execute-FDIV th s))
    (:FLOAD          (execute-FLOAD inst th s))
    (:FLOAD_0        (execute-FLOAD_X th s 0))
    (:FLOAD_1        (execute-FLOAD_X th s 1))
    (:FLOAD_2        (execute-FLOAD_X th s 2))
    (:FLOAD_3        (execute-FLOAD_X th s 3))
    (:FMUL           (execute-FMUL th s))
    (:FNEG           (execute-FNEG th s))
    (:FREM           (execute-FREM th s))
    (:FRETURN        (execute-FRETURN th s))
    (:FSTORE         (execute-FSTORE inst th s))
    (:FSTORE_0       (execute-FSTORE_X th s 0))
    (:FSTORE_1       (execute-FSTORE_X th s 1))
    (:FSTORE_2       (execute-FSTORE_X th s 2))
    (:FSTORE_3       (execute-FSTORE_X th s 3))
    (:FSUB           (execute-FSUB th s))
    (:GETFIELD       (execute-GETFIELD inst th s))
    (:GETSTATIC      (execute-GETSTATIC inst th s))
    (:GOTO           (execute-GOTO inst th s))
    (:GOTO_W         (execute-GOTO_W inst th s))
    (:I2B            (execute-I2B th s))
    (:I2C            (execute-I2C th s))
    (:I2D            (execute-I2D th s))
    (:I2F            (execute-I2F th s))
    (:I2L            (execute-I2L th s))
    (:I2S            (execute-I2S th s))
    (:IADD           (execute-IADD th s))
    (:IALOAD         (execute-IALOAD th s))
    (:IAND           (execute-IAND th s))
    (:IASTORE        (execute-IASTORE th s))
    ;;we pass in the appropiate constant for each instruction:
    (:ICONST_M1      (execute-ICONST_X th s -1)) ;;fixme: make this a BV
    (:ICONST_0       (execute-ICONST_X th s 0))
    (:ICONST_1       (execute-ICONST_X th s 1))
    (:ICONST_2       (execute-ICONST_X th s 2))
    (:ICONST_3       (execute-ICONST_X th s 3))
    (:ICONST_4       (execute-ICONST_X th s 4))
    (:ICONST_5       (execute-ICONST_X th s 5))
    (:IDIV           (execute-IDIV th s))
    (:IF_ACMPEQ      (execute-IF_ACMPEQ inst th s))
    (:IF_ACMPNE      (execute-IF_ACMPNE inst th s))
    (:IF_ICMPEQ      (execute-IF_ICMPEQ inst th s))
    (:IF_ICMPGE      (execute-IF_ICMPGE inst th s))
    (:IF_ICMPGT      (execute-IF_ICMPGT inst th s))
    (:IF_ICMPLE      (execute-IF_ICMPLE inst th s))
    (:IF_ICMPLT      (execute-IF_ICMPLT inst th s))
    (:IF_ICMPNE      (execute-IF_ICMPNE inst th s))
    (:IFEQ           (execute-IFEQ inst th s))
    (:IFGE           (execute-IFGE inst th s))
    (:IFGT           (execute-IFGT inst th s))
    (:IFLE           (execute-IFLE inst th s))
    (:IFLT           (execute-IFLT inst th s))
    (:IFNE           (execute-IFNE inst th s))
    (:IFNONNULL      (execute-IFNONNULL inst th s))
    (:IFNULL         (execute-IFNULL inst th s))
    (:IINC           (execute-IINC inst th s))
    (:ILOAD          (execute-ILOAD inst th s))
    (:ILOAD_0        (execute-ILOAD_X th s 0))
    (:ILOAD_1        (execute-ILOAD_X th s 1))
    (:ILOAD_2        (execute-ILOAD_X th s 2))
    (:ILOAD_3        (execute-ILOAD_X th s 3))
    (:IMUL           (execute-IMUL th s))
    (:INEG           (execute-INEG th s))
    (:INSTANCEOF     (execute-INSTANCEOF inst th s))
    ;; (:INVOKEDYNAMIC (execute-INVOKEDYNAMIC inst th s))
    (:INVOKEINTERFACE (execute-INVOKEINTERFACE inst th s))
    (:INVOKESPECIAL  (execute-INVOKESPECIAL inst th s))
    (:INVOKESTATIC   (execute-INVOKESTATIC inst th s))
    (:INVOKEVIRTUAL  (execute-INVOKEVIRTUAL inst th s))
    (:IOR            (execute-IOR th s))
    (:IREM           (execute-IREM th s))
    (:IRETURN        (execute-IRETURN th s))
    (:ISHL           (execute-ISHL th s))
    (:ISHR           (execute-ISHR th s))
    (:ISTORE         (execute-ISTORE inst th s))
    (:ISTORE_0       (execute-ISTORE_X th s 0))
    (:ISTORE_1       (execute-ISTORE_X th s 1))
    (:ISTORE_2       (execute-ISTORE_X th s 2))
    (:ISTORE_3       (execute-ISTORE_X th s 3))
    (:ISUB           (execute-ISUB th s))
    (:IUSHR          (execute-IUSHR th s))
    (:IXOR           (execute-IXOR th s))
    (:JSR            (execute-JSR inst th s))
    (:JSR_W          (execute-JSR_W inst th s))
    (:L2D            (execute-L2D th s))
    (:L2F            (execute-L2F th s))
    (:L2I            (execute-L2I th s))
    (:LADD           (execute-LADD th s))
    (:LALOAD         (execute-LALOAD th s))
    (:LAND           (execute-LAND th s))
    (:LASTORE        (execute-LASTORE th s))
    (:LCMP           (execute-LCMP th s))
    ;;we pass in the appropriate constant:
    (:LCONST_0       (execute-LCONST_X th s 0))
    (:LCONST_1       (execute-LCONST_X th s 1))
    (:LDC            (execute-LDC inst th s nil))
    (:LDC_W          (execute-LDC inst th s t)) ; no need for a separate function for the wide version
    (:LDC2_W         (execute-LDC2_W inst th s))
    (:LDIV           (execute-LDIV th s))
    (:LLOAD          (execute-LLOAD inst th s))
    (:LLOAD_0        (execute-LLOAD_X th s 0))
    (:LLOAD_1        (execute-LLOAD_X th s 1))
    (:LLOAD_2        (execute-LLOAD_X th s 2))
    (:LLOAD_3        (execute-LLOAD_X th s 3))
    (:LMUL           (execute-LMUL th s))
    (:LNEG           (execute-LNEG th s))
    (:LOOKUPSWITCH   (execute-LOOKUPSWITCH inst th s))
    (:LOR            (execute-LOR th s))
    (:LREM           (execute-LREM th s))
    (:LRETURN        (execute-LRETURN th s))
    (:LSHL           (execute-LSHL th s))
    (:LSHR           (execute-LSHR th s))
    (:LSTORE         (execute-LSTORE inst th s))
    (:LSTORE_0       (execute-LSTORE_X th s 0))
    (:LSTORE_1       (execute-LSTORE_X th s 1))
    (:LSTORE_2       (execute-LSTORE_X th s 2))
    (:LSTORE_3       (execute-LSTORE_X th s 3))
    (:LSUB           (execute-LSUB th s))
    (:LUSHR          (execute-LUSHR th s))
    (:LXOR           (execute-LXOR th s))
    (:MONITORENTER   (execute-MONITORENTER th s))
    (:MONITOREXIT    (execute-MONITOREXIT th s))
    (:MULTIANEWARRAY (execute-MULTIANEWARRAY inst th s))
    (:NEW            (execute-NEW inst th s))
    (:NEWARRAY       (execute-NEWARRAY inst th s))
    (:NOP            (execute-NOP th s))
    (:POP            (execute-POP th s))
    (:POP2           (execute-POP2 th s))
    (:PUTFIELD       (execute-PUTFIELD inst th s))
    (:PUTSTATIC      (execute-PUTSTATIC inst th s))
    (:RET            (execute-RET inst th s))
    (:RETURN         (execute-RETURN th s))
    (:SALOAD         (execute-SALOAD th s))
    (:SASTORE        (execute-SASTORE th s))
    (:SIPUSH         (execute-SIPUSH inst th s))
    (:SWAP           (execute-SWAP th s))
    (:tableswitch    (execute-tableswitch inst th s))
    ;; NOTE: WIDE is transformed away by the class file parser
    (otherwise (error-state (list "error-unknown-opcode" (instruction-opcode inst)) s))
    ))

;TH is a thread designator
;fixme: should ensure that the indicated thread is steppable (e.g., has a stack frame, etc.)
(defund step (th s)
  (declare (xargs :guard (and (thread-designatorp th)
                              (jvm-statep s))
                  :verify-guards nil ;todo add and prove guard
                  ))
  (let ((inst (current-inst th s)))
    (do-inst (instruction-opcode inst) inst th s)))

;SCHED is a list of thread designators
(defund run (sched s)
  (if (endp sched)
      s
    (let ((thread-designator (first sched)))
      (if (bound-in-alistp thread-designator (thread-table s)) ;if the given thread ID is not bound in the thread-table, skip it.
          (if (call-stack-non-emptyp thread-designator s)
              (run (rest sched) (step thread-designator s))
            ;; if the call-stack is empty, we can't step this thread: ; todo: should this be an error?
            (run (rest sched) s))
        (run (rest sched) s)))))

;fixme this should give an error if called on a non-recursive function:
(acl2::defopeners lookup-method-for-invokespecial-aux)

;move
;see also G-IFF-GEN
(defthm in-of-rkeys-when-g
  (implies (and (equal (g a x) free)
                (not (equal free nil)))
           (equal (set::in a (acl2::rkeys x))
                  t)))

;move
(defthm in-of-rkeys-when-g-rev
  (implies (and (equal free (g a x)) ;note that this is a binding hyp
                (not (equal free nil)))
           (equal (set::in a (acl2::rkeys x))
                  t)))

;fixme more like this
(defthm statep-consequence-1
  (implies (and (member-equal class-name *built-in-exception-classes*)
                (jvm-statep s))
           (bound-to-a-non-interfacep class-name (CLASS-TABLE S)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable jvm-statep class-tablep class-table acl2::memberp-of-cons-when-constant))))

(defthm string-has-been-internedp-of-myif
  (equal (string-has-been-internedp string (myif test tp ep))
         (myif test
               (string-has-been-internedp string tp)
               (string-has-been-internedp string ep)))
  :hints (("Goal" :in-theory (enable myif))))



;mentioned in the macro-expansion of prog2$
;TODO: Just enable return-last?
;move
;; ;; Is this still needed?  Note that remove-guard-holders may handle this
;; (defthm acl2::return-last-rewrite
;;   (equal (acl2::return-last fn eager-arg last-arg)
;;          last-arg)
;;   :rule-classes nil
;;   :hints (("Goal" :in-theory (enable return-last))))




(defthm operand-stack-size-bound
  (implies (and (syntaxp (quotep k1))
                (syntaxp (quotep k2))
                (<= k2 k1))
           (not (< (+ k1 (operand-stack-size stack))
                   k2))))

;;TODO: To initialize the JVM state: build all class objects, intern all strings mentioned in all classes/interfaces



;; Safer than opening step because the if can cause problems if unresolved (the
;; run-xxx may distribute over the if, causing a loop).
(defthm step-opener
  (equal (step th s)
         (let ((inst (current-inst th s)))
           (do-inst (instruction-opcode inst)
                    inst th s)))
  :hints (("Goal" :in-theory (enable step))))

(acl2::defopeners pop-items-off-stack-aux)
