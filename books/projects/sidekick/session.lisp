; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "SIDEKICK")
(include-book "io")
(include-book "std/strings/pretty" :dir :system)
(include-book "webcommand")
(set-state-ok t)
(program)

(defmacro session ()
  (push-webcommand (list (cons :action :session))))

; Notes about the ACL2 world.

; Logical names are the names of functions, macros, theorems, packages, etc.
;
; One can map from a logical names to the world when the name was introduced.
; After each event is processed its 'event-landmark gets set to an event-tuple
; that records information about the event.
;
; ACL2 associates an ABSOLUTE EVENT NUMBER with each event.  This is a natural
; that can be used for fast lookups.
;
; ACL2 maintains fancy structures called "Zap Tables" to be able to quickly
; look up the world corresponding to an event/command number without a lot of
; overhead.  These tables are automatically extended as new events are added;
; they live in world globals called EVENT-INDEX and COMMAND-INDEX.
;
; Q: Are world globals thread-safe?
;
; A: Maybe but probably not?  They are ostensibly applicative.  However,
; global-val is implemented using getprop, which calls fgetprop.  Fgetprop
; probably isn't thread-safe since it's looking directly at property list
; stuff?  So I'm not sure.
;
; Aside from the updating code, which we probably don't care much of anything
; about, it looks like the main function is LOOKUP-WORLD-INDEX, which can use
; these fancy structures to look up arbitrary commands and events by index.
; The interface is pretty simple for an example.
;
; Command tuples.
;  Gets installed as the global value for 'command-landmark.
;  Divide the world into command blocks.
;     Each command block has one or more event blocks.
;  Have "absolute command numbers," enumerated from 0, for things like
;  undoing.
;
;  (make command-tuple
;        :number n
;        :defun-mode/form (if (eq defun-mode :program)
;                             form
;                           (cons defun-mode form))
;        :cbd cbd
;        :last-make-event-expansion last-make-event-expansion))
;
; access-command-tuple-form, access-command-tuple-defun-mode, access-command-tuple-number,
; etc.
;
; (max-absolute-command-number wrld)
;
;  (scan-to-command wrld) -> prev-wrld
;    go backwards to the most recent binding of command-landmark.
;    returns the world as of the last command
;
;  (scan-to-landmark-number 'command-landmark n wrld) --> wrld
;    go backwards for a particular command number.
;    causes a hard error if not found.
;    probably slow because it doesn't use the zap table.
;
;  (lookup-world-index 'command n wrld) --> world
;
;     higher level version of scan-to-landmark-number, which i guess
;     does some fixup on the number?  ah, but this one is more optimized
;     because it uses the zap table.

; --- pages and pages of irrelevant shit ---
;
; landmark descriptor (LMD) -- decodes into (command-landmark . n) or
; (event-landmark . n) and then gets looked up using lookup-world-index.
;
; These are for the user-visible numbers like 0, 1, 2, etc.; they differ from
; the absolute event numbers.  LMD numbers can be negative when they occur in
; the prehistory.
;
;  absolute-to-relative-command-number (n wrld)
;  relative-to-absolute-command-number (n wrld)
;
; Command Descriptors -- indicate landmarks
;   :min, :start, :max, n, name, search? wtf, gods this is elaborate

; Displaying events and commands.
;
;   Phase 1: collect up LDDs that we're going to print
;   Phase 2: print them.
;
;






;; (defconst *jalist-from-ldd-evisc-tuple*
;;   (evisc-tuple 5 5
;;                (list (cons *evisceration-ellipsis-mark* "..."))
;;                nil))

(defconst *json-pbt-printconfig*
  (str::make-printconfig :print-lowercase t))

(define jalist-from-ldd (ldd state)
  ;; Based on reading the code for print-ldd and supporting stuff.
  ;; I have no idea what I'm doing.
  (b* ((status          (acl2::access-ldd-status ldd))
       (defun-mode-pair (access ldd-status status :defun-mode-pair))
       (disabled        (access ldd-status status :disabled))
       (memoized        (access ldd-status status :memoized))
       ((mv eviscerated state)
        ;; Blah, as of d05dea5b0522d51d0e7f9a5889c0fb7740a327d7,
        ;; print-ldd-full-or-sketch now modifies state... it doesn't
        ;; really seem like it should have to...
        (acl2::print-ldd-full-or-sketch (acl2::access-ldd-fullp ldd)
                                        (acl2::access-ldd-form ldd)
                                        state))
       (form-str (str::pretty eviscerated
                              :config *json-pbt-printconfig*
                              :eviscp t))
       (alist (list
               ;; command or event
               (cons :class (acl2::access-ldd-class ldd))
               ;; symbol class char, indicating program/ideal/verified
               (cons :orig-symbol-class (car defun-mode-pair))
               (cons :current-symbol-class (cdr defun-mode-pair))
               (cons :disabled disabled)
               (cons :memoized memoized)
               ;; don't think we care about the "mark" thing
               (cons :markp  (acl2::access-ldd-markp ldd))
               (cons :n (acl2::access-ldd-n ldd))
               (cons :most-recent
                     (and (eq (acl2::access-ldd-class ldd) 'acl2::command)
                          (eql (acl2::access-ldd-n ldd)
                               (acl2::absolute-to-relative-command-number
                                (acl2::max-absolute-command-number (w state))
                                (w state)))))
               (cons :form form-str))))
    (mv alist state)))

(define jalists-from-ldds (ldds state)
  :returns (mv jalists state)
  (b* (((when (atom ldds))
        (mv nil state))
       ((mv car state)
        (jalist-from-ldd (car ldds) state))
       ((mv cdr state)
        (jalists-from-ldds (cdr ldds) state)))
    (mv (cons car cdr) state)))

(defun json-pcs-fn (cd1 cd2 markp state)
  ;; Based on pcs-fn.  I have no idea what I'm doing.
  (let ((wrld (w state))
        (ens (ens state)))
    (er-let* ((cmd-wrld1 (er-decode-cd cd1 wrld :ps state))
              (cmd-wrld2 (er-decode-cd cd2 wrld :ps state)))
             (b* ((later-wrld
                   (if (>= (access-command-tuple-number (cddar cmd-wrld1))
                           (access-command-tuple-number (cddar cmd-wrld2)))
                       cmd-wrld1
                     cmd-wrld2))
                  (earlier-wrld
                   (if (>= (access-command-tuple-number (cddar cmd-wrld1))
                           (access-command-tuple-number (cddar cmd-wrld2)))
                       cmd-wrld2
                     cmd-wrld1))
                  (ldds (make-ldds-command-sequence later-wrld
                                                    (cddar earlier-wrld)
                                                    ens
                                                    wrld
                                                    markp
                                                    nil))
                  ((mv alists state) (jalists-from-ldds ldds state)))
               (mv nil alists state)))))

(defmacro json-pbt (cd1)
  ;; Based on PBT.  I have no idea what I'm doing.
  (list 'json-pcs-fn cd1 :x nil 'state))

; (json-pbt 0)


(defun json-pcb-pcb!-fn (cd fullp state)
  ;; Based on pcb-pcb!-fn.  I have no idea what I'm doing.
  (let ((wrld (w state))
        (ens (ens state)))
    (er-let* ((cmd-wrld (er-decode-cd cd wrld :pcb state)))
             (b* ((ldds   (acl2::make-ldds-command-block cmd-wrld ens wrld fullp nil))
                  ((mv alists state)
                   (jalists-from-ldds ldds state)))
               (mv nil alists state)))))

(defun json-pcb!-fn (cd fullp state)
  (json-pcb-pcb!-fn cd fullp state))

(defmacro json-pcb! (cd fullp)
  (list 'json-pcb!-fn cd fullp 'state))



; (json-pcb! 8 t)


(defun json-pc-fn (cd state)
  (let ((wrld (w state)))
    (er-let* ((cmd-wrld  (er-decode-cd cd wrld :pc state)))
             (b* ((ldd (acl2::make-command-ldd nil t cmd-wrld (ens state) wrld))
                  ((mv alist state)
                   (jalist-from-ldd ldd state)))
               (mv nil alist state)))))

(defmacro json-pc (cd)
  (list 'json-pc-fn cd 'state))


(define sk-undo-back-through ((num stringp) state)
  :returns (mv json-eventdata state)
  :mode :program
  (b* ((n (str::strval num))
       ((unless n)
        (mv (sk-json-error "Error in sk-undo-back-through: not a number: ~a" num)
            state))
       ;; This should be fixed now
       ;; #+hons
       ;; ((when t)
       ;;  (mv (sk-json-error "Sorry, undo doesn't work on ACL2(h) because memoization isn't ~
       ;;                      thread safe.")
       ;;      state))
       ((mv erp ?val state) (acl2::ubt!-ubu!-fn :ubt n state))
       ((when erp)
        (mv (sk-json-error "ubt!-ubu!-fn returned an error.")
            state))
       (ans (bridge::json-encode (list (cons :error nil)))))
    (mv ans state)))




;; ; Now I want something like :pcb!

;; (progn
;;   (program)
;;   (set-state-ok t)
;;   (defun my-make-ldds-command-block1 (wrld1 cmd-ldd indent fullp super-stk ens wrld ans)
;;     (progn$
;;      (cw "---------------~%")
;;      (cw "--- caar wrld1 is ~x0.~%" (caar wrld1))
;;      (cw "super-stk ~x0.~%" super-stk)
;;      (cw "ans is ~x0.~%" ans)
;;      (cond
;;       ((or (null wrld1)
;;            (and (eq (caar wrld1) 'command-landmark)
;;                 (eq (cadar wrld1) 'global-value)))
;;        (cond
;;         (super-stk
;;          (b* ((new-ldd (make-event-ldd nil (1- indent) fullp (car super-stk) ens wrld)))
;;            (cw "case 1 - New ldd: ~x0.~%" new-ldd)
;;            (my-make-ldds-command-block1 wrld1 cmd-ldd (1- indent) fullp
;;                                         (cdr super-stk) ens wrld
;;                                         (list (list :pop
;;                                                     :open (car super-stk)
;;                                                     :new-ldd new-ldd
;;                                                     :sub-events ans)))))
;;         (t
;;          (cons (list :single cmd-ldd) ans))))
;;       ((and (eq (caar wrld1) 'event-landmark)
;;             (eq (cadar wrld1) 'global-value))
;;        (cond
;;         ((and super-stk
;;               (<= (access-event-tuple-depth (cddar wrld1))
;;                   (access-event-tuple-depth (car super-stk))))
;;          (b* ((new-ldd (make-event-ldd nil (1- indent) fullp (car super-stk) ens wrld)))
;;            (cw "case 2 - New ldd: ~x0.~%" new-ldd)
;;            (my-make-ldds-command-block1 wrld1 cmd-ldd (1- indent) fullp
;;                                         (cdr super-stk)
;;                                         ens wrld
;;                                         (list (list :pop2
;;                                                     :open (car super-stk)
;;                                                     :new-ldd new-ldd
;;                                                     :sub-events ans)))))
;;         ((or (eq (access-event-tuple-type (cddar wrld1)) 'encapsulate)
;;              (eq (access-event-tuple-type (cddar wrld1)) 'include-book))
;;          (progn$
;;           (cw "case 3 - encap/include: extending super-stk with ~x0.~%" (cddar wrld1))
;;           (my-make-ldds-command-block1 (cdr wrld1) cmd-ldd (1+ indent) fullp
;;                                        (cons (cddar wrld1) super-stk)
;;                                        ens wrld ans)))
;;         (t
;;          (b* ((new-ldd (make-event-ldd nil indent fullp (cddar wrld1) ens wrld)))
;;            (cw "case 4 -- adding new ldd ~x0.~%" new-ldd)
;;            (my-make-ldds-command-block1 (cdr wrld1) cmd-ldd indent fullp
;;                                         super-stk ens wrld
;;                                         (cons new-ldd ans))))))
;;       (t
;;        (progn$
;;         (cw "last case, just skipping this part of the world i guess~%")
;;         (my-make-ldds-command-block1 (cdr wrld1) cmd-ldd indent fullp
;;                                      super-stk ens wrld ans)))))))

;; (defun my-make-ldds-command-block (cmd-wrld ens wrld fullp ans)

;; ; Cmd-wrld is a world starting with a command landmark.  We make a list of ldds
;; ; to describe the entire command block, sketching the command and sketching
;; ; each of the events contained within the block.

;;   (b* ((cmd-ldd (make-command-ldd nil fullp cmd-wrld ens wrld))
;;        (- (cw "Using cmd-ldd ~x0.~%" cmd-ldd))
;;        (wrld1 (scan-to-event (cdr cmd-wrld))))
;;     (cond
;;      ((equal (access-event-tuple-form (cddar wrld1))
;;              (access-command-tuple-form (cddar cmd-wrld)))

;; ; If the command form is the same as the event form of the
;; ; chronologically last event then that event is to be skipped.

;;       (my-make-ldds-command-block1 (cdr wrld1) cmd-ldd 1 fullp nil ens wrld ans))
;;      (t (my-make-ldds-command-block1 wrld1 cmd-ldd 1 fullp nil ens wrld ans)))))


;; (logic)
;; (defsection nesting-test
;;   (defun n1 (x) x)
;;   (defsection n23
;;     (defun n2 (x) x)
;;     (defun n3 (x) x))
;;   (encapsulate ()
;;     (defun n4 (x) x))
;;   (defsection n56
;;     (defsection n5
;;       (defun n5 (x) x))
;;     (defsection n6
;;       (defun n6 (x) x))))



