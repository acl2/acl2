; Outer-local.lisp
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")


(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)

;; Maybe this should be in std instead?  And if successful, maybe integrated
;; into defsection and define.
(defxdoc outer-local
  :parents (macro-libraries) ;; bozo maybe another level of hierarchy
  :short "Support for events that are local to the outer context."
  :long "<p>Think of @('outer-local') as being like @('progn'), except that the
events inside it are local to some encapsulate context above in which they are
sitting.  Outer-local only works when paired with @('with-outer-locals'), which
is essentially like @('(encapsulate nil ...)') except that it allows
@('outer-local') events to work.</p>

<p>Example:</p>
@({
 (with-outer-locals
   (defun exported-fn ...)
   (local (defthm lemma ...))
   (defthm exported-thm ...)
   (outer-local :depth 1 (defthm book-thm ...)))
})
<p>produces, essentially:</p>
@({
 (local
  (encapsulate nil
    (defun exported-fn ...)
    (local (defthm lemma ...))
    (defthm exported-thm ...)
    (defthm book-thm ...)))
 (defun exported-fn ...)
 (defthm exported-thm ...))
})

<p>Effectively, the event marked @('outer-local') is visible in book or
encapsulate surrounding this with-outer-locals event, but local to that
context.</p>

<p>The @(':depth') argument to @('outer-local') is optional but must occur
first if it is present.  It takes a positive integer, defaulting to 1.  There
must be @('depth') nestings of @('with-outer-locals') surrounding each
outer-local invocation in order for it to work as intended; in that case, the
events inside the outer-local are local to the context @('depth') levels
outside it.</p>

<p>Note: IN-THEORY events inside outer-local probably won't act as you would
like them to, at least in the presence of nonlocal IN-THEORY events.</p>")


;; The payload of each of these is the :push or :pop rather than the :no-op,
;; which is just there to make sure the :push or :pop is not redundant.
(defmacro outer-local-push (&key (level '1))
  `(progn (table outer-local-event-table :action :no-op)
          (table outer-local-event-table :action '(:push . ,level))
          (value-triple :invisible)))

(defmacro outer-local-pop ()
  '(progn (table outer-local-event-table :action :no-op)
          (table outer-local-event-table :action :pop)
          (value-triple :invisible)))

(defmacro outer-local (&rest args)
  (b* (((mv level events)
        (if (eq (car args) :level)
            (if (or (atom (cdr args))
                    (not (posp (cadr args))))
                (progn$
                 (er hard? 'outer-local
                     ":level must be provided a positive integer argument")
                 (mv nil nil))
              (mv (cadr args) (cddr args)))
          (if (member :level args)
              (progn$
               (er hard? 'outer-local
                   ":level must occur first in an outer-local form, if given")
               (mv nil nil))
            (mv 1 args)))))
    `(with-output :off :all :stack :push
       (progn
         (outer-local-push :level ,level)
         (with-output :stack :pop (progn . ,events))
         (outer-local-pop)))))


(defun with-outer-local-collect-events
  ;; Scan through the world to collect the events to replay for with-outer-locals.
  (world ;; scanning through
   context-depth ;; natural; base depth of events we're scanning
   event-stack-top ;; event list that we're currently collecting
   event-stack ;; nestings of outer-local contexts
   )
  (declare (xargs :mode :program))
  (b* (((when (atom world))
        (er hard? 'with-outer-local "Reached end of world while scanning"))
       ((unless (eq (caar world) 'event-landmark))
        ;; skip
        (with-outer-local-collect-events (cdr world) context-depth event-stack-top event-stack))
       (event-tuple (cddr (car world)))
       (event-depth (access-event-tuple-depth event-tuple))
       ;; (- (cw "depth: ~x0 event: ~x1~%" event-depth (access-event-tuple-form event-tuple)))
       ((when (<= event-depth context-depth))
        ;; Reached the previous event, so we're done.
        (b* (((when (consp event-stack))
              ;; Haven't popped off all the outer-local contexts -- error.
              (er hard? 'with-outer-local
                  "Found the previous event while still in an outer-local context")))
          event-stack-top))
       ((unless (eql event-depth (+ 1 context-depth)))
        ;; Skip this event since we've already captured it as part of a
        ;; (+ 1 context-depth) event.
        (with-outer-local-collect-events (cdr world) context-depth event-stack-top event-stack))

       (form (access-event-tuple-form event-tuple))
       ((unless (and (eq (first form) 'table)
                     (eq (second form) 'outer-local-event-table)
                     (eq (third form) :action)))
        ;; Just a regular form; cons it onto the collected events
        (with-outer-local-collect-events
          (cdr world) context-depth (cons form event-stack-top) event-stack))
       ((when (eq (fourth form) :no-op))
        ;; Skip
        (with-outer-local-collect-events
          (cdr world) context-depth event-stack-top event-stack))
       ((when (eq (fourth form) :pop))
        ;; Popping the outer-local context means we push a new frame of the
        ;; event-stack, since we're doing everything in reverse.
        (with-outer-local-collect-events
          (cdr world) context-depth nil (cons event-stack-top event-stack)))
       ((unless (and (consp (fourth form))
                     (eq (car (fourth form)) 'quote)
                     (eq (car (cadr (fourth form))) ':push)
                     (posp (cdr (cadr (fourth form))))))
        (er hard? 'with-outer-local "bad outer-local-event-table form: ~x0" form))
       ;; Push.  This means the top-of-stack events are in an outer-local
       ;; context.  If they're in level 1, we just throw them away.  If in a
       ;; higher level, then we put them in an outer-local context of the
       ;; previous level.
       ((unless (consp event-stack))
        (er hard? 'with-outer-local
            "event stack was empty when we reached an outer-local-push event"))
       (level (cdr (cadr (fourth form))))
       ((when (eql level 1))
        ;; just throw away the top-of-stack events and pop the stack
        (with-outer-local-collect-events
          (cdr world) context-depth (car event-stack) (cdr event-stack))))
    (with-outer-local-collect-events
      (cdr world) context-depth
      (cons `(outer-local :level ,(1- level) . ,event-stack-top)
            (car event-stack))
      (cdr event-stack))))

(defun with-outer-local-events (world)
  (declare (xargs :mode :program))
  (b* ((world (scan-to-event world))
       (tuple (cddr (car world)))
       (context-depth (access-event-tuple-depth tuple)))
    ;; (cw "context depth: ~x0~%" context-depth)
    (cons 'progn
          (with-outer-local-collect-events
            (cdr world) context-depth nil nil))))

(defmacro finish-with-outer-local ()
  `(make-event (with-outer-local-events (w state))))

(defmacro with-outer-locals (&rest events)
  `(with-output :off :all :stack :push
     (progn
       (local
        (with-output :stack :pop
          (encapsulate nil . ,events)))
       (finish-with-outer-local))))






