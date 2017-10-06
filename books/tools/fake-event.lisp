; fake-event.lisp
; Copyright (C) 2011 Centaur Technology
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

(defxdoc fake-event
  :parents (events)
  :short "Execute an event form without affecting the world."
  :long "<p>Usage:</p>

@({
    (fake-event <form>)
})

<p>where @('<form>') evaluates to an event form.  This causes that event form
to be run, but without affecting the logical world.  Fake-event returns the
same error-triple that the event form produced.  The logical world resulting
from that event's success or failure is saved in the state global
fake-event-saved-world.</p>

<p>Fake-event is a bit like @(see make-event), in that both are macros that
evaluate a form to obtain an event, then run that event. Actually, fake-event
doesn't evaluate the form itself (it macroexpands to a call in which the form
is not quoted, so that it is evaluated before fake-event-fn operates upon it.)
It then calls the resulting event using a make-event inside an LD.</p>

<p>Unlike make-event, fake-event can only take a form that evaluates to a
single value, not an error triple.  But fake-event-er is a simple wrapper for
fake-event that supports an error-triple-valued form.</p>

<p>If the event produces a hard error, then fake-event will also produce a hard
error unless the keyword argument :hard-error-ok t is given.  If :hard-error-ok
is set, fake-event returns @('(mv :fake-event-ld-error nil state)').</p>")

(defun fake-event-fn (event hard-error-ok state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (erp val state)
    (ld `((with-output
           :off :all :stack :push
           (make-event
            (mv-let (err-val return-val state)
              (with-output :stack :pop ,event)
              (er-progn
               (assign fake-event-error-val err-val)
               (assign fake-event-return-value return-val)
               (assign fake-event-saved-world (w state))
               (value '(value-triple nil)))))))
        :ld-prompt nil
        :ld-verbose nil
        :ld-error-action :error
        :ld-post-eval-print nil
        :ld-pre-eval-print nil
        :ld-user-stobjs-modified-warning

; Matt K. mod: ACL2 now requires keyword :ld-user-stobjs-modified-warning in
; code.  If this macro is only to be evaluated at the top level, that keyword
; isn't needed.  But I'm including it, with value :same to preserve existing
; behavior, just in case someone uses it in code.  Perhaps more thought should
; be given to whether or not we want a warning here when a user stobj is
; modified.

        :same)
    (declare (ignore val))
    (if erp
        (if hard-error-ok
            (mv :fake-event-ld-error nil state)
          (value (er hard 'fake-event-fn "LD returned error: ~x0~%" erp)))
      (mv (@ fake-event-error-val)
          (@ fake-event-return-value)
          state))))

(defmacro fake-event (event &key hard-error-ok)
  `(fake-event-fn ,event ,hard-error-ok state))

(defmacro fake-event-er (event &key hard-error-ok)
  `(er-let*
    ((event ,event))
    (fake-event event :hard-error-ok ,hard-error-ok)))

(local
 (progn
   (defun test-fake-event (n state)
     (declare (xargs :mode :program :stobjs state))
     (if (zp n)
         (mv 0 state)
       (mv-let (rand state) (random$ 10 state)
         (mv-let (erp val state)
           (fake-event `(with-output
                         :off :all
                         (make-event
                          '(defthm foo (member ,rand '(0 1 5 7))
                             :rule-classes nil))))
           (declare (ignore val))
           (mv-let (rest state)
             (test-fake-event (1- n) state)
             (mv (+ rest (if erp 0 1)) state))))))

   (make-event (mv-let (n state) (test-fake-event 20 state)
                 (if (> n 10)
                     (value '(value-triple :more))
                   (value '(value-triple :less)))))))
