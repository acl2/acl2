; fake-event.lisp
; Copyright (C) 2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

;; See documentation under (defmacro fake-event ...)

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
        :ld-pre-eval-print nil)
    (declare (ignore val))
    (if erp
        (if hard-error-ok
            (mv :fake-event-ld-error nil state)
          (value (er hard 'fake-event-fn "LD returned error: ~x0~%" erp)))
      (mv (@ fake-event-error-val)
          (@ fake-event-return-value)
          state))))

(defmacro fake-event (event &key hard-error-ok)
  ":doc-section Programming
Execute an event form without affecting the world.~/

Usage:
~bv[]
 (fake-event <form>)
~ev[]
where ~c[<form>] evaluates to an event form.  This causes that event form to be
run, but without affecting the logical world.  Fake-event returns the same
error-triple that the event form produced.  The logical world resulting from
that event's success or failure is saved in the state global
fake-event-saved-world.~/

Fake-event is a bit like make-event, in that both are macros that evaluate a
form to obtain an event, then run that event. Actually, fake-event doesn't
evaluate the form itself (it macroexpands to a call in which the form is not
quoted, so that it is evaluated before fake-event-fn operates upon it.)  It
then calls the resulting event using a make-event inside an LD.

Unlike make-event, fake-event can only take a form that evaluates to a single
value, not an error triple.  But fake-event-er is a simple wrapper for
fake-event that supports an error-triple-valued form.

If the event produces a hard error, then fake-event will also produce a hard
error unless the keyword argument :hard-error-ok t is given.  If :hard-error-ok
is set, fake-event returns ~c[(mv :fake-event-ld-error nil state)]."
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
