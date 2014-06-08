; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;   Kookamara LLC
;   11410 Windermere Meadows, Austin TX, 78759, USA.
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "SIDEKICK")
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "lock")
(defttag :sidekick)

(defsection sidekick-state
  :parents (sidekick)
  :short "The global state of the sidekick, locking considerations, and
functions for manipulating the state."

  :long "<p>If you look at the sidekick as an <a
 href='https://en.wikipedia.org/wiki/Model%E2%80%93view%E2%80%93controller'>MVC</a>
 application, this is essentially the model.</p>

<p>The model will typically be updated by two sides:</p>

<ul>
<li>The user, via the web interface</li>
<li>The sidekick hint, as it notices new subgoals and generates advice.</li>
</ul>

<p>Because of this, access to the model should generally be protected; see
@(see with-sidekick-lock).</p>

<p>The model itself is represented as a @(see wstate-p) structure, which has
the advice we've generated and also an unprincipled amalgamation of whatever
settings we want to be able to control from the web interface.</p>")

(local (xdoc::set-default-parents sidekick-state))

(defaggregate wframe
  :short "Sidekickly advice for a single subgoal."
  :tag :wframe
  ((name     "Name of the subgoal we were trying to prove."
             stringp
             :rule-classes :type-prescription)
   (subgoal  "The actual subgoal we were trying to prove.  (BOZO Untranslated?)")
   (advice   "The list of advice we have to recommend... bozo how to represent this?")
   ))

(deflist wframelist-p (x)
  (wframe-p x))

(defaggregate wstate
  :short "The application state of the sidekick."

  ((frames wframelist-p
           "Main part of the state.  This has the advice we've generated for
            whatever subgoals we've encountered, so far.")

   ;; Other switches and so forth.
   (random-p booleanp
             :rule-classes :type-prescription
             :default t
             "Should random testing be enabled (for instance).")))

(defval *initial-wstate*
  :short "Startup state for the sidekick."
  (make-wstate))


(define wget-raw ()
  :short "(Completely unsound).  Get the current, global sidekick state."
  :returns (wstate wstate-p)
  :long "<p>Logically this just returns the @(see *initial-wstate*), so we know
it is a @(see wstate-p).  Under the hood, this returns whatever our current
state is.  See also @(see wset-raw).</p>

<p>This is obviously completely unsound.</p>

<p>We could probably make up a reasonable logical story about this, e.g., it's
an oracle read or similar.  But we don't really care about soundness in the
sidekick code itself (because the whole sidekick is just a debugging aide) and
making this sound would make things more complicated, e.g., we'd need to be
modifying @(see state) or some @(see stobj) or something while the sidekick
analyzes subgoals during a computed hint, and that just seems messy.</p>

<p>We do try to at least disable @('wget') and its executable counterpart and
hide it from the @(see tau-system), which may practically help to prevent ACL2
from accidentally using this.  But it would be trivial to intentionally exploit
this to prove @('nil').</p>"

  :prepwork ((set-tau-auto-mode nil))

  (progn$
   (er hard? 'wget "Under the hood definition not installed?")
   *initial-wstate*)

  ///
  ;; To at least make this less unsound, try to prevent wget from being
  ;; used for much of anything
  (in-theory (disable (:executable-counterpart wget-raw)
                      (:type-prescription wget-raw)
                      (:definition wget-raw)))

  (set-tau-auto-mode t))

(define wset-raw (wstate)
  :short "(Low level).  Replace the global sidekick state with a new state."
  :returns (nil)
  :long "<p>Logically this does nothing, but under the hood it updates the
sidekick state; see also @(see wget).</p>

<p>You should typically not use this directly.  Instead, use higher level
operations like @(see wiz-push-frame).  See also @(see with-sidekick-lock).</p>"
  (declare (ignore wstate))
  (er hard? 'wset-raw "Under the hood definition not installed?"))

(progn!
 (set-raw-mode t)

 (defvar *sidekick-state*
   *initial-wstate*)

 (defun wget-raw ()
   (with-sidekick-lock *sidekick-state*))

 (defun wset-raw (wstate)
   (with-sidekick-lock (setf *sidekick-state* wstate))
   nil))


(define wiz-push-frame ((frame wframe-p))
  :short "Safely add a new advice frame."
  :returns (nil)
  (with-sidekick-lock
   (b* ((st (wget-raw))
        (st (change-wstate st :frames (cons frame (wstate->frames st)))))
     (wset-raw st))))

#||
(wget-raw)
(wiz-push-frame (make-wframe :name "Blah"))
(wget-raw)
(wiz-push-frame (make-wframe :name "Bloop"))
(wget-raw)
||#

(define wiz-clear-frames ()
  :short "Throw away all current advice frames."
  :returns (nil)
  (with-sidekick-lock
   (b* ((st (wget-raw))
        (st (change-wstate st :frames nil)))
     (wset-raw st))))

#||
(wiz-clear-frames)
||#


;; and so on -- add accessors/mutators for whatever other fields we need...

