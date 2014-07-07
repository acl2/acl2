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

