; ACL2 Standard Library
; Copyright (C) 2008-2016 Centaur Technology
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

(in-package "STOBJS")
(include-book "std/util/bstar" :dir :system)

(defxdoc defabsstobj-events
  :parents (std/stobjs defabsstobj)
  :short "Alternative to @(see defabsstobj) that tries to prove the necessary
  correspondence and preservation theorems instead of making you prove them
  ahead of time."

  :long "<p>This is essentially a drop-in replacement for @(see defabsstobj)
  that.  Instead of requiring you to copy/paste the preservation/correspondence
  theorems and prove them ahead of time, it just tries to go ahead and prove
  them before submitting the @('defabsstobj') form.</p>

  <p>This can often eliminate a lot of tedious copy/paste updating.  It is also
  useful in macros that generate abstract stobjs, such as @(see def-1d-arr) and
  similar.</p>

  <p>The syntax is like that of @(see defabsstobj), e.g.,:</p>

  @({
      (defabsstobj-events st
        :foundation st$c
        :recognizer (stp :logic st$ap :exec st$cp)
        :creator (create-st :logic create-st$a :exec create-st$c)
        :corr-fn st$corr
        :exports ((foo :logic foo$a :exec foo$c)
                  ...
                  (baz :exec baz$a :exec baz$c)))
  })

  <p>The macro operates very simply:</p>

  <ol>
   <li>Use @(see defabsstobj-missing-events) to generate the necessary theorems, then</li>
   <li>Try to submit these events to ACL2 via a @(see make-event), then finally</li>
   <li>Submit the @(see defabsstobj) form.</li>
  </ol>

  <p>The theorems submitted in Step 2 are just attempted in your current theory
  and with no hints.  If some theorem can't be proven, the easiest thing to do
  is extract it (copy and paste it) above your defabsstobj-events form so that
  you can give it hints.  For instance:</p>

  @({
      (encapsulate ()
       (local (defthm foo{correspondence}  ;; presumably need hints
                ...
                :hints (...)))
       (defabsstobj-events st ...))
  })")

(defun untrans-defabsstobj-missing-defthms (forms state)
  (declare (xargs :mode :program :stobjs state))
  (if (atom forms)
      nil
    (cons `(defthm ,(caar forms)
             ,(acl2::untranslate (cadar forms) t (w state))
             :rule-classes nil)
          (untrans-defabsstobj-missing-defthms (cdr forms) state))))

(defmacro defabsstobj-events (&rest args)
  `(progn
     (local
      (make-event
       (acl2::er-let*
        ((events (defabsstobj-missing-events . ,args)))
        (let ((thms (untrans-defabsstobj-missing-defthms events state)))
          (value (cons 'progn thms))))))
     (defabsstobj . ,args)))


