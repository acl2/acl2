; OSLIB -- Operating System Utilities
; Copyright (C) 2013-2014 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "OSLIB")
(include-book "catpath")
(include-book "getpid-logic")
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/cat" :dir :system)

(local (in-theory (disable w)))

(defsection tempfile
  :parents (oslib)
  :short "Generate a suitable name for a temporary file."

  :long "<p>Signature: @(call tempfile) &rarr; @('(mv filename/nil
state)').</p>

<p>Example:</p>

@({
 (tempfile \"foo\") --> (\"/tmp/jared-31721-foo\" <state>)
})

<p>Note: this function is attachable.  If you need to generate temporary file
names using some other scheme, you can define your own strategy and attach it
to @('tempfile-fn'); see @(see defattach).</p>

<p>The intent is that this function should produce a good @('filename') to use
for the name of a temporary file.  To allow @('tempfile') implementations to
fail for whatever reason, @('filename') may be @('nil').</p>

@(def tempfile)
@(def tempfile-fn)"

  (defmacro tempfile (basename &optional (state 'state))
    `(tempfile-fn ,basename ,state))

  (encapsulate
    (((tempfile-fn * state) => (mv * state)
      :formals (basename state)
      :guard (stringp basename)))

    (local (defun tempfile-fn (basename state)
             (declare (xargs :stobjs state)
                      (ignore basename))
             (mv "" state)))

    (defthm type-of-tempfile-fn
      ;; Tempfile-fn can fail, for whatever reason, by producing NIL.
      (or (stringp (mv-nth 0 (tempfile-fn basename state)))
          (not (mv-nth 0 (tempfile-fn basename state))))
      :rule-classes :type-prescription)

    (defthm state-p1-of-tempfile-fn
      (implies (force (state-p1 state))
               (state-p1 (mv-nth 1 (tempfile-fn basename state)))))

    (defthm w-state-of-tempfile-fn
      (equal (w (mv-nth 1 (tempfile-fn basename state)))
             (w state)))))



(define default-tempfile-aux
  ((tempdir stringp "Directory to generate the file in")
   (basename stringp "Base name to use for the new file")
   state)
  :returns (mv (tempfile "Something like @('$TEMPDIR/$USER-$PID-$BASENAME')"
                         (or (stringp tempfile)
                             (not tempfile))
                         :rule-classes :type-prescription)
               (new-state state-p1 :hyp (force (state-p1 state))))

  :parents (tempfile)
  :short "Join together a temp directory, the user name, the PID, and the base
name to create a temporary filename."

  (b* (((mv pid state) (getpid state))
       ((unless (natp pid))
        (er hard? __function__ "getpid failed")
        (mv nil state))
       ((mv ?err user state) (getenv$ "USER" state))
       ((unless (stringp user))
        (er hard? __function__ "reading $USER failed")
        (mv nil state))
       (filename (str::cat user "-" (str::natstr pid) "-" basename))
       (path     (catpath tempdir filename)))
    (mv path state))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))


(defun pathname-to-unix (str)
  (declare (xargs :guard (stringp str)))
; Copied from axioms.lisp:pathname-os-to-unix
  (if (equal str "")
      str
    (let* ((sep #\\)
           (str0 (substitute ACL2::*directory-separator* sep str)))
      str0)))

(define default-tempdir (state)
  :returns (mv (tempdir "Directory to use for temporary files."
                        stringp :rule-classes :type-prescription)
               (new-state state-p1 :hyp (force (state-p1 state))))

  :parents (tempfile)
  :short "Figure out what directory to use for temporary files."
  :long "<p>We think it's conventional for Linux programs to look at the value
of the @('TMPDIR') environment variable.  On Windows, apparently programs
should use @('TEMP').  If either of these is set, we try to respect the choice.
Otherwise, we just default to @('/tmp').</p>"

  (b* (((mv ?err tempdir state) (getenv$ "TMPDIR" state))
       ((mv ?err temp state)   (getenv$ "TEMP" state))
       (tmpdir (or (and (stringp tempdir) tempdir)
                   (and (stringp temp) (pathname-to-unix temp)) ;; ACL2 traffics in unix-style pathnames
                   "/tmp")))
    (mv tmpdir state))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))


(define default-tempfile ((basename stringp)
                          state)
  :returns (mv (tempfile (or (stringp tempfile)
                             (not tempfile))
                         :rule-classes :type-prescription)
               (new-state state-p1 :hyp (force (state-p1 state))))
  :parents (tempfile)
  :short "Default way to generate temporary file names."
  (b* (((mv dir state) (default-tempdir state)))
    (default-tempfile-aux dir basename state))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))


(defattach tempfile-fn default-tempfile)


