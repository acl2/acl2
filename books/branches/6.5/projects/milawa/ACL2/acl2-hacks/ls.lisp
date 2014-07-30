; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
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

(in-package "ACL2")

;; We introduce a wrapper for ls so that we can inspect generated files.  We
;; need a ttag to call sys-call, but this should be a sound extension of ACL2
;; as it does not muck with any system internals.

(defttag ls)

(defun ls (filename)
  (declare (xargs :guard (stringp filename))
           (ignore filename))
  (cw "ls has not yet been redefined under the hood~%"))

(progn!
 (set-raw-mode t)

 (defun ls (filename)
   ;; I've complained before that ACL2's sys-call does not provide a standard
   ;; interface across Lisps, but it has not been standardized.  So, calling
   ;; ls, which ought to be a really simple thing, is not and is probably buggy
   ;; in some cases.  This sort of shit is really lame, and makes me want to
   ;; use a different language.  In the meantime, we have this hacky solution.
   #+gcl
   ;; GCL needs the filename to be quoted, or it won't handle filenames with
   ;; spaces correctly.
   (if (position #\" filename)
       (ACL2::cw "Sorry.  ACL2's sys-call is too broken to use \"ls\" on files~
                  whose names include quotes on GCL.~%")
     (sys-call "ls" (list "-lh" (concatenate 'string "\"" filename "\""))))
   #+allegro
   ;; Allegro is completely fucked.  Whether or not you quote the string, the
   ;; spaces within it will be interpreted as argument separators.  So, I don't
   ;; know of any way to actually say ls "hello world.txt" in allegro.
   (if (position #\Space filename)
       (ACL2::cw "Sorry.  ACL2's sys-call is too broken to use \"ls\" on files~
                  whose names include spaces on Allegro.~%")
     (sys-call "ls" (list "-lh" filename)))
   #+(or clisp cmu openmcl sbcl)
   ;; CLISP, CMU, SBCL, and OpenMCL do not want the filename to be quoted, and
   ;; I think their behavior is the most proper.  You seem to be able to put
   ;; most anything you want into filenames here.
   (prog2$
    ;; Often prevent horrible death on fork when too much memory is allocated
    (funcall (intern "GC" (find-package "CCL")))
    (sys-call "ls" (list "-lh" filename)))
   #-(or gcl allegro clisp cmu openmcl sbcl)
   (ACL2::cw "Sorry.  ACL2's sys-call is not standardized, and support for this~
             platform has not yet been implemented.")
   nil
   ))
