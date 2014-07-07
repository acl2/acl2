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

;; It is unfortunate that we have to write this file, but ACL2 provides no nice
;; way to disable fertilization and generalization, which usually don't work
;; and are not implemented in Milawa.
;;
;; Originally I implemented a custom "defthm" hint that inserted a :do-not
;; '(generalize fertilize) into my proofs on "Goal" automatically.  But this
;; does not get carried through into forcing rounds, and ACL2 does not provide
;; any kind of "All" target.  So, sometimes in forcing rounds I still had
;; fertilization taking place.
;;
;; Now we just use a default hint that always disables generalization and
;; fertilization when goals are stable under simplification.  This is chatty
;; but I don't have many alternatives.

(table no-fertilize-table 'fertilize-okp nil)
(table no-fertilize-table 'generalize-okp nil)

(defun no-fertilize-hint (world stable-under-simplificationp state)
  (declare (xargs :mode :program :stobjs state))
  (and stable-under-simplificationp
       (let ((generalize-okp (cdr (assoc 'generalize-okp (table-alist 'no-fertilize-table world))))
             (fertilize-okp  (cdr (assoc 'fertilize-okp (table-alist 'no-fertilize-table world)))))
         (cond ((and (not generalize-okp)
                     (not fertilize-okp))
                (prog2$ (if (not (gag-mode))
                            (cw ";; hint: no fertilize/generalize~|")
                          nil)
                        '(:do-not '(generalize fertilize))))
               ((not generalize-okp)
                (prog2$ (if (not (gag-mode))
                            (cw ";; hint: no generalize~|")
                          nil)
                        '(:do-not '(generalize))))
               ((not fertilize-okp)
                (prog2$ (if (not (gag-mode))
                            (cw ";; hint: no fertilize~|")
                          nil)
                        '(:do-not '(fertilize))))
               (t
                nil)))))

(add-default-hints! '((no-fertilize-hint world stable-under-simplificationp state)))

(defmacro allow-generalize (flag)
  (declare (xargs :guard (booleanp flag)))
  `(table no-fertilize-table 'generalize-okp ,flag))

(defmacro allow-fertilize (flag)
  (declare (xargs :guard (booleanp flag)))
  `(table no-fertilize-table 'fertilize-okp ,flag))

