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
(include-book "misc/hons-help2" :dir :system)
(include-book "compact-print")

;; This is the same as ACL2's compact-write-file, except that it prints symbols
;; from the MILAWA package instead of the ACL2 package.  This helps keep file
;; sizes down, e.g., we only print PEQUAL* instead of MILAWA::PEQUAL*, etc.
;;
;; Though we use a ttag, this should be a sound extension of ACL2 as it does
;; not muck with any system internals.

(defund MILAWA::compact-write-file (data filename)
  (declare (xargs :guard t)
           (ignore data))
  (progn$
   (cw "Warning: compact-write-file has not been redefined!~%")
   filename))

(defttag compact-write-file)

(progn!
 (set-raw-mode t)
 (defund MILAWA::compact-write-file (data filename)
   (setq *compact-print-file-ht* (hl-mht))
   (setq *compact-print-file-n* 0)
   (setq *space-owed* nil)
   (with-open-file (*standard-output* filename
                                      :direction :output
                                      :if-does-not-exist :create
                                      :if-exists :supersede)
                   (with-standard-io-syntax
                    (let ((*package* (find-package "MILAWA"))
                          (*readtable* *acl2-readtable*))
                      (compact-print-file-scan data)
                      (compact-print-file-help data
                                               (gethash data *compact-print-file-ht*)
                                               ;; In V3-5, an extra stream argument was added.  We still
                                               ;; want to support v3-4, so we only sometimes add the arg.
                                               #-v3-4 *standard-output*
                                               )
                      (setq *compact-print-file-ht* (hl-mht)))))
   filename))

(value-triple (milawa::compact-write-file '(1 . 2) "compact-write-file.test.out"))