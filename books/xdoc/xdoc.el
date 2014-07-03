; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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
; xdoc.el - Contributed by Matt Kaufmann
;
; This file introduces xdoc-link-mode, a hack which instructs emacs to carry
; out a tags search for the contents of any foo.xdoc-link file that it opens.

(defun xdoc-cmd ()
  (let ((filename buffer-file-name)
	(sym (read (current-buffer))))
    (kill-buffer (current-buffer))
    (cond ((symbolp sym)
	   (find-tag (symbol-name sym)))
	  ((null filename)
	   (error "Unable to process xdoc-cmd; missing filename?"))
	  (t
	   (error "Unable to process xdoc-cmd; see file ~s"
		  filename)))))

(define-derived-mode xdoc-link-mode
  fundamental-mode "Xdoc-link"
  "Major mode for xdoc-link files."
  )

(add-hook 'xdoc-link-mode-hook
	  'xdoc-cmd)

(setq auto-mode-alist
      (cons  '("\\.xdoc-link\\'" . xdoc-link-mode) auto-mode-alist))