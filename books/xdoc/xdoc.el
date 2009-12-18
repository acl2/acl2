; XDOC Documentation System for ACL2
; Copyright (C) 2009 Centaur Technology
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
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