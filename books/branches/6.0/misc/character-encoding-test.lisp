; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann
; email:       Kaufmann@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; April, 2012

(in-package "ACL2")

; This file has been saved using the utf-8 character encoding.  As a result,
; the constant below has length 2 when using ACL2, which fixes the character
; encoding at iso-8859-1 (see :DOC character-encoding).  If the length of this
; constant is 1, then this file was probably saved with a different encoding,
; quite possibly iso-8859-1.

; WARNING: Before saving this file in emacs, evaluate the following form to set
; the indicated buffer-local variable, especially if you have loaded
; distributed file emacs/emacs-acl2.el into your emacs session, since that file
; sets the character encoding to iso-8859-1.

; (setq save-buffer-coding-system 'utf-8)

; If you have not done this, then in a linux shell, executing
;   cat character-encoding-test.lisp
; may show clearly that the string below has a single character.

; We have considered defining a function test-1 in file
; character-encoding-test.acl2, with the same body as test-2 below.  However,
; in SBCL 1.0.49 we found that our attempt to set the external format to
; iso-8859-1 (see function acl2-set-character-encoding in the ACL2 sources) did
; not affect reading directly from standard input.  Since .acl2 files are
; indeed read that way using the standard ACL2 makefile approach, SBCL was
; reading that .acl2 file in utf-8 format.  So we have abandoned the use of a
; .acl2 file and restricted ourselves just to the file-based test below.

(defun test-2 () "ó")

(defthm len-test-2
  (equal (length (test-2)) 2)
  :rule-classes nil)
