; Access to CCL::ADVISE
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original authors: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "include-raw")

; NOT SOUND.  You can do any old underhanded thing you want when you advise a
; function, including, e.g., smashing ACL2's state.


(defun advise$-fn (fn form when name)
  (declare (ignorable fn form when name)
           (xargs :guard t))
  (er hard? 'advise$ "Raw lisp definition not installed?"))

(defun unadvise$-fn (fn when name)
  (declare (ignorable fn when name)
           (xargs :guard t))
  (er hard? 'unadvise$ "Raw lisp definition not installed?"))

(defun advisedp$-fn (fn when name)
  (declare (ignorable fn when name)
           (xargs :guard t))
  (er hard? 'advisedp$ "Raw lisp definition not installed?"))


(defmacro advise$ (fn form &key when name)
  `(advise$-fn ,fn ,form ,when ,name))

(defmacro unadvise$ (fn &key when name)
  `(unadvise$-fn ,fn ,when ,name))

(defmacro advisedp$ (fn &key when name)
  `(advisedp$-fn ,fn ,when ,name))


(defttag :unsound-advise$)
(include-raw "advise-raw.lsp")




#||

(include-book
 "advise")

(defun f (x)
  (declare (xargs :guard (natp x)))
  (mv (+ 1 x) (+ 2 x)))

(advise$ 'f
         '(cw "Values were ~x0~%" values)
         :when :after)

(f 3)
(f 5)

||#