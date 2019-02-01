; cert.pl build system
; Copyright (C) 2018 Centaur Technology
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

(in-package "ACL2")

(defun ifdef-fn (varname forms negate state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((endif-tail (member :endif forms)))
    (cond ((or (not endif-tail)
               (consp (cdr endif-tail)))
           (er soft 'ifdef-fn
               "IFDEF requires that the last argument to it be the keyword ~
                symbol :ENDIF, in order to support scanning by cert.pl.  ~
                Additionally, that symbol should be on a separate line from ~
                other forms."))
          ((not (stringp varname))
           (er soft 'ifdef-fn
               "IFDEF requires that its first argument be a literal string. ~
                Additionally, to support scanning by cert.pl, that string ~
                should be on the same line of the file as the IFDEF."))
          (t (er-let*
              ((var (getenv$ varname state)))
              (if (xor negate (and var (not (equal var ""))))
                  (value (cons 'progn (butlast forms 1))) ;; remove the :endif
                (value '(value-triple :skipped))))))))

(defmacro ifdef (varname &rest forms)
  `(make-event (ifdef-fn ,varname ',forms nil state)))

(defmacro ifndef (varname &rest forms)
  `(make-event (ifdef-fn ,varname ',forms t state)))
  
               
(defmacro ifdef-define (x)
  `(value-triple (setenv$ ,x "1")))

(defmacro ifdef-undefine (x)
  `(value-triple (setenv$ ,x "")))
