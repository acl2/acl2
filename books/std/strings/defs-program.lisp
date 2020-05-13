; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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
; mostly copied from defs.lisp by Jared Davis <jared@centtech.com>
;
; Modified by Jared to pull out the common part into defs-aux.lisp

(in-package "STR")
(include-book "std/basic/defs" :dir :system)
(include-book "std/util/bstar" :dir :system)

; This book needs to be included here so that there is one unique definition of
; each of the functions with raw Lisp definitions in fast-cat.lisp.  Otherwise,
; the definitions introduced redundantly below wouldn't be considered redundant
; if that book was included first.
(include-book "printtree")

;(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "make-event/acl2x-help" :dir :system))
; (include-book "std/lists/list-defuns" :dir :system)
(local (include-book "defs-aux"))

; cert_param (acl2x)
; cert_param (acl2xskip)
; (depends-rec "top")
(make-event
 '(:or
   (acl2::acl2x-replace (include-book
                         "top" :uncertified-okp :ignore-certs)
                        (value-triple :invisible)
                        :outside-certification
                        (include-book
                         "top" :uncertified-okp :ignore-certs))
   (make-event
    (er hard? 'defs-program
        "~%************************* DEFS-PROGRAM FAILURE *************************~%~
         Failed to include std/strings/top.  It may be that something has ~
         changed in this book or one of the books it includes that makes it ~
         impossible to include uncertified.  Please check this by running ~
         \"make clean\" followed by \"make std/strings/defs-program.cert\".~%~
           ************************************************************************"))))


(program)

(make-event
 '(:or
   (make-event
    (b* ((events (std::defredundant-fn *str-library-basic-defs* t state)))
      (acl2::value events)))
   (make-event
    (er hard? 'defs-program
        "~%************************* DEFS-PROGRAM FAILURE *************************~%~
         Failed to redundantly define the required events.  If you haven't ~
         done anything to break files that this book depends on, this may be ~
         a symptom that make-event expansions from stale certificates are ~
         being loaded.  The simplest way to fix this is to run \"make ~
         clean\".  Otherwise, you can try to locate and delete the ~
         certificate containing the bad expansion, but you're on your own for ~
         that.~%~
           ************************************************************************"))))

