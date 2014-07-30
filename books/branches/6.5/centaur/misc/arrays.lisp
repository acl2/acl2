; Centaur Miscellaneous Books
; Copyright (C) 2008-2013 Centaur Technology
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

(defun def-array-set-fn (name stobj field update length guard fix check)
  (let* ((length (or length
                     (intern-in-package-of-symbol
                      (concatenate 'string
                                   (symbol-name field) "-LENGTH")
                      field)))
         (update (or update
                     (intern-in-package-of-symbol
                      (concatenate 'string
                                   "UPDATE-" (symbol-name field) "I")
                      field)))
         (fast-name (intern-in-package-of-symbol
                     (concatenate 'string
                                  (symbol-name name) "-FAST")
                     name)))

    `(progn
       (definline ,name (idx x ,stobj)
         (declare (xargs :guard (and (natp idx) ,guard)
                         :stobjs ,stobj))
         (mbe :logic (,update (nfix idx) ,fix ,stobj)
              :exec (if (and (< idx (,length ,stobj))
                             ,check)
                        (,update idx x ,stobj)
                      (ec-call (,update idx x ,stobj)))))
       (definline ,fast-name (idx x ,stobj)
         (declare (xargs :guard (and (natp idx)
                                     (< idx (,length ,stobj))
                                     ,guard)
                         :stobjs ,stobj))
         (mbe :logic (,update (nfix idx) ,fix ,stobj)
              :exec ,(if (equal check ''t)
                         `(,update idx x ,stobj)
                       `(if ,check
                            (,update idx x ,stobj)
                          (ec-call (,update idx x ,stobj)))))))))

(defmacro def-array-set (name &key stobj field update length
                              guard fix (check 't))
  (def-array-set-fn name stobj field update length guard fix check))



(defun def-slot-set-fn (name stobj field update guard fix check)
  (let* ((update (or update
                     (intern-in-package-of-symbol
                      (concatenate 'string
                                   "UPDATE-" (symbol-name field))
                      field))))

    `(definline ,name (x ,stobj)
       (declare (xargs :guard ,guard
                       :stobjs ,stobj))
       (mbe :logic (,update ,fix ,stobj)
            :exec (if ,check
                      (,update x ,stobj)
                    (ec-call (,update x ,stobj)))))))

(defmacro def-slot-set (name &key stobj field update
                              guard fix (check 't))
  (def-slot-set-fn name stobj field update guard fix check))

;;(defun def-array-extract-fn (name stobj field
