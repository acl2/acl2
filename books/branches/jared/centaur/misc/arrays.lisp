; Centaur Miscellaneous Books
; Copyright (C) 2008-2013 Centaur Technology
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
