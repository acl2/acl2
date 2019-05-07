; ACL2 Version 8.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2019, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Regarding authorship of ACL2 in general:

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; serialize.lisp -- logical definitions for "serialization" routines,
;                   i.e., saving ACL2 objects in files for later loading

; This file was developed and contributed by Jared Davis on behalf of
; Centaur Technology.

; Note: The serialization routines are restricted to work only in
; ACL2(h).  However, they are independent of the remainder of the HONS
; extension and might some day become part of ordinary ACL2.

; Please direct correspondence about this file to Jared Davis
; <jared@centtech.com>.

(in-package "ACL2")

(defmacro serialize-write (filename obj &key verbosep)
  `(serialize-write-fn ,filename ,obj ,verbosep state))

(defun serialize-write-fn (filename obj verbosep state)
  (declare (xargs :guard (and (stringp filename)
                              (booleanp verbosep)
                              (state-p state))
                  :stobjs state)
           (ignorable filename obj verbosep))
  #-acl2-loop-only
  (cond
   ((live-state-p state)
    #-hons
    (er hard? 'serialize-write-fn
        "Serialization routines are currently only available in the HONS ~
         version of ACL2.")
    #+hons
    (with-open-file
     (stream filename
             :direction :output
             :if-exists :supersede)
     (let* ((*ser-verbose* verbosep))
       (ser-encode-to-stream obj stream)))
    (return-from serialize-write-fn state))
   (t

; We fall through to the logic code if we are doing a proof, where
; *hard-error-returns-nilp* is true.  Otherwise, we throw here with an error
; message.

    (er hard? 'serialize-write-fn "Serialization requires a live state.")))
  (mv-let (erp val state)
          (read-acl2-oracle state)
          (declare (ignore erp val))
          state))

(defmacro serialize-read (filename &key
                                   (hons-mode ':smart)
                                   verbosep)
  `(serialize-read-fn ,filename ,hons-mode ,verbosep state))

(defun serialize-read-fn (filename hons-mode verbosep state)

; This function returns a single object.

  (declare (xargs :guard (and (stringp filename)
                              (member hons-mode '(:never :always :smart))
                              (booleanp verbosep)
                              (state-p state))
                  :stobjs state)
           (ignorable filename hons-mode verbosep))

  #-acl2-loop-only
  (cond
   ((live-state-p state)
    (return-from
     serialize-read-fn
     #-hons
     (progn (er hard? 'serialize-read-fn
                "Serialization routines are currently only available in the ~
                 HONS version of ACL2.")
            (mv nil state))
     #+hons
     (with-open-file
      (stream filename :direction :input)
      (let* ((*ser-verbose* verbosep)
             (val           (ser-decode-from-stream t hons-mode stream)))
        (mv val state)))))
   (t

; We fall through to the logic code if we are doing a proof, where
; *hard-error-returns-nilp* is true.  Otherwise, we throw here with an error
; message.

    (er hard? 'serialize-read-fn "Serialization requires a live state.")))
  (mv-let (erp val state)
          (read-acl2-oracle state)
          (declare (ignore erp))
          (mv val state)))

(defmacro with-serialize-character (val form)
  (declare (xargs :guard (member val '(nil #\Y #\Z))))
  `(state-global-let*
    ((serialize-character ,val set-serialize-character))
    ,form))
