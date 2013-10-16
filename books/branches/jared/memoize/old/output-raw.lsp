; output-raw.lsp
; Copyright (C) 2013, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; This file was originally part of the HONS version of ACL2.  The original
; version of ACL2(h) was contributed by Bob Boyer and Warren A. Hunt, Jr.  The
; design of this system of Hash CONS, function memoization, and fast
; association lists (applicative hash tables) was initially implemented by
; Boyer and Hunt.

(in-package "ACL2")

; [Jared] this is just some output stuff that used to be part of memoize

(defv *hons-verbose* t)
(defg *ofv-note-printed* nil)
(defg *ofv-msg-list* nil)

(defg *ofe-msg-list* nil)
(defg *ofb-msg-list* nil)

(defun ofe (&rest r)  ; For writing to *error-output*; calls (error).
  (our-syntax-nice
   (format *error-output* "~%; ** Error:  ")
   (let ((*print-pretty* t)
         (*print-level* 4)
         (*print-length* 10)
         (*print-lines*  10))
     (apply #'format *error-output*
            (loop for x in r collect (abbrev x)))
     (force-output *terminal-io*)
     (force-output *error-output*)
     (force-output *standard-output*)
     (force-output *debug-io*)
     (clear-input *terminal-io*)
     (clear-input *standard-input*)
     (clear-input *debug-io*)
     (push (cons 'ofe r) *ofe-msg-list*)
     (error "~%; See *ofe-msg-list*."))))

(defun ofb (&rest r) ; For writing to *debug-io* and breaking.
  (our-syntax-nice
   (format *debug-io* "~%; ** Warning and break:  ")
   (let ((*print-level* 3) (*print-length* 5) (*print-lines* 6))
     (let ((ab (loop for x in r collect (abbrev x))))
       (apply #'format *debug-io* ab)
       (when (loop for x in ab as y in r thereis (not (eq x y)))
         (push (cons 'ofe r) *ofb-msg-list*)
         (format *error-output* "~%; See *ofb-msg-list*."))
       (force-output *debug-io*)
       (error "")))
   (break "ofb")))

(defun ofv (&rest r) ; For verbose but helpful info.
  (our-syntax-nice
   (when *hons-verbose*
     (format *debug-io* "~%; Aside:  ")
     (let ((*print-level* 3)
           (*print-length* 5)
           (*print-lines* 5))
       (let ((ab (loop for x in r collect (abbrev x))))
         (apply #'format *debug-io* ab)
         (when (loop for x in ab as y in r thereis (not (eq x y)))
           (push (cons 'ofv r) *ofv-msg-list*)
           (format *debug-io* "~%; See *ofv-msg-list*."))
         (unless *ofv-note-printed*
           (format *debug-io*
                   "~%; Aside:  (setq acl2::*hons-verbose* nil) to ~
                    suppress asides.")
           (setq *ofv-note-printed* t))))
     (force-output *debug-io*))))

(defun ofvv (&rest r) ; For very verbose but helpful info.
  (our-syntax-nice
   (when (and (integerp *hons-verbose*) (> *hons-verbose* 1))
     (format *debug-io* "~%; Aside:  ")
     (let ((*print-level* 3) (*print-length* 5) (*print-lines* 5))
       (let ((ab (loop for x in r collect (abbrev x))))
         (apply #'format *debug-io* ab)
         (when (loop for x in ab as y in r thereis (not (eq x y)))
           (push (cons 'ofv r) *ofv-msg-list*)
           (format *debug-io* "~%; See *ofv-msg-list*."))
         (unless *ofv-note-printed*
           (format *debug-io*
                   "~%; Aside:  (setq acl2::*hons-verbose* nil) ~
                    to suppress asides.")
           (setq *ofv-note-printed* t))))
     (force-output *debug-io*))))

(defmacro ofg (&rest r) ; For verbose gc info.
    `(when *hons-verbose*
       (format *debug-io* ,@r)
       (force-output *debug-io*)))


(defun ofw (&rest r) ; For writing to *debug-io*, with a warning.
  (our-syntax-nice
   (format *debug-io* "~%; ** Warning:  ")
   (apply #'format *debug-io* r)
   (force-output *debug-io*)))


(defmacro ofd (&rest r) ; For writing to *debug-io*.
  `(progn (format *debug-io* ,@r) (force-output *debug-io*)))


(defmacro ofto (&rest r) ; For writing to *terminal-io*
  `(progn (format *terminal-io* ,@r)
          (force-output *terminal-io*)))
