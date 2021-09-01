; compact-print-raw.lsp
; Copyright (C) 2013, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

(in-package "ACL2")

; compact-print-raw.lsp
;
; This file is DEPRECATED.  It is provided only so that former users of
; compact-print and compact-read can still access them.
;
; This file was derived from the original Hons and Memoization code developed
; by Bob Boyer and Warren Hunt.  This code was formerly part of the
; experimental Hons version of ACL2.
;
; Jared split these functions out of memoize-raw.lisp when he added the new
; serialization code to ACL2.  He suggests using the new ACL2 commands
; serialize-read and serialize-write instead of these routines.

; Matt K. removed #-hons code August 2021 and left the #+hons code in place
; without the #+hons directive (since hons is always enabled).

(progn




; HONS READ

; Hash consing when reading is implemented via a change to the readtable for
; the characters open parenthesis, close parenthesis, and period, the consing
; dot.


; See matching comment below.

; Note: our implementation of the #=/## reader, which we built because some
; Lisps would not let us get past #500 or so, does not comply with ANSI at
; least in this regard: it does not allow the entry of looping structures as in
; '(#0= (3 #0#)), which is no problem for ACL2 users.

; WARNING: Any call of READ using *hons-readtable* as *readtable* needs to
; worry about the possible top-level return of HREAD-CLOSE-PAREN-OBJ and
; HREAD-DOT-OBJ, which are simply part of the fiction whereby we read while
; honsing.  Those two objects should absolutely not be returned as the value of
; an ACL2 function.  See, for example, the definition of HONS-READ.


; *** NOTE:  The following collection of functions is just that: a
;            collection.  Unless you understand everything about the
;            various read table macros, then don't touch this code!
;
; [Jared]: poke, poke, poke...




;; [Jared]: I turned these into defconstants instead of defgs, since they are
;; never written, to further separate this from the memoize code.

;; [Jared]: hrmn, well, sbcl seems to gripe about them being redeclared.  I don't
;; understand why.  I'll make them parameters instead

(defparameter hread-close-paren-obj '(#\)))
(defparameter hread-dot-obj         '(#\.))

;; [Jared]: note that these get reinitialized in hons-readtable-init
(defg *hons-readtable*        (copy-readtable *acl2-readtable*))
(defg *hacked-acl2-readtable* (copy-readtable *acl2-readtable*))

(defvar *compact-print-file-ht*)
(declaim (hash-table *compact-print-file-ht*))

(defparameter *hons-read-ht* nil) ; bound sometimes

(defmacro hons-read-ar-len () (expt 2 21))

(defparameter *hons-read-ar*
  (make-array (hons-read-ar-len) :initial-element 0))

(defparameter *hons-read-ar-max* -1)

(defparameter *compact-print-file-n* 0)
(declaim (type fixnum *compact-print-file-n*))


; [Jared]: using defg for this probably breaks any attempt to compact-print
; from multiple threads at the same time.  We should fix this.
(defg *space-owed* nil)

(defun hread-nonsense (x)
  (or (eq x hread-close-paren-obj) (eq x hread-dot-obj)))

(defun check-hread-nonsense (x stream)
  (cond ((hread-nonsense x)
         (hread-error "~&;  Illegal object: ~s." stream (car x)))))

(defun hread-error (string stream &rest r)
  (our-syntax-nice
   (let* ((*standard-input* *debug-io*))
     (apply #'format *error-output* string r)
     (cond ((and (streamp stream) (file-position stream))
            (format *error-output*
                    "~&; near file-position ~s in stream ~s."
                    (file-position stream) stream)))
     (error "hread."))))

(defun illegal-error1 (x stream)
  (hread-error "~&; ** Error:  Illegal:  ~s." stream x))

(defun illegal-error2 (stream char)
  (illegal-error1 char stream))

(defun close-paren-read-macro (stream char)
  (declare (ignore char))
  (if *read-suppress* (illegal-error1 #\\ stream))
  hread-close-paren-obj)

(defun dot-read-macro (stream char)
  (declare (ignore char))
  (if *read-suppress* (illegal-error1 #\. stream))
  (let ((ch (peek-char nil stream t nil t)))
    (cond ((or (member ch '(#\( #\) #\' #\` #\, #\" #\;
                            #\Tab #\Space #\Newline))
               (eql 13 (char-code ch))
               (multiple-value-bind (fn nonterminating)
                   (get-macro-character ch)
                 (and fn (not nonterminating))))
           hread-dot-obj)
          (t (let ((*readtable* *acl2-readtable*))
               (unread-char #\. stream)
               (hons-copy (read stream t nil t)))))))

(defun hons-read-list (stream)

  ; HONS-READ-LIST must return a HONSP whenever it turns a CONSP, even
  ; when the object comes from some readmacro such as that for quote
  ; or backquote that might return a CONS.  Hence the calls to
  ; HONS-COPY.

  (let ((o (read stream t nil t)))
    (cond
     ((eq o hread-close-paren-obj) nil)
     ((eq o hread-dot-obj)
      (let ((lo (read stream t nil t))
            (lp (read stream t nil t)))
        (check-hread-nonsense lo stream)
        (cond
         ((eq lp hread-close-paren-obj)
          (hons-copy lo))
         (t (illegal-error1 #\. stream)))))
     (t (hons o (hons-read-list stream))))))

(defun hons-read-list-top (stream)

  (let ((o (read stream t nil t)))
    (cond
     ((eq o hread-close-paren-obj) nil)
     (t (check-hread-nonsense o stream)
        (hons o (hons-read-list stream))))))

(defun hons-read-reader (stream char)

  (declare (ignore char))
  (cond (*read-suppress*
         (unread-char #\( stream)
         (let ((*readtable* *acl2-readtable*))
           (read stream t nil t)
           nil))
        (t (hons-read-list-top stream))))

(defg *use-hons-in-read-object* t)

(defun clear-hons-read-ar (index)
  (loop for i from 0 to index do
        (setf (aref (the (simple-array t (*)) *hons-read-ar*)
                    (the fixnum i))
              0)))

(defvar *inside-hons-read*
; WARNING: Do not use defg, since this variable can be let-bound.
  nil)

(defun hons-read (&optional stream (eep t) eofv rp)

  "HONS-READ takes the same args as READ.  If *USE-HONS-IN-READ-OBJECT* is
  non-NIL, then HONS is used in the reading instead of CONS.

  We currently disallow any call of hons-read with rp=nil inside a call of
  hons-read."

  (when (and (not rp) *inside-hons-read*)
    (error "Recursive hons-read!"))
  (let ((*inside-hons-read* t)
        (our-eofv (cons nil nil)))
    (cond (*use-hons-in-read-object*

; Although a readmacro such as quote or backquote might return a CONS
; that is not HONSP, HONS-READ-LIST will turn those into HONSES.

           (cond (rp ; DO NOT BIND *HONS-READ-HT/AR-MAX*.
                  (let* ((*readtable* *hons-readtable*)
                         (x (read stream eep our-eofv rp)))
                    (cond ((and (null eep) (eq x our-eofv))
                           eofv)
                          (t (check-hread-nonsense x stream)
                             (hons-copy x)))))
                 (t ; DO BIND *HONS-READ-HT/AR-MAX*, OTHERWISE SAME.
                  (let* ((*hons-read-ht* nil)
                         (*hons-read-ar-max* -1)
                         (*readtable* *hons-readtable*)
                         (x (read stream eep our-eofv rp)))
                    (clear-hons-read-ar *hons-read-ar-max*)
                    (cond ((and (null eep) (eq x our-eofv))
                           eofv)
                          (t (check-hread-nonsense x stream)
                             (hons-copy x)))))))
          (t (cond (rp ; DO NOT BIND *HONS-READ-HT/AR-MAX*.
                    (let* ((*readtable* *hacked-acl2-readtable*)
                           (x (read stream eep our-eofv rp)))
                      (cond ((and (null eep) (eq x our-eofv))
                             eofv)
                            (t x))))
                   (t ; DO BIND *HONS-READ-HT/AR-MAX*, OTHERWISE SAME.
                    (let* ((*hons-read-ht* nil)
                           (*hons-read-ar-max* -1)
                           (*readtable* *hacked-acl2-readtable*)
                           (x (read stream eep our-eofv rp)))
                      (clear-hons-read-ar *hons-read-ar-max*)
                      (cond ((and (null eep) (eq x our-eofv))
                             eofv)
                            (t x)))))))))

(defun hons-read-file (file-name)
  (with-open-file (stream file-name)
    (let ((eof (cons nil nil)) temp ans)
      (loop (setq temp (hons-read stream nil eof nil))
            (cond ((eq eof temp)
                   (setq ans (nreverse ans))
                   (when *use-hons-in-read-object*
                     (setq ans (hons-copy ans)))
                   (return ans))
                  (t (push temp ans)))))))


;  COMPACT PRINT AND READ

(defun compact-read-file (fn)

; May be called directly.

   "(COMPACT-READ-FILE fn) READs the first Lisp/ACL2 form of the file named FN.
   The file should have exactly one Lisp object in it.

   HONS is used instead of CONS while reading when *USE-HONS-IN-READ-OBJECT* is
   not NIL.

   The *ACL2-READTABLE* is used during reading.  The reading respects Common
   Lisp's #2= and #2# readmacro support, but not for circular cons structures."

   (with-open-file (stream fn)
     (let* ((eof (cons nil nil))
            (p (hons-read stream nil eof nil)))
          (when (eq p eof)
            (error "compact-read-file: ~s appears empty." fn))
          (unless (eq (read stream nil eof) eof)
            (error "compact-read-file: ~s has too many forms." fn))
          p)))



(defmacro space-if-necessary (stream)

; do not call

  `(when *space-owed*
     (write-char #\Space ,stream)
     (setq *space-owed* nil)))

(defun compact-print-file-scan (x)

; do not call

  (unless (or (and (symbolp x)
                   (let ((p (symbol-package x)))
                     (or (eq p *main-lisp-package*)
                         (eq p *package*)))
                   (<= (length (symbol-name x)) 4))

              ; On the one hand, in ANSI Lisp, you can't READ the same
              ; string twice.  On the other hand, in HONSing, we
              ; cannonicalize strings.  Should we or shouldn't we
              ; identify common strings here?  Sometimes we do, and
              ; sometimes we don't.

              (and (stringp x) (<= (length x) 2))
              (and (integerp x) (< -100 x 1000))
              (characterp x))
    (let ((g (gethash x *compact-print-file-ht*)))
      (unless (or (atom x) g)
        (compact-print-file-scan (car x))
        (compact-print-file-scan (cdr x)))
      (unless (eq g 'give-it-a-name)
        (setf (gethash x *compact-print-file-ht*)
              (if g 'give-it-a-name 'found-at-least-once))))))

(defun compact-print-file-help (x hash stream)

; do not call directly.

  (cond ((typep hash 'fixnum)
         (space-if-necessary stream)
         (write-char #\# stream)
         (princ hash stream)
         (write-char #\# stream))
        (t (cond ((eq hash 'give-it-a-name)
                  (let ((n *compact-print-file-n*))
                    (declare (type fixnum n))
                    (when (eql n most-positive-fixnum)
                      (error "*compact-print-file-n* overflow."))
                    (setq n (the fixnum (+ 1 n)))
                    (setq *compact-print-file-n* n)
                    (setf (gethash x *compact-print-file-ht*) n)
                    (space-if-necessary stream)
                    (write-char #\# stream)
                    (princ n stream)
                    (write-char #\= stream))))
           (cond
            ((null x)
             (write-char #\( stream)
             (write-char #\) stream)
             (setq *space-owed* nil))
            ((atom x)
             (space-if-necessary stream)

             ; This PRIN1 could commence with a vertical bar that
             ; might be immediately preceded by a sharp sign, which
             ; could confuse comment reading.

             (prin1 x stream)
             (setq *space-owed* t))
            (t (write-char #\( stream)
               (setq *space-owed* nil)
               (loop (compact-print-file-help
                      (car x)
                      (gethash (car x) *compact-print-file-ht*)
                      stream)
                     (cond
                      ((null (cdr x))
                       (write-char #\) stream)
                       (setq *space-owed* nil)
                       (return))
                      ((or (progn
                             (setq hash
                                   (gethash (cdr x)
                                            *compact-print-file-ht*))
                             (or (eq hash 'give-it-a-name)
                                 (typep hash 'fixnum)))
                           (atom (cdr x)))
                       (space-if-necessary stream)
                       (write-char #\. stream)
                       (setq *space-owed* t)
                       (compact-print-file-help (cdr x) hash stream)
                       (write-char #\) stream)
                       (setq *space-owed* nil)
                       (return))
                      (t (pop x)))))))))

(defun compact-print-stream (data stream)
  (cond ((null *print-circle-stream*)
         (error "Attempt to call compact-print-stream without ~
                 initializing ~% *print-circle-stream*.  Consider ~
                 opening output ~% channel with macro ~
                 with-output-object-channel-sharing."))
        ((not (eq stream *print-circle-stream*))
         (error "Attempt to call compact-print-stream on other ~
                 than the current stream.")))
  (let ((*compact-print-file-ht* (hl-mht))
        (*print-array* t))
    (setq *space-owed* nil)
    (let ((p *package*))
      (loop for two in

            ;; We'll cause an error if the settings of these are
            ;; different than they will be under OUR-SYNTAX.

            '((*print-array*                t)
              (*print-base*                 10)
              (*print-case*                 :upcase)
              (*print-circle*               t)
              (*print-escape*               t)
              (*print-pretty*               nil)
              (*print-radix*                nil)
              (*read-base*                  10)
              (*read-suppress*              nil)
              (*readtable*                  *acl2-readtable*))
            when (not (equal (symbol-value (car two))
                             (if (symbolp (cadr two))
                                 (symbol-value (cadr two))
                               (cadr two))))
            do
            (error "PRINT-COMPACT-STREAM: Problem with the setting of ~a" two))

; Currently, there is no way from within ACL2 to alter
; READTABLE-CASE.  Thank goodness.  So the following error will
; never happen.  But if ACL2 were someday 'enhanced' to permit
; control over READTABLE-CASE, there just might be a problem
; about the setting of *PRINT-READABLY* to T by OUR-SYNTAX
; below if the current setting of *PRINT-READABLY* were NIL.

      ;; *PACKAGE* -- we let the user use any ACL2 package.

      (unless (eq (readtable-case *acl2-readtable*) :upcase)
        (error "PRINT-COMPACT-STREAM: Problem with the setting of ~
               (readtable-case *acl2-readtable*)."))

      ;; We do not cause an error if the following *PRINT-...*
      ;; variable settings are different from what OUR-SYNTAX will
      ;; effect, and for many good reasons, as follows.

      ;; *PRINT-READABLY* -- a very tedious explanation.  When
      ;; *PRINT-READABLY* is T, then some extra errors may be caught
      ;; when attempting to print unprintable objects, and there are
      ;; effects upon the printing of arrays.  OUR-SYNTAX binds
      ;; *PRINT-READABLY* to T, and that will be O.K. because (a) we
      ;; don't print packages or arrays in ACL2, (b) we want an error
      ;; signaled by PRINT-OBJECT$ whenever it might be appropriate,
      ;; and (c) as far as we can imagine, when printing any ordinary
      ;; ACL2 object no errors should arise, excepting of the
      ;; catastrophic sort, e.g., disk space exhaused, power outage,
      ;; stack overflow.  But errors may well happen in printing some
      ;; legitimate Lisp, as opposed to ACL2, objects, when printing
      ;; with *PRINT-READABLY* bound to T, e.g., some bizarre
      ;; 'floating point numbers' such as 'infinity', packages, and
      ;; readtables.  Cf. the ANSI function PRINT-UNREADABLE-OBJECT.

      ;; *PRINT-LENGTH*          -- only for pretty
      ;; *PRINT-LEVEL*           -- only for pretty
      ;; *PRINT-LINES*           -- only for pretty
      ;; *PRINT-PPRINT-DISPATCH* -- only for pretty
      ;; *PRINT-MISER-WIDTH*     -- only for pretty
      ;; *PRINT-RIGHT-MARGIN*    -- only for pretty

      ;; *READ-DEFAULT-FLOAT-FORMAT* -- no floats in ACL2

      ;; *PRINT-GENSYM* -- no gensyms in ACL2

      ;; *READ-EVAL* -- OUR-SYNTAX uses T for *READ-EVAL*.  But we
      ;; don't print #. in compact-printing unless the # is properly
      ;; quoted with vertical bars or back-slashes.

      ;; Though OUR-SYNTAX binds *PRINT-CIRCLE* to NIL,
      ;; COMPACT-PRINT-STREAM is designed to do the job that
      ;; *PRINT-CIRCLE* should do, except for circular objects, which
      ;; are not found in ACL2.

      (our-syntax
       (setq *package* p) ; Bound by OUR-SYNTAX to *ACL2-READTABLE*.
       (compact-print-file-scan data)
       (compact-print-file-help
        data
        (gethash data *compact-print-file-ht*)
        stream)
       nil))))

(defun compact-print-file
  (data file-name &key (if-exists :supersede))

; May be called directly.

  "(COMPACT-PRINT-FILE x str) PRIN1s x to a new file named str so that
   Common Lisp can READ the result and get back something EQUAL,
   assuming the package and readtable are the same on print and read.
   COMPACT-PRINT-FILE prints as though *PRINT-CIRCLE* were T to
   minimize printing by a kind of compression, using traditional Lisp
   #..# syntax.  However, circular object are not handled.  See the
   bindings of some *PRINT-...* variables via OUR-SYNTAX in
   COMPACT-PRINT-STREAM, which favor accuracy and not prettiness.  The
   ACL2 package, ACL2 readtable, and decimal *PRINT-BASE* are used."

  (setq *compact-print-file-n* 0)
  (with-open-file (stream file-name
                          :direction :output
                          :if-exists if-exists)
    (let ((*print-circle-stream* stream)

; These *print... and *read... settings are deliberately inflicted
; upon the user of COMPACT-PRINT-FILE.  The user is still free to
; choose *PACKAGE*.  Read the comment in compact-print-stream for
; information about our rather fascist approach to these settings.

          (*print-base* 10)
          (*print-case* :UPCASE)
          (*print-circle* t)
          (*print-escape* t)
          (*print-pretty* nil)
          (*read-base* 10)
          (*read-eval* t)  ; to support #.constant printing
          (*read-suppress* nil)
          (*readtable* *acl2-readtable*)

          ; Not relevant once one knows that *PRINT-PRETTY* is NIL:

          (*print-length* nil)
          (*print-level* nil)
          (*print-lines* nil)
          (*print-radix* nil)
          (*print-right-margin* nil)

          ; Not relevant when printing only ACL2 objects:

          (*print-readably* t)
          (*read-default-float-format*  'single-float)
          (*print-gensym* t)
          (*print-array* t)

          ; This one is crucial to know about since strings are ACL2
          ; objects:

          #+CCL
          (ccl::*print-string-length* nil)

          #+CCL
          (ccl::*print-abbreviate-quote* nil)

          ; These are irrelevant as long as we are printing
          ; an ACL2 object.

          #+CCL
          (ccl::*print-structure* t)
          #+CCL
          (ccl::*print-simple-vector* nil)
          #+CCL
          (ccl::*print-simple-bit-vector* nil)

          ; Do many other Lisps have their own private set of secret
          ; print control variables?

          )
      (compact-print-stream data stream))
    (namestring (our-truename stream))))

(defun ns-=-reader (stream subchar arg)

; We don't use DEFUN because this function might return 0 values.

; Do not call ns-=-reader directly.

; NS-=-READER intentionally does not read circular Lisp objects
; correctly, such as those normally created by reading #2=(1 #2#).
; Such a circular object could not be an ACL2 object anyway.  An
; attempt to read such an object will result in a clean error, e.g., a
; report that the expression #2# makes no sense because a #2= ?
; expression has not been fully read.

; *HONS-READ-HT* must always have a value, either NIL or a hash table;
; cf. READ-OBJECT and COMPACT-READ-FILE.

; *HONS-READ-AR* must always have a value, either NIL or a simple
; vector.  cf. READ-OBJECT and COMPACT-READ-FILE.

  (declare (ignore subchar))
  (cond ((null arg)
         (hread-error "~&; ns-=-reader: ** Error: #= is illegal."
                      stream arg))
        (*read-suppress* (values))
        ((< arg (hons-read-ar-len))
         (let ((x (read stream t nil t)))
           (cond ((eql x 0) ; 0 might be confused for the default
                  (unless *hons-read-ht*
                    (setq *hons-read-ht* (make-hash-table)))
                  (multiple-value-bind (val present-p)
                      (gethash arg *hons-read-ht*)
                    (when present-p
                      (hread-error
                       "~&; ns-=-reader: ** Error: #~s= is already ~
                        defined to be ~s."
                       stream arg val))
                    (setf (gethash arg *hons-read-ht*) 0)))
                 (t (setf *hons-read-ar-max*
                          (max (the fixnum *hons-read-ar-max*)
                               (the fixnum arg)))
                    (setf (aref (the (simple-array t (*))
                                  *hons-read-ar*)
                                (the fixnum arg))
                          x)))))
        (*hons-read-ht*
         (multiple-value-bind (val present-p)
             (gethash arg *hons-read-ht*)
           (when present-p
             (hread-error
              "~&; ns-=-reader: ** Error: #~s= is already ~
               defined to be ~s."
              stream arg val))
           (setf (gethash arg *hons-read-ht*)
                 (read stream t nil t))))
        (t (setq *hons-read-ht* (make-hash-table))
           (setf (gethash arg *hons-read-ht*)
                 (read stream t nil t)))))

(defun ns-ns-reader (stream subchar arg)

; Do not call NS-NS-READER directly.

; *HONS-READ-HT* must always have as its value NIL or a hash table.
; *HONS-READ-AR* must always have as its value NIL or a simple,
; one-dimensional array.  cf. READ-OBJECT and COMPACT-READ-FILE.

  (declare (ignore subchar))
  (cond (*read-suppress* nil)  ; ?
        ((null arg)
         (hread-error
          "~&; ns-ns-reader: ** Error: meaningless ##."
          stream arg))
        ((and *hons-read-ar* (< arg (hons-read-ar-len)))
         (let ((ans (aref (the (simple-array t (*)) *hons-read-ar*)
                          (the fixnum arg))))
           (cond ((eql ans 0) ; could be the default
                  (unless *hons-read-ht*
                    (setq *hons-read-ht* (make-hash-table)))
                  (multiple-value-bind (val present-p)
                      (gethash arg *hons-read-ht*)
                    (cond (present-p val)
                          (t (hread-error
                              "~&; ns-ns-reader: ** Error: ~
                               meaningless #~s#."
                              stream arg)))))
                 (t ans))))
        (*hons-read-ht*
         (multiple-value-bind (val present-p)
             (gethash arg *hons-read-ht*)
           (cond (present-p val)
                 (t (hread-error
                     "~&; ns-ns-reader: ** Error: meaningless ~
                      #~s#."
                     stream arg)))))
        (t (hread-error
            "~&; ns-ns-reader:  ** Error:  meaningless #~s#."
            stream arg))))


;  HONS READTABLE INIT

(defg *hons-readtable-init-done* nil)

(defun hons-readtable-init ()

  (when *hons-readtable-init-done*
    ;; Already initialized
    (return-from hons-readtable-init nil))

  (setq *hons-readtable*
        ;; BOZO why?  it already started as a copy of the acl2-readtable...
        (copy-readtable *acl2-readtable*))

  (set-macro-character
   #\( #'hons-read-reader       nil *hons-readtable*)
  (set-macro-character
   #\) #'close-paren-read-macro nil *hons-readtable*)
  (set-macro-character
   #\. #'dot-read-macro         t   *hons-readtable*)
  (set-dispatch-macro-character
   #\# #\# #'ns-ns-reader           *hons-readtable*)
  (set-dispatch-macro-character
   #\# #\= #'ns-=-reader            *hons-readtable*)

  (setq *hacked-acl2-readtable*
        ;; BOZO why?  it already started as a copy of the acl2-readtable...
        (copy-readtable *acl2-readtable*))

  (set-dispatch-macro-character
   #\# #\# #'ns-ns-reader           *hacked-acl2-readtable*)
  (set-dispatch-macro-character
   #\# #\= #'ns-=-reader            *hacked-acl2-readtable*)

  (setq *hons-readtable-init-done* t))



)


; [Jared] formerly this was called as part of hons-init-hook...
; maybe this is sufficient?
(eval-when (:load-toplevel)
 (hons-readtable-init))
