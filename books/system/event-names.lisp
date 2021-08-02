; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(program)

(defun event-names-rec (wrld-tail omit-boot-strap acc)
  (declare (xargs :mode :program))
  (cond
   ((or (endp wrld-tail)
        (and omit-boot-strap
             (and (eq (caar wrld-tail) 'command-landmark)
                  (eq (cadar wrld-tail) 'global-value)
                  (equal (access-command-tuple-form (cddar wrld-tail))
                         '(exit-boot-strap-mode)))))
    acc)
   (t
    (let* ((trip (car wrld-tail))
           (ev-tuple (and (consp trip)
                          (eq (car trip) 'event-landmark)
                          (eq (cadr trip) 'global-value)
                          (cddr trip)))
           (type (and ev-tuple (access-event-tuple-type ev-tuple)))
           (namex (and type (access-event-tuple-namex ev-tuple))))
      (event-names-rec (cdr wrld-tail)
                       omit-boot-strap
                       (if (and namex (symbolp namex))
                           (cons namex acc)
                         acc))))))

(defun event-names (wrld omit-boot-strap)

; There can be duplicates in the result from event-names-rec, especially
; because of promotion of a function to :logic mode, but also because of
; redefinition.  So we sort.

  (strict-merge-sort-symbol<
   (event-names-rec wrld omit-boot-strap nil)))

(defun initial-substringp-rec (bound s1 s2)
  (declare (type (unsigned-byte 29) bound)
           (type string s1 s2))
  (cond ((zp bound) t)
        (t (let ((bound (1-f bound)))
             (declare (type (unsigned-byte 29) bound))
             (and (char-equal (char s1 bound)
                              (char s2 bound))
                  (initial-substringp-rec bound s1 s2))))))

(defun initial-substringp (s1 len-s1 s2)

; Return t if s1 is a case-insensitive initial substring of s2, else nil.

  (declare (type string s1 s2)
           (type (unsigned-byte 29) len-s1)
           (xargs :guard (equal (length s1) len-s1)))
  (and (<= len-s1 (length s2))
       (assert$
        (unsigned-byte-p 29 len-s1) ; surely, for strings we'll encounter!
        (initial-substringp-rec len-s1 s1 s2))))

(defun event-names-matching-prefix1 (prefix len-prefix names acc)
  (cond
   ((endp names)

; It's not really necessary to call reverse here, but since in our intended use
; names is sorted in increasing order, it seems like a nice presentation of the
; result to provide that order as well.

    (reverse acc))
   (t (event-names-matching-prefix1
       prefix
       len-prefix
       (cdr names)
       (if (initial-substringp prefix len-prefix (symbol-name (car names)))
           (cons (car names) acc)
         acc)))))

(defun event-names-matching-prefix (prefix-symbol wrld omit-boot-strap)
  (let ((prefix (symbol-name prefix-symbol)))
    (event-names-matching-prefix1 prefix
                                  (length prefix)
                                  (event-names wrld omit-boot-strap)
                                  nil)))

(defmacro ep (prefix &optional omit-boot-strap)
  `(event-names-matching-prefix ,prefix (w state) ,omit-boot-strap))

(defmacro ep- (prefix) ; omit-boot-strap
  `(ep ,prefix t))

(defxdoc ep
  :parents (history)
  :short "Return the sorted list of event names matching a given prefix"
  :long "@({
 Example:

 ACL2 !>:ep with-output ; or, (ep 'with-output); see @(see keyword-commands)
 (WITH-OUTPUT WITH-OUTPUT-FN
              WITH-OUTPUT-FORCED WITH-OUTPUT-LOCK
              WITH-OUTPUT-OBJECT-CHANNEL-SHARING)
 ACL2 !>
 })

 <p>The value returned by @('(:ep NAME)') is the list of all event names @('E')
 for which @('\"NAME\"') is a prefix of the @(see symbol-name) of @('E'), where
 this notion of ``prefix'' is case-insensitive.</p>

 <p>Also see @(see ep-) for a similar utility that omits names of built-in
 @(see events).</p>")

(defxdoc ep-
  :parents (history)
  :short "Return the sorted list of non-builtin event names matching a given
 prefix"
  :long "<p>See @(see ep) for an analogous utility that includes built-in event
 names in the result.  In the following example, we see that @('ep-') is
 similar but only considers names that are not built into ACL2, so for example
 the result below does not include the name @('with-output').</p>

 @({
 Example:

 ACL2 !>(defmacro with-output-off (form)
          `(with-output :off :all ,form))

 Summary
 Form:  ( DEFMACRO WITH-OUTPUT-OFF ...)
 Rules: NIL
 Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
  WITH-OUTPUT-OFF
 ACL2 !>:ep- with-output
 (WITH-OUTPUT-OFF)
 ACL2 !>
 })")
