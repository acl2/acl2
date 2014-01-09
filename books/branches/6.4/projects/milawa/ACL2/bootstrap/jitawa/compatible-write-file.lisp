;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; compatible-write-file.lisp
;
; We now introduce an alternative to compact-write-file that can produce a
; compatible proof file for both Common Lisp and the Verified Lisp.


; Symbol Encoding
;
; The Verified Lisp uses a syntax that is similar to Common Lisp but has some
; differences.  We now try to identify a subset of symbols that are compatible
; across both Lisps.
;
; BOZO THIS PARAGRAPH IS OUTDATED AND DEAD WRONG (please update it):
; The Verified Lisp gives two ways to write symbols.  A Plain Symbol (with no
; bar escapes) must be non-empty, must begin with a character other than 0-9 or
; quote, and may not contain: parens, periods, sharp signs, or vertical bars,
; or ASCII characters under 32.  These symbols are also case-sensitive.  An
; Escaped Symbol begins and ends with vertical bars, and may contain any
; characters (case-sensitive); backslash is an escape, i.e., \| creates a
; vertical bar and \\ creates a backslash, but all other characters stand for
; themselves.
;
; Common Lisp also has plain symbols, but with some differences.  We also would
; like to prohibit colons (because of the package system), semicolons (because
; of comments), backquotes or commas (because of quasiquotation), double quotes
; (because of string literals), backslashes (because of their special
; interpretation as an escape), amperstands (because of their use in lambda
; lists, slash (since it can lead to number confusion, e.g., 1/2), and
; lowercase characters (because Common Lisp reads symbols in a case-insensitive
; way).  We also need to prohibit dash as a first character since, e.g., -35
; could be interpreted as a number.  On the other hand, Common Lisp's
; bar-escape mechanism seems to be directly compatible with the Verified Lisp.
;
; We will use plain symbols only when the name is PLAIN_OK.
;
;   TAIL_CHAR ::= UPPERCASE_ALPHA (A-Z)
;               | DIGIT (0-9)
;               | '~' (tilde)
;   ;; NO!!     | '!' (bang)
;               | '@' (at)
;   ;; NO!!     | '$' (dollar)
;   ;; NO!!     | '%' (percent)
;               | '^' (caret)
;               | '*' (star)
;               | '-' (dash)
;               | '_' (underscore)
;               | '+' (plus)
;               | '=' (equal)
;               | '[' (square open)
;               | ']' (square close)
;               | '{' (squiggly open)
;               | '}' (squiggly close)
;               | '<' (angle open)
;               | '>' (angle close)
;               | '?' (question mark)
;
;   HEAD_CHAR ::= TAIL_CHAR other than DIGIT or '-' (dash)
;
;   PLAIN_OK ::= HEAD_CHAR TAIL_CHAR*

(defun safe-symtail-char-p (x)
  (declare (xargs :guard (characterp x)))
  (or (and (char<= #\A x) (char<= x #\Z))
      (and (char<= #\0 x) (char<= x #\9))
      (member x '(#\~ #\@ #\^ #\* #\- #\_
                  #\+ #\= #\[ #\] #\{ #\}
                  #\< #\> #\?))))

(defun safe-symtail-charlist-p (x)
  (declare (xargs :guard (character-listp x)))
  (or (atom x)
      (and (safe-symtail-char-p (car x))
           (safe-symtail-charlist-p (cdr x)))))

(defun safe-symhead-char-p (x)
  (declare (xargs :guard (characterp x)))
  (and (safe-symtail-char-p x)
       (not (eql x #\-))
       (not (and (char<= #\0 x) (char<= x #\9)))))

(defun safe-symcharlist-p (x)
  (declare (xargs :guard (character-listp x)))
  (and (consp x)
       (safe-symhead-char-p (car x))
       (safe-symtail-charlist-p (cdr x))))

(defun escape-unsafe-symcharlist (x)
  (declare (xargs :guard (character-listp x)))
  (cond ((atom x)
         nil)
        ((eql (car x) #\\)
         (list* #\\ #\\ (escape-unsafe-symcharlist (cdr x))))
        ((eql (car x) #\|)
         (list* #\\ #\| (escape-unsafe-symcharlist (cdr x))))
        (t
         (cons (car x) (escape-unsafe-symcharlist (cdr x))))))

(defthm character-listp-of-escape-unsafe-symcharlist
  (implies (character-listp x)
           (character-listp (escape-unsafe-symcharlist x))))

(defun downcase-plain-symcharlist (x)
  (declare (xargs :guard (character-listp x)))
  (cond ((atom x)
         nil)
        ((and (char<= #\A (car x))
              (char<= (car x) #\Z))
         (cons (code-char (+ (char-code #\a)
                             (- (char-code (car x))
                                (char-code #\A))))
               (downcase-plain-symcharlist (cdr x))))
        (t
         (cons (car x)
               (downcase-plain-symcharlist (cdr x))))))

(defthm character-listp-of-downcase-plain-symcharlist
  (implies (character-listp x)
           (character-listp (downcase-plain-symcharlist x))))

(defun symbol-representation (x)
  ;; Returns a string
  (declare (xargs :guard (symbolp x)))
  (let* ((name  (symbol-name x))
         (chars (coerce (the string name) 'list)))
    (if (safe-symcharlist-p chars)
        (let ((downcase-chars (downcase-plain-symcharlist chars)))
          (coerce downcase-chars 'string))
      (let* ((escaped-chars (escape-unsafe-symcharlist chars))
             (bars          (cons #\| (append escaped-chars '(#\|)))))
        (coerce bars 'string)))))

(defthm stringp-of-symbol-representation
  (stringp (symbol-representation x)))

(memoize 'symbol-representation)



(defun compatible-write-file (obj filename size)
  (declare (xargs :guard (and (stringp filename)
                              (natp size))
                  :mode :program)
           (ignorable obj filename size))
  nil)

(defttag compatible-write-file)

(progn!
 (set-raw-mode t)
 (in-package "ACL2")

 (defun compatible-write-file-scan (obj ht)

; Similar to compact-print-file-scan.  OBJ is any valid Milawa object.  HT is
; an EQL hash table, which we are destructively modifying.  The idea here is to
; decide which subterms of OBJ we would like to give #1=-style labels to when
; we do our printing.
;
; A vague goal is to assign labels when they will help to create a smaller
; printed representation.  So it would be dumb to assign a label to any subterm
; that is only used once, since, e.g., #1=FOO takes more space than FOO all by
; itself.  Furthermore, our "full events" object has on the order of 525
; million unique conses.  It seems fairly reasonable to assume that we will
; want to label something like 100+ million of these nodes, which means a label
; might typically require 8 or 9 digits (along with two sharp signs, e.g.,
; #100000000#) to reference.  So, we won't introduce labels if the symbol has
; fewer than 11 characters.
;
; Initially HT is empty.  As we encounter an object for the first time, if we
; regard it as worth labelling we bind it to :SEEN.  If we see it a second
; time, we bind it to :LABEL.  Our printing function will only label things
; that are bound to :LABEL.

   (let ((worth-labelling-p
          (cond ((consp obj)
                 t)
                ((symbolp obj)
                 (let ((name (symbol-name obj)))
                   (unless (equal obj (intern name "MILAWA"))
                     (er hard? 'compatible-write-file-scan
                         "Symbol is not in the Milawa package: ~x0." obj))
                   ;; We check length against 9 instead of 11, since we expect
                   ;; that most symbols need to be encoded and have vertical
                   ;; bars in their printed representation.
                   (>= (length name) 9)))
                ((natp obj)
                 ;; We think large enough numbers are sufficiently unlikely
                 ;; that we won't bother to label any numbers.
                 nil)
                (t
                 (er hard? 'compatible-write-file-scan
                     "Illegal object for Milawa: ~x0." obj)))))
     (when worth-labelling-p
       (let ((val (gethash obj ht)))
         (when (eq val :seen)
           ;; Not sure if we should recur into the car/cdr.  Bob doesn't in
           ;; compact-print-file-scan, so I guess I won't either.  But I haven't
           ;; thought about whether this is good.
           (setf (gethash obj ht) :label))
         (when (not val)
           (setf (gethash obj ht) :seen)
           (unless (atom obj)
             (compatible-write-file-scan (car obj) ht)
             (compatible-write-file-scan (cdr obj) ht)))))))


 (defun compatible-write-file-aux (obj ht stream free)

; Similar to COMPACT-PRINT-FILE-HELP.  OBJ is the object to write.  HT is the
; hash table that binds some objects to :SEEN and some to :LABEL.  STREAM is
; the stream we are printing to.  FREE is the lowest index that has not been
; assigned.  We return FREE'.

   (when (not obj)
     (write-char #\( stream)
     (write-char #\) stream)
     (return-from compatible-write-file-aux free))

   (let ((lookup (gethash obj ht)))
     (when (natp lookup)
       (write-char #\# stream)
       (write-string (coerce (explode-atom lookup 10) 'string) stream)
       (write-char #\# stream)
       (write-char #\Space stream)
       (return-from compatible-write-file-aux free))
     (when (eq lookup :label)
       (setf (gethash obj ht) free)
       (write-char #\# stream)
       (write-string (coerce (explode-atom free 10) 'string) stream)
       (write-char #\= stream)
       (incf free)))

   (cond ((symbolp obj)
          (write-string (symbol-representation obj) stream)
          (write-char #\Space stream))

         ((natp obj)
          (write-string (coerce (explode-atom obj 10) 'string) stream)
          (write-char #\Space stream))

         ((consp obj)
          (write-char #\( stream)
          (setq free (compatible-write-file-aux-list obj ht stream free))
          (write-char #\) stream))

         (t
          (er hard? 'compatible-write-file-aux
              "Not a valid Milawa object: ~x0" obj)))

   free)

 (defun compatible-write-file-aux-list (obj ht stream free)
   (setq free (compatible-write-file-aux (car obj) ht stream free))
   (cond ((null (cdr obj))
          free)
         ((or (atom (cdr obj))
              (let ((lookup (gethash (cdr obj) ht)))
                (or (natp lookup)
                    (eq lookup :label))))
          (progn
            (write-char #\. stream)
            (write-char #\Space stream)
            (compatible-write-file-aux (cdr obj) ht stream free)))
         (t
          (compatible-write-file-aux-list (cdr obj) ht stream free))))

 (defun compatible-write-file (obj filename size)
   ;; We can use an EQ hash table since there aren't any numbers in it.
   (let ((ht (make-hash-table :size size :test 'eq))
         (*print-base* 10))
     (time (compatible-write-file-scan obj ht))
     (with-open-file
      (stream filename
              :direction :output
              :if-exists :supersede)
      (compatible-write-file-aux obj ht stream 0)))))


(defun dumb-read-file (filename state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (channel state)
    (open-input-channel filename :object state)
    (mv-let (eofp obj state)
      (read-object channel state)
      (declare (ignore eofp))
      (let ((state (close-input-channel channel state)))
        (mv obj state)))))

#||

(in-package "ACL2")

(set-debugger-enable t)

(defun MILAWA::test-write (obj state)
  (declare (xargs :mode :program :stobjs state))
  (prog2$
   (compatible-write-file obj "test.obj" 60)
   (mv-let (read state)
     (dumb-read-file "test.obj" state)
     (prog2$ (or (equal read obj)
                 (er hard? 'test "Oops, didn't read the right result."))
             (mv read state)))))


(in-package "MILAWA")

(test-write 3 acl2::state)
(test-write 'foo acl2::state)
(test-write 'foo.bar acl2::state)
(test-write '(foo.bar . foo.bar) acl2::state)
(test-write '(foo foo (foo . foo) bar bar (foo . foo) . (foo . foo)) acl2::state)


||#