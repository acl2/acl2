; Copyright (C) 2013, Regents of the University of Texas
; Written by J Strother Moore, February, 2013
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; A Utility for Comparing the .out Files Produced during Book Certification

; To recertify:
; (certify-book "compare-out-files")

; Basic Design Goals

; This utility is for comparing the time performance of two runs of ACL2 across
; two sets of nearly identical books.  For example, suppose have a directory
; dir1 containing a set of books and another directory dir2 containing a near
; copy of that set of books.  Suppose not only that both sets of books certify
; successfully but for each book a .out file was produced for each
; certification, containing the session log for the certification.  (If when
; you installed your acl2 you did `make regression' to re-certify the community
; books, then you will see sample .out files for each book.)  Suppose you'd
; like to compare the times taken for ``matching'' events in the two
; certification runs of each .out, where by ``matching'' we mean events with
; the same name.  Then you can do this:

; (include-book "system/compare-out-files" :dir :system)

; (compare-out-files
;   "dir1"                      ; `benchmark' books directory
;   "dir2"                      ; `contender' books directory
;   list-of-books               ; list of book names
;   n                           ; number of examples of best and worst to collect
;   k                           ; cutoff -- ignore events taking less time than this
;   state  )                    ;           time measured in centiseconds

; This will print a supposedly self-explanatory comparison of all the books.

; Example call:
; (compare-out-files
;  "/u/moore/work/v5-0/acl2-sources/books/"            ; benchmark books directory
;  "/u/moore/work/v6-0/acl2-sources/books/"            ; contender books directory
;  '("arithmetic-3/bind-free/arithmetic-theory"        ; list of book names to compare
;    "arithmetic-3/bind-free/banner"
;    "arithmetic-3/bind-free/basic-helper"
;    "arithmetic-3/bind-free/basic"
;    "arithmetic-3/bind-free/building-blocks"
;    "arithmetic-3/bind-free/collect"
;    "arithmetic-3/bind-free/common"
;    "arithmetic-3/bind-free/default-hint"
;    "arithmetic-3/bind-free/integerp-meta"
;    "arithmetic-3/bind-free/integerp"
;    "arithmetic-3/bind-free/mini-theories-helper"
;    "arithmetic-3/bind-free/mini-theories"
;    "arithmetic-3/bind-free/normalize"
;    "arithmetic-3/bind-free/numerator-and-denominator"
;    "arithmetic-3/bind-free/remove-weak-inequalities"
;    "arithmetic-3/bind-free/simplify-helper"
;    "arithmetic-3/bind-free/simplify"
;    "arithmetic-3/bind-free/top"
;    "arithmetic-3/extra/ext"
;    "arithmetic-3/extra/top-ext"
;    "arithmetic-3/floor-mod/floor-mod"
;    "arithmetic-3/floor-mod/mod-expt-fast"
;    "arithmetic-3/pass1/basic-arithmetic-helper"
;    "arithmetic-3/pass1/basic-arithmetic"
;    "arithmetic-3/pass1/expt-helper"
;    "arithmetic-3/pass1/expt"
;    "arithmetic-3/pass1/inequalities"
;    "arithmetic-3/pass1/mini-theories"
;    "arithmetic-3/pass1/non-linear"
;    "arithmetic-3/pass1/num-and-denom-helper"
;    "arithmetic-3/pass1/numerator-and-denominator"
;    "arithmetic-3/pass1/prefer-times"
;    "arithmetic-3/pass1/top"
;    "arithmetic-3/top")
;   5                                                  ; number-of-extrema
;  10                                                  ; cutoff = 0.10 seconds
;  state)

; At the end of this file is the (supposedly self-explanatory) output for the
; example above.  We suggest you look at this output before bothering to run
; this utility, just to confirm it provides the information you're wanting.

; The two sets of books should be nearly the same because this utility compares
; events with the same names.  It doesn't help much to compare two .out files
; with different events in them!  Unmatched events are ignored, as are books
; that exist in one of the directories but not the other.

; All times reported are in CENTISECONDS.  So 1 second is reported as 100.

; --- Implementation Details Unimportant to the User ---

; We do this is multiple passes.  The first pass collects a list of ``records''
; (s-expressions), one for each book listed in a certain list.  The records are
; essentially a parsed version of the Summaries in the .out files on the two
; directories.  The most useful part of these records is another list of
; records, one of each event in the two books.  In subsequent passes we crawl
; over the list of book records and the lists of event records within them and
; collect various statistics.

; In an abuse of nomenclaure we call the record for a book a ``book'' and the
; record for an event an ``event''.  Both kinds of records contain times taken
; for that book or event in BOTH systems.  E.g., an event record lists the
; times taken by that event in the benchmark system and in the contender
; system.

; A book is:

; (file                                     ; See explanation below
;  (:MISSING-REPORT report)
;  (:CERTIFICATION-TIMES Tm1 Tm2 (ct1 ct2))
;  (:MATCHED-EVENTS mlst)
;  (:UNMATCHED-EVENTS umlst))

; An event is:

; (cmd
;  name
;  tm1 tm2
;  file)

; Explanation: In a book record, file is a string filename, e.g.,
; "ihs/quotient-remainder-lemmas" of a certified book from dir1 and/or dir2.
; Report is nil if the .cert and .out [or .cert.out] files were found on both
; directories.  Otherwise, report is a non-nil explanation of what's missing.
; Tm1 and Tm2 are the summed Times recovered from the .out files on dir1 and
; dir2, respectively.  Those times include ALL events found except those in
; *ignored-events*, below.  We believe Tm1 and Tm2 are better
; approximations of the actual time take to do the certification than the times
; reported for the final CERTIFY-BOOK events.  Those times are ct1 and ct2 but
; the ``reported'' certification times are otherwise ignored by this tool.  All
; times are in centiseconds.  Finally, mlst and umlst are lists of matched and
; unmatched events, as per below.  They include ALL events recovered from the
; two .out files.

; In an event event record, cmd is an ACL2 command, e.g., DEFTHM or DEFUN, etc.
; There may be unrecognized commands and they have cmd ???.  Name is the
; ``name'' of the event, as a string.  Some events do not have meaningful
; names.  Tm1 and tm2 are times recovered from the Time lines of the two .out
; files.  File is the filename string.

; A ``matched'' event is one with two non-nil times.  An ``unmatched'' event is
; one with a ``time'' of NIL in one slot or the other.  If an unmatched event
; contains NIL in time slot i then the event was not recovered from the
; diri/filename.out file.

; All of this information is recovered from the Summary blocks of the .out files.
; A summary block looks like this:

; Summary
; Form:  ( DEFTHM ASSOC-OF-AP ...)
; Rules: (...
;         ...)
; Time: xx.xx (...)

; The event corresponding to this would be:
; (DEFTHM                         ; cmd
; "ASSOC-OF-AP"                   ; name
;  xxxx1 xxxx2                    ; centiseconds reported by dir1 and dir2
;  "misc/lemmas-about-ap")        ; filename

; After running the compare-out facility, the list of books (containing their
; matched and unmatched events) is stored in the state global variable books.
; Thus, (@ books) will deliver a parsed version of the raw data of all files
; listed.  Note that this raw data is independent of cutoff, number-of-extrema,
; and the *probably-irrelevant-events*.  It just lists everything parsed out of
; the .out files.

; --- the rest of the comments might need editing for Version 6 of this ---

; (1) The most important piece of information is the time taken by both
; systems.  By ``time'' we mean the sum of the reported CERTIFY-BOOK times.  We
; don't count every book found but every book found certified and with .out
; files present on BOTH directories.

; (2) We report the 5 books with the worst performance by the contender and the
; 5 books with the best performance.

; (3) We report the 5 events with the worst performance and the 5 events with
; the best performance.

; The number ``5'' used above is really a variable, number-of-extrema.

; For the purposes of identifying best and worst, we avoid books and events
; that take less than 100 centiseconds.  This cutoff is actually a variable,
; named cutoff.

; We ignore certain events because their times include the times printed in
; other summaries.  These events are listed in the constant
; *ignored-events*.

; We rank best and worst two ways:  percent change and absolute difference.
; So (2), above is really four lists of 5:
; - worst 5 books by percentage change
; - best 5 books by percentage change
; - worst 5 books by absolute time difference
; - best 5 books by absolute time difference

; Similarly, (3) is really four lists of 5, listing events.

; We first preprocess all the books and collect a ``performance book'' for each
; book.  This list of books actually has much more information in it than we
; need to answer the 3 main questions above.  But we code it this way to make
; it easier to add further questions later.

; For every book we collect the following information.  Abuse Warning: We call
; this structure a ``book.''


; We compute these quantities individually to keep this code simple.  Once upon
; a time we computed everything in a single pass through the pairs but that
; just became too difficult to modify as we learned we wanted additional
; information.

; In order to use this code, the ``relevant'' events have to have Summaries
; that look like this (skipping the semi-colon and space leading each line
; below):

; Time:  xxx.xx <rest of line irrelevant>
; Prover steps <rest of line irrelevant>
; name

; where xxx.xx has 2 digits to the right of the decimal point.  If name is T,
; NIL, ||, a number, or starts with an open parenthesis or a string quote, we
; ignore this Summary.  If name starts with a space and then a string quote, we
; read the string as a string.  That is generally the last summary in an .out
; file and names the book just certified.

(in-package "ACL2")
(program)
(set-state-ok t)

; The typical Summary block looks like this:

; Summary
; Form:  ( DEFTHM ASSOC-OF-AP ...)
; Rules: (...
;         ...)
; Time: xx.xx (...)

; We have to recover the Form and the Time from each of these Summary blocks.

; We first scan until we find "Form: ".  Then we read the form as a pair.  We
; would read the example form above as (DEFTHM . "ASSOC-OF-APP").  Typically,
; the car of this pair is an ACL2 event command name like DEFUN or DEFTHM,
; although we do not recognize all possible commands and just code some (e.g.,
; PROGN, MAKE-EVENT, and ENCAPSULATE) with the symbol ???.

; Name is a string because we don't want to parse such symbolic names as |(x *
; y) = (* y x)| or VL::X4321.  So we read a maximum of 100 characters, looking
; for "<return>Rules:".  Having identified the <return> at the end of the Form
; line, we back up past the closing paren.  There is always some ``noise''
; between the ``user-supplied name'' and the closing paren and <return>.
; This noise ususally takes the form of elipses and closing parens, as in:

; Form:  ( DEFTHM ASSOC-OF-APP ...)
; Form:  ( IN-THEORY (DISABLE ...))
; Form:  ( MUTUAL-RECURSION ( DEFUN EVL ...) ...)
; Form:  ( PROGN (DEFUN AUTOHIDE-CP ...) ...)
; Form:  ( ENCAPSULATE NIL (LOCAL ...) ...)

; As we read the 100 (max) character to the "<return>Rules:" line we accumulate
; the characters read (in reverse order) onto a list and keep inspecting that
; list to see if we've read the characters of this terminal string.  Once we
; have that list of characters, we try to strip off noise to recover an event
; command (as a symbol) and a user-supplied name (as a string).  If we fail, we
; use the ``command'' symbol ??? and the entire line as the ``name'' string.

(defun scan-to-form1 (c1 c2 c3 c4 c5 c6 channel state)

; We return (mv flg state), where flg indicates wehther we are now positioned
; after "Form:  ".  When flg is nil, it means we read to EOF.

  (mv-let (c7 state)
          (read-char$ channel state)
          (cond ((eql c7 nil) (mv nil state))
                ((and (eql c1 #\F)
                      (eql c2 #\o)
                      (eql c3 #\r)
                      (eql c4 #\m)
                      (eql c5 #\:)
                      (eql c6 #\Space)
                      (eql c7 #\Space))
                 (mv t state))
                (t (scan-to-form1 c2 c3 c4 c5 c6 c7 channel state)))))

(defun scan-to-form (channel state)

; Scan to the next "Form: " and return (mv flg state), where flg indicates
; whether we found that string.  If not, flg is nil and we read to the eof.

  (scan-to-form1 nil nil nil nil nil nil channel state))

(defun whitespacep (char)
  (or (eql char #\Space)
      (eql char #\Newline)
      (eql char #\Tab)))

(defun chop-leading-whitespace (lst)
  (cond ((endp lst) nil)
        ((whitespacep (car lst))
         (chop-leading-whitespace (cdr lst)))
        (t lst)))

(defun char-matchp (pat lst)
  (cond ((endp pat) t)
        ((endp lst) nil)
        ((eql (car pat) :whitespace)
         (and (whitespacep (car lst))
              (char-matchp (cdr pat) (cdr lst))))
        (t (and (eql (car pat) (car lst))
                (char-matchp (cdr pat) (cdr lst))))))

(defun len-of-whitespace (lst)
  (cond ((endp lst) 0)
        ((whitespacep (car lst))
         (+ 1 (len-of-whitespace (cdr lst))))
        (t 0)))

(defun len-of-standard-ending (lst)

; Lst is reversed.  In the standard ending, the last chars read will be

; <whitespace>...))    -or- <whitespace>...)
; <return>Rules:

; (So the colon is in the car of lst.)  We compute the length of this standard
; ending so we can chop it off before reversing lst.  Returning 0 means the
; ending is not standard -- as would happen if we failed to find the end before
; running out of buffer space.

  (cond ((char-matchp '(#\: #\s #\e #\l #\u #\R  #\Newline) lst)
         (let ((lst1 (nthcdr 7 lst)))
           (cond ((char-matchp '(#\) #\. #\. #\. ) lst1)
                  (let ((lst1 (nthcdr 4 lst1)))
                    (+ 7 4 (len-of-whitespace lst1))))
                 ((char-matchp '(#\) #\) #\. #\. #\. ) lst1)
                  (let ((lst1 (nthcdr 5 lst1)))
                    (+ 7 5 (len-of-whitespace lst1))))
                 (t 7))))
        (t 0)))

(defun parse-rev-lst-into-pairs1 (symbols)

; This is an ugly hack.  For each <symbol> in symbols, we lay down code to test
; whether the characters in the built-in variable name REV-LST are #\( #\Space
; <chars-in-symbol> and if so make a pair with <symbol> as its car and the rest
; of the chars in REV-LST -- coerced to a string -- as its cdr.  However,
; CERTIFY-BOOK is different because it is printed without the #\Space after the
; open paren and is known to have a string as its next arg so we get rid of the
; leading and trailing string quotes.  INCLUDE-BOOK and DEFPKG are different
; because they have strings as their next args and we eliminate their string
; quotes too.  THEORY-INVARIANT is different because there is no open paren or
; space or name!  THM is different because there is no space after the standard
; ending.

  (cond
   ((endp symbols)
    '((t (cons '??? (coerce rev-lst 'string)))))
   ((eq (car symbols) 'CERTIFY-BOOK)
; Certify-book is different from the others because the leading space is absent.
    (cons
     `((char-matchp '(#\( ; #\Space
                      ,@(coerce (symbol-name (car symbols)) 'list)
                      :whitespace)
                    rev-lst)
       (cons ',(car symbols)
             (coerce
              (cdr
               (chop-leading-whitespace
                (nthcdr ,(+ 1 (length (symbol-name (car symbols))))
                        (all-but-last rev-lst))))
              'string)))
     (cons `((char-matchp '(#\( ; #\Space
                            #\A #\C #\L #\2 #\: #\:
                            ,@(coerce (symbol-name (car symbols)) 'list)
                            :whitespace)
                          rev-lst)
             (cons ',(car symbols)
                   (coerce
                    (cdr
                     (chop-leading-whitespace
                      (nthcdr ,(+ 7 (length (symbol-name (car symbols))))
                              (all-but-last rev-lst))))
                    'string)))
           (parse-rev-lst-into-pairs1 (cdr symbols)))))
   ((member-eq (car symbols) '(INCLUDE-BOOK DEFPKG))
    (cons
     `((char-matchp '(#\( #\Space
                      ,@(coerce (symbol-name (car symbols)) 'list)
                      :whitespace)
                    rev-lst)
       (cons ',(car symbols)
             (coerce
              (cdr
               (chop-leading-whitespace
                (nthcdr ,(+ 2 (length (symbol-name (car symbols))))
                        (all-but-last rev-lst))))
              'string)))
     (cons `((char-matchp '(#\( #\Space #\A #\C #\L #\2 #\: #\:
                            ,@(coerce (symbol-name (car symbols)) 'list)
                            :whitespace)
                          rev-lst)
             (cons ',(car symbols)
                   (coerce
                    (cdr
                     (chop-leading-whitespace
                      (nthcdr ,(+ 8 (length (symbol-name (car symbols))))
                              (all-but-last rev-lst))))
                    'string)))
           (parse-rev-lst-into-pairs1 (cdr symbols)))))
   ((member-eq (car symbols) '(THEORY-INVARIANT))
    (cons
     `((char-matchp '(,@(coerce (symbol-name (car symbols)) 'list))
                    rev-lst)
       (cons ',(car symbols)
             (coerce (chop-leading-whitespace
                      (nthcdr ,(length (symbol-name (car symbols)))
                              rev-lst))
                     'string)))
     (cons `((char-matchp '(#\A #\C #\L #\2 #\: #\:
                            ,@(coerce (symbol-name (car symbols)) 'list))
                          rev-lst)
             (cons ',(car symbols)
                   (coerce (chop-leading-whitespace
                            (nthcdr ,(+ 6 (length (symbol-name (car symbols))))
                                    rev-lst))
                           'string)))
           (parse-rev-lst-into-pairs1 (cdr symbols)))))
   ((member-eq (car symbols) '(THM))
    (cons
       `((char-matchp '(#\( #\Space
                        ,@(coerce (symbol-name (car symbols)) 'list))
                      rev-lst)
         (cons ',(car symbols)
               (coerce (chop-leading-whitespace
                        (nthcdr ,(+ 2 (length (symbol-name (car symbols))))
                                rev-lst))
                       'string)))
       (cons `((char-matchp '(#\( #\Space #\A #\C #\L #\2 #\: #\:
                              ,@(coerce (symbol-name (car symbols)) 'list))
                            rev-lst)
               (cons ',(car symbols)
                     (coerce (chop-leading-whitespace
                              (nthcdr ,(+ 8 (length (symbol-name (car symbols))))
                                      rev-lst))
                             'string)))
             (parse-rev-lst-into-pairs1 (cdr symbols)))))
   (t (cons
       `((char-matchp '(#\( #\Space
                        ,@(coerce (symbol-name (car symbols)) 'list)
                        :whitespace)
                      rev-lst)
         (cons ',(car symbols)
               (coerce (chop-leading-whitespace
                        (nthcdr ,(+ 2 (length (symbol-name (car symbols))))
                                rev-lst))
                       'string)))
       (cons `((char-matchp '(#\( #\Space #\A #\C #\L #\2 #\: #\:
                              ,@(coerce (symbol-name (car symbols)) 'list)
                              :whitespace)
                            rev-lst)
               (cons ',(car symbols)
                     (coerce (chop-leading-whitespace
                              (nthcdr ,(+ 8 (length (symbol-name (car symbols))))
                                      rev-lst))
                             'string)))
             (parse-rev-lst-into-pairs1 (cdr symbols)))))))

(defmacro parse-rev-lst-into-pairs (symbols)
  `(cond ,@(parse-rev-lst-into-pairs1 symbols)))

; Read-form-as-pair1 reads and accumulates chars until the "<return>Rules:".
; It then passes the accumulated list to read-form-as-pair2 which strips off
; the "<return>Rules:" ``standard ending'' including the typical "...)" noise
; and then parses the rest as (cmd . string).

(defun read-form-as-pair2 (lst)
  (let* ((k (len-of-standard-ending lst))
         (rev-lst (revappend (nthcdr k lst) nil)))
    (parse-rev-lst-into-pairs
     (DEFTHM DEFUN MUTUAL-RECURSION DEFMACRO DEFCONST DEFLABEL
       DEFDOC DEFPKG CERTIFY-BOOK INCLUDE-BOOK IN-THEORY DEFTHEORY THM
       TABLE THEORY-INVARIANT VERIFY-GUARDS DEFATTACH DEFAXIOM DEFSTOBJ
       ENCAPSULATE PROGN PROGN! MAKE-EVENT))))

(defun read-form-as-pair1 (channel state k lst)
  (cond ((zp k) (mv (read-form-as-pair2 lst) state))
        (t (mv-let
            (char state)
            (read-char$ channel state)
            (cond
             ((null char)
              (cond
               ((null lst) (mv nil state))
               (t (mv (read-form-as-pair2 lst) state))))
             ((eql char #\:)
; If we just read "<return>Rules:", stop.
              (cond ((char-matchp '(#\s #\e #\l #\u #\R #\Newline)
                                  lst)
                     (mv (read-form-as-pair2 (cons #\: lst)) state))
                    (t (read-form-as-pair1 channel state (- k 1) (cons char lst)))))
             (t (read-form-as-pair1 channel state (- k 1) (cons char lst))))))))

(defun read-form-as-pair (channel state)
  (read-form-as-pair1 channel state 100 nil))

; Next we scan past "Time:  " and read a rational

(defun scan-to-time1 (c1 c2 c3 c4 c5 c6 channel state)

; We return (mv flg state), where flg indicates whether we are now positioned after "Time:  ".
; When flg is nil, it means we read to EOF.

  (mv-let (c7 state)
          (read-char$ channel state)
          (cond ((eql c7 nil) (mv nil state))
                ((and (eql c1 #\T)
                      (eql c2 #\i)
                      (eql c3 #\m)
                      (eql c4 #\e)
                      (eql c5 #\:)
                      (eql c6 #\Space)
                      (eql c7 #\Space))
                 (mv t state))
                (t (scan-to-time1 c2 c3 c4 c5 c6 c7 channel state)))))

(defun scan-to-time (channel state)
  (scan-to-time1 nil nil nil nil nil nil channel state))

(defun read-rational1 (num den channel state)
  (mv-let (char state)
          (read-char$ channel state)
          (cond ((eql char #\.)
                 (cond ((null den)
                        (read-rational1 num 1 channel state))
                       (t (mv nil state))))
                ((member char '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
                 (read-rational1 (+ (- (char-code char) 48) (* num 10))
                                 (if den (* 10 den) den)
                                 channel state))
                (t (mv (/ num (if den den 1)) state)))))

(defun read-rational (channel state)

; Read successive chars until a space (or any other nondecimal char) and parse
; them as the decimal representation of a rational x.  For example, we read
; "1234.567" as 1234567/1000. Return (mv x state), where x is nil if the
; characters do not parse as a decimal.

  (read-rational1 0 nil channel state))

(defun get-form-time-pair (channel state)

; We search through the open character input channel for the next Summary block
; and return (mv `((cmd . "name-as-string") . time-in-centiseconds) state),
; where cmd is one of several recognized primitive commands (e.g., DEFUN,
; DEFTHM, etc) or ??? for unrecognized commands.  The first result is nil
; upon reaching eof.

  (mv-let
   (flg state)
   (scan-to-form channel state)
   (cond
    ((null flg) (mv nil state))
    (t (mv-let
        (pair state)
        (read-form-as-pair channel state)
        (cond
         ((null pair) (mv nil state))
         (t (mv-let
             (x state)
             (scan-to-time channel state)
             (cond
              ((null x) (mv nil state))
              (t (mv-let
                  (rat state)
                  (read-rational channel state)
                  (cond
                   ((null rat) (mv nil state))
                   (t (mv (cons pair (floor (+ 1/2 (* 100 rat)) 1)) state))))))))))))))

(defun get-form-time-pairs1 (lst channel state)
  (mv-let (pair state)
          (get-form-time-pair channel state)
          (cond ((null pair) (mv (revappend lst nil) state))
                (t (get-form-time-pairs1 (cons pair lst) channel state)))))

(defun open-out-or-cert-out-channel (dir book state)
  (let ((file (concatenate 'string dir book ".out")))
    (mv-let (ch state)
            (open-input-channel file :character state)
            (cond
             (ch (mv ch state))
             (t (let ((file (concatenate 'string dir book ".cert.out")))
                  (mv-let (ch state)
                          (open-input-channel file :character state)
                          (cond
                           (ch (mv ch state))
                           (t  (mv nil state))))))))))

(defun get-form-time-pairs (dir book state)
  (mv-let (ch state)
          (open-out-or-cert-out-channel dir book state)
          (cond
           (ch (mv-let (pairs state)
                       (get-form-time-pairs1 nil ch state)
                       (let ((state (close-input-channel ch state)))
                         (mv pairs state))))
           (t (mv nil state)))))

(defun last-pairs-are-same-certify-booksp (book pairs1 pairs2)

; Pairs1 and pairs2 are the form-time pairs recovered from the .out files
; associated with the two certifications of file.  We expect the last such pair
; in each list to be a certify-book pair.  We check that they are and do not
; consider the two lists of pairs comparable if they're not.  We do not insist
; that the file named in each final pair is book, book generally includes the
; path down to a particular .lisp file and the pairs only contain the most
; immediate name of the books.

  (declare (ignore book))
  (cond
   ((or (endp pairs1)
        (endp pairs2))
    nil)
   (t
    (let* ((pair1 (car (last pairs1)))
           (pair2 (car (last pairs2)))
           (form1 (car pair1))
           (form2 (car pair2)))
      (and (consp form1)
           (eq (car form1) 'CERTIFY-BOOK)
           (stringp (cdr form1))
           (consp form2)
           (eq (car form2) 'CERTIFY-BOOK)
           (stringp (cdr form2))

; We don't actually check that both certify-books are for book!  The problem is
; that that our variable book is bound to something like "arithmetic/mod-gcd"
; whereas the cdr of the two forms is something like "mod-gcd".

           (equal (cdr form1) (cdr form2))
           )))))

; The fields of a book record:
;  (:MISSING-REPORT missing-report)          ; nil if the book is found on both dirs; else
;                                            ; an explanation

(defun missing-report (dir1 dir2 book state)

; Prior to computing one-dirp we must confirm that the .cert and .out files exist.  If they
; do, we return nil; if something is missing, we try to explain.

  (let* ((file1 (concatenate 'string dir1 book ".cert"))
         (file2 (concatenate 'string dir2 book ".cert")))
    (mv-let
     (exists1 state)
     (open-input-channel file1 :character state)
     (mv-let
      (exists2 state)
      (open-input-channel file2 :character state)
      (let* ((state (if exists1 (close-input-channel exists1 state) state))
             (state (if exists2 (close-input-channel exists2 state) state)))
        (cond
         ((and (null exists1)
               (null exists2))
          (mv '(:cert-missing-from :both) state))
         ((null exists1)
          (mv '(:cert-missing-from 1) state))
         ((null exists2)
          (mv '(:cert-missing-from 2) state))
         (t
          (mv-let
           (ch1 state)
           (open-out-or-cert-out-channel dir1 book state)
           (mv-let
            (ch2 state)
            (open-out-or-cert-out-channel dir2 book state)
            (let* ((state (if ch1 (close-input-channel ch1 state) state))
                   (state (if ch2 (close-input-channel ch2 state) state)))
              (cond
               ((and (null ch1)
                     (null ch2))
                (mv '(:out-and-cert-out-missing-from :both) state))
               ((null ch1)
                (mv '(:out-and-cert-out-missing-from 1) state))
               ((null ch2)
                (mv '(:out-and-cert-out-missing-from 2) state))
               (t (mv nil state)))))))))))))

;  (:CERTIFICATION-TIMES tm1 tm2 (ct1 ct2))

(defconst *ignored-events*

; These events have the property that their sub-events have their own Summary
; blocks.  For example, an ENCAPSULATE consisting of 3 DEFTHMs causes four
; Summary blocks to appear in the .out file: a Summary block for each DEFTHM
; followed by a Summary block for the encapsulate itself.  The time for the
; ENCAPSULATE includes the times of the component DEFTHMs.  The ENCAPSULATE
; summary will, of course, include additional time for the second pass, but we
; cannot tell from the .out file which previously parsed summaries ``belong''
; to the ENCAPSULATE so we cannot adjust the ENCAPSULATE time to correct for
; the double-counting of the DEFTHM events.  So we just ignore ENCAPSULATE
; events and content ourselves to analyze only their constituents events.

  '(ENCAPSULATE PROGN PROGN! CERTIFY-BOOK MAKE-EVENT))

(defun certification-time1 (pairs ans ct)
  (cond
   ((endp pairs) (mv ans ct))
   ((eq (car (car (car pairs))) 'certify-book)
    (certification-time1 (cdr pairs) ans (cdr (car pairs))))
   ((member-eq (car (car (car pairs))) *ignored-events*)
    (certification-time1 (cdr pairs) ans ct))
   (t (certification-time1 (cdr pairs)
                           (+ (cdr (car pairs)) ans)
                           ct))))

(defun certification-time (pairs)

; We return (mv tm ct).  Tm is the sum of the times of all pairs except the
; *ignored-events* and CERTIFY-BOOK.  Ct is the time reported in the
; last pair, which is known to be a CERTIFY-BOOK pair.  Times are in
; centiseconds.

  (certification-time1 pairs 0 0))

; The remaining components depend on the identification of matched events.
; That is, to compute them we need to know which elements of pairs1 and pairs2
; correspond to the same entry in the book and which are unique to one
; directory or the other.  So first we define the basic function that pairs off
; corresponding pairs and converts form-time pairs to matched and unmatched
; events.

; Recall the distinction between form-time pairs and our ``events.''  An event,
; here, actually is a combination of two matching pairs: (cmd name tm1 tm2
; book).  Unmatched events are like events except one of the tm fields is nil
; indicating that the event came from the other directory.

(defun convert-form-time-pair-to-unmatched-event (file i pair)

; I is the number, 1 or 2, of the directory from which this pair comes.  If i
; is 1, pair comes from Summary block in dir1/file; otherwise it comes from
; dir2/file.  We don't actually need dir1 or dir2 here.  An unmatched pair is
; (cmd name tm1 tm2 file), where tm1 or tm2 is nil.  For example, (DEFTHM
; "LEMMA-43-HACK" nil 220 "support") means LEMMA-43-HACK was found in
; dir2/support.out but not in dir1/support.out, and that the lemma took 2.20
; seconds (220 centiseconds) to prove.

  (if (equal i 1)
      (list (caar pair) (cdar pair) (cdr pair) nil file)
      (list (caar pair) (cdar pair) nil (cdr pair) file)))

(defun convert-form-time-pairs-to-unmatched-events (file i pairs unmatched-events)
  (cond ((endp pairs) unmatched-events)
        (t (convert-form-time-pairs-to-unmatched-events
            file i (cdr pairs)
            (cons (convert-form-time-pair-to-unmatched-event file i (car pairs))
                  unmatched-events)))))

; The following function computes two results, called mlst and umlst for
; ``matched events'' and ``unmatched events''.

;  (:MATCHED-EVENTS mlst)
;  (:UNMATCHED-EVENTS umlst)

(defun convert-form-time-pairs-to-events (file pairs1 pairs2 matched-events unmatched-events)

; We map through the two lists of pairs in tandem, create events for matching
; pairs and accumulate them (in reverse order) onto matched-events and create
; unmatched events for unmatched pairs and accumulate them (in reverse order)
; on unmatched-events.

  (cond
   ((endp pairs1)
    (mv (revappend matched-events nil)
        (revappend
         (convert-form-time-pairs-to-unmatched-events file 2 pairs2 unmatched-events)
         nil)))
   (t (let* ((pair1 (car pairs1))
             (pair2 (assoc-equal (car pair1) pairs2)))
        (cond
         (pair2 ; (car pair1) and (car pair2) are equal
          (convert-form-time-pairs-to-events
           file
           (cdr pairs1)
           (remove1-equal pair2 pairs2)
           (cons (list (caar pair1) (cdar pair1) (cdr pair1) (cdr pair2) file)
                 matched-events)
           unmatched-events))
         (t (convert-form-time-pairs-to-events
             file
             (cdr pairs1)
             pairs2
             matched-events
             (cons (convert-form-time-pair-to-unmatched-event file 1 pair1)
                   unmatched-events))))))))

(defun book-maker (dir1 dir2 file state)

; Recall that a book for file is:
; (file
;  (:MISSING-REPORT missing-report)
;  (:CERTIFICATION-TIMES Tm1 Tm2 ct1 ct2)
;  (:MATCHED-EVENTS mlst)
;  (:UNMATCHED-EVENTS umlst))
; where the none of the fields after the first are present if there is a
; non-nil missing-report.

  (mv-let
   (missing-report state)
   (missing-report dir1 dir2 file state)
   (cond
    (missing-report
     (mv `(,file (:MISSING-REPORT ,missing-report)) state))
    (t
     (mv-let
      (pairs1 state)
      (get-form-time-pairs dir1 file state)
      (mv-let
       (pairs2 state)
       (get-form-time-pairs dir2 file state)
       (cond
        ((not (last-pairs-are-same-certify-booksp file pairs1 pairs2))
         (mv `(,file (:MISSING-REPORT (:pairs-do-not-end-in-same-certify-books)))
             state))
        (t
         (mv-let
          (Tm1 ct1)
          (certification-time pairs1)
          (mv-let
           (Tm2 ct2)
           (certification-time pairs2)
           (mv-let
            (matched-events unmatched-events)
            (convert-form-time-pairs-to-events file pairs1 pairs2 nil nil)
            (mv `(,file
                  (:MISSING-REPORT nil)
                  (:CERTIFICATION-TIMES ,Tm1 ,Tm2 (,ct1 ,ct2))
                  (:MATCHED-EVENTS ,matched-events)
                  (:UNMATCHED-EVENTS ,unmatched-events))
                state))))))))))))

(defun book-makers (dir1 dir2 files state ans)
  (cond
   ((endp files)
    (mv (revappend ans nil) state))
   (t (mv-let (book state)
              (book-maker dir1 dir2 (car files) state)
              (book-makers dir1 dir2 (cdr files) state (cons book ans))))))

(defun tm (i x)

; x is either a book record or an event record.  We can tell the difference
; because only book records contain a string as the car.  We access tm1 or
; tm2 according to whether i is 1 or 2.

  (cond ((stringp (car x))
         (nth i (assoc-eq :CERTIFICATION-TIMES (cdr x))))
        (t (nth (+ 1 i) x))))

(defun score (relp x cutoff)

; x is either a book or an event.  In either case, we recover the two times,
; tm1 and tm2, from x and then compute the relative or absolute score,
; depending on relp.  If both times are insignificantly small (given cutoff) we
; return nil instead of a numeric score.

; If you change the filter below identifying significant events, change it in
; length-significant-matched-events and sum-significant-matched-events1.  I
; don't define the predicate significant-eventp because it would need to
; operate, below, on books or events.

  (let ((tm1 (tm 1 x))
        (tm2 (tm 2 x)))
    (cond ((or (null tm1)
               (null tm2)
               (and (<= tm1 cutoff)
                    (<= tm2 cutoff))
               (member-eq (car x) *ignored-events*))
           nil)
          (relp (/ (- tm1 tm2) (if (equal tm1 0) 1 tm1)))
          (t    (- tm1 tm2)))))

(defun collect-extrema1 (biggestp score x scored-lst)

; We add (score . x) to a similar list of pairs, scored-lst, in sorted order.
; However the order is ascending if biggestp is t and descending if biggestp is
; nil.  Think of this scored-lst as the ordered sequence of the k biggest or
; smallest values seen so far and assume that (score . x) is supposed to be
; added to it.

  (cond ((endp scored-lst) (list (cons score x)))
        ((if biggestp
             (< score (car (car scored-lst)))
             (> score (car (car scored-lst))))
         (cons (cons score x) scored-lst))
        (t (cons (car scored-lst)
                 (collect-extrema1 biggestp score x (cdr scored-lst))))))

(defun collect-extrema (biggestp score x scored-lst len bound k)

; Scored-lst is a list of pairs.  The car of each pair is a numeric score and
; in the cdr is some item with that score.  Think of scored-lst as the list of
; the k biggest (or smallest) items seen so far.  We wish, possibly, to add
; (score . x) to it while maintaining the invariant that the result contains no
; more than k items and that they are the biggest (smallest) we've seen so far.
; Scored-lst is ordered ascending if biggestp is t and is ordered descending if
; biggestp is nil.  Len is the length of scored-lst.  Bound is the smallest
; score currently in scored-lst (if biggestp is t) or the largest score in
; scored-lst (if biggestp is nil).  K is the maximum length scored-lst can
; attain.  We return (mv scored-lst' len' bound').

  (cond
   ((< len k)
    (let ((scored-lst1 (collect-extrema1 biggestp score x scored-lst)))
      (mv scored-lst1 (+ 1 len) (car (car scored-lst1)))))
   ((and bound (if biggestp (<= score bound) (>= score bound)))
    (mv scored-lst len bound))
   (t (let ((scored-lst1 (collect-extrema1 biggestp score x (cdr scored-lst))))
        (mv scored-lst1 len (car (car scored-lst1)))))))

(defun map-collect-extrema-over-list
  (biggestp relp lst scored-lst len bound k cutoff)

; Lst is a list of either books or events (depending on bookp).  Scored-lst
; is a list of the at most k largest or smallest (as per biggestp) items seen
; so far (with len being the length of scored-lst and bound being the smallest
; or largest item in scored-lst).  We compute the score (relative or absolute,
; as per relp, of the significantly large (as per cutoff) items in lst and
; possibly add each to scored-lst if it deserves collecting.  We return (mv
; scored-lst' len' bound').

  (cond
   ((endp lst)
    (mv scored-lst len bound))
   (t (let ((score (score relp (car lst) cutoff)))
        (cond
         (score
          (mv-let
           (scored-lst len bound)
           (collect-extrema
            biggestp
            score
            (if (stringp (car (car lst))) ; is this a book?
                (list (car (car lst))
                      (tm 1 (car lst))
                      (tm 2 (car lst))
                      (nth 3 (assoc-eq :certification-times (cdr (car lst)))))
                (car lst))
            scored-lst len bound k)
           (map-collect-extrema-over-list biggestp relp (cdr lst)
                                          scored-lst len bound
                                          k cutoff)))
         (t (map-collect-extrema-over-list biggestp relp (cdr lst)
                                           scored-lst len bound
                                           k cutoff)))))))
(defun map-collect-extrema-over-list-list
  (biggestp relp books scored-lst len bound k cutoff)
  (cond
   ((endp books)
    (mv scored-lst len bound))
   (t (mv-let (scored-lst len bound)
              (map-collect-extrema-over-list
               biggestp relp
               (cadr (assoc-eq :matched-events
                               (cdr (assoc-equal (car (car books))
                                                 books))))
               scored-lst len bound k cutoff)
              (map-collect-extrema-over-list-list
               biggestp relp
               (cdr books)
               scored-lst len bound k cutoff)))))

(defun round-to-nearest (x)
  (cond ((integerp x) x)
        ((< 0 x) (floor (+ x 1/2) 1))
        (t (- (floor (+ (- x) 1/2) 1)))))

(defun round-to-nearest-percent (x)
  (round-to-nearest (* 100 x)))

(defun convert-fractional-scores-to-percents (scored-lst)
  (cond ((endp scored-lst) nil)
        (t (cons (list* (round-to-nearest-percent (car (car scored-lst)))
                        '%
                        (cdr (car scored-lst)))
                 (convert-fractional-scores-to-percents (cdr scored-lst))))))

(defun convert-abs-scores-to-centiseconds (scored-lst)
  (cond ((endp scored-lst) nil)
        (t (cons (list* (car (car scored-lst))
                        'cs
                        (cdr (car scored-lst)))
                 (convert-abs-scores-to-centiseconds (cdr scored-lst))))))

(defun collect-best-and-worst-books (books number-of-extrema cutoff)
  (list 'books
        (list 'best-relative
              (convert-fractional-scores-to-percents
               (revappend
                (mv-let (lst len bound)
                        (map-collect-extrema-over-list
                         t t
                         books
                         nil 0 nil
                         number-of-extrema cutoff)
                        (declare (ignore len bound))
                        lst)
                nil)))
        (list 'worst-relative
              (convert-fractional-scores-to-percents
               (mv-let (lst len bound)
                       (map-collect-extrema-over-list
                        nil t
                        books
                        nil 0 nil
                        number-of-extrema cutoff)
                       (declare (ignore len bound))
                       lst)))
        (list 'best-absolute
              (convert-abs-scores-to-centiseconds
               (revappend
                (mv-let (lst len bound)
                        (map-collect-extrema-over-list
                         t nil
                         books
                         nil 0 nil
                         number-of-extrema cutoff)
                        (declare (ignore len bound))
                        lst)
                nil)))
        (list 'worst-absolute
              (convert-abs-scores-to-centiseconds
               (mv-let (lst len bound)
                       (map-collect-extrema-over-list
                        nil nil
                        books
                        nil 0 nil
                        number-of-extrema cutoff)
                       (declare (ignore len bound))
                       lst)))))

(defun collect-best-and-worst-events (books number-of-extrema cutoff)
  (list 'events
        (list 'best-relative
              (convert-fractional-scores-to-percents
               (revappend
                (mv-let (lst len bound)
                        (map-collect-extrema-over-list-list
                         t t
                         books
                         nil 0 nil
                         number-of-extrema cutoff)
                        (declare (ignore len bound))
                        lst)
                nil)))
        (list 'worst-relative
              (convert-fractional-scores-to-percents
               (mv-let (lst len bound)
                       (map-collect-extrema-over-list-list
                        nil t
                        books
                        nil 0 nil
                        number-of-extrema cutoff)
                       (declare (ignore len bound))
                       lst)))
        (list 'best-absolute
              (convert-abs-scores-to-centiseconds
               (revappend
                (mv-let (lst len bound)
                        (map-collect-extrema-over-list-list
                         t nil
                         books
                         nil 0 nil
                         number-of-extrema cutoff)
                        (declare (ignore len bound))
                        lst)
                nil)))
        (list 'worst-absolute
              (convert-abs-scores-to-centiseconds
               (mv-let (lst len bound)
                       (map-collect-extrema-over-list-list
                        nil nil
                        books
                        nil 0 nil
                        number-of-extrema cutoff)
                       (declare (ignore len bound))
                       lst)))))

(defun missing-books (lst ans)
  (cond ((endp lst) (revappend ans nil))
        ((cadr (assoc-eq :missing-report (cdr (car lst))))
         (missing-books (cdr lst) (cons (car lst) ans)))
        (t (missing-books (cdr lst) ans))))

(defun sum-lst (lst ans)
  (cond ((endp lst) ans)
        (t (sum-lst (cdr lst) (+ (car lst) ans)))))

(defun median (lst)
  (let ((lst (merge-sort-lexorder lst))
        (k (length lst)))
    (cond ((evenp k)
           (/ (+ (nth (- (/ k 2) 1) lst) (nth (/ k 2) lst)) 2))
          (t (nth (floor k 2) lst)))))



(defun collect-certification-times (i lst ans)
  (cond ((endp lst) ans)
        ((cadr (assoc-eq :missing-report (cdr (car lst))))
         (collect-certification-times i (cdr lst) ans))
        (t (collect-certification-times
            i (cdr lst)
            (cons (tm i (car lst)) ans)))))

(defun collect-certification-scores (relp lst ans)
  (cond ((endp lst) ans)
        ((cadr (assoc-eq :missing-report (cdr (car lst))))
         (collect-certification-scores relp (cdr lst) ans))
        (t (collect-certification-scores
            relp
            (cdr lst)
            (let ((tm1 (tm 1 (car lst)))
                  (tm2 (tm 2 (car lst))))
              (cons (if relp
                        (/ (- tm1 tm2) (if (equal tm1 0) 1 tm1))
                        (- tm1 tm2))
                    ans))))))

(defun sum-reported-cts (lst ct1 ct2)
  (cond ((endp lst) (list ct1 ct2))
        ((cadr (assoc-eq :missing-report (cdr (car lst))))
         (sum-reported-cts (cdr lst) ct1 ct2))
        (t (let ((temp (assoc-eq :certification-times (cdr (car lst)))))
             (sum-reported-cts (cdr lst)
                               (+ ct1 (car  (nth 3 temp)))
                               (+ ct2 (cadr (nth 3 temp))))))))

(defun collect-significant-matched-event-times1 (i lst cutoff ans)
  (cond
   ((endp lst) ans)
   ((or (and (<= (tm 1 (car lst)) cutoff)
             (<= (tm 2 (car lst)) cutoff))
        (member-eq (car (car lst))
                   *ignored-events*))
    (collect-significant-matched-event-times1 i (cdr lst) cutoff ans))
   (t (collect-significant-matched-event-times1
       i (cdr lst) cutoff
       (cons (tm i (car lst)) ans)))))

(defun collect-significant-matched-event-times (i lst cutoff ans)
  (cond ((endp lst) ans)
        ((cadr (assoc-eq :missing-report (cdr (car lst))))
         (collect-significant-matched-event-times i (cdr lst) cutoff ans))
        (t (collect-significant-matched-event-times
            i
            (cdr lst)
            cutoff
            (collect-significant-matched-event-times1
             i
             (cadr (assoc-eq :matched-events (cdr (car lst))))
             cutoff
             ans)))))

(defun collect-significant-matched-event-scores1 (relp lst cutoff ans)
  (cond
   ((endp lst) ans)
   (t (let ((score (score relp (car lst) cutoff)))
        (cond
         ((null score)
          (collect-significant-matched-event-scores1 relp (cdr lst) cutoff ans))
         (t (collect-significant-matched-event-scores1
             relp (cdr lst) cutoff
             (cons score ans))))))))

(defun collect-significant-matched-event-scores (relp lst cutoff ans)
  (cond ((endp lst) ans)
        ((cadr (assoc-eq :missing-report (cdr (car lst))))
         (collect-significant-matched-event-scores relp (cdr lst) cutoff ans))
        (t (collect-significant-matched-event-scores
            relp
            (cdr lst)
            cutoff
            (collect-significant-matched-event-scores1
             relp
             (cadr (assoc-eq :matched-events (cdr (car lst))))
             cutoff
             ans)))))

(defun count-matched-events (lst ans)

; We count the number of matched events by collecting and then counting the
; number of significant events, where we use -1 as the cutoff: every event is
; significant wrt -1.

  (length (collect-significant-matched-event-times 1 lst -1 ans)))

(defun count-positives (lst ans)
  (cond ((endp lst) ans)
        ((> (car lst) 0) (count-positives (cdr lst) (+ 1 ans)))
        (t (count-positives (cdr lst) ans))))

(defun count-zeroes (lst ans)
  (cond ((endp lst) ans)
        ((equal (car lst) 0) (count-zeroes (cdr lst) (+ 1 ans)))
        (t (count-zeroes (cdr lst) ans))))

(defun spread (lst)
  (let* ((n (length lst))
         (p (count-positives lst 0))
         (z (count-zeroes lst 0))
         (p-pct (round-to-nearest-percent (/ p n)))
         (z-pct (round-to-nearest-percent (/ z n)))
         (n-pct (- 100 (+ p-pct z-pct))))
    `(spread (better ,p-pct %)
             (unchanged ,z-pct %)
             (worse ,n-pct %))))

(defun unmatched-event-distribution1 (i umlst um-alist)
  (cond ((endp umlst) um-alist)
        ((null (tm i (car umlst)))
         (unmatched-event-distribution1 i (cdr umlst) um-alist))
        (t (let* ((temp (assoc-eq (car (car umlst)) um-alist))
                  (cnt (or (cadr temp) 0))
                  (tm (or (caddr temp) 0)))
             (unmatched-event-distribution1
              i
              (cdr umlst)
              (put-assoc-eq (car (car umlst))
                            (list (+ 1 cnt)
                                  (+ (tm i (car umlst))
                                     tm))
                            um-alist))))))

(defun event-distribution1 (i mlst cutoff sig-alist cut-alist ign-alist)
  (cond
   ((endp mlst)
    (mv sig-alist cut-alist ign-alist))
   ((member-eq (car (car mlst)) *ignored-events*)
    (let* ((temp (assoc-eq (car (car mlst)) ign-alist))
           (cnt (or (cadr temp) 0))
           (tm (or (caddr temp) 0)))
      (event-distribution1 i (cdr mlst) cutoff
                           sig-alist
                           cut-alist
                           (put-assoc-eq (car (car mlst))
                                         (list (+ 1 cnt)
                                               (+ (tm i (car mlst)) tm))
                                         ign-alist))))

   ((and (<= (tm 1 (car mlst)) cutoff)
         (<= (tm 2 (car mlst)) cutoff))
    (let* ((temp (assoc-eq (car (car mlst)) cut-alist))
           (cnt (or (cadr temp) 0))
           (tm (or (caddr temp) 0)))
      (event-distribution1 i (cdr mlst) cutoff
                           sig-alist
                           (put-assoc-eq (car (car mlst))
                                         (list (+ 1 cnt)
                                               (+ (tm i (car mlst)) tm))
                                         cut-alist)
                           ign-alist)))
   (t
    (let* ((temp (assoc-eq (car (car mlst)) sig-alist))
           (cnt (or (cadr temp) 0))
           (tm (or (caddr temp) 0)))
      (event-distribution1 i (cdr mlst) cutoff
                           (put-assoc-eq (car (car mlst))
                                         (list (+ 1 cnt)
                                               (+ (tm i (car mlst)) tm))
                                         sig-alist)
                           cut-alist
                           ign-alist)))))


(defun event-distribution2 (i books cutoff sig-alist cut-alist ign-alist um-alist)

; Scan all books and accumulate alists mapping event types to number of
; instances and total times, organized by the categories significant, ignored,
; cutoff, and unmatched.

  (cond
   ((endp books)
    (mv sig-alist cut-alist ign-alist um-alist))
   (t (mv-let (sig-alist cut-alist ign-alist)
              (event-distribution1
               i
               (cadr (assoc-eq :matched-events (cdr (car books))))
               cutoff sig-alist cut-alist ign-alist)
              (event-distribution2 i (cdr books) cutoff
                                   sig-alist cut-alist ign-alist
                                   (unmatched-event-distribution1
                                    i
                                    (cadr (assoc-eq :unmatched-events (cdr (car books))))
                                    um-alist))))))

(defun zip-matched-alists (alist1 alist2)

; Alist1 and alist2 contain elements of the form (cmd cnt tm), e.g., (DEFTHM 10
; 2500).  We assume the commands in the two alist come from matched events,
; e.g., the cnts for identical cmds are the same.  We combine them into a
; single alist with elements of the form (cmd cnt tm1 tm2 rel abs).

  (cond ((endp alist1)
         (if (endp alist2)
             nil
             (er hard 'zip-matched-alists
                 "Matched alists have different numbers of elements, alist1 = ~
                  ~x0, alist2 = ~x1!"
                 alist1 alist2)))
        (t
         (let* ((temp1 (car alist1))
                (cmd (car temp1))
                (temp2 (assoc-eq cmd alist2))
                (cnt (if (equal (cadr temp1) (cadr temp2))
                         (cadr temp1)
                         (er hard 'zip-matched-alists "Count's differ ~x0 v ~x1!"
                             temp1 temp2)))
                (tm1 (caddr temp1))
                (tm2 (caddr temp2))
                (rel (round-to-nearest-percent (/ (- tm1 tm2) (if (equal tm1 0) 1 tm1))))
                (abs (- tm1 tm2)))
           (cons (list cmd cnt tm1 tm2 rel abs)
                 (zip-matched-alists (cdr alist1)
                                     (remove1-equal temp2 alist2)))))))


(defun zip-unmatched-alists (alist1 alist2)

; Alist1 and alist2 contain elements of the form (cmd cnt tm), e.g., (DEFTHM 10
; 2500).  But they are not matched, so there may be different numbers of a
; given kind of event and different events listed in each.  We just add the
; counts together.  We combine the two alists into a single alist with elements
; of the form (cmd cnt tm1 tm2 rel abs).

  (cond ((and (endp alist1)
              (endp alist2))
         nil)
        (t
         (let* ((temp1 (if alist1
                           (car alist1)
                           '(nil 0 0)))
                (cmd (or (car temp1) (car (car alist2))))
                (temp2 (or (assoc-eq cmd alist2)
                           '(nil 0 0)))
                (cnt (+ (cadr temp1) (cadr temp2)))
                (tm1 (caddr temp1))
                (tm2 (caddr temp2))
                (rel (round-to-nearest-percent (/ (- tm1 tm2) (if (equal tm1 0) 1 tm1))))
                (abs (- tm1 tm2)))
           (cons (list cmd cnt tm1 tm2 rel abs)
                 (zip-unmatched-alists (cdr alist1)
                                       (remove1-equal temp2 alist2)))))))

(defun strip-nth (n lst)
  (cond ((endp lst) nil)
        (t (cons (nth n (car lst)) (strip-nth n (cdr lst))))))

(defun summarize-category (alist)
  (let* ((cnt (sum-lst (strip-nth 1 alist) 0))
         (tm1 (sum-lst (strip-nth 2 alist) 0))
         (tm2 (sum-lst (strip-nth 3 alist) 0))
         (rel (round-to-nearest-percent (/ (- tm1 tm2) (if (equal tm1 0) 1 tm1))))
         (abs (- tm1 tm2)))
    `((cnt ,cnt)
      (tm1 ,tm1 cs)
      (tm2 ,tm2 cs)
      (rel ,rel %)
      (abs ,abs cs)
      (distribution
       (cmd cnt tm1 tm2 rel abs)
       ,@(strip-cdrs
         (merge-sort-car->
          (pairlis$ (strip-nth 5 alist)
                    alist)))))))

(defun event-distribution (books cutoff)
  (mv-let
   (sig-alist1 cut-alist1 ign-alist1 um-alist1)
   (event-distribution2 1 books cutoff nil nil nil nil)
   (mv-let
    (sig-alist2 cut-alist2 ign-alist2 um-alist2)
    (event-distribution2 2 books cutoff nil nil nil nil)
    (let* ((sig-cat (summarize-category (zip-matched-alists sig-alist1 sig-alist2)))
           (ign-cat (summarize-category (zip-matched-alists ign-alist1 ign-alist2)))
           (cut-cat (summarize-category (zip-matched-alists cut-alist1 cut-alist2)))
           (unm-cat (summarize-category (zip-unmatched-alists um-alist1 um-alist2)))
           (cnt (+ (cadr (nth 0 sig-cat))
                   (cadr (nth 0 ign-cat))
                   (cadr (nth 0 cut-cat))))
           (tm1 (+ (cadr (nth 1 sig-cat))
                   (cadr (nth 1 ign-cat))
                   (cadr (nth 1 cut-cat))))
           (tm2 (+ (cadr (nth 2 sig-cat))
                   (cadr (nth 2 ign-cat))
                   (cadr (nth 2 cut-cat))))
           (rel (round-to-nearest-percent (/ (- tm1 tm2) (if (equal tm1 0) 1 tm1))))
           (abs (- tm1 tm2)))
      `((matched-events
         (cnt ,cnt)
         (tm1 ,tm1 cs)
         (tm2 ,tm2 cs)
         (rel ,rel %)
         (abs ,abs cs)
         (significant ,@sig-cat)
         (ignored ,@ign-cat)
         (cutoff ,@cut-cat))
        (unmatched-events
         ,@unm-cat))))))

(defun summary-report (dir1 dir2 lst number-of-extrema cutoff)
  (let* ((n (length lst))
         (missing-books (missing-books lst nil))
         (k (length missing-books))
         (cert-times1
          (collect-certification-times 1 lst nil))
         (cert-times2
          (collect-certification-times 2 lst nil))
         (tm1 (sum-lst cert-times1 0))
         (tm2 (sum-lst cert-times2 0))
         (ct-tuple (sum-reported-cts lst 0 0))
         (rel (round-to-nearest-percent
               (/ (- tm1 tm2)
                  (if (equal tm1 0) 1 tm1))))
         (abs (- tm1 tm2))
         (rel-cert-scores (collect-certification-scores t lst nil))
         (abs-cert-scores (collect-certification-scores nil lst nil))
         (md-rel (round-to-nearest-percent (median rel-cert-scores)))
         (md-abs (median abs-cert-scores))
         (sig-event-times1 (collect-significant-matched-event-times 1 lst cutoff nil))
         (sig-event-times2 (collect-significant-matched-event-times 2 lst cutoff nil))
         (etm1 (sum-lst sig-event-times1 0))
         (etm2 (sum-lst sig-event-times2 0))
         (erel (round-to-nearest-percent
                (/ (- etm1 etm2) (if (equal etm1 0) 1 etm1))))
         (eabs (- etm1 etm2))
         (rel-sig-event-scores (collect-significant-matched-event-scores t lst cutoff nil))
         (abs-sig-event-scores (collect-significant-matched-event-scores nil lst cutoff nil))
         (md-erel (round-to-nearest-percent (median rel-sig-event-scores)))
         (md-eabs (median abs-sig-event-scores)))

    (list "

  COMPARISON OF .out/.cert.out FILES

  We determine whether the contender run is faster than the baseline run.
  Time is measured in centiseconds (100 CS = 1 second).  Let tm1 and tm2
  be the times measured for the same book or event in the baseline and
  contender runs, respectively.  We calculate two scores:

  absolute:  (- tm1 tm2)
  relative:  (/ (- tm1 tm2) tm1) expressed as a percentage

  Positive scores indicate that the contender is faster.  For example
  if tm1 is 400 (i.e., 4.00 seconds) and tm2 is 300 (i.e., 3.00 seconds),
  then the absolute score for the book or event is 100 (1.00 second) and
  the relative score is 1/4 expressed as 25%.

  We also compute the median score (relative and absolute) for all books and
  the median score (relative and absolute) for all matched significant events.

  An event is ``matched'' if the same event is recorded in both the baseline
  and contender runs, where ``same event'' just means the printed Summary Form
  lines are the same.  (Several events in a book may have the same Form line,
  e.g., ``Form: ( IN-THEORY (DISABLE ...))'' and forms are matched in the order
  they appear.)

  An event is ``significant'' if the kind of the event is not one of those
  listed in *IGNORED-EVENTS* and the times reported for both runs exceed a
  specified CUTOFF.  (*IGNORED-EVENTS* lists composite events like ENAPSULATE
  whose sub-events each have their own Summaries.)  The value of the CUTOFF
  parameter is reported below.

  We show the n best and worst performing books and events, where n is
  the parameter NUMBER-OF-EXTREMA, shown below."

          '-----------------------------------------------------------------

          (list 'baseline dir1)
          (list 'contender dir2)
          (list 'books-scanned n)
          (list 'books-compared (- n k))
          (list 'comparison-based-on-total-time-per-book
                (list 'total-times tm1 tm2 ct-tuple 'cs)
                (list 'relative rel '%)
                (list 'absolute abs 'cs)
                (list 'relative-median md-rel '%)
                (list 'absolute-median md-abs 'cs)
                (spread rel-cert-scores))
          (list 'comparison-based-on-matched-event-times
                (list 'cutoff cutoff 'cs)
                (list 'matched-events
                      (length (collect-significant-matched-event-times 1 lst -1 nil))
                      'IGNORING 'DUPLICATES)
                (list 'significant-events
                      (length sig-event-times1))
                (list 'total-significant-event-times etm1 etm2)
                (list 'relative erel '%)
                (list 'absolute eabs 'cs)
                (list 'relative-median md-erel '%)
                (list 'absolute-median md-eabs 'cs)
                (spread rel-sig-event-scores))
          '-----------------------------------------------------------------
          'BEST-AND-WORST
          (list 'number-of-extrema number-of-extrema)
          (list 'cutoff cutoff 'cs)
          (collect-best-and-worst-books lst number-of-extrema cutoff)
          (collect-best-and-worst-events lst number-of-extrema cutoff)
          '-----------------------------------------------------------------
          "

  EVENT CATEGORIZATION

  We describe the distribution of events into SIGNIFICANT, IGNORED, CUTOFF, and
  UNMATCHED categories, where each of the first three contain matched events.
  IGNORED events are such compound events as PROGN and ENCAPSULATE, which are
  composed of subevents whose time is accounted for in other categories.
  CUTOFF events are those whose total duration is less than or equal to the
  specified CUTOFF.  SIGNIFICANT events are the other events: matched, atomic
  events such as DEFTHM and DEFUN, whose duration exceeds the CUTOFF.  Within
  each category we break down the performance according to event type.

  "
          (event-distribution lst cutoff)

          '-----------------------------------------------------------------
          "

  MISCELLANEOUS DETAILS

  Some books which were supposed to participate in the comparison were not
  found in both the baseline and contender systems.  We also list the basic
  parameters controlling this analysis.

  "

          (list 'baseline dir1)
          (list 'contender dir2)
          (list '*ignored-events* *ignored-events*)
          (list 'cutoff cutoff 'cs)
          (list 'number-of-extrema number-of-extrema)
          (list 'missing-books (length missing-books) missing-books))))

(defun compare-out-files (dir1 dir2 books number-of-extrema cutoff state)
  (mv-let
   (lst state)
   (book-makers dir1 dir2 books state nil)
   (er-progn
    (assign books lst)
    (value (summary-report dir1 dir2 lst number-of-extrema cutoff)))))

; To illustrate the utility, we repeat the example provided at the beginning of
; this file, along with the output.


; ACL2 !>(compare-out-files
;  "/u/moore/work/v5-0/acl2-sources/books/"            ; benchmark books directory
;  "/u/moore/work/v6-0/acl2-sources/books/"            ; contender books directory
;  '("arithmetic-3/bind-free/arithmetic-theory"        ; list of book names to compare
;    "arithmetic-3/bind-free/banner"
;    "arithmetic-3/bind-free/basic-helper"
;    "arithmetic-3/bind-free/basic"
;    "arithmetic-3/bind-free/building-blocks"
;    "arithmetic-3/bind-free/collect"
;    "arithmetic-3/bind-free/common"
;    "arithmetic-3/bind-free/default-hint"
;    "arithmetic-3/bind-free/integerp-meta"
;    "arithmetic-3/bind-free/integerp"
;    "arithmetic-3/bind-free/mini-theories-helper"
;    "arithmetic-3/bind-free/mini-theories"
;    "arithmetic-3/bind-free/normalize"
;    "arithmetic-3/bind-free/numerator-and-denominator"
;    "arithmetic-3/bind-free/remove-weak-inequalities"
;    "arithmetic-3/bind-free/simplify-helper"
;    "arithmetic-3/bind-free/simplify"
;    "arithmetic-3/bind-free/top"
;    "arithmetic-3/extra/ext"
;    "arithmetic-3/extra/top-ext"
;    "arithmetic-3/floor-mod/floor-mod"
;    "arithmetic-3/floor-mod/mod-expt-fast"
;    "arithmetic-3/pass1/basic-arithmetic-helper"
;    "arithmetic-3/pass1/basic-arithmetic"
;    "arithmetic-3/pass1/expt-helper"
;    "arithmetic-3/pass1/expt"
;    "arithmetic-3/pass1/inequalities"
;    "arithmetic-3/pass1/mini-theories"
;    "arithmetic-3/pass1/non-linear"
;    "arithmetic-3/pass1/num-and-denom-helper"
;    "arithmetic-3/pass1/numerator-and-denominator"
;    "arithmetic-3/pass1/prefer-times"
;    "arithmetic-3/pass1/top"
;    "arithmetic-3/top")
;   5                                                  ; number-of-extrema
;  10                                                  ; cutoff = 0.10 seconds
;  state)
;
;  ("
;
;   COMPARISON OF .out/.cert.out FILES
;
;   We determine whether the contender run is faster than the baseline run.
;   Time is measured in centiseconds (100 CS = 1 second).  Let tm1 and tm2
;   be the times measured for the same book or event in the baseline and
;   contender runs, respectively.  We calculate two scores:
;
;   absolute:  (- tm1 tm2)
;   relative:  (/ (- tm1 tm2) tm1) expressed as a percentage
;
;   Positive scores indicate that the contender is faster.  For example
;   if tm1 is 400 (i.e., 4.00 seconds) and tm2 is 300 (i.e., 3.00 seconds),
;   then the absolute score for the book or event is 100 (1.00 second) and
;   the relative score is 1/4 expressed as 25%.
;
;   We also compute the median score (relative and absolute) for all books and
;   the median score (relative and absolute) for all matched significant events.
;
;   An event is ``matched'' if the same event is recorded in both the baseline
;   and contender runs, where ``same event'' just means the printed Summary Form
;   lines are the same.  (Several events in a book may have the same Form line,
;   e.g., ``Form: ( IN-THEORY (DISABLE ...))'' and forms are matched in the order
;   they appear.)
;
;   An event is ``significant'' if the kind of the event is not one of those
;   listed in *IGNORED-EVENTS* and the times reported for both runs exceed a
;   specified CUTOFF.  (*IGNORED-EVENTS* lists composite events like ENAPSULATE
;   whose sub-events each have their own Summaries.)  The value of the CUTOFF
;   parameter is reported below.
;
;   We show the n best and worst performing books and events, where n is
;   the parameter NUMBER-OF-EXTREMA, shown below."
;   -----------------------------------------------------------------
;   (BASELINE "/u/moore/work/v5-0/acl2-sources/books/")
;   (CONTENDER "/u/moore/work/v6-0/acl2-sources/books/")
;   (BOOKS-SCANNED 34)
;   (BOOKS-COMPARED 34)
;   (COMPARISON-BASED-ON-TOTAL-TIME-PER-BOOK
;        (TOTAL-TIMES 3342 3539 (1243 3859) CS)
;        (RELATIVE -6 %)
;        (ABSOLUTE -197 CS)
;        (RELATIVE-MEDIAN -14 %)
;        (ABSOLUTE-MEDIAN -2 CS)
;        (SPREAD (BETTER 12 %)
;                (UNCHANGED 15 %)
;                (WORSE 73 %)))
;   (COMPARISON-BASED-ON-MATCHED-EVENT-TIMES
;        (CUTOFF 10 CS)
;        (MATCHED-EVENTS 1274 IGNORING DUPLICATES)
;        (SIGNIFICANT-EVENTS 61)
;        (TOTAL-SIGNIFICANT-EVENT-TIMES 2421 2503)
;        (RELATIVE -3 %)
;        (ABSOLUTE -82 CS)
;        (RELATIVE-MEDIAN -7 %)
;        (ABSOLUTE-MEDIAN -1 CS)
;        (SPREAD (BETTER 33 %)
;                (UNCHANGED 13 %)
;                (WORSE 54 %)))
;   -----------------------------------------------------------------
;   BEST-AND-WORST (NUMBER-OF-EXTREMA 5)
;   (CUTOFF 10 CS)
;   (BOOKS (BEST-RELATIVE ((10 % "arithmetic-3/bind-free/simplify"
;                              462 416 (25 447))
;                          (9 % "arithmetic-3/bind-free/normalize"
;                             164 149 (15 166))
;                          (5 %
;                             "arithmetic-3/bind-free/arithmetic-theory"
;                             150 142 (8 164))
;                          (5 % "arithmetic-3/bind-free/integerp-meta"
;                             444 423 (16 447))
;                          (-5 % "arithmetic-3/bind-free/collect"
;                              40 42 (7 59))))
;          (WORST-RELATIVE ((-27 % "arithmetic-3/extra/ext"
;                                106 135 (21 148))
;                           (-32 %
;                                "arithmetic-3/pass1/expt" 28 37 (34 42))
;                           (-33 % "arithmetic-3/bind-free/basic-helper"
;                                12 16 (12 21))
;                           (-36 % "arithmetic-3/bind-free/top"
;                                42 57 (27 64))
;                           (-58 % "arithmetic-3/extra/top-ext"
;                                66 104 (37 113))))
;          (BEST-ABSOLUTE ((46 CS "arithmetic-3/bind-free/simplify"
;                              462 416 (25 447))
;                          (21 CS
;                              "arithmetic-3/bind-free/integerp-meta"
;                              444 423 (16 447))
;                          (15 CS "arithmetic-3/bind-free/normalize"
;                              164 149 (15 166))
;                          (8 CS
;                             "arithmetic-3/bind-free/arithmetic-theory"
;                             150 142 (8 164))
;                          (-2 CS
;                              "arithmetic-3/bind-free/simplify-helper"
;                              23 25 (26 34))))
;          (WORST-ABSOLUTE ((-29 CS "arithmetic-3/extra/ext"
;                                106 135 (21 148))
;                           (-33 CS "arithmetic-3/bind-free/integerp"
;                                153 186 (8 203))
;                           (-38 CS "arithmetic-3/extra/top-ext"
;                                66 104 (37 113))
;                           (-41 CS "arithmetic-3/floor-mod/floor-mod"
;                                746 787 (34 811))
;                           (-68 CS
;                                "arithmetic-3/floor-mod/mod-expt-fast"
;                                645 713 (626 720)))))
;   (EVENTS (BEST-RELATIVE ((58 % DEFTHM "SIMPLIFY-MOD-+-MOD" 31
;                               13 "arithmetic-3/floor-mod/floor-mod")
;                           (48 % DEFUN
;                               "FACTOR-SCATTER-EXPONENTS-INFO-LIST"
;                               73 38 "arithmetic-3/bind-free/simplify")
;                           (28 % DEFTHM "REWRITE-FLOOR-MOD" 92
;                               66 "arithmetic-3/floor-mod/floor-mod")
;                           (26 % DEFTHM
;                               "PSEUDO-TERM-LIST-LISTP-BAG-TERMS" 42 31
;                               "arithmetic-3/bind-free/integerp-meta")
;                           (23 % DEFTHM "SUBTRACT-BAG-GOOD-*" 13 10
;                               "arithmetic-3/bind-free/integerp-meta")))
;           (WORST-RELATIVE ((-44 % INCLUDE-BOOK
;                                 "ext" 9 13 "arithmetic-3/extra/top-ext")
;                            (-55 % INCLUDE-BOOK "top-ext"
;                                 31 48 "arithmetic-3/extra/top-ext")
;                            (-57 % DEFTHM "NOT-INTEGERP-4V"
;                                 7 11 "arithmetic-3/bind-free/integerp")
;                            (-65 % INCLUDE-BOOK
;                                 "arithmetic-3/bind-free/top"
;                                 23 38 "arithmetic-3/extra/top-ext")
;                            (-106 % DEFUN "SIMPLIFY-MOD-+-MOD-FN" 35
;                                  72 "arithmetic-3/floor-mod/floor-mod")))
;           (BEST-ABSOLUTE ((35 CS DEFUN
;                               "FACTOR-SCATTER-EXPONENTS-INFO-LIST"
;                               73 38 "arithmetic-3/bind-free/simplify")
;                           (29 CS VERIFY-GUARDS "META-INTEGERP" 176 147
;                               "arithmetic-3/bind-free/integerp-meta")
;                           (26 CS DEFTHM "REWRITE-FLOOR-MOD" 92
;                               66 "arithmetic-3/floor-mod/floor-mod")
;                           (18 CS DEFTHM "SIMPLIFY-MOD-+-MOD" 31
;                               13 "arithmetic-3/floor-mod/floor-mod")
;                           (13 CS DEFTHM
;                               "MOD-EXPT-FAST-1-AS-MOD-AND-EXPT" 101 88
;                               "arithmetic-3/floor-mod/mod-expt-fast")))
;           (WORST-ABSOLUTE ((-15 CS INCLUDE-BOOK
;                                 "arithmetic-3/bind-free/top"
;                                 23 38 "arithmetic-3/extra/top-ext")
;                            (-15 CS DEFTHM "REWRITE-MOD-MOD" 105
;                                 120 "arithmetic-3/floor-mod/floor-mod")
;                            (-17 CS INCLUDE-BOOK "top-ext"
;                                 31 48 "arithmetic-3/extra/top-ext")
;                            (-37 CS DEFUN "SIMPLIFY-MOD-+-MOD-FN" 35
;                                 72 "arithmetic-3/floor-mod/floor-mod")
;                            (-70 CS DEFTHM
;                                 "MOD-THEOREM-TWO-HELPER-HELPER" 484 554
;                                 "arithmetic-3/floor-mod/mod-expt-fast"))))
;   -----------------------------------------------------------------
;   "
;
;   EVENT CATEGORIZATION
;
;   We describe the distribution of events into SIGNIFICANT, IGNORED, CUTOFF, and
;   UNMATCHED categories, where each of the first three contain matched events.
;   IGNORED events are such compound events as PROGN and ENCAPSULATE, which are
;   composed of subevents whose time is accounted for in other categories.
;   CUTOFF events are those whose total duration is less than or equal to the
;   specified CUTOFF.  SIGNIFICANT events are the other events: matched, atomic
;   events such as DEFTHM and DEFUN, whose duration exceeds the CUTOFF.  Within
;   each category we break down the performance according to event type.
;
;   "
;   ((MATCHED-EVENTS
;         (CNT 1347)
;         (TM1 5635 CS)
;         (TM2 8653 CS)
;         (REL -54 %)
;         (ABS -3018 CS)
;         (SIGNIFICANT (CNT 61)
;                      (TM1 2421 CS)
;                      (TM2 2503 CS)
;                      (REL -3 %)
;                      (ABS -82 CS)
;                      (DISTRIBUTION (CMD CNT TM1 TM2 REL ABS)
;                                    (VERIFY-GUARDS 2 194 164 15 30)
;                                    (DEFUN 21 677 656 3 21)
;                                    (MUTUAL-RECURSION 1 12 15 -25 -3)
;                                    (DEFTHM 23 1223 1260 -3 -37)
;                                    (INCLUDE-BOOK 14 315 408 -30 -93)))
;         (IGNORED (CNT 73)
;                  (TM1 2293 CS)
;                  (TM2 5114 CS)
;                  (REL -123 %)
;                  (ABS -2821 CS)
;                  (DISTRIBUTION (CMD CNT TM1 TM2 REL ABS)
;                                (MAKE-EVENT 2 0 0 0 0)
;                                (PROGN 9 22 66 -200 -44)
;                                (ENCAPSULATE 28 1028 1189 -16 -161)
;                                (CERTIFY-BOOK 34 1243 3859 -210 -2616)))
;         (CUTOFF (CNT 1213)
;                 (TM1 921 CS)
;                 (TM2 1036 CS)
;                 (REL -12 %)
;                 (ABS -115 CS)
;                 (DISTRIBUTION (CMD CNT TM1 TM2 REL ABS)
;                               (DEFUN 132 179 174 3 5)
;                               (THEORY-INVARIANT 20 0 0 0 0)
;                               (??? 7 0 0 0 0)
;                               (DEFTHEORY 15 0 0 0 0)
;                               (DEFMACRO 14 0 0 0 0)
;                               (MUTUAL-RECURSION 1 1 1 0 0)
;                               (TABLE 8 0 0 0 0)
;                               (VERIFY-GUARDS 11 8 9 -13 -1)
;                               (IN-THEORY 84 0 7 -700 -7)
;                               (INCLUDE-BOOK 116 165 218 -32 -53)
;                               (DEFTHM 805 568 627 -10 -59))))
;    (UNMATCHED-EVENTS (CNT 0)
;                      (TM1 0 CS)
;                      (TM2 0 CS)
;                      (REL 0 %)
;                      (ABS 0 CS)
;                      (DISTRIBUTION (CMD CNT TM1 TM2 REL ABS))))
;   -----------------------------------------------------------------
;   "
;
;   MISCELLANEOUS DETAILS
;
;   Some books which were supposed to participate in the comparison were not
;   found in both the baseline and contender systems.  We also list the basic
;   parameters controlling this analysis.
;
;   "
;   (BASELINE "/u/moore/work/v5-0/acl2-sources/books/")
;   (CONTENDER "/u/moore/work/v6-0/acl2-sources/books/")
;   (*IGNORED-EVENTS* (ENCAPSULATE PROGN PROGN! CERTIFY-BOOK MAKE-EVENT))
;   (CUTOFF 10 CS)
;   (NUMBER-OF-EXTREMA 5)
;   (MISSING-BOOKS 0 NIL))
; ACL2 !>
