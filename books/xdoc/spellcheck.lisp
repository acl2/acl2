; XDOC Documentation System for ACL2
; Copyright (C) 2009-2015 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "XDOC")
(include-book "std/strings/defs-program" :dir :system)
(include-book "std/osets/top" :dir :system)
(program)


; We now implement a primitive spell-checking capability so that, when a user
; searches for something like in-theroy instead of in-theory, or fast-alist
; instead of fast-alists, we can hopefully point them to the right topic.



; This is similar to the basic idea of soundex codes, but slightly tweaked to
; possibly better fit what we're trying to do...

(defun soundex-mangle-tail-1 (x)
  ;; Merge similar sounding characters into sets
  (declare (xargs :guard (character-listp x)))
  (b* (((when (atom x))
        nil)
       (x1   (str::downcase-char (car x)))
       ((when (and (eql x1 #\s)
                   (atom (cdr x))))
        ;; Special hack to automatically drop the "s" from the end of the
        ;; string, so that, e.g., "alist" and "alists" will merge to the same
        ;; code.
        nil)
       (rest (soundex-mangle-tail-1 (cdr x))))
      (cond ((position x1 "aeiouyhw$") (cons #\Space rest))
            ((position x1 "bfpv")      (cons #\b rest))
            ((position x1 "cgjkqsxz")  (cons #\c rest))
            ((position x1 "dt")        (cons #\d rest))
            ((eql x1 #\l)              (cons #\l rest))
            ((position x1 "mn")        (cons #\m rest))
            ((eql x1 #\r)              (cons #\r rest))
            ((position x1 "-_/>? ")    (cons #\Space rest))
            (t                         (cons x1 rest)))))

(defun soundex-mangle-tail-2 (x)
  ;; Eat adjacent duplicates except for spaces
  (declare (xargs :guard (character-listp x)))
  (b* (((when (atom x))
        nil)
       ((when (atom (cdr x)))
        (cons (car x) (soundex-mangle-tail-2 (cdr x))))
       (x1 (first x))
       (x2 (second x))
       ((when (and (eql x1 x2)
                   (not (eql x1 #\Space))))
        (cons x1 (soundex-mangle-tail-2 (cddr x)))))
      (cons x1 (soundex-mangle-tail-2 (cdr x)))))

(defun soundex-mangle-tail (x)
  (declare (xargs :guard (character-listp x)))
  (b* ((x (soundex-mangle-tail-1 x))
       (x (soundex-mangle-tail-2 x))
       (x (remove #\Space x)))
      (cond ((atom x)
             '(#\Space #\Space #\Space))
            ((atom (cdr x))
             (cons (first x) '(#\Space #\Space)))
            ((atom (cddr x))
             (list* (first x) (second x) '(#\Space)))
            (t
             (list (first x) (second x) (third x))))))

#||
(soundex-mangle-tail (str::explode "xplode"))
(soundex-mangle-tail (str::explode "xplod"))
(soundex-mangle-tail (str::explode "xplds"))
(soundex-mangle-tail (str::explode "xxpld"))
(soundex-mangle-tail (str::explode "mpolde"))
(soundex-mangle-tail (str::explode "ampolde"))
(soundex-mangle-tail (str::explode "unpolde"))
||#

(defun soundex (x)
  "Returns our soundex-like code as a string."
  (declare (xargs :guard (stringp x)))
  (b* ((chars (str::explode x)))
    (if (atom chars)
        "    "
      (str::implode
       (cons (str::downcase-char (car chars))
             (soundex-mangle-tail (cdr chars)))))))

#||
(soundex "explode")
(soundex "explodes")
(soundex "explod")
(soundex "expld")
(soundex "exxpld")
(soundex "impolde")
(soundex "ampolde")
(soundex "unpolde")
(soundex "alist")
(soundex "alists")
(soundex "+")
(soundex "-")
(soundex "foo-bar")
(soundex "foobar")
(soundex "foo_bar")
(soundex "pairlis")
(soundex "pairlis$")
(soundex "union")
(soundex "union$")

;; basic performance test: a million soundex codes for reasonably sized names...
;;   2.68 seconds, 880 MB
;; so we're at 373,000 soundex codes per second.  that seems perfectly fine, since
;; there are today well under 10k xdoc topics.

(let ((x "reasonable-name"))
  (time (loop for i from 1 to 1000000 do
              (xdoc::soundex x))))

||#

(defun soundex-list (x)
  (declare (xargs :guard (string-listp x)))
  (if (atom x)
      nil
    (cons (soundex (car x))
          (soundex-list (cdr x)))))


; Now we have the problem of seeing how closely actual symbols match...

(defun find-diffs (x y)
  (declare (xargs :guard (equal (len x) (len y))))
  (cond ((atom x)
         nil)
        ((equal (car x) (car y))
         (find-diffs (cdr x) (cdr y)))
        (t
         (cons (cons (car x) (car y))
               (find-diffs (cdr x) (cdr y))))))

(defun nearly-equal-aux (x y)
  (declare (xargs :guard (and (string-listp x)
                              (string-listp y))))
  (let ((xl (len x))
        (yl (len y)))
    (and ;; X is longer than Y by exactly 1.
         (eql xl (+ 1 yl))
         ;; There are at least a couple of tokens in each
         (<= 1 xl)
         (<= 1 yl)
         (or ;; X is just ([prefix]@Y) for some short prefix
          (and (equal (cdr x) y)
               (<= (length (car x)) 3))
          ;; X is just (Y@[suffix]) for some short suffix
          (and (equal (butlast x 1) y)
               (<= (length (car (last y))) 3))))))

(defun nearly-equal (x y)
  (declare (xargs :guard (and (string-listp x)
                              (string-listp y))))
  (or (nearly-equal-aux x y)
      (nearly-equal-aux y x)))

(defun merge-final-ps (x)
  ;; Merge together final tokens to perhaps get better soundex matches for
  ;; "foop" versus "foo" "p"
  (declare (xargs :guard (string-listp x)))
  (cond ((atom x)
         nil)
        ((atom (cdr x))
         (list (first x)))
        ((and (atom (cddr x))
              (equal (second x) "p"))
         (list (str::cat (first x) "p")))
        (t
         (cons (car x)
               (merge-final-ps (cdr x))))))

#||
(merge-final-ps '("integer" "list" "p"))
(merge-final-ps '("integer" "listp"))
(merge-final-ps '("maybe" "string" "p"))
||#

(defun collect-plausible-misspellings-aux
  (goal        ;; the exact symbol the user asked for
   goal-tokens ;; the pre-tokenized name of the symbol the user asked for
   desperation ;; number of tokens that can differ
   topic-names ;; the list of all xdoc topic names to consider
   )
  (declare (xargs :guard (and (symbolp goal)
                              (string-listp goal-tokens)
                              (natp desperation)
                              (symbol-listp topic-names))))
  (b* (((when (atom topic-names))
        nil)
       (name1        (car topic-names))
       (name1-tokens (str::strtok (str::downcase-string (symbol-name name1))
                                  '(#\- #\_ #\/ #\> #\? #\Space)))
       (rest         (collect-plausible-misspellings-aux goal goal-tokens desperation
                                                         (cdr topic-names)))

       ((when (equal goal-tokens name1-tokens))
        ;; Identical except perhaps for package-name and/or the number of
        ;; dashes/hyphens/etc
        (cons name1 rest))

       ((unless (>= desperation 1)) rest)

       ((when (equal (mergesort name1-tokens)
                     (mergesort goal-tokens)))
        ;; Identical up to number of or order of tokens, i.e., foo-bar versus
        ;; bar-foo.
        (cons name1 rest))

       ((unless (>= desperation 2)) rest)

       ;; Merge in any final token whose name is just "p", so that, e.g., we
       ;; treat "foo-p" and "foop" the same from now on.
       (name1-tokens (merge-final-ps name1-tokens))
       (goal-tokens  (merge-final-ps goal-tokens))

       ((when (equal goal-tokens name1-tokens))
        (cons name1 rest))

       ((unless (>= desperation 3)) rest)

       ((when (and (equal (len name1-tokens)
                          (len goal-tokens))
                   (let ((diffs (find-diffs name1-tokens goal-tokens)))
                     (and (equal (len diffs) 1)
                          (equal (soundex (caar diffs))
                                 (soundex (cdar diffs)))))))
        ;; Same number of tokens, only one token differs, and the token that is
        ;; different is phonetically similar, catches things like intager-listp
        (cons name1 rest))

       ((unless (>= desperation 4)) rest)

       ((when (equal (soundex (symbol-name goal))
                     (soundex (symbol-name name1))))
        ;; Straightforward phonetic comparison of both symbols without any
        ;; regard to the tokenization.
        (cons name1 rest))

       ((unless (>= desperation 5)) rest)

       ((when (nearly-equal name1-tokens goal-tokens))
        ;; Identical except that one or the other has an extra suffix/prefix.
        (cons name1 rest)))

      rest))

(defun collect-plausible-misspellings (goal topic-names)
  (declare (xargs :guard (and (symbolp goal)
                              (symbol-listp topic-names))))
  (let ((goal-tokens (str::strtok (str::downcase-string (symbol-name goal))
                                  '(#\- #\_ #\/ #\> #\? #\Space))))
    (or (collect-plausible-misspellings-aux goal goal-tokens 0 topic-names)
        (collect-plausible-misspellings-aux goal goal-tokens 1 topic-names)
        (collect-plausible-misspellings-aux goal goal-tokens 2 topic-names)
        (collect-plausible-misspellings-aux goal goal-tokens 3 topic-names)
        (collect-plausible-misspellings-aux goal goal-tokens 4 topic-names)
        (collect-plausible-misspellings-aux goal goal-tokens 5 topic-names)
        )))

; Matt K. addition: interface function, in ACL2 package so that it can be
; referenced in the ACL2 sources (see near-misses).  Note that
; system/event-names needs to be included in order for this macro to be used.
(defmacro acl2::plausible-misspellings (name)
  `(collect-plausible-misspellings ,name
                                   (acl2::event-names (w state) nil)))

#||
(defconst *topic-names*
  '(acl2::explode acl2::append str::cat acl2::implode acl2::coerce
                  vl-maybe-integer-p vl-maybe-stringp
                 acl2::integer-listp acl2::nat-listp revappend))

(collect-plausible-misspellings 'xdoc::explode *topic-names*)
(collect-plausible-misspellings 'xdoc::explode *topic-names*)
(collect-plausible-misspellings 'xdoc::cate *topic-names*)

(collect-plausible-misspellings 'integer-listp *topic-names*)
(collect-plausible-misspellings 'integer-list-p *topic-names*)

(collect-plausible-misspellings 'nat-lstp *topic-names*)
(collect-plausible-misspellings 'integr-listp *topic-names*)
(collect-plausible-misspellings 'intager-listp *topic-names*)
(collect-plausible-misspellings 'appnd *topic-names*)
(collect-plausible-misspellings 'apend *topic-names*)
(collect-plausible-misspellings 'revapp *topic-names*)

(collect-plausible-misspellings 'integr--listp *topic-names*)
(collect-plausible-misspellings 'integrlistp *topic-names*)

(collect-plausible-misspellings 'listp-integer *topic-names*)

(collect-plausible-misspellings 'vl-nat-listp *topic-names*)
(collect-plausible-misspellings 'maybe-integerp *topic-names*)
(collect-plausible-misspellings 'maybe-integer-p *topic-names*)
(collect-plausible-misspellings 'maybe-stringp *topic-names*)
(collect-plausible-misspellings 'maybe-string-p *topic-names*)

||#


; Ranking the candidates.  The general hope is that the use of desperation
; levels above should give us only a few candidates to choose from, all of
; which are pretty likely.  As a stupid way to rank the candidates and choose
; the "best" ones, we'll introduce a stupid heuristic:
;
;    - Consider each character c that occurs in the goal name and in the
;      candidate name, excluding hyphens.
;
;    - Sum the differences been how many times each such c occurs in the
;      goal, versus how many times it occurs in the candidate.
;
; The candidate with the lowest score wins.  This dumb heuristic should prefer
; candidates that are simple permutations of words, transpositions of
; characters, or where just one character was missing, etc., over candidates
; that have more significant differences.

(defun candidate-score-aux (domain goal-chars candidate-chars)
  (declare (xargs :guard (and (character-listp domain)
                              (character-listp goal-chars)
                              (character-listp candidate-chars))))
  (b* (((when (atom domain))
        0)
       (n1   (acl2::duplicity (car domain) goal-chars))
       (n2   (acl2::duplicity (car domain) candidate-chars))
       (diff (abs (- n1 n2))))
      (+ diff
         (candidate-score-aux (cdr domain) goal-chars candidate-chars))))

(defun candidate-score (goal candidate)
  (declare (xargs :guard (and (stringp goal)
                              (stringp candidate))))
  (b* ((goal-chars      (str::explode (str::downcase-string goal)))
       (candidate-chars (str::explode (str::downcase-string candidate)))
       (domain          (remove #\- (mergesort
                                     (append goal-chars candidate-chars)))))
      (candidate-score-aux domain goal-chars candidate-chars)))

(defun rank-candidates (goal candidates)
  ;; Builds an alist of (score . candidate)
  (declare (xargs :guard (and (symbolp goal)
                              (symbol-listp candidates))))
  (if (atom candidates)
      nil
    (cons (cons (candidate-score (symbol-name goal)
                                 (symbol-name (car candidates)))
                (car candidates))
          (rank-candidates goal (cdr candidates)))))

(defun sort-candidates (goal candidates)
  (declare (xargs :guard (and (symbolp goal)
                              (symbol-listp candidates))))
  (strip-cdrs (mergesort (rank-candidates goal candidates))))


(defun xdoc-autocorrect (goal topic-names)
  ;; Returns a list of possible topics that the user might have meant
  (declare (xargs :guard (and (symbolp goal)
                              (symbol-listp topic-names))))
  (b* ((candidates (collect-plausible-misspellings goal topic-names))
       (candidates (sort-candidates goal candidates)))
    (take (min (len candidates) 5)
          candidates)))


#||

(xdoc-autocorrect 'aples '(appoles apples appals apols appals appels appllas appallas app-les))

||#

