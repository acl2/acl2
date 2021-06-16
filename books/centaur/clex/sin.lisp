; Centaur Lexer Library
; Copyright (C) 2013 Centaur Technology
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

(in-package "CLEX")
(include-book "strin")
(include-book "std/stobjs/absstobjs" :dir :system)
(include-book "std/strings/strpos" :dir :system)
(local (include-book "arithmetic"))
(local (in-theory (disable acl2::update-nth-when-zp)))

(defxdoc sin
  :parents (clex)
  :short "Abstract @(see acl2::stobj) for a string input stream."

  :long "<p>The @('sin') (\"string input\") stobj allows you to efficiently,
easily process strings in a stream-like, sequential fashion, while remembering
the line and column number you are currently at and (if applicable) the name of
the file that the input came from.</p>

<p>This abstraction is especially useful for writing lexers or parsers, which
typically involve scanning through the string from the front, and breaking it
apart into individual tokens.  Practically speaking, any lexer or parser that
will actually be used needs to be able to provide location information to help
its user track down errors.</p>

<p>Logically, the @('sin') stobj is viewed as a @(see strin-p) structure. which
is an ordinary @(see defaggregate) with a character list, line number, column
number, and filename.  In the execution, the character list is replaced with a
string and an index into that string, and destructive updates are used to keep
memory usage down.</p>

@(def sin)")


(defsection sin$c
  :parents (sin)
  :short "Concrete string input stream @(see acl2::stobj)."

  :long "<p>In the implementation, we take care to ensure that all indices
satisfy @('(unsigned-byte-p 60)'), making them fixnums on Lisps such as CCL and
SBCL.  For this to work, we also use 0-based line number indices instead of
1-based line numbers, which ensures that both the line and column numbers never
exceed the current position.</p>

@(def sin-str-p)
@(def sin$cp)"
  :autodoc nil

  (define sin-str-p (x)
    :enabled t
    (and (stringp x)
         (< (len (coerce x 'list)) (expt 2 60))))

  (defstobj sin$c
    (sin$c-str  :type (satisfies sin-str-p)  :initially "")
    (sin$c-pos  :type (unsigned-byte 60)     :initially 0)
    (sin$c-line :type (unsigned-byte 60)     :initially 0)
    (sin$c-col  :type (unsigned-byte 60)     :initially 0)
    (sin$c-file :type string                 :initially "")
    :inline t))

(define sin$c-okp (sin$c)
  :parents (sin$c)
  :short "Basic well-formedness of the concrete @(see sin$c) stobj."
  :enabled t
  (b* ((str  (sin$c-str sin$c))
       (pos  (sin$c-pos sin$c))
       (line (sin$c-line sin$c))
       (col  (sin$c-col sin$c))
       (file (sin$c-file sin$c)))
    (and (stringp str)
         (natp pos)
         (natp line)
         (natp col)
         (stringp file)
         (<= pos (length str))
         (<= line pos)
         (<= col pos))))

(define sin$corr (sin$c x)
  :parents (sin$c)
  :short "Correspondence between the concrete @(see sin$c) stobj and its
abstract @(see strin-p) representation."
  :enabled t
  (and (sin$c-okp sin$c)
       (strin-p x)
       (b* (((strin x) x)
            (chars (strin-left x))
            (str   (sin$c-str sin$c))
            (pos   (sin$c-pos sin$c))
            (line  (sin$c-line sin$c))
            (col   (sin$c-col sin$c))
            (file  (sin$c-file sin$c)))
         (and
          (equal chars (nthcdr pos (coerce str 'list)))
          ;; Line numbers start at 0 internally but 1 externally.
          (equal x.line  (+ 1 line))
          (equal x.col   col)
          (equal x.file  file)))))

(define sin$c-init ((contents stringp)
                    (filename stringp)
                    sin$c)
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-init)."
  (b* ((sin$c (update-sin$c-pos  0        sin$c))
       (sin$c (update-sin$c-line 0        sin$c))
       (sin$c (update-sin$c-col  0        sin$c))
       (sin$c (update-sin$c-file filename sin$c)))
    (mbe :logic
         (update-sin$c-str contents sin$c)
         :exec
         (if (< (the (integer 0 *) (length contents)) (expt 2 60))
             (update-sin$c-str contents sin$c)
           (ec-call (update-sin$c-str contents sin$c)))))
  ///
  (defthm sin-init{correspondence}
    (implies (and (sin$corr sin$c x)
                  (stringp contents)
                  (stringp filename)
                  (strin-p x))
             (sin$corr (sin$c-init contents filename sin$c)
                       (strin-init contents filename x)))))


(define sin$c-endp ((sin$c sin$c-okp))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-endp)."
  :inline t
  (b* (((the string str)             (sin$c-str sin$c))
       ((the (unsigned-byte 60) pos) (sin$c-pos sin$c))
       ((the (unsigned-byte 60) len) (length str)))
    (eql pos len))
  ///
  (defthm sin-endp{correspondence}
    (implies (and (sin$corr sin$c x)
                  (strin-p sin))
             (equal (sin$c-endp$inline sin$c)
                    (strin-endp x)))))


(define sin$c-len ((sin$c sin$c-okp))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-len)."
  :inline t
  :enabled t
  (b* (((the string str)             (sin$c-str sin$c))
       ((the (unsigned-byte 60) pos) (sin$c-pos sin$c))
       ((the (unsigned-byte 60) len) (length str)))
    (the (unsigned-byte 60) (- len pos)))
  ///
  (defthm sin-len{correspondence}
    (implies (and (sin$corr sin$c x)
                  (strin-p x))
             (equal (sin$c-len sin$c)
                    (strin-len x)))))


(define sin$c-car ((sin$c sin$c-okp))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-car)."
  :inline t
  (b* (((the string str)             (sin$c-str sin$c))
       ((the (unsigned-byte 60) pos) (sin$c-pos sin$c))
       ((the (unsigned-byte 60) len) (length str)))
    (if (eql pos len)
        nil
      (the character (char str pos))))
  ///
  (defthm sin-car{correspondence}
    (implies (and (sin$corr sin$c sin)
                  (strin-p sin))
             (equal (sin$c-car$inline sin$c)
                    (strin-car sin)))))


(define sin$c-nth ((n natp) (sin$c sin$c-okp))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-nth)."
  :inline t
  (b* (((the string str)             (sin$c-str sin$c))
       ((the (unsigned-byte 60) pos) (sin$c-pos sin$c))
       ((the (unsigned-byte 60) len) (length str))
       ((the (integer 0 *) idx)      (+ pos n))
       ((when (>= idx len))
        nil))
    (the character (char str idx)))
  ///
  (DEFTHM SIN-NTH{CORRESPONDENCE}
    (IMPLIES (AND (SIN$CORR SIN$C SIN)
                  (NATP N)
                  (STRIN-P SIN))
             (EQUAL (SIN$C-NTH$INLINE N SIN$C)
                    (STRIN-NTH N SIN)))))


(define sin$c-firstn ((n natp) (sin$c sin$c-okp))
  :guard (<= n (sin$c-len sin$c))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-firstn)."
  :guard-hints(("Goal" :in-theory (enable sin$c-len)))
  (b* (((the string str)             (sin$c-str sin$c))
       ((the (unsigned-byte 60) pos) (sin$c-pos sin$c))
       ((the (unsigned-byte 60) len) (length str))
       ((the (unsigned-byte 60) stop)
        (+ pos (the (unsigned-byte 60) n))))
    (the string (subseq (the string str) pos stop)))
  ///
  (local (in-theory (enable subseq subseq-list)))
  (DEFTHM SIN-FIRSTN{CORRESPONDENCE}
    (IMPLIES (AND (SIN$CORR SIN$C SIN)
                  (NATP N)
                  (STRIN-P SIN)
                  (<= N (STRIN-LEN SIN)))
             (EQUAL (SIN$C-FIRSTN N SIN$C)
                    (STRIN-FIRSTN N SIN)))))


(define sin$c-cdr ((sin$c sin$c-okp))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-cdr)."
  :long "<p>This is not very efficient.  It's better to use @(see sin$c-nthcdr)
than to use this in a loop.</p>"
  (b* (((the string str)             (sin$c-str sin$c))
       ((the (unsigned-byte 60) pos) (sin$c-pos sin$c))
       ((the (unsigned-byte 60) len) (length str))
       ((when (eql pos len))
        sin$c)
       ((the character char1)        (char str pos))
       ((the (unsigned-byte 60) pos) (+ 1 pos)))
    (if (eql char1 #\Newline)
        (b* (((the (unsigned-byte 60) line) (sin$c-line sin$c))
             ((the (unsigned-byte 60) line) (+ 1 line))
             (sin$c (update-sin$c-col 0 sin$c))
             (sin$c (update-sin$c-line line sin$c)))
          (update-sin$c-pos pos sin$c))
      (b* (((the (unsigned-byte 60) col) (sin$c-col sin$c))
           ((the (unsigned-byte 60) col) (+ 1 col))
           (sin$c (update-sin$c-col col sin$c)))
        (update-sin$c-pos pos sin$c))))
  ///
  (local (in-theory (enable strin-cdr)))
  (DEFTHM SIN-CDR{CORRESPONDENCE}
    (IMPLIES (AND (SIN$CORR SIN$C SIN) (STRIN-P SIN))
             (SIN$CORR (SIN$C-CDR SIN$C)
                       (STRIN-CDR SIN)))))



(define sin$c-nthcdr ((n natp) (sin$c sin$c-okp))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-nthcdr)."
  (b* (((the string str)              (sin$c-str  sin$c))
       ((the (unsigned-byte 60) pos)  (sin$c-pos  sin$c))
       ((the (unsigned-byte 60) line) (sin$c-line sin$c))
       ((the (unsigned-byte 60) col)  (sin$c-col  sin$c))
       ((the (unsigned-byte 60) len)  (length str))
       ((mv (the (unsigned-byte 60) new-pos)
            (the (unsigned-byte 60) new-line)
            (the (unsigned-byte 60) new-col))
        (if (< (the (integer 0 *) n) (expt 2 60))
            (lc-nthcdr-str-fast n str pos len line col)
          (ec-call
           (lc-nthcdr-str-fast n str pos len line col))))
       (sin$c (update-sin$c-line new-line sin$c))
       (sin$c (update-sin$c-col  new-col  sin$c)))
    (update-sin$c-pos new-pos sin$c))
  ///

  ;; The correspondence is a bit tricky because of the use of 0-indexing in the
  ;; implementation and 1-indexing in the interface.  We have to show that
  ;; line-after-nthcdr is sort of monotonic, i.e., if we give it the same
  ;; string but line+1 to start with, then it'll produce new-line+1.

  (local (in-theory (enable strin-nthcdr)))

  (local (define count-newlines ((x character-listp))
           :returns (num-newlines natp :rule-classes :type-prescription)
           (cond ((atom x)
                  0)
                 ((eql (car x) #\Newline)
                  (+ 1 (count-newlines (cdr x))))
                 (t
                  (count-newlines (cdr x))))))

  (local (defthmd line-after-nthcdr-removal
           (equal (line-after-nthcdr n x line)
                  (+ (count-newlines (take n x))
                     (nfix line)))
           :hints(("Goal" :in-theory (enable line-after-nthcdr
                                             count-newlines
                                             acl2::take)))))

  (local (defthmd l0
           (implies (equal new-line (line-after-nthcdr n x line))
                    (equal (line-after-nthcdr n x line2)
                           (+ (nfix (- (nfix new-line) (nfix line)))
                              (nfix line2))))
           :hints(("Goal" :in-theory (enable line-after-nthcdr-removal)))))

  (local (defthm l1
           (implies (and (EQUAL (STRIN->LINE SIN) (+ 1 LINE2))
                         (force (strin-p sin))
                         (force (natp line2)))
                    (EQUAL (LINE-AFTER-NTHCDR N (STRIN-LEFT SIN) (STRIN->LINE SIN))
                           (+ 1
                              (LINE-AFTER-NTHCDR N (STRIN-LEFT SIN) LINE2))))
           :hints(("Goal"
                   :in-theory (enable line-after-nthcdr-removal)
                   :use ((:instance l0
                                    (line (STRIN->LINE SIN))
                                    (line2 (+ 1 LINE2))
                                    (new-line
                                     (LINE-AFTER-NTHCDR N (STRIN-LEFT SIN)
                                                        (STRIN->LINE SIN)))))))))

  (DEFTHM SIN-NTHCDR{CORRESPONDENCE}
    (IMPLIES (AND (SIN$CORR SIN$C SIN)
                  (NATP N)
                  (STRIN-P SIN))
             (SIN$CORR (SIN$C-NTHCDR N SIN$C)
                       (STRIN-NTHCDR N SIN)))))



(define sin$c-matches-p ((lit stringp) (sin$c sin$c-okp))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-matches-p)."
  (b* (((the string str)             (sin$c-str sin$c))
       ((the (unsigned-byte 60) pos) (sin$c-pos sin$c))
       ((the (unsigned-byte 60) len) (length str))
       ((the (integer 0 *) litlen)   (length lit)))
    (str::strprefixp-impl lit str 0 pos litlen len))
  ///
  (DEFTHM SIN-MATCHES-P{CORRESPONDENCE}
    (IMPLIES (AND (SIN$CORR SIN$C SIN)
                  (STRINGP LIT)
                  (STRIN-P SIN))
             (EQUAL (SIN$C-MATCHES-P LIT SIN$C)
                    (STRIN-MATCHES-P LIT SIN)))))

(define sin$c-imatches-p ((lit stringp) (sin$c sin$c-okp))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-imatches-p)."
  :enabled t
  (b* (((the string str)             (sin$c-str sin$c))
       ((the (unsigned-byte 60) pos) (sin$c-pos sin$c))
       ((the (unsigned-byte 60) len) (length str))
       ((the (integer 0 *) litlen)   (length lit)))
    (str::istrprefixp-impl lit str 0 pos litlen len))
  ///
  (DEFTHM SIN-IMATCHES-P{CORRESPONDENCE}
    (IMPLIES (AND (SIN$CORR SIN$C SIN)
                  (STRINGP LIT)
                  (STRIN-P SIN))
             (EQUAL (SIN$C-IMATCHES-P LIT SIN$C)
                    (STRIN-IMATCHES-P LIT SIN)))))

(define sin$c-count-charset ((set charset-p) (sin$c sin$c-okp))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-count-charset)."
  (b* (((the string str)             (sin$c-str sin$c))
       ((the (unsigned-byte 60) pos) (sin$c-pos sin$c))
       ((the (unsigned-byte 60) len) (length str)))
    (str-count-leading-charset-fast pos str len set))
  ///
  (DEFTHM SIN-COUNT-CHARSET{CORRESPONDENCE}
    (IMPLIES (AND (SIN$CORR SIN$C SIN)
                  (CHARSET-P SET)
                  (STRIN-P SIN))
             (EQUAL (SIN$C-COUNT-CHARSET SET SIN$C)
                    (STRIN-COUNT-CHARSET SET SIN)))))

(define sin$c-find ((lit stringp) (sin$c sin$c-okp))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-find)."
  (b* (((the string str)             (sin$c-str sin$c))
       ((the (unsigned-byte 60) pos) (sin$c-pos sin$c))
       ((the (unsigned-byte 60) len) (length str))
       ((the (integer 0 *) litlen)   (length lit))
       (idx (str::strpos-fast lit str pos litlen len)))
    (and idx
         (the (unsigned-byte 60) (- idx pos))))
  ///
  (DEFTHM SIN-FIND{CORRESPONDENCE}
    (IMPLIES (AND (SIN$CORR SIN$C SIN)
                  (STRINGP LIT)
                  (STRIN-P SIN))
             (EQUAL (SIN$C-FIND LIT SIN$C)
                    (STRIN-FIND LIT SIN)))))



(define strin-get-line ((x strin-p))
  :returns (col posp :rule-classes :type-prescription)
  :parents (strin-p)
  :short "Wrapper for @(see strin->line) that fixes the line number to a @(see
posp)."
  :long "<p>This just lets us always assume that @('sin-line') is a posp.  We
typically just leave this disabled, because who wants to reason about line
numbers?</p>"
  :inline t
  (mbe :logic (let ((line (strin->line x)))
                (if (posp line)
                    line
                  1))
       :exec (strin->line x)))

(define sin$c-get-line ((sin$c sin$c-okp))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-get-line)."
  :inline t
  (+ 1 (sin$c-line sin$c))
  ///
  (defthm sin-line{correspondence}
    (implies (and (sin$corr sin$c x)
                  (strin-p sin))
             (equal (sin$c-get-line sin$c)
                    (strin-get-line x)))
    :hints(("Goal" :in-theory (enable strin-get-line)))))


(define strin-get-col ((x strin-p))
  :returns (col natp :rule-classes :type-prescription)
  :parents (strin-p)
  :short "Wrapper for @(see strin->col) that fixes the column number to a @(see
natp)."
  :long "<p>This just lets us always assume that @('sin-col') is a natural.  We
typically just leave this disabled, because who wants to reason about column
number?  (Well, maybe for Python you need something like that...)</p>"
  :inline t
  (lnfix (strin->col x)))

(define sin$c-get-col ((sin$c sin$c-okp))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-get-col)."
  :inline t
  (sin$c-col sin$c)
  ///
  (defthm sin-col{correspondence}
    (implies (and (sin$corr sin$c x)
                  (strin-p sin))
             (equal (sin$c-get-col sin$c)
                    (strin-get-col x)))
    :hints(("Goal" :in-theory (enable strin-get-col)))))


(define strin-get-file ((x strin-p))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (strin-p)
  :short "Simple wrapper that fixes the filename number to a string."
  :long "<p>This just lets us always assume that @('sin-file') is a string.  We
typically leave this disabled, because there's not much reason to want to expose
the implementation.</p>"
  :inline t
  (mbe :logic (let ((file (strin->file x)))
                (if (stringp file)
                    file
                  ""))
       :exec (strin->file x)))

(define sin$c-get-file ((sin$c sin$c-okp))
  :parents (sin$c)
  :short "Concrete implementation of @(see strin-get-file)."
  :inline t
  (sin$c-file sin$c)
  ///
  (defthm sin-file{correspondence}
    (implies (and (sin$corr sin$c x)
                  (strin-p sin))
             (equal (sin$c-get-file sin$c)
                    (strin-get-file x)))
    :hints(("Goal" :in-theory (enable strin-get-file)))))




(defabsstobj-events sin
  :foundation sin$c
  :recognizer (sinp :logic strin-p
                    :exec sin$cp)
  :creator (create-sin :logic empty-strin
                       :exec create-sin$c)
  :corr-fn sin$corr
  :exports ((sin-init :logic strin-init
                      :exec  sin$c-init
                      :protect t)

            (sin-line :logic strin-get-line$inline
                      :exec  sin$c-get-line$inline)
            (sin-col :logic strin-get-col$inline
                     :exec  sin$c-get-col$inline)
            (sin-file :logic strin-get-file$inline
                      :exec  sin$c-get-file$inline)

            (sin-endp :logic strin-endp
                      :exec  sin$c-endp$inline)
            (sin-len  :logic strin-len
                      :exec  sin$c-len$inline)
            (sin-car  :logic strin-car
                      :exec  sin$c-car$inline)
            (sin-nth  :logic strin-nth
                      :exec  sin$c-nth$inline)
            (sin-firstn :logic strin-firstn
                        :exec  sin$c-firstn)

            (sin-cdr  :logic strin-cdr
                      :exec  sin$c-cdr
                      :protect t)
            (sin-nthcdr :logic strin-nthcdr
                        :exec  sin$c-nthcdr
                        :protect t)

            (sin-matches-p :logic strin-matches-p
                           :exec  sin$c-matches-p)
            (sin-imatches-p :logic strin-imatches-p
                            :exec  sin$c-imatches-p)
            (sin-count-charset :logic strin-count-charset
                               :exec  sin$c-count-charset)
            (sin-find :logic strin-find
                      :exec  sin$c-find)

            ))
