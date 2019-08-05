; Centaur AIG Library
; Copyright (C) 2012 Centaur Technology
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
(include-book "std/util/bstar" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "std/io/base" :dir :system)
(include-book "std/util/defmvtypes" :dir :system)
(include-book "std/basic/defs" :dir :system)
(set-state-ok t)

(local (in-theory (disable w)))

(defthm w-state-of-write-byte$
  (equal (w (write-byte$ byte channel state))
         (w state))
  :hints(("Goal" :in-theory (enable write-byte$ w get-global))))

(defthm w-state-of-read-byte$
  (equal (w (mv-nth 1 (read-byte$ channel state)))
         (w state))
  :hints(("Goal" :in-theory (enable read-byte$ w get-global))))

(define write-ascii-string1 (idx str stream state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-output-channel-p stream :byte state)
                              (stringp str)
                              (natp idx))
                  :measure (nfix (- (length str) (nfix idx)))))
  :returns (new-state)
  (if (<= (length str) (lnfix idx))
      state
    (let ((state (write-byte$ (char-code (char str idx)) stream state)))
      (write-ascii-string1 (1+ (lnfix idx)) str stream state)))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state) (w state)))

  (defthm open-output-channel-p1-of-write-ascii-string1
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-output-channel-p1 stream :byte state))
             (let ((state (write-ascii-string1 idx str stream state)))
               (and (state-p1 state)
                    (open-output-channel-p1 stream :byte state))))))

(define write-ascii-string (str stream state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-output-channel-p stream :byte state)
                              (stringp str))))
  :returns (new-state)
  (write-ascii-string1 0 str stream state)
  ///
  (defret w-state-of-<fn>
    (equal (w new-state) (w state)))

  (defthm open-output-channel-p1-of-write-ascii-string
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-output-channel-p1 stream :byte state))
             (let ((state (write-ascii-string str stream state)))
               (and (state-p1 state)
                    (open-output-channel-p1 stream :byte state))))))


(encapsulate nil
  (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
  (local (in-theory (disable floor)))
  (define write-ascii-nat (n stream state)
    (declare (xargs :guard (and (symbolp stream)
                                (open-output-channel-p stream :byte state)
                                (natp n))
                    :ruler-extenders :all
                    :measure (nfix n)
                    :verify-guards nil))
    :returns (new-state)
    (b* ((n (lnfix n))
         (digit (mod n 10))
         (rest (floor n 10))
         (byte (+ (char-code #\0) digit))
         (state (if (zp rest)
                    state
                  (write-ascii-nat rest stream state))))
      (write-byte$ byte stream state))
    ///
    (defthm open-output-channel-p1-of-write-ascii-nat
      (implies (and (state-p1 state)
                    (symbolp stream)
                    (open-output-channel-p1 stream :byte state))
               (let ((state (write-ascii-nat n stream state)))
                 (and (state-p1 state)
                      (open-output-channel-p1 stream :byte state)))))

    (verify-guards write-ascii-nat)
    (defret w-state-of-<fn>
      (equal (w new-state) (w state)))))


(define maybe-byte-p (x)
  (declare (xargs :guard t))
  (or (not x)
      (bytep x))
  ///

  (defthm maybe-byte-p-of-byte
    (implies (and (natp x) (< x 256))
             (maybe-byte-p x))
    :hints(("Goal" :in-theory (enable maybe-byte-p))))

  (defthm maybe-byte-p-of-read-byte$
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-input-channel-p1 stream :byte state))
             (maybe-byte-p (mv-nth 0 (read-byte$ stream state))))
    :hints(("Goal" :in-theory (enable maybe-byte-p))))

  (defthm maybe-byte-p-compound-recognizer
    (implies (maybe-byte-p x)
             (or (not x)
                 (natp x)))
    :hints(("Goal" :in-theory (enable maybe-byte-p)))
    :rule-classes :compound-recognizer)

  (defthm maybe-byte-p-bound
    (implies (and (maybe-byte-p x)
                  x)
             (< x 256))
    :hints(("Goal" :in-theory (enable maybe-byte-p)))
    :rule-classes :forward-chaining))

(local (defthm maybe-byte-p-bound-rw
         (implies (and (maybe-byte-p x) x)
                  (< x 256))
         :rule-classes :rewrite))


(define maybe-byte-fix ((x maybe-byte-p))
  :inline t
  :returns (new-x maybe-byte-p :rule-classes (:rewrite :type-prescription))
  (mbe :logic (if (maybe-byte-p x) x 0)
       :exec x)
  ///
  (defret maybe-byte-fix-when-maybe-byte-p
    (implies (maybe-byte-p x)
             (equal (maybe-byte-fix x) x))))
  




(define read-byte-buf (stream buf state)
  :inline t
  :returns (mv byte new-buf new-state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))))
  (mbe :logic (mv-let (res buf state)
                (if buf
                    (mv buf nil state)
                  (b* (((mv byte state) (read-byte$ stream state)))
                    (mv byte nil state)))
                (mv (and (maybe-byte-p res) res) buf state))
       :exec (if buf
                 (mv buf nil state)
               (b* (((mv byte state) (read-byte$ stream state)))
                 (mv byte nil state))))
  ///

  (defthm maybe-byte-p-of-read-byte-buf-res
    (maybe-byte-p (mv-nth 0 (read-byte-buf stream buf state)))
    :rule-classes (:rewrite
                   (:type-prescription

; Added by Matt K., 8/9/2014: the :typed-term provided below was implicit
; before an ACL2 change considered for source function
; find-type-prescription-pat, which avoids using weak compound-recognizer rules
; (in this case, maybe-byte-p-compound-recognizer) to infer the :typed-term
; when it is not supplied.  I'm now making the :typed-term explicit so that
; this book certifies regardless of whether or not such a change is made to
; ACl2.

; See also maybe-byte-p-of-peek-byte-buf-res, which has been modified in the
; same way for the same reason.

                    :typed-term
                    (mv-nth 0 (read-byte-buf stream buf state)))))

  (defthm maybe-byte-p-of-read-byte-buf-buf
    (maybe-byte-p (mv-nth 1 (read-byte-buf stream buf state)))
    :rule-classes (:rewrite :type-prescription))
  
  (defret w-state-of-<fn>
    (equal (w new-state) (w state)))

  (defthm open-input-channel-p1-of-read-byte-buf
    (implies (and (symbolp stream)
                  (state-p1 state)
                  (open-input-channel-p1 stream :byte state))
             (b* (((mv & & state) (read-byte-buf stream buf state)))
               (and (open-input-channel-p1 stream :byte state)
                    (state-p1 state))))))

(define peek-byte-buf (stream buf state)
  :inline t
  :returns (mv byte new-buf new-state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))))
  (mbe :logic (mv-let (res buf state)
                (if (and (maybe-byte-p buf) buf)
                    (mv buf buf state)
                  (b* (((mv byte state) (read-byte$ stream state)))
                    (mv byte byte state)))
                (mv (and (maybe-byte-p res) res)
                    (and (maybe-byte-p buf) buf)
                    state))
       :exec (if buf
                 (mv buf buf state)
               (b* (((mv byte state) (read-byte$ stream state)))
                 (mv byte byte state))))
  ///


  (defthm maybe-byte-p-of-peek-byte-buf-res
    (maybe-byte-p (mv-nth 0 (peek-byte-buf stream buf state)))
    :rule-classes (:rewrite (:type-prescription

; Added by Matt K., 8/9/2014: See the comment in
; maybe-byte-p-of-read-byte-buf-res, which is equally applicable here.

                             :typed-term
                             (mv-nth 0 (peek-byte-buf stream buf state)))))

  (defthm maybe-byte-p-of-peek-byte-buf-buf
    (maybe-byte-p (mv-nth 1 (peek-byte-buf stream buf state)))
    :rule-classes (:rewrite :type-prescription))

  (defthm peek-byte-buf-of-peek-byte-buf
    (implies (mv-nth 0 (peek-byte-buf stream buf state))
             (equal (peek-byte-buf stream
                                   (mv-nth 1 (peek-byte-buf stream buf state))
                                   (mv-nth 2 (peek-byte-buf stream buf state)))
                    (peek-byte-buf stream buf state))))

  (defthm open-input-channel-p1-of-peek-byte-buf
    (implies (and (symbolp stream)
                  (state-p1 state)
                  (open-input-channel-p1 stream :byte state))
             (b* (((mv & & state) (peek-byte-buf stream buf state)))
               (and (open-input-channel-p1 stream :byte state)
                    (state-p1 state)))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(define skip-byte-buf (stream buf state)
  :inline t
  :returns (mv new-buf new-state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state))))
  (if buf
      (mv nil state)
    (b* (((mv & state) (read-byte$ stream state)))
      (mv nil state)))
  ///

  (defthm maybe-byte-p-of-skip-byte-buf
    (maybe-byte-p (mv-nth 0 (skip-byte-buf stream buf state)))
    :rule-classes (:rewrite :type-prescription))

  (defthm open-input-channel-p1-of-skip-byte-buf
    (implies (and (symbolp stream)
                  (state-p1 state)
                  (open-input-channel-p1 stream :byte state))
             (b* (((mv & state) (skip-byte-buf stream buf state)))
               (and (open-input-channel-p1 stream :byte state)
                    (state-p1 state)))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))



(define aiger-buf-measure (stream buf state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))))
  (+ (if buf 1 0) (non-exec (file-measure stream state)))
  ///

  (defthm aiger-buf-measure-of-read-byte-buf-weak
    (b* (((mv & buf1 state1) (read-byte-buf stream buf state)))
      (<= (aiger-buf-measure stream buf1 state1)
          (aiger-buf-measure stream buf state)))
    :hints(("Goal" :in-theory (enable read-byte-buf)))
    :rule-classes :linear)

  (defthm aiger-buf-measure-of-read-byte-buf-strong
    (b* (((mv res1 buf1 state1) (read-byte-buf stream buf state)))
      (implies res1
               (< (aiger-buf-measure stream buf1 state1)
                  (aiger-buf-measure stream buf state))))
    :hints(("Goal" :in-theory (enable read-byte-buf)))
    :rule-classes :linear)

  ;; there is no strong
  (defthm aiger-buf-measure-of-peek-byte-buf
    (b* (((mv & buf1 state1) (peek-byte-buf stream buf state)))
      (<= (aiger-buf-measure stream buf1 state1)
          (aiger-buf-measure stream buf state)))
    :hints(("Goal" :in-theory (enable peek-byte-buf)))
    :rule-classes :linear)

  ;; there is no strong
  (defthm aiger-buf-measure-of-skip-byte-buf
    (b* (((mv buf1 state1) (skip-byte-buf stream buf state)))
      (<= (aiger-buf-measure stream buf1 state1)
          (aiger-buf-measure stream buf state)))
    :hints(("Goal" :in-theory (enable skip-byte-buf)))
    :rule-classes :linear)

  (defthm aiger-buf-measure-of-skip-byte-buf-strong-by-peek
    (b* (((mv peek buf1 state1) (peek-byte-buf stream buf state))
         ((mv buf2 state2) (skip-byte-buf stream buf1 state1)))
      (implies peek
               (< (aiger-buf-measure stream buf2 state2)
                  (aiger-buf-measure stream buf state))))
    :hints(("Goal" :in-theory (enable peek-byte-buf
                                      skip-byte-buf)))
    :rule-classes :linear))





(define read-ascii-nat1 (rest stream buf state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf)
                              (natp rest))
                  :measure (aiger-buf-measure stream buf state)))
  :returns (mv (nat natp :rule-classes :type-prescription)
               (new-buf maybe-byte-p :rule-classes (:rewrite :type-prescription))
               (new-state))
  (b* (((mv byte buf state) (peek-byte-buf stream buf state))
       ((when (not (and (integerp byte)
                        (<= (char-code #\0) byte)
                        (<= byte (char-code #\9)))))
        (mv (lnfix rest) buf state))
       ((mv buf state) (skip-byte-buf stream buf state)))
    (read-ascii-nat1
     (+ (* 10 (lnfix rest)) (- byte (char-code #\0)))
     stream buf state))
  ///

  (defthm open-input-channel-p1-of-read-ascii-nat1
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-input-channel-p1 stream :byte state))
             (b* (((mv & & state)
                   (read-ascii-nat1 rest stream buf state)))
               (and (state-p1 state)
                    (open-input-channel-p1 stream :byte state)))))

  (defthm aiger-buf-measure-of-read-ascii-nat1
    (b* (((mv & buf1 state1)
          (read-ascii-nat1 rest stream buf state)))
      (<= (aiger-buf-measure stream buf1 state1)
          (aiger-buf-measure stream buf state)))
    :rule-classes :linear)

  
  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(local (defthm maybe-natp-compound-recognzier
         (equal (maybe-natp x)
                (or (not x)
                    (natp x)))
         :rule-classes :compound-recognizer))

(define read-ascii-nat (stream buf state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))))
  :returns (mv (res maybe-natp :rule-classes :type-prescription)
               (new-buf maybe-byte-p :rule-classes (:rewrite :type-prescription))
               (new-state))
  (b* (((mv byte buf state) (peek-byte-buf stream buf state))
       ((when (not (and (integerp byte)
                        (<= (char-code #\0) byte)
                        (<= byte (char-code #\9)))))
        (mv nil buf state))
       ((mv buf state) (skip-byte-buf stream buf state)))
    (read-ascii-nat1
     (- byte (char-code #\0))
     stream buf state))
  ///

  (defthm natp-read-ascii-nat-when-peek
    (implies (b* ((n (mv-nth 0 (peek-byte-buf stream buf state))))
               (and (integerp n)
                    (<= (char-code #\0) n)
                    (<= n (char-code #\9))))
             (natp (mv-nth 0 (read-ascii-nat stream buf state))))
    :hints(("Goal" :in-theory (enable read-ascii-nat))))

  (defthm integerp-read-ascii-nat-when-peek
    ;; BOZO horrible
    (implies (b* ((n (mv-nth 0 (peek-byte-buf stream buf state))))
               (and (integerp n)
                    (<= (char-code #\0) n)
                    (<= n (char-code #\9))))
             (integerp (mv-nth 0 (read-ascii-nat stream buf state))))
    :hints(("Goal"
            :in-theory (disable natp-read-ascii-nat-when-peek
                                read-ascii-nat)
            :use ((:instance natp-read-ascii-nat-when-peek)))))

  (defthm open-input-channel-p1-of-read-ascii-nat
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-input-channel-p1 stream :byte state))
             (b* (((mv & & state)
                   (read-ascii-nat stream buf state)))
               (and (state-p1 state)
                    (open-input-channel-p1 stream :byte state)))))

  (defthm aiger-buf-measure-of-read-ascii-nat-weak
    (b* (((mv & buf1 state1)
          (read-ascii-nat stream buf state)))
      (<= (aiger-buf-measure stream buf1 state1)
          (aiger-buf-measure stream buf state)))
    :rule-classes :linear)

  (defthm aiger-buf-measure-of-read-ascii-nat-strong
    (b* (((mv res buf1 state1)
          (read-ascii-nat stream buf state)))
      (implies res
               (< (aiger-buf-measure stream buf1 state1)
                  (aiger-buf-measure stream buf state))))
    :rule-classes :linear)

  (defthm aiger-buf-measure-of-read-ascii-nat-strong1
    (b* (((mv & buf1 state1)
          (read-ascii-nat stream buf state))
         (byte1 (mv-nth 0 (peek-byte-buf stream buf state))))
      (implies (and (integerp byte1)
                    (<= (char-code #\0) byte1)
                    (<= byte1 (char-code #\9)))
               (< (aiger-buf-measure stream buf1 state1)
                  (aiger-buf-measure stream buf state))))
    :rule-classes :linear)

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))



(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (in-theory (enable* ihsext-bounds-thms)))

(local (defthm logtail-decr
         (implies (and (posp n)
                       (posp s))
                  (< (logtail s n) n))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)
                 :induct t))
         :rule-classes :linear))

(local (defthm logtail-decr2
         (implies (and (posp (logtail s n))
                       (posp s))
                  (< (logtail s n) n))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)
                 :induct t))
         :rule-classes :linear))


(local
 (encapsulate nil
   (local (defthm bound-when-logtail-7-is-0-lemma
            (implies (and (equal (logtail n x) 0)
                          (natp x)
                          (natp n))
                     (< x (ash 1 n)))
            :hints (("goal" :in-theory (enable* ihsext-inductions
                                                ihsext-recursive-redefs)))
            :rule-classes nil))
   (defthm bound-when-logtail-7-is-0
     (implies (and (equal (logtail 7 x) 0)
                   (natp x)
                   (natp n))
              (< x 128))
     :rule-classes :forward-chaining
     :hints (("goal" :use ((:instance bound-when-logtail-7-is-0-lemma
                            (n 7))))))

   (defthm logior-128-loghead-7-bound
     (< (logior 128 (loghead 7 n)) 256)
     :hints (("goal" :use ((:instance unsigned-byte-p-of-loghead
                            (size1 8) (size 7) (i n))
                           (:instance unsigned-byte-p-of-logior
                            (n 8) (i 128) (j (loghead 7 n))))
              :in-theory (disable unsigned-byte-p-of-logior
                                  unsigned-byte-p-of-loghead))))))

(define aiger-write-delta (n stream state)
  (declare (xargs :guard (and (natp n)
                              (symbolp stream)
                              (open-output-channel-p stream :byte state))
                  :verify-guards nil
                  :measure (nfix n)))
  :returns (new-state)
  (b* ((n (lnfix n))
       (nextn (ash n -7))
       (donep (zp nextn))
       (newbyte (if donep n (logior #x80 (logand #x7F n))))
       (state (write-byte$ newbyte stream state)))
    (if donep
        state
      (aiger-write-delta nextn stream state)))
  ///

  (defret w-state-of-<fn>
    (equal (w new-state) (w state)))


  (verify-guards aiger-write-delta)

  (defthm open-output-channel-p1-of-aiger-write-delta
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-output-channel-p1 stream :byte state))
             (let ((state (aiger-write-delta n stream state)))
               (and (state-p1 state)
                    (open-output-channel-p1 stream :byte state))))))


(define write-char-separated-ascii-nat-list (lst sep stream state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-output-channel-p stream :byte state)
                              (nat-listp lst)
                              (characterp sep))))
  :returns (new-state)
  (if (atom lst)
      state
    (b* ((state (write-ascii-nat (car lst) stream state))
         (state (write-byte$ (char-code sep) stream state)))
      (write-char-separated-ascii-nat-list
       (cdr lst) sep stream state)))
  ///

  (defret w-state-of-<fn>
    (equal (w new-state) (w state)))

  (defthm open-output-channel-p1-of-write-char-separated-ascii-nat-list
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-output-channel-p1 stream :byte state))
             (let ((state (write-char-separated-ascii-nat-list lst sep stream state)))
               (and (state-p1 state)
                    (open-output-channel-p1 stream :byte state))))))

(define write-char-separated-ascii-nat-list-no-end (lst sep stream state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-output-channel-p stream :byte state)
                              (nat-listp lst)
                              (characterp sep))))
  :returns (new-state)
  (if (atom lst)
      state
    (b* ((state (write-ascii-nat (car lst) stream state))
         (state (if (consp (cdr lst))
                    (write-byte$ (char-code sep) stream state)
                  state)))
      (write-char-separated-ascii-nat-list-no-end
       (cdr lst) sep stream state)))
  ///

  (defret w-state-of-<fn>
    (equal (w new-state) (w state)))

  (defthm open-output-channel-p1-of-write-char-separated-ascii-nat-list-no-end
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-output-channel-p1 stream :byte state))
             (let ((state (write-char-separated-ascii-nat-list-no-end lst sep stream state)))
               (and (state-p1 state)
                    (open-output-channel-p1 stream :byte state))))))


(defun drop-trailing-0s (lst)
  (declare (Xargs :guard t))
  (if (Atom lst)
      nil
    (let ((rest (drop-trailing-0s (cdr lst))))
      (if rest
          (cons (car lst) rest)
        (if (eql (car lst) 0)
            nil
          (list (car lst)))))))

(defthm nat-listp-drop-trailing-0s
  (implies (nat-listp x)
           (nat-listp (drop-trailing-0s x))))

(define aiger-write-header (maxvar nins nlatches nouts ngates nbads ncnstrs stream state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-output-channel-p stream :byte state)
                              (natp maxvar) (natp nins) (natp nlatches) (natp nouts)
                              (natp ngates) (natp nbads) (natp ncnstrs))))
  :returns (new-state)
  (b* ((state (write-ascii-string "aig " stream state))
       (state (write-char-separated-ascii-nat-list-no-end
               (append (list maxvar nins nlatches nouts ngates)
                       (drop-trailing-0s (list nbads ncnstrs)))
               #\Space stream state))
       (state (write-byte$ (char-code #\Newline) stream state)))
    state)
  ///

  (defret w-state-of-<fn>
    (equal (w new-state) (w state)))

  (defthm open-output-channel-p1-of-aiger-write-header
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-output-channel-p1 stream :byte state))
             (let ((state (aiger-write-header maxvar nins nlatches nouts ngates
                                              nbads ncnstrs stream state)))
               (and (state-p1 state)
                    (open-output-channel-p1 stream :byte state))))))



(define skip-ascii-chars (char stream buf state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (characterp char)
                              (maybe-byte-p buf))
                  :measure (aiger-buf-measure stream buf state)))
  :returns (mv (new-buf maybe-byte-p :rule-classes (:rewrite :type-prescription))
               (new-state))
  (b* (((mv byte buf state) (peek-byte-buf stream buf state))
       ((when (not (eql byte (char-code char))))
        (mv buf state))
       ((mv buf state) (skip-byte-buf stream buf state)))
    (skip-ascii-chars char stream buf state))
  ///

  (defthm open-input-channel-p1-of-skip-ascii-chars
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-input-channel-p1 stream :byte state))
             (b* (((mv & state)
                   (skip-ascii-chars char stream buf state)))
               (and (state-p1 state)
                    (open-input-channel-p1 stream :byte state)))))

  (defthm maybe-byte-p-of-skip-ascii-chars
    (maybe-byte-p (mv-nth 0 (skip-ascii-chars char stream buf state)))
    :rule-classes (:rewrite :type-prescription))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))



(define require-ascii-str1 (idx str stream buf state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (natp idx)
                              (stringp str)
                              (<= idx (length str))
                              (maybe-byte-p buf))
                  :measure (nfix (- (length str) (nfix idx)))))
  :returns (mv ok
               (new-buf maybe-byte-p :rule-classes (:rewrite :type-prescription))
               (new-state))
  (if (<= (length str) (lnfix idx))
      (mv t (maybe-byte-fix buf) state)
    (b* (((mv byte buf state)
          (peek-byte-buf stream buf state))
         ((when (or (not byte)
                    (not (eql byte (char-code (char str idx))))))
          (cw "Bad: ~x0 ~x1~%" (char str idx)
              (if byte (code-char byte) nil))
          (mv nil buf state))
         ((mv buf state) (skip-byte-buf stream buf state)))
      (require-ascii-str1 (1+ (lnfix idx)) str stream buf state)))
  ///

  (defthm open-input-channel-p1-of-require-ascii-str1
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-input-channel-p1 stream :byte state))
             (b* (((mv & & state)
                   (require-ascii-str1 idx str stream buf state)))
               (and (state-p1 state)
                    (open-input-channel-p1 stream :byte state)))))

  (defthm maybe-byte-p-of-require-ascii-str1
    (implies (maybe-byte-p buf)
             (maybe-byte-p (mv-nth 1 (require-ascii-str1 idx str stream buf
                                                         statE))))
    :rule-classes (:rewrite :type-prescription))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(define require-ascii-str (str stream buf state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (stringp str)
                              (maybe-byte-p buf))))
  :returns (mv ok
               (new-buf maybe-byte-p :rule-classes (:rewrite :type-prescription))
               (new-state))
  (require-ascii-str1 0 str stream buf state)
  ///

  (defthm open-input-channel-p1-of-require-ascii-str
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-input-channel-p1 stream :byte state))
             (b* (((mv & & state)
                   (require-ascii-str str stream buf state)))
               (and (state-p1 state)
                    (open-input-channel-p1 stream :byte state)))))

  (defthm maybe-byte-p-of-require-ascii-str
    (implies (maybe-byte-p buf)
             (maybe-byte-p (mv-nth 1 (require-ascii-str str stream buf statE))))
    :rule-classes (:rewrite :type-prescription))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))




;; skips spaces and tabs
(define skip-linespace (stream buf state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))
                  :measure (aiger-buf-measure stream buf state)))
  :returns (mv (new-buf maybe-byte-p :rule-classes (:rewrite :type-prescription))
               (new-state))
  (b* (((mv byte buf state) (peek-byte-buf stream buf state))
       ((when (not (and (integerp byte)
                        (member (code-char byte) '(#\Space #\Tab)))))
        (mv buf state))
       ((mv buf state) (skip-byte-buf stream buf state)))
    (skip-linespace stream buf state))
  ///

  (defthm open-input-channel-p1-of-skip-linespace
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-input-channel-p1 stream :byte state))
             (b* (((mv & state)
                   (skip-linespace stream buf state)))
               (and (state-p1 state)
                    (open-input-channel-p1 stream :byte state)))))

  (defthm maybe-byte-p-of-skip-linespace
    (maybe-byte-p (mv-nth 0 (skip-linespace stream buf state)))
    :rule-classes (:rewrite :type-prescription))

  (defthm aiger-buf-measure-of-skip-linespace
    (b* (((mv  buf1 state1)
          (skip-linespace stream buf state)))
      (<= (aiger-buf-measure stream buf1 state1)
          (aiger-buf-measure stream buf state)))
    :rule-classes :linear)

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

;; Reads natural numbers until we come to some non-digit, non-space/tab
;; character.
(define read-nats-in-line (stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))
                  :measure (aiger-buf-measure stream buf state)))
  :returns (mv (nats nat-listp)
               (new-buf maybe-byte-p :rule-classes (:rewrite :type-prescription))
               (new-state))
  (b* (((mv buf state) (skip-linespace stream buf state))
       ((mv byte buf state) (peek-byte-buf stream buf state))
       ((unless (and (integerp byte)
                     (<= (char-code #\0) byte)
                     (<= byte (char-code #\9))))
        (mv nil buf state))
       ((mv head buf state) (read-ascii-nat stream buf state))
       ((mv rest buf state) (read-nats-in-line stream buf state)))
    (mv (cons head rest) buf state))
  ///
  (defthm open-input-channel-p1-of-read-nats-in-line
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-input-channel-p1 stream :byte state))
             (b* (((mv & & state)
                   (read-nats-in-line stream buf state)))
               (and (state-p1 state)
                    (open-input-channel-p1 stream :byte state)))))

  (defthm aiger-buf-measure-of-read-nats-in-line
    (b* (((mv & buf1 state1)
          (read-nats-in-line stream buf state)))
      (<= (aiger-buf-measure stream buf1 state1)
          (aiger-buf-measure stream buf state)))
    :rule-classes :linear)

  (local (defthm integerp-when-natp
           (implies (natp x)
                    (integerp x))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(defun aiger-err (msg)
  (declare (xargs :guard t))
  msg)

(define read-bytecoded-nat (stream buf state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))
                  :verify-guards nil
                  :measure (aiger-buf-measure stream buf state)))
  :returns (mv err
               (val natp :rule-classes :type-prescription)
               (new-buf maybe-byte-p :rule-classes (:rewrite :type-prescription))
               (new-state))
  (b* (((mv byte buf state) (read-byte-buf stream buf state))
       ((when (not byte))

        (mv (aiger-err "EOF while reading bytecoded natural~%")
            0 buf state))
       ((when (not (logbitp 7 byte)))
        ;; done
        (mv nil byte buf state))
       ((mv err rest buf state)
        (read-bytecoded-nat stream buf state))
       ((when err)
        (mv err 0 buf state)))
    (mv nil
        (+ (logand #x7F byte) (ash rest 7))
        buf state))
  ///

  (verify-guards read-bytecoded-nat)

  (defthm open-input-channel-p1-of-read-bytecoded-nat
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-input-channel-p1 stream :byte state))
             (b* (((mv & & & state)
                   (read-bytecoded-nat stream buf state)))
               (and (state-p1 state)
                    (open-input-channel-p1 stream :byte state)))))

  (defthm aiger-buf-measure-of-read-bytecoded-nat-weak
    (b* (((mv & & buf1 state1)
          (read-bytecoded-nat stream buf state)))
      (<= (aiger-buf-measure stream buf1 state1)
          (aiger-buf-measure stream buf state)))
    :hints (("goal" :induct (read-bytecoded-nat stream buf state)))
    :rule-classes :linear)


  (defthm aiger-buf-measure-of-read-bytecoded-nat-strong
    (b* (((mv err & buf1 state1)
          (read-bytecoded-nat stream buf state)))
      (implies (not err)
               (< (aiger-buf-measure stream buf1 state1)
                  (aiger-buf-measure stream buf state))))
    :hints (("goal" :induct (read-bytecoded-nat stream buf state)))
    :rule-classes :linear)

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))



(local
 (defthm natp-nth-in-nat-list
   (implies (and (nat-listp x)
                 (natp n)
                 (< n (len x)))
            (natp (nth n x)))
   :rule-classes (:rewrite :type-prescription)))


(define aiger-parse-header (stream buf state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))))
  :returns (mv err
               (n-ins natp :rule-classes :type-prescription)
               (n-latches natp :rule-classes :type-prescription)
               (n-ands natp :rule-classes :type-prescription)
               (n-outs natp :rule-classes :type-prescription)
               (n-bads natp :rule-classes :type-prescription)
               (n-constrs natp :rule-classes :type-prescription)
               (new-buf maybe-byte-p :rule-classes (:rewrite :type-prescription))
               (new-state))
  (b* (((mv ok buf state) (require-ascii-str "aig" stream buf state))
       ((when (not ok))
        (mv (aiger-err "Bad header: no \"aig\"~%")
            0 0 0 0 0 0 buf state))
       ((mv buf state) (skip-ascii-chars #\Space stream buf state))
       ((mv sizes buf state)
        (read-nats-in-line stream buf state))
       ((when (not (<= 5 (len sizes))))
        (mv (aiger-err "Bad header: not enough numbers in size list")
            0 0 0 0 0 0 buf state))
       ((mv first buf state) (read-byte-buf stream buf state))
       ((when (not (and first (eql (code-char first) #\Newline))))
        (mv (aiger-err "Bad header: didn't reach newline while reading size list~%")
            0 0 0 0 0 0 buf state))
       ((mv buf state) (skip-ascii-chars #\Space stream buf state))
       ((nths & i l o a b c j f) sizes)
       ;; the b c j f entries aren't required
       (b (nfix b))
       (c (nfix c))
       (j (nfix j))
       (f (nfix f))
       ((unless (and (equal j 0)
                     (equal f 0)))
        (mv (aiger-err "We don't support justice properties or fairness constraints yet~%")
            0 0 0 0 0 0 buf state)))
    (mv nil i l a o b c buf state))
  ///
  (defthm open-input-channel-p1-of-aiger-parse-header
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-input-channel-p1 stream :byte state))
             (b* ((state
                   (mv-nth 8 (aiger-parse-header stream buf state))))
               (and (state-p1 state)
                    (open-input-channel-p1 stream :byte state)))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

