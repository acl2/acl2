; Standard IO Library
; base.lisp
; Copyright (C) 2008-2013 Centaur Technology
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
; Documented by Jared Davis <jared@centtech.com>
; Moved into std by David Rager <ragerdl@gmail.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "system/f-put-global" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(include-book "std/basic/bytep" :dir :system)
(include-book "file-measure")
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/strings/coerce" :dir :system))

; We enable this since arithmetic theories probably shouldn't need to know
; about it.
(in-theory (enable bytep))

;; Various guard-related facts about IO functions.  BOZO maybe some of these
;; theorems should be local.

(local (in-theory (disable open-channels-p
                           ordered-symbol-alistp
                           plist-worldp
                           symbol-alistp
                           timer-alistp
                           known-package-alistp
                           true-listp
                           32-bit-integer-listp
                           integer-listp
                           readable-files-p
                           written-files-p
                           read-files-p
                           writeable-files-p
                           true-list-listp
                           all-boundp
                           nth
                           update-nth)))

(local (table evisc-table (list 'quote *INITIAL-GLOBAL-TABLE*) "*INITIAL-GLOBAL-TABLE*"))

;; [Jared] Removed because this is now built into ACL2
;; (defthm assoc-equal-of-add-pair
;;     (equal (assoc-equal k1 (add-pair k2 v a))
;;            (if (equal k1 k2)
;;                (cons k2 v)
;;              (assoc-equal k1 a))))

(defthm open-channel-listp-of-add-pair
  (implies (and (open-channel1 v)
                (open-channel-listp x))
           (open-channel-listp (add-pair k v x))))

;; [Jared] Removed because this is now built into ACL2
;; (defthm ordered-symbol-alistp-of-add-pair
;;   (implies (and (symbolp k)
;;                 (ordered-symbol-alistp x))
;;            (ordered-symbol-alistp (add-pair k v x))))

(defthm open-channels-p-of-add-pair
  (implies (and (symbolp k)
                (open-channel1 v)
                (open-channels-p x))
           (open-channels-p (add-pair k v x)))
  :hints(("Goal" :in-theory (enable open-channels-p))))

(defthm open-channels-p-of-remove1-assoc-equal
  (implies (open-channels-p x)
           (open-channels-p (remove1-assoc-equal k x)))
  :hints(("Goal" :in-theory (enable open-channels-p
                                    open-channel-listp
                                    ordered-symbol-alistp))))

(defthm lookup-in-readable-files-p
  (implies (and (readable-files-p x)
                (assoc-equal k x)
                (equal type (cadr k)))
           (typed-io-listp (cdr (assoc-equal k x)) type))
  :hints(("Goal" :in-theory (enable readable-files-p))))

(defxdoc *file-types*
  :parents (std/io)
  :short "Different ways to open files for reading and writing."

  :long "<p>See @(see io) for general discussion of file types.</p>

@(def *file-types*)")





; -----------------------------------------------------------------------------
;
;                                  INPUT
;
; -----------------------------------------------------------------------------

(defsection std/io/open-input-channel

; Matt K. mod:
; The documentation formerly said:

;   BOZO it's too bad that the failure situations are handled so differently.
;   It would probably be nicer to never cause a hard error, and instead return
;   some explanation of why opening the file failed.

; In fact open-input-channel should never cause a hard error; this is ensured
; by the use of safe-open in its source code, which in turn invokes
; ignore-errors.  Perhaps it's possible to add some explanation, but it's not
; clear (to me, at this time) how to get that information from Lisp.  Even if
; we had that information, it would be a major change to open-input-channel to
; return a non-nil first value in the failure case.

  :parents (std/io open-input-channel)
  :short "Open an file for reading."

  :long "<p><b>Signature:</b> @(call open-input-channel) returns @('(mv channel
state)')</p>

<ul>

<li>@('file-name') is a string that names the file to open.</li>

<li>@('typ') is the type of input to be used and must be one of the valid @(see
*file-types*).</li>

<li>@('state') is the ACL2 @(see state).</li>

</ul>

<p>This is a @(see logic)-mode function, but its logical definition is tricky;
see @(see logical-story-of-io).  The main logical consequence is that (on
success) @('channel') will become an open input channel of the indicated type,
and hence can be read from or closed.</p>

<p>Under the hood, we use Lisp's file operations to try to open the file.  On
success, @('channel') is a symbol in the @('ACL2-INPUT-CHANNEL') package.
Under the hood, this symbol will be associated with a raw Lisp file stream.
Note that to avoid resource leaks, you should eventually use @(see
close-input-channel) to free this stream.</p>

<p>On failure, @('channel') is @('nil').  There are various reasons that
@('open-input-channel') can fail.  For example, this can happen if you try to
open a file that does not exist or for which you do not have permission.</p>"

  (defthm state-p1-of-open-input-channel
    (implies (and (state-p1 state)
                  (stringp fname)
                  (member type *file-types*))
             (state-p1 (mv-nth 1 (open-input-channel fname type state))))
    :hints(("Goal" :in-theory (enable state-p1))))

  (defthm symbolp-of-open-input-channel
    (symbolp (mv-nth 0 (open-input-channel fname type state)))
    :rule-classes (:rewrite :type-prescription))

  (defthm open-input-channel-p1-of-open-input-channel
    (implies (and (state-p1 state)
                  (stringp fname)
                  (member type *file-types*)
                  (equal channel (mv-nth 0 (open-input-channel fname type state)))
                  channel)
             (open-input-channel-p1
              channel
              type
              (mv-nth 1 (open-input-channel fname type state))))
    :hints(("Goal" :in-theory (enable state-p1)))))


;; helper theorems for reading
(local (defthm lookup-in-open-channels-p
         (implies (and (open-channels-p x)
                       (assoc k x))
                  (open-channel1 (cdr (assoc k x))))
         :hints(("Goal" :in-theory (enable open-channels-p
                                           ordered-symbol-alistp
                                           open-channel-listp)))))

(local (defthm open-channel1-of-read
         (implies (open-channel1 x)
                  (open-channel1 (cons (car x) (cddr x))))))

(local (defthm read-file-listp1-from-open-channel1
         (implies (and (open-channel1 x)
                       (natp y))
                  (read-file-listp1 (list (caddar x)
                                          (cadar x)
                                          (cadddr (car x))
                                          y)))
         :hints(("Goal" :in-theory (enable open-channel1 read-file-listp1)))))



(defsection std/io/close-input-channel
  :parents (std/io close-input-channel)
  :short "Close an input channel."

  :long "<p><b>Signature</b>: @(call close-input-channel) returns
@('state').</p>

<ul>

<li>@('channel') is a symbol that must refer to a currently open input channel;
see @(see open-input-channel).</li>

<li>@('state') is the ACL2 @(see state).</li>

</ul>

<p>This is a @(see logic)-mode function, but its logical definition is tricky;
see @(see logical-story-of-io).  The main logical consequence is that
@('channel') will no longer be an open input channel, and hence can no longer
be read from or closed.</p>

<p>Under the hood, we close the raw Lisp stream associated with @('channel').
It is generally necessary to close the input channels when you are done with
them to avoid resource leaks.</p>"

  (defthm state-p1-of-close-input-channel-free
    ;; type is a free variable here.  the two variants that follow try to get
    ;; around this problem
    (implies (and (open-input-channel-p1 channel type state)
                  (state-p1 state))
             (state-p1 (close-input-channel channel state)))
    :hints(("Goal" :in-theory (e/d (state-p1
                                    read-files-p)
                                   (read-file-listp1)))))

  (defthm state-p1-of-close-input-channel-types
    (implies (and (or (open-input-channel-p1 channel :byte state)
                      (open-input-channel-p1 channel :object state)
                      (open-input-channel-p1 channel :character state))
                  (state-p1 state))
             (state-p1 (close-input-channel channel state)))
    :hints(("Goal" :in-theory (disable close-input-channel
                                       open-input-channel-p1))))

  (defthm state-p1-of-close-input-channel-of-open
    (implies (and (open-input-channel-p1
                   (mv-nth 0 (open-input-channel fname type state1))
                   type state)
                  (state-p1 state))
             (state-p1 (close-input-channel
                        (mv-nth 0 (open-input-channel fname type state1))
                        state)))
    :hints(("Goal" :in-theory (disable close-input-channel
                                       open-input-channel-p1
                                       open-input-channel)))))

(defsection std/io/read-char$
  :parents (std/io read-char$)
  :short "Read one character from an open @(':character') stream."

  :long "<p>NOTE: We generally prefer to avoid @(see read-char$).  It is easy
to use @(see read-byte$) instead, which is generally more efficient and avoids
certain character-encoding issues; see below for details.</p>

<p><b>Signature:</b> @(call read-char$) returns @('(mv char/nil state)').</p>

<ul>

<li>@('channel') is a symbol that must refer to an open @(':character') input
channel; see @(see open-input-channel).</li>

<li>@('state') is the ACL2 @(see state).</li>

</ul>

<p>This is a @(see logic)-mode function, but its logical definition is tricky;
see @(see logical-story-of-io).  The main logical consequence is the updating
of state.</p>

<p>Under the hood, we read a <see topic='@(url characters)'>character</see>
from the Lisp input stream that is associated with @('channel').  If we reach
the end of the file, @('nil') is returned.</p>

<h3>Character versus Byte Input</h3>

<p>In some sense, it is redundant for ACL2 to have separate kinds of input
channels for characters and bytes.  After all, ACL2 has exactly 256 @(see
characters) corresponding to bytes 0-255, and provides functions like @(see
char-code) and @(see code-char) for converting between these characters and
bytes.  So, one could easily define @('read-char$') as a wrapper that calls
@('code-char') on @('read-byte$'), or could define @('read-byte$') as a wrapper
for @('read-char$') that calls @('char-code').</p>

<p>That being said, we generally prefer to use byte input.  Common Lisp
implementations have some freedom in how they implement characters.  Because of
this, and because different Lisps might try to use different encodings when
reading files, ACL2's @('read-char$') has some extra checks to make sure that
the characters being read in are legal.  At any rate, for a basic timing test
on CCL, we measured @('read-char$') at 12.5% slower than @('read-byte$') with
@('code-char').</p>

<p>On the other hand, there is no equivalent of @('peek-char$') for @(':byte')
input streams.  So, that might be worth considering.</p>"

  ;; Performance testing code
  #||
  (include-book ;; newline to fool dependency scanner
    "std/util/bstar" :dir :system)
  (defun skip-chars-until-eof (channel state)
    (declare (xargs :mode :program :stobjs state))
    (b* (((mv char/nil state) (read-char$ channel state))
         ((unless char/nil)
          state))
      (skip-chars-until-eof channel state)))

  (defun skip-bytes-until-eof (channel state)
    (declare (xargs :mode :program :stobjs state))
    (b* (((mv byte/nil state) (read-byte$ channel state))
         ((unless byte/nil)
          state))
      (skip-bytes-until-eof channel state)))

  (defun skip-chars-until-eof-alt (channel state)
    (declare (xargs :mode :program :stobjs state))
    (b* (((mv byte/nil state) (read-byte$ channel state))
         ((unless byte/nil)
          state)
         (?char (code-char byte/nil)))
      (skip-bytes-until-eof channel state)))

  (b* (;; (file "/dev/shm/top.v") ;; 40 MB file on a ram disk ; ;
       (file "/n/fv2/jared/fresh/e/acl2/acl2-characters") ;; file to check encoding stuff ; ;

       ((mv channel state) (open-input-channel file :character state))
       (state (time$ (skip-chars-until-eof channel state)))
       (state (close-input-channel channel state))

       ((mv channel state) (open-input-channel file :byte state))
       (state (time$ (skip-bytes-until-eof channel state)))
       (state (close-input-channel channel state))

       ((mv channel state) (open-input-channel file :byte state))
       (state (time$ (skip-chars-until-eof-alt channel state)))
       (state (close-input-channel channel state))

       )
    state)
  ||#

  (defthm state-p1-of-read-char$
    (implies (and (state-p1 state)
                  (symbolp channel)
                  (open-input-channel-p1 channel :character state))
             (state-p1 (mv-nth 1 (read-char$ channel state))))
    :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1)))))

  (defthm open-input-channel-p1-of-read-char$
    (implies (and (state-p1 state)
                  (open-input-channel-p1 channel :character state))
             (open-input-channel-p1 channel :character (mv-nth 1 (read-char$ channel state)))))

  (local (defthm character-cadr-of-open-channel1
           (implies (and (open-channel1 x)
                         (equal (cadar x) :character)
                         (cdr x))
                    (characterp (cadr x)))))

  (defthm characterp-of-read-char$
    (implies (and (mv-nth 0 (read-char$ channel state))
                  (state-p1 state)
                  (open-input-channel-p1 channel :character state))
             (characterp (mv-nth 0 (read-char$ channel state))))
    :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1))))
    :rule-classes
    (:rewrite
     (:type-prescription :corollary
                         (implies (and (state-p1 state)
                                       (open-input-channel-p1 channel :character state))
                                  (or (characterp (mv-nth 0 (read-char$ channel state)))
                                      (null (mv-nth 0 (read-char$ channel state)))))))))

(defsection std/io/peek-char$
  :parents (std/io peek-char$)
  :short "Inspect the next character that will be read from an open
@(':character') input stream."

  :long "<p><b>Signature:</b> @(call peek-char$) returns @('char/nil').</p>

<ul>

<li>@('channel') is a symbol that must refer to an open @(':character') input
channel; see @(see open-input-channel).</li>

<li>@('state') is the ACL2 @(see state).</li>

</ul>

<p>This is a @(see logic)-mode function, but its logical definition is tricky;
see @(see logical-story-of-io).</p>

<p>Under the hood, this uses Lisp's I/O functions to say which character will
be retrieved next by @(see read-char$), without altering the contents of the
stream.  This provides only a single character of lookahead.</p>

<p>You should typically never need to reason about @('peek-char$').  We prove
it returns the same thing as @('read-char$'), so you should be able to just
reason about @('read-char$') instead.</p>"

  (defthm peek-char$-removal
    (equal (peek-char$ channel state)
           (mv-nth 0 (read-char$ channel state))))

  (in-theory (disable peek-char$)))


(defsection std/io/read-byte$
  :parents (std/io read-byte$)
  :short "Read one byte from an open @(':byte') stream."

  :long "<p><b>Signature:</b> @(call read-byte$) returns @('(mv byte/nil
state)').</p>

<ul>

<li>@('channel') is a symbol that must refer to an open @(':byte') input
channel; see @(see open-input-channel).</li>

<li>@('state') is the ACL2 @(see state).</li>

</ul>

<p>This is a @(see logic)-mode function, but its logical definition is tricky;
see @(see logical-story-of-io).  The main logical consequence is the updating
of state.</p>

<p>Under the hood, we read a byte (i.e., a number between 0 and 255, inclusive)
from the Lisp input stream that is associated with @('channel').  If we reach
the end of the file, @('nil') is returned.</p>"

  (defthm state-p1-of-read-byte$
    (implies (and (state-p1 state)
                  (symbolp channel)
                  (open-input-channel-p1 channel :byte state))
             (state-p1 (mv-nth 1 (read-byte$ channel state))))
    :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1)))))

  (defthm open-input-channel-p1-of-read-byte$
    (implies (and (state-p1 state)
                  (open-input-channel-p1 channel :byte state))
             (open-input-channel-p1 channel :byte (mv-nth 1 (read-byte$ channel state)))))

  (local (defthm bytep-cadr-of-open-channel1
           (implies (and (open-channel1 x)
                         (equal (cadar x) :byte)
                         (cdr x))
                    (and (bytep (cadr x))
                         (unsigned-byte-p 8 (cadr x))
                         (natp (cadr x))
                         (integerp (cadr x))))))

  (defthm bytep-of-read-byte$
    (implies (and (state-p1 state)
                  (open-input-channel-p1 channel :byte state)
                  (mv-nth 0 (read-byte$ channel state)))
             (and (bytep (mv-nth 0 (read-byte$ channel state)))
                  (natp (mv-nth 0 (read-byte$ channel state)))
                  (integerp (mv-nth 0 (read-byte$ channel state)))
                  (unsigned-byte-p 8 (mv-nth 0 (read-byte$ channel state)))))
    :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1 bytep)))))

  (defthm bytep-of-read-byte$-type
    (implies (and (state-p1 state)
                  (open-input-channel-p1 channel :byte state))
             (or (null (mv-nth 0 (read-byte$ channel state)))
                 (natp (mv-nth 0 (read-byte$ channel state)))))
    :hints(("Goal" :use bytep-of-read-byte$))
    :rule-classes :type-prescription)

  (defthm bytep-of-read-byte$-linear
    (implies (and (state-p1 state)
                  (open-input-channel-p1 channel :byte state))
             (and (< (mv-nth 0 (read-byte$ channel state)) 256)
                  (<= 0 (mv-nth 0 (read-byte$ channel state)))))
    :hints(("Goal" :use bytep-of-read-byte$))
    :rule-classes :linear)


  (local (defthm l1
           (implies (and (state-p1 state)
                         (open-input-channel-p1 channel :byte state))
                    (let* ((entry  (cdr (assoc-equal channel (nth 0 state)))) ;; open-input-channels
                           (header (car entry)))
                      (and (open-channel1 entry)
                           (equal (second header) :byte))))
           :hints(("Goal" :in-theory (enable state-p1)))))

  (local (defthm l2
           (let ((header (car entry))
                 (stream (cdr entry)))
             (implies (and (open-channel1 entry)
                           (equal (second header) :byte))
                      (typed-io-listp stream :byte)))))

  (local (defthm l3
           (implies (and (typed-io-listp :byte x)
                         (not (car x)))
                    (not (cadr x)))))

  (local (defthm l4
           (implies (and (state-p1 state)
                         (open-input-channel-p1 channel :byte state))
                    (let* ((entry  (cdr (assoc-equal channel (nth 0 state)))) ;; open-input-channels
                           (stream (cdr entry)))
                      (implies (not (car stream))
                               (not (cadr stream)))))
           :hints(("Goal"
                   :in-theory (disable l1 l2)
                   :use ((:instance l1)
                         (:instance l2 (entry (cdr (assoc-equal channel (nth 0 state))))))))))

  (defthm no-bytes-after-read-byte$-null
    ;; Silly, but useful for avoiding NULL checks on every single byte you read.
    (let ((byte1  (mv-nth 0 (read-byte$ channel state)))
          (state2 (mv-nth 1 (read-byte$ channel state))))
      (implies (and (not byte1)
                    (state-p1 state)
                    (open-input-channel-p1 channel :byte state))
               (not (mv-nth 0 (read-byte$ channel state2)))))
    :hints(("Goal" :in-theory (disable open-input-channel-p1)))))


(defsection std/io/read-object
  :parents (std/io read-object)
  :short "Read one object from an open @(':object') stream."

  :long "<p><b>Signature:</b> @(call read-object) returns @('(mv eofp obj
state)').</p>

<ul>

<li>@('channel') is a symbol that must refer to an open @(':object') input
channel; see @(see open-input-channel).</li>

<li>@('state') is the ACL2 @(see state).</li>

</ul>

<p>This is a @(see logic)-mode function, but its logical definition is tricky;
see @(see logical-story-of-io).  The main logical consequence is the updating
of state.</p>

<p>Under the hood, we use the Lisp reader to try to read an object from the
Lisp input stream that is associated with @('channel').</p>

<p>Ideally, the input stream contains well-formed S-expressions that are free
of \"bad\" objects like @('0.75'), symbols from packages that ACL2 doesn't know
about, etc; see @(see ACL2::|About Types|).  In this case, @('read-object')
reads the first S-expression in the file and returns it as @('obj'), setting
@('eofp') to @('nil').  If there are no more S-expressions in the file,
@('eofp') is @('t') and @('obj') is @('nil').</p>

<p>But the input stream can also be malformed.  For instance, we might
encounter malformed S-expressions without enough closing parens, or bad objects
like @('0.75').  These sorts of problems will cause hard errors or raw Lisp
errors!</p>

<p>Note that if the input contains plain symbols without explicit package name
prefixes, e.g., @('foo') instead of @('acl2::foo'), then these symbols will be
treated as coming from the current package.  If that isn't what you want, you
can explicily call @(see in-package) to switch into whatever package you want
to be the default.  For example, if the file @('temp') contains exactly:</p>

@({
foo
})

<p>Then the following book:</p>

@({
 (in-package \"ACL2\")
 (include-book \"std/util/bstar\" :dir :system)
 (include-book \"centaur/vl/portcullis\" :dir :system)

 (make-event
  (b* (((mv ?err ?val state) (in-package \"VL\"))
       ((mv channel state)   (open-input-channel \"temp\" :object state))
       ((mv ?eofp obj state) (read-object channel state))
       (state                (close-input-channel channel state)))
    (value `(defconst *foo* ',obj))))
})

<p>Defines @('*foo*') as the symbol @('vl::foo'), instead of
@('acl2::foo').</p>"

  (defthm state-p1-of-read-object
    (implies (and (state-p1 state)
                  (symbolp channel)
                  (open-input-channel-p1 channel :object state))
             (state-p1 (mv-nth 2 (read-object channel state))))
    :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1)))))

  (defthm open-input-channel-p1-of-read-object
    (implies
     (and (state-p1 state)
          (open-input-channel-p1 channel :object state))
     (open-input-channel-p1 channel :object
                            (mv-nth 2 (read-object channel state))))))

(defsection state-preserved-after-eof

  ;; Sometimes it's useful to know that state isn't modified when read at EOF
  ;; (copied from unicode)

 (local (defthm lemma
          (equal (equal a (cons x y))
                 (and (consp a)
                      (equal (car a) x)
                      (equal (cdr a) y)))))

 (local (defthm lemma2-char
          (implies (and (open-channel1 foo)
                        (equal (cadar foo) :character)
                        (not (cadr foo)))
                   (equal (cddr foo) (cdr foo)) )))

 (local (defthm lemma2-byte
          (implies (and (open-channel1 foo)
                        (equal (cadar foo) :byte)
                        (not (cadr foo)))
                   (equal (cddr foo) (cdr foo)) )))

 (local (in-theory (disable open-channel1)))

 (local (defthm update-nth-of-nth-same
          (implies (< (nfix n) (len x))
                   (equal (update-nth n (nth n x) x)
                          x))
          :hints(("Goal" :in-theory (enable nth update-nth)))))

 (defsection char
   :extension std/io/read-char$
   (defthm state-preserved-by-read-char$-when-eof
     (implies (and (not (mv-nth 0 (read-char$ channel state)))
                   (state-p1 state)
                   (open-input-channel-p1 channel :character state))
              (equal (mv-nth 1 (read-char$ channel state))
                     state))
     :hints(("Goal" :in-theory (e/d (read-char$ state-p1))))))

 (defsection byte
   :extension std/io/read-byte$
   (defthm state-preserved-by-read-byte$-when-eof
     (implies (and (not (mv-nth 0 (read-byte$ channel state)))
                   (state-p1 state)
                   (open-input-channel-p1 channel :byte state))
              (equal (mv-nth 1 (read-byte$ channel state))
                     state))
     :hints(("Goal" :in-theory (e/d (read-byte$ state-p1))))))

 (defsection object
   :extension std/io/read-object
   (defthm state-preserved-by-read-object-when-eof
     (implies (and (mv-nth 0 (read-object channel state))
                   (state-p1 state)
                   (open-input-channel-p1 channel :object state))
              (equal (mv-nth 2 (read-object channel state))
                     state))
     :hints(("Goal" :in-theory (e/d (read-object state-p1)))))))

(defsection std/io/read-file-into-string
  :parents (std/io read-file-into-string)

  :long "<p>See @(see read-file-into-string).</p>"

  (local (in-theory (disable read-char$ open-input-channel-p1)))

  (defthm
    stringp-of-read-file-into-string1
    (implies
     (not
      (null
       (mv-nth 0
               (read-file-into-string1 channel state ans bound))))
     (stringp
      (mv-nth 0
              (read-file-into-string1 channel state ans bound))))
    :rule-classes
    (:rewrite
     (:type-prescription
      :corollary
      (or
       (null
        (mv-nth 0
                (read-file-into-string1 channel state ans bound)))
       (stringp
        (mv-nth
         0
         (read-file-into-string1 channel state ans bound)))))))

  (defthm
    state-p1-of-read-file-into-string1
    (implies
     (and (symbolp channel)
          (open-input-channel-p channel
                                :character state)
          (state-p state))
     (state-p1 (mv-nth 1
                       (read-file-into-string1 channel state ans bound))))))

; -----------------------------------------------------------------------------
;
;                                  OUTPUT
;
; -----------------------------------------------------------------------------

(defsection std/io/open-output-channel
  :parents (std/io open-output-channel)
  :short "Open a file for writing."

  :long "<p><b>Signature:</b> @(call open-output-channel) returns @('(mv
channel state)')</p>

<ul>

<li>@('file-name') can be either @(':string') (to indicate that you want to
print to a string stream), or a string like @('\"temp.txt\"') that names the
file to write to.</li>

<li>@('typ') is the type of input to be used and must be one of the valid @(see
*file-types*).</li>

<li>@('state') is the ACL2 @(see state).</li>

</ul>

<p>This is a @(see logic)-mode function, but its logical definition is tricky;
see @(see logical-story-of-io).  The main logical consequence is that (on
success) @('channel') will become an open output channel of the indicated type,
and hence can be written to or closed.</p>

<p>Under the hood, we either create a new Lisp string stream in memory (when
@('file-name') is @(':string')) or we use Lisp's file operations to open
@('file-name') for writing.  Note that if @('file-name') refers to a file that
already exists, it will be overwritten (i.e., not appended to).</p>

<p>On success, @('channel') is a symbol in the @('ACL2-OUTPUT-CHANNEL')
package.  Under the hood, this symbol will be associated with the Lisp stream.
Note that to avoid resource leaks, you should eventually use @(see
close-output-channel) to free this stream.</p>

<p>On failure, @('channel') is @('nil').  There are various reasons that
@('open-output-channel') can fail.  For example, this can happen if you try to
write to a file in a directory that does not exist, and it may happen
(depending on your host Lisp) if you try to open a file for which you do not
have permission.</p>"

  (defthm state-p1-of-open-output-channel
    (implies (and (state-p1 state)
                  (stringp fname)
                  (member type *file-types*))
             (state-p1 (mv-nth 1 (open-output-channel fname type state))))
    :hints(("Goal" :in-theory (enable state-p1))))

  (defthm symbolp-of-open-output-channel
    (symbolp (mv-nth 0 (open-output-channel fname type state)))
    :rule-classes (:rewrite :type-prescription))

  (defthm open-output-channel-p1-of-open-output-channel
    (implies (and (state-p1 state)
                  (stringp fname)
                  (member type *file-types*)
                  (equal channel (mv-nth 0 (open-output-channel fname type state)))
                  channel)
             (open-output-channel-p1
              channel
              type
              (mv-nth 1 (open-output-channel fname type state))))
    :hints(("Goal" :in-theory (enable state-p1))))

  (defthm open-output-channel-p1-of-put-global
    ;; This is needed for open-output-channel!.
    (equal (open-output-channel-p1 channel type (put-global key val state))
           (open-output-channel-p1 channel type state))
    :hints(("Goal" :in-theory (enable open-output-channel-p1 put-global))))

  )



(local
 (defthm written-file-from-open-channel1
   (implies (and (open-channel1 x)
                 (natp y))
            (written-file (cons (list (caddar x)
                                      (cadar x)
                                      (cadddr (car x))
                                      y)
                                (cdr x))))
   :hints(("Goal" :in-theory (enable open-channel1 written-file)))))



(defsection std/io/close-output-channel
  :parents (std/io close-output-channel)
  :short "Close an output channel."

  :long "<p><b>Signature</b>: @(call close-output-channel) returns
@('state').</p>

<ul>

<li>@('channel') is a symbol that must refer to a currently open output
channel; see @(see open-output-channel).</li>

<li>@('state') is the ACL2 @(see state).</li>

</ul>

<p>This is a @(see logic)-mode function, but its logical definition is tricky;
see @(see logical-story-of-io).  The main logical consequence is that
@('channel') will no longer be an open output channel, and hence can no longer
be written to or closed.</p>

<p>Under the hood, we close the raw Lisp stream associated with @('channel').
This typically involves flushing the buffers associated with the file (i.e.,
actually writing your output to disk).  It is generally necessary to close
output channels when you are done with them to avoid resource leaks.</p>"

  (defthm state-p1-of-close-output-channel-free
    ;; type is a free variable here.  the two variants that follow try to get
    ;; around this problem
    (implies (and (open-output-channel-p1 channel type state)
                  (state-p1 state))
             (state-p1 (close-output-channel channel state)))
    :hints(("Goal" :in-theory (e/d (state-p1
                                    written-files-p)
                                   (written-file)))))

  (defthm state-p1-of-close-output-channel-types
    (implies (and (or (open-output-channel-p1 channel :byte state)
                      (open-output-channel-p1 channel :object state)
                      (open-output-channel-p1 channel :character state))
                  (state-p1 state))
             (state-p1 (close-output-channel channel state)))
    :hints(("Goal" :in-theory (disable close-output-channel
                                       open-output-channel-p1))))

  (defthm state-p1-of-close-output-channel-of-open
    (implies (and (open-output-channel-p1
                   (mv-nth 0 (open-output-channel fname type state1))
                   type state)
                  (state-p1 state))
             (state-p1 (close-output-channel
                        (mv-nth 0 (open-output-channel fname type state1))
                        state)))
    :hints(("Goal" :in-theory (disable close-output-channel
                                       open-output-channel-p1
                                       open-output-channel)))))


;; BOZO Should these be local?

(defthm open-channel1-of-cons-byte
  (implies (and (open-channel1 x)
                (equal (cadar x) :byte)
                (natp y)
                (< y 256))
           (open-channel1 (list* (car x) y (cdr x)))))

(defthm open-channel1-of-cons-object
  (implies (and (open-channel1 x)
                (equal (cadar x) :object))
           (open-channel1 (list* (car x) y (cdr x)))))

(defthm typed-io-listp-of-append
  (equal (typed-io-listp (append x y) type)
         (and (typed-io-listp (list-fix x) type)
              (typed-io-listp y type))))

(defthm typed-io-listp-of-rev
  (equal (typed-io-listp (rev x) type)
         (typed-io-listp (list-fix x) type))
  :hints(("Goal" :in-theory (enable rev))))

(defthm open-channel1-of-revappend-charlist
  (implies (and (open-channel1 x)
                (equal (cadar x) :character)
                (character-listp y))
           (open-channel1 (cons (car x) (append (rev y) (cdr x))))))


(defsection std/io/princ$
  :parents (std/io princ$)
  :short "Print an atom to a @(':character') output stream."
  :long "<p>ACL2 has nice documentation for @(see princ$).  The @(see std/io)
library adds the following lemmas:</p>"

  (local (include-book "std/strings/explode-nonnegative-integer" :dir :system))
  (local (include-book "std/strings/explode-atom" :dir :system))

  (defthm state-p1-of-princ$
    (implies (and (state-p1 state)
                  (symbolp channel)
                  (open-output-channel-p1 channel :character state))
             (state-p1 (princ$ x channel state)))
    :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1 explode-atom)))))

  (defthm open-output-channel-p1-of-princ$
    (implies (and (state-p1 state)
                  (open-output-channel-p1 channel :character state))
             (open-output-channel-p1 channel :character
                                     (princ$ x channel state)))))


(defsection std/io/write-byte$
  :parents (std/io write-byte$)
  :short "Write one byte to an open @(':byte') output stream."
  :long "<p><b>Signature:</b> @(call write-byte$) returns @('state').</p>

<ul>

<li>@('byte') must be a natural number with @('byte < 256').</li>

<li>@('channel') is a symbol that must refer to an open @(':byte') input
channel; see @(see open-input-channel).</li>

<li>@('state') is the ACL2 @(see state).</li>

</ul>

<p>This is a @(see logic)-mode function, but its logical definition is tricky;
see @(see logical-story-of-io).  The main logical consequence is the updating
of state.</p>

<p>Under the hood, we write a byte to the Lisp output stream that is associated
with @('channel').</p>"

  (defthm state-p1-of-write-byte$
    (implies (and (state-p1 state)
                  (symbolp channel)
                  (natp byte)
                  (< byte 256)
                  (open-output-channel-p1 channel :byte state))
             (state-p1 (write-byte$ byte channel state)))
    :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1)))))

  (defthm open-output-channel-p1-of-write-byte$
    (implies (and (state-p1 state)
                  (open-output-channel-p1 channel :byte state))
             (open-output-channel-p1 channel :byte
                                     (write-byte$ byte channel state)))))


(defsection std/io/print-object$
  :parents (std/io print-object$)
  :short "Print a Lisp object to an @(':object') output stream."
  :long "<p>BOZO document me.</p>"

  (defthm state-p1-of-print-object$
    (implies (and (state-p1 state)
                  (symbolp channel)
                  (open-output-channel-p1 channel :object state))
             (state-p1 (print-object$ x channel state)))
    :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1)))))

  (defthm open-output-channel-p1-of-print-object$
    (implies (and (state-p1 state)
                  (open-output-channel-p1 channel :object state))
             (open-output-channel-p1 channel
                                     :object (print-object$ x channel state))))

  (defthm get-serialize-character-of-print-object$
    (equal (get-serialize-character (print-object$ obj channel state))
           (get-serialize-character state))
    :hints(("Goal" :in-theory (enable get-serialize-character
                                      get-global)))))


(defsection serialize-characterp
  :parents (std/io/set-serialize-character)
  :short "Recognizer for valid serialize characters."

  (defund serialize-characterp (c)
    (declare (xargs :guard t))
    (or (not c)
        (equal c #\Z)
        (equal c #\Y))))

(defsection std/io/set-serialize-character
  :parents (std/io set-serialize-character)
  :short "Control the use of @(see serialize) in @(see print-object$)."

  (defthm state-p1-of-set-serialize-character
    (implies (state-p1 state)
             (state-p1 (set-serialize-character c state))))

  (defthm open-output-channel-p1-of-set-serialize-character
    (implies (and (state-p1 state)
                  (open-output-channel-p1 channel :object state))
             (open-output-channel-p1 channel :object (set-serialize-character c state)))
    :hints(("Goal" :in-theory (enable put-global))))

  (defthm get-serialize-character-of-set-serialize-character
    ;; Ugh, this is so gross...
    (equal (get-serialize-character (set-serialize-character c state))
           (cond ((not c)
                  nil)
                 ((serialize-characterp c)
                  c)
                 (t
                  (get-serialize-character state))))
    :hints(("Goal" :in-theory (enable acl2::get-serialize-character
                                      set-serialize-character
                                      serialize-characterp))))

  (defthm boundp-global1-of-set-serialize-character
    (iff (boundp-global1 'serialize-character
                         (set-serialize-character c state))
         (cond ((not c)
                t)
               ((serialize-characterp c)
                t)
               (t
                (boundp-global1 'serialize-character state))))
    :hints(("Goal" :in-theory (enable serialize-characterp)))))



(defsection open-channels-distinct-from-standard-io
  :parents (open-input-channel open-output-channel)
  :short "Technical lemmas to show that opening input/output channels does not
produce a symbol like @('ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0'),
for the guards of @(see close-input-channel) and @(see close-output-channel)."

;; This is true because symbol created ends in "-" and then the new file clock,
;; which is at least 1.  Blech!

  (local (in-theory (disable floor mod print-base-p)))
  (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

  (defthm print-base-p-implies-posp
    (implies (print-base-p x)
             (posp x))
    :hints(("Goal" :in-theory (enable print-base-p)))
    :rule-classes :forward-chaining)

  (defthm print-base-p-bound
    (implies (print-base-p x)
             (<= x 16))
    :hints(("Goal" :in-theory (enable print-base-p)))
    :rule-classes :forward-chaining)

  (local (defthm explode-nonnegative-integer-length-incr
           (<= (len ans) (len (explode-nonnegative-integer n base ans)))
           :rule-classes :linear))

  (local (defthm explode-nonnegative-integer-length-incr-strict
           (implies (and (posp n) (print-base-p base))
                    (< (len ans) (len (explode-nonnegative-integer n base ans))))
           :hints(("Goal" :in-theory (enable mod)
                   :induct (explode-nonnegative-integer n base ans)
                   :expand ((:free (base) (explode-nonnegative-integer n base ans)))))
           :rule-classes nil))

  (local (defthm ans-not-zero-when-member-nonzero
           (implies (and (bind-free `((c . (car ,ans))))
                         (member (double-rewrite c) ans)
                         (not (equal (double-rewrite c) #\0)))
                    (not (equal (explode-nonnegative-integer x base ans)
                                '(#\0))))))

  (local (defthm posp-x/base
           (implies (and (integerp x)
                         (< 0 x)
                         (print-base-p base))
                    (or (not (integerp (* (/ base) x)))
                        (< 0 (* (/ base) x))))
           :rule-classes :type-prescription))

  (local (defthm explode-nonnegative-integer-of-positive-is-not-zero-list
           (implies (and (posp x)
                         (print-base-p base))
                    (not (equal (explode-nonnegative-integer x base ans)
                                '(#\0))))
           :hints(("Goal" ; :in-theory (enable mod)
                   :expand ((:free (base) (explode-nonnegative-integer x base ans)))
                   :use ((:instance explode-nonnegative-integer-length-incr-strict
                                    (n (* (/ base) x)) (ans (cons #\0 ans))))
                   :do-not-induct t))
           :otf-flg t))

  (local (defun charlist-suffixp (x suff)
           (or (equal x suff)
               (and (consp x)
                    (charlist-suffixp (cdr x) suff)))))

  (local (defun symb-ends-in-dash-zero (x)
           (charlist-suffixp (explode (symbol-name x))
                             '(#\- #\0))))

  (local (defthm suffixp-dash-zero-implies-member-dash
           (implies (not (member #\- x))
                    (not (charlist-suffixp x '(#\- #\0))))))

  (local (defthm explode-nonneg-no-dash
           (implies (not (member #\- ans))
                    (not (member #\- (explode-nonnegative-integer x base
                                                                  ans))))))

  (local (defthm character-listp-explode-nonneg
           (equal
            (character-listp (explode-nonnegative-integer n base ans))
            (character-listp ans))))

  (local (defthm charlist-suffixp-append-dash-x
           (equal (charlist-suffixp (append x (cons #\- y)) '(#\- #\0))
                  (charlist-suffixp (cons #\- y) '(#\- #\0)))
           :hints (("goal" :induct (append x (cons #\- y))
                    :in-theory (enable append)))))

  (local (defthm symb-ends-in-dash-zero-of-make-output-channel
           (implies (posp clock)
                    (not (symb-ends-in-dash-zero (make-output-channel str clock))))))

  (local (defthm symb-ends-in-dash-zero-of-make-input-channel
           (implies (posp clock)
                    (not (symb-ends-in-dash-zero (make-input-channel str clock))))))

  (defthm make-output-channel-not-standard-co
    (implies (posp clock)
             (not (equal (make-output-channel str clock)
                         *standard-co*)))
    :hints (("goal" :in-theory (disable
                                symb-ends-in-dash-zero-of-make-output-channel
                                make-output-channel)
             :use symb-ends-in-dash-zero-of-make-output-channel)))

  (defthm make-input-channel-not-standard-ci
    (implies (posp clock)
             (not (equal (make-input-channel str clock)
                         *standard-ci*)))
    :hints (("goal" :in-theory (disable
                                symb-ends-in-dash-zero-of-make-input-channel
                                make-input-channel)
             :use symb-ends-in-dash-zero-of-make-input-channel)))

  (defthm make-input-channel-not-standard-oi
    (implies (posp clock)
             (not (equal (make-input-channel str clock)
                         *standard-oi*)))
    :hints (("goal" :in-theory (disable
                                symb-ends-in-dash-zero-of-make-input-channel
                                make-input-channel)
             :use symb-ends-in-dash-zero-of-make-input-channel)))

  (defthm open-output-channel-is-not-standard-co
    (implies (state-p1 state)
             (not (equal (mv-nth 0 (open-output-channel fname type state))
                         *standard-co*)))
    :hints(("Goal" :in-theory (disable make-output-channel))))

  (defthm open-input-channel-is-not-standard-ci
    (implies (state-p1 state)
             (not (equal (mv-nth 0 (open-input-channel fname type state))
                         *standard-ci*)))
    :hints(("Goal" :in-theory (disable make-input-channel))))

  (defthm open-input-channel-is-not-standard-oi
    (implies (state-p1 state)
             (not (equal (mv-nth 0 (open-input-channel fname type state))
                         *standard-oi*)))
    :hints(("Goal" :in-theory (disable make-input-channel)))))



(in-theory (disable state-p1
                    open-input-channel-p1
                    open-input-channel
                    close-input-channel
                    read-char$
                    read-byte$
                    read-object
                    open-output-channel-p1
                    open-output-channel
                    close-output-channel
                    princ$
                    write-byte$
                    print-object$
                    set-serialize-character
                    get-serialize-character
                    file-measure))
