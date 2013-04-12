; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>
; Documented by Jared Davis <jared@centtech.com>
; Moved by David Rager <ragerdl@gmail.com> on 1/10/13.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "system/f-put-global" :dir :system)

(defsection bytep

  ;; This should probably be defined elsewhere.
  ;;
  ;; We leave this enabled since arithmetic theories probably shouldn't need to
  ;; know about it.

  (defun bytep (x)
    (declare (xargs :guard t))
    (and (natp x)
         (< x 256)))

  (defthm bytep-compound-recognizer
    (implies (bytep x)
             (and (integerp x)
                  (<= 0 x)))
    :rule-classes :compound-recognizer))

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

(defthm assoc-equal-of-add-pair
    (equal (assoc-equal k1 (add-pair k2 v a))
           (if (equal k1 k2)
               (cons k2 v)
             (assoc-equal k1 a))))

(defthm open-channel-listp-of-add-pair
  (implies (and (open-channel1 v)
                (open-channel-listp x))
           (open-channel-listp (add-pair k v x))))

(defthm ordered-symbol-alistp-of-add-pair
  (implies (and (symbolp k)
                (ordered-symbol-alistp x))
           (ordered-symbol-alistp (add-pair k v x))))

(defthm open-channels-p-of-add-pair
  (implies (and (symbolp k)
                (open-channel1 v)
                (open-channels-p x))
           (open-channels-p (add-pair k v x)))
  :hints(("Goal" :in-theory (enable open-channels-p))))

(defthm open-channels-p-of-delete-assoc-equal
  (implies (open-channels-p x)
           (open-channels-p (delete-assoc-equal k x)))
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
  :parents (io)
  :short "Different ways to open files for reading and writing."

  :long "<p>See @(see io) for general discussion of file types.</p>

@(def *file-types*)")

(defxdoc logical-story-of-io
  :parents (io)
  :short "How file reading operations are modeled in the ACL2 logic."

  :long "<p>ACL2's file input operations are available in @(':logic') mode (see
@(see defun-mode)).  This is somewhat tricky to justify in the logic, since,
e.g., the contents of a file is external to ACL2, can be changed over time, and
so on.</p>

<p>Practically speaking, most users don't need to pay any attention to the
details of this story.  Instead, see the book @('io/base'), which develops
the basic theorems that are necessary to reason about the io primitives.</p>

<p>If, for some reason, you do want to understand the logical story, you might
start with this paper:</p>

<p>Jared Davis.  <a
href='http://www.ccs.neu.edu/home/pete/acl206/papers/davisb.pdf'>Reasoning
about ACL2 File Input</a>.  ACL2 Workshop 2006.</p>")




; -----------------------------------------------------------------------------
;
;                                  INPUT
;
; -----------------------------------------------------------------------------

(defsection open-input-channel
  :parents (io)
  :short "Open a file for reading."

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

<p>There are various reasons and ways that @('open-input-channel') can fail.
For instance:</p>

<ul>

<li>If you try to open a file that does not exist, @('channel') will be
@('nil').</li>

<li>If you try to open a file for which you do not have permission, say
@('/etc/shadow'), a hard Lisp error can result.</li>

</ul>

<p>BOZO it's too bad that the failure situations are handled so differently.
It would probably be nicer to never cause a hard error, and instead return some
explanation of why opening the file failed.</p>"

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

(defsection close-input-channel
  :parents (io)
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

(defsection read-char$
  :parents (io)
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
    "tools/bstar" :dir :system)
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

(defsection peek-char$
  :parents (io)
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

(defsection read-byte$
  :parents (io)
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
                         (natp (cadr x))
                         (integerp (cadr x))))))

  (defthm bytep-of-read-byte$
    (implies (and (state-p1 state)
                  (open-input-channel-p1 channel :byte state)
                  (mv-nth 0 (read-byte$ channel state)))
             (and (bytep (mv-nth 0 (read-byte$ channel state)))
                  (natp (mv-nth 0 (read-byte$ channel state)))
                  (integerp (mv-nth 0 (read-byte$ channel state)))))
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
    :rule-classes :linear))


(defsection read-object
  :parents (io)
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
 (include-book \"tools/bstar\" :dir :system)
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
   :extension read-char$
   (defthm state-preserved-by-read-char$-when-eof
     (implies (and (not (mv-nth 0 (read-char$ channel state)))
                   (state-p1 state)
                   (open-input-channel-p1 channel :character state))
              (equal (mv-nth 1 (read-char$ channel state))
                     state))
     :hints(("Goal" :in-theory (e/d (read-char$ state-p1))))))

 (defsection byte
   :extension read-byte$
   (defthm state-preserved-by-read-byte$-when-eof
     (implies (and (not (mv-nth 0 (read-byte$ channel state)))
                   (state-p1 state)
                   (open-input-channel-p1 channel :byte state))
              (equal (mv-nth 1 (read-byte$ channel state))
                     state))
     :hints(("Goal" :in-theory (e/d (read-byte$ state-p1))))))

 (defsection object
   :extension read-object$
   (defthm state-preserved-by-read-object-when-eof
     (implies (and (mv-nth 0 (read-object channel state))
                   (state-p1 state)
                   (open-input-channel-p1 channel :object state))
              (equal (mv-nth 2 (read-object channel state))
                     state))
     :hints(("Goal" :in-theory (e/d (read-object state-p1)))))))



; -----------------------------------------------------------------------------
;
;                                  OUTPUT
;
; -----------------------------------------------------------------------------

(defsection open-output-channel
  :parents (io)
  :short "Open a file for writing."

  :long "<p><b>Signature:</b> @(call open-output-channel) returns @('(mv
channel state)')</p>

<ul>

<li>@('file-name') can be either @(':string') (to indicate that you want to
print to a string stream), or a string like @('\"temp.txt\"')that names the
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

<p>There are various reasons and ways that @('open-output-channel') can fail,
which can be platform dependent.  For instance:</p>

<ul>

<li>If you try to write to a file in a directory that does not exist, then on
SBCL you will get a raw Lisp error but on CCL the directory will be
created.</li>

<li>If you try to open a file for which you do not have permission, say
@('/etc/shadow'), a hard Lisp error can result.</li>

</ul>"

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
    :hints(("Goal" :in-theory (enable open-output-channel-p1 put-global)))))



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



(defsection close-output-channel
  :parents (io)
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

(defthm open-channel1-of-revappend-charlist
  (implies (and (open-channel1 x)
                (equal (cadar x) :character)
                (character-listp y))
           (open-channel1 (cons (car x) (revappend y (cdr x)))))
  :otf-flg t)

;; matches unicode/explode-nonnegative-integer.lisp
(defthm character-listp-of-explode-nonnegative-integer
  (equal (character-listp (explode-nonnegative-integer n base acc))
         (character-listp acc))
  :hints(("Goal" :in-theory (disable floor mod digit-to-char))))

;; does NOT match unicode/explode-atom.lisp (so we renamed this theorem).
;; unicode version includes print-base-p hyp.
(defthm character-listp-explode-atom
  (character-listp (explode-atom x base)))

; Added by Matt K. for princ$ change 12/7/2012.
(defthm character-listp-explode-atom+
  (character-listp (explode-atom+ x base radix)))



;; I-AM-HERE
(defsection princ$
  :parents (io)
  ;; BOZO ACL2's documentation for princ$ is nice, it'd be good to have a better
  ;; integration between it and XDOC.

  (defthm state-p1-of-princ$
    (implies (and (state-p1 state)
                  (symbolp channel)
                  (open-output-channel-p1 channel :character state))
             (state-p1 (princ$ x channel state)))
    :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1 explode-atom)))))

  (defthm open-output-channel-p1-of-princ$
    (implies (and (state-p1 state)
                  (open-output-channel-p1 channel :character state))
             (open-output-channel-p1 channel :character (princ$ x channel state)))))


(defsection write-byte$
  :parents (io)

  ;; Write-byte$
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
             (open-output-channel-p1 channel :byte (write-byte$ byte channel state)))))


(defsection print-object$
  :parents (io)

  ;; print-object$
  (defthm state-p1-of-print-object$
    (implies (and (state-p1 state)
                  (symbolp channel)
                  (open-output-channel-p1 channel :object state))
             (state-p1 (print-object$ x channel state)))
    :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1)))))

  (defthm open-output-channel-p1-of-print-object$
    (implies (and (state-p1 state)
                  (open-output-channel-p1 channel :object state))
             (open-output-channel-p1 channel :object (print-object$ x channel state)))))



;; Close-output-channel's guard requires that the channel is not the symbol:
;; ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0.
;; So we need to prove that this symbol is never returned from
;; open-output-channel.  This is true because symbol created ends in "-" and
;; then the new file clock, which is at least 1.  Blech!
(encapsulate nil
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
           (charlist-suffixp (coerce (symbol-name x) 'list)
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


(defsection file-measure
  :parents (io)
  :short "A measure for admitting functions that read from files."

  :long "<p><b>Signature:</b> @(call file-measure) returns a natural
number.</p>

<ul>

<li>@('channel') may be any symbol but is typically an open input channel.</li>

<li>@('state-state') is typically the ACL2 @(see state).</li>

</ul>

<p>This is a @(see logic)-mode function, but its logical definition is tricky;
see @(see logical-story-of-io).  The basic gist is that it returns how many
objects are left in the channel and hence how many functions can still be
read.</p>

<p>This function is only meant to be used to admit functions, and cannot be
executed on the real ACL2 @(see state).</p>

<p>History.  Jared wrote an initial version of this function for the Unicode
books.  Sol then extended it with a hack that allows us to prove it decreasing
without assuming state-p1 in the object case.  (Really it's just a workaround
for the fact that read-object checks @('(cdr entry)') as a substitute for
@('(consp (cdr entry))') to find whether there are objects remaining.</p>"

  (defun file-measure (channel state-state)
    (declare (xargs :guard (and (symbolp channel)
                                (state-p1 state-state))))
    (+ (len (cddr (assoc-equal channel (open-input-channels state-state))))
       (if (consp (cddr (assoc-equal channel (open-input-channels state-state))))
           (if (cdr (last (cddr (assoc-equal channel (open-input-channels
                                                      state-state))))) 1 0)
         (if (cddr (assoc-equal channel (open-input-channels state-state))) 1 0))))

  (defthm file-measure-of-read-byte$-weak
    (<= (file-measure channel (mv-nth 1 (read-byte$ channel state)))
        (file-measure channel state))
    :rule-classes (:rewrite :linear))

  (defthm file-measure-of-read-byte$-strong
    (implies (mv-nth 0 (read-byte$ channel state))
             (< (file-measure channel (mv-nth 1 (read-byte$ channel state)))
                (file-measure channel state)))
    :rule-classes (:rewrite :linear))

  (defthm file-measure-of-read-byte$-rw
    (implies (mv-nth 0 (read-byte$ channel state))
             (equal (file-measure channel (mv-nth 1 (read-byte$ channel state)))
                    (+ -1 (file-measure channel state)))))

  (defthm file-measure-of-read-char$-weak
    (<= (file-measure channel (mv-nth 1 (read-char$ channel state)))
        (file-measure channel state))
    :rule-classes (:rewrite :linear))

  (defthm file-measure-of-read-char$-strong
    (implies (mv-nth 0 (read-char$ channel state))
             (< (file-measure channel (mv-nth 1 (read-char$ channel state)))
                (file-measure channel state)))
    :rule-classes (:rewrite :linear))

  (defthm file-measure-of-read-char$-rw
    (implies (mv-nth 0 (read-char$ channel state))
             (equal (file-measure channel (mv-nth 1 (read-char$ channel state)))
                    (1- (file-measure channel state)))))

  (defthm file-measure-of-read-object-weak
    (<= (file-measure channel (mv-nth 2 (read-object channel state)))
        (file-measure channel state))
    :rule-classes (:rewrite :linear))

  (defthm file-measure-of-read-object-strong
    (implies (not (mv-nth 0 (read-object channel state)))
             (< (file-measure channel (mv-nth 2 (read-object channel state)))
                (file-measure channel state)))
    :rule-classes (:rewrite :linear))

  (defthm file-measure-of-read-object-rw
    (implies (not (mv-nth 0 (read-object channel state)))
             (equal (file-measure channel (mv-nth 2 (read-object channel state)))
                    (1- (file-measure channel state))))))


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
                    file-measure))
