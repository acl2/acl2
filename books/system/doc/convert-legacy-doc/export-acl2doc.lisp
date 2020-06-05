; XDOC Documentation System for ACL2
; Copyright (C) 2014 Centaur Technology
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
;
; Modified November 2014 by Matt Kaufmann, to convert book documentation
; instead of ACL2 system documentation

; defdoc -> defxdoc converter

(in-package "XDOC")
(include-book "import-acl2doc")
(include-book "std/util/defconsts" :dir :system)
(include-book "std/strings/top" :dir :system)
(include-book "std/osets/sort" :dir :system)
(include-book "xdoc/parse-xml" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)
(set-state-ok t)
(program)


; Note: quick and dirty, ugly ill-documented code.
;
; I thought this was going to be really easy: i'd just use the existing ACL2
; importer to turn the strings into XML, then dump them into an output file.
; That took 10 minutes to write, but the result was rather ugly.
;
;  - there was no sensible word wrapping
;  - there was excessive escaping since no @({...}) or @('...') were used
;  - every link was of the <see topic='@(url foo)'>foo</see> variety, which
;    was really long
;  - the <code> blocks weren't indented, so emacs color highlighting was
;    completely wrong.
;  - the defxdoc forms were indented weirdly, e.g.,
;
;     (defxdoc
;      acl2::|A Sketch of How the Rewriter Works|
;      :parents (acl2::|Pages Written Especially for the Tours|)
;      :short "A Sketch of How the Rewriter Works"
;      :long
;      "<p></p>
;      ...")
;
; I started to fix some of these with some elisp macros.  But for the
; preprocessor stuff, it seems like fixing it in ACL2 is easier.  My basic
; approach was:
;
;  - Change the way XDOC stuff is generated so it's pure XML
;  - Parse in these XML tokens with XDOC's primitive XML parser
;  - Write a fixer-upper that replaces, e.g., <code> with @({...}), <tt> with
;    @('...'), and fixes <see ...> links in the obvious case.
;  - Fix up the XML tokens, creating new, mixed XML/preprocessor text.

(defun next-open-or-close-tag (tokens)
  ;; returns (mv prefix suffix), car of suffix is thef first open/close tag.
  (b* (((when (atom tokens))
        (mv nil nil))
       ((when (or (opentok-p (car tokens))
                  (closetok-p (car tokens))))
        (mv nil tokens))
       ((mv prefix suffix)
        (next-open-or-close-tag (cdr tokens))))
    (mv (cons (car tokens) prefix) suffix)))

(defun tokens-to-plaintext-aux (tokens acc)
  ;; acc is a character list in reverse order.
  (b* (((when (atom tokens))
        acc)
       (acc (cond ((texttok-p (car tokens))
                   (str::revappend-chars (texttok-text (car tokens)) acc))
                  ((entitytok-p (car tokens))
                   (str::revappend-chars (entitytok-as-plaintext (car tokens)) acc))
                  (t
                   (progn$
                    (cw "*** TOKENS-TO-PLAINTEXT: Expected only text/entity tokens!")
                    acc)))))
    (tokens-to-plaintext-aux (cdr tokens) acc)))

(defun tokens-to-plaintext (tokens)
  (b* ((acc (tokens-to-plaintext-aux tokens nil))
       (str (str::rchars-to-string acc)))
    ;; Ordinary entities have already been converted.  however, acl2's exporter
    ;; also converts @ into @@.  So for use in @({...}) and @('...') sections, we
    ;; need to convert it back.
    (str::strsubst "@@" "@" str)))

(defun write-attrval (x acc)
  ;; see read-attrval.  x is some attribute value.  if it has any quotes we
  ;; need to escape them.  we'll prefer single quotes because they're nicer
  ;; within lisp text.
  (cond ((not (str::substrp "'" x))
         ;; no single quotes in the value, so it's okay to use 'value'
         (cons #\' (str::revappend-chars x (cons #\' acc))))
        ((not (str::substrp "\"" x))
         ;; no double quotes in value, so it's okay to use "value"
         (cons #\" (str::revappend-chars x (cons #\" acc))))
        (t
         (er hard? 'write-attrval-aux
             "Attribute value has quotes in it."))))

(defun write-atts (x acc)
  ;; atts is an alist of name . value
  (b* (((when (atom x))
        acc)
       ((cons name value) (car x))
       (acc (cons #\Space acc))
       (acc (str::revappend-chars name acc))
       (acc (cons #\= acc))
       (acc (write-attrval value acc)))
    (write-atts (cdr x) acc)))

(defun write-opentok (x acc)
  (b* ((name (opentok-name x))
       (atts (opentok-atts x))
       (acc (str::revappend-chars "<" acc))
       (acc (str::revappend-chars name acc))
       (acc (write-atts atts acc))
       (acc (str::revappend-chars ">" acc)))
    acc))

(defun write-closetok (x acc)
  (b* ((name (closetok-name x))
       (acc (str::revappend-chars "</" acc))
       (acc (str::revappend-chars name acc))
       (acc (str::revappend-chars ">" acc))
       ;;(acc (if (member-equal (closetok-name (car tokens)) '("p" "blockquote"))
       ;;         (list* #\Newline #\Newline acc)
       ;;       acc))
       )
    acc))

(defun pure-upper-case-p (x)
  (and (str::string-has-some-up-alpha-p x 0 (length x))
       (not (str::string-has-some-down-alpha-p x 0 (length x)))))

(defun fixup (tokens acc state)
  ;; acc is a character list in reverse order.
  (b* (((when (atom tokens))
        (mv acc state))

       ((when (texttok-p (car tokens)))
        (fixup (cdr tokens)
               (str::revappend-chars (texttok-text (car tokens)) acc)
               state))

       ((when (entitytok-p (car tokens)))
        (fixup (cdr tokens)
               (str::revappend-chars (entitytok-as-entity (car tokens)) acc)
               state))

       ((when (closetok-p (car tokens)))
        (fixup (cdr tokens)
               (write-closetok (car tokens) acc)
               state))

       ((when (opentok-p (car tokens)))
        (b* ((name (opentok-name (car tokens)))
             (atts (opentok-atts (car tokens))))

          (cond ((equal name "code")
                 ;; Convert <code>...</code> fragments into @({...}) when possible,
                 ;; since it's (1) more readable and (2) helps &amp; stuff go away.
                 (b* (((mv prefix suffix) (next-open-or-close-tag (cdr tokens)))

                      ((unless (and (consp suffix)
                                    (closetok-p (car suffix))
                                    (equal (closetok-name (car suffix)) "code")))
                       ;; Code tag that is never closed or has embedded markup.
                       ;; Embedded markup can occasionally happen, e.g., it is
                       ;; used in 'acl2::|A Flying Tour of ACL2| as a horrble
                       ;; structuring device.  It's sort of a miracle that it
                       ;; works at all.  We can't turn these into preprocessor
                       ;; stuff, so leave them as code tags.
                       (cw "Warning: <code> block too fancy for preprocessor!~%")
                       (fixup (cdr tokens)
                              (write-opentok (car tokens) acc)
                              state))

                      (guts (tokens-to-plaintext prefix))
                      ((when (str::substrp "})" guts))
                       ;; Code tag with }) occurring somewhere inside it.  Rare,
                       ;; but can occasionally happen with abstract stobj stuff,
                       ;; e.g., ":preserved update-misc{preserved})".  So, we can't
                       ;; safely turn these into preprocessor things.  Leave them
                       ;; as ordinary code tags.
                       (cw "Warning: <code> block too fancy for preprocessor!~%")
                       (fixup (cdr tokens)
                              (write-opentok (car tokens) acc)
                              state))

                      ;; Indent every code line one space, so that s-exprssions
                      ;; will not start on column zero and screw up emacs
                      ;; syntax highlighting.
                      (guts (str::trim-bag guts '(#\Newline)))
                      (indented-guts (str::prefix-lines guts " "))

                      ;; Else, fine to use the preprocessor instead.
                      (acc (str::revappend-chars "@({" acc))
                      (acc (cons #\Newline acc))
                      ;(acc (cons #\Space acc)) ;; due to trim
                      ;(acc (str::revappend-chars (str::trim indented-guts) acc))
                      ;(acc (cons #\Newline acc)) ;; due to trim
                      (acc (str::revappend-chars indented-guts acc))
                      (acc (cons #\Newline acc))
                      (acc (str::revappend-chars "})" acc)))
                   (fixup (cdr suffix) acc state)))

                ((equal name "tt")
                 (b* (((mv prefix suffix) (next-open-or-close-tag (cdr tokens)))

                      ((unless (and (consp suffix)
                                    (closetok-p (car suffix))
                                    (equal (closetok-name (car suffix)) "tt")))
                       ;; tt tag with embedded markup?  don't convert it...
                       (fixup (cdr tokens)
                              (write-opentok (car tokens) acc)
                              state))

                      (guts (tokens-to-plaintext prefix))
                      ((when (str::substrp "')" guts))
                       ;; has ') somewhere inside it, can't convert it.
                       ;; several occurrences of this due to things like
                       ;; <tt>(equal x x')</tt>.
                       (fixup (cdr tokens)
                              (write-opentok (car tokens) acc)
                              state))

                      ;; else, fine to use the preprocessor.
                      (acc (str::revappend-chars "@('" acc))
                      (acc (str::revappend-chars guts acc))
                      (acc (str::revappend-chars "')" acc)))
                   (fixup (cdr suffix) acc state)))

                ((equal name "see")
                 (b* (((mv prefix suffix) (next-open-or-close-tag (cdr tokens)))

                      ((unless (and (consp suffix)
                                    (closetok-p (car suffix))
                                    (equal (closetok-name (car suffix)) "see")))
                       ;; see tag with embedded markup?  something fancy, don't
                       ;; convert it
                       (fixup (cdr tokens)
                              (write-opentok (car tokens) acc)
                              state))

                      (topic (cdr (assoc-equal "topic" atts)))
                      (codep (assoc-equal "use-tsee" atts))

                      ((unless topic)
                       (cw "*** Fubar atts for <see> tag: ~x0.~%" atts)
                       (fixup (cdr tokens)
                              (write-opentok (car tokens) acc)
                              state))

                      ((unless (and (str::strprefixp "@(url " topic)
                                    (str::strsuffixp ")" topic)))
                       (cw "*** Fubar topic for <see> tag: ~x0.~%" topic)
                       (fixup (cdr tokens)
                              (write-opentok (car tokens) acc)
                              state))

                      (link-target (subseq topic (length "@(url ") (- (length topic) 1)))
                      (link-text   (tokens-to-plaintext prefix))
                      ((unless (str::istreqv link-target link-text))
                       ;; fancy link, leave it alone
                       (or (not codep)
                           (cw "*** Fubar: fancy code link?~%~
                                   Tag: ~x0~%
                                   Text: ~x1~%~%"
                               (car tokens)
                               link-text))
                       (fixup (cdr tokens)
                              (write-opentok (car tokens) acc)
                              state))

                      ;; simple link, turn it into @(see foo).  safety check to
                      ;; try to avoid package problems...
                      ((mv error ?target-sym &)
                       (parse-symbol link-target 0 (length link-target)
                                     'acl2::rewrite
                                     (known-package-alist state)
                                     t))
                      ((when error)
                       (cw "*** fubar link symbol: ~x0.~%" topic)
                       (fixup (cdr tokens)
                              (write-opentok (car tokens) acc)
                              state))

; Originally this is what we were doing.  This was kind of misguided.  We were
; using the link target (a symbol, so typically in all upper case) and then
; trying to downcase it.  That's better than leaving it in all upper case.  But
; better yet, let's just use the actual link text, since that'll preserve the
; capitalization of things like ~ilc[Guard].  This might not be completely safe
; for symbols that need bar escaping or that sort of thing.  But maybe it will
; work in practice.

                      (new-link-text
                       (fmt-to-str target-sym 'acl2::rewrite))

                      (new-link-text
                       (if (str::istreqv (symbol-name target-sym) link-text)
                           ;; seems safe enough
                           link-text
                         (prog2$
                          (cw "*** hard symbol to link nicely: ~x0.~%" topic)
                          new-link-text)))

                      (- (or (not (pure-upper-case-p new-link-text))
                             (cw "Capitalized link may get downcased: ~x0.~%"
                                 new-link-text)))
                      (acc (if codep
                               (str::revappend-chars "@(tsee " acc)
                             (str::revappend-chars "@(see " acc)))
                      ;; (acc (str::revappend-chars new-link-text acc))
                      (acc (str::revappend-chars new-link-text acc))

                      (acc (str::revappend-chars ")" acc)))
                   (fixup (cdr suffix) acc state)))

                (t
                 (fixup (cdr tokens)
                        (write-opentok (car tokens) acc)
                        state))))))
    (cw "*** FIXUP: bad token ~x0.~%")
    (mv acc state)))

(defun fixup-str (tokens state)
  (b* (((mv acc state) (fixup tokens nil state)))
    (mv (str::rchars-to-string acc) state)))

(defun fixup-topic (topic state)
  (b* ((name    (cdr (assoc :name topic)))
       (parents (cdr (assoc :parents topic)))
       (short   (str::trim (cdr (assoc :short topic))))
       (long    (str::trim (cdr (assoc :long topic))))
       (- (cw "Processing ~x0.~%" name))
       ((mv err1 short-tokens) (parse-xml short))
       ((when err1)
        (cw "*** In topic ~x0, error in :short:~%" name)
        (let ((state (princ$ err1 *standard-co* state)))
          (mv nil state)))
       ((mv err2 long-tokens)  (parse-xml long))
       ((when err2)
        (cw "*** In topic ~x0, error in :long:~%" name)
        (let ((state (princ$ err2 *standard-co* state)))
          (mv nil state)))
       ((mv short-fixed state) (fixup-str short-tokens state))
       ((mv long-fixed state)  (fixup-str long-tokens state)))
    (mv `((:name    . ,name)
          (:parents . ,parents)
          (:short   . ,short-fixed)
          (:long    . ,long-fixed))
        state)))

(defun fixup-topics (topics state)
  (b* (((when (atom topics))
        (mv nil state))
       ((mv topic1 state) (fixup-topic (car topics) state))
       ((mv rest state)   (fixup-topics (cdr topics) state)))
    (mv (cons topic1 rest) state)))



; sorting topics in the file... kind of a crapshoot.  maybe a mostly alphabetical
; order is at least somewhat reasonable?

(defun acl2-native-symbolp (x)
  (equal (intern$ (symbol-name x) "ACL2") x))

(assert! (acl2-native-symbolp 'common-lisp::append))
(assert! (acl2-native-symbolp 'acl2::rewrite))
(assert! (not (acl2-native-symbolp 'xdoc::rewrite)))

(defun prepare-for-sort (topics)
  (if (atom topics)
      nil
    (cons (cons (if (acl2-native-symbolp (cdr (assoc :name (car topics)))) 0 1)
                (car topics))
          (prepare-for-sort (cdr topics)))))

(defun my-sort (topics)
  (strip-cdrs (set::mergesort (prepare-for-sort topics))))

#||
(acl2::defconsts (*fixed-topics* state)
  (mv-let
   (fixed state)
   (fixup-topics
    (cons '((:name    . acl2::acl2)
            (:parents . (acl2::top))
            (:short   . "ACL2 documentation (system only, not including the community books)")
            (:long    . "<p>This is the ACL2 documentation.  For a manual that includes both the ACL2 documentation and the ACL2 community books, see <a href='http://fv.centtech.com/acl2/latest/doc/'>http://fv.centtech.com/acl2/latest/doc/</a>.</p>"))
          xdoc::*acl2-ground-zero-topics*)
    state)
   (mv (my-sort fixed) state)))
||#

; I started out just using fms! to print things, which was easy but not very
; good.  It indented the forms weirdly and printed symbol names unnecessarily.
; So I use a custom function to print these now.

(defun write-parents-aux (x acc state)
  (b* (((when (atom x))
        (mv acc state))
       (str1 (fmt-to-str (car x) 'acl2::rewrite))
       (acc (str::revappend-chars str1 acc))
       ((when (atom (cdr x)))
        (mv acc state)))
    (write-parents-aux (cdr x) (cons #\Space acc) state)))

(defun write-topic (x acc state)
  (b* ((name    (cdr (assoc :name x)))
       (parents (cdr (assoc :parents x)))
       (short   (str::trim (cdr (assoc :short x))))
       (long    (str::trim (cdr (assoc :long x))))

       (acc     (str::revappend-chars "(defxdoc " acc))

       ;; use fmt-to-string to deal with all lisp-encoding stuff
       (name-str (fmt-to-str name  'acl2::rewrite))
       (short-str (fmt-to-str short 'acl2::rewrite))
       (long-str (fmt-to-str long  'acl2::rewrite))

       (acc     (str::revappend-chars name-str acc))
       (acc     (cons #\Newline acc))
       (acc     (str::revappend-chars "  :parents (" acc))
       ((mv acc state) (write-parents-aux parents acc state))
       (acc     (str::revappend-chars ")" acc))
       (acc     (cons #\Newline acc))
       (acc     (str::revappend-chars "  :short " acc))
       (acc     (str::revappend-chars (str::trim short-str) acc))
       (acc     (cons #\Newline acc))
       (acc     (str::revappend-chars "  :long " acc))
       ;; Put one space in front of everything.
       (acc     (str::revappend-chars (str::prefix-lines (str::trim long-str)
                                                         " ")
                                      acc))
       (acc     (cons #\) acc))
       (acc     (cons #\Newline acc))
       (acc     (cons #\Newline acc)))
    (mv acc state)))

(defun write-topics (x acc state)
  (b* (((when (atom x))
        (mv acc state))
       ((mv acc state) (write-topic (car x) acc state)))
    (write-topics (cdr x) acc state)))

(defttag :open-output-channel)

(defun substring-p-aux (index str1 str2)
  (cond ((zp index) t)
        (t (let ((index (1- index)))
             (and (eql (char str1 index)
                       (char str2 index))
                  (substring-p-aux index str1 str2))))))

(defun substring-p (str1 str2)
  (let ((len1 (length str1)))
    (and (<= len1 (length str2))
         (substring-p-aux len1 str1 str2))))

(defun some-substring-p (str-list str2)
  (cond ((endp str-list) nil)
        (t (or (substring-p (car str-list) str2)
               (some-substring-p (cdr str-list) str2)))))

(defun topics-outside-dir-1 (dirs topics acc)
  (cond ((endp topics) acc)
        (t (topics-outside-dir-1
            dirs
            (cdr topics)
            (let ((topic (car topics)))
              (if (some-substring-p dirs
                                    (cdr (assoc :from topic)))
                  acc
                (cons (list (cdr (assoc :name topic))
                            (cdr (assoc :from topic)))
                      acc)))))))

(defun concatenate-to-all (prefix lst)
  (cond ((endp lst) nil)
        (t (cons (concatenate 'string prefix (car lst))
                 (concatenate-to-all prefix (cdr lst))))))

(defun topics-outside-dir (dir subdirs xdoc-table)
  (let ((sys-dir "[books]/"))
    (topics-outside-dir-1 (concatenate-to-all sys-dir (cons dir subdirs))
                          xdoc-table
                          nil)))

(defun include-xdoc-books (dirs acc)
  (cond ((endp dirs) acc)
        (t (include-xdoc-books
            (cdr dirs)
            (list* #\Newline
                   #\Newline
                   (str::revappend-chars
                    (fmt-to-str (list 'include-book
                                      (concatenate 'string (car dirs) "-xdoc"))
                                'acl2::rewrite)
                    acc))))))

(defun export-acl2doc (topics outfile subdirs state)

; We insist that all topics are introduced under dir, unless dir is nil.

  (b* (((mv channel state)
        (open-output-channel! outfile :character state))
       ((unless channel)
        (er soft 'export-acl2doc "failed to open ~x0" outfile))
       (acc (str::revappend-chars
             "; This file was initially generated automatically from legacy documentation
; strings.  See source files in this directory for copyright and license
; information."
             nil))
       (acc (str::revappend-chars "(in-package \"ACL2\")"
                                  (list* #\Newline #\Newline acc)))
       (acc (str::revappend-chars "(include-book \"xdoc/top\" :dir :system)"
                                  (list* #\Newline #\Newline acc)))
       (acc (include-xdoc-books subdirs
                                (list* #\Newline #\Newline acc)))
       ((mv fixed-topics state) (fixup-topics topics state))
       (fixed-topics (my-sort fixed-topics))
       ((mv acc state) (write-topics fixed-topics acc state))
       (string-to-print (str::rchars-to-string acc))
       (state (princ$ string-to-print channel state))
       (state (close-output-channel channel state)))
      (value outfile)))

(defun include-book-forms (infiles)
  (cond ((endp infiles) nil)
        (t (cons `(include-book ,(car infiles) :dir :system)
                 (include-book-forms (cdr infiles))))))

(defmacro make-xdoc-file (&key out ins dir subdirs)
  (declare (xargs :guard (and (string-listp ins)
                              (or (null dir)
                                  (stringp dir))
                              (string-listp subdirs))))
  `(progn

     (include-book "std/portcullis" :dir :system)
     (include-book "xdoc/base" :dir :system)

     (table xdoc 'doc nil)

     ,@(include-book-forms ins)

     (encapsulate
      ()
      (local (include-book "system/doc/acl2-doc-wrap" :dir :system))
      (make-event
       `(defconst *ignored-xdoc-table* ; includes above books and system
          ',(get-xdoc-table (w state)))))

     (defun remove-ignored-topics (x bad)
       (declare (xargs :mode :program))
       (if (atom x)
           nil
         (if (find-topic (cdr (assoc :name (car x))) bad)
             (remove-ignored-topics (cdr x) bad)
           (cons (car x)
                 (remove-ignored-topics (cdr x) bad)))))

     (make-event
      `(defconst *new-xdoc-table*
         ',(remove-ignored-topics (xdoc::get-xdoc-table (w state))
                                  *ignored-xdoc-table*)))

     (make-event
      (let ((bad (and ,dir
                      (topics-outside-dir ,dir ',subdirs *new-xdoc-table*))))
        (cond (bad (er soft 'make-xdoc-file
                       "Found these TOPIC/FILE pairs for which topic is ~
                          defined in FILE but FILE is not under ~x0:~|  ~x1"
                       ,dir bad))
              (t (er-progn
                  (export-acl2doc *new-xdoc-table* ,out ',subdirs state)
                  (value '(value-triple '(:exported-to ,out))))))))))
