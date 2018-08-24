; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "../util/defs")
(include-book "../util/echars")
(include-book "std/io/base" :dir :system)
(local (include-book "../util/arithmetic"))
(set-state-ok t)

(local (in-theory (disable acl2::file-measure-of-read-byte$-rw)))

(define vl-read-file-loop-aux
  :parents (vl-read-file)
  :short "Tail-recursive, executable loop for @(see vl-read-file)."
  ((channel  (and (symbolp channel)
                  (open-input-channel-p channel :byte state)))
   (filename stringp :type string        "Current file name")
   (line     posp    :type (integer 1 *) "Current line number")
   (col      natp    :type (integer 0 *) "Current column number")
   (len      natp    :type (integer 0 *) "Current byte number")
   (nrev)
   &key
   (state 'state))
  :split-types t
  :returns
  (mv (nrev "Characters from the file in reverse order.")
      (len  natp :rule-classes :type-prescription)
      state)
  :long "<p>You should never need to reason about this function directly,
because it is typically rewritten into @(see vl-read-file-loop) using the
following rule:</p> @(def vl-read-file-loop-aux-redef)"
  :measure (file-measure channel state)
  (b* ((nrev  (nrev-fix nrev))
       (len (lnfix len))
       ((unless (mbt (state-p state)))
        (mv nrev len state))
       ((mv byte state)
        (read-byte$ channel state))
       ((unless byte) ;; EOF
        (mv nrev len state))
       ((the character char) (code-char (the (unsigned-byte 8) byte)))
       (echar      (make-vl-echar-fast :char char
                                       :filename filename
                                       :line line
                                       :col col))
       (newlinep   (eql char #\Newline))
       (next-line  (if newlinep (the (integer 0 *) (+ 1 line)) line))
       (next-col   (if newlinep 0 (the (integer 0 *) (+ 1 col))))
       (next-len   (the (integer 0 *) (+ 1 len)))
       (nrev       (nrev-push echar nrev)))
    (vl-read-file-loop-aux channel filename next-line next-col next-len nrev)))

(define vl-read-file-loop
  :parents (vl-read-file)
  :short "Logically nice loop for @(see vl-read-file)."
  ((channel  symbolp  "Channel we're reading from.")
   (filename stringp  "Current file name.")
   (line     posp     "Current line number.")
   (col      natp     "Current column number.")
   &key
   (state 'state))
  :guard (open-input-channel-p channel :byte state)
  :returns
  (mv (data "Characters from the file." vl-echarlist-p)
      (len  "Number of characters read." (equal len (len data)))
      (state (and (state-p1 state)
                  (open-input-channel-p1 channel :byte state))
             :hyp (and (force (state-p1 state))
                       (force (symbolp channel))
                       (force (open-input-channel-p1 channel :byte state)))))
  :measure (file-measure channel state)
  :verify-guards nil
  (mbe :logic
       (b* (((unless (state-p state))
             (mv nil 0 state))
            ((mv byte state)
             (read-byte$ channel state))
            ((unless byte)
             (mv nil 0 state))
            (char      (code-char (the (unsigned-byte 8) byte)))
            (echar     (make-vl-echar-fast :char char
                                           :filename filename
                                           :line line
                                           :col col))
            (newlinep  (eql char #\Newline))
            (next-line (if newlinep (+ 1 line) line))
            (next-col  (if newlinep 0 (+ 1 col)))
            ((mv rest len state)
             (vl-read-file-loop channel filename next-line next-col)))
         (mv (cons echar rest) (+ 1 len) state))
       :exec
       (b* (((local-stobjs nrev)
             (mv echars len nrev state))
            ((mv nrev len state)
             (vl-read-file-loop-aux channel filename line col 0 nrev))
            ((mv echars nrev)
             (nrev-finish nrev)))
         (mv echars len nrev state)))
  ///
  (local (in-theory (enable vl-read-file-loop-aux)))

  (defthm true-listp-of-vl-read-file-loop
    (true-listp (mv-nth 0 (vl-read-file-loop channel filename line col)))
    :rule-classes :type-prescription)

  (defthm vl-read-file-loop-aux-redef
    (equal (vl-read-file-loop-aux channel filename line col len acc)
           (b* (((mv data & state)
                 (vl-read-file-loop channel filename line col)))
             (mv (append acc data)
                 (+ (lnfix len) (len data))
                 state))))

  (verify-guards vl-read-file-loop-fn))

(defsection vl-read-file-hook
  :parents (vl-read-file)
  :short "Customizable hook for @(see vl-read-file)."
  :long "<p>This is generally intended for collecting up statistics on the
files that have been read.  By default we do nothing.</p>"

  (encapsulate
    (((vl-read-file-hook * * * state) => state
      :formals (filename contents len state)
      :guard (and (stringp filename)
                  (vl-echarlist-p contents)
                  (equal len (len contents)))))
    (local (defun vl-read-file-hook (filename contents len state)
             (declare (ignore filename contents len))
             state))
    (defthm state-p1-of-vl-read-file-hook
      (implies (force (state-p1 state))
               (state-p1 (vl-read-file-hook filename contents len state)))))

  (define vl-read-file-hook-default ((filename stringp)
                                     (contents vl-echarlist-p)
                                     (len (equal len (len contents)))
                                     state)
    :returns (state state-p1 :hyp (state-p1 state))
    (declare (ignore filename contents len))
    state)

  (defattach vl-read-file-hook vl-read-file-hook-default))

(define vl-read-file
  :parents (loader)
  :short "Read an entire file into a list of extended characters."
  ((filename stringp "The file to read.")
   &key (state 'state))
  :returns
  (mv (okp    booleanp :rule-classes :type-prescription)
      (result "On success, the entire contents of @('filename') as a list of
               @(see extended-characters)."
              vl-echarlist-p)
      (len    (equal len (len result)))
      (state  state-p1 :hyp (force (state-p1 state))))
  :long "<p>We read the file with @(see read-byte$) instead of @(see
read-char$), because this seems perhaps to be more reliable.  In particular,
even if the Lisp system wants to use Unicode or some other encoding for
character streams, @('read-byte$') should always safely return octets.</p>"
  (b* ((filename            (string-fix filename))
       ((mv channel state)  (open-input-channel filename :byte state))
       ((unless channel)    (mv nil nil 0 state))
       ((mv data len state) (vl-read-file-loop channel filename 1 0))
       (state               (close-input-channel channel state))
       (state               (vl-read-file-hook filename data len state)))
    (mv t data len state))
  ///
  (defthm true-listp-of-vl-read-file
    (true-listp (mv-nth 1 (vl-read-file filename)))
    :rule-classes :type-prescription)

  (defthm vl-read-file-when-error
    (b* (((mv okp result ?state) (vl-read-file filename)))
      (implies (not okp)
               (not result)))))

;; [Jared] it looks like these aren't used anymore (they used to be used in
;; vl2014's kit/pp command. Commenting them out until we want them again.

;; (define vl-read-file-rchars
;;   :parents (vl-read-file)
;;   :short "Optimized alternative to @(see vl-read-file) that reads the entire
;; file into @(see nrev)."
;;   ((filename stringp "The file to read.") nrev &key (state 'state))
;;   :returns (mv okp nrev state)
;;   :long "<p>We implement this mainly for @(see vl-read-files).</p>"
;;   :enabled t
;;   (mbe :logic
;;        (non-exec
;;         (b* (((mv okp data state)
;;               (vl-read-file filename)))
;;           (mv okp (append nrev data) state)))
;;        :exec
;;        (b* (((mv channel state)  (open-input-channel filename :byte state))
;;             ((unless channel)    (mv nil nrev state))
;;             ((mv nrev state)     (vl-read-file-loop-aux channel filename 1 0 nrev))
;;             (state               (close-input-channel channel state)))
;;          (mv t nrev state)))
;;   :guard-hints(("Goal" :in-theory (enable vl-read-file))))

;; (define vl-read-files-aux
;;   :parents (vl-read-files)
;;   :short "Tail recursive loop for @(see vl-read-files)."
;;   ((filenames string-listp "The files to read.") nrev &key (state 'state))
;;   :returns (mv errmsg? nrev state)
;;   :long "<p>You should never need to reason about this directly, because of
;; the following rule:</p> @(def vl-read-files-aux-redef)"
;;   (b* (((when (atom filenames))
;;         (let ((nrev (nrev-fix nrev)))
;;           (mv nil nrev state)))
;;        ((mv okp nrev state)
;;         (vl-read-file-rchars (car filenames) nrev))
;;        ((unless okp)
;;         (mv (msg "Error reading file ~s0." (car filenames))
;;             nrev state)))
;;     (vl-read-files-aux (cdr filenames) nrev)))

;; (define vl-read-files
;;   :parents (loader)
;;   :short "Read an entire list of files into a list of extended characters."
;;   ((filenames string-listp "The files to read.") &key (state 'state))
;;   :returns
;;   (mv (errmsg? "NIL on success, or an error @(see msg) that says which
;;                 file we were unable to read, otherwise.")
;;       (data    "On success, extended characters from all files, in order."
;;                vl-echarlist-p :hyp :fguard)
;;       (state   state-p1 :hyp (force (state-p1 state))))
;;   :verify-guards nil
;;   (mbe :logic
;;        (b* (((when (atom filenames))
;;              (mv nil nil state))
;;             ((mv okp first state) (vl-read-file (car filenames)))
;;             ((unless okp)
;;              (mv (msg "Error reading file ~s0." (car filenames)) nil state))
;;             ((mv okp rest state) (vl-read-files (cdr filenames))))
;;          (mv okp (append first rest) state))
;;        :exec
;;        (with-local-stobj nrev
;;          (mv-let (errmsg echars nrev state)
;;            (b* (((mv errmsg nrev state) (vl-read-files-aux filenames nrev))
;;                 ((mv echars nrev)       (nrev-finish nrev)))
;;              (mv errmsg echars nrev state))
;;            (mv errmsg echars state))))
;;   ///
;;   (local (in-theory (enable vl-read-files-aux)))

;;   (defthm true-listp-of-vl-read-files
;;     (true-listp (mv-nth 1 (vl-read-files filenames)))
;;     :rule-classes :type-prescription)

;;   (defthm vl-read-files-aux-redef
;;     (equal (vl-read-files-aux filenames acc)
;;            (b* (((mv errmsg data state)
;;                  (vl-read-files filenames)))
;;              (mv errmsg (append acc data) state)))
;;     :hints(("Goal" :induct (vl-read-files-aux-fn filenames acc state))))

;;   (verify-guards vl-read-files-fn))
