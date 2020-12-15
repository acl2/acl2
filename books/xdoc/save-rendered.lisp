; XDOC Documentation System for ACL2
; Copyright (C) 2009-2016 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com> (but see next comment)

; This book was created by Matt Kaufmann to define function save-rendered,
; essentially using code that was formerly in community book
; books/doc/top.lisp, with original author Jared Davis.

(in-package "XDOC")

(include-book "defxdoc-raw")
(include-book "save")
(include-book "system/doc/render-doc-base" :dir :system)
(include-book "alter")
(include-book "xdoc-error")

(set-state-ok t)
(program)

(defttag :open-output-channel!)

(defconst *acl2-doc-search-separator* "###---###---###---###---###")

(defun acl2-doc-fix-symbol-msg (sym)
  (cond ((eq (intern$ (symbol-name sym) "ACL2") sym)
         (msg "~s0" (symbol-name sym)))
        (t (msg "~s0::~s1" (symbol-package-name sym) (symbol-name sym)))))

(defun acl2-doc-fix-symbol-lst-msg (lst)
  (cond ((endp lst) "")
        ((endp (cdr lst))
         (acl2-doc-fix-symbol-msg (car lst)))
        (t (msg "~@0 ~@1"
                (acl2-doc-fix-symbol-msg (car lst))
                (acl2-doc-fix-symbol-lst-msg (cdr lst))))))

(defun acl2-doc-print-topic (tuple channel state)

; Warning: Do not set the buffer to read-only here, because this
; function may be called repeatedly for the same buffer, e.g., by
; function acl2-doc-search-buffer.

  (fms! "~s0~|Topic: ~@1~|Parent list: (~@2)~|~@3~%~s4~|"
        (list (cons #\0 *acl2-doc-search-separator*)
              (cons #\1 (acl2-doc-fix-symbol-msg (nth 0 tuple)))
              (cons #\2 (acl2-doc-fix-symbol-lst-msg (nth 1 tuple)))
              (cons #\3 (if (equal (length tuple) 4)
                            (if (eq (nth 0 tuple) 'TOP)
                                ""
                              (msg ":DOC source: ~s0~|" (nth 3 tuple)))
                          ":DOC source: ACL2 Sources~|"))
              (cons #\4 (nth 2 tuple)))
        channel state nil))

(defun acl2-doc-print-topic-lst (tuple-lst channel state)
  (cond ((endp tuple-lst) state)
        (t (pprogn (acl2-doc-print-topic (car tuple-lst) channel state)
                   (acl2-doc-print-topic-lst (cdr tuple-lst) channel state)))))

(defun save-rendered (outfile
                      header
                      topic-list-name
                      error ; when true, cause an error on xdoc or Markup error
                      write-acl2-doc-search-file
                      state)

; See books/doc/top.lisp for an example call of xdoc::save-rendered.  In
; particular, the constant *rendered-doc-combined-header* defined in that file
; is an example of header, which goes at the top of the generated file; and
; topic-list-name is a symbol, such as acl2::*acl2+books-documentation*.

; Below we bind force-missing-parents-p and maybe-add-top-topic-p both true.
; These could be formal parameters if need be.

; Example of outfile:
;   (acl2::extend-pathname (cbd)
;                           "../system/doc/rendered-doc-combined.lsp"
;                           state))


  (let ((force-missing-parents-p t)
        (maybe-add-top-topic-p t)
        (search-file (if (position acl2::*directory-separator* outfile)
                         (concatenate 'string
                                      (acl2::get-directory-of-file outfile)
                                      acl2::*directory-separator-string*
                                      "acl2-doc-search")
                       "acl2-doc-search")))
    (state-global-let*
     ((current-package "ACL2" set-current-package-state))
     (b* ((- (initialize-xdoc-errors error))
          (state (f-put-global 'broken-links-limit nil state))
          ((mv ? all-topics0 state)
           (all-xdoc-topics state))
          (all-topics
           (time$
            (let* ((all-topics1 (normalize-parents-list ; Should we clean-topics?
                                 all-topics0))
                   (all-topics2 (if maybe-add-top-topic-p
                                    (maybe-add-top-topic all-topics1)
                                  all-topics1))
                   (all-topics3 (if force-missing-parents-p
                                    (force-missing-parents all-topics2)
                                  all-topics2)))
              all-topics3)))
          ((mv rendered state)
           (time$ (render-topics all-topics all-topics state)))
          (rendered (time$ (split-acl2-topics rendered nil nil nil)))
          (- (cw "Writing ~s0~%" outfile))
          ((mv channel state) (open-output-channel! outfile :character state))
          ((unless channel)
           (cw "can't open ~s0 for output." outfile)
           (acl2::silent-error state))
          (state (princ$ header channel state))
          (state (fms! "(in-package \"ACL2\")~|~%(defconst ~x0 '~|"
                       (list (cons #\0 topic-list-name))
                       channel state nil))
          (state (time$ (fms! "~x0"
                              (list (cons #\0 rendered))
                              channel state nil)))
          (state (fms! ")" nil channel state nil))
          (state (newline channel state))
          (state (close-output-channel channel state))
          (- (report-xdoc-errors 'save-rendered))
          ((when (not write-acl2-doc-search-file))
           (value '(value-triple :ok)))
          ((mv channel state)
           (open-output-channel! search-file :character state))
          ((unless channel)
           (cw "can't open ~s0 for output." search-file)
           (acl2::silent-error state))
          (state (acl2-doc-print-topic-lst rendered channel state))
          (state (close-output-channel channel state)))
       (value '(value-triple :ok))))))

(defmacro save-rendered-event (outfile
                               header
                               topic-list-name
                               error ; when true, cause an error on xdoc or Markup error
                               &key
                               script-file ; e.g., for building TAGS-acl2-doc
                               script-args
                               timep ; if a surrounding time$ call is desired
                               write-acl2-doc-search-file
                               )
  (let* ((form1 `(save-rendered
                  ,outfile ,header ,topic-list-name ,error
                  ,write-acl2-doc-search-file state))
         (form2 `(prog2$ (let ((script-file ,script-file)
                               (script-args ,script-args))
                           (and script-file
                                (sys-call ; requires active trust tag
                                 script-file script-args)))
                         ,form1))
         (form3 (if timep
                    `(time$ ,form2)
                  form2)))
    `(make-event
      ,form3)))
