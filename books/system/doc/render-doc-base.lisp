; Converter From ACL2 System Documentation to Text
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

; 10/29/2013, 12/2013, 5/2016: Mods made by Matt Kaufmann to support
; Emacs-based ACL2-Doc browser

(in-package "XDOC")
(include-book "xdoc/display" :dir :system)

(defconst *pkg-witness-acl2*
  (pkg-witness "ACL2"))

(defun base-pkg-display-override-acl2-pkg (base-pkg)
  (declare (ignore base-pkg)
           (xargs :guard t))
  *pkg-witness-acl2*)

(defattach base-pkg-display-override base-pkg-display-override-acl2-pkg)

(defun substitute? (new old seq)
  (declare (xargs :guard (and (stringp seq)
                              (characterp new))))

; Wait for state-global-let* to be defined, so that we can provide a
; local lemma.

  (if (position old seq)
      (substitute new old seq)
    seq))

; Comment from Matt K.

; Some of the complexity below first arose from an attempt by me to deal with a
; new topic name that contained the square-bracket character: SV::4VEC-[= .
; That name was breaking the acl2-doc Emacs browser.  My thought was to escape
; the square bracket, "...\[..."; but that got messy to handle for both Common
; Lisp and Emacs Lisp, in particular because Common Lisp was escaping the "\",
; and "\\[" didn't help Emacs.  So in part, I'm taking the easy way out
; instead, simply replacing [ and ] by { and }, respectively.  I'm not happy
; that rendered-name-acl2-doc already replaces ( and ) by those characters, but
; { and } seem less likely to cause confusion; in particular, there are topics
; SV::4VEC-< and SV::4VEC-[= that don't seem much related, so it would be sad
; to convert the latter to SV::4VEC-<=.

; But on 9/26/2018 I noticed a new problem, caused by the following topic
; (presumably added recently) in community book books/centaur/sv/vl/trunc.lisp.

; VL::|VL-EXPR-IS-{'0,_...}-P|

; Both the single-quote and the comma caused problems, and I see no obvious way
; to replace each by a character that suggests it (as I did for square
; brackets, described above).  So I'll replace ' by {{quote}} and , by
; {{comma}}.

(encapsulate
 ()

 (local
  (defthm character-listp-first-n-ac
    (implies (and (character-listp x)
                  (character-listp ac)
                  (force (natp n))
                  (force (<= n (len x))))
             (character-listp (first-n-ac n x ac)))
    :hints (("Goal" :induct (first-n-ac n x ac)))))

 (local
  (defthm len-revappend
    (equal (len (revappend x y))
           (+ (len x) (len y)))))

; Mihir M. mod, 04/2019: Adapt to the new definition of take.
 (local
  (defthm len-of-take
    (equal (len (take n x))
           (nfix n))))

 (local
  (defthm character-listp-nthcdr
    (implies (character-listp x)
             (character-listp (nthcdr n x)))))

 (local
  (defthm character-listp-cdr
    (implies (character-listp x)
             (character-listp (cdr x)))))

 (local
  (defthm position-equal-ac-upper-bound
    (implies (position-equal-ac c lst n)
             (< (position-equal-ac c lst n)
                (+ (len lst) n)))
    :rule-classes :linear))

 (local
  (defthm len-nthcdr
    (implies (and (natp n)
                  (true-listp x))
             (equal (len (nthcdr n x))
                    (if (<= n (len x))
                        (- (len x) n)
                      0)))))

 (defun escape-char (c replacement name)
   (declare (xargs :guard (and (characterp c)
                               (stringp replacement)
                               (stringp name))))
   (let ((pos (position c name)))
     (cond ((not (mbt (stringp name)))
            "")
           ((null pos)
            name)
           (t
            (concatenate 'string
                         (subseq name 0 pos)
                         replacement
                         (escape-char c
                                      replacement
                                      (subseq name (1+ pos) nil))))))))

(defun rendered-name-acl2-doc (name)
  (declare (xargs :guard (stringp name)))
  (substitute?
   #\_ #\Space
   (substitute?
    #\{ #\(
    (substitute?
     #\} #\)
     (substitute?
      #\{ #\[
      (substitute?
       #\} #\]
       (escape-char
        #\' "<<quote>>"
        (escape-char
         #\` "<<backquote>>"
         (escape-char
          #\, "<<comma>>"
          name)))))))))

(defattach rendered-name rendered-name-acl2-doc)

(include-book "std/util/defconsts" :dir :system)
(set-state-ok t)
(program)

(include-book "acl2-doc-wrap")

(defun rendered-symbol (sym)
  (intern-in-package-of-symbol
   (str::upcase-string (rendered-name (symbol-name sym)))
   sym))

(defun rendered-symbol-lst (symlist)
  (cond ((endp symlist) nil)
        (t (cons (rendered-symbol (car symlist))
                 (rendered-symbol-lst (cdr symlist))))))

(defun render-topic (x all-topics topics-fal state)
  ;; Adapted from display-topic
  (b* ((name (cdr (assoc :name x)))
       (parents (cdr (assoc :parents x)))
       (from (cdr (assoc :from x)))
       ((mv text state) (preprocess-topic
                         (acons :parents nil x) ;; horrible hack
                         all-topics topics-fal
                         t ;; disable autolinking to avoid auto links in text mode
                         state))
       ((mv err tokens) (parse-xml text))
       ((mv tokens state)
        (if (not err)
            (mv tokens state)
          (b* ((- (cw "Error rendering xdoc topic ~x0:~%~%" name))
               (state (princ$ err *standard-co* state))
               (state (newline *standard-co* state))
               (state (newline *standard-co* state))
               ((mv & tokens) (parse-xml "Error rendering topic")))
            (mv tokens state))))
       ((mv err topic-to-rendered-table state)
        (topic-to-rendered-table-init state))
       ((when err) ; impossible?
        (mv (er hard 'render-topic
                "Unexpected implementation error!")
            state))
       (merged-tokens
        (reverse (merge-text tokens nil 0 nil
                             topic-to-rendered-table
                             (f-get-global 'xdoc-tag-elide-alist state))))
       (acc (tokens-to-terminal merged-tokens 70 nil nil nil))
       (terminal (str::trim (str::rchars-to-string acc))))

; Originally the first value returned was (cons name terminal).  But we prefer
; to avoid the "." in the output file, to make its viewing more pleasant.  If
; we decide to associate additional information with name, then we may have a
; more convincing reason to make this change.

    (mv (list* (rendered-symbol name)
               (rendered-symbol-lst parents)
               terminal
               (if (equal from "ACL2 Sources")

; We avoid storing the from field in this case, simply to avoid a bit of
; bloating in generated ACL2 source file doc.lisp.

                   nil
                 (list from)))
        state)))

(defun render-topics1 (x all-topics topics-fal state)
  (b* (((when (atom x))
        (mv nil state))
       ((mv first state) (render-topic (car x) all-topics topics-fal state))
       ((mv rest state) (render-topics1 (cdr x) all-topics topics-fal state)))
    (mv (cons first rest) state)))

(defun render-topics (x all-topics state)
  (b* ((prev-event-table-binding
        ;; save the previous binding (or lack) of xdoc-get-event-table, set it
        ;; to one generated from the current world, and restore at the end
        (and (acl2::f-boundp-global 'xdoc-get-event-table state)
             (list (f-get-global 'xdoc-get-event-table state))))
       (state (f-put-global 'xdoc-get-event-table (make-get-event*-table (w state) nil) state))
       (topics-fal (topics-fal all-topics))
       ((mv ans state) (render-topics1 x all-topics topics-fal state))
        (- (fast-alist-free (@ xdoc-get-event-table)))
        (state (if prev-event-table-binding
                   (f-put-global 'xdoc-get-event-table (car prev-event-table-binding) state)
                 (makunbound-global 'xdoc-get-event-table state))))
    (fast-alist-free topics-fal)
    (mv ans state)))

(defun set-current-package-state (pkg state)
  (mv-let (erp val state)
          (acl2::set-current-package pkg state)
          (declare (ignore val))
          (assert$ (null erp)
                   state)))

(defun split-acl2-topics (alist acl2-topics acl2-pc-topics other-topics)

; Added by Matt K.  It seems good to me for there to be an intuitive sense of
; the order of topics when one is searching using the Emacs interface to the
; documentation, specifically, the "," key.  So we put the "ACL2-PC" package
; topics at the end, since to me they seem less likely to be what one is
; searching for.

  (cond ((endp alist)
         (append (acl2::merge-sort-symbol-alistp acl2-topics)
                 (acl2::merge-sort-symbol-alistp acl2-pc-topics)
                 (acl2::merge-sort-symbol-alistp other-topics)))
        ((eq (intern (symbol-name (caar alist)) "ACL2")
             (caar alist))
         (split-acl2-topics (cdr alist)
                            (cons (car alist) acl2-topics)
                            acl2-pc-topics
                            other-topics))
        ((equal (symbol-package-name (caar alist)) "ACL2-PC")
         (split-acl2-topics (cdr alist)
                            acl2-topics
                            (cons (car alist) acl2-pc-topics)
                            other-topics))
        (t
         (split-acl2-topics (cdr alist)
                            acl2-topics
                            acl2-pc-topics
                            (cons (car alist) other-topics)))))
