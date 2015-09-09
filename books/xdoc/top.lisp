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


; top.lisp -- most end users should include this book directly.  If you are
; new to xdoc, you can try running:
;
;  (include-book "xdoc/top" :dir :system)
;  :xdoc xdoc

(in-package "XDOC")
(include-book "base")
(include-book "book-thms")

(defun bootstrap-revappend-chars-aux (x n xl y)
  (declare (xargs :mode :program)
           (type string x)
           (type (integer 0 *) n xl))
  (if (eql n xl)
      y
    (bootstrap-revappend-chars-aux x
                                   (the (integer 0 *)
                                        (+ 1 (the (integer 0 *) n)))
                                   xl
                                   (cons (char x n) y))))

(defun bootstrap-revappend-chars (x acc)
  ;; Same as str::revappend-chars, but minimize dependencies
  (declare (xargs :mode :program)
           (type string x))
  (bootstrap-revappend-chars-aux x 0 (length x) acc))

(defun bar-escape-chars (x)
  (declare (xargs :mode :program))
  (cond ((atom x)
         nil)
        ((eql (car x) #\|)
         (list* #\\ #\| (bar-escape-chars (cdr x))))
        (t
         (cons (car x) (bar-escape-chars (cdr x))))))

(defun bar-escape-string (x)
  (declare (xargs :mode :program)
           (type string x))
  ;; Dumb optimization: don't need to escape anything unless there's a #\|
  ;; somewhere.
  (if (position #\| x)
      (coerce (bar-escape-chars (coerce x 'list)) 'string)
    x))

(defun full-escape-symbol (x)
  (declare (xargs :mode :program))
  (concatenate 'string "|" (bar-escape-string (symbol-package-name x)) "|::|"
               (bar-escape-string (symbol-name x)) "|"))

(defun revappend-bar-escape-string (x n xl acc)
  (declare (xargs :mode :program)
           (type string x)
           (type unsigned-byte n xl))
  (if (eql n xl)
      acc
    (let* ((char (char x n))
           (acc  (if (eql char #\|)
                     (cons #\\ acc)
                   acc)))
      (revappend-bar-escape-string x (+ n 1) xl (cons char acc)))))

(defun revappend-full-escape-symbol (x acc)
  (declare (xargs :mode :program))
  (let* ((pkg  (symbol-package-name x))
         (name (symbol-name x))
         (acc  (cons #\| acc))
         (acc  (revappend-bar-escape-string pkg 0 (length pkg) acc))
         (acc  (list* #\| #\: #\: #\| acc))
         (acc  (revappend-bar-escape-string name 0 (length name) acc))
         (acc  (cons #\| acc)))
    acc))


(defun acl2::colon-xdoc-initialized (state)

; This interface function was added by Matt K. so that the proof-checker can
; determine if xdoc is ready to go.  If we only use the ld-keyword-aliases to
; determine that xdoc is available, then events will be submitted when xdoc is
; invoked from within the proof-checker (see colon-xdoc-init).  This would
; cause a weird complaint about make-event when exiting the proof-checker.

; In general, it seems best only to submit events at the top-level of the ACL2
; loop, so that ACL2 can handle them properly, for example laying down
; command-markers appropriately.  This interface function can be used by other
; applications (besides the proof-checker) in order to avoid calling xdoc when
; this would create events.

; This function is in the ACL2 package so that it can be run even when the
; "XDOC" package is not present.

  (declare (xargs :stobjs state :mode :program))
  (cdr (assoc 'colon-xdoc-support-loaded (table-alist 'xdoc (w state)))))

(defmacro colon-xdoc-init ()
  '(with-output :off (summary event observation)
     (make-event
      (if (not (acl2::colon-xdoc-initialized state))
        `(progn
           (include-book ;; newlines to fool dependency scanner
            "xdoc/defxdoc-raw" :dir :system :ttags :all)
           (include-book
            "xdoc/topics" :dir :system)
           (include-book
            "xdoc/display" :dir :system)
           (encapsulate ()
            (local (xdoc-quiet)) ;; Suppress warnings when just using :xdoc (or :doc)
            (local (set-inhibit-warnings "Documentation")))
           (table xdoc 'colon-xdoc-support-loaded t))
        '(value-triple :invisible)))))

(defmacro xdoc (name)
  (declare (xargs :guard (or (symbolp name)
                             (and (quotep name)
                                  (symbolp (unquote name))))))
  (let ((name (if (symbolp name)
                  name
                (unquote name))))
    `(with-output :off (summary event)
       (progn
         (colon-xdoc-init)
         (make-event
          (b* (((mv all-xdoc-topics state)
                (with-guard-checking t (all-xdoc-topics state)))
               ((mv & & state) (colon-xdoc-fn ',name all-xdoc-topics state)))
            (value '(value-triple :invisible))))))))

; Hijack ACL2's :doc keyword and replace it with :xdoc

(add-ld-keyword-alias! :doc '(1 xdoc))

(defun xdoc-extend-fn (name long world)
  (declare (xargs :mode :program))
  (let* ((all-topics   (xdoc::get-xdoc-table world))
         (old-topic    (xdoc::find-topic name all-topics))
         (long         (cond ((not long) "")
                             ((stringp long) long)
                             (t
                              (er hard? 'xdoc-extend "Can't extend ~x0 with non-string ~x1."
                                  name long)))))
    (cond ((not old-topic)
           (prog2$
            (er hard? 'xdoc-extend "Topic ~x0 wasn't found." name)
            all-topics))
          (t
           (let* ((other-topics (remove-equal old-topic all-topics))
                  (old-long     (or (cdr (assoc :long old-topic)) ""))
                  (new-long     (concatenate 'string old-long long))
                  (new-topic    (acons :long new-long (delete-assoc :long old-topic))))
             (cons new-topic other-topics))))))

(defmacro xdoc-extend (name long)
  `(table xdoc 'doc
          ;; Since we don't quote long, it can be something like (concatenate
          ;; 'string ...), and that's fine, it'll get evaluated here and
          ;; xdoc-extend will get the resulting string.
          (xdoc-extend-fn ',name ,long world)))

(defun xdoc-prepend-fn (name long world)
  (declare (xargs :mode :program))
  (let* ((all-topics   (xdoc::get-xdoc-table world))
         (old-topic    (xdoc::find-topic name all-topics))
         (long         (cond ((not long) "")
                             ((stringp long) long)
                             (t
                              (er hard? 'xdoc-extend "Can't prepend ~x0 with non-string ~x1."
                                  name long)))))
    (cond ((not old-topic)
           (er hard? 'xdoc-prepend "Topic ~x0 wasn't found." name))
          (t
           (let* ((other-topics (remove-equal old-topic all-topics))
                  (old-long     (or (cdr (assoc :long old-topic)) ""))
                  (new-long     (concatenate 'string long old-long))
                  (new-topic    (acons :long new-long (delete-assoc :long old-topic))))
             (cons new-topic other-topics))))))

(defmacro xdoc-prepend (name long)
  `(table xdoc 'doc
          (xdoc-prepend-fn ',name ,long world)))

(defun order-subtopics-fn (name order world)
  (declare (xargs :mode :program))
  (let* ((all-topics (xdoc::get-xdoc-table world))
         (old-topic  (xdoc::find-topic name all-topics)))
    (cond ((not old-topic)
           (er hard? 'order-subtopics "Topic ~x0 wasn't found." name))
          ((not (symbol-listp order))
           (er hard? 'order-subtopics "Subtopics are not a symbol list: ~x0" order))
          (t
           (let* ((other-topics (remove-equal old-topic all-topics))
                  (new-topic    (acons :suborder order
                                       (delete-assoc :suborder old-topic))))
             (cons new-topic other-topics))))))

(defmacro order-subtopics (name order)
  `(table xdoc 'doc
          (order-subtopics-fn ',name ',order world)))

(defund extract-keyword-from-args (kwd args)
  (declare (xargs :guard (keywordp kwd)))
  (cond ((atom args)
         nil)
        ((eq (car args) kwd)
         (if (consp (cdr args))
             (cons (car args)
                   (cadr args))
           (er hard? 'extract-keyword-from-args
               "Expected something to follow ~s0." kwd)))
        (t
         (extract-keyword-from-args kwd (cdr args)))))

(defund throw-away-keyword-parts (args)
  (declare (xargs :guard t))
  (cond ((atom args)
         nil)
        ((keywordp (car args))
         (throw-away-keyword-parts (if (consp (cdr args))
                                       (cddr args)
                                     (er hard? 'throw-away-keyword-parts
                                         "Expected something to follow ~s0."
                                         (car args)))))
        (t
         (cons (car args)
               (throw-away-keyword-parts (cdr args))))))

(defun formula-info-to-defs1 (entries acc)
  ;; See book-thms.lisp.  Entries should be the kind of structure that
  ;; new-formula-info produces.  We build a string that is mostly "@(def fn)"
  ;; entries.  We accumulate the characters of the string onto acc in reverse
  ;; order, as per usual for string-building functions.
  (declare (xargs :mode :program))
  (cond ((atom entries)
         acc)
        ((and (consp (car entries))
              (symbolp (caar entries)))
         ;; theorems, definitions, defchooses
         (let* ((acc (list* #\Space #\f #\e #\d #\( #\@ acc)) ;; "@(def "
                (acc (revappend-full-escape-symbol (caar entries) acc))
                (acc (list* #\Newline #\) acc)))
           (formula-info-to-defs1 (cdr entries) acc)))
        ((stringp (car entries))
         ;; xdoc fragments
         (let* ((acc (bootstrap-revappend-chars (car entries) acc)))
           (formula-info-to-defs1 (cdr entries) acc)))
        (t
         (formula-info-to-defs1 (cdr entries) acc))))

(defun formula-info-to-defs (headerp entries acc)
  (declare (xargs :mode :program))
  (let* ((original acc)
         (acc (if headerp
                  (bootstrap-revappend-chars "<h3>Definitions and Theorems</h3>" acc)
                acc))
         (before-entries acc)
         (acc (formula-info-to-defs1 entries acc)))
    (if (equal acc before-entries)
        ;; Avoid adding empty "Definitions and Theorems" sections.
        original
      acc)))

(defun defsection-autodoc-fn (name parents short long extension marker state)
  (declare (xargs :mode :program :stobjs state))
  (let* ((wrld      (w state))
         (trips     (acl2::reversed-world-since-event wrld marker nil))
         (info      (reverse (acl2::new-formula-info trips wrld nil)))
         (acc       nil)
         (acc       (if long
                        (bootstrap-revappend-chars long acc)
                      acc))
         (acc       (list* #\Newline #\Newline acc))
         (acc       (formula-info-to-defs (not extension) info acc))
         (long      (reverse (the string (coerce acc 'string)))))
    (if extension
        `(xdoc-extend ,extension ,long)
      `(defxdoc ,name
         :parents ,parents
         :short ,short
         :long ,long))))

(defun make-xdoc-fragments (args) ;; args to a defsection
  (cond ((atom args)
         nil)
        ((stringp (car args))
         (cons `(acl2::acl2-xdoc-fragment ,(car args))
               (make-xdoc-fragments (cdr args))))
        (t
         (cons (car args)
               (make-xdoc-fragments (cdr args))))))

(defun defsection-fn (wrapper ; (encapsulate nil) or (progn)
                      name args)
  (declare (xargs :mode :program))
  (let* ((parents     (cdr (extract-keyword-from-args :parents args)))
         (short       (cdr (extract-keyword-from-args :short args)))
         (long        (cdr (extract-keyword-from-args :long args)))
         (extension   (cdr (extract-keyword-from-args :extension args)))
         (extension
          (cond ((symbolp extension) extension)
                ((and (consp extension)
                      (atom (cdr extension))
                      (symbolp (car extension)))
                 ;; DWIM feature -- previously you had to write :extension foo.
                 ;; I always screwed this up because I was used to writing, e.g.,
                 ;; :parents (foo).  So now we allow :extension (foo) as well.
                 (car extension))
                (t
                 (er hard? 'defsection "In section ~x0, invalid :extension: ~x1."
                     name extension))))
         (defxdoc-p   (and (not extension)
                           (or parents short long)))
         (autodoc-arg (extract-keyword-from-args :autodoc args))
         (autodoc-p   (and (or defxdoc-p extension)
                           (or (not autodoc-arg)
                               (cdr autodoc-arg))))
         (new-args (make-xdoc-fragments (throw-away-keyword-parts args))))
    (cond ((or (not name)
               (not (symbolp name)))
           (er hard? 'defsection "Section name must be a non-nil symbol; found
                                  ~x0." name))
          ((and extension
                (or parents short))
           (er hard? 'defsection "In section ~x0, you are using :extension, ~
                                  so :parents and :short are not allowed." name))
          ((not autodoc-p)
           `(with-output
              :stack :push
              :off :all
              :on error  ;; leave errors on, or you can think forms succeeded when they didn't.
              (progn
                ,@(and defxdoc-p
                       `((defxdoc ,name
                           :parents ,parents
                           :short ,short
                           :long ,long)))
                (with-output :stack :pop
                  (,@wrapper
                   ;; A silly value-triple so that an empty defsection is okay.
                   (value-triple :invisible)
                   . ,new-args))
                ,@(and extension
                       `(xdoc-extend ,extension ,long)))))
          (t
           ;; Fancy autodoc stuff.
           (let ((marker `(table acl2::intro-table :mark ',name)))
             `(with-output
                :stack :push
                :off :all
                :on error
                (progn
                  ;; We originally just put down a single marker here, but that
                  ;; led to problems when there were multiple extensions of the
                  ;; same topic -- the table event for the second extension was
                  ;; redundant(!) and that led to slurping in all the events
                  ;; not just in the second extension, but all the way back to
                  ;; the start of the first extension.  To avoid this redundancy,
                  ;; be sure to set the marker to nil before installing the real
                  ;; marker.
                  (table acl2::intro-table :mark nil)
                  ,marker

                  (with-output :stack :pop
                    (,@wrapper
                     ;; A silly value-triple so that an empty defsection is okay.
                     (value-triple :invisible)
                     . ,new-args))
                  (make-event
                   (defsection-autodoc-fn ',name ',parents ,short ,long ',extension ',marker state))
                  (value-triple ',name))))))))

(defmacro defsection (name &rest args)
  (declare (xargs :guard (symbolp name)))
  (defsection-fn '(encapsulate nil) name args))

(defmacro defsection-progn (name &rest args)
  (declare (xargs :guard (symbolp name)))
  (defsection-fn '(progn) name args))



;; Moved from cutil/deflist for greater availability
(defsection mksym

  (defun concatenate-symbol-names (x)
    (declare (xargs :guard (symbol-listp x)))
    (if (consp x)
        (acl2::concatenate 'string
                           (symbol-name (car x))
                           (concatenate-symbol-names (cdr x)))
      ""))

  (defmacro mksym (&rest args)
    `(intern-in-package-of-symbol
      (concatenate-symbol-names (list ,@args))
      mksym-package-symbol)))

; Moved from acl2-doc.lisp to make it more widely available
(defmacro defpointer (from to &optional keyword-p)
  `(defxdoc ,from
     :parents (pointers)
     :short ,(concatenate 'string
                          "See @(see "
                          (acl2::string-downcase (symbol-name to))
                          ")"
                          (if keyword-p
                              (concatenate 'string
                                           " for keyword @(':"
                                           (acl2::string-downcase (symbol-name from))
                                           "').")
                            "."))))


(defun add-resource-directory-fn (dirname fullpath world)
  (declare (xargs :guard (and (stringp dirname)
                              (stringp fullpath))
                  :mode :program))
  (let* ((resource-dirs (cdr (assoc-eq 'resource-dirs (table-alist 'xdoc world))))
         (look          (cdr (assoc-equal dirname resource-dirs))))
    (if look
        (if (equal look fullpath)
            ;; Already have it, no need to extend the alist.
            resource-dirs
          (er hard? 'add-resource-directory
              "Conflicting paths for resource directory ~x0.~%  ~
                 - Previous path: ~x1.~%  ~
                 - New path: ~x2."
              dirname look fullpath))
      (cons (cons dirname fullpath)
            resource-dirs))))

(defmacro add-resource-directory (dirname path)
  `(make-event
    (let ((dirname  ,dirname)
          (fullpath (acl2::extend-pathname (cbd) ,path state)))
      (value `(table xdoc 'resource-dirs
                     (add-resource-directory-fn ,dirname ,fullpath world))))))

