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


; preprocess.lisp  -- the xdoc preprocessor

(in-package "XDOC")
(include-book "autolink")
(include-book "std/strings/defs-program" :dir :system)
(include-book "std/io/read-string" :dir :system)
(include-book "unsound-eval")
(include-book "verbosep")
(include-book "xdoc-error")
(local (include-book "std/testing/assert-bang" :dir :system))
(set-state-ok t)
(program)

; ----------------- World Lookup Stuff --------------------------

(defun get-formals (fn context world)
  (b* ((formals (getprop fn 'formals :bad 'current-acl2-world world))
       ((unless (eq formals :bad))
        formals)
       (macro-args (getprop fn 'macro-args :bad 'current-acl2-world world))
       ((unless (eq macro-args :bad))
        macro-args))
    (and (xdoc-verbose-p)
         (xdoc-error "get-formals failed for ~x1." context fn))
    (str::cat "Error getting formals for "
              (symbol-package-name fn)
              "::"
              (symbol-name fn))))

(defun get-measure (fn context world)
  (b* ((just (getprop fn 'justification nil 'current-acl2-world world))
       ((when just)
        (access justification just :measure)))
    (and (xdoc-verbose-p)
         (xdoc-error "get-measure failed for ~x1." context fn))
    (str::cat "Error getting measure for "
              (symbol-package-name fn)
              "::"
              (symbol-name fn))))

(defun get-guard (fn context world)
  (b* ((formals (getprop fn 'formals :bad 'current-acl2-world world))
       ((unless (eq formals :bad))
        (getprop fn 'guard nil 'current-acl2-world world)))
    (and (xdoc-verbose-p)
         (xdoc-error "get-guard failed for ~x1." context fn))
    (str::cat "Error getting guard for "
              (symbol-package-name fn)
              "::"
              (symbol-name fn))))

(defun get-body (fn context world)
  ;; This gets the original body normalized or non-normalized body based on
  ;; what the user typed for the :normalize xarg.  The use of "last" skips past
  ;; any other :definition rules that have been added since then.
  (b* ((bodies (getprop fn 'def-bodies nil 'current-acl2-world world))
       ((when bodies)
        (access def-body (car (last bodies)) :concl)))
    (and (xdoc-verbose-p)
         (xdoc-error "get-body failed for ~x1." context fn))
    (str::cat "Error getting body for "
              (symbol-package-name fn)
              "::"
              (symbol-name fn))))


(defun eat-things-from-event (keys event)
  ;; EVENT might be something like (DEFTHM FOO :HINTS ... :RULE-CLASSES ...)
  ;; KEYS is a list of things we want to remove, e.g., it might contain HINTS.
  ;; We look for members of keys and eat them and their associated values.
  (cond ((atom event)
         event)
        ((atom (cdr event))
         event)
        ((member (car event) keys)
         (eat-things-from-event keys (cddr event)))
        (t
         (cons (car event) (eat-things-from-event keys (cdr event))))))

(defun clean-up-xargs (xargs)
  ;; Xargs is like (xargs :guard t :verify-guards nil ...) from a function declaration
  ;; I leave in :guard, :stobjs, and :non-executable since those are possibly of interest...
  (eat-things-from-event '(:guard-hints :guard-debug :hints :measure :ruler-extenders :mode
                                        :normalize :otf-flg :verify-guards :well-founded-relation)
                         xargs))

(defun clean-up-function-decl-item (item)
  ;; Item is like (xargs ...) or (integer foo) or whatever; it's something that occurs
  ;; in a declaration.  I'll leave in type declarations.
  (cond ((and (consp item)
              (eq (car item) 'xargs))
         (let ((clean-xargs (clean-up-xargs (cdr item))))
           (if clean-xargs
               (cons 'xargs clean-xargs)
             nil)))
        (t
         item)))

(defun clean-up-function-decl-items (items)
  (if (consp items)
      (let ((clean1 (clean-up-function-decl-item (car items)))
            (rest   (clean-up-function-decl-items (cdr items))))
        (if clean1
            (cons clean1 rest)
          rest))
    items))

(defun clean-up-function-decl (decl)
  ;; DECL is like (declare (xargs ...) (type string ...)) etc.
  (cond ((and (consp decl)
              (eq (car decl) 'declare))
         (let ((items (clean-up-function-decl-items (cdr decl))))
           (if items
               (cons 'declare items)
             nil)))
        ((stringp decl)
         ;; drop doc-strings, but leave other string documentation
         (if (str::istrprefixp ":doc-section" decl)
             nil
           decl))
        (t
         decl)))

(defun clean-up-function-decls (decls)
  (if (consp decls)
      (let ((clean1 (clean-up-function-decl (car decls)))
            (rest   (clean-up-function-decls (cdr decls))))
        (if clean1
            (cons clean1 rest)
          rest))
    decls))

(defun find-event-in-mutual-recursion (name defuns)
  (cond ((atom defuns)
         nil)
        ((eq name (second (car defuns)))
         (car defuns))
        (t
         (find-event-in-mutual-recursion name (cdr defuns)))))

(defun clean-up-defun (event)
  (let ((name    (second event))
        (formals (third event))
        (decls   (clean-up-function-decls (butlast (cdddr event) 1)))
        (body    (car (last event))))
    (if decls
        (append (list 'defun name formals)
                decls
                (list body))
      (list 'defun name formals body))))

(defun clean-up-event (name event)
  (if (atom event)
      event
    (case (car event)
      (defthm
        ;; I'll leave in the rule-classes, since they're probably important.
        (eat-things-from-event '(:hints :instructions :doc :otf-flg) event))
      (defun
        (clean-up-defun event))
      (defmacro
        (let ((name    (second event))
              (formals (third event))
              (decls   (clean-up-function-decls (butlast (cdddr event) 1)))
              (body    (car (last event))))
          (if decls
              (append (list 'defmacro name formals) decls (list body))
            (list 'defmacro name formals body))))
      (mutual-recursion
       ;; horrible
       (let ((defun (find-event-in-mutual-recursion name (cdr event))))
         (if defun
             (clean-up-defun defun)
           (er hard? 'clean-up-event
               "Expected to find ~x0 in mutual-recursion, but failed: ~x1"
               name event))))
      (otherwise
       event))))


;; (defun get-event-types (wrld acc)
;;   (declare (xargs :mode :program))
;;   (b* ((wrld (acl2::scan-to-event wrld))
;;        ((when (atom wrld)) acc)
;;        (form (acl2::access-event-tuple-form (cddr (car wrld))))
;;        (kind (and (consp form) (car form))))
;;     (get-event-types (cdr wrld)
;;                      (if kind (cons kind acc) acc))))


(defun hons-acons-list-unique (keys val acc)
  (if (atom keys)
      acc
    (hons-acons-list-unique (cdr keys) val
                            (if (hons-get (car keys) acc)
                                acc
                              (hons-acons (car keys) val acc)))))

(defun make-get-event*-table (wrld acc)
  (b* ((wrld (acl2::scan-to-event wrld))
       ((when (atom wrld)) acc)
       (event (cddr (car wrld)))
       (form (acl2::access-event-tuple-form event))
       (kind (and (consp form) (car form)))
       (namex (acl2::access-event-tuple-namex event))
       (acc (cond ((member-eq kind
                              '(acl2::verify-termination
                                acl2::verify-termination-boot-strap
                                acl2::verify-guards))
                   acc)
                  ((not namex) acc)
                  ((symbolp namex)
                   (if (hons-get namex acc)
                       acc
                     (hons-acons namex form acc)))
                  ((symbol-listp namex) (hons-acons-list-unique namex form acc))
                  (t acc))))
    (make-get-event*-table (cdr wrld) acc)))

#!ACL2
(defun xdoc::get-event* (name wrld)
  ;; Historically XDOC used ACL2::GET-EVENT, but we found that this was
  ;; sometimes returning "bad" events like VERIFY-TERMINATION and
  ;; VERIFY-TERMINATION-BOOT-STRAP instead of function definitions.  Matt
  ;; Kaufmann developed this modification of ACL2::GET-EVENT to avoid these
  ;; cases.
  (let* ((wrld1 (lookup-world-index 'event
                                    (getprop name 'absolute-event-number 0
                                             'current-acl2-world wrld)
                                    wrld))
         (ev (access-event-tuple-form (cddr (car wrld1)))))
    (cond ((null ev) nil)
          ((and (consp ev)
                (member-eq (car ev)
                           '(verify-termination
                             verify-termination-boot-strap
                             verify-guards)))
           (xdoc::get-event* name (scan-to-event (cdr wrld1))))
          (t ev))))

(defun get-event-aux (name context world table)
  ;; A general purpose event lookup as in :pe
  ;; Table must be either something produced by make-get-event*-table (on the current world) or 0.
  (b* ((props (acl2::getprops name 'current-acl2-world world))
       (evt   (and props (if (eql table 0)
                             (get-event* name world)
                           (cdr (hons-get name table)))))
       ((when evt)
        evt))
    (and (xdoc-verbose-p)
         (xdoc-error "get-event failed for ~x1." context name))
    (str::cat "Error getting event for "
              (symbol-package-name name)
              "::"
              (symbol-name name))))

(defun get-event (name context state)
  (declare (xargs :stobjs state))
  (clean-up-event name (get-event-aux name context
                                      (w state)
                                      (if (boundp-global 'xdoc-get-event-table state)
                                          (f-get-global 'xdoc-get-event-table state)
                                        0))))

(defun start-event (event acc)
  (b* ((acc (str::printtree-rconcat "<b>" acc))
       (acc (str::printtree-rconcat (case (and (consp event)
                                             (car event))
                                    (defun     "Function: ")
                                    (defthm    "Theorem: ")
                                    (defmacro  "Macro: ")
                                    ;; not defstobj because it gets used for the
                                    ;; stobjs and accessors...
                                    (otherwise "Definition: "))
                                  acc))
       (acc (str::printtree-rconcat "</b>" acc)))
    acc))


#||

(get-event-aux 'append 'test (w state) 0)
(get-event 'append 'test state)

(get-event-aux 'binary-append 'test (w state) 0)
(get-event 'binary-append 'test state)

(get-event-aux 'write-byte$ 'test (w state) 0)
(get-event 'write-byte$ 'test state)

(defun UGLY (X)
  (DECLARE
   (XARGS :GUARD T
          :GUARD-HINTS (("Goal" :USE ((:INSTANCE DEFAULT-CAR))))
          :VERIFY-GUARDS NIL))
  (IF (CONSP X) (UGLY (CDR X)) 0))

(get-event-aux 'ugly 'test (w state) 0)
(get-event 'ugly 'test state)

(xml-ppr-obj (get-event 'ugly 'test state)
             :topics-fal (make-fast-alist '((acl2::consp . t)
                                            (acl2::defun . t)
                                            (acl2::declare . t)
                                            (acl2::xargs . t)
                                            (xdoc::ugly . t)
                                            (acl2::cdr . t)))
             :base-pkg 'xdoc::foo)

||#


#||
;; test get-event* table mode:
(make-event `(defconst *table* ',(make-get-event*-table (w state) nil)))

(defun check-get-event*-table (table wrld)
  (if (atom table)
      nil
    (b* ((spec (get-event* (caar table) wrld)))
      (if (equal spec (cdar table))
          (check-get-event*-table (cdr table) wrld)
        (list (caar table) (cdar table) spec)))))

(assert! (equal (check-get-event*-table *table* (w state)) nil))

||#



#||

(defmacro foo ()
  `(progn (logic)
          (make-event
           '(encapsulate
              (((h *) => *))
              (local (defun h (x) (+ x 1)))
              (defun f (x) (+ x 1))
              (defun g (x) (+ x 2))))))

(defstobj st fld)

(defun-sk all-integerp (x)
  (forall a (implies (member-equal a x)
                     (integerp a))))

(defconst *const* 3)

(foo)

(get-event 'undefined 'test state) ; good, fails
(get-event 'append 'test state)
(get-event 'binary-append 'test state)
(get-event 'st 'test state)
(get-event 'fld 'test state) ;; bad? returns the whole stobj
(get-event 'all-integerp 'test state)
(get-event 'all-integerp-witness 'test state) ;; good i guess - returns the encapsulate
(get-event 'f 'test state)
(get-event 'h 'test state) ;; good i guess, returns the encapsulate
(get-event 'acl2::car-cons 'test state)
(get-event '*const* 'test state)

(get-formals 'binary-append (w state))  ;; --> (ACL2::X ACL2::Y)
(get-formals 'append (w state)) ;; --> (ACL2::X ACL2::Y &REST ACL2::RST)
(get-formals 'all-integerp-witness (w state)) ;; good, works
(get-formals 'all-integerp (w state)) ;; good, works
(get-formals 'fld (w state)) ;; good, works
(get-formals 'st (w state)) ;; good, fails

(get-measure 'binary-append (w state)) ;; good, works
(get-measure 'append (w state))  ;; good, fails
(get-measure 'st (w state)) ;; good, fails
(get-measure 'fld (w state)) ;; good, fails
(get-measure 'all-integerp-witness (w state)) ;; good, fails
(get-measure 'all-integerp (w state)) ;; good, fails

(get-guard 'binary-append (w state)) ;; good, works
(get-guard 'append (w state)) ;; hrmn -- fails?
(get-guard 'all-integerp-witness (w state)) ;; NIL???
(get-guard 'all-integerp (w state)) ;; NIL???
(get-guard 'fld (w state)) ;; works
(get-guard 'st (w state)) ;; good, fails

||#


; -------------- Preprocessor Command Parsing  ------------------


; Convention: X is a string we are traversing, N is our current position in the
; string, and XL is the length of the string.  See autolink.lisp.

;; these appear not to be used
;; (defun read-literal (x n xl chars) ;; ==> (MV SUCCESSP N-PRIME)
;;   ;; Try to read CHARS, verbatim.
;;   (declare (type string x))
;;   (cond ((eql n xl)
;;          (mv (atom chars) n))
;;         ((consp chars)
;;          (if (eql (char x n) (car chars))
;;              (read-literal x (+ n 1) xl (cdr chars))
;;            (mv nil n)))
;;         (t
;;          (mv t n))))

;; (defun read-through-some-char-aux (x n xl chars acc) ;; ==> (MV SUCCESSP STRING N-PRIME)
;;   (declare (type string x))
;;   (b* (((when (eql xl n))
;;         (mv nil (str::rchars-to-string acc) n))
;;        (charN (char x n))
;;        ((when (member charN chars))
;;         (mv t (str::rchars-to-string (cons charN acc)) n)))
;;     (read-through-some-char-aux x (+ 1 n) xl chars (cons charN acc))))

;; (defun read-through-some-char (x n xl chars)
;;   ;; Try to read until one of CHARS is found
;;   (declare (type string x))
;;   (read-through-some-char-aux x n xl chars nil))


; Basic preprocessor directives:

(defun parse-directive (x n xl base-pkg kpa) ;; ==> (MV ERROR COMMAND ARG ARG-RAW N-PRIME)
  ;; Every basic directive has the form @(command arg)
  ;; Where command and arg are symbols.
  ;; We assume @( has just been read, and N is now pointing right after the open paren.
  ;; We try to read the command and arg.
  ;; Historically, on success, we returned the ARG as a symbol alone.
  ;; Now, to support fancier @(see Foo) capitalization preservation, we need to also
  ;; return the raw argument.
  (declare (type string x))
  (b* ((n                    (skip-past-ws x n xl))
       ;; We want to get nice error messages here, because if there'a a directive we
       ;; really do expect it to be a valid symbol.
       ((mv error command n) (parse-symbol x n xl (pkg-witness "XDOC") kpa t))
       ((when error)
        (mv error nil nil nil n))
       (n                    (skip-past-ws x n xl))
       (arg-start-n          n)
       ((mv error arg n)     (parse-symbol x n xl base-pkg kpa t)))
      (cond
       ;; Some error parsing arg.  Add a little more context.
       (error (mv (str::cat "In " (symbol-name command) " directive: " error)
                  nil nil nil n))

       ;; Ends with ), good.
       ((and (< n xl)
             (eql (char x n) #\)))
        (mv nil command arg (subseq x arg-start-n n) (+ n 1)))

       (t
        (mv (str::cat "In " (symbol-name command) " directive, expected ) after "
                      (symbol-name arg) ". Near " (error-context x n xl) ".")
            nil nil nil n)))))

#||
(let ((x "body Foo)"))
  (parse-directive x 0 (length x) 'acl2::foo (known-package-alist state)))

(let ((x "body foo) bar"))
  (parse-directive x 0 (length x) 'acl2::foo (known-package-alist state)))

(let ((x "body xdoc::foo) bar"))
  (parse-directive x 0 (length x) 'acl2::foo (known-package-alist state)))

(let ((x "xdoc::body xdoc::foo) bar"))
  (parse-directive x 0 (length x) 'acl2::foo (known-package-alist state)))

(let ((x "acl2::body xdoc::foo) bar"))
  (parse-directive x 0 (length x) 'acl2::foo (known-package-alist state)))

(let ((x "acl2::body)xdoc::foo) bar"))
  (parse-directive x 0 (length x) 'acl2::foo (known-package-alist state)))
||#


; -------------- Preproc-Data ----------------------------

; Read-only data passed around while preprocessing is kept in the preproc-data
; alist, the keys of which are:
;   :context -- for errors, usually the name of the topic we're processing
;   :topics-fal -- for autolinking, ignored if disable-autolinking-p or archive-p is set
;   :disable-autolinking-p -- disable autolinking, ignored if archive-p is set
;   :archive-p  -- archive support, leave everything that should be autolinked
;                  in preprocessor constructs so that they'll later be autolinked.
;                  See note on Archive Mode below.
;   :base-pkg   -- base package for the topic
;   :kpa        -- current known package alist.

(acl2::def-b*-binder preproc-data
  :body
  (std::da-patbind-fn 'preproc-data
                      '((context               . (lambda (x) (cdr (assoc :context               x))))
                        (topics-fal            . (lambda (x) (cdr (assoc :topics-fal            x))))
                        (disable-autolinking-p . (lambda (x) (cdr (assoc :disable-autolinking-p x))))
                        (archive-p             . (lambda (x) (cdr (assoc :archive-p             x))))
                        (base-pkg              . (lambda (x) (cdr (assoc :base-pkg              x))))
                        (kpa                   . (lambda (x) (cdr (assoc :kpa                   x)))))
                      acl2::args acl2::forms acl2::rest-expr))

; ---------------- Archive Mode ----------------------------

; Archive mode is enabled by setting the :archive-p key in preproc-data.  This
; mode doesn't fully preprocess the string -- in particular, it avoids doing
; anything that would require a complete topics-fal for autolinking.  Instead,
; it expands all constructs that refer to definitions from the world --
; @(def/formals/thm ...) etc, as well as @(`...`) evaluation.  Instead of
; autolinking the results from these and placing them in <code> or <v> blocks,
; in archive mode we replace them with @({...}) and @('...') blocks so they can
; be autolinked by a later, non-archive-mode preprocessing pass.

; Should archive-mode preprocess things that neither require autolinking nor
; examining the world?  One consideration is that we need to support a
; subsequent preprocessing pass, so we can't remove escapes such as replacing
; @@ with @.  For now we choose not to preprocess math mode blocks, but we do
; process simple directives like @(sym, @(url, and @(see (but not @(see?,
; because that looks at the topics-fal).  Rather an arbitrary choice.

; -------------- Escaping End Delimiters for @('...') and @({...}) -----

; Historical note:
; Previously there was no way to escape end delimiters for these two constructs.
; We added this while adding support for archiving because we came across something like this:
;  a topic contained "@(def foo)"
; foo's definition contained the object:
;   (bar #\})
; we translated @(def foo) to @({ ... (bar #\}) ... })
; which produced errors, because we though the @({ construct ended after "bar #\".

; So now we allow escaping these: in particular, inside a @({ }) block, any
; substring consisting of (close brace, one or more backslashes, close paren)
; will have one backslash removed.  Similarly for @('...'), any substring
; (single-quote, one or more backslashes, close paren) will also have one
; backslash removed.  Conversely, when we render an object into a @('...') or
; @({...}) form, any substring consisting of (delimiter, zero or more
; backslashes, close paren) will have one backslash added after the delimiter.

(defun zero-or-more-backslashes-followed-by-close-paren-p (x n xl)
  (declare (type string x)
           (type (integer 0 *) n)
           (type (integer 0 *) xl))
  (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
                   :exec (eql n xl)))
        nil)
       (char (char x n))
       ((when (eql char #\))) t)
       ((when (eql char #\\))
        (zero-or-more-backslashes-followed-by-close-paren-p x (+ 1 n) xl)))
    nil))

(defun revappend-chars-escaping-end-delim-aux (x n xl delim-char acc)
  (declare (type string x)
           (type (integer 0 *) n)
           (type (integer 0 *) xl)
           (type character delim-char))
  (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
              :exec (eql n xl)))
        acc)
       (char (char x n))
       ((when (and (eql char delim-char)
                   (zero-or-more-backslashes-followed-by-close-paren-p
                    x (+ 1 n) xl)))
        (revappend-chars-escaping-end-delim-aux
         x (+ 1 n) xl delim-char
         (cons #\\ (cons char acc)))))
    (revappend-chars-escaping-end-delim-aux
     x (+ 1 n) xl delim-char (cons char acc))))

(defun revappend-chars-escaping-end-delim (x delim-char acc)
  (revappend-chars-escaping-end-delim-aux x 0 (length x) delim-char acc))

(defun escape-end-delim (x delim-char)
  (str::rchars-to-string (revappend-chars-escaping-end-delim x delim-char nil)))


(defun revappend-chars-unescaping-end-delim-aux (x n xl delim-char acc)
  (declare (type string x)
           (type (integer 0 *) n)
           (type (integer 0 *) xl)
           (type character delim-char))
  (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
              :exec (eql n xl)))
        acc)
       (char (char x n))
       ((when (and (< (+ 1 n) xl)
                   (eql char delim-char)
                   (eql (char x (+ 1 n)) #\\)
                   (zero-or-more-backslashes-followed-by-close-paren-p
                    x (+ 2 n) xl)))
        (revappend-chars-unescaping-end-delim-aux
         x (+ 2 n) xl delim-char
         (cons char acc))))
    (revappend-chars-unescaping-end-delim-aux
     x (+ 1 n) xl delim-char (cons char acc))))

(defun revappend-chars-unescaping-end-delim (x delim-char acc)
  (revappend-chars-unescaping-end-delim-aux x 0 (length x) delim-char acc))

(defun unescape-end-delim (x delim-char)
  (str::rchars-to-string (revappend-chars-unescaping-end-delim x delim-char nil)))

#||
(unescape-end-delim "abc})def" #\})    --> abc})def
(unescape-end-delim "abc}\\)def" #\})  --> abc})def
(unescape-end-delim "abc}\\\\)def" #\})  --> abc}\\)def
(unescape-end-delim "abc}\\\\def" #\})  --> abc}\\\\def
(unescape-end-delim "abc\\\\)def" #\})  --> abc\\\\)def
(unescape-end-delim "abc})})def" #\})    --> abc})})def
(unescape-end-delim "abc}\\)}\\)def" #\})    --> abc})})def


(escape-end-delim "abc})def" #\})    --> abc}\\)def
(escape-end-delim "abc}\\)def" #\})  --> abc}\\\\)def
(escape-end-delim "abc}\\\\)def" #\})  --> abc}\\\\\\)def
(escape-end-delim "abc}\\\\def" #\})  --> abc}\\\\def
(escape-end-delim "abc\\\\)def" #\})  --> abc\\\\)def
(escape-end-delim "abc})})def" #\})    --> abc}\\)}\\)def
(escape-end-delim "abc}\\)}\\)def" #\})    --> abc}\\\\)}\\\\)def


||#


; -------------- Executing Directives ---------------------------

(defun process-url-directive (arg acc) ;; ===> ACC
  ;; @(url foo) just expands into the file name for foo.
  (file-name-mangle arg acc))

(defun process-sym-directive (arg preproc-data acc) ;; ===> ACC
  ;; @(sym foo) just expands into the standard name mangling for foo
  (b* (((preproc-data preproc-data)))
    (sym-mangle arg preproc-data.base-pkg preproc-data.archive-p acc)))

(defun process-sym-cap-directive (arg preproc-data acc) ;; ===> ACC
  ;; @(csym foo) just expands into the standard capitalized name mangling for foo
  (b* (((preproc-data preproc-data)))
    (sym-mangle-cap arg preproc-data.base-pkg preproc-data.archive-p acc)))

(defun want-to-preserve-case-p (arg arg-raw base-pkg)
  ;; Decide whether we want to preserve the case on a link like @(see Foo).
  ;;  - ARG is the true symbol we're trying to link to.
  ;;  - ARG-RAW is some string that the user typed to refer to ARG.
  ;;  - BASE-PKG is the package we're printing relative to.
  (and
   ;; The symbol being linked to must be in the same package, because otherwise
   ;; we're going to print a foo:: prefix and lowercasing everything seems
   ;; quite reasonable.
   (in-package-p arg base-pkg)
   ;; You had better not have typed any sort of :: stuff, because if you did,
   ;; then you wrote a link like @(see foo::Bar), and we are just going to
   ;; downcase you.
   (not (position #\: arg-raw))
   ;; You had better have at least one lowercase letter somewhere, because
   ;; otherwise it's likely that you're a macro that wrote @(see GUARD) and we
   ;; don't want to let you shout at us.
   (str::string-has-some-down-alpha-p arg-raw 0 (length arg-raw))
   ;; We'll require some upper case character too, because otherwise we may as
   ;; well use our default mechanism and capitalize, e.g., ACL2.
   (str::string-has-some-up-alpha-p arg-raw 0 (length arg-raw))
   ;; For good measure, let's make sure you are really naming our symbol.  This
   ;; should hopefully prevent any kind of mistakes from symbols with bars or
   ;; backslash escape characters.
   (str::istreqv arg-raw (symbol-name arg))))

(defun process-see-directive (arg arg-raw preproc-data acc) ;; ===> ACC
  ;; @(see foo) just expands into a link with a (usually) lowercase name, but we go to
  ;; some trouble to preserve case for things like @(see Guard).
  (b* (((preproc-data preproc-data))
       (acc (str::printtree-rconcat "<see topic=\"" acc))
       (acc (file-name-mangle arg acc))
       (acc (str::printtree-rconcat "\">" acc))
       (acc (if (want-to-preserve-case-p arg arg-raw preproc-data.base-pkg)
                ;; BOZO can this possibly be right?  What if arg-raw has '<' in it?
                ;; If this is a bug, fix the other see-like directives below, too.
                (str::printtree-rconcat (str::trim arg-raw) acc)
              (sym-mangle arg preproc-data.base-pkg preproc-data.archive-p acc)))
       (acc (str::printtree-rconcat "</see>" acc)))
    acc))

(defun process-see-cap-directive (arg preproc-data acc) ;; ===> ACC
  ;; @(csee foo) just expands into a link with a capitalized name.
  (b* (((preproc-data preproc-data))
       (acc (str::printtree-rconcat "<see topic=\"" acc))
       (acc (file-name-mangle arg acc))
       (acc (str::printtree-rconcat "\">" acc))
       (acc (sym-mangle-cap arg preproc-data.base-pkg preproc-data.archive-p acc))
       (acc (str::printtree-rconcat "</see>" acc)))
    acc))

(defun process-tsee-directive (arg arg-raw preproc-data acc) ;; ===> ACC
  ;; @(tsee foo) is basically <tt>@(see ...)</tt>.
  (b* ((acc (str::printtree-rconcat "<tt>" acc))
       (acc (process-see-directive arg arg-raw preproc-data acc))
       (acc (str::printtree-rconcat "</tt>" acc)))
    acc))

(defun process-see?-directive (arg arg-raw preproc-data acc) ;; ===> ACC
  ;; @(see? foo) is useful for macros like DEFLIST or DEFPROJECTION where you
  ;; are extending some function.  If FOO is the name of a documented topic,
  ;; then we insert a link to it just as in @(see foo).  But if FOO isn't
  ;; documented, we just turn it into a <tt>foo</tt> style thing.
  (b* (((preproc-data preproc-data))
       ((when preproc-data.archive-p)
        ;; Don't have the topics-fal yet so just preserve it as-is.
        (b* ((acc (str::printtree-rconcat "@(see? " acc))
             (acc (str::printtree-rconcat arg-raw acc))
             (acc (str::printtree-rconcat ")" acc)))
          acc))
       ((when (hons-get arg preproc-data.topics-fal))
        (process-see-directive arg arg-raw preproc-data acc))
       ;; Not documented, don't insert a link.
       (acc (str::printtree-rconcat "<tt>" acc))
       (acc (if (want-to-preserve-case-p arg arg-raw preproc-data.base-pkg)
                (str::printtree-rconcat (str::trim arg-raw) acc)
              (sym-mangle arg preproc-data.base-pkg preproc-data.archive-p acc)))
       (acc (str::printtree-rconcat "</tt>" acc)))
    acc))

(defun process-srclink-directive (arg acc) ;; ===> ACC
  (b* ((shortname (explode (str::downcase-string (symbol-name arg))))
       (acc (str::printtree-rconcat "<srclink>" acc))
       (acc (simple-html-encode-chars shortname acc))
       (acc (str::printtree-rconcat "</srclink>" acc)))
    acc))

(defun process-obj-to-code (obj preproc-data state acc)
  (b* (((preproc-data preproc-data))
       ((when preproc-data.archive-p)
        (b* ((acc  (str::printtree-rconcat "@({" acc))
             (acc  (revappend-chars-escaping-end-delim (fmt-to-str obj preproc-data.base-pkg) #\} acc))
             (acc  (str::printtree-rconcat "})" acc)))
          acc))
       (acc  (str::printtree-rconcat "<code>" acc))
       (acc  (xml-ppr-obj-aux obj (and (not preproc-data.disable-autolinking-p)
                                       preproc-data.topics-fal)
                              preproc-data.base-pkg state acc))
       (acc  (str::printtree-rconcat "</code>" acc)))
    acc))

(defun process-obj-to-verb (obj preproc-data state acc)
  (b* (((preproc-data preproc-data))
       ((when preproc-data.archive-p)
        (b* ((acc  (str::printtree-rconcat "@('" acc))
             (acc  (revappend-chars-escaping-end-delim (fmt-to-str obj preproc-data.base-pkg) #\' acc))
             (acc  (str::printtree-rconcat "')" acc)))
          acc))
       (acc  (str::printtree-rconcat "<v>" acc))
       (acc  (xml-ppr-obj-aux obj (and (not preproc-data.disable-autolinking-p)
                                       preproc-data.topics-fal)
                              preproc-data.base-pkg state acc))
       (acc  (str::printtree-rconcat "</v>" acc)))
    acc))

(defun process-body-directive (arg preproc-data state acc) ;; ===> ACC
  ;; @(body foo) -- look up the body and pretty-print it in a <code> block.
  (b* (((preproc-data preproc-data))
       (body (get-body arg preproc-data.context (w state))))
    (process-obj-to-code body preproc-data state acc)))

(defun process-def-directive (arg preproc-data state acc) ;; ===> ACC
  ;; @(def foo) -- look up the definition for foo, pretty-print it in a <code>
  ;; block, along with a source-code link.
  (b* (((preproc-data preproc-data))
       (def (get-event arg preproc-data.context state))
       (acc (str::printtree-rconcat "<p>" acc))
       (acc (start-event def acc))
       (acc (process-srclink-directive arg acc))
       (acc (str::printtree-rconcat "</p>" acc)))
    (process-obj-to-code def preproc-data state acc)))

(defun process-gdef-directive (arg preproc-data state acc) ;; ===> ACC
  ;; @(gdef foo) -- Look up the definition for foo, pretty-print it as in @def,
  ;; but don't use a source-code link because this is a "Generated Definition"
  ;; for which a tags-search will probably fail.
  (b* (((preproc-data preproc-data))
       (def (get-event arg preproc-data.context state))
       (acc (str::printtree-rconcat "<p>" acc))
       (acc (start-event def acc))
       (acc (sym-mangle arg preproc-data.base-pkg preproc-data.archive-p acc))
       (acc (str::printtree-rconcat "</p>" acc)))
    (process-obj-to-code def preproc-data state acc)))

(defun process-thm-directive (arg preproc-data state acc) ;; ===> ACC
  ;; @(thm foo) -- Look up the theorem named foo, and pretty-print its event
  ;; along with a source link.
  (b* (((preproc-data preproc-data))
       (def (get-event arg preproc-data.context state))
       (acc (str::printtree-rconcat "<p>" acc))
       (acc (start-event def acc))
       (acc (process-srclink-directive arg acc))
       (acc (str::printtree-rconcat "</p>" acc)))
    (process-obj-to-code def preproc-data state acc)))

(defun process-gthm-directive (arg preproc-data state acc) ;; ===> ACC
  ;; @(gthm foo) -- Like @(thm foo), but don't provide a source link since this
  ;; is a generated theorem.
  (b* (((preproc-data preproc-data))
       (def (get-event arg preproc-data.context state))
       (acc (str::printtree-rconcat "<p>" acc))
       (acc (start-event def acc))
       (acc (sym-mangle arg preproc-data.base-pkg preproc-data.archive-p acc))
       (acc (str::printtree-rconcat "</p>" acc)))
    (process-obj-to-code def preproc-data state acc)))

(defun process-formals-directive (arg preproc-data state acc) ;; ===> ACC
  ;; @(formals foo) -- just find the formals for foo and print them with;out
  ;; any extra formatting.
  (b* (((preproc-data preproc-data))
       (formals (get-formals arg preproc-data.context (w state)))
       (acc     (fmt-and-encode-to-acc formals preproc-data.base-pkg acc)))
    acc))

(defun process-call-directive (arg preproc-data state acc) ;; ===> ACC
  ;; @(call foo) -- find the formals to foo and insert <tt>(foo x y z)</tt>.
  (b* (((preproc-data preproc-data))
       (formals (get-formals arg preproc-data.context (w state)))
       (call    (cons arg formals))
       (acc     (str::printtree-rconcat "<tt>" acc))
       (acc     (fmt-and-encode-to-acc call preproc-data.base-pkg acc))
       (acc     (str::printtree-rconcat "</tt>" acc)))
    acc))

(defun process-ccall-directive (arg preproc-data state acc) ;; ===> ACC
  ;; @(ccall foo) -- "code call" is like @(call foo), but uses <code> instead
  ;; of <tt> tags.
  (b* (((preproc-data preproc-data))
       (formals (get-formals arg preproc-data.context (w state)))
       (call    (cons arg formals))
       (acc     (str::printtree-rconcat "<code>" acc))
       (acc     (fmt-and-encode-to-acc call preproc-data.base-pkg acc))
       (acc     (str::printtree-rconcat "</code>" acc)))
    acc))

(defun process-measure-directive (arg preproc-data state acc) ;; ===> ACC
  ;; @(measure foo) -- find the measure for foo and print it without any extra
  ;; formatting.
  (b* (((preproc-data preproc-data))
       (measure (get-measure arg preproc-data.context (w state)))
       (acc     (fmt-and-encode-to-acc measure preproc-data.base-pkg acc)))
    acc))


(defun process-directive (command arg arg-raw preproc-data state acc)
   "Returns (MV ACC STATE)"
   ;; Command and Arg are the already-parsed symbols we have read from the
   ;; documentation string.  Carry out whatever directive we've been asked to
   ;; do.  Acc is the accumulator for our output characters.
   (case command
     (def       (mv (process-def-directive arg preproc-data state acc)
                    state))
     (thm       (mv (process-thm-directive arg preproc-data state acc)
                    state))
     (srclink   (mv (process-srclink-directive arg acc)                               state))
     (gdef      (mv (process-gdef-directive arg preproc-data state acc)
                    state))
     (gthm      (mv (process-gthm-directive arg preproc-data state acc)
                    state))
     (body      (mv (process-body-directive arg preproc-data state acc)
                    state))
     (formals   (mv (process-formals-directive arg preproc-data state acc)                state))
     (measure   (mv (process-measure-directive arg preproc-data state acc)                state))
     (call      (mv (process-call-directive    arg preproc-data state acc)                state))
     (ccall     (mv (process-ccall-directive   arg preproc-data state acc)                state))
     (url       (mv (process-url-directive     arg acc)                               state))
     (see       (mv (process-see-directive     arg arg-raw preproc-data acc)              state))
     (csee      (mv (process-see-cap-directive arg preproc-data acc)                      state))
     (tsee      (mv (process-tsee-directive    arg arg-raw preproc-data acc)              state))
     (sym       (mv (process-sym-directive     arg preproc-data acc)                      state))
     (csym      (mv (process-sym-cap-directive arg preproc-data acc)                      state))
     (see?      (mv (process-see?-directive    arg arg-raw preproc-data acc)   state))
     (otherwise
      (b* (((preproc-data preproc-data)))
       (and (xdoc-verbose-p)
            (xdoc-error "unknown directive ~x1." preproc-data.context command))
       (let* ((acc (str::printtree-rconcat "[[ unknown directive " acc))
              (acc (str::printtree-rconcat (symbol-package-name command) acc))
              (acc (str::printtree-rconcat "::" acc))
              (acc (str::printtree-rconcat (symbol-name command) acc))
              (acc (str::printtree-rconcat "]]" acc)))
         (mv acc state))))))




; Ugly special hacks for some problems with <code> segments.
;
; As an example, consider:
;
;  |(defxdoc ...
;  |  :long "<p>blah blah blah</p>
;  |
;  |<p>blah blah blah</p>
;  |
;  |<code>
;  |(example-sexpr ...)
;  |</code>
;  |
;  |<p>blah blah blah</p>")
;
; The <code> block above causes problems for Emacs, because the algorithm for
; figuring out where an S-expression begins seems to basically look for an
; opening paren at the start of a line.  The result is that Emacs thinks the
; "(example-sexpr ...)" is the start of a form, rather than the "(defxdoc
; ...)," which can cause incorrect and irritating syntax highlighting, and can
; also cause problems for commands like "C-t e" that want to send a form to the
; *shell* buffer.  To cope with this, I typically indent <code> blocks with a
; single space, e.g.,
;
;  |<code>                   instead of    |<code>
;  | (example-sexpr ...)                   |(example-sexpr ...)
;  |</code>                                |</code>
;
; but, this convention isn't followed by the code blocks introduced with @(def
; ...)  and similar, and so the <code> blocks I write may not line up right
; with generated code blocks.
;
; To fix this, we look at the text between <code> and </code>, and if every
; line begins with a space, we eat those spaces.
;
; PATCH.  I eventually found that I wanted to be even more permissive than
; the above.  Sometimes when I write preprocessor things in @({...}) blocks,
; I find that I want to separate what I'm writing from the markup even more.
; That is, it's sort of easier to ignore the markup when I write:
;
;  |@({
;  |    this is some stuff
;  |})
;
; Than:
;
;  |@({
;  | this is some stuff
;  |})
;
; At any rate, it seems pretty reasonable to try to eat up any amount of spaces
; that are at the start of every line in the block.  So, now, instead of just
; eating one space, we eat however many spaces are shared by all lines.

(encapsulate
  ()
  (local (defthm first-n-ac-expand
           (implies (syntaxp (quotep i))
                    (equal (first-n-ac i l ac)
                           (cond ((zp i) (reverse ac))
                                 (t (first-n-ac (1- i)
                                                (cdr l)
                                                (cons (car l) ac))))))))

  (defun just-started-code-p (acc)
    (declare (xargs :guard (true-listp acc)))
    (mbe :logic (equal (take 6 acc)
                       (reverse (coerce "<code>" 'list)))
         :exec
         (and (consp (cdr (cdr (cdr (cdr (cdr acc))))))
              (eql (first acc) #\>)
              (eql (second acc) #\e)
              (eql (third acc) #\d)
              (eql (fourth acc) #\o)
              (eql (fifth acc) #\c)
              (eql (sixth acc) #\<)))))


(defun read-code-segment

; We assume we're inside a <code> block.  We read until </code> is found,
; gathering the characters we see and tracking how many spaces follow each
; newline.

  (x n xl    ; string we're reading, position, length as usual
     acc     ; accumulator for chars in this <code> block so far
     spacesp ; are we currently reading spaces?
     curr-sp ; how many spaces we've seen on this line so far
     min-sp  ; minimum number of spaces we've seen on any prev line
     )
  "Returns (MV N ACC MIN-SP)"
  (b* (((when (>= n xl))
        ;; End of string while reading <code>?  Shouldn't really happen.
        ;; Let's return 0 so that we won't change the section.
        (mv n acc 0))

       (char-n (char x n))
       ((when (and (eql char-n #\<)
                   (str::strprefixp-impl "</code>" x 0 n
                                         7 ;; (length "</code>")
                                         xl)))
        ;; Found </code> tag, so stop reading.  This is kind of subtle.
        ;;
        ;; Case 1: we had </code> at the start of the line, or after just some
        ;; spaces.  In this case, we don't care how many spaces we've seen so
        ;; far, because we explicitly want to allow for things like
        ;;
        ;;   |<code>
        ;;   |  foo
        ;;   |</code>
        ;;
        ;; Case 2: someone put the </code> inline with their text, i.e., they
        ;; wrote something like
        ;;
        ;;   |<code>
        ;;   |  foo
        ;;   | bar</code>
        ;;
        ;; In this case, we definitely DO want to consider spaces on the
        ;; current line.
        (mv n acc (if spacesp
                      min-sp
                    (min curr-sp min-sp))))

       (acc (cons char-n acc))
       ((when (eql char-n #\Space))
        (read-code-segment x (+ 1 n) xl
                           acc
                           spacesp
                           (if spacesp (+ 1 curr-sp) curr-sp)
                           min-sp))

       ((unless (eql char-n #\Newline))
        ;; A normal character, just accumulate it.
        (read-code-segment x (+ 1 n) xl
                           acc nil curr-sp min-sp)))

    ;; For newlines, the situation is also subtle.  We want to allow
    ;; people to double-space things, e.g.,
    ;;
    ;;    |<code>
    ;;    |  foo
    ;;    |[newline here]
    ;;    |  bar
    ;;    |</code>
    ;;
    ;; So basically: consider curr-sp only if there are non-spaces here.
    (read-code-segment x (+ 1 n) xl
                       acc
                       t ;; start reading spaces again
                       0 ;; new line has no spaces yet
                       (if spacesp
                           min-sp
                         (min curr-sp min-sp)))))

#||
 (b* ((x  "      three spaces
  two spaces
 blah</code> more text <p>blah blah</p>")
     ((mv n acc min-sp)
      (read-code-segment x 0 (length x) nil t 0 100)))
  (list n (str::rchars-to-string acc) min-sp))
||#

(defun starts-with-n-spaces (n x)
  (or (zp n)
      (and (consp x)
           (eql (car x) #\Space)
           (starts-with-n-spaces (- n 1) (cdr x)))))

(defun revappend-code-chars
  (code-chars ; characters from the <code> section (regular, non-reversed order)
   acc        ; accumulator we're writing them into
   min-sp     ; minimum spaces after each newline (except blank lines)
   )
  (b* (((when (atom code-chars))
        acc)
       ((cons char1 rest) code-chars)
       (acc (cons char1 acc))
       ((unless (eql char1 #\Newline))
        (revappend-code-chars (cdr code-chars) acc min-sp))
       ;; Have a newline.
       ((when (and (posp min-sp)
                   (starts-with-n-spaces min-sp rest)))
        ;; Skip these n spaces
        (revappend-code-chars (nthcdr min-sp rest) acc min-sp)))
    ;; Else, doesn't start with n spaces.  Must be a pure blank line.
    ;; Don't muck with it.
    (revappend-code-chars rest acc min-sp)))

(defun transform-code-segments (x n xl acc)
  (b* (((when (>= n xl))
        acc)
       (char-n (char x n))
       (acc    (cons char-n acc))
       (n      (+ 1 n))
       ((unless (and (eql char-n #\>)
                     (just-started-code-p acc)))
        (transform-code-segments x n xl acc))
       ;; Started a code segment.
       ((mv n code-acc min-sp)
        (read-code-segment x n xl
                           nil ;; accumulator for chars
                           t   ;; yes, we're reading spaces, to begin
                           0   ;; no spaces seen so far
                           100 ;; as good as infinity, here.
                           ))
       (code-chars (reverse code-acc))
       (acc (revappend-code-chars code-chars acc min-sp)))
    (transform-code-segments x n xl acc)))

(defun transform-code (x)
  ;; Fix leading spaces in <code> segments
  (str::rchars-to-string (transform-code-segments x 0 (length x) nil)))

#||
 (transform-code
"<p>This is
some regular text</p>
<code>
    blah1
    <blah>blah2</blah>
    blah3
</code>
<p>And more text</p>")
||#




; Horribly, we now pretty much repeat the same thing, but whereas the above
; targets <code> blocks, we now deal with @({...}) blocks.  Here, we assume
; that we've already extracted the whole string that we want to transform.

(defun read-ppcode-segment
  (x n xl    ; string we're reading, position, length as usual
     spacesp ; are we currently reading spaces?
     curr-sp ; how many spaces we've seen on this line so far
     min-sp  ; minimum number of spaces we've seen on any prev line
     )
  "Returns MIN-SP"
  (b* (((when (>= n xl))
        ;; End of string.  That's when we want to stop.
        (if spacesp
            min-sp
          (min curr-sp min-sp)))

       (char-n (char x n))
       ;; No </code> handling; we'll read to the end of the string.
       ((when (eql char-n #\Space))
        (read-ppcode-segment x (+ 1 n) xl
                             spacesp
                             (if spacesp (+ 1 curr-sp) curr-sp)
                             min-sp))

       ((unless (eql char-n #\Newline))
        ;; normal character, stop reading spaces if we were doing so
        (read-ppcode-segment x (+ 1 n) xl
                             nil curr-sp min-sp)))
    ;; Newline character, start new line
    (read-ppcode-segment x (+ 1 n) xl
                         t ;; start reading spaces again
                         0 ;; new line has no spaces yet
                         (if spacesp
                             min-sp
                           (min curr-sp min-sp)))))

(defun maybe-fix-spaces-in-sub (x)
  (declare (type string x))
  (b* ((xl      (length x))
       (min-sp  (read-ppcode-segment x 0 xl t 0 100))
       ((when (zp min-sp))
        ;; Fine, don't do anything
        x)
       (code-chars (explode x))
       (code-chars (if (starts-with-n-spaces min-sp code-chars)
                       (nthcdr min-sp code-chars)
                     code-chars))
       (acc (revappend-code-chars code-chars nil min-sp)))
    (str::rchars-to-string acc)))

(encapsulate
  ()
  (logic)

  (local
   (progn

     (defun test (x expect)
       (declare (xargs :mode :program))
       (equal (maybe-fix-spaces-in-sub x) expect))

     (assert! (test " foo
 bar
 baz"
                    "foo
bar
baz"))

     (assert! (test " foo
bar
 baz"
                    " foo
bar
 baz"))

     (assert! (test " foo

 bar
 baz
"
                    "foo

bar
baz
"))

     (assert! (test "foo
 bar
baz
"
                    "foo
 bar
baz
")))))


(defun fancy-trim-start (x n xl current-line-start)
  ;; Say a blank line consists of nothing but spaces.  We throw away all blank
  ;; lines at the start of a string.
  (b* (((when (eql n xl))
        ;; It was all whitespace.
        n)
       (c (char x n))
       (n (+ 1 n))
       ((when (eql c #\Space))
        ;; Another space, stick with current line
        (fancy-trim-start x n xl current-line-start))
       ((when (eql c #\Newline))
        ;; Advance to the next line
        (fancy-trim-start x n xl n)))
    current-line-start))

(defun fancy-trim-stop (x n start)
  ;; N counts down from (length x) to start.
  (b* (((when (<= n start))
        ;; saw nothing but spaces and newlines, turn it into the empty string.
        start)
       (n (- n 1))
       (c (char x n))
       ((when (or (eql c #\Space)
                  (eql c #\Newline)
                  (eql c #\Tab)))
        (fancy-trim-stop x n start)))
    n))

(defun fancy-extract-block (x start end)
  (b* ((start (fancy-trim-start x start end start))
       ((when (eql start end))
        "")
       (end   (+ 1 (fancy-trim-stop x end start))))
    (subseq x start end)))




; Support for Lisp Evaluation
;
; @(`(foo ...)`) evaluates foo and pretty-prints the result with <tt>s
;
; @(`(:code (foo ...))`) evaluates foo with <code>s
;
; @(`(:raw (foo ...))`) evaluates foo, which must return STR or (mv STR ...),
; and inserts STR into the accumulator, verbatim, without any special
; encoding.
;
; We might add other keywords later.

(defun preprocess-eval-parse
  (str       ;; the ... part of the @(`...`) form
   base-pkg  ;; base package for this topic, which we need to parse relative to
   state)
  "Returns (mv errmsg? parsed-sexpr state)"
  (b* ((curr-pkg         (current-package state))
       ;; Switch to the base-pkg to do the parsing, so that we read the symbols
       ;; in the string relative to the base-pkg that was used at the time...
       ((mv err & state) (acl2::in-package-fn (symbol-package-name base-pkg) state))
       ((when err)
        (mv (str::cat "Error: can't switch to package " (symbol-package-name base-pkg)
                      " to parse @(`...`).  Input: " str)
            nil
            state))
       ((mv err objects state) (acl2::read-string str))
       ((mv & & state) (acl2::in-package-fn curr-pkg state))
       ((when err)
        (mv (str::cat "Error: failed to parse @(`...`).  Input: " str)
            nil
            state))
       ((unless (equal (len objects) 1))
        (mv (str::cat "Error: parsed " (str::nat-to-dec-string (len objects))
                      " expressions (instead of 1) from @(`...`).  Input: " str)
            nil
            state))
       (sexpr (car objects)))
    (mv nil sexpr state)))

(defun preprocess-eval-main (sexpr preproc-data state acc)
  "Returns (MV ERRMSG? ACC STATE)"
  (b* (((mv kind sexpr)
        (if (and (consp sexpr)
                 (consp (cdr sexpr))
                 (not (cddr sexpr))
                 (keywordp (first sexpr)))
            (mv (first sexpr) (second sexpr))
          (mv nil sexpr)))
       ((mv err vals state) (acl2::unsound-eval sexpr))
       ((preproc-data preproc-data))
       ((when err)
        (mv (str::cat "Error: failed to evaluate @(`...`): "
                      ;; BOZO this isn't right, we really want something like
                      ;; ~@, but we don't have that unless we use ACL2's
                      ;; built-in fmt-to-string stuff, which I don't want to
                      ;; use due to the problems described in
                      ;; fmt-to-str-orig.lisp...  For now, we can at least just
                      ;; stringify the error in a dumb way.
                      (str::pretty err :config (str::make-printconfig :home-package preproc-data.base-pkg)))
            acc
            state))
       (ret (cond ((atom vals)
                   ;; The use of ER here is special; this is just a sanity
                   ;; check, this should be an impossible case, not triggerable
                   ;; by the user, just due to how unsound-eval works.
                   (er hard? 'preprocess-eval-main "unsound-eval returned an atom?"))
                  ((atom (cdr vals))
                   (car vals))
                  (t
                   (cons 'mv vals))))

       ((unless kind)
        (b* ((acc (process-obj-to-verb ret preproc-data state acc)))
          (mv nil acc state)))

       ((when (eq kind :code))
        (b* ((acc (process-obj-to-code ret preproc-data state acc)))
          (mv nil acc state)))

       ((when (eq kind :raw))
        (b* ((str (car vals))
             ((unless (stringp str))
              (mv (str::cat "Error: @(`(:raw ...)`) must return a string as its "
                            "first (or only) return value, but "
                            (str::pretty sexpr :config (str::make-printconfig :home-package preproc-data.base-pkg))
                            " returned "
                            (str::pretty ret :config (str::make-printconfig :home-package preproc-data.base-pkg)))
                  acc state))
             (acc (str::printtree-rconcat str acc)))
          (mv nil acc state))))
    (mv (msg "Error: @(`(~x0 ...)`) is not a known evaluation keyword.  Input sexpr: ~x1."
             kind (str::pretty sexpr))
        acc state)))

(defun preprocess-eval (str preproc-data state acc)
  "Returns (MV ACC STATE)"
  (b* (((preproc-data preproc-data))
       ((mv errmsg sexpr state) (preprocess-eval-parse str preproc-data.base-pkg state))
       ((when errmsg)
        (or (not (xdoc-verbose-p))
            (xdoc-error "~@1" preproc-data.context errmsg))
        (let ((acc (simple-html-encode-str errmsg 0 (length errmsg) acc)))
          (mv acc state)))
       ((mv errmsg acc state)
        (preprocess-eval-main sexpr preproc-data state acc))
       ((when errmsg)
        (or (not (xdoc-verbose-p))
            (xdoc-error "~@1" preproc-data.context errmsg))
        (let ((acc (simple-html-encode-str errmsg 0 (length errmsg) acc)))
          (mv acc state))))
    (mv acc state)))

(defun preprocess-encode-string (x preproc-data acc)
  (b* (((preproc-data preproc-data)))
    (autolink-and-encode x 0 (length x) 0
                         (and (not preproc-data.disable-autolinking-p)
                              preproc-data.topics-fal)
                         preproc-data.base-pkg preproc-data.kpa acc)))

(defun just-passed-code-p (x idx baseidx)
  (let* ((tag "<code>")
         (taglen (length tag)))
    (and (<= baseidx (- idx taglen))
         (str::strrange-equiv taglen x (- idx taglen) tag 0))))

(defun preprocess-aux (x n xl xbaseidx preproc-data state acc)
  "Returns (MV ACC STATE)"
  ;; Main preprocessor loop.  Read from the string and accumulate the result
  ;; into acc, expanding away any preprocessor directives.

  ;; xbaseidx is <= n and is the earliest character such that all chars past it
  ;; up to n are not anything special.  Whenever we see a special sequence or
  ;; come to the end of the string we accumulate that subsequence onto the acc.
  (declare (type string x))
  (b* (((when (= n xl))
        (mv (str::pcat acc (subseq x xbaseidx n)) state))
       (context (b* (((preproc-data preproc-data))) preproc-data.context))

       (char (char x n))
       ((when (eql char #\@))
        (cond ((and (< (+ n 1) xl)
                    (eql (char x (+ n 1)) #\@))
               (b* (((preproc-data preproc-data))
                    (acc (str::pcat acc (subseq x xbaseidx n))))
                 ;; @@ --> @, but if archive-p, leave it
                 (preprocess-aux x (+ n 2) xl (+ n 2) preproc-data state
                                 (if preproc-data.archive-p
                                     (cons #\@ (cons #\@ acc))
                                   (cons #\@ acc)))))

              ((and (< (+ n 1) xl)
                    (eql (char x (+ n 1)) #\())
               ;; @( --> directive
               (b* (((when (and (< (+ n 2) xl)
                                (member (char x (+ n 2)) '(#\' #\{))))
                     ;; @(' directive -- turns into raw <tt> block with auto linking
                     (b* ((char (char x (+ n 2)))
                          ((mv end-str start-xml end-xml)
                           (if (eql char #\')
                               (mv "')" "<v>" "</v>")
                             (mv "})" "<code>" "</code>")))
                          (end
                           ;; Bugfix January 2014: some of the indices were off here -- I was looking
                           ;; for ') at N+2, but we need to start at N+3 because:
                           ;;    N == @, N+1 == (, N+2 == opening ', so N+3 == first char OR closing '
                           (str::strpos-fast end-str x (+ n 3)
                                             2 ;; length of string we're looking for
                                             xl))
                          ((unless end)
                           (prog2$ (and (xdoc-verbose-p)
                                        (xdoc-error "no closing ~s1 found for @(~s2 ..." context
                                                    end-str (coerce (list char) 'string)))
                                   (mv (str::pcat acc (subseq x xbaseidx n)) state)))
                          ((preproc-data preproc-data))
                          ((when preproc-data.archive-p)
                           ;; skip
                           (preprocess-aux x (+ end 2) xl xbaseidx preproc-data state acc))
                          (sub
                           (if (eql char #\')
                               ;; Change January 2014: we were using fancy-extract-block here, but it
                               ;; doesn't make sense to be worrying about initial/trailing whitespace
                               ;; in @('...'), so changing to just use a simple subseq
                               (unescape-end-delim (subseq x (+ n 3) end) #\')
                             (maybe-fix-spaces-in-sub
                              (unescape-end-delim (fancy-extract-block x (+ n 3) end) #\}))))

                          (acc (str::pcat acc (subseq x xbaseidx n)))
                          (acc (str::printtree-rconcat start-xml acc))
                          (acc (preprocess-encode-string sub preproc-data acc))
                          (acc (str::printtree-rconcat end-xml acc)))
                       (preprocess-aux x (+ end 2) xl (+ end 2) preproc-data state acc)))

                    ((when (and (< (+ n 2) xl)
                                (or (eql (char x (+ n 2)) #\[)
                                    (eql (char x (+ n 2)) #\$))))
                     ;; @([...]) directive -- turns into <math> block
                     ;; @($...$) directive -- turns into a <mathfrag> block
                     (b* ((fragp (eql (char x (+ n 2)) #\$))
                          (end (str::strpos-fast (if fragp "$)" "])")
                                                 x (+ n 3)
                                                 2 ;; length of string we're looking for
                                                 xl))
                          ((unless end)
                           (prog2$ (and (xdoc-verbose-p)
                                        (if fragp
                                            (xdoc-error "no closing $) found for @($ ..." context)
                                          (xdoc-error "no closing ]) found for @([ ..." context)))
                                   (mv (str::pcat acc (subseq x xbaseidx n)) state)))
                          ((preproc-data preproc-data))
                          ((when preproc-data.archive-p)
                           ;; skip
                           (preprocess-aux x (+ end 2) xl xbaseidx preproc-data state acc))
                          (sub (subseq x (+ n 3) end))
                          (acc (str::pcat acc (subseq x xbaseidx n)))
                          (acc (str::printtree-rconcat (if fragp "<mathfrag>" "<math>") acc))
                          ;; Unlike @('...') we don't want to try to automatically insert hyperlinks, as
                          ;; that would very likely totally screw up katex.
                          (acc (simple-html-encode-str sub 0 (length sub) acc))
                          (acc (str::printtree-rconcat (if fragp "</mathfrag>" "</math>") acc)))
                       (preprocess-aux x (+ end 2) xl (+ end 2) preproc-data state acc)))

                    ((when (and (< (+ n 2) xl)
                                (eql (char x (+ n 2)) #\`)))
                     ;; @(`...`) directive -- Lisp evaluation of the form.
                     (b* ((end (str::strpos-fast "`)" x (+ n 2) 2 xl))
                          ((unless end)
                           (prog2$ (and (xdoc-verbose-p)
                                        (xdoc-error "no closing `) found for @(` ..." context))
                                   (mv (str::pcat acc (subseq x xbaseidx n)) state)))
                          (str (subseq x (+ n 3) end))
                          (acc (str::pcat acc (subseq x xbaseidx n)))
                          ((mv acc state)
                           (preprocess-eval str preproc-data state acc)))
                       (preprocess-aux x (+ end 2) xl (+ end 2) preproc-data state acc)))

                    ((preproc-data preproc-data))
                    (orig-n n)
                    ((mv error command arg arg-raw n) (parse-directive x (+ n 2) xl preproc-data.base-pkg preproc-data.kpa))
                    (acc (str::pcat acc (subseq x xbaseidx orig-n)))
                    ((when error)
                     (prog2$ (and (xdoc-verbose-p)
                                  (xdoc-error "~x1." context error))
                             (mv acc state)))
                    ((mv acc state)
                     (process-directive command arg arg-raw preproc-data state acc)))
                 (preprocess-aux x n xl n preproc-data state acc)))

              (t
               ;; @ sign in some other context.
               (preprocess-aux x (+ n 1) xl xbaseidx preproc-data state acc))))

       ((preproc-data preproc-data))
       ((when (and (not preproc-data.archive-p)
                   (eql char #\Newline)))
        ;; Gross hack #1: eat initial newlines from the start of a <code>
        ;; block, since otherwise they look ugly when firefox renders them.
        (b* (;; (codetag "<code>")
             ;; (taglen (length codetag))
             ;; ;; Regardless we're going to accumulate the string here.
             (acc (str::pcat acc (subseq x xbaseidx n))))
          (if ;; Check that the next substring to be added has <code> as a suffix.
              (just-passed-code-p x n xbaseidx)
              (if (and (< (+ n 1) xl)
                       (eql (char x (+ n 1)) #\Newline))
                  ;; Avoid eating multiple newlines at the start of a code block.
                  (preprocess-aux x (+ n 2) xl (+ n 2) preproc-data state acc)
                (preprocess-aux x (+ n 1) xl (+ n 1) preproc-data state acc))
          ;; Gross hack #2: the XSLT transformer in firefox seems to have some
          ;; problems if there aren't spaces at the end of lines, e.g., it will
          ;; run together the hover-text in the hierarchical description in
          ;; preview.html.  Fix by putting a space before newlines.  Horrible.
          (preprocess-aux x (+ n 1) xl (+ n 1) preproc-data state
                          (list* #\Newline #\Space acc))))))

    ;; Otherwise just keep the char and keep going.
    (preprocess-aux x (+ n 1) xl xbaseidx preproc-data state acc)))

(defun preprocess-main (x context topics-fal disable-autolinking-p base-pkg
                          state acc)
  "Returns (mv acc state)"
  (declare (type (or string null) x))
  (b* ((x (or x ""))
       ;; (current-pkg    (acl2::f-get-global 'current-package state))
       ;; Temporarily make "fmt" print as if it's in base-pkg.
       ;; ((mv & & state) (acl2::set-current-package (symbol-package-name base-pkg) state))
       (kpa            (known-package-alist state))
       (x              (transform-code x))
       (preproc-data `((:context . ,context)
                       (:base-pkg . ,base-pkg)
                       (:archive-p . nil)
                       (:disable-autolinking-p . ,disable-autolinking-p)
                       (:topics-fal . ,topics-fal)
                       (:kpa . ,kpa)))
       ((mv acc state) (preprocess-aux x 0 (length x) 0 preproc-data state acc))
       ;; Restore base-pkg for whoever called us.
       ;; ((mv & & state) (acl2::set-current-package current-pkg state))
       )
    (mv acc state)))


(defun replace-assoc (key val alist)
  (declare (xargs :guard (if (eqlablep key)
                             (alistp alist)
                           (eqlable-alistp alist))))
  (if (atom alist)
      (list (cons key val))
    (if (eql key (caar alist))
        (cons (cons key val) (cdr alist))
      (cons (car alist)
            (replace-assoc key val (cdr alist))))))

;; This differs from preprocess-topic (in prepare-topic.lisp) in that this just
;; replaces the :long and :short parts of a topic with their preprocessed
;; results, whereas that produces one entire string (which also includes XML
;; headers and error checking).
(defun preprocess-transform-topic (topic topics-fal state)
  (b* ((long (or (cdr (assoc :long topic)) ""))
       (short (or (cdr (assoc :short topic)) ""))
       (base-pkg (cdr (assoc :base-pkg topic)))
       (name (cdr (assoc :name topic)))
       ((mv short-printtree state)
        (preprocess-main short name topics-fal nil base-pkg state nil))
       (short-pre (str::printtree->str short-printtree))
       ((mv long-printtree state)
        (preprocess-main long name topics-fal nil base-pkg state nil))
       (long-pre (str::printtree->str long-printtree)))
    (mv (replace-assoc :long long-pre (replace-assoc :short short-pre topic)) state)))

(defun preprocess-transform-topics (x topics-fal state)
  (b* (((when (atom x))
        (mv nil state))
       ((mv first state) (preprocess-transform-topic (car x) topics-fal state))
       ((mv rest state)  (preprocess-transform-topics (cdr x) topics-fal state)))
    (mv (cons first rest) state)))
