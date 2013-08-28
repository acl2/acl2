; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>


; preprocess.lisp  -- the xdoc preprocessor

(in-package "XDOC")
(include-book "autolink")
(include-book "str/strprefixp" :dir :system)
(include-book "str/istrprefixp" :dir :system)
(include-book "str/strpos" :dir :system)
(include-book "oslib/catpath" :dir :system)
(local (include-book "misc/assert" :dir :system))
(set-state-ok t)
(program)



; ----------------- World Lookup Stuff --------------------------

(defun get-formals (fn world)
  (let ((formals (getprop fn 'formals :bad 'current-acl2-world world)))
    (if (not (eq formals :bad))
        formals
      (let ((macro-args (getprop fn 'macro-args :bad 'current-acl2-world world)))
        (if (not (eq macro-args :bad))
            macro-args
          (prog2$
           (cw "; xdoc note: get-formals failed for ~s0::~s1.~%"
               (symbol-package-name fn) (symbol-name fn))
           (concatenate 'string
                        "Error getting formals for "
                        (symbol-package-name fn)
                        "::"
                        (symbol-name fn))))))))

(defun get-measure (fn world)
  (let ((just (getprop fn 'justification nil 'current-acl2-world world)))
    (if just
        (access justification just :measure)
      (or (cw "; xdoc note: get-measure failed for ~x0.~%" fn)
          (concatenate 'string
                       "Error getting measure for "
                       (symbol-package-name fn)
                       "::"
                       (symbol-name fn))))))

(defun get-guard (fn world)
  (if (not (eq (getprop fn 'formals :bad 'current-acl2-world world) :bad))
      (getprop fn 'guard nil 'current-acl2-world world)
    (prog2$
     (cw "; xdoc note: get-guard failed for ~x0.~%" fn)
     (concatenate 'string
                  "Error getting guard for "
                  (symbol-package-name fn)
                  "::"
                  (symbol-name fn)))))

(defun get-body (fn world)
  ;; This gets the original body normalized or non-normalized body based on
  ;; what the user typed for the :normalize xarg.  The use of "last" skips past
  ;; any other :definition rules that have been added since then.
  (let ((bodies (getprop fn 'def-bodies nil 'current-acl2-world world)))
    (if bodies
        (access def-body (car (last bodies)) :concl)
      (or (cw "; xdoc note: get-body failed for ~x0.~%" fn)
          (concatenate 'string
                       "Error getting body for "
                       (symbol-package-name fn)
                       "::"
                       (symbol-name fn))))))


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

(defun clean-up-event (event)
  (if (atom event)
      event
    (case (car event)
      (defthm
        ;; I'll leave in the rule-classes, since they're probably important.
        (eat-things-from-event '(:hints :instructions :doc :otf-flg) event))
      (defun
        (let ((name    (second event))
              (formals (third event))
              (decls   (clean-up-function-decls (butlast (cdddr event) 1)))
              (body    (car (last event))))
          (if decls
              (append (list 'defun name formals)
                      decls
                      (list body))
            (list 'defun name formals body))))
      (defmacro
        (let ((name    (second event))
              (formals (third event))
              (decls   (clean-up-function-decls (butlast (cdddr event) 1)))
              (body    (car (last event))))
          (if decls
              (append (list 'defmacro name formals) decls (list body))
            (list 'defmacro name formals body))))
      (otherwise
       event))))

(defun get-event-aux (name world)
  ;; A general purpose event lookup as in :pe
  (let* ((props (acl2::getprops name 'current-acl2-world world))
        (evt   (and props (acl2::get-event name world))))
    (or evt
        (cw "; xdoc note: get-event failed for ~x0.~%" name)
        (concatenate 'string
                     "Error getting event for "
                     (symbol-package-name name)
                     "::"
                     (symbol-name name)))))

(defun get-event (name world)
  (clean-up-event (get-event-aux name world)))

#|

(get-event-aux 'append (w state))
(get-event 'append (w state))

(get-event-aux 'binary-append (w state))
(get-event 'binary-append (w state))

(get-event-aux 'write-byte$ (w state))
(get-event 'write-byte$ (w state))

(defun UGLY (X)
  (DECLARE
   (XARGS :GUARD T
          :GUARD-HINTS (("Goal" :USE ((:INSTANCE DEFAULT-CAR))))
          :VERIFY-GUARDS NIL))
  (IF (CONSP X) (UGLY (CDR X)) 0))

(get-event-aux 'ugly (w state))
(get-event 'ugly (w state))

(xml-ppr-obj (get-event 'ugly (w state))
             state
             :topics-fal (make-fast-alist '((acl2::consp . t)
                                            (acl2::defun . t)
                                            (acl2::declare . t)
                                            (acl2::xargs . t)
                                            (xdoc::ugly . t)
                                            (acl2::cdr . t)))
             :base-pkg 'xdoc::foo)

|#

(defun get-def (fn world)
  (get-event fn world))

(defun get-theorem (name world)
  ;; BOZO maybe do some cleaning to remove hints, etc.
  (get-event name world))

;; (defmacro foo ()
;;   `(progn (logic)
;;           (make-event
;;            '(encapsulate
;;               (((h *) => *))
;;               (local (defun h (x) (+ x 1)))
;;               (defun f (x) (+ x 1))
;;               (defun g (x) (+ x 2))))))

;; (defstobj st fld)

;; (defun-sk all-integerp (x)
;;   (forall a (implies (member-equal a x)
;;                      (integerp a))))

;; (defconst *const* 3)

;; (foo)

;; (get-event 'undefined (w state)) ; good, fails
;; (get-event 'append (w state))
;; (get-event 'binary-append (w state))
;; (get-event 'st (w state))
;; (get-event 'fld (w state)) ;; bad? returns the whole stobj
;; (get-event 'all-integerp (w state))
;; (get-event 'all-integerp-witness (w state)) ;; good i guess - returns the encapsulate
;; (get-event 'f (w state))
;; (get-event 'h (w state)) ;; good i guess, returns the encapsulate
;; (get-event 'acl2::car-cons (w state))
;; (get-event '*const* (w state))

;; (get-formals 'binary-append (w state))  ;; --> (ACL2::X ACL2::Y)
;; (get-formals 'append (w state)) ;; --> (ACL2::X ACL2::Y &REST ACL2::RST)
;; (get-formals 'all-integerp-witness (w state)) ;; good, works
;; (get-formals 'all-integerp (w state)) ;; good, works
;; (get-formals 'fld (w state)) ;; good, works
;; (get-formals 'st (w state)) ;; good, fails

;; (get-measure 'binary-append (w state)) ;; good, works
;; (get-measure 'append (w state))  ;; good, fails
;; (get-measure 'st (w state)) ;; good, fails
;; (get-measure 'fld (w state)) ;; good, fails
;; (get-measure 'all-integerp-witness (w state)) ;; good, fails
;; (get-measure 'all-integerp (w state)) ;; good, fails

;; (get-guard 'binary-append (w state)) ;; good, works
;; (get-guard 'append (w state)) ;; hrmn -- fails?
;; (get-guard 'all-integerp-witness (w state)) ;; NIL???
;; (get-guard 'all-integerp (w state)) ;; NIL???
;; (get-guard 'fld (w state)) ;; works
;; (get-guard 'st (w state)) ;; good, fails











; -------------- Preprocessor Command Parsing  ------------------


; Convention: X is a string we are traversing, N is our current position in the
; string, and XL is the length of the string.  See autolink.lisp.

(defun read-literal (x n xl chars) ;; ==> (MV SUCCESSP N-PRIME)
  ;; Try to read CHARS, verbatim.
  (declare (type string x))
  (cond ((= n xl)
         (mv (atom chars) n))
        ((consp chars)
         (if (eql (char x n) (car chars))
             (read-literal x (+ n 1) xl (cdr chars))
           (mv nil n)))
        (t
         (mv t n))))

(defun read-through-some-char-aux (x n xl chars acc) ;; ==> (MV SUCCESSP STRING N-PRIME)
  (declare (type string x))
  (if (= xl n)
      (mv nil (str::rchars-to-string acc) n)
    (let ((charN (char x n)))
      (if (member charN chars)
          (mv t (str::rchars-to-string (cons charN acc)) n)
        (read-through-some-char-aux x (+ 1 n) xl chars (cons charN acc))))))

(defun read-through-some-char (x n xl chars)
  ;; Try to read until one of CHARS is found
  (declare (type string x))
  (read-through-some-char-aux x n xl chars nil))

(defun skip-past-ws (x n xl) ;; ==> N-PRIME
  (declare (type string x))
  (cond ((= xl n)
         n)
        ((member (char x n) '(#\Space #\Tab #\Newline #\Page))
         (skip-past-ws x (+ 1 n) xl))
        (t
         n)))

(defun parse-directive (x n xl base-pkg kpa) ;; ==> (MV ERROR COMMAND ARG N-PRIME)
  ;; Every directive has the form @(command arg)
  ;; Where command and arg are symbols.
  ;; We assume @( has just been read, and N is now pointing right after the open paren.
  (declare (type string x))
  (b* ((n                    (skip-past-ws x n xl))
       ;; We want to get nice error messages here, because if there'a a directive we
       ;; really do expect it to be a valid symbol.
       ((mv error command n) (parse-symbol x n xl (pkg-witness "XDOC") kpa t))
       ((when error)
        (mv error nil nil n))
       (n                    (skip-past-ws x n xl))
       ((mv error arg n)     (parse-symbol x n xl base-pkg kpa t)))
      (cond
       ;; Some error parsing arg.  Add a little more context.
       (error (mv (concatenate 'string "In " (symbol-name command) " directive: " error)
                  nil nil n))

       ;; Ends with ), good.
       ((and (< n xl)
             (eql (char x n) #\)))
        (mv nil command arg (+ n 1)))

       (t
        (mv (concatenate 'string "In " (symbol-name command) " directive, expected ) after "
                         (symbol-name arg)
                         ". Near " (error-context x n xl) ".")
            nil nil n)))))

;; (let ((x "body foo)"))
;;   (parse-directive x 0 (length x) 'acl2::foo))

;; (let ((x "body foo) bar"))
;;   (parse-directive x 0 (length x) 'acl2::foo))

;; (let ((x "body xdoc::foo) bar"))
;;   (parse-directive x 0 (length x) 'acl2::foo))

;; (let ((x "xdoc::body xdoc::foo) bar"))
;;   (parse-directive x 0 (length x) 'acl2::foo))

;; (let ((x "acl2::body xdoc::foo) bar"))
;;   (parse-directive x 0 (length x) 'acl2::foo))

;; (let ((x "acl2::body)xdoc::foo) bar"))
;;   (parse-directive x 0 (length x) 'acl2::foo))




; -------------- Executing Directives ---------------------------

(defun process-url-directive (arg state acc) ;; ===> (MV ACC STATE)

; @(url foo) just expands into the file name for foo.

  (b* ((acc            (file-name-mangle arg acc)))
      (mv acc state)))


(defun process-sym-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)

; @(sym foo) just expands into the standard name mangling for foo

  (b* ((acc            (sym-mangle arg base-pkg acc)))
      (mv acc state)))


(defun process-sym-cap-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)

; @(csym foo) just expands into the standard capitalized name mangling for foo

  (b* ((acc            (sym-mangle-cap arg base-pkg acc)))
      (mv acc state)))


(defun process-see-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)

; @(see foo) just expands into a link with a lowercase name.

  (b* ((acc            (str::revappend-chars "<see topic=\"" acc))
       (acc            (file-name-mangle arg acc))
       (acc            (str::revappend-chars "\">" acc))
       (acc            (sym-mangle arg base-pkg acc))
       (acc            (str::revappend-chars "</see>" acc)))
      (mv acc state)))


(defun process-see-cap-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)

; @(csee foo) just expands into a link with a capitalized name.

  (b* ((acc            (str::revappend-chars "<see topic=\"" acc))
       (acc            (file-name-mangle arg acc))
       (acc            (str::revappend-chars "\">" acc))
       (acc            (sym-mangle-cap arg base-pkg acc))
       (acc            (str::revappend-chars "</see>" acc)))
      (mv acc state)))


(defconst *xdoc-link-file-message*
  "; This is an XDOC Link file.
; Ordinarily, you should not see this file.
;
; If you are viewing this file in a web browser, you probably
; have not configured your web browser to send .xdoc-link files
; to Emacs.
;
;   (Or, if you have already done that, but you accessed this
;    file through a web server, the server may just not be
;    assigning .xdoc-link files the appropriate MIME type.)
;
; If you are viewing this file in Emacs, you probably have not
; loaded xdoc.el from the xdoc/ directory.
;
; Please see the XDOC manual for more information.")

(defun process-srclink-directive (arg dir state acc) ;; ===> (MV ACC STATE)

; We do two things:
;
;   1. Extend acc with a srclink tag, and
;
;   2. Write a .xdoc-link file to dir for this tag, unless DIR is NIL in
;      which case we skip this step
;
; This is kind of ugly in that we may write the same .xdoc-link file many
; times, but this doesn't seem to practically be a problem.
;
; Our emacs linking mechanism is slightly broken, in that all we can tell emacs
; is the name of a symbol to look for using its tags mechanism.  We are hoping
; that:
;
;   1. The user has the appropriate TAGS tables set up (reasonable),
;
;   2. The symbol is actually defined in a source file somewhere, instead of
;      being introduced by a macro or something, and
;
;   3. The symbol is not defined in multiple packages, so that the user will be
;      taken to the right source file.  (That is, we can't tell emacs something
;      like "foo::bar", because it doesn't understand (in-package ...); We can
;      only tell it to search for bar.)
;
; Whether or not #2 and #3 hold is a total crap-shoot, and we're basically
; hoping that most of the time find-tag will take them to the right place.

  (b* ((shortname (coerce (string-downcase (symbol-name arg)) 'list))
       (filename  (b* ((nacc (file-name-mangle arg nil))
                       (nacc (str::revappend-chars ".xdoc-link" nacc)))
                    (str::rchars-to-string nacc)))

       ;; NOTE: the use of filename here is legacy stuff for the classic
       ;; viewer.  We don't need it or use it in the fancy viewer.  The fancy
       ;; viewer only uses the shortname, i.e., the text of the link.
       (acc (str::revappend-chars "<srclink file=\"" acc))
       (acc (str::revappend-chars filename acc))
       (acc (str::revappend-chars "\">" acc))
       (acc (simple-html-encode-chars shortname acc))
       (acc (str::revappend-chars "</srclink>" acc))

       ((unless dir)
        ;; This is an important hack for, e.g., :xdoc to work correctly.  If
        ;; DIR is nil, then don't actually try to write any files!
        (mv acc state))

       (fullpath           (oslib::catpath dir filename))
       ((mv channel state) (open-output-channel fullpath :character state))
       (state (princ$ *xdoc-link-file-message* channel state))
       (state (newline channel state))
       (state (newline channel state))
       (state (princ$ (coerce shortname 'string) channel state))
       (state (newline channel state))
       (state (close-output-channel channel state)))
      (mv acc state)))

(defun process-body-directive (arg topics-fal base-pkg state acc) ;; ===> (MV ACC STATE)

; @(body foo) -- look up the body and pretty-print it in a <code> block.

  (b* ((body           (get-body arg (w state)))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (xml-ppr-obj-aux body topics-fal base-pkg state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-def-directive (arg dir topics-fal base-pkg state acc) ;; ===> (MV ACC STATE)

; @(def foo) -- look up the definition for foo, pretty-print it in a <code>
; block, along with a source-code link.

  (b* ((def            (get-def arg (w state)))
       (acc            (str::revappend-chars "<p><b>Definition: </b>" acc))
       ((mv acc state) (process-srclink-directive arg dir state acc))
       (acc            (str::revappend-chars "</p>" acc))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (xml-ppr-obj-aux def topics-fal base-pkg state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-gdef-directive (arg topics-fal base-pkg state acc) ;; ===> (MV ACC STATE)

; @(gdef foo) -- Look up the definition for foo, pretty-print it as in @def,
; but don't use a source-code link because this is a "Generated Definition" for
; which a tags-search will probably fail.

  (b* ((def            (get-def arg (w state)))
       (acc            (str::revappend-chars "<p><b>Definition: </b>" acc))
       (acc            (sym-mangle arg base-pkg acc))
       (acc            (str::revappend-chars "</p>" acc))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (xml-ppr-obj-aux def topics-fal base-pkg state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-thm-directive (arg dir topics-fal base-pkg state acc) ;; ===> (MV ACC STATE)

; @(thm foo) -- Look up the theorem named foo, and pretty-print its event along
; with a source link.

  (b* ((theorem        (get-theorem arg (w state)))
       (acc            (str::revappend-chars "<p><b>Theorem: </b>" acc))
       ((mv acc state) (process-srclink-directive arg dir state acc))
       (acc            (str::revappend-chars "</p>" acc))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (xml-ppr-obj-aux theorem topics-fal base-pkg state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-gthm-directive (arg topics-fal base-pkg state acc) ;; ===> (MV ACC STATE)

; @(gthm foo) -- Like @(thm foo), but don't provide a source link since this is
; a generated theorem.

  (b* ((theorem        (get-theorem arg (w state)))
       (acc            (str::revappend-chars "<p><b>Theorem: </b>" acc))
       (acc            (sym-mangle arg base-pkg acc))
       (acc            (str::revappend-chars "</p>" acc))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (xml-ppr-obj-aux theorem topics-fal base-pkg state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-formals-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)

; @(formals foo) -- just find the formals for foo and print them without any
; extra formatting.

  (b* ((formals        (get-formals arg (w state)))
       ((mv acc state) (fmt-and-encode-to-acc formals base-pkg state acc)))
      (mv acc state)))

(defun process-call-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)

; @(call foo) -- find the formals to foo and insert <tt>(foo x y z)</tt>.
; BOZO consider adding an emacs link.

  (b* ((formals        (get-formals arg (w state)))
       (call           (cons arg formals))
       (acc            (str::revappend-chars "<tt>" acc))
       ((mv acc state) (fmt-and-encode-to-acc call base-pkg state acc))
       (acc            (str::revappend-chars "</tt>" acc)))
      (mv acc state)))

(defun process-ccall-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)

; @(ccall foo) -- "code call" is like @(call foo), but uses <code> instead
; of <tt> tags.

  (b* ((formals        (get-formals arg (w state)))
       (call           (cons arg formals))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (fmt-and-encode-to-acc call base-pkg state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-measure-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)

; @(measure foo) -- find the measure for foo and print it without any extra
; formatting.

  (b* ((measure        (get-measure arg (w state)))
       ((mv acc state) (fmt-and-encode-to-acc measure base-pkg state acc)))
      (mv acc state)))


(defun process-directive (command arg dir topics-fal base-pkg state acc) ;; ===> (MV ACC STATE)

; Command and Arg are the already-parsed symbols we have read from the
; documentation string.  Carry out whatever directive we've been asked to do.
; DIR is the output dir.  Acc is the accumulator for our output characters.

  (case command
    (def       (process-def-directive     arg dir topics-fal base-pkg state acc))
    (thm       (process-thm-directive     arg dir topics-fal base-pkg state acc))
    (srclink   (process-srclink-directive arg dir state acc))
    (gdef      (process-gdef-directive    arg topics-fal base-pkg state acc))
    (gthm      (process-gthm-directive    arg topics-fal base-pkg state acc))
    (body      (process-body-directive    arg topics-fal base-pkg state acc))
    (formals   (process-formals-directive arg base-pkg state acc))
    (measure   (process-measure-directive arg base-pkg state acc))
    (call      (process-call-directive    arg base-pkg state acc))
    (ccall     (process-ccall-directive   arg base-pkg state acc))
    (url       (process-url-directive     arg state acc))
    (see       (process-see-directive     arg base-pkg state acc))
    (csee      (process-see-cap-directive arg base-pkg state acc))
    (sym       (process-sym-directive     arg base-pkg state acc))
    (csym      (process-sym-cap-directive arg base-pkg state acc))
    (otherwise
     (prog2$
      (cw "; xdoc error: unknown directive ~x0.~%" command)
      (let* ((acc (str::revappend-chars "[[ unknown directive " acc))
             (acc (str::revappend-chars (symbol-package-name command) acc))
             (acc (str::revappend-chars "::" acc))
             (acc (str::revappend-chars (symbol-name command) acc))
             (acc (str::revappend-chars "]]" acc)))
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

(defun read-code-segment (x n xl acc always-spacep)
  "Returns (MV N ACC ALWAYS-SPACEP)"

; We assume we're inside a <code> block.  We read until </code> is found,
; gathering the characters we see and tracking whether each newline is followed
; by a space.

  (b* (((when (>= n xl))
        (mv n acc always-spacep))

       (char-n (char x n))
       ((when (and (eql char-n #\<)
                   (str::strprefixp-impl "</code>" x 0 n
                                         7 ;; (length "</code>")
                                         xl)))
        ;; Found </code> tag, so stop reading
        (mv n acc always-spacep))

       (acc (cons char-n acc))
       ((unless (eql char-n #\Newline))
        ;; A normal character, just accumulate it.
        (read-code-segment x (+ 1 n) xl acc always-spacep))

       (n (+ 1 n))
       ((when (>= n xl))
        ;; End of string while reading <code>?  Shouldn't really happen...
        (mv n acc always-spacep))

       (char-n (char x n))
       ((when (eql char-n #\<))
        ;; We allow the </code> to come without a space.
        (mv n acc always-spacep))

       (acc (cons char-n acc))
       (always-spacep (and always-spacep
                           (or (eql char-n #\Space)
                               (eql char-n #\Newline)))))
    (read-code-segment x (+ 1 n) xl acc always-spacep)))

(defun revappend-code-chars (code-chars acc always-spacep)
  (b* (((when (atom code-chars))
        acc)
       (char1 (car code-chars))
       (acc   (cons char1 acc))
       ((unless (eql char1 #\Newline))
        (revappend-code-chars (cdr code-chars) acc always-spacep))
       ((when (and always-spacep
                   (consp (cdr code-chars))
                   (eql (second code-chars) #\Space)))
        ;; Skip the first space
        (revappend-code-chars (cddr code-chars) acc always-spacep)))
    (revappend-code-chars (cdr code-chars) acc always-spacep)))

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
       ((mv n code-acc always-spacep)
        (read-code-segment x n xl nil t))
       (code-chars (reverse code-acc))
       (acc (revappend-code-chars code-chars acc always-spacep)))
    (transform-code-segments x n xl acc)))

(defun transform-code (x)
  ;; Fix leading spaces in <code> segments
  (str::rchars-to-string (transform-code-segments x 0 (length x) nil)))

;; (transform-code 
;; "<p>This is 
;; some regular text</p>
;; <code>
;;     blah1
;;     <blah>blah2</blah>
;;     blah3
;; </code>
;; <p>And more text</p>")

(defun advance-line (x n xl)
  ;; Returns the index of the next newline after character N, or else XL
  (b* (((when (= n xl))
        n)
       (c (char x n))
       ((when (eql c #\Newline))
        n))
    (advance-line x (+ 1 n) xl)))

(defun all-lines-start-with-space-p (x n xl)
  ;; Assumptions:
  ;;  - We are starting a line
  ;;  - Every line we've seen so far starts with a space
  (b* (((when (>= n xl))
        ;; DO NOT WEAKEN TO (= N XL).  We unusually allow this to exceed the
        ;; string length; consider the call of advance-line below.
        ;; Success, reached end of string, no space required
        t)
       (c (char x n))
       ((when (eql c #\Newline))
        ;; Fine, blank line, no space required
        (all-lines-start-with-space-p x (+ 1 n) xl))
       ((when (eql c #\Space))
        ;; Fine, has a space, skip to next line
        (b* ((n (advance-line x (+ 1 n) xl)))
          (all-lines-start-with-space-p x (+ 1 n) xl))))
    ;; Nope, found a non-space char at start of the line.
    nil))

(encapsulate
  ()
  (logic)

  (local
   (progn

     (defun test (x)
       (declare (xargs :mode :program))
       (all-lines-start-with-space-p x 0 (length x)))

     (assert! (test " foo
 bar
 baz"))

     (assert! (not (test " foo
bar
 baz")))

     (assert! (test " foo

 bar
 baz
"))

     (assert! (not (test "foo
 bar
baz
"))))))

(defun delete-leading-line-space (x n xl acc)
  ;; Assumes (all-lines-start-with-space-p x n xl)
  (b* (((when (>= n xl))
        acc)
       (c (char x n))
       ((when (eql c #\Newline))
        (delete-leading-line-space x (+ 1 n) xl (cons c acc)))
       ;; Else it must be a space.  Skip the space but copy the other chars
       ;; through the end of the line.
       (start (+ 1 n))
       (end   (advance-line x start xl))
       ;; BOZO abuse of revappend-chars-aux to only copy until end...
       ;; should fix its guard to allow this sort of thing
       (acc   (str::revappend-chars-aux x start end acc)))
    (delete-leading-line-space x end xl acc)))

(defun maybe-fix-spaces-in-sub (x)
  (declare (type string x))
  (b* ((xl (length x))
       ((unless (all-lines-start-with-space-p x 0 xl))
        ;; Fine, don't do anything
        x)
       (acc (delete-leading-line-space x 0 xl nil)))
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


(defun fancy-trim-start (x n xl new-start)
  (b* (((when (= n xl))
        ;; saw nothing but spaces and newlines, turn it into the empty string.
        n)
       (c (char x n))
       (n (+ 1 n))
       ((when (eql c #\Space))
        (fancy-trim-start x n xl new-start))
       ((when (eql c #\Newline))
        (fancy-trim-start x n xl n)))
    new-start))

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
       (end   (+ 1 (fancy-trim-stop x end start)))
       ((unless (<= start end))
        ""))
    (subseq x start end)))





(defun preprocess-aux (x n xl dir topics-fal base-pkg kpa state acc)
  "Returns (MV ACC STATE)"
  (declare (type string x))

; Main preprocessor loop.  Read from the string and accumulate the result into
; acc, expanding away any preprocessor directives.

  (b* (((when (= n xl))
        (mv acc state))

       (char (char x n))
       ((when (eql char #\@))
        (cond ((and (< (+ n 1) xl)
                    (eql (char x (+ n 1)) #\@))
               ;; @@ --> @
               (preprocess-aux x (+ n 2) xl dir topics-fal base-pkg kpa state (cons #\@ acc)))

              ((and (< (+ n 1) xl)
                    (eql (char x (+ n 1)) #\())
               ;; @( --> directive
               (b* (((when (and (< (+ n 2) xl)
                                (eql (char x (+ n 2)) #\')))
                     ;; @(' directive -- turns into raw <tt> block with auto linking
                     (b* ((end (str::strpos-fast "')" x (+ n 2) 2 xl))
                          ((unless end)
                           (prog2$ (cw "; xdoc error: no closing ') found for @(' ...~%")
                                   (mv acc state)))
                          (sub (fancy-extract-block x (+ n 3) end))
                          (acc (str::revappend-chars "<tt>" acc))
                          (acc (autolink-and-encode sub 0 (length sub) topics-fal base-pkg kpa acc))
                          (acc (str::revappend-chars "</tt>" acc)))
                       (preprocess-aux x (+ end 2) xl dir topics-fal base-pkg kpa state acc)))

                    ((when (and (< (+ n 2) xl)
                                (eql (char x (+ n 2)) #\{)))
                     ;; @({ directive -- turns into raw <code> block with auto linking
                     (b* ((end (str::strpos-fast "})" x (+ n 2) 2 xl))
                          ((unless end)
                           (prog2$ (cw "; xdoc error: no closing }) found for @({ ...~%")
                                   (mv acc state)))
                          (sub (maybe-fix-spaces-in-sub (fancy-extract-block x (+ n 3) end)))
                          (acc (str::revappend-chars "<code>" acc))
                          (acc (autolink-and-encode sub 0 (length sub) topics-fal base-pkg kpa acc))
                          (acc (str::revappend-chars "</code>" acc)))
                       (preprocess-aux x (+ end 2) xl dir topics-fal base-pkg kpa state acc)))


                    ((mv error command arg n) (parse-directive x (+ n 2) xl base-pkg kpa))
                    ((when error)
                     (prog2$ (cw "; xdoc error: ~x0.~%" error)
                             (mv acc state)))
                    ((mv acc state)
                     (process-directive command arg dir topics-fal base-pkg state acc)))
                 (preprocess-aux x n xl dir topics-fal base-pkg kpa state acc)))

              (t
               ;; @ sign in some other context.
               (preprocess-aux x (+ n 1) xl dir topics-fal base-pkg kpa state (cons #\@ acc)))))

       ((when (eql char #\Newline))
        ;; Gross hack #1: eat initial newlines from the start of a <code>
        ;; block, since otherwise they look ugly when firefox renders them.
        (if (just-started-code-p acc)
            (if (and (< (+ n 1) xl)
                     (eql (char x (+ n 1)) #\Newline))
                ;; Avoid eating multiple newlines at the start of a code block.
                (preprocess-aux x (+ n 2) xl dir topics-fal base-pkg kpa state (cons #\Newline acc))
              (preprocess-aux x (+ n 1) xl dir topics-fal base-pkg kpa state acc))
          ;; Gross hack #2: the XSLT transformer in firefox seems to have some
          ;; problems if there aren't spaces at the end of lines, e.g., it will
          ;; run together the hover-text in the hierarchical description in
          ;; preview.html.  Fix by putting a space before newlines.  Horrible.
          (preprocess-aux x (+ n 1) xl dir topics-fal base-pkg kpa state
                          (list* #\Newline #\Space acc)))))

    ;; Otherwise just keep the char and keep going.
    (preprocess-aux x (+ n 1) xl dir topics-fal base-pkg kpa state (cons char acc))))

(defun preprocess-main (x dir topics-fal base-pkg state acc)
  (declare (type (or string null) x))
  (b* ((x (or x ""))
       ;; (current-pkg    (acl2::f-get-global 'current-package state))
       ;; Temporarily make "fmt" print as if it's in base-pkg.
       ;; ((mv & & state) (acl2::set-current-package (symbol-package-name base-pkg) state))
       (kpa            (known-package-alist state))
       (x              (transform-code x))
       ((mv acc state) (preprocess-aux x 0 (length x) dir topics-fal base-pkg kpa state acc))
       ;; Restore base-pkg for whoever called us.
       ;; ((mv & & state) (acl2::set-current-package current-pkg state))
       )
      (mv acc state)))

