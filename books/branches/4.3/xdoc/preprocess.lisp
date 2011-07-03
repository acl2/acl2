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
(include-book "names")
(include-book "str/top" :dir :system)
(include-book "unicode/read-file-characters" :dir :system)
(set-state-ok t)
(program)


(defun fmt-to-chars (string alist state)

; Use ACL2's fancy new string-printing stuff to pretty-print an object into a
; string.

  (b* (((mv channel state)  (open-output-channel :string :character state))
       ((mv & state)        (fmt string alist channel state nil))
       ((mv err str state)  (get-output-stream-string$ channel state)))
    (or (not err)
        (er hard? 'fmt-to-chars "Error with get-output-stream-string$???"))
    (mv (coerce str 'list) state)))

(defun fmt-to-chars-and-encode (string alist state acc) ;; ==> (MV ACC-PRIME STATE)

; Like fmt, but HTML-escape the result and accumulate it onto acc (in reverse
; order) instead of printing it.

  (mv-let (data state)
          (fmt-to-chars string alist state)
          ;; We cdr the data because fmt puts in a newline.
          (let ((acc (simple-html-encode-chars (cdr data) acc)))
            (mv acc state))))





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

(defun get-event (name world)
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

; Throughout these functions, X is a string we are traversing, N is our current
; position in the string, XL is the length of the string, and an imagined guard
; is:
;
;  (declare (xargs :guard (and (stringp x)
;                              (natp n)
;                              (natp xl)
;                              (= xl (length x))
;                              (<= n xl)))
;
; We could do a lot of this in logic mode, but there doesn't seem to be much
; point to that.

(defun error-context (x n xl) ;; ==> STRING
  ;; Tries to show what text is near an error.
  (declare (type string x))
  (let ((min (nfix (- n 20)))
        (max (min (+ n 20) xl)))
    (subseq x min max)))

; What a pain.  We have to implement a symbol parser.

(defun parse-symbol-name-part (x n xl bar-escape-p slash-escape-p some-chars-p acc)
  ;; ==> (MV ERROR NAME N-PRIME)
  (declare (type string x))

; This tries to read just one part of a symbol name (i.e., the package part,
; or the name part.)

  (if (= xl n)

      ; End of string?  Error if we were escaped, or if we have not actually read
      ; some characters yet.  Otherwise, it was okay.

      (let ((result (reverse (coerce acc 'string))))
        (if (or bar-escape-p slash-escape-p (not some-chars-p))
            (mv (concatenate 'string "Near " (error-context x n xl)
                             ": unexpected end of string while reading symbol.  "
                             "Characters read so far: " result)
                result n)
          (mv nil result n)))

    (let ((n+1  (+ n 1))
          (char (char x n)))
      (cond (slash-escape-p
             ;; Slash escape is on, so just add next char verbatim and turn off
             ;; slash escape.
             (parse-symbol-name-part x n+1 xl bar-escape-p nil t (cons char acc)))
            ((eql char #\|)
             ;; Bar just toggles bar-escaped-ness.
             (parse-symbol-name-part x n+1 xl (not bar-escape-p) nil t acc))
            ((eql char #\\)
             ;; Slash starts a slash-escape.
             (parse-symbol-name-part x n+1 xl bar-escape-p t t acc))
            (bar-escape-p
             ;; Bar-escape is on and not a special char.  Read verbatim through it's
             ;; turned off.
             (parse-symbol-name-part x n+1 xl t nil t (cons char acc)))
            ((member char '(#\Space #\( #\) #\Newline #\Tab #\Page #\: #\, #\' #\`))
             ;; Whitespace, paren, colon, comma, quote, backquote, outside of a
             ;; bar escape; end of symbol.  We can stop as long as we've actually
             ;; read some characters.
             (if some-chars-p
                 (mv nil (reverse (coerce acc 'string)) n)
               (mv (concatenate 'string "Near " (error-context x n xl) ": expected to read "
                                "some part of a symbol, but found " (coerce (list char) 'string) ".")
                   "" n)))
            ((or (and (char<= #\a char) (char<= char #\z)))
             ;; lowercase letters outside of bar escape get capitalized
             (parse-symbol-name-part x n+1 xl nil nil t (cons (char-upcase char) acc)))
            (t
             ;; Otherwise add the char verbatim
             (parse-symbol-name-part x n+1 xl nil nil t (cons char acc)))))))

(defun parse-symbol (x n xl base-pkg) ;; ==> (MV ERROR SYMBOL N-PRIME)
  (declare (type string x))

; This extends parse-symbol-name-part to read both parts.  We support keywords,
; etc.  This is definitely not going to handle everything in Common Lisp, but
; whatever.

  (if (= xl n)
      (mv (concatenate 'string "Near " (error-context x n xl) ": end of string while "
                       "trying to parse a symbol.")
          nil n)
    (let ((char (char x n)))
      (if (eql char #\:)
          ;; Starts with a colon.  Maybe it's keyword symbol?
          (b* (((mv error name n)
                (parse-symbol-name-part x (+ n 1) xl nil nil nil nil)))
              (if error
                  (mv error nil n)
                (mv nil (intern-in-package-of-symbol name :keyword) n)))

        ;; Doesn't start with a colon.
        (b* (((mv error part1 n)
              (parse-symbol-name-part x n xl nil nil nil nil))
             ((when error)
              (mv error nil n)))

            (if (and (< (+ n 1) xl)
                     (eql (char x n) #\:)
                     (eql (char x (+ n 1)) #\:))
                ;; "::" is matched.
                (b* (((mv error part2 n)
                      (parse-symbol-name-part x (+ n 2) xl nil nil nil nil))
                     ((when error)
                      (mv error nil n)))
                    ;; Things look pretty good here.  One weird thing we will try
                    ;; to detect is if there are extra colons, e.g.,
                    ;; foo::bar::baz should be disallowed.  We really want a
                    ;; whitespace or paren or quote or something
                    (if (eql (char x n) #\:)
                        (mv (concatenate 'string "Near " (error-context x n xl)
                                         ": Three layers of colons in symbol name?")
                            nil n)
                      (mv nil (intern$ part2 part1) n)))

              ;; Didn't match ::.
              (if (and (< n xl)
                       (eql (char x n) #\:))
                  (mv (concatenate 'string "Near " (error-context x n xl)
                                   ": Lone colon after symbol name?")
                      nil n)

                ;; We seem to have an okay package name, but no ::, so put
                ;; it into the base package.
                (mv nil (intern-in-package-of-symbol part1 base-pkg) n))))))))

;; (defun test (x)
;;   (declare (xargs :mode :program))
;;   (parse-symbol x 0 (length x) 'acl2::foo))

;; (test "foo")
;; (test "bar")
;; (test "123")
;; (test "xdoc::bar)")
;; (test "xdoc::|foo|)")
;; (test "xdoc::bar12 ")
;; (test ":foo)")
;; (test ":|foo|)")
;; (test ":")
;; (test ":||")
;; (test "||:")
;; (test "::|foo|)")
;; (test "acl2:::bar)")
;; (test "acl2::bar)")
;; (test "acl2::bar:")
;; (test "acl2::bar|:|)")

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
      (mv nil (reverse (coerce acc 'string)) n)
    (let ((charN (char x n)))
      (if (member charN chars)
          (mv t (reverse (coerce (cons charN acc) 'string)) n)
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

(defun parse-directive (x n xl base-pkg) ;; ==> (MV ERROR COMMAND ARG N-PRIME)
  ;; Every directive has the form @(command arg)
  ;; Where command and arg are symbols.
  ;; We assume @( has just been read, and N is now pointing right after the open paren.
  (declare (type string x))
  (b* ((n                    (skip-past-ws x n xl))
       ((mv error command n) (parse-symbol x n xl (pkg-witness "XDOC")))
       ((when error)
        (mv error nil nil n))
       (n                    (skip-past-ws x n xl))
       ((mv error arg n)     (parse-symbol x n xl base-pkg)))
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
       (filename  (concatenate 'string
                               (reverse (coerce (file-name-mangle arg nil) 'string))
                               ".xdoc-link"))

       (acc (str::revappend-chars "<srclink file=\"" acc))
       (acc (str::revappend-chars filename acc))
       (acc (str::revappend-chars "\">" acc))
       (acc (simple-html-encode-chars shortname acc))
       (acc (str::revappend-chars "</srclink>" acc))

       ((unless dir)
        (mv acc state))

       (fullpath           (acl2::extend-pathname dir filename state))
       ((mv channel state) (open-output-channel fullpath :character state))
       (state (princ$ *xdoc-link-file-message* channel state))
       (state (newline channel state))
       (state (newline channel state))
       (state (princ$ (coerce shortname 'string) channel state))
       (state (newline channel state))
       (state (close-output-channel channel state)))
      (mv acc state)))

(defun process-body-directive (arg state acc) ;; ===> (MV ACC STATE)

; @(body foo) -- look up the body and pretty-print it in a <code> block.

  (b* ((body           (get-body arg (w state)))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (fmt-to-chars-and-encode "~x0"
                                                (list (cons #\0 body))
                                                state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-def-directive (arg dir state acc) ;; ===> (MV ACC STATE)

; @(def foo) -- look up the definition for foo, pretty-print it in a <code>
; block, along with a source-code link.

  (b* ((def            (get-def arg (w state)))
       (acc            (str::revappend-chars "<p><b>Definition: </b>" acc))
       ((mv acc state) (process-srclink-directive arg dir state acc))
       (acc            (str::revappend-chars "</p>" acc))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (fmt-to-chars-and-encode "~x0"
                                                (list (cons #\0 def))
                                                state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-gdef-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)

; @(gdef foo) -- Look up the definition for foo, pretty-print it as in @def,
; but don't use a source-code link because this is a "Generated Definition" for
; which a tags-search will probably fail.

  (b* ((def            (get-def arg (w state)))
       (acc            (str::revappend-chars "<p><b>Definition: </b>" acc))
       (acc            (sym-mangle arg base-pkg acc))
       (acc            (str::revappend-chars "</p>" acc))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (fmt-to-chars-and-encode "~x0"
                                                (list (cons #\0 def))
                                                state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-thm-directive (arg dir state acc) ;; ===> (MV ACC STATE)

; @(thm foo) -- Look up the theorem named foo, and pretty-print its event along
; with a source link.

  (b* ((theorem        (get-theorem arg (w state)))
       (acc            (str::revappend-chars "<p><b>Theorem: </b>" acc))
       ((mv acc state) (process-srclink-directive arg dir state acc))
       (acc            (str::revappend-chars "</p>" acc))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (fmt-to-chars-and-encode "~x0"
                                                (list (cons #\0 theorem))
                                                state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-gthm-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)

; @(gthm foo) -- Like @(thm foo), but don't provide a source link since this is
; a generated theorem.

  (b* ((theorem        (get-theorem arg (w state)))
       (acc            (str::revappend-chars "<p><b>Theorem: </b>" acc))
       (acc            (sym-mangle arg base-pkg acc))
       (acc            (str::revappend-chars "</p>" acc))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (fmt-to-chars-and-encode "~x0"
                                                (list (cons #\0 theorem))
                                                state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-formals-directive (arg state acc) ;; ===> (MV ACC STATE)

; @(formals foo) -- just find the formals for foo and print them without any
; extra formatting.

  (b* ((formals        (get-formals arg (w state)))
       ((mv acc state) (fmt-to-chars-and-encode "~x0"
                                                (list (cons #\0 formals))
                                                state acc)))
      (mv acc state)))

(defun process-call-directive (arg state acc) ;; ===> (MV ACC STATE)

; @(call foo) -- find the formals to foo and insert <tt>(foo x y z)</tt>.
; BOZO consider adding an emacs link.

  (b* ((formals        (get-formals arg (w state)))
       (call           (cons arg formals))
       (acc            (str::revappend-chars "<tt>" acc))
       ((mv acc state) (fmt-to-chars-and-encode "~x0"
                                                (list (cons #\0 call))
                                                state acc))
       (acc            (str::revappend-chars "</tt>" acc)))
      (mv acc state)))

(defun process-ccall-directive (arg state acc) ;; ===> (MV ACC STATE)

; @(ccall foo) -- "code call" is like @(call foo), but uses <code> instead
; of <tt> tags.

  (b* ((formals        (get-formals arg (w state)))
       (call           (cons arg formals))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (fmt-to-chars-and-encode "~x0"
                                                (list (cons #\0 call))
                                                state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-measure-directive (arg state acc) ;; ===> (MV ACC STATE)

; @(measure foo) -- find the measure for foo and print it without any extra
; formatting.

  (b* ((measure        (get-measure arg (w state)))
       ((mv acc state) (fmt-to-chars-and-encode "~x0"
                                                (list (cons #\0 measure))
                                                state acc)))
      (mv acc state)))


(defun process-directive (command arg dir base-pkg state acc) ;; ===> (MV ACC STATE)

; Command and Arg are the already-parsed symbols we have read from the
; documentation string.  Carry out whatever directive we've been asked to do.
; DIR is the output dir.  Acc is the accumulator for our output characters.

  (case command
    (def       (process-def-directive arg dir state acc))
    (thm       (process-thm-directive arg dir state acc))
    (srclink   (process-srclink-directive arg dir state acc))
    (gdef      (process-gdef-directive arg base-pkg state acc))
    (gthm      (process-gthm-directive arg base-pkg state acc))
    (body      (process-body-directive arg state acc))
    (formals   (process-formals-directive arg state acc))
    (measure   (process-measure-directive arg state acc))
    (call      (process-call-directive arg state acc))
    (ccall     (process-ccall-directive arg state acc))
    (url       (process-url-directive arg state acc))
    (see       (process-see-directive arg base-pkg state acc))
    (csee      (process-see-cap-directive arg base-pkg state acc))
    (sym       (process-sym-directive arg base-pkg state acc))
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

; We assume we're inside a <code> block.  We read until a < character is
; encountered, gathering the characters we see and tracking whether each
; newline is followed by a space.

  (b* (((when (>= n xl))
        (mv n acc always-spacep))

       (char-n (char x n))
       ((when (eql char-n #\<))
        ;; We assume this is the </code> tag and stop reading.
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
  (reverse (coerce (transform-code-segments x 0 (length x) nil) 'string)))

;; (transform-code 
;; "<p>This is 
;; some regular text</p>
;; <code>
;;   blah1
;; blah2
;;   blah3
;; </code>
;; <p>And more text</p>")

(defun preprocess-aux (x n xl dir base-pkg state acc)
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
               (preprocess-aux x (+ n 2) xl dir base-pkg state (cons #\@ acc)))

              ((and (< (+ n 1) xl)
                    (eql (char x (+ n 1)) #\())
               ;; @( --> directive
               (b* (((mv error command arg n) (parse-directive x (+ n 2) xl base-pkg))
                    ((when error)
                     (prog2$ (cw "; xdoc error: ~x0.~%" error)
                             (mv acc state)))
                    ((mv acc state)
                     (process-directive command arg dir base-pkg state acc)))
                 (preprocess-aux x n xl dir base-pkg state acc)))

              (t
               ;; @ sign in some other context.
               (preprocess-aux x (+ n 1) xl dir base-pkg state (cons #\@ acc)))))

       ((when (eql char #\Newline))
        ;; Gross hack #1: eat initial newlines from the start of a <code>
        ;; block, since otherwise they look ugly when firefox renders them.
        (if (just-started-code-p acc)
            (if (and (< (+ n 1) xl)
                     (eql (char x (+ n 1)) #\Newline))
                ;; Avoid eating multiple newlines at the start of a code block.
                (preprocess-aux x (+ n 2) xl dir base-pkg state (cons #\Newline acc))
              (preprocess-aux x (+ n 1) xl dir base-pkg state acc))
          ;; Gross hack #2: the XSLT transformer in firefox seems to have some
          ;; problems if there aren't spaces at the end of lines, e.g., it will
          ;; run together the hover-text in the hierarchical description in
          ;; preview.html.  Fix by putting a space before newlines.  Horrible.
          (preprocess-aux x (+ n 1) xl dir base-pkg state (list* #\Newline #\Space acc)))))

    ;; Otherwise just keep the char and keep going.
    (preprocess-aux x (+ n 1) xl dir base-pkg state (cons char acc))))

(defun preprocess-main (x dir base-pkg state acc)
  (declare (type string x))
  (b* ((current-pkg    (acl2::f-get-global 'current-package state))
       ;; Temporarily make "fmt" print as if it's in base-pkg.
       ((mv & & state) (acl2::set-current-package (symbol-package-name base-pkg) state))
       (x              (transform-code x))
       ((mv acc state) (preprocess-aux x 0 (length x) dir base-pkg state acc))
       ;; Restore base-pkg for whoever called us.
       ((mv & & state) (acl2::set-current-package current-pkg state)))
      (mv acc state)))




