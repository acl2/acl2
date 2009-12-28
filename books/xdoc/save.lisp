; XDOC Documentation System for ACL2
; Copyright (C) 2009 Centaur Technology
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "XDOC")
(include-book "defxdoc")
(include-book "str/top" :dir :system)
(include-book "unicode/read-file-characters" :dir :system)
(include-book "finite-set-theory/osets/sets" :dir :system)
(set-state-ok t)
(program)


; A stupid file copy routine, so we can copy our style files, etc.  We avoid
; using "system" because of memory problems with forking on huge images.

(defun stupid-copy-file-aux (in out state)
  ;; In, out are channels.
  (mv-let (byte state)
          (read-byte$ in state)
          (if (not byte)
              state
            (let ((state (write-byte$ byte out state)))
              (stupid-copy-file-aux in out state)))))

(defun stupid-copy-file (src dest state)
  (b* (((mv in state)  (open-input-channel src :byte state))
       ((mv out state) (open-output-channel dest :byte state))
       (state          (stupid-copy-file-aux in out state))
       (state          (close-input-channel in state))
       (state          (close-output-channel out state)))
      state))

(defun stupid-copy-files (srcdir filenames destdir state)
  (if (atom filenames)
      state
    (b* ((srcfile  (acl2::extend-pathname srcdir (car filenames) state))
         (destfile (acl2::extend-pathname destdir (car filenames) state))
         (state    (stupid-copy-file srcfile destfile state)))
        (stupid-copy-files srcdir (cdr filenames) destdir state))))


; XDOC Preprocessor

(defun in-package-p (sym base-pkg)
  (equal (intern-in-package-of-symbol (symbol-name sym) base-pkg)
         sym))
  
(defun get-formals (fn world)
  (or (getprop fn 'formals nil 'current-acl2-world world)
      (cw "; xdoc note: get-formals failed for ~s0::~s1.~%" 
          (symbol-package-name fn) (symbol-name fn))
      (concatenate 'string 
                   "Error getting formals for " 
                   (symbol-package-name fn)
                   "::" 
                   (symbol-name fn))))

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
  (if (getprop fn 'formals nil 'current-acl2-world world)
      (getprop fn 'guard nil 'current-acl2-world world)
    (or (cw "; xdoc note: get-guard failed for ~x0.~%" fn)
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

(defun get-def (fn world)
  (let ((def (acl2::get-def fn world)))
    (or (and def
             (cons 'defun def))
        (cw "; xdoc note: get-def failed for ~x0.~%" fn)
        (concatenate 'string 
                     "Error getting definition for "
                     (symbol-package-name fn)
                     "::"
                     (symbol-name fn)))))

(defun get-theorem (name world)
  (let ((thm (acl2::get-event name world)))
    (or thm
        (cw "; xdoc note: get-theorem failed for ~x0.~%" name)
        (concatenate 'string 
                     "Error getting theorem for " 
                     (symbol-package-name name)
                     "::" 
                     (symbol-name name)))))


;; (get-formals 'binary-append (w state))
;; (get-measure 'binary-append (w state))
;; (get-guard 'binary-append (w state))
;; (get-body 'binary-append (w state))
;; (get-def 'binary-append (w state))
;; (get-theorem 'acl2::car-cons (w state))


(defun funny-char-code (x acc)
  (declare (type character x))
  (let* ((code  (char-code x))
         (high  (ash code -4))
         (low   (logand code #xF)))
    (list* (digit-to-char high)
           (digit-to-char low)
           acc)))

(defun file-name-mangle-aux (x n xl acc)
  ;; colons become two underscores.
  ;; funny characters become _[code], somewhat like url encoding
  (declare (type string x))
  (if (= n xl)
      acc
    (let ((char (char x n)))
      (cond ((or (and (char<= #\a char) (char<= char #\z))
                 (and (char<= #\A char) (char<= char #\Z))
                 (and (char<= #\0 char) (char<= char #\9))
                 (eql char #\-)
                 (eql char #\.))
             (file-name-mangle-aux x (+ n 1) xl (cons char acc)))
            ((eql char #\:)
             (file-name-mangle-aux x (+ n 1) xl (revappend '(#\_ #\_) acc)))
            (t
             (file-name-mangle-aux x (+ n 1) xl (funny-char-code char (cons #\_ acc))))))))

(defun file-name-mangle (x acc)
  (declare (type symbol x))
  (let ((str (concatenate 'string 
                          (symbol-package-name x)
                          "::"
                          (symbol-name x))))
    (file-name-mangle-aux str 0 (length str) acc)))




; Command recognition / parsing.
;
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

(defun error-context (x n xl) ;; ==> STRING describing location of error
  (declare (type string x))
  (let ((min (nfix (- n 20)))
        (max (min (+ n 20) xl)))
    (subseq x min max)))

(defun parse-symbol-name-part (x n xl bar-escape-p slash-escape-p some-chars-p acc) ;; ==> (MV ERROR NAME N-PRIME)
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
  (declare (type string x))
  ;; Note: @( must have just been read.  N is now pointing after the open paren.
  (b* ((n                    (skip-past-ws x n xl))
       ((mv error command n) (parse-symbol x n xl 'xdoc))
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


(defun fmt-to-chars (string alist state) ;; ==> STATE
  ;; We can't use fmt to print directly to a string, which sucks.  So, we print
  ;; to a temporary file and read it back in.  This is truly horrible, but it's 
  ;; a lot easier than reimplementing ppr.
  (b* (((mv channel state)  (open-output-channel ".fmt-to-chars.tmp" :character state))
       ((mv & state)        (fmt string alist channel state nil))
       (state               (close-output-channel channel state))
       ((mv data state)     (acl2::read-file-characters ".fmt-to-chars.tmp" state)))
      (mv data state)))

(defun simple-html-encode-chars (x acc)
  (if (atom x)
      acc
    (let ((acc (case (car x)
                 (#\< (revappend str::*html-less* acc))
                 (#\> (revappend str::*html-greater* acc))
                 (#\& (revappend str::*html-amp* acc))
                 (#\" (revappend str::*html-quote* acc))
                 (t   (cons (car x) acc)))))
      (simple-html-encode-chars (cdr x) acc))))

(defun fmt-to-chars-and-encode (string alist state acc) ;; ==> (MV ACC-PRIME STATE)
  (mv-let (data state) 
          (fmt-to-chars string alist state)
          (if (stringp data)
              (prog2$ 
               (cw "; xdoc note: error reading fmt-to-chars.tmp; using filler instead.~%")
               (mv (str::revappend-chars "[[ error reading fmt-to-chars.tmp ]]" acc)
                   state))
            ;; We cdr the data because fmt puts in a newline.
            (let ((acc (simple-html-encode-chars (cdr data) acc)))
              (mv acc state)))))



(defun sym-mangle (x base-pkg acc)
  (let* ((acc (if (in-package-p x base-pkg)
                  acc
                (list* #\: #\:
                       (simple-html-encode-chars (coerce (string-downcase (symbol-package-name x)) 'list) acc)))))
    (simple-html-encode-chars (coerce (string-downcase (symbol-name x)) 'list) acc)))

(defun upcase-first-letter (x)
  (declare (type string x))
  (if (equal x "")
      x
    (concatenate 'string 
                 (coerce (list (char-upcase (char x 0))) 'string)
                 (subseq x 1 nil))))

(defun sym-mangle-cap (x base-pkg acc)
  (if (in-package-p x base-pkg)
      (let ((name-cap (upcase-first-letter (string-downcase (symbol-name x)))))
        (simple-html-encode-chars (coerce name-cap 'list) acc))
    (let* ((pkg-cap (upcase-first-letter (string-downcase (symbol-package-name x))))
           (acc (list* #\: #\: (simple-html-encode-chars (coerce pkg-cap 'list) acc))))
      (simple-html-encode-chars (coerce (string-downcase (symbol-name x)) 'list) acc))))

(defun process-see-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)
  (b* ((acc            (str::revappend-chars "<see topic=\"" acc))
       (acc            (file-name-mangle arg acc))
       (acc            (str::revappend-chars "\">" acc))
       (acc            (sym-mangle arg base-pkg acc))
       (acc            (str::revappend-chars "</see>" acc)))
      (mv acc state)))

(defun process-see-cap-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)
  (b* ((acc            (str::revappend-chars "<see topic=\"" acc))
       (acc            (file-name-mangle arg acc))
       (acc            (str::revappend-chars "\">" acc))
       (acc            (sym-mangle-cap arg base-pkg acc))
       (acc            (str::revappend-chars "</see>" acc)))
      (mv acc state)))

(defun process-url-directive (arg state acc) ;; ===> (MV ACC STATE)
  (b* ((acc            (file-name-mangle arg acc)))
      (mv acc state)))

(defun process-sym-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)
  (b* ((acc            (sym-mangle arg base-pkg acc)))
      (mv acc state)))

(defun process-sym-cap-directive (arg base-pkg state acc) ;; ===> (MV ACC STATE)
  (b* ((acc            (sym-mangle-cap arg base-pkg acc)))
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
;   2. Write a .xdoc-link file to dir for this tag.
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
  (b* ((body           (get-body arg (w state)))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (fmt-to-chars-and-encode "~x0" 
                                                (list (cons #\0 body))
                                                state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-def-directive (arg dir state acc) ;; ===> (MV ACC STATE)
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
  (b* ((formals        (get-formals arg (w state)))
       ((mv acc state) (fmt-to-chars-and-encode "~x0" 
                                                (list (cons #\0 formals))
                                                state acc)))
      (mv acc state)))

(defun process-call-directive (arg state acc) ;; ===> (MV ACC STATE)
  ;; BOZO consider adding an emacs link.
  (b* ((formals        (get-formals arg (w state)))
       (call           (cons arg formals))
       (acc            (str::revappend-chars "<tt>" acc))
       ((mv acc state) (fmt-to-chars-and-encode "~x0" 
                                                (list (cons #\0 call))
                                                state acc))
       (acc            (str::revappend-chars "</tt>" acc)))
      (mv acc state)))

(defun process-measure-directive (arg state acc) ;; ===> (MV ACC STATE)
  (b* ((measure        (get-measure arg (w state)))
       ((mv acc state) (fmt-to-chars-and-encode "~x0" 
                                                (list (cons #\0 measure))
                                                state acc)))
      (mv acc state)))


(defun process-directive (command arg dir base-pkg state acc) ;; ===> (MV ACC STATE)
  (case command
    (def       (process-def-directive arg dir state acc))
    (thm       (process-thm-directive arg dir state acc))
    (srclink   (process-srclink-directive arg dir state acc))

    (gdef      (process-gdef-directive arg base-pkg state acc))
    (gthm      (process-gthm-directive arg base-pkg state acc))

    (body      (process-body-directive arg state acc))
    (formals   (process-formals-directive arg state acc))
    (call      (process-call-directive arg state acc))
    (measure   (process-measure-directive arg state acc))
    (see       (process-see-directive arg base-pkg state acc))
    (csee      (process-see-cap-directive arg base-pkg state acc))
    (url       (process-url-directive arg state acc))
    (sym       (process-sym-directive arg base-pkg state acc))
    (csym      (process-sym-cap-directive arg base-pkg state acc))
    (otherwise 
     (prog2$ 
      (cw "; xdoc error: unknown directive ~x0.~%" command)
      (let* ((acc (str::revappend-chars "[[ unknown directive " acc))
             (acc (str::revappend-chars (symbol-name command) acc))
             (acc (str::revappend-chars "]]" acc)))
        (mv acc state))))))

(defun preprocess-aux (x n xl dir base-pkg state acc) ;; ==> (MV ACC STATE)
  (declare (type string x))
  (if (= n xl)
      (mv acc state)
    (let ((char (char x n)))
      (if (eql char #\@)
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
                 (preprocess-aux x (+ n 1) xl dir base-pkg state (cons #\@ acc))))
        (preprocess-aux x (+ n 1) xl dir base-pkg state (cons char acc))))))

(defun preprocess-main (x dir base-pkg state acc)
  (declare (type string x))
  (b* ((current-pkg    (acl2::f-get-global 'current-package state))
       ((mv & & state) (acl2::set-current-package (symbol-package-name base-pkg) state))
       ((mv acc state) (preprocess-aux x 0 (length x) dir base-pkg state acc))
       ((mv & & state) (acl2::set-current-package current-pkg state)))
      (mv acc state)))


(defun add-parents (parents base-pkg acc)
  (if (atom parents)
      acc
    (let* ((acc (str::revappend-chars "<parent topic=\"" acc))
           (acc (file-name-mangle (car parents) acc))
           (acc (str::revappend-chars "\">" acc))
           (acc (sym-mangle-cap (car parents) base-pkg acc))
           (acc (str::revappend-chars "</parent>" acc))
           (acc (cons #\Newline acc)))
      (add-parents (cdr parents) base-pkg acc))))

(defun preprocess-topic (x dir state)
  (b* ((name     (cdr (assoc :name x)))
       (base-pkg (cdr (assoc :base-pkg x)))
       (short    (or (cdr (assoc :short x)) ""))
       (long     (or (cdr (assoc :long x)) ""))
       (parents  (cdr (assoc :parents x)))
       ((unless (symbolp name))
        (mv (er hard? 'preprocess-topic "Name is not a string: ~x0.~%" x)
            state))
       ((unless (symbolp base-pkg))
        (mv (er hard? 'preprocess-topic "Base-pkg is not a symbol: ~x0.~%" base-pkg)
            state))
       ((unless (symbol-listp parents))
        (mv (er hard? 'preprocess-topic "Parents are not a symbol-listp: ~x0.~%" x)
            state))
       ((unless (stringp short))
        (mv (er hard? 'preprocess-topic "Short is not a string: ~x0.~%" x)
            state))
       ((unless (stringp long))
        (mv (er hard? 'preprocess-topic "Long is not a string: ~x0.~%" x)
            state))
       (acc    nil)
       (acc    (str::revappend-chars "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "<?xml-stylesheet type=\"text/xsl\" href=\"xdoc-to-dynamic-html.xsl\"?>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "<page>" acc))
       (acc    (str::revappend-chars "<topic name=\"" acc))
       (acc    (sym-mangle-cap name base-pkg acc))
       (acc    (str::revappend-chars "\">" acc))
       (acc    (cons #\Newline acc))
       (acc    (add-parents parents base-pkg acc))
       (acc    (str::revappend-chars "<short>" acc))
       ((mv acc state) (preprocess-main short dir base-pkg state acc))
       (acc    (str::revappend-chars "</short>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "<long>" acc))
       ((mv acc state) (preprocess-main long dir base-pkg state acc))
       (acc    (str::revappend-chars "</long>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "</topic>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "</page>" acc))
       (acc    (cons #\Newline acc)))
      (mv (reverse (coerce acc 'string)) state)))

(defun save-topic (x dir state)
  (b* ((name               (cdr (assoc :name x)))
       (-                  (cw "Saving ~s0::~s1.~%" (symbol-package-name name) (symbol-name name)))
       ((mv text state)    (preprocess-topic x dir state))
       (filename           (concatenate 'string 
                                        (reverse (coerce (file-name-mangle name nil) 'string))
                                        ".xml"))
       (fullpath           (acl2::extend-pathname dir filename state))
       ((mv channel state) (open-output-channel fullpath :character state))
       (state              (princ$ text channel state))
       (state              (close-output-channel channel state)))
      state))

(defun save-topics-aux (x dir state)
  (if (atom x)
      state
    (let ((state (save-topic (car x) dir state)))
      (save-topics-aux (cdr x) dir state))))


; Flat index.

(defun index-add-topic (x dir index-pkg state acc)
  (b* ((name     (cdr (assoc :name x)))
       (short    (cdr (assoc :short x)))
       (base-pkg (cdr (assoc :base-pkg x)))
       (acc   (str::revappend-chars "<index_entry>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "<index_head><see topic=\"" acc))
       (acc   (file-name-mangle name acc))
       (acc   (str::revappend-chars "\">" acc))
       (acc   (sym-mangle-cap name index-pkg acc))
       (acc   (str::revappend-chars "</see>" acc))
       (acc   (str::revappend-chars "</index_head>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "<index_body>" acc))
       (acc   (cons #\Newline acc))
       ((mv acc state) (preprocess-main short dir base-pkg state acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "</index_body>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "</index_entry>" acc))
       (acc   (cons #\Newline acc)))
      (mv acc state)))

(defun index-add-topics (x dir index-pkg state acc)
  (if (atom x)
      (mv acc state)
    (b* (((mv acc state) (index-add-topic (car x) dir index-pkg state acc)))
        (index-add-topics (cdr x) dir index-pkg state acc))))

(defun save-index (x dir index-pkg state)
  (b* (;; The main body for both index pages is the same.
       (acc nil)
       (acc (str::revappend-chars "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "<?xml-stylesheet type=\"text/xsl\" href=\"xdoc-to-dynamic-html.xsl\"?>" acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "<page>" acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "<index>" acc))
       (acc (cons #\Newline acc))
       ((mv acc state) (index-add-topics x dir index-pkg state acc))
       (acc (str::revappend-chars "</index>" acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "</page>" acc))
       (filename (acl2::extend-pathname dir "index.xml" state))
       ((mv channel state) (open-output-channel filename :character state))
       (state (princ$ (reverse (coerce acc 'string)) channel state))
       (state (close-output-channel channel state)))
      state))


; Hierarchical index


(defun normalize-parents (x)
  ;; Given an xdoc entry, remove duplicate parents and self-parents.
  (let* ((name    (cdr (assoc :name x)))
         (parents (cdr (assoc :parents x)))
         (orig    parents)
         (parents (if (member-equal name parents)
                      (prog2$
                       (cw "; xdoc note: removing self-referencing :parents entry for ~x0.~%" name)
                       (remove-equal name parents))
                    parents))
         (parents (if (no-duplicatesp-equal parents)
                      parents
                    (prog2$ 
                     (cw "; xdoc note: removing duplicate :parents for ~x0.~%" name)
                     (remove-duplicates-equal parents)))))
    (if (equal parents orig)
        x
      (acons :parents parents x))))

(defun normalize-parents-list (x)
  (if (atom x)
      nil
    (cons (normalize-parents (car x))
          (normalize-parents-list (cdr x)))))

(defun find-roots (x)
  ;; gather names of all doc topics which have no parents.
  (if (atom x)
      nil
    (if (not (cdr  (assoc :parents (car x))))
        (cons (cdr (assoc :name (car x)))
              (find-roots (cdr x)))
      (find-roots (cdr x)))))

(defun find-children-aux (par x)
  ;; gather names of all xdoc topics in x which have parent par.
  (if (atom x)
      nil
    (if (member-equal par (cdr (assoc :parents (car x))))
        (cons (cdr (assoc :name (car x)))
              (find-children-aux par (cdr x)))
      (find-children-aux par (cdr x)))))

(defun find-children (par x)
  ;; gather names of children topics and sort them.
  (sets::mergesort (find-children-aux par x)))

(defun find-topic (name x)
  (if (atom x)
      nil
    (if (equal (cdr (assoc :name (car x))) name)
        (car x)
      (find-topic name (cdr x)))))


(mutual-recursion

 (defun make-hierarchy-aux (path dir base-pkg all id acc state)

; - Path is our current location in the hierarchy, and is used to avoid loops.
;   (The first element in path is the current topic we are on.)
;
; - Base-pkg is just used for symbol printing
;
; - All is the list of all xdoc documentation topics.
;
; - ID is a number that we assign to this topic entry for hiding with
;   JavaScript.  (We don't use names because the topics might be repeated under
;   different parents).
;
; - Acc is the character list we are building.
;
; We return (MV ACC-PRIME ID-PRIME STATE)

   (b* ((name     (car path))
        (id-chars (list* #\t #\o #\p #\i #\c #\- (explode-atom id 10)))
        (depth    (len path))
        (children (find-children name all))
        (kind     (cond ((not children) "leaf")
                        ((< depth 2) "show")
                        (t "hide")))

        ((when    (member-equal name (cdr path)))
         (prog2$ 
          (er hard? 'make-hierarchy "Circular topic hierarchy.  Path is ~x0.~%" path)
          (mv acc id state)))
        
        (topic (find-topic name all))
        (short (cdr (assoc :short topic)))

        (acc (str::revappend-chars "<hindex topic=\"" acc))
        (acc (file-name-mangle name acc))
        (acc (str::revappend-chars "\" id=\"" acc))
        (acc (revappend id-chars acc))
        (acc (str::revappend-chars "\" kind=\"" acc))
        (acc (str::revappend-chars kind acc))
        (acc (str::revappend-chars "\">" acc))
        (acc (cons #\Newline acc))

        (acc (str::revappend-chars "<hindex_name>" acc))
        (acc (sym-mangle-cap name base-pkg acc))
        (acc (str::revappend-chars "</hindex_name>" acc))
        (acc (cons #\Newline acc))

        (acc (str::revappend-chars "<hindex_short id=\"" acc))
        (acc (revappend id-chars acc))
        (acc (str::revappend-chars "\">" acc))
        ((mv acc state) (preprocess-main short dir base-pkg state acc))
        (acc (str::revappend-chars "</hindex_short>" acc))

        (acc (str::revappend-chars "<hindex_children id=\"" acc))
        (acc (revappend id-chars acc))
        (acc (str::revappend-chars "\" kind=\"" acc))
        (acc (str::revappend-chars kind acc))
        (acc (str::revappend-chars "\">" acc))
        (acc (cons #\Newline acc))

        (id   (+ id 1))
        ((mv acc id state) 
         (make-hierarchy-list-aux children path dir base-pkg all id acc state))
        (acc (str::revappend-chars "</hindex_children>" acc))
        (acc (str::revappend-chars "</hindex>" acc))
        (acc (cons #\Newline acc)))
       (mv acc id state)))
       
 (defun make-hierarchy-list-aux (children path dir base-pkg all id acc state)
   
; - Children are the children of this path.
; - Path is our current location in the hierarchy.
; -

   (if (atom children)
       (mv acc id state)
     (b* (((mv acc id state)
           (make-hierarchy-aux (cons (car children) path) dir base-pkg all id acc state))
          ((mv acc id state)
           (make-hierarchy-list-aux (cdr children) path dir base-pkg all id acc state)))
         (mv acc id state)))))

(defun save-hierarchy (x dir base-pkg state)
  ; X is all topics.
  (b* ((x     (normalize-parents-list x))
       (roots (sets::mergesort (find-roots x)))
       (acc   nil)
       (acc   (str::revappend-chars "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "<?xml-stylesheet type=\"text/xsl\" href=\"xdoc-to-dynamic-html.xsl\"?>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "<page>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "<hindex_root>" acc))
       (acc   (cons #\Newline acc))
       ((mv acc & state) (make-hierarchy-list-aux roots nil dir base-pkg x 0 acc state))
       (acc   (str::revappend-chars "</hindex_root>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "</page>" acc))
       (acc   (cons #\Newline acc))
       (filename (acl2::extend-pathname dir "topics.xml" state))
       ((mv channel state) (open-output-channel filename :character state))
       (state (princ$ (reverse (coerce acc 'string)) channel state))
       (state (close-output-channel channel state)))
      state))


(make-event 
 (let ((cbd (cbd)))
   (value `(defconst *xdoc-root-dir* ',cbd))))

(defun save-topics (x dir index-pkg state)
  (cond ((not (stringp dir))
         (prog2$ (er hard? 'save-topics "Dir must be a string, but is: ~x0.~%" dir)
                 state))
        ((atom x)
         (prog2$ (cw "; xdoc note: no topics are documented.~%")
                 state))
        (t
         (b* ((-        (cw "; Copying skeleton files~%"))
              (state    (time$ (stupid-copy-files *xdoc-root-dir*
                                                  (list "Makefile-trans"
                                                        "xdoc.css"
                                                        "xdoc.js"
                                                        "xdoc-to-text.xsl"
                                                        "frames.html"
                                                        "xdoc-to-html-aux.xsl"
                                                        "xdoc-to-full-index.xsl"
                                                        "xdoc-to-brief-index.xsl"
                                                        "xdoc-to-dynamic-html.xsl"
                                                        "xdoc-to-static-html.xsl"
                                                        "xdoc-to-topic-index.xsl"
                                                        "plus.png"
                                                        "minus.png"
                                                        "leaf.png")
                                                  dir state)))
              ;; Note: generate the index after the topic files, so that errors
              ;; in short messages will be seen there.
              (-        (cw "; Preprocess and save ~x0 topics.~%" (len x)))
              (state    (time$ (save-topics-aux x dir state)))
              (-        (cw "; Generate index.xml"))
              (state    (time$ (save-index x dir index-pkg state)))
              (-        (cw "; Generate topics.xml"))
              (state    (time$ (save-hierarchy x dir index-pkg state))))
             state))))

(defmacro save (dir &key (index-pkg 'acl2::foo))
  `(save-topics (get-xdoc-table (w state)) ,dir ',index-pkg state))

           
