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
  (if (getprop fn 'formals nil 'current-acl2-world world)
      (let ((formals (get-formals fn world))
            (body    (get-body fn world))
            (guard   (get-guard fn world)))
        `(defun ,fn ,formals
           ,@(or (not guard) 
                 `((declare (xargs :guard ,guard))))
           ,body))
    (or (cw "; xdoc note: get-def failed for ~x0.~%" fn)
        (concatenate 'string 
                     "Error getting definition for "
                     (symbol-package-name fn)
                     "::"
                     (symbol-name fn)))))

(defun get-theorem (name world)
  ;; This gets the original, normalized or non-normalized body based on what
  ;; the user typed for the :normalize xarg.  The use of "last" skips past 
  ;; any other :definition rules that have been added since then.
  (let ((thm (getprop name 'untranslated-theorem nil 'current-acl2-world world)))
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
                          (symbol-name x)
                          ".xml")))
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
  (let ((min (nfix (- n 5)))
        (max (min (+ n 5) xl)))
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
        (mv (concatenate 'string "In " (symbol-name command) " directive, expected ) after " arg 
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

(defun process-body-directive (arg state acc) ;; ===> (MV ACC STATE)
  (b* ((body           (get-body arg (w state)))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (fmt-to-chars-and-encode "~x0" 
                                                (list (cons #\0 body))
                                                state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-def-directive (arg state acc) ;; ===> (MV ACC STATE)
  (b* ((def            (get-def arg (w state)))
       (acc            (str::revappend-chars "<code>" acc))
       ((mv acc state) (fmt-to-chars-and-encode "~x0" 
                                                (list (cons #\0 def))
                                                state acc))
       (acc            (str::revappend-chars "</code>" acc)))
      (mv acc state)))

(defun process-thm-directive (arg state acc) ;; ===> (MV ACC STATE)
  (b* ((theorem        (get-theorem arg (w state)))
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

(defun process-measure-directive (arg state acc) ;; ===> (MV ACC STATE)
  (b* ((measure        (get-measure arg (w state)))
       ((mv acc state) (fmt-to-chars-and-encode "~x0" 
                                                (list (cons #\0 measure))
                                                state acc)))
      (mv acc state)))

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

(defun process-directive (command arg base-pkg state acc) ;; ===> (MV ACC STATE)
  (case command
    (def       (process-def-directive arg state acc))
    (body      (process-body-directive arg state acc))
    (thm       (process-thm-directive arg state acc))
    (formals   (process-formals-directive arg state acc))
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

(defun preprocess-aux (x n xl base-pkg state acc) ;; ==> (MV ACC STATE)
  (declare (type string x))
  (if (= n xl)
      (mv acc state)
    (let ((char (char x n)))
      (if (eql char #\@)
          (cond ((and (< (+ n 1) xl)
                      (eql (char x (+ n 1)) #\@))
                 ;; @@ --> @
                 (preprocess-aux x (+ n 2) xl base-pkg state (cons #\@ acc)))

                ((and (< (+ n 1) xl)
                      (eql (char x (+ n 1)) #\())
                 ;; @( --> directive
                 (b* (((mv error command arg n) (parse-directive x (+ n 2) xl base-pkg))
                      ((when error)
                       (prog2$ (cw "; xdoc error: ~x0.~%" error)
                               (mv acc state)))
                      ((mv acc state)
                       (process-directive command arg base-pkg state acc)))
                     (preprocess-aux x n xl base-pkg state acc)))

                (t
                 ;; @ sign in some other context.
                 (preprocess-aux x (+ n 1) xl base-pkg state (cons #\@ acc))))
        (preprocess-aux x (+ n 1) xl base-pkg state (cons char acc))))))

(defun preprocess-main (x base-pkg state acc)
  (declare (type string x))
  (b* ((current-pkg    (acl2::f-get-global 'current-package state))
       ((mv & & state) (acl2::set-current-package (symbol-package-name base-pkg) state))
       ((mv acc state) (preprocess-aux x 0 (length x) base-pkg state acc))
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

(defun preprocess-topic (x state)
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
       (acc    (str::revappend-chars "<?xml-stylesheet type=\"text/xsl\" href=\"xdoc.xsl\"?>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "<topic name=\"" acc))
       (acc    (sym-mangle-cap name base-pkg acc))
       (acc    (str::revappend-chars "\">" acc))
       (acc    (cons #\Newline acc))
       (acc    (add-parents parents base-pkg acc))
       (acc    (str::revappend-chars "<short>" acc))
       ((mv acc state) (preprocess-main short base-pkg state acc))
       (acc    (str::revappend-chars "</short>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "<long>" acc))
       ((mv acc state) (preprocess-main long base-pkg state acc))
       (acc    (str::revappend-chars "</long>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "</topic>" acc))
       (acc    (cons #\Newline acc)))
      (mv (reverse (coerce acc 'string)) state)))

(defun save-topic (x dir state)
  (b* ((name               (cdr (assoc :name x)))
       (-                  (cw "Saving ~s0::~s1.~%" (symbol-package-name name) (symbol-name name)))
       ((mv text state)    (preprocess-topic x state))
       (filename           (reverse (coerce (file-name-mangle name nil) 'string)))
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

(make-event 
 (let ((cbd (cbd)))
   (value `(defconst *xdoc-root-dir* ',cbd))))

(defun save-topics (x dir state)
  (cond ((not (stringp dir))
         (prog2$ (er hard? 'save-topics "Dir must be a string, but is: ~x0.~%" dir)
                 state))
        ((atom x)
         (prog2$ (cw "; xdoc note: no topics are documented.~%")
                 state))
        (t
         (b* ((-        (cw "; Copying xdoc.css and xdoc.xsl~%"))
              (css-in   (acl2::extend-pathname *xdoc-root-dir* "xdoc.css" state))
              (css-out  (acl2::extend-pathname dir "xdoc.css" state))
              (state    (stupid-copy-file css-in css-out state))
              (xsl-in   (acl2::extend-pathname *xdoc-root-dir* "xdoc.xsl" state))
              (xsl-out  (acl2::extend-pathname dir "xdoc.xsl" state))
              (state    (stupid-copy-file xsl-in xsl-out state))
              (-        (cw "; Preprocess and save ~x0 topics.~%" (len x))))
             (time$ (save-topics-aux x dir state))))))

(defmacro save (dir)
  `(save-topics (get-xdoc-table (w state)) ,dir state))

           
