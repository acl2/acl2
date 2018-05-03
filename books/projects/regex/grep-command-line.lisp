; Copyright (C) 2004, Regents of the University of Texas
; Written by Sol Swords
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

;; (local (include-book "defsum-thms"))
;; (include-book "defsum")

(include-book "tools/defsum" :dir :system)
(include-book "regex-fileio")
(include-book "regex-chartrans")
(program)
(set-state-ok t)

(defsum grep-output-mode
  (grep-output-count) ;; -c --count
  (grep-output-match) ;; -o --only-matching
  (grep-output-line)
  (grep-output-filename) ;; -l --files-with-matches
  (grep-output-non-matching-filename) ;; -L --files-without-match
  (grep-output-silent) ;; -q --quiet --silent
  )

(defsum grep-color-mode ;; --color --colour
  (grep-color-never)
  (grep-color-always)
  (grep-color-auto))


(defsum grep-pattern-input
  (grep-pattern-string (stringp pattern)) ;; -e --regexp
  (grep-pattern-file (stringp filename)) ;; -f --file
  (grep-pattern-none-yet))

(defsum grep-translation
  (grep-translation-none)
  (grep-translation-ignore-case) ;; -i --ignore-case -y
  )

(defsum grep-overall-mode
  (grep-mode-help) ;; --help
  (grep-mode-version) ;; -V --version
  (grep-mode-match))

(defsum grep-binary-files-mode ;; --binary-files
  (grep-binary-binary)
  (grep-binary-text)  ;; -a --text
  (grep-binary-without-match) ;; -I
  )

(defsum grep-directories-mode ;; -d -directories
  (grep-directories-read)
  (grep-directories-skip)
  (grep-directories-recurse) ;; -r -R --recursive
  )

(defsum grep-match-mode
  (grep-match-default)
  (grep-match-line)  ;; -x --line-regexp
  (grep-match-word) ;; -w --word-regexp
  )

(defsum grep-filename-mode
  (grep-filename-default) ;; print filenames if there are multiple files
  (grep-filename-print-filename)
  (grep-filename-no-filename))

(defsum grep-filename-filter
  (grep-filter-all)
  (grep-filter-exclude (stringp filter)) ;; --exclude
  (grep-filter-include (stringp filter)) ;; --include
  )

(defsum grep-regexp-mode
  (grep-regexp-basic) ;; -G --basic-regexp
  (grep-regexp-extended) ;; -E --extended-regexp
  (grep-regexp-fixed) ;; -F --fixed-strings
  (grep-regexp-perl) ;; -P --perl-regexp
  )

(defsum grep-c-l
  :updatable t
  :compact nil  ;; :compact t is not compatible with updatable
  (grep-command-line
   (grep-output-mode-p outmode)
   (grep-pattern-input-p pattern)
   (booleanp ignore-case)
   (booleanp print-errors) ;; -s --no-messages
   (booleanp invert-match) ;; -v --invert-match
   (booleanp print-line-nums) ;; -n --line-number
   (grep-match-mode-p match-mode)
   (integerp before-context) ;; -B --before-context -C --context
   (integerp after-context) ;; -A --after-context -C --context
   (booleanp context-print-multiple) ;; -C vs -NUM
   (grep-color-mode-p color)
   (grep-overall-mode-p mode)
   (grep-binary-files-mode-p binary-mode)
   (booleanp print-byte-offset)
   (booleanp read-devices) ;; -D --devices
   (grep-directories-mode-p directory-mode)
   (grep-filename-mode-p print-filenames) ;; -H --with-filename -h --no-filename
   (booleanp line-buffered) ;; --line-buffered
   (stringp label) ;; --label
   (grep-filename-filter-p filter)
   (integerp max-count) ;; -m --max-count
   (booleanp msdos-binary) ;; -U --binary
   (booleanp unix-byte-offsets) ;; -u --unix-byte-offsets
   (booleanp mmap) ;; --mmap
   (booleanp filename-null) ;; -Z --null
   (booleanp line-null) ;; -z --null-data
   (grep-regexp-mode-p regexp-mode)
   ))




(defconst *grep-command-line-defaults*
  (grep-command-line
   (grep-output-line)
   (grep-pattern-none-yet)
   nil ;; case-sensitive
   t ;; print errors
   nil ;;don't invert match
   nil ;; don't print line numbers
   (grep-match-default)
   0 ;; before context
   0 ;; after context
   nil ;; don't print context lines more than once
   (grep-color-never)
   (grep-mode-match)
   (grep-binary-binary)
   nil ;; don't print byte offset
   t ;; read devices as if ordinary files
   (grep-directories-read) ;; as if they were ordinary files
   (grep-filename-default)
   nil ;; no line buffering policy (??)
   "" ;; empty label for stdin
   (grep-filter-all) ;; include all filenames
   -1 ;; no max count
   nil ;; not msdos binary mode
   nil ;; unix byte offset style
   nil ;; no mmap (...)
   nil ;; no null byte after filename
   nil ;; input lines not null-terminated
   (grep-regexp-basic)))





(defun grep-option-parse (tokens cmdline)
  (if (atom tokens)
      (mv cmdline tokens)
    (pattern-match
     (car tokens)
     ((any "--count" "-c")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-outmode
        (grep-output-count) cmdline)))
     ((any "ignore-case" "-i")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-ignore-case
        t cmdline)))
     ((any "--files-with-matches" "-l")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-outmode
        (grep-output-filename) cmdline)))
     ((any "--line-number" "-n")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-print-line-nums
        t cmdline)))
     ((any "--only-matching" "-o")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-outmode
        (grep-output-match) cmdline)))
     ((any "--quiet" "--silent" "-q")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-outmode
        (grep-output-match) cmdline)))
     ((any "--no-messages" "-s")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-print-errors
        nil cmdline)))
     ((any "--invert-match" "-v")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-invert-match
        t cmdline)))
     ((any "--line-regexp" "-x")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-match-mode
        (grep-match-line) cmdline)))
     ((any "--version" "-V")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-mode
        (grep-mode-version) cmdline)))
     ((any "--help")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-mode
        (grep-mode-help) cmdline)))
     ((any "--byte-offset" "-b")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-print-byte-offset
        t cmdline)))
     ((any "--with-filename" "-H")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-print-filenames
        (grep-filename-print-filename) cmdline)))
     ((any "--no-filename" "-h")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-print-filenames
        (grep-filename-no-filename) cmdline)))
     ((any "--line-buffered")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-line-buffered
        t cmdline)))
     ((any "--files-without-match" "-L")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-outmode
        (grep-output-non-matching-filename) cmdline)))
     ((any "--text" "-a")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-binary-mode
        (grep-binary-text) cmdline)))
     ((any "--word-regexp" "-w")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-match-mode
        (grep-match-word) cmdline)))
     ((any "--recursive" "-r" "-R")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-directory-mode
        (grep-directories-recurse) cmdline)))
     ((any "--binary" "-U")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-msdos-binary
        t cmdline)))
     ((any "--unix-byte-offsets" "-u")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-unix-byte-offsets
        t cmdline)))
     ((any "--mmap")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-mmap
        t cmdline)))
     ((any "--null" "-Z")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-filename-null
        t cmdline)))
     ((any "--null-data" "-z")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-line-null
        t cmdline)))
     ((any "--basic-regexp" "-G")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-regexp-mode
        (grep-regexp-basic) cmdline)))
     ((any "--extended-regexp" "-E")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-regexp-mode
        (grep-regexp-extended) cmdline)))
     ((any "--fixed-strings" "-F")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-regexp-mode
        (grep-regexp-fixed) cmdline)))
     ((any "--perl-regexp" "-P")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-regexp-mode
        (grep-regexp-perl) cmdline)))
     ((any "--regexp=" "-e")
      (grep-option-parse
       (cddr tokens)
       (update-grep-command-line-pattern
        (grep-pattern-string (cadr tokens)) cmdline)))
     ((any "--file=" "-f")
      (grep-option-parse
       (cddr tokens)
       (update-grep-command-line-pattern
        (grep-pattern-file (cadr tokens)) cmdline)))
     ((any "--after-context=" "-A")
      (mv-let
       (num rest pow)
       (parse-int (cadr tokens) 0)
       (declare (ignore rest pow))
       (if num
           (grep-option-parse
            (cddr tokens)
            (update-grep-command-line-after-context
             num cmdline))
         (mv (er hard? 'top-level "bad after-context")
             nil))))
     ((any "--before-context=" "-B")
      (mv-let
       (num rest pow)
       (parse-int (cadr tokens) 0)
       (declare (ignore rest pow))
       (if num
           (grep-option-parse
            (cddr tokens)
            (update-grep-command-line-before-context
             num cmdline))
         (mv (er hard? 'top-level "bad after-context")
             nil))))
     ((any "--context=" "-C")
      (mv-let
       (num rest pow)
       (parse-int (cadr tokens) 0)
       (declare (ignore rest pow))
       (if num
           (grep-option-parse
            (cddr tokens)
            (update-grep-command-line-before-context

             num (update-grep-command-line-after-context
                  cmdline num)))
         (mv (er hard? 'top-level "bad after-context")
             nil))))
     ((any "--color" "--colour")
      (grep-option-parse
       (cdr tokens)
       (update-grep-command-line-color

        (grep-color-always) cmdline)))
     ((any "--color=" "--colour=")
      (grep-option-parse
       (cddr tokens)
       (update-grep-command-line-color

        (pattern-match (cadr tokens)
                       ("never" (grep-color-never))
                       ("always" (grep-color-always))
                       ("auto" (grep-color-auto))
                       (&
                        (er hard? 'top-level "bad color specification"))) cmdline)))
     ((any "--binary-files=")
      (grep-option-parse
       (cddr tokens)
       (update-grep-command-line-binary-mode

        (pattern-match (cadr tokens)
                       ("binary" (grep-binary-binary))
                       ("text" (grep-binary-text))
                       ("without-match" (grep-binary-without-match))
                       (&
                        (er hard? 'top-level "bad binary-files option"))) cmdline)))
     ((any "--devices=" "-D")
      (grep-option-parse
       (cddr tokens)
       (update-grep-command-line-read-devices

        (pattern-match (cadr tokens)
                       ("read" t)
                       ("skip" nil)
                       (&
                        (er hard? 'top-level "bad devices option"))) cmdline)))
     ((any "--directories=" "-d")
      (grep-option-parse
       (cddr tokens)
       (update-grep-command-line-directory-mode

        (pattern-match (cadr tokens)
                       ("read" (grep-directories-read))
                       ("skip" (grep-directories-skip))
                       ("recurse" (grep-directories-recurse))
                       (&
                        (er hard? 'top-level "bad directories option"))) cmdline)))
     ((any "--label=")
      (grep-option-parse
       (cddr tokens)
       (update-grep-command-line-label
        (cadr tokens) cmdline)))
     ((any "--include=")
      (grep-option-parse
       (cddr tokens)
       (update-grep-command-line-filter

        (grep-filter-include (cadr tokens)) cmdline)))
     ((any "--exclude=")
      (grep-option-parse
       (cddr tokens)
       (update-grep-command-line-filter

        (grep-filter-exclude (cadr tokens)) cmdline)))
     ((any "--max-count=" "-m")
      (mv-let
       (num rest pow)
       (parse-int (cadr tokens) 0)
       (declare (ignore rest pow))
       (if num
           (grep-option-parse
            (cddr tokens)
            (update-grep-command-line-max-count
             num cmdline))
         (mv (er hard? 'top-level "bad max count")
             nil))))
     ((any "-" "--")
      (if (atom (cdr tokens))
          (mv
              (cdr tokens) (update-grep-command-line-pattern
               cmdline
               (grep-pattern-string "-")))
        (mv
            (cddr tokens) (update-grep-command-line-pattern
             cmdline
             (grep-pattern-string (cadr tokens))))))
     (&
      (cond ((and (>= (length (car tokens)) 1)
                  (eql (char (car tokens) 0) #\-))
             (mv-let
              (num rest pow)
              (parse-int (car tokens) 1)
              (declare (ignore rest pow))
              (if num
                  (grep-option-parse
                   (cdr tokens)
                   (update-grep-command-line-after-context

                    num (update-grep-command-line-before-context
                     cmdline
                     num)))
                (mv (er hard? 'top-level "Unrecognized option")
                    nil))))
            (t
             (if (equal (grep-command-line-pattern cmdline)
                        (grep-pattern-none-yet))
                 (mv
                  (update-grep-command-line-pattern

                   (grep-pattern-string (car tokens)) cmdline)
                  (cdr tokens))
               (mv cmdline tokens))))))))




(defun grep-display-help ()
  (cw "Run man grep or info grep on unix to see command-line options.~%
    Some options are not implemented.~%"))

(defun grep-display-version ()
  (cw "Grep for ACL2~%"))


(defun pattern-parse-by-mode (string options)
  (declare (xargs :guard (and (stringp string)
                              )))
  (let* ((opts (parse-options
                (pattern-match
                 (grep-command-line-regexp-mode options)
                 ((grep-regexp-basic) 'bre)
                 ((grep-regexp-extended) 'ere)
                 ((grep-regexp-fixed) 'fixed)
                 ((grep-regexp-perl)
                  (er hard? 'top-level "Perl regexps not yet implemented")))
                t nil t
                (grep-command-line-ignore-case options)))
         (string (if (grep-command-line-ignore-case options)
                     (case-insens-trans string)
                   string))
         (reg (regex-do-parse string opts)))
    (if (regex-p reg)
        reg
      (er hard? 'top-level "Regexp parse error: ~p0" reg))))


(defun parse-pattern-file-channel (channel options state)
  (declare (xargs :guard (and (symbolp channel)
                              (state-p state)
                              (grep-command-line-p options)
                              (open-input-channel-p channel :character
                                                    state))))
  (mv-let (more line state)
          (read-line$ channel nil state)
          (cond ((and (equal line "")
                      (not more))
                 (mv (r-nomatch) state))
                ((not more)
                 (mv (pattern-parse-by-mode line options)
                     state))
                (t (mv-let (patt state)
                           (parse-pattern-file-channel channel options state)
                           (mv (r-disjunct
                                (pattern-parse-by-mode line options)
                                patt)
                               state))))))


(defun parse-pattern-file (fname options state)
  (declare (xargs :guard (and (stringp fname)
                              (grep-command-line-p options)
                              (state-p state))))
  (mv-let (channel state) (open-input-channel fname :character state)
          (if (and (symbolp channel)
                   (open-input-channel-p channel :character state))
              (mv-let (regex state)
                      (parse-pattern-file-channel channel options state)
                      (let ((state (close-input-channel channel state)))
                        (mv regex state)))
            (mv (er hard? 'top-level "Bad filename")
                state))))


(defun get-pattern (options state)
  (declare (xargs :guard (and (grep-command-line-p options)
                              (state-p state))))
  (pattern-match
   (grep-command-line-pattern options)
   ((grep-pattern-string str)
    (mv (pattern-parse-by-mode str options) state))
   ((grep-pattern-file fname)
    (parse-pattern-file fname options state))
   (& (mv (er hard? 'top-level "No pattern") state))))





;; (defun grep-through-file (pattern options file linenum state)
;;   (declare (xargs :guard (and (regex-p pattern)
;;                               (grep-command-line-p options)
;;                               (symbolp file)
;;                               (natp linenum)
;;                               (state-p state)
;;                               (open-input-channel-p file :character state))))
;;   (mv-let (more line state)
;;           (read-line$ file nil state)
;;           (let ((trans-line (if (grep-command-line-ignore-case options)
;;                                 (case-insens-trans line)
;;                               line)))
;;             (mv-let (havematch matchstr brs)
;;                     (match-regex pattern trans-line line)
;;                     (declare (ignore brs))
;;                     (mv-let (matches state)
;;                             (if more
;;                                 (grep-through-file pattern options file
;;                                                    (1+ linenum) state)
;;                               (mv nil state))
;;                             (if havematch
;;                                 (mv (cons (cons linenum matchstr) matches)
;;                                     state)
;;                               (mv matches state)))))))




;; (defun print-line-range
;;   (start end current fname print-name print-num channel state)
;;   (if (and (integerp end)
;;            (> current end))
;;       state
;;     (mv-let (more line state)
;;             (read-line$ channel nil state)
;;             (if (< current start)
;;                 (if more
;;                     (print-line-range start end (1+ current) fname
;;                                       print-name print-num channel state)
;;                   state)
;;               (prog2$
;;                (and print-name (cw "~s0:" fname))
;;                (prog2$
;;                 (and print-num (cw "~x0:" current))
;;                 (prog2$
;;                  (cw "~s0~%" line)
;;                  (if more
;;                      (print-line-range start end (1+ current) fname
;;                                        print-name print-num channel state)
;;                    state))))))))

;; (defun print-matching-lines-in-file
;;   (fname nextline matches print-name options channel state)
;;   (let ((print-num (grep-command-line-print-line-nums options))
;;         (before-context (grep-command-line-before-context options))
;;         (after-context (grep-command-line-after-context options)))
;;     (if (atom matches)
;;         state
;;       (let ((state
;;              (print-line-range
;;               (max nextline (- (caar matches) before-context))
;;               (+ (caar matches) after-context)
;;               nextline
;;               fname print-name print-num
;;               channel state)))
;;         (print-matching-lines-in-file
;;          fname (+ 1 (caar matches) after-context) (cdr matches) print-name
;;          options channel state)))))


;; (defun print-matches-in-file
;;   (fname matches print-name options)
;;   (if (atom matches)
;;       nil
;;     (prog2$
;;      (and print-name (cw "~s0:" fname))
;;      (prog2$
;;       (and (grep-command-line-print-line-nums options)
;;            (cw "~x0:" (caar matches)))
;;       (prog2$
;;        (cw "~s0~%" (cdar matches))
;;        (print-matches-in-file fname (cdr matches) print-name options))))))

;; (defun print-non-matching-lines-in-file
;;   (fname nextline matches print-name options channel state)
;;   (let ((print-num (grep-command-line-print-line-nums options))
;;         (before-context (grep-command-line-before-context options))
;;         (after-context (grep-command-line-after-context options)))
;;     (if (atom matches)
;;         (print-line-range nextline nil nextline fname
;;                           print-name print-num channel state)
;;       (if (atom (cdr matches))
;;           (print-line-range (- (1+ (caar matches)) before-context) nil
;;                             nextline fname print-name print-num channel state)
;;         (let ((state (print-line-range (- (1+ (caar matches)) before-context)
;;                                        (+ (1- (caadr matches)) after-context)
;;                                        nextline fname print-name print-num
;;                                        channel state)))
;;           (print-non-matching-lines-in-file
;;            fname (+ (caadr matches) after-context) (cdr matches)
;;            print-name options channel state))))))


;; (defun print-match-range (start end matches fname print-name print-num)
;;   (if (or (atom matches)
;;           (< end (caar matches)))
;;       nil
;;     (prog2$ (if (and (>= (caar matches) start)
;;                      (stringp (cdar matches)))
;;                 (prog2$
;;                  (and print-name (cw "~s0:" fname))
;;                  (prog2$ (and print-num (cw "~x0:" (caar matches)))
;;                          (cw "~s0~%" (cdar matches))))
;;               nil)
;;         (print-match-range start end (cdr matches) fname print-name print-num))))


;; (defun fill-out-matches (matches linenum channel state)
;;   (mv-let (more line state)
;;           (read-line$ channel nil state)
;;           (declare (ignore line))
;;           (if (and (consp matches)
;;                    (equal linenum (caar matches)))
;;               (if more
;;                   (mv-let (rest state)
;;                           (fill-out-matches
;;                            (cdr matches) (1+ linenum) channel state)
;;                           (mv (cons (car matches) rest) state))
;;                 (mv (list (car matches)) state))
;;             (if more
;;                 (mv-let (rest state)
;;                         (fill-out-matches
;;                          matches (1+ linenum) channel state)
;;                         (mv (cons (list linenum) rest) state))
;;               (mv (list (list linenum)) state)))))



;; (defun print-non-matching-matches-in-file
;;   (fname matches all-matches print-name options)
;;   (let ((print-num (grep-command-line-print-line-nums options))
;;         (before-context (grep-command-line-before-context options))
;;         (after-context (grep-command-line-after-context options)))
;;     (if (atom matches)
;;         nil
;;       (prog2$ (if (cdar matches)
;;                   nil
;;                 (print-match-range
;;                  (- (caar matches) before-context)
;;                  (+ (caar matches) after-context)
;;                  all-matches fname print-name print-num))
;;               (print-non-matching-matches-in-file
;;                fname (cdr matches) all-matches print-name options)))))


;; (defun print-matches-or-lines-in-file
;;   (fname matches print-name options channel state)
;;   (pattern-match-list
;;    ((grep-command-line-outmode options)
;;     (grep-command-line-invert-match options))
;;    (((grep-output-line) nil)
;;     (print-matching-lines-in-file
;;      fname 0 matches print-name options channel state))
;;    (((grep-output-line) t)
;;     (print-non-matching-lines-in-file
;;      fname 0 matches print-name options channel state))
;;    (((grep-output-match) nil)
;;     (prog2$ (print-matches-in-file
;;              fname matches print-name options)
;;             state))
;;    (((grep-output-match) t)
;;     (mv-let (full-matches state)
;;             (fill-out-matches matches 0 channel state)
;;             (prog2$ (print-non-matching-matches-in-file
;;                      fname full-matches matches print-name options)
;;                     state)))
;;    (& (prog2$ (er hard? 'top-level "Bad outmode or invert-mode")
;;               state))))





;; (defun print-matches (fname matches multi options state)
;;   (let ((print-fname (pattern-match
;;                       (grep-command-line-print-filenames options)
;;                       ((grep-filename-default) multi)
;;                       ((grep-filename-print-filename) t)
;;                       (& nil))))
;;     (pattern-match
;;      (grep-command-line-outmode options)
;;      ((grep-output-count)
;;       (prog2$ (if print-fname
;;                   (cw "~s0:~y1" fname (len matches))
;;                 (cw "~y1" (len matches)))
;;               state))
;;      ((grep-output-filename)
;;       (prog2$ (if matches
;;                   (cw "~s0~%" fname)
;;                 nil)
;;               state))
;;      ((grep-output-non-matching-filename)
;;       (prog2$ (if matches
;;                   nil
;;                 (cw "~s0~%" fname))
;;               state))
;;      ((grep-output-silent)
;;       state)
;;      (& (mv-let (channel state)
;;                 (open-input-channel fname :character state)
;;                 (let ((state (print-matches-or-lines-in-file
;;                               fname matches print-fname options channel
;;                               state)))
;;                   (close-input-channel channel state)))))))


(defun print-line (fname print-name linenum print-num line sep)
  (prog2$
   (if print-name
       (cw "~s0~s1" (if (equal fname "/dev/stdin")
                         "(standard input)"
                       fname) sep)
     nil)
   (prog2$
    (if print-num
        (cw "~x0~s1" linenum sep)
      nil)
    (cw "~s0~%" line))))


(defun print-lines (fname print-name print-num oldlines num)
  (if (or (zp num) (atom oldlines))
      nil
    (prog2$
     (print-lines fname print-name print-num (cdr oldlines) (1- num))
     (print-line fname print-name (caar oldlines) print-num
                 (cdar oldlines) "-"))))



(defmacro print-for-match (line)
  `(prog2$
    (print-lines fname print-name print-num oldlines
                 before-context)
    (prog2$
     (print-line fname print-name linenum print-num
                 ,line ":")
     (if more
         (grep-through-file pattern file fname print-name
                            (1+ linenum) nil after-context
                            (1+ count) options state)
       (mv 0 state)))))


(defmacro print-in-range (line)
  `(if (> nextn 0)
       (prog2$
        (print-line fname print-name linenum print-num
                    ,line "-")
        (if more
            (grep-through-file pattern file fname print-name (1+ linenum)
                               nil (1- nextn) count options state)
          (mv (if (> count 0) 0 1) state)))
     (prog2$
      (if (and (= nextn 0)
               (or (> before-context 0)
                   (> after-context 0))
               (not (equal fname "/dev/stdin")))
          (cw "--~%")
        nil)
      (if more
          (grep-through-file pattern file fname print-name (1+ linenum)
                             (cons (cons linenum ,line) oldlines)
                             -1 count options state)
        (mv (if (> count 0) 0 1) state)))))

(defmacro count-through-file (count)
  `(if more
       (grep-through-file pattern file fname print-name
                          (1+ linenum) oldlines nextn ,count
                          options state)
     (prog2$
      (if print-name
          (cw "~s0:" fname)
        nil)
      (prog2$ (cw "~y0~%" ,count)
              (mv (if (> ,count 0) 0 1) state)))))


(defun grep-through-file (pattern file fname print-name linenum
                                  oldlines nextn count options state)
  (let ((invert (grep-command-line-invert-match options))
        (before-context (grep-command-line-before-context options))
        (after-context (grep-command-line-after-context options))
        (print-num (grep-command-line-print-line-nums options))
        (outmode (grep-command-line-outmode options)))
    (mv-let (more line state)
            (read-line$ file nil state)
            (let ((trans-line (if (grep-command-line-ignore-case options)
                                  (case-insens-trans line)
                                line)))
              (mv-let
               (havematch matchstr brs)
               (match-regex pattern trans-line line)
               (declare (ignore brs))
               (let ((matched (equal havematch invert)))
                 (pattern-match-list
                  (outmode matched)

                  (((grep-output-line) nil)
                   (print-for-match line))

                  (((grep-output-line) t)
                   (print-in-range line))

                  (((grep-output-match) nil)
                   (print-for-match matchstr))

                  (((grep-output-match) t)
                   (print-in-range matchstr))

                  (((grep-output-filename) t)
                   (prog2$ (cw "~s0~%" fname)
                           (mv 0 state)))

                  (((grep-output-filename) nil)
                   (if more
                       (grep-through-file pattern file fname print-name
                                          (1+ linenum) oldlines nextn count
                                          options state)
                     (mv 1 state)))

                  (((grep-output-count) nil)
                   (count-through-file (1+ count)))

                  (((grep-output-count) t)
                   (count-through-file count))

                  (((grep-output-non-matching-filename) t)
                   (mv 0 state))

                  (((grep-output-non-matching-filename) nil)
                   (if more
                       (grep-through-file pattern file fname print-name
                                          (1+ linenum) oldlines nextn count
                                          options state)
                     (prog2$ (cw "~s0~%" fname)
                             (mv 1 state))))

                  (((grep-output-silent) t)
                   (mv 0 state))

                  (((grep-output-silent) nil)
                   (if more
                       (grep-through-file pattern file fname print-name
                                          (1+ linenum) oldlines nextn count
                                          options state)
                     (mv 1 state)))

                  (& (mv (er hard? 'top-level "Bad output mode in options")
                         state)))))))))




(defun grep-through-files (pattern options files multi state)
  (declare (xargs :guard (and (regex-p pattern)
                              (grep-command-line-p options)
                              (string-listp files)
                              (booleanp multi)
                              (state-p state))))
  (if (atom files)
      (mv 1 state)
    (let* ((file (car files)))
      (mv-let (channel state)
              (open-input-channel file :character state)
              (if (and (symbolp channel)
                       (open-input-channel-p channel :character state))
                 (let ((print-fname (pattern-match
                      (grep-command-line-print-filenames options)
                      ((grep-filename-default) multi)
                      ((grep-filename-print-filename) t)
                      (& nil))))
                   (mv-let
                    (code state)
                    (grep-through-file pattern channel file
                                       print-fname 0 nil -1 0
                                       options state)
                    (mv-let
                     (code2 state)
                     (grep-through-files pattern options
                                         (cdr files) multi state)
                     (mv (cond ((or (= code 2)
                                    (= code2 2))
                                2)
                               ((or (= code 0)
                                    (= code2 0))
                                0)
                               (t 1))
                         state))))
                (prog2$ (cw "File couldn't be opened: ~p0~%" file)
                        (mv 2 state)))))))




(defun find-first-occurrence-after (str char idx)
  (declare (xargs :guard (and (stringp str)
                              (characterp char))))
  (cond ((string-index-end idx str)
         nil)
        ((equal (char str idx) char)
         idx)
        (t
         (find-first-occurrence-after str char (1+ idx)))))


(defun grep-split-abbrev-args (arg idx)
  (if (string-index-end idx arg)
      nil
    (mv-let (num rest power)
            (parse-int arg idx)
            (declare (ignore power))
            (if num
                (cons (concatenate 'string
                                   "-"
                                   (subseq arg idx rest))
                      (grep-split-abbrev-args arg rest))
              (cons (concatenate 'string
                                 "-"
                                 (subseq arg idx (1+ idx)))
                    (grep-split-abbrev-args arg (1+ idx)))))))



(defun grep-split-args (args)
  (if (atom args)
      nil
    (let ((arg (car args)))
      (cond
       ((and (> (length arg) 2)
             (equal (subseq arg 0 2) "--"))
        (let ((equal (find-first-occurrence-after arg #\= 0)))
          (if equal
              (cons (subseq arg 0 (1+ equal))
                    (cons (subseq arg (1+ equal) nil)
                          (grep-split-args (cdr args))))
            (cons arg (grep-split-args (cdr args))))))
       ((and (>= (length arg) 2)
             (equal (char arg 0) #\-))
        (append (grep-split-abbrev-args arg 1)
                (grep-split-args (cdr args))))
       (t (cons arg (grep-split-args (cdr args))))))))


(defun grep-exec (args state)
  (mv-let
   (options files)
   (grep-option-parse
    (grep-split-args args)
    *grep-command-line-defaults*)
   (pattern-match
    (grep-command-line-mode options)
    ((grep-mode-help)
     (prog2$ (grep-display-help) (mv 0 state)))
    ((grep-mode-version)
     (prog2$ (grep-display-version) (mv 0 state)))
    ((grep-mode-match)
     (if (grep-pattern-none-yet-p (grep-command-line-pattern options))
         (prog2$ (grep-display-help) (mv 0 state))
       (mv-let (pattern state)
               (get-pattern options state)
               (let ((files (if (consp files) files (list "/dev/stdin"))))
                 (grep-through-files pattern options files
                                     (consp (cdr files)) state)))))
    (& (prog2$ (er hard? 'top-level "bad top-level mode (should never occur)")
               (mv 2 state))))))



