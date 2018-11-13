(include-book "../file-system-m2")
(include-book "centaur/getopt/top" :dir :system)
(include-book "oslib/argv" :dir :system)

(defoptions wc-opts
  :parents (demo2)
  :tag :demo2

  ((bytes    "Count bytes"
             booleanp
             :rule-classes :type-prescription
             :alias #\c)

   (lines "Count lines"
          booleanp
          :rule-classes :type-prescription
          :alias #\l)

   (words "Count words"
           booleanp
           :rule-classes :type-prescription
           :alias #\w)))

(defun wc-helper (text nl nw nc beginning-of-word-p pos)
  (declare (xargs :measure (nfix (- (length text) pos))))
  (if
      (zp (- (length text) pos))
      (mv nl nw nc)
    (b*
        ((c (char text pos))
         (nc (+ nc 1))
         (nl (if (equal c #\newline) (+ nl 1) nl))
         ((mv beginning-of-word-p nw)
          (if (or (equal c #\space) (equal c #\newline) (equal c #\tab))
              (mv t nw)
            (if beginning-of-word-p
                (mv nil (+ nw 1))
              (mv beginning-of-word-p nw)))))
      (wc-helper text nl nw nc beginning-of-word-p (+ pos 1)))))

(b*
    (((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-fat32-in-memory
       fat32-in-memory val state))
     ((mv & val state)
      (getenv$ "WC_OUTPUT" state))
     ((mv channel state)
      (open-output-channel val :character state))
     ((mv & val state)
      (getenv$ "WC_INPUT" state))
     (fat32-pathname (pathname-to-fat32-pathname (coerce val 'list)))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory))
     ((mv val error-code &)
      (m1-lstat fs fat32-pathname))
     ((unless (equal error-code 0))
      (mv fat32-in-memory state))
     (file-length (struct-stat->st_size val))
     ((mv fd-table file-table fd &)
      (m1-open fat32-pathname fs nil nil))
     ((mv file-text file-read-length &)
      (m1-pread
       fd file-length 0 fs fd-table file-table))
     ((unless (equal file-read-length file-length))
      (mv fat32-in-memory state))
     ((mv nl nw nc)
      (wc-helper file-text 0 0 0 t 0))
     ((mv argv state)              (oslib::argv))
     ((mv errmsg opts ?extra-args) (parse-wc-opts argv))
     ((wc-opts opts) opts)
     (state
      (if errmsg state
        (if opts.bytes
            (princ$
             nc
             channel state)
          (if opts.lines
              (princ$
               nl
               channel state)
            (if opts.words
                (princ$
                 nw
                 channel state)
              state)))))
     (state (newline channel state))
     (state (close-output-channel channel state)))
  (mv fat32-in-memory state))
