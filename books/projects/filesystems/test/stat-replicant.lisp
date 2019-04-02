(include-book "../lofat")
(include-book "centaur/getopt/top" :dir :system)
(include-book "oslib/argv" :dir :system)

(encapsulate
  ()
  (local (include-book "arithmetic-3/top" :dir :system))
  (defun
      fixed-width-print-helper (x n)
    (declare
     (xargs :hints (("goal" :in-theory (disable floor mod)))))
    (if
        (or (zp n) (zp x))
        nil
      (append
       (fixed-width-print-helper (floor x 10) (- n 1))
       (list (code-char (+ (mod x 10) (char-code #\0))))))))

(defthm len-of-fixed-width-print-helper
  (<= (len (fixed-width-print-helper x n))
      (nfix n))
  :rule-classes :linear
  :hints (("goal" :in-theory (disable ceiling floor))))

(defun fixed-width-print (x n)
  (coerce (if (zp x)
              (cons #\0
                    (make-list (- n 1) :initial-element #\space))
            (append (fixed-width-print-helper x n)
                    (make-list (- n (len (fixed-width-print-helper x n)))
                               :initial-element #\space)))
          'string))

(defthm
  length-of-fixed-width-print
  (implies (not (zp n))
           (equal (len (explode (fixed-width-print x n)))
                  n))
  :hints (("goal" :in-theory (enable fixed-width-print))))

(defoptions stat-opts
  :parents (demo2)
  :tag :demo2

  ((file-system "Provide filesystem parameters"
                booleanp
                :rule-classes :type-prescription
                :alias #\f)))

(b*
    (((mv argv state)              (oslib::argv))
     ((mv errmsg opts ?extra-args) (parse-stat-opts argv))
     ((when errmsg)
      (mv fat32-in-memory state))
     ((stat-opts opts) opts)
     ((unless opts.file-system)
      (mv fat32-in-memory state))
     ((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory val state))
     ((mv & val state)
      (getenv$ "STAT_OUTPUT" state))
     ((mv channel state)
      (open-output-channel val :character state))
     ((mv & pathname state)
      (getenv$ "STAT_INPUT" state))
     (statfsbuf (lofat-statfs fat32-in-memory))
     (state
      (pprogn
       (princ$ "  File: \"" channel state)
       (princ$ pathname channel state)
       (princ$"\"" channel state)
       (newline channel state)
       (princ$ "    ID: " channel state)
       ;; Choosing to print 0 as a constant here - rather than take it from the
       ;; stat - becasue the coreutils version has some complicated rules for
       ;; printing the value in the f_fsid field
       (princ$ (fixed-width-print 0 8) channel state)
       (princ$ " Namelen: " channel state)
       (princ$ (fixed-width-print
                (struct-statfs->f_namelen statfsbuf)
                7)
               channel state)
       (princ$ " Type: " channel state)
       (if (equal (struct-statfs->f_type statfsbuf) *S_MAGIC_FUSEBLK*)
           (princ$ "fuseblk" channel state)
         (princ$ "UNKNOWN ()" channel state))
       (newline channel state)
       (princ$ "Block size: " channel state)
       (princ$ (fixed-width-print
                (struct-statfs->f_bsize statfsbuf) 10)
               channel state)
       (princ$ " Fundamental block size: " channel state)
       (princ$ (struct-statfs->f_bsize statfsbuf) channel state)
       (newline channel state)
       (princ$ "Blocks: Total: " channel state)
       (princ$ (fixed-width-print
                (struct-statfs->f_blocks statfsbuf)
                10) channel state)
       (princ$ " Free: " channel state)
       (princ$ (fixed-width-print
                (struct-statfs->f_bavail statfsbuf)
                10) channel state)
       (princ$ " Available: " channel state)
       (princ$ (struct-statfs->f_bavail statfsbuf) channel state)
       (newline channel state)
       (princ$ "Inodes: Total: " channel state)
       (princ$ (fixed-width-print
                (struct-statfs->f_files statfsbuf)
                10) channel state)
       (princ$ " Free: " channel state)
       (princ$ (struct-statfs->f_ffree statfsbuf) channel state)
       (newline channel state)
       (close-output-channel channel state))))
  (mv fat32-in-memory state))
