(in-package "ACL2")

(include-book "test-stuff")

(defconst *tar-regtype* #\0)
(defconst *tar-dirtype* #\5)
(defconst *tar-block-size* 512)
(defconst *tar-blank-block*
  (coerce (make-list *tar-block-size*
                     :initial-element (code-char 0))
          'string))

(local
 (in-theory (disable nth update-nth ceiling floor mod true-listp take member-equal)))

(defund tar-len-decode-helper (rev-char-list)
  (declare (xargs :guard (character-listp rev-char-list)))
  (if (atom rev-char-list)
      0
      (+ (nfix (- (char-code (car rev-char-list))
                  (char-code #\0)))
         (* 8
            (tar-len-decode-helper (cdr rev-char-list))))))

(defund
  tar-len-decode (string)
  (declare
   (xargs :guard (stringp string)
          :guard-hints
          (("goal" :in-theory (disable reverse-removal)))))
  (tar-len-decode-helper (reverse (coerce string 'list))))

(defund tar-name-decode (string)
  (declare (xargs :guard (stringp string) :measure (length string)))
  (if
      (mbe :logic (or (not (stringp string)) (zp (length string))
                      (not (equal (char string (- (length string) 1))
                                  (code-char 0))))
           :exec (or (zp (length string))
                     (not (equal (char string (- (length string) 1))
                                 (code-char 0)))))
      string
    (tar-name-decode (subseq string 0 (- (length string) 1)))))

(defund
  process-dir-file
  (fat32-in-memory path state)
  (declare
   (xargs
    :stobjs (fat32-in-memory state)
    :guard (and (lofat-fs-p fat32-in-memory)
                (fat32-filename-list-p path)
                (state-p state)
                (open-output-channel-p *standard-co* :character
                                       state))))
  (b* (((mv fat32-in-memory retval &)
        (lofat-mkdir fat32-in-memory path))
       (state (princ$ retval *standard-co* state))
       (state (princ$ ": value of retval, from lofat-mkdir" *standard-co* state))
       (state (newline *standard-co* state)))
    (mv fat32-in-memory state)))

(defund process-reg-file (fat32-in-memory path file-text file-table
                                          fd-table state)
  (declare (xargs :stobjs (fat32-in-memory state)
                  :guard (and (lofat-fs-p fat32-in-memory)
                              (fd-table-p fd-table)
                              (file-table-p file-table)
                              (stringp file-text)
                              (fat32-filename-list-p path)
                              (state-p state)
                              (open-output-channel-p *standard-co* :character
                                                     state))
                  :guard-debug t))
  (b*
      (((mv fd-table file-table fd &)
        (lofat-open path fd-table file-table))
       (state (princ$ fd *standard-co* state))
       (state (princ$ ": value of fd, from lofat-open" *standard-co* state))
       (state (newline *standard-co* state))
       ((unless (natp fd))
        (mv fat32-in-memory fd-table file-table state))
       ((mv fat32-in-memory retval &) (lofat-pwrite fd
                                                    file-text
                                                    0
                                                    fat32-in-memory
                                                    fd-table
                                                    file-table))
       (state (princ$ retval *standard-co* state))
       (state (princ$ ": value of retval, from lofat-pwrite" *standard-co* state))
       (state (newline *standard-co* state))
       ((mv fd-table file-table &) (lofat-close fd fd-table file-table)))
    (mv fat32-in-memory fd-table file-table state)))

(defthm
  fd-table-p-of-process-reg-file
  (fd-table-p
   (mv-nth 1
           (process-reg-file fat32-in-memory path
                             file-text file-table fd-table state)))
  :hints
  (("goal" :in-theory (enable process-reg-file lofat-close))))

(defthm
  file-table-p-of-process-reg-file
  (file-table-p
   (mv-nth 2
           (process-reg-file fat32-in-memory path
                             file-text file-table fd-table state)))
  :hints
  (("goal" :in-theory (enable process-reg-file lofat-close))))

(defthm
  lofat-fs-p-of-process-reg-file
  (implies
   (lofat-fs-p fat32-in-memory)
   (lofat-fs-p
    (mv-nth 0
            (process-reg-file fat32-in-memory path
                              file-text file-table fd-table state))))
  :hints
  (("goal" :in-theory (enable process-reg-file
                              lofat-close lofat-pwrite))))

(defthm
  lofat-fs-p-of-process-dir-file
  (implies
   (lofat-fs-p fat32-in-memory)
   (lofat-fs-p (mv-nth 0 (process-dir-file fat32-in-memory path state))))
  :hints
  (("goal" :in-theory (enable process-dir-file lofat-mkdir))))

(defund process-block-sequence (file-text state fat32-in-memory fd-table
                                          file-table output-path)
  (declare (xargs :stobjs (state fat32-in-memory)
                  :measure (length file-text)
                  :guard (and (state-p state) (stringp file-text)
                              (lofat-fs-p fat32-in-memory)
                              (fd-table-p fd-table)
                              (file-table-p file-table)
                              (open-output-channel-p *standard-co* :character
                                                     state)
                              (fat32-filename-list-p output-path))
                  :guard-hints (("Goal" :in-theory (enable process-reg-file
                                                           lofat-close process-dir-file)) )))
  (b*
      (((unless (mbe :exec (>= (length file-text) 512)
                     :logic (and (stringp file-text) (>= (length file-text) 512))))
        (mv state fat32-in-memory fd-table file-table))
       (first-block (subseq file-text 0 512))
       ((when (equal first-block *tar-blank-block*))
        (process-block-sequence
         (subseq file-text 512 nil) state fat32-in-memory fd-table file-table
         output-path))
       (first-block-name (tar-name-decode (subseq first-block 0 100)))
       (state (princ$ "File with name " *standard-co* state))
       (state (princ$ first-block-name *standard-co* state))
       (first-block-typeflag (char first-block 156))
       (state (princ$
               (cond ((equal first-block-typeflag *TAR-REGTYPE*)
                      " is a regular file")
                     ((equal first-block-typeflag *tar-dirtype*)
                      " is a directory file")
                     (t " is other than a regular or directory file"))
               *standard-co* state))
       (state (princ$ ", has length " *standard-co* state))
       (first-block-length (tar-len-decode (subseq first-block 124 135)))
       (state (princ$ first-block-length *standard-co* state))
       (state (princ$ ", has contents:" *standard-co* state))
       (state (newline *standard-co* state))
       (first-block-text
        (subseq file-text 512
                (min (+ 512 first-block-length) (length file-text))))
       (state (princ$ first-block-text
                      *standard-co* state))
       (state (newline *standard-co* state))
       (state (princ$ "About to append" *standard-co* state))
       (state (newline *standard-co* state))
       (path (append output-path (path-to-fat32-path
                                          (coerce first-block-name 'list))))
       ((mv fat32-in-memory fd-table file-table state)
        (cond ((not (fat32-filename-list-p path))
               (let
                   ((state (princ$ "path is problematic" *standard-co* state)))
                 (mv fat32-in-memory fd-table file-table state)))
              ((equal first-block-typeflag *TAR-REGTYPE*)
               (let
                   ((state (princ$
                            "typeflag indicates a regular file"
                            *standard-co* state)))
                 (process-reg-file fat32-in-memory path first-block-text
                                   file-table fd-table state)))
              ((equal first-block-typeflag *tar-dirtype*)
               (mv-let
                   (fat32-in-memory state)
                   (process-dir-file fat32-in-memory path state)
                   (mv fat32-in-memory fd-table file-table state)))
              (t
               (let
                   ((state (princ$
                            "path is fine, but typeflag is problematic"
                            *standard-co* state)))
                 (mv fat32-in-memory fd-table file-table state))))))
    (process-block-sequence
     (subseq file-text (min (+ 512
                               (* 512 (ceiling first-block-length 512)))
                            (length file-text))
             nil)
     state fat32-in-memory fd-table file-table output-path)))
