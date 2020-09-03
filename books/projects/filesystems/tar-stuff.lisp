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

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defund
    tar-len-encode-helper (len n)
    (declare (xargs :guard (and (natp len) (natp n))))
    (if
     (zp n)
     nil
     (cons (code-char (+ (mod len 8) (char-code #\0)))
           (tar-len-encode-helper (floor len 8) (- n 1))))))

(defthm
  len-of-tar-len-encode-helper
  (equal (len (tar-len-encode-helper len n))
         (nfix n))
  :hints (("goal" :in-theory (enable tar-len-encode-helper))))

(defthm
  character-listp-of-tar-len-encode-helper
  (character-listp (tar-len-encode-helper len n))
  :hints (("goal" :in-theory (enable tar-len-encode-helper))))

(defund tar-len-encode (len)
  ;; It would be folly to stipulate that the length has to be less than 8^11,
  ;; and then keep struggling with every new guard proof.
  (declare (xargs :guard (natp len)
                  :guard-hints (("Goal" :in-theory (enable
                                                    tar-len-encode-helper)) )))
  (coerce (revappend (tar-len-encode-helper len 11) (list (code-char 0)))
          'string))

(defthm length-of-tar-len-encode
  (equal (len (explode (tar-len-encode len))) 12)
  :hints (("Goal" :in-theory (enable tar-len-encode)) ))

(defund
  tar-header-block (path len typeflag)
  (declare
   (xargs :guard (and (characterp typeflag)
                      (stringp path)
                      (>= 100 (length path))
                      (natp len))
          :guard-hints
          (("goal" :in-theory (e/d
                               (string-listp)
                               (make-list-ac-removal))))))
  (let ((path (mbe :exec path
                       :logic (str-fix path))))
       (concatenate
        'string
        path
        (coerce (make-list (- 124 (length path))
                           :initial-element (code-char 0))
                'string)
        (tar-len-encode len)
        (coerce (make-list (- 155 136)
                           :initial-element (code-char 0))
                'string)
        (string (mbe :exec typeflag
                     :logic (char-fix typeflag)))
        (coerce (make-list (- 512 156)
                           :initial-element (code-char 0))
                'string))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defund hifat-tar-reg-file-string (fs path)
    (declare (xargs :guard (and (stringp path) (m1-file-alist-p fs)
                                (hifat-no-dups-p fs) (<= (length path) 100))
                    :guard-debug t
                    :guard-hints (("Goal" :in-theory (e/d
                                                      (string-listp ceiling)
                                                      (make-list-ac-removal))))))
    (b*
        ((fat32-path (path-to-fat32-path (coerce path 'list)))
         ((unless (fat32-filename-list-p fat32-path)) "")
         ((mv val & &) (hifat-lstat fs fat32-path))
         (file-length (struct-stat->st_size val))
         ((mv fd-table file-table fd &)
          (hifat-open fat32-path nil nil))
         ((unless (>= fd 0)) "")
         ((mv contents & &)
          (hifat-pread
           fd file-length 0 fs fd-table file-table))
         (len (length contents))
         (first-block
          (tar-header-block path len *tar-regtype*)))
      (concatenate
       'string
       first-block
       contents
       (coerce
        (make-list
         (- (* 512 (ceiling len 512)) len) :initial-element
         (code-char 0))
        'string)))))

;; Path is not needed as an argument! This is the recursive part only.
(defund
  hifat-get-names-from-dirp
  (dirp dir-stream-table)
  (declare
   (xargs
    :measure
    (len
     (dir-stream->file-list
      (cdr
       (assoc-equal (nfix dirp)
                    (dir-stream-table-fix dir-stream-table)))))
    :hints (("goal" :in-theory (enable hifat-readdir)))
    :guard (and (natp dirp) (dir-stream-table-p dir-stream-table))))
  (b*
      (((mv name errno dir-stream-table)
        (hifat-readdir dirp dir-stream-table))
       ((when (or (equal errno *ebadf*)
                  (equal name *empty-fat32-name*)))
        (mv nil dir-stream-table))
       ((mv tail dir-stream-table)
        (hifat-get-names-from-dirp dirp dir-stream-table)))
    (mv (list* name tail) dir-stream-table)))

(defthm fat32-filename-list-p-of-hifat-get-names-from-dirp
  (fat32-filename-list-p
   (mv-nth 0
           (hifat-get-names-from-dirp dirp dir-stream-table)))
  :hints (("goal" :in-theory (enable hifat-get-names-from-dirp
                                     hifat-readdir))))

(defthm dir-stream-table-p-of-hifat-get-names-from-dirp
  (dir-stream-table-p
   (mv-nth 1
           (hifat-get-names-from-dirp dirp dir-stream-table)))
  :hints (("goal" :in-theory (enable hifat-get-names-from-dirp
                                     hifat-readdir))))

;; Making a recursive function to do tar can get really annoying because in
;; theory we could hit directory cycles and just keep traversing deeper and
;; deeper into the tree. It's important for proof purposes that we induct on
;; the pathnames, keeping the fs the same and accessing its inside parts only
;; through system calls.
;;
;; The way this proof is going to look is, we'll have to do one real
;; partial collapse, and possibly a few more later which won't have any
;; effect. But the one partial collapse will bring the whole directory into one
;; variable, and then effectively all lookups will just be lookups inside that
;; thing.
;;
;; Always gotta remember, though, that indiscriminate use of hifat-find-file will
;; be incorrect for looking up the contents of a directory because that
;; function will not work for looking up a root directory!
;; Anyway, to return to the induction scheme, it will be needed to make
;; something like a max path length and stop when we get there...
(defund
  hifat-tar-name-list-string
  (fs path name-list fd-table
      file-table dir-stream-table entry-count)
  (declare
   (xargs :guard (and (m1-file-alist-p fs)
                      (hifat-no-dups-p fs)
                      (fat32-filename-list-p path)
                      (natp entry-count)
                      (fat32-filename-list-p name-list)
                      (file-table-p file-table)
                      (fd-table-p fd-table)
                      (dir-stream-table-p dir-stream-table))
          :guard-hints
          (("goal" :in-theory (e/d (hifat-tar-name-list-string)
                                   (append append-of-cons))
            :do-not-induct t))
          :measure (nfix entry-count)
          :verify-guards nil))
  (b*
      ((fd-table (mbe :exec fd-table
                      :logic (fd-table-fix fd-table)))
       (file-table (mbe :exec file-table
                        :logic (file-table-fix file-table)))
       (dir-stream-table
        (mbe :exec dir-stream-table
             :logic (dir-stream-table-fix dir-stream-table)))
       ((unless (and (consp name-list)
                     (not (zp entry-count))))
        (mv "" fd-table file-table))
       (head (car name-list))
       (head-path (append path (list head)))
       ((mv st & &) (hifat-lstat fs head-path))
       (len (struct-stat->st_size st))
       ((mv fd-table file-table fd &)
        (hifat-open head-path fd-table file-table))
       ((unless (>= fd 0))
        (mv "" fd-table file-table))
       ((mv & & pread-error-code)
        (hifat-pread fd len 0 fs fd-table file-table))
       ((mv fd-table file-table &)
        (hifat-close fd fd-table file-table))
       ((unless (and (<= (len (fat32-path-to-path head-path))
                         100)))
        (mv "" fd-table file-table))
       (head-string (hifat-tar-reg-file-string
                     fs
                     (implode (fat32-path-to-path head-path))))
       ((when (zp pread-error-code))
        (b* (((mv tail-string fd-table file-table)
              (hifat-tar-name-list-string
               fs head-path (cdr name-list)
               fd-table file-table
               dir-stream-table (- entry-count 1))))
          (mv (concatenate 'string
                           head-string tail-string)
              fd-table file-table)))
       ((mv dirp dir-stream-table &)
        (hifat-opendir fs head-path dir-stream-table))
       ((mv names dir-stream-table)
        (hifat-get-names-from-dirp dirp dir-stream-table))
       ((mv & dir-stream-table)
        (hifat-closedir dirp dir-stream-table))
       ((mv head-string fd-table file-table)
        (hifat-tar-name-list-string
         fs (append path (list))
         names fd-table file-table
         dir-stream-table (- entry-count 1)))
       ((mv tail-string fd-table file-table)
        (hifat-tar-name-list-string
         fs path (cdr name-list)
         fd-table file-table
         dir-stream-table (- entry-count 1))))
    (mv
     (concatenate
      'string
      (tar-header-block (implode (fat32-path-to-path head-path))
                        0 *tar-dirtype*)
      head-string tail-string)
     fd-table file-table)))

(defthm
  fd-table-p-of-hifat-tar-name-list-string
  (fd-table-p
   (mv-nth 1
           (hifat-tar-name-list-string fs path name-list fd-table file-table
                                       dir-stream-table entry-count)))
  :hints
  (("goal" :in-theory (e/d (hifat-tar-name-list-string)
                           (append append-of-cons)))))

(defthm
  stringp-of-hifat-tar-name-list-string
  (stringp
   (mv-nth 0
           (hifat-tar-name-list-string fs path name-list fd-table file-table
                                       dir-stream-table entry-count)))
  :hints
  (("goal" :in-theory (e/d (hifat-tar-name-list-string)
                           (append append-of-cons))))
  :rule-classes :type-prescription)

(defthm
  file-table-p-of-hifat-tar-name-list-string
  (file-table-p
   (mv-nth 2
           (hifat-tar-name-list-string fs path name-list fd-table file-table
                                       dir-stream-table entry-count)))
  :hints
  (("goal" :in-theory (e/d (hifat-tar-name-list-string)
                           (append append-of-cons)))))
