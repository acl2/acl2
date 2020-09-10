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
  get-names-from-dirp
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
      ((dirp (mbe :exec dirp :logic (nfix dirp)))
       (dir-stream-table
        (mbe :exec dir-stream-table :logic (dir-stream-table-fix dir-stream-table)))
       ((mv name errno dir-stream-table)
        (hifat-readdir dirp dir-stream-table))
       ((when (or (equal errno *ebadf*)
                  (equal name *empty-fat32-name*)))
        (mv nil dir-stream-table))
       ((mv tail dir-stream-table)
        (get-names-from-dirp dirp dir-stream-table)))
    (mv (list* name tail) dir-stream-table)))

(defthmd get-names-from-dirp-alt-lemma-1
  (implies (and (dir-stream-table-p dir-stream-table)
                (consp (assoc-equal x dir-stream-table)))
           (dir-stream-p (cdr (assoc-equal x dir-stream-table)))))

(defthm get-names-from-dirp-alt-lemma-3
  (implies
   (and
    (not
     (consp
      (dir-stream->file-list (cdr (assoc-equal dirp dir-stream-table)))))
    (dir-stream-table-p dir-stream-table)
    (consp (assoc-equal dirp dir-stream-table)))
   (equal (cdr (assoc-equal dirp dir-stream-table))
          '((file-list))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (dir-stream-p dir-stream->file-list)
                    ())
    :use (:instance get-names-from-dirp-alt-lemma-1
                    (x dirp))
    :expand (strip-cars (cdr (assoc-equal dirp dir-stream-table))))))

(defthm
  get-names-from-dirp-alt-lemma-4
  (implies
   (and
    (member-equal
     "           "
     (cdr (dir-stream->file-list
           (cdr (assoc-equal dirp
                             (dir-stream-table-fix dir-stream-table))))))
    (equal
     (get-names-from-dirp
      dirp
      (put-assoc-equal
       dirp
       (dir-stream
        (cdr
         (dir-stream->file-list
          (cdr (assoc-equal dirp
                            (dir-stream-table-fix dir-stream-table))))))
       (dir-stream-table-fix dir-stream-table)))
     (list
      (take
       (position-equal-ac
        "           "
        (cdr
         (dir-stream->file-list
          (cdr (assoc-equal dirp
                            (dir-stream-table-fix dir-stream-table)))))
        0)
       (cdr
        (dir-stream->file-list
         (cdr (assoc-equal dirp
                           (dir-stream-table-fix dir-stream-table))))))
      (put-assoc-equal
       dirp
       (dir-stream
        (cddr
         (nthcdr
          (position-equal-ac
           "           "
           (cdr
            (dir-stream->file-list
             (cdr (assoc-equal dirp
                               (dir-stream-table-fix dir-stream-table)))))
           0)
          (dir-stream->file-list
           (cdr (assoc-equal dirp
                             (dir-stream-table-fix dir-stream-table)))))))
       (dir-stream-table-fix dir-stream-table)))))
   (equal
    (cons
     (car (dir-stream->file-list
           (cdr (assoc-equal dirp
                             (dir-stream-table-fix dir-stream-table)))))
     (mv-nth
      0
      (get-names-from-dirp
       dirp
       (put-assoc-equal
        dirp
        (dir-stream
         (cdr
          (dir-stream->file-list
           (cdr (assoc-equal dirp
                             (dir-stream-table-fix dir-stream-table))))))
        (dir-stream-table-fix dir-stream-table)))))
    (take
     (position-equal-ac
      "           "
      (cdr (dir-stream->file-list
            (cdr (assoc-equal dirp
                              (dir-stream-table-fix dir-stream-table)))))
      1)
     (dir-stream->file-list
      (cdr (assoc-equal dirp
                        (dir-stream-table-fix dir-stream-table)))))))
  :instructions
  ((:bash
    ("goal"
     :do-not-induct t
     :in-theory (disable (:rewrite position-equal-ac-of-+))
     :use
     (:instance
      (:rewrite position-equal-ac-of-+)
      (n 1)
      (acc 0)
      (lst
       (cdr
        (dir-stream->file-list
         (cdr (assoc-equal dirp
                           (dir-stream-table-fix dir-stream-table))))))
      (item "           "))))
   (:dive 2 1)
   := :top (:dive 2)
   :x :top :bash (:dive 2 1 2)
   := :up
   (:=
    (position-equal-ac
     "           "
     (cdr (dir-stream->file-list
           (cdr (assoc-equal dirp
                             (dir-stream-table-fix dir-stream-table)))))
     0))
   :top (:dive 1 2)
   :=
   :up :s
   :top :bash))

(defthm
  get-names-from-dirp-alt-lemma-5
  (implies
   (and
    (member-equal
     "           "
     (cdr (dir-stream->file-list
           (cdr (assoc-equal dirp
                             (dir-stream-table-fix dir-stream-table))))))
    (equal
     (get-names-from-dirp
      dirp
      (put-assoc-equal
       dirp
       (dir-stream
        (cdr
         (dir-stream->file-list
          (cdr (assoc-equal dirp
                            (dir-stream-table-fix dir-stream-table))))))
       (dir-stream-table-fix dir-stream-table)))
     (list
      (take
       (position-equal-ac
        "           "
        (cdr
         (dir-stream->file-list
          (cdr (assoc-equal dirp
                            (dir-stream-table-fix dir-stream-table)))))
        0)
       (cdr
        (dir-stream->file-list
         (cdr (assoc-equal dirp
                           (dir-stream-table-fix dir-stream-table))))))
      (put-assoc-equal
       dirp
       (dir-stream
        (cddr
         (nthcdr
          (position-equal-ac
           "           "
           (cdr
            (dir-stream->file-list
             (cdr (assoc-equal dirp
                               (dir-stream-table-fix dir-stream-table)))))
           0)
          (dir-stream->file-list
           (cdr (assoc-equal dirp
                             (dir-stream-table-fix dir-stream-table)))))))
       (dir-stream-table-fix dir-stream-table)))))
   (equal
    (mv-nth
     1
     (get-names-from-dirp
      dirp
      (put-assoc-equal
       dirp
       (dir-stream
        (cdr
         (dir-stream->file-list
          (cdr (assoc-equal dirp
                            (dir-stream-table-fix dir-stream-table))))))
       (dir-stream-table-fix dir-stream-table))))
    (put-assoc-equal
     dirp
     (dir-stream
      (cdr
       (nthcdr
        (position-equal-ac
         "           "
         (cdr
          (dir-stream->file-list
           (cdr (assoc-equal dirp
                             (dir-stream-table-fix dir-stream-table)))))
         1)
        (dir-stream->file-list
         (cdr (assoc-equal dirp
                           (dir-stream-table-fix dir-stream-table)))))))
     (dir-stream-table-fix dir-stream-table))))
  :instructions
  ((:bash
    ("goal"
     :in-theory (disable)
     :use
     (:instance
      (:rewrite position-equal-ac-of-+)
      (n 1)
      (acc 0)
      (lst
       (cdr
        (dir-stream->file-list
         (cdr (assoc-equal dirp
                           (dir-stream-table-fix dir-stream-table))))))
      (item "           "))))
   (:dive 1 2)
   := :up :s :top (:dive 2 2 1 1 1)
   := :up (:drop 1)
   :x
   :top :bash))

(defthmd
  get-names-from-dirp-alt
  (equal
   (get-names-from-dirp dirp dir-stream-table)
   (cond
    ((member-equal
      *empty-fat32-name*
      (dir-stream->file-list
       (cdr (assoc-equal (nfix dirp)
                         (dir-stream-table-fix dir-stream-table)))))
     (mv
      (take
       (position-equal
        *empty-fat32-name*
        (dir-stream->file-list
         (cdr (assoc-equal (nfix dirp)
                           (dir-stream-table-fix dir-stream-table)))))
       (dir-stream->file-list
        (cdr (assoc-equal (nfix dirp)
                          (dir-stream-table-fix dir-stream-table)))))
      (put-assoc-equal
       (nfix dirp)
       (dir-stream
        (nthcdr
         (+
          1
          (position-equal
           *empty-fat32-name*
           (dir-stream->file-list
            (cdr (assoc-equal (nfix dirp)
                              (dir-stream-table-fix dir-stream-table))))))
         (dir-stream->file-list
          (cdr (assoc-equal (nfix dirp)
                            (dir-stream-table-fix dir-stream-table))))))
       (dir-stream-table-fix dir-stream-table))))
    ((consp (assoc-equal (nfix dirp)
                         (dir-stream-table-fix dir-stream-table)))
     (mv (dir-stream->file-list
          (cdr (assoc-equal (nfix dirp)
                            (dir-stream-table-fix dir-stream-table))))
         (put-assoc-equal (nfix dirp)
                          (dir-stream nil)
                          (dir-stream-table-fix dir-stream-table))))
    (t (mv (dir-stream->file-list
            (cdr (assoc-equal (nfix dirp)
                              (dir-stream-table-fix dir-stream-table))))
           (dir-stream-table-fix dir-stream-table)))))
  :hints (("goal" :in-theory (e/d (get-names-from-dirp hifat-readdir)
                                  nil)
           :induct (get-names-from-dirp dirp dir-stream-table))))

(defthm fat32-filename-list-p-of-get-names-from-dirp
  (fat32-filename-list-p
   (mv-nth 0
           (get-names-from-dirp dirp dir-stream-table)))
  :hints (("goal" :in-theory (enable get-names-from-dirp
                                     hifat-readdir))))

(defthm dir-stream-table-p-of-get-names-from-dirp
  (dir-stream-table-p
   (mv-nth 1
           (get-names-from-dirp dirp dir-stream-table)))
  :hints (("goal" :in-theory (enable get-names-from-dirp
                                     hifat-readdir))))

(defthm
  no-duplicatesp-of-get-names-from-dirp
  (implies
   (no-duplicatesp-equal
    (dir-stream->file-list
     (cdr (assoc-equal (nfix dirp)
                       (dir-stream-table-fix dir-stream-table)))))
   (no-duplicatesp-equal
    (mv-nth 0
            (get-names-from-dirp dirp dir-stream-table))))
  :hints (("goal" :in-theory (enable get-names-from-dirp-alt))))

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
(defund hifat-tar-name-list-string
  (fs path name-list fd-table file-table dir-stream-table entry-count)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (hifat-no-dups-p fs)
                              (fat32-filename-list-p path)
                              (natp entry-count)
                              (fat32-filename-list-p name-list)
                              (file-table-p file-table)
                              (fd-table-p fd-table)
                              (dir-stream-table-p dir-stream-table))
                  :guard-hints (("goal" :in-theory (e/d (hifat-tar-name-list-string)
                                                        (append append-of-cons))
                                 :do-not-induct t))
                  :measure (nfix entry-count) :verify-guards nil))
  (b* ((fd-table (mbe :exec fd-table :logic (fd-table-fix fd-table)))
       (file-table (mbe :exec file-table :logic (file-table-fix file-table)))
       (dir-stream-table (mbe :exec dir-stream-table
                              :logic (dir-stream-table-fix dir-stream-table)))
       ((unless (and (consp name-list) (not (zp entry-count)))) (mv "" fd-table file-table))
       (head (car name-list))
       (head-path (append path (list head)))
       ((mv st retval &) (hifat-lstat fs head-path))
       ((mv tail-string fd-table file-table)
        (hifat-tar-name-list-string fs path (cdr name-list) fd-table file-table
                                    dir-stream-table (- entry-count 1)))
       ((unless (>= retval 0)) (mv tail-string fd-table file-table))
       (len (struct-stat->st_size st))
       ((mv fd-table file-table fd &) (hifat-open head-path fd-table file-table))
       ((mv & & pread-error-code) (hifat-pread fd len 0 fs fd-table file-table))
       ((mv fd-table file-table &) (hifat-close fd fd-table file-table))
       ((unless (and (<= (len (fat32-path-to-path head-path)) 100))) (mv "" fd-table file-table)))
    (if (zp pread-error-code)
        ;; regular file.
        (b* ((head-string (hifat-tar-reg-file-string fs
                                                     (implode (fat32-path-to-path head-path)))))
          (mv (concatenate 'string head-string tail-string) fd-table file-table))
      ;; directory file.
      (b*
          (((mv dirp dir-stream-table &) (hifat-opendir fs head-path dir-stream-table))
           ((mv names dir-stream-table) (get-names-from-dirp dirp dir-stream-table))
           ((mv & dir-stream-table) (hifat-closedir dirp dir-stream-table))
           ((mv head-string fd-table file-table) (hifat-tar-name-list-string
                                                  fs head-path
                                                  names fd-table file-table
                                                  dir-stream-table (- entry-count 1))))
        (mv (concatenate 'string
                         (tar-header-block (implode (fat32-path-to-path head-path))
                                           0 *tar-dirtype*)
                         head-string tail-string)
            fd-table file-table)))))

(defthm
  fd-table-p-of-hifat-tar-name-list-string-lemma-1
  (not
   (consp
    (assoc-equal (find-new-index (strip-cars alist))
                 alist)))
  :hints
  (("goal" :in-theory (disable (:rewrite find-new-index-correctness-1))
    :use (:instance (:rewrite find-new-index-correctness-1)
                    (fd-list (strip-cars alist))))))

(defthm
  fd-table-p-of-hifat-tar-name-list-string
  (equal
   (mv-nth 1
           (hifat-tar-name-list-string fs path name-list fd-table file-table
                                       dir-stream-table entry-count))
   (fd-table-fix fd-table))
  :hints
  (("goal" :in-theory (e/d (hifat-tar-name-list-string hifat-close hifat-open)
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
  (equal
   (mv-nth 2
           (hifat-tar-name-list-string fs path name-list fd-table file-table
                                       dir-stream-table entry-count))
   (file-table-fix file-table))
  :hints
  (("goal" :in-theory (e/d (hifat-tar-name-list-string hifat-close hifat-open)
                           (append append-of-cons)))))

(defthmd
  hifat-tar-name-list-string-reduction-correctness-lemma-1
  (equal
   (mv-nth 0
           (hifat-tar-name-list-string fs path name-list fd-table file-table
                                       dir-stream-table entry-count))
   (mv-nth 0
           (hifat-tar-name-list-string fs path name-list nil file-table
                                       dir-stream-table entry-count)))
  :hints
  (("goal"
    :in-theory
    (e/d (hifat-tar-name-list-string hifat-open hifat-close hifat-pread)
         (append-of-cons binary-append (:rewrite nth-of-take)
                         (:rewrite nth-when->=-n-len-l)
                         (:rewrite prefixp-when-equal-lengths)
                         (:rewrite fat32-filename-p-correctness-1)
                         (:rewrite stringp-when-nonempty-stringp)
                         (:definition len)
                         (:rewrite prefixp-of-cons-left)
                         (:rewrite take-of-too-many)
                         (:rewrite take-of-take-same)))
    :induct
    (hifat-tar-name-list-string fs path name-list fd-table
                                file-table dir-stream-table entry-count)
    :expand
    (:free (fs path name-list
               fd-table file-table dir-stream-table)
           (hifat-tar-name-list-string fs path name-list fd-table file-table
                                       dir-stream-table entry-count)))))

(defthmd
  hifat-tar-name-list-string-reduction-correctness-lemma-2
  (equal
   (mv-nth 0
           (hifat-tar-name-list-string fs path name-list fd-table file-table
                                       dir-stream-table entry-count))
   (mv-nth 0
           (hifat-tar-name-list-string fs path name-list fd-table nil
                                       dir-stream-table entry-count)))
  :hints
  (("goal"
    :in-theory
    (e/d (hifat-tar-name-list-string hifat-open hifat-close hifat-pread)
         (append-of-cons binary-append (:rewrite nth-of-take)
                         (:rewrite nth-when->=-n-len-l)
                         (:rewrite prefixp-when-equal-lengths)
                         (:rewrite fat32-filename-p-correctness-1)
                         (:rewrite stringp-when-nonempty-stringp)
                         (:definition len)
                         (:rewrite prefixp-of-cons-left)
                         (:rewrite take-of-too-many)
                         (:rewrite take-of-take-same)))
    :induct
    (hifat-tar-name-list-string fs path name-list fd-table
                                file-table dir-stream-table entry-count)
    :expand
    (:free (fs path name-list
               fd-table file-table dir-stream-table)
           (hifat-tar-name-list-string fs path name-list fd-table file-table
                                       dir-stream-table entry-count)))))

(defthm
  hifat-tar-name-list-string-reduction-correctness-lemma-4
  (implies
   (not (m1-directory-file-p (mv-nth 0 (hifat-find-file fs path))))
   (equal
    (mv-nth 0
            (hifat-tar-name-list-string fs path name-list fd-table file-table
                                        dir-stream-table entry-count))
    ""))
  :hints
  (("goal"
    :in-theory (e/d (hifat-tar-name-list-string hifat-lstat hifat-find-file)
                    (append append-of-cons)))))

(defthmd
  hifat-tar-name-list-string-reduction-correctness-lemma-3
  (equal
   (mv-nth 0
           (hifat-tar-name-list-string fs path name-list fd-table file-table
                                       dir-stream-table entry-count))
   (mv-nth 0
           (hifat-tar-name-list-string fs path name-list fd-table file-table
                                       nil entry-count)))
  :hints
  (("goal"
    :in-theory
    (e/d (hifat-tar-name-list-string hifat-open hifat-close
                                     hifat-pread hifat-opendir hifat-closedir
                                     hifat-lstat get-names-from-dirp-alt)
         (append-of-cons binary-append (:rewrite nth-of-take)
                         (:rewrite nth-when->=-n-len-l)
                         (:rewrite prefixp-when-equal-lengths)
                         (:rewrite fat32-filename-p-correctness-1)
                         (:rewrite stringp-when-nonempty-stringp)
                         (:definition len)
                         (:rewrite prefixp-of-cons-left)
                         (:rewrite take-of-too-many)
                         (:rewrite take-of-take-same)
                         (:definition strip-cars)
                         (:linear position-equal-ac-when-member)
                         (:rewrite nthcdr-when->=-n-len-l)
                         (:rewrite m1-directory-file-p-when-m1-file-p)
                         (:definition position-equal-ac)
                         (:rewrite consp-of-nthcdr)
                         (:rewrite hifat-find-file-correctness-3)
                         (:rewrite get-names-from-dirp-alt-lemma-3)
                         (:rewrite
                          dir-stream-table-p-of-cdr-when-dir-stream-table-p)
                         (:rewrite
                          dir-stream-table-p-when-subsetp-equal)
                         (:rewrite consp-car-of-dir-stream-table-fix)
                         (:type-prescription
                          true-listp-nthcdr-type-prescription)
                         (:rewrite take-fewer-of-take-more)
                         (:rewrite dir-stream-table-p-when-not-consp)
                         (:rewrite take-when-atom)
                         (:linear
                          len-of-explode-when-m1-file-contents-p-1)
                         (:rewrite
                          hifat-find-file-correctness-3-lemma-2)
                         (:REWRITE DEFAULT-CAR)
                         (:REWRITE
                          M1-FILE->CONTENTS$INLINE-OF-M1-FILE-FIX-X-NORMALIZE-CONST)
                         (:REWRITE
                          CDR-OF-FAT32-FILENAME-LIST-FIX-X-NORMALIZE-CONST-UNDER-FAT32-FILENAME-LIST-EQUIV)
                         (:REWRITE
                          CONS-OF-FAT32-FILENAME-FIX-X-NORMALIZE-CONST-UNDER-FAT32-FILENAME-LIST-EQUIV)
                         (:REWRITE
                          CONS-OF-FAT32-FILENAME-LIST-FIX-Y-NORMALIZE-CONST-UNDER-FAT32-FILENAME-LIST-EQUIV)
                         (:REWRITE
                          CAR-OF-FAT32-FILENAME-LIST-FIX-X-NORMALIZE-CONST-UNDER-FAT32-FILENAME-EQUIV)
                         (:REWRITE PUT-ASSOC-EQUAL-WITHOUT-CHANGE . 2)
                         (:REWRITE
                          DIR-STREAM-OF-FAT32-FILENAME-LIST-FIX-FILE-LIST-NORMALIZE-CONST)
                         (:REWRITE
                          CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV)
                         (:TYPE-PRESCRIPTION NATP-POSITION-AC)))
    :induct
    (hifat-tar-name-list-string fs path name-list fd-table
                                file-table dir-stream-table entry-count)
    :expand
    (:free (fs path name-list
               fd-table file-table dir-stream-table)
           (hifat-tar-name-list-string fs path name-list fd-table file-table
                                       dir-stream-table entry-count)))))

(defund hifat-tar-name-list-string-reduction
  (fs path name-list entry-count)
  (b*
      (((mv string & &)
        (hifat-tar-name-list-string fs path name-list nil nil nil entry-count)))
    string))

(defthmd
  hifat-tar-name-list-string-reduction-correctness-1
  (equal
   (mv-nth 0
           (hifat-tar-name-list-string fs path name-list fd-table file-table
                                       dir-stream-table entry-count))
   (hifat-tar-name-list-string-reduction fs path name-list entry-count))
  :instructions
  ((:dive 2)
   :x :top (:dive 1)
   (:rewrite hifat-tar-name-list-string-reduction-correctness-lemma-1)
   (:rewrite hifat-tar-name-list-string-reduction-correctness-lemma-2)
   (:rewrite hifat-tar-name-list-string-reduction-correctness-lemma-3)
   :top :s))

(defund alist-shift (alist shift)
  (if (atom alist)
      nil
    (cons (cons (caar alist) (+ shift (cdar alist)))
          (alist-shift (cdr alist) shift))))

(defund
  hifat-tar-name-list-alist
  (fs path name-list entry-count)
  (declare (xargs :measure (nfix entry-count)))
  (b*
      (((unless (and (consp name-list)
                     (not (zp entry-count))))
        nil)
       (head (car name-list))
       (head-path (append path (list head)))
       ((mv st retval &) (hifat-lstat fs head-path))
       (tail-alist
        (hifat-tar-name-list-alist
         fs head-path (cdr name-list) (- entry-count 1)))
       ((unless (>= retval 0)) tail-alist)
       (len (struct-stat->st_size st))
       ((mv fd-table file-table fd &)
        (hifat-open head-path nil nil))
       ((unless (>= fd 0)) nil)
       ((mv & & pread-error-code)
        (hifat-pread fd len 0 fs fd-table file-table))
       ((mv & & &)
        (hifat-close fd fd-table file-table))
       ((unless (and (<= (len (fat32-path-to-path head-path)) 100))) nil)
       (head-string (hifat-tar-reg-file-string
                     fs
                     (implode (fat32-path-to-path head-path))))
       ((when (zp pread-error-code))
        (cons (cons head-path 0)
              (alist-shift tail-alist (len head-string))))
       ((mv dirp dir-stream-table &)
        (hifat-opendir fs head-path nil))
       ((mv names dir-stream-table)
        (get-names-from-dirp dirp dir-stream-table))
       ((mv & &)
        (hifat-closedir dirp dir-stream-table))
       (head-alist
        (hifat-tar-name-list-alist fs (append path (list head)) names (- entry-count 1)))
       (tail-alist
        (hifat-tar-name-list-alist fs path (cdr name-list) (- entry-count 1))))
    (append
     (alist-shift
      head-alist
      (length
       (tar-header-block (implode (fat32-path-to-path head-path))
                         0 *tar-dirtype*)))
     (alist-shift
      tail-alist
      (+
       (length
        (tar-header-block (implode (fat32-path-to-path head-path))
                          0 *tar-dirtype*))
       (length (hifat-tar-name-list-string-reduction
             fs (append path (list head))
             names (- entry-count 1))))))))

(defthm consp-of-assoc-of-alist-shift
  (implies (alistp alist)
           (equal (consp (assoc-equal x (alist-shift alist shift)))
                  (consp (assoc-equal x alist))))
  :hints (("goal" :in-theory (enable alist-shift))))

(defthm alistp-of-alist-shift
  (alistp (alist-shift alist shift))
  :hints (("goal" :in-theory (enable alist-shift))))

(defthm alistp-of-hifat-tar-name-list-alist
  (alistp (hifat-tar-name-list-alist fs path name-list entry-count))
  :hints (("goal" :in-theory (enable hifat-tar-name-list-alist))))

(defthm assoc-of-alist-shift
  (implies (case-split (not (null x)))
           (equal (assoc-equal x (alist-shift alist shift))
                  (if (atom (assoc-equal x alist))
                      nil
                      (cons (car (assoc-equal x alist))
                            (+ shift (cdr (assoc-equal x alist)))))))
  :hints (("goal" :in-theory (enable alist-shift))))

(defthm strip-cars-of-alist-shift
  (equal (strip-cars (alist-shift alist shift))
         (strip-cars alist))
  :hints (("goal" :in-theory (enable alist-shift))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-1
  (consp
   (assoc-equal
    (cdr (assoc-equal (mv-nth 2 (hifat-open path fd-table file-table))
                      (mv-nth 0
                              (hifat-open path fd-table file-table))))
    (mv-nth 1
            (hifat-open path fd-table file-table))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-open)))
  :rule-classes :type-prescription)

(defthm
  hifat-tar-name-list-alist-correctness-lemma-3
  (implies
   (not (equal (mv-nth 1 (hifat-find-file fs path))
               0))
   (>
    (mv-nth
     1
     (hifat-find-file
      fs
      (file-table-element->fid
       (cdr
        (assoc-equal
         (cdr (assoc-equal (mv-nth 2 (hifat-open path fd-table file-table))
                           (mv-nth 0
                                   (hifat-open path fd-table file-table))))
         (mv-nth 1
                 (hifat-open path fd-table file-table)))))))
    0))
  :hints (("goal" :in-theory (enable hifat-open)))
  :rule-classes :linear)

(defthm hifat-tar-name-list-alist-correctness-lemma-4
  (implies (and (integerp start)
                (equal start end)
                (stringp seq))
           (equal (subseq seq start end) ""))
  :hints (("goal" :in-theory (enable subseq subseq-list))))

(defthm hifat-tar-name-list-alist-correctness-lemma-7
  (equal (subseq "" start end)
         (implode (take (+ end (- start)) nil)))
  :hints (("goal" :in-theory (e/d (subseq subseq-list repeat)
                                  (take-of-too-many take-when-atom)))))

(defthm
  stringp-of-hifat-tar-name-list-string-reduction
  (stringp
   (hifat-tar-name-list-string-reduction fs path name-list entry-count))
  :hints (("goal" :do-not-induct t
           :use hifat-tar-name-list-string-reduction-correctness-1))
  :rule-classes :type-prescription)

(defthm
  hifat-tar-name-list-alist-correctness-lemma-2
  (and (< 0
          (len (explode (tar-header-block path len typeflag))))
       (not (equal (tar-header-block path len typeflag)
                   "")))
  :hints (("goal" :in-theory (enable tar-header-block)))
  :rule-classes
  ((:linear
    :corollary (< 0
                  (len (explode (tar-header-block path len typeflag)))))
   (:rewrite :corollary (not (equal (tar-header-block path len typeflag)
                                    "")))))

(defthm hifat-tar-name-list-alist-correctness-lemma-10
  (iff (prefixp (append y x) y) (atom x))
  :hints (("goal" :in-theory (enable prefixp))))

(defthm hifat-tar-name-list-alist-correctness-lemma-15
  (iff (equal x (append x y))
       (equal y (if (consp x) (cdr (last x)) x))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-13
  (implies
   (case-split (or (not (prefixp path1 path2))
                   (equal path1 path2)))
   (and
    (not
     (consp (assoc-equal path2
                         (hifat-tar-name-list-alist
                          fs path1 name-list entry-count))))
    (atom
     (assoc-equal path2
                  (hifat-tar-name-list-alist
                   fs path1 name-list entry-count)))))
  :hints
  (("goal" :in-theory (enable hifat-tar-name-list-alist))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-16
  (not
   (member-equal nil
    (strip-cars
                 (hifat-tar-name-list-alist fs path name-list entry-count))))
  :hints (("goal" :in-theory (e/d (hifat-tar-name-list-alist)
                                  (append append-of-cons))))
  :rule-classes :type-prescription)

(defthm
  hifat-tar-name-list-alist-correctness-lemma-17
  (implies (and (consp path)
                (not (zp (mv-nth 1 (hifat-find-file fs path)))))
           (equal (hifat-tar-name-list-alist fs path name-list entry-count)
                  nil))
  :hints (("goal" :in-theory (enable hifat-tar-name-list-alist alist-shift
                                     hifat-pread hifat-lstat hifat-open))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-18
  (not
   (consp
    (assoc-equal nil
                 (hifat-tar-name-list-alist fs path name-list entry-count))))
  :hints (("goal" :in-theory (enable hifat-tar-name-list-alist alist-shift)))
  :rule-classes :type-prescription)

(defthm
  hifat-tar-name-list-alist-correctness-lemma-19
  (implies
   (consp
    (assoc-equal path2
                 (hifat-tar-name-list-alist fs path1 name-list entry-count)))
   (natp
    (cdr (assoc-equal
          path2
          (hifat-tar-name-list-alist fs path1 name-list entry-count)))))
  :hints (("goal" :in-theory (enable hifat-tar-name-list-alist alist-shift)))
  :rule-classes :type-prescription)

(defthm
  hifat-tar-name-list-alist-correctness-lemma-20
  (implies (and (consp name-list)
                (prefixp (append path1 (list name))
                         path2)
                (not (member-equal name name-list)))
           (not
            (prefixp (append path1 (list (car name-list)))
                     path2)))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable append-when-prefixp
                        (:rewrite equal-when-append-same))
    :use ((:instance append-when-prefixp
                     (x (append path1 (list (car name-list))))
                     (y path2))
          (:instance append-when-prefixp
                     (x (append path1 (list name)))
                     (y path2))
          (:instance (:rewrite equal-when-append-same)
                     (y2 (cons name (cdr (nthcdr (len path1) path2))))
                     (y1 (cons (car name-list)
                               (cdr (nthcdr (len path1) path2))))
                     (x path1))))))

(encapsulate
  () (local (in-theory (disable atom)))

  (defthmd
    hifat-tar-name-list-alist-correctness-lemma-11
    (implies
     (and (member-equal
           path2
           (strip-cars (hifat-tar-name-list-alist
                        fs path1 name-list entry-count)))
          (not (member-equal name name-list)))
     (not (prefixp (append path1 (list name))
                   path2)))
    :hints
    (("goal"
      :in-theory (e/d (hifat-tar-name-list-alist
                       hifat-pread hifat-open hifat-lstat)
                      (append append-of-cons))))
    :rule-classes
    (:rewrite
     (:rewrite
      :corollary
      (implies
       (and (not (null path2))
            (prefixp (append path1 (list name))
                     path2)
            (not (member-equal name name-list)))
       (not
        (consp
         (assoc-equal path2
                      (hifat-tar-name-list-alist
                       fs path1 name-list entry-count))))))
     (:rewrite
      :corollary
      (implies
       (and (not (null path2))
            (prefixp (append path1 (list name))
                     path2)
            (not (member-equal name name-list)))
       (atom (assoc-equal path2
                          (hifat-tar-name-list-alist
                           fs path1 name-list entry-count))))
      :hints (("goal" :in-theory (enable atom)))))))

(encapsulate
  ()

  (local (include-book "std/basic/inductions" :dir :system))
  (local (include-book "std/lists/intersectp" :dir :system))

  (defthm
    hifat-tar-name-list-alist-correctness-lemma-22
    (implies
     (and
      (not (zp n))
      (not (member-equal (car name-list)
                         (cdr name-list))))
     (not
      (prefixp
       (append path1 (list (car name-list)))
       (nth (+ -1 n)
            (strip-cars (hifat-tar-name-list-alist fs path1 (cdr name-list)
                                                   (+ -1 entry-count)))))))
    :hints
    (("goal"
      :use
      (:instance
       hifat-tar-name-list-alist-correctness-lemma-11
       (path2
        (nth (+ -1 n)
             (strip-cars (hifat-tar-name-list-alist fs path1 (cdr name-list)
                                                    (+ -1 entry-count)))))
       (name (car name-list))
       (path1 path1)
       (name-list (cdr name-list))
       (fs fs)
       (entry-count (- entry-count 1))))))

  (local
   (defthmd
     lemma-1
     (implies
      (not (member-equal (car name-list)
                         (cdr name-list)))
      (not
       (intersectp-equal
        (take n
              (strip-cars (hifat-tar-name-list-alist fs path1 (cdr name-list)
                                                     (+ -1 entry-count))))
        (strip-cars
         (hifat-tar-name-list-alist
          fs (append path1 (list (car name-list)))
          (mv-nth
           0
           (get-names-from-dirp
            0
            (list
             (cons
              0
              (dir-stream
               (<<-sort
                (strip-cars
                 (m1-file->contents
                  (mv-nth
                   0
                   (hifat-find-file
                    (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
                    (list (car name-list))))))))))))
          (+ -1 entry-count))))))
     :hints
     (("goal"
       :induct (dec-induct n)
       :in-theory (e/d nil (append-of-take-and-cons))
       :expand
       (:with
        take-as-append-and-nth
        (take n
              (strip-cars (hifat-tar-name-list-alist fs path1 (cdr name-list)
                                                     (+ -1 entry-count)))))))))

  (defthm
    hifat-tar-name-list-alist-correctness-lemma-23
    (implies
     (not (member-equal (car name-list)
                        (cdr name-list)))
     (not
      (intersectp-equal
       (strip-cars (hifat-tar-name-list-alist fs path1 (cdr name-list)
                                              (+ -1 entry-count)))
       (strip-cars
        (hifat-tar-name-list-alist
         fs (append path1 (list (car name-list)))
         (mv-nth
          0
          (get-names-from-dirp
           0
           (list
            (cons
             0
             (dir-stream
              (<<-sort
               (strip-cars
                (m1-file->contents
                 (mv-nth
                  0
                  (hifat-find-file
                   (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
                   (list (car name-list))))))))))))
         (+ -1 entry-count))))))
    :hints
    (("goal" :do-not-induct t
      :use (:instance lemma-1
                      (n
                       (len
                        (strip-cars (hifat-tar-name-list-alist fs path1 (cdr name-list)
                                                               (+ -1
                                                                  entry-count)))))))))

  (defthm
    hifat-tar-name-list-alist-correctness-lemma-24
    (implies
     (and
      (not (consp path1))
      (not (member-equal (car name-list)
                         (cdr name-list)))
      (equal
       (car name-list)
       (car (nth (+ -1 n)
                 (strip-cars (hifat-tar-name-list-alist fs path1 (cdr name-list)
                                                        (+ -1 entry-count)))))))
     (not
      (consp
       (nth (+ -1 n)
            (strip-cars (hifat-tar-name-list-alist fs path1 (cdr name-list)
                                                   (+ -1 entry-count)))))))
    :hints
    (("goal"
      :use
      (:instance
       hifat-tar-name-list-alist-correctness-lemma-11
       (path2
        (nth (+ -1 n)
             (strip-cars (hifat-tar-name-list-alist fs path1 (cdr name-list)
                                                    (+ -1 entry-count)))))
       (name-list (cdr name-list))
       (entry-count (- entry-count 1))
       (name (car name-list))))))

  (local
   (defthmd
     lemma-2
     (implies
      (and (not (consp path1))
           (not (member-equal (car name-list)
                              (cdr name-list))))
      (not
       (intersectp-equal
        (take n
              (strip-cars (hifat-tar-name-list-alist fs path1 (cdr name-list)
                                                     (+ -1 entry-count))))
        (strip-cars
         (hifat-tar-name-list-alist
          fs (list (car name-list))
          (mv-nth
           0
           (get-names-from-dirp
            0
            (list
             (cons
              0
              (dir-stream
               (<<-sort
                (strip-cars
                 (m1-file->contents
                  (mv-nth 0
                          (hifat-find-file fs (list (car name-list))))))))))))
          (+ -1 entry-count))))))
     :hints
     (("goal"
       :induct (dec-induct n)
       :in-theory (e/d nil (append-of-take-and-cons))
       :expand
       (:with
        take-as-append-and-nth
        (take n
              (strip-cars (hifat-tar-name-list-alist fs path1 (cdr name-list)
                                                     (+ -1 entry-count)))))))))

  (defthm
    hifat-tar-name-list-alist-correctness-lemma-25
    (implies
     (and (not (consp path1))
          (not (member-equal (car name-list)
                             (cdr name-list))))
     (not
      (intersectp-equal
       (strip-cars (hifat-tar-name-list-alist fs path1 (cdr name-list)
                                              (+ -1 entry-count)))
       (strip-cars
        (hifat-tar-name-list-alist
         fs (list (car name-list))
         (mv-nth
          0
          (get-names-from-dirp
           0
           (list
            (cons
             0
             (dir-stream
              (<<-sort
               (strip-cars
                (m1-file->contents
                 (mv-nth 0
                         (hifat-find-file fs (list (car name-list))))))))))))
         (+ -1 entry-count))))))
     :hints
     (("goal"
       :do-not-induct t
       :use (:instance lemma-2 (n
                                (len (hifat-tar-name-list-alist fs path1 (cdr name-list)
                                                                (+ -1 entry-count)))))))))

(encapsulate
  ()

  (local
   (defthmd lemma-1 (iff (equal (len (explode str1)) 0)
                         (equal (explode str1) nil))
     :hints
     (("goal" :expand (len (explode str1))))))

  (local
   (defthmd lemma-2
     (implies (and (<= 0 (- start)) (<= 0 start))
              (integerp (- start)))))

  (defthm
    subseq-of-string-append
    (equal
     (subseq (string-append str1 str2)
             start end)
     (cond ((and (not (stringp str2))
                 (not (stringp str1)))
            (subseq "" 0 (- end start)))
           ((not (stringp str1))
            (subseq str2 start end))
           ((not (stringp str2))
            (subseq str1 start end))
           ((not (integerp (- end start))) "")
           ((and (< end (+ start (len (explode str1))))
                 (not (null end))
                 (natp (- end start))
                 (not (integerp start)))
            (subseq str1 0 (- end start)))
           ((and (>= end (+ start (len (explode str1))))
                 (not (null end))
                 (integerp (- end start))
                 (not (integerp start)))
            (string-append str1
                           (subseq str2 0
                                   (- end (+ start (len (explode str1)))))))
           ((and (< start 0)
                 (not (null end))
                 (natp (- end start))
                 (>= end (+ start (len (explode str1)))))
            (string-append str1
                           (subseq str2 0
                                   (- end (+ start (len (explode str1)))))))
           ((and (< start 0)
                 (not (null end))
                 (< end (+ start (len (explode str1))))
                 (> end start))
            (subseq str1 0 (- end start)))
           ((not (integerp (- start))) "")
           ((and (not (null end))
                 (not (acl2-numberp end))
                 (not (integerp start)))
            "")
           ((and (acl2-numberp end)
                 (not (integerp end)))
            "")
           ((and (integerp start)
                 (<= start (len (explode str1)))
                 (<= 0 start)
                 (null end))
            (string-append (subseq str1 start nil)
                           str2))
           ((and (< (len (explode str1)) start)
                 (null end)
                 (natp (- (+ (len (explode str1))
                             (len (explode str2)))
                          start)))
            (subseq str2 (- start (len (explode str1)))
                    nil))
           ((and (<= (+ start (len (explode str1))) end)
                 (not (integerp start))
                 (< (- start) (len (explode str1))))
            (string-append str1
                           (subseq str2 0
                                   (+ (- end (+ start (len (explode str1))))))))
           ((and (<= (+ start (len (explode str1))) end)
                 (not (integerp start))
                 (< (len (explode str1)) start)
                 (<= start
                     (+ (len (explode str1))
                        (len (explode str2)))))
            (string-append str1
                           (subseq str2 0
                                   (+ (- end (+ start (len (explode str1))))))))
           ((and (<= (+ start (len (explode str1))) end)
                 (< start 0)
                 (not (null end)))
            (string-append str1
                           (subseq str2 0
                                   (+ (- end (+ start (len (explode str1))))))))
           ((and (not (integerp start))
                 (< end (+ start (len (explode str1))))
                 (< start end))
            (subseq str1 0 (- end start)))
           ((and (not (natp (- (+ (len (explode str1))
                                  (len (explode str2)))
                               start)))
                 (null end))
            "")
           ((and (<= start 0)
                 (equal (len (explode str1)) 0)
                 (not (null end))
                 (not (acl2-numberp end)))
            (string-append str1 (subseq str2 0 (- start))))
           ((and (not (integerp start))
                 (equal (len (explode str1)) 0)
                 (not (null end))
                 (not (acl2-numberp end)))
            str1)
           ((and (< 0 start)
                 (not (null end))
                 (not (acl2-numberp end)))
            "")
           ((and (< (- start) (len (explode str1)))
                 (not (null end))
                 (not (acl2-numberp end)))
            (subseq str1 0 (- start)))
           ((and (< start 0)
                 (not (null end))
                 (<= (len (explode str1)) (- start))
                 (not (acl2-numberp end)))
            (string-append str1
                           (subseq str2
                                   0 (- (+ start (len (explode str1)))))))
           ((and (< start 0)
                 (<= (+ (len (explode str1)) start) end)
                 (integerp end))
            (string-append str1
                           (subseq str2 0
                                   (- end (+ start (len (explode str1)))))))
           ((and (< (len (explode str1)) start)
                 (<= start
                     (+ (len (explode str1))
                        (len (explode str2))))
                 (null end))
            (subseq str2 (- start (len (explode str1)))
                    nil))
           ((and (< (len (explode str1)) start)
                 (<= start
                     (+ (len (explode str1))
                        (len (explode str2))))
                 (integerp end))
            (subseq str2 (- start (len (explode str1)))
                    (- end (len (explode str1)))))
           ((and (integerp start)
                 (<= start (len (explode str1)))
                 (<= 0 start)
                 (< (len (explode str1)) end)
                 (integerp end))
            (string-append (subseq str1 start nil)
                           (subseq str2 0 (- end (len (explode str1))))))
           ((and (<= 0 start)
                 (<= start end)
                 (<= end (len (explode str1)))
                 (integerp end))
            (subseq str1 start end))
           ((and (integerp start)
                 (< start 0)
                 (null end))
            (string-append str1
                           (subseq str2 0 (- (len (explode str2)) start))))
           ((and (< start 0)
                 (not (null end))
                 (<= start end)
                 (< end (+ start (len (explode str1)))))
            (subseq str1 0 (- end start)))
           ((and (< start 0)
                 (not (null end))
                 (<= start end)
                 (< end (+ start (len (explode str1)))))
            (subseq str1 start end))
           ((and (integerp start)
                 (< (+ (len (explode str1))
                       (len (explode str2)))
                    start))
            (subseq "" start end))
           ((and (acl2-numberp end)
                 (not (integerp end)))
            "")
           ((and (not (null end)) (< end start))
            "")
           (t (implode (append (explode str1)
                               (explode str2))))))
    :hints (("goal" :in-theory (e/d (subseq subseq-list) ((:e force)))
             :do-not-induct t
             :use ((:instance painful-debugging-lemma-21
                              (x start)
                              (y (- (len (explode str1)))))
                   (:theorem (iff (integerp (+ (- start)
                                               (len (explode str1))
                                               (len (explode str2))))
                                  (integerp (- start))))
                   lemma-1 lemma-2))))

  (defthm hifat-tar-name-list-alist-correctness-lemma-28
    (implies
     (stringp seq)
     (equal (subseq seq 0 (len (explode seq))) seq))
    :hints (("Goal" :in-theory (enable subseq subseq-list)))))

;; Move later.

(defthm
  hifat-tar-name-list-alist-correctness-lemma-31
  (equal (mv-nth '0
                 (hifat-tar-name-list-string fs (cons (car name-list1) 'nil)
                                             name-list2 fd-table file-table
                                             dir-stream-table entry-count))
         (hifat-tar-name-list-string-reduction fs (list (car name-list1))
                                               name-list2 entry-count))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (enable (:rewrite hifat-tar-name-list-string-reduction-correctness-1)))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-30
  (implies
   (m1-directory-file-p
    (mv-nth
     0
     (hifat-find-file fs
                      (file-table-element->fid
                       (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                         file-table))))))
   (> (mv-nth 2
              (hifat-pread fd count offset fs fd-table file-table))
      0))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-pread)))
  :rule-classes :linear)

(defthm
  hifat-tar-name-list-alist-correctness-lemma-32
  (implies
   (and
    (consp (assoc-equal fd fd-table))
    (consp (assoc-equal (cdr (assoc-equal fd fd-table))
                        file-table))
    (not
     (m1-directory-file-p
      (mv-nth
       0
       (hifat-find-file fs
                        (file-table-element->fid
                         (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                           file-table)))))))
    (equal
     (mv-nth
      1
      (hifat-find-file fs
                       (file-table-element->fid
                        (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                          file-table)))))
     0))
   (equal (mv-nth 2
                  (hifat-pread fd count offset fs fd-table file-table))
          0))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-pread))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-14
  (equal (mv-nth '0
                 (hifat-tar-name-list-string
                  fs
                  (binary-append path1 (cons (car name-list1) 'nil))
                  name-list2 fd-table file-table
                  dir-stream-table entry-count))
         (hifat-tar-name-list-string-reduction
          fs
          (append path1 (list (car name-list1)))
          name-list2 entry-count))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (enable (:rewrite hifat-tar-name-list-string-reduction-correctness-1)))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-36
  (implies
   (and
    (consp path)
    (consp
     (assoc-equal path2
                  (hifat-tar-name-list-alist fs path name-list entry-count))))
   (equal (mv-nth 1 (hifat-lstat fs path))
          0))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-lstat))))

(encapsulate
  ()

  (local (in-theory
          (e/d (;; Enabling the definition lemma just leads to sadness with
                ;; regards to hifat-tar-name-list-string-reduction. The small
                ;; number of subgoals which need the definition should be
                ;; handled with expand hints.
                (:induction hifat-tar-name-list-string)
                hifat-tar-name-list-alist
                hifat-open hifat-lstat
                ;; I don't know if I can justify enabling every system call,
                ;; but this one has to be enabled on account of really stupid
                ;; subgoals.
                hifat-opendir
                get-names-from-dirp-alt painful-debugging-lemma-21)
               (append-of-cons
                binary-append
                string-append
                take-of-too-many
                (:rewrite nthcdr-when->=-n-len-l)
                (:rewrite take-of-len-free)
                (:linear position-equal-ac-when-member)
                (:definition position-equal-ac)
                (:rewrite consp-of-nthcdr)
                (:rewrite
                 dir-stream-table-p-when-subsetp-equal)
                (:rewrite hifat-to-lofat-inversion-lemma-2)
                (:rewrite <<-sort-consp)
                (:definition strip-cars)
                (:rewrite m1-directory-file-p-when-m1-file-p)
                (:rewrite true-listp-when-string-list)
                (:rewrite hifat-find-file-correctness-3)
                (:definition string-listp)
                (:rewrite
                 string-listp-when-fat32-filename-list-p)
                (:linear
                 len-when-hifat-bounded-file-alist-p . 2)
                (:linear
                 len-when-hifat-bounded-file-alist-p . 1)
                (:rewrite m1-regular-file-p-correctness-1)
                (:definition nthcdr)
                (:definition atom)
                (:definition min)
                (:definition nfix)
                (:definition natp)
                (:definition fat32-path-to-path)))))

  (defthm
    not-consp-assoc-nil-hifat-tar-name-list-alist
    (not
     (consp
      (assoc-equal nil
                   (hifat-tar-name-list-alist fs path name-list entry-count))))
    :rule-classes :type-prescription)

  (defthm
    acl2-numberp-of-cdr-of-assoc-of-hifat-tar-name-list-alist
    (implies
     (consp
      (assoc-equal path2
                   (hifat-tar-name-list-alist fs path1 name-list entry-count)))
     (acl2-numberp
      (cdr
       (assoc-equal path2
                    (hifat-tar-name-list-alist fs path1 name-list entry-count)))))
    :rule-classes :type-prescription)

  (defthm
    hifat-tar-name-list-alist-correctness-lemma-5
    (implies (and (not (zp (mv-nth 1 (hifat-find-file fs path))))
                  (consp path))
             (equal (hifat-tar-name-list-alist fs path name-list entry-count)
                    nil))
    :hints (("goal" :in-theory (e/d (alist-shift hifat-pread) nil))))

  (defthm
    hifat-tar-name-list-alist-correctness-lemma-6
    (implies
     (consp
      (assoc-equal path2
                   (hifat-tar-name-list-alist fs path1 name-list entry-count)))
     (natp
      (cdr (assoc-equal
            path2
            (hifat-tar-name-list-alist fs path1 name-list entry-count)))))
    :rule-classes :type-prescription)

  (defthm
    hifat-tar-name-list-alist-correctness-lemma-8
    (implies
     (equal (mv-nth 1 (hifat-find-file fs path))
            0)
     (equal
      (mv-nth
       1
       (hifat-find-file
        fs
        (file-table-element->fid
         (cdr
          (assoc-equal
           (cdr (assoc-equal (mv-nth 2 (hifat-open path fd-table file-table))
                             (mv-nth 0
                                     (hifat-open path fd-table file-table))))
           (mv-nth 1
                   (hifat-open path fd-table file-table)))))))
      0))
    :hints (("goal" :do-not-induct t
             :in-theory (enable hifat-open))))

  (defthm
    hifat-tar-name-list-alist-correctness-lemma-9
    (implies
     (and
      (not (<= (mv-nth 1 (hifat-find-file fs '("           ")))
               0)))
     (not
      (consp
       (assoc-equal
        path2
        (hifat-tar-name-list-alist
         fs '(".          ")
         (mv-nth
          0
          (get-names-from-dirp (mv-nth 0
                                       (hifat-opendir fs '(".          ") nil))
                               (mv-nth 1
                                       (hifat-opendir fs '(".          ")
                                                      nil))))
         (+ -1 entry-count))))))
    :hints (("goal" :do-not-induct t
             :in-theory (enable hifat-open hifat-find-file)))
    :rule-classes :type-prescription)

  (defthm
    hifat-tar-name-list-alist-correctness-lemma-26
    (implies
     (no-duplicatesp-equal name-list)
     (no-duplicatesp-equal
      (strip-cars (hifat-tar-name-list-alist fs path1 name-list entry-count))))
    :hints
    (("goal"
      :in-theory (e/d (hifat-opendir strip-cars)
                      (take-when-prefixp prefixp-of-cons-right
                                         take-of-cons get-names-from-dirp-alt)))))

  ;; This lemma is gathering too many case-splits. We'll have to disable some
  ;; of the splitter lemmas.
  ;; The degree to which it's becoming difficult to prove this with lemmas
  ;; about hifat-pread, hifat-lstat and such illustrates that perhaps
  ;; separation logic would have been the right way to go here...
  (defthm
    hifat-tar-name-list-alist-correctness-1
    (implies
     (consp
      (assoc-equal path2
                   (hifat-tar-name-list-alist fs path1 name-list entry-count)))
     (and
      (subseq
       (mv-nth
        0
        (hifat-tar-name-list-string fs path1 name-list fd-table file-table
                                    dir-stream-table entry-count))
       (cdr (assoc-equal
             path2
             (hifat-tar-name-list-alist fs path1 name-list entry-count)))
       (+
        (cdr (assoc-equal
              path2
              (hifat-tar-name-list-alist fs path1 name-list entry-count)))
        (length
         (hifat-tar-reg-file-string fs
                                    (implode (fat32-path-to-path path2))))))
      (>=
       (length
        (mv-nth
         0
         (hifat-tar-name-list-string fs path1 name-list fd-table file-table
                                     dir-stream-table entry-count)))
       (+
        (cdr (assoc-equal
              path2
              (hifat-tar-name-list-alist fs path1 name-list entry-count)))
        (length
         (hifat-tar-reg-file-string fs
                                    (implode (fat32-path-to-path path2))))))))
    :hints
    (("goal"
      :induct
      (hifat-tar-name-list-string fs path1 name-list fd-table
                                  file-table dir-stream-table entry-count)
      :expand
      ((hifat-tar-name-list-alist fs path1 name-list entry-count)
       (hifat-tar-name-list-string fs path1 name-list fd-table file-table
                                   dir-stream-table entry-count))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (consp
        (assoc-equal path2
                     (hifat-tar-name-list-alist fs path1 name-list entry-count)))
       (subseq
        (mv-nth
         0
         (hifat-tar-name-list-string fs path1 name-list fd-table file-table
                                     dir-stream-table entry-count))
        (cdr (assoc-equal
              path2
              (hifat-tar-name-list-alist fs path1 name-list entry-count)))
        (+
         (cdr (assoc-equal
               path2
               (hifat-tar-name-list-alist fs path1 name-list entry-count)))
         (length
          (hifat-tar-reg-file-string fs
                                     (implode (fat32-path-to-path path2))))))))
     (:linear
      :corollary
      (implies
       (consp
        (assoc-equal path2
                     (hifat-tar-name-list-alist fs path1 name-list entry-count)))
       (>=
        (length
         (mv-nth
          0
          (hifat-tar-name-list-string fs path1 name-list fd-table file-table
                                      dir-stream-table entry-count)))
        (+
         (cdr (assoc-equal
               path2
               (hifat-tar-name-list-alist fs path1 name-list entry-count)))
         (length
          (hifat-tar-reg-file-string fs
                                     (implode (fat32-path-to-path path2)))))))))))
