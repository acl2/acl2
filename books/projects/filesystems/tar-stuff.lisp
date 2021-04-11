(in-package "ACL2")

(include-book "test-stuff")
(include-book "std/alists/remove-assocs" :dir :system)

(local (in-theory (e/d
                   ()
                   ((:definition str::strprefixp$inline)
                    (:linear len-when-prefixp)
                    (:rewrite
                     append-nthcdr-dirname-basename-lemma-1
                     . 3)
                    (:linear listpos-upper-bound-strong-2)
                    (:rewrite <<-sort-consp)
                    (:rewrite no-duplicatesp-of-member)
                    (:linear getopt::defoptions-lemma-8)
                    (:rewrite assoc-of-car-when-member)
                    (:definition remove-equal)
                    (:rewrite subsetp-of-remove2)
                    (:rewrite prefixp-of-append-arg2)
                    (:rewrite true-listp-when-string-list)
                    (:rewrite strip-cars-of-hifat-file-alist-fix)
                    (:rewrite
                     string-listp-when-fat32-filename-list-p)
                    (:rewrite fat32-filename-list-p-of-remove)
                    (:linear len-of-member)
                    (:rewrite
                     remove-duplicates-when-no-duplicatesp)))))

(defconst *tar-regtype* #\0)
(defconst *tar-dirtype* #\5)
(defconst *tar-block-size* 512)
(defconst *tar-blank-block*
  (coerce (make-list *tar-block-size*
                     :initial-element (code-char 0))
          'string))

(local
 (in-theory (disable nth update-nth ceiling floor mod true-listp take member-equal)))

(defthmd list-equiv-when-true-listp
  (implies (and (true-listp x) (true-listp y))
           (iff (list-equiv x y) (equal x y)))
  :hints (("goal" :in-theory (enable fast-list-equiv)
           :induct (fast-list-equiv x y))))

(defthm consp-of-remove-assocs-equal
  (iff (consp (remove-assocs-equal keys alist))
       (not (subsetp-equal (strip-cars alist) keys)))
  :hints (("goal" :in-theory (enable remove-assocs-equal))))

(defthm m1-file-alist-p-of-remove-assocs-equal
  (implies (m1-file-alist-p alist)
           (m1-file-alist-p (remove-assocs-equal keys alist)))
  :hints (("goal" :in-theory (enable remove-assocs-equal))))

(defthm assoc-of-remove-assocs
  (equal (assoc-equal x (remove-assocs-equal keys alist))
         (if (member-equal x keys)
             nil (assoc-equal x alist)))
  :hints (("goal" :in-theory (enable remove-assocs-equal))))

(defthm remove-assocs-equal-when-atom
  (implies (not (intersectp-equal (strip-cars alist)
                                  keys))
           (equal (remove-assocs-equal keys alist)
                  (true-list-fix alist)))
  :hints (("goal" :in-theory (e/d (remove-assocs-equal)
                                  (intersectp-is-commutative)))))

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
  (fat32$c path state)
  (declare
   (xargs
    :stobjs (fat32$c state)
    :guard (and (lofat-fs-p fat32$c)
                (fat32-filename-list-p path)
                (state-p state)
                (open-output-channel-p *standard-co* :character
                                       state))))
  (b* (((mv fat32$c retval &)
        (lofat-mkdir fat32$c path))
       (state (princ$ retval *standard-co* state))
       (state (princ$ ": value of retval, from lofat-mkdir" *standard-co* state))
       (state (newline *standard-co* state)))
    (mv fat32$c state)))

(defund process-reg-file (fat32$c path file-text file-table
                                          fd-table state)
  (declare (xargs :stobjs (fat32$c state)
                  :guard (and (lofat-fs-p fat32$c)
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
        (mv fat32$c fd-table file-table state))
       ((mv fat32$c retval &) (lofat-pwrite fd
                                                    file-text
                                                    0
                                                    fat32$c
                                                    fd-table
                                                    file-table))
       (state (princ$ retval *standard-co* state))
       (state (princ$ ": value of retval, from lofat-pwrite" *standard-co* state))
       (state (newline *standard-co* state))
       ((mv fd-table file-table &) (lofat-close fd fd-table file-table)))
    (mv fat32$c fd-table file-table state)))

(defthm
  fd-table-p-of-process-reg-file
  (fd-table-p
   (mv-nth 1
           (process-reg-file fat32$c path
                             file-text file-table fd-table state)))
  :hints
  (("goal" :in-theory (enable process-reg-file lofat-close))))

(defthm
  file-table-p-of-process-reg-file
  (file-table-p
   (mv-nth 2
           (process-reg-file fat32$c path
                             file-text file-table fd-table state)))
  :hints
  (("goal" :in-theory (enable process-reg-file lofat-close))))

(defthm
  lofat-fs-p-of-process-reg-file
  (implies
   (lofat-fs-p fat32$c)
   (lofat-fs-p
    (mv-nth 0
            (process-reg-file fat32$c path
                              file-text file-table fd-table state))))
  :hints
  (("goal" :in-theory (enable process-reg-file
                              lofat-close lofat-pwrite))))

(defthm
  lofat-fs-p-of-process-dir-file
  (implies
   (lofat-fs-p fat32$c)
   (lofat-fs-p (mv-nth 0 (process-dir-file fat32$c path state))))
  :hints
  (("goal" :in-theory (enable process-dir-file lofat-mkdir))))

(defund process-block-sequence (file-text state fat32$c fd-table
                                          file-table output-path)
  (declare (xargs :stobjs (state fat32$c)
                  :measure (length file-text)
                  :guard (and (state-p state) (stringp file-text)
                              (lofat-fs-p fat32$c)
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
        (mv state fat32$c fd-table file-table))
       (first-block (subseq file-text 0 512))
       ((when (equal first-block *tar-blank-block*))
        (process-block-sequence
         (subseq file-text 512 nil) state fat32$c fd-table file-table
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
       ((mv fat32$c fd-table file-table state)
        (cond ((not (fat32-filename-list-p path))
               (let
                   ((state (princ$ "path is problematic" *standard-co* state)))
                 (mv fat32$c fd-table file-table state)))
              ((equal first-block-typeflag *TAR-REGTYPE*)
               (let
                   ((state (princ$
                            "typeflag indicates a regular file"
                            *standard-co* state)))
                 (process-reg-file fat32$c path first-block-text
                                   file-table fd-table state)))
              ((equal first-block-typeflag *tar-dirtype*)
               (mv-let
                   (fat32$c state)
                   (process-dir-file fat32$c path state)
                   (mv fat32$c fd-table file-table state)))
              (t
               (let
                   ((state (princ$
                            "path is fine, but typeflag is problematic"
                            *standard-co* state)))
                 (mv fat32$c fd-table file-table state))))))
    (process-block-sequence
     (subseq file-text (min (+ 512
                               (* 512 (ceiling first-block-length 512)))
                            (length file-text))
             nil)
     state fat32$c fd-table file-table output-path)))

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
                  (equal name nil)))
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
  get-names-from-dirp-alt-lemma-2
  (implies (consp (dir-stream->file-list x))
           (car (dir-stream->file-list x)))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (fat32-filename-list-p)
                    (fat32-filename-list-p-of-dir-stream->file-list))
    :use fat32-filename-list-p-of-dir-stream->file-list))
  :rule-classes :type-prescription)

(defthmd
  get-names-from-dirp-alt
  (equal
   (get-names-from-dirp dirp dir-stream-table)
   (cond
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
  (declare (xargs :guard (and (m1-file-alist-p fs) (hifat-no-dups-p fs)
                              (fat32-filename-list-p path) (natp entry-count)
                              (fat32-filename-list-p name-list) (file-table-p file-table)
                              (fd-table-p fd-table) (dir-stream-table-p dir-stream-table))
                  :guard-hints (("goal" :in-theory (e/d (hifat-tar-name-list-string)
                                                        (append append-of-cons))
                                 :do-not-induct t))
                  :measure (nfix entry-count) :verify-guards nil))
  (b* ((fd-table (mbe :exec fd-table :logic (fd-table-fix fd-table)))
       (file-table (mbe :exec file-table :logic (file-table-fix file-table)))
       (dir-stream-table (mbe :exec dir-stream-table
                              :logic (dir-stream-table-fix dir-stream-table)))
       ((unless (and (consp name-list) (not (zp entry-count)))) (mv "" fd-table file-table))
       (head (car name-list)) (head-path (append path (list head)))
       ((mv st retval &) (hifat-lstat fs head-path))
       ((mv tail-string fd-table file-table)
        (hifat-tar-name-list-string fs path (cdr name-list) fd-table file-table
                                    dir-stream-table (- entry-count 1)))
       ((unless (>= retval 0)) (mv tail-string fd-table file-table))
       (len (struct-stat->st_size st))
       ((mv fd-table file-table fd &) (hifat-open head-path fd-table file-table))
       ((mv & & pread-error-code) (hifat-pread fd len 0 fs fd-table file-table))
       ((mv fd-table file-table &) (hifat-close fd fd-table file-table))
       ((unless (and (<= (len (fat32-path-to-path head-path)) 100)))
        (mv tail-string fd-table file-table)))
    (if (zp pread-error-code)
        ;; regular file.
        (b* ((head-string (hifat-tar-reg-file-string fs(implode (fat32-path-to-path head-path)))))
          (mv (concatenate 'string head-string tail-string) fd-table file-table))
      ;; directory file.
      (b*
          (((mv dirp dir-stream-table &) (hifat-opendir fs head-path dir-stream-table))
           ((mv names dir-stream-table) (get-names-from-dirp dirp dir-stream-table))
           ((mv & dir-stream-table) (hifat-closedir dirp dir-stream-table))
           ((mv head-string fd-table file-table)
            (hifat-tar-name-list-string fs head-path names fd-table file-table
                                        dir-stream-table (- entry-count 1))))
        (mv (concatenate 'string (tar-header-block (implode (fat32-path-to-path head-path))
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
  (("goal" :in-theory (disable find-new-index-correctness-1)
    :use (:instance find-new-index-correctness-1
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
                         (:rewrite take-of-len-free)
                         (:rewrite str::consp-of-explode)
                         (:linear position-when-member)
                         (:rewrite default-car)
                         (:rewrite append-atom-under-list-equiv)
                         (:linear len-when-hifat-bounded-file-alist-p
                                  . 2)
                         (:linear len-when-hifat-bounded-file-alist-p
                                  . 1)
                         (:rewrite hifat-subsetp-preserves-assoc)
                         (:rewrite consp-of-assoc-when-hifat-equiv-lemma-1)
                         (:rewrite member-when-atom)
                         (:rewrite consp-of-append)
                         (:linear lower-bound-of-len-when-sublistp)
                         (:linear len-when-prefixp)
                         (:rewrite put-assoc-equal-without-change . 2)
                         (:type-prescription natp-position-ac)
                         (:definition length)
                         (:definition atom)
                         (:definition min)))
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

(defthm
  stringp-of-hifat-tar-name-list-string-reduction
  (stringp
   (hifat-tar-name-list-string-reduction fs path name-list entry-count))
  :hints (("goal" :do-not-induct t
           :use hifat-tar-name-list-string-reduction-correctness-1))
  :rule-classes :type-prescription)

(defund alist-shift (alist shift)
  (if (atom alist)
      nil
    (cons (cons (caar alist) (+ shift (cdar alist)))
          (alist-shift (cdr alist) shift))))

(defthm consp-of-assoc-of-alist-shift
  (implies (alistp alist)
           (equal (consp (assoc-equal x (alist-shift alist shift)))
                  (consp (assoc-equal x alist))))
  :hints (("goal" :in-theory (enable alist-shift))))

(defthm alistp-of-alist-shift
  (alistp (alist-shift alist shift))
  :hints (("goal" :in-theory (enable alist-shift))))

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

(defund hifat-tar-name-list-alist (fs path name-list entry-count)
  (declare (xargs :measure (nfix entry-count)))
  (b* (((unless (and (consp name-list) (not (zp entry-count)))) nil)
       (head (car name-list))
       (head-path (append path (list head)))
       ((mv st retval &) (hifat-lstat fs head-path))
       (tail-alist
        (hifat-tar-name-list-alist fs path (cdr name-list) (- entry-count 1)))
       ((unless (>= retval 0)) tail-alist)
       (len (struct-stat->st_size st))
       ((mv fd-table file-table fd &)
        (hifat-open head-path nil nil))
       ((unless (>= fd 0)) nil)
       ((mv & & pread-error-code)
        (hifat-pread fd len 0 fs fd-table file-table))
       ((mv & & &)
        (hifat-close fd fd-table file-table))
       ((unless (and (<= (len (fat32-path-to-path head-path)) 100))) tail-alist)
       (head-string (hifat-tar-reg-file-string
                     fs
                     (implode (fat32-path-to-path head-path))))
       ((when (zp pread-error-code))
        (cons (cons head-path 0)
              (alist-shift tail-alist (length head-string))))
       ((mv dirp dir-stream-table &)
        (hifat-opendir fs head-path nil))
       ((mv names dir-stream-table)
        (get-names-from-dirp dirp dir-stream-table))
       ((mv & &)
        (hifat-closedir dirp dir-stream-table))
       (head-alist
        (hifat-tar-name-list-alist fs (append path (list head)) names (- entry-count 1))))
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

(defthm alistp-of-hifat-tar-name-list-alist
  (alistp (hifat-tar-name-list-alist fs path name-list entry-count))
  :hints (("goal" :in-theory (enable hifat-tar-name-list-alist))))

(defthm no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-2
  (implies (and (integerp start)
                (equal start end)
                (stringp seq))
           (equal (subseq seq start end) ""))
  :hints (("goal" :in-theory (enable subseq subseq-list))))

(defthm
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-3
  (not
   (member-equal
    nil
    (strip-cars (hifat-tar-name-list-alist fs path name-list entry-count))))
  :hints
  (("goal" :in-theory (e/d (hifat-tar-name-list-alist)
                           (append append-of-cons
                                   (:rewrite prefixp-of-append-arg1)))))
  :rule-classes :type-prescription)

(defthm
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-4
  (implies (and (consp path)
                (not (zp (mv-nth 1 (hifat-find-file fs path)))))
           (equal (hifat-tar-name-list-alist fs path name-list entry-count)
                  nil))
  :hints (("goal" :in-theory (enable hifat-tar-name-list-alist alist-shift
                                     hifat-pread hifat-lstat hifat-open))))

(defthm
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-5
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
  ()

  ;; These were the (less general) lemmas in books/std/lists/prefixp.lisp.
  (local
   (defthm when-prefixp-append-same
     (iff (prefixp (append x y) x) (atom y))
     :hints (("goal" :in-theory (enable prefixp)))))
  (local
   (defthm prefixp-of-append-when-same-length
     (implies (<= (len x) (len y))
              (implies (equal (len x) (len y))
                       (equal (prefixp x (append y z))
                              (prefixp x y))))
     :hints(("Goal"
             :induct (prefixp x y)
             :in-theory (enable prefixp list-equiv)))))

  (defthm
    no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-1
    (implies
     (case-split (or (not (prefixp path1 path2))
                     (equal path1 path2)))
     (and
      (not
       (consp (assoc-equal
               path2
               (hifat-tar-name-list-alist fs path1 name-list entry-count))))
      (atom (assoc-equal
             path2
             (hifat-tar-name-list-alist fs path1 name-list entry-count)))))
    :hints (("goal" :in-theory (e/d (hifat-tar-name-list-alist)
                                    ((:rewrite prefixp-of-append-arg1))))))

  (defthmd
    no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-6
    (implies
     (and
      (member-equal
       path2
       (strip-cars (hifat-tar-name-list-alist fs path1 name-list entry-count)))
      (not (member-equal name name-list)))
     (not (prefixp (append path1 (list name))
                   path2)))
    :hints
    (("goal" :in-theory
      (e/d (hifat-tar-name-list-alist hifat-pread hifat-open hifat-lstat)
           (atom append append-of-cons
                 (:rewrite prefixp-of-append-arg1)))
      :expand (list-equiv (cons name 'nil) (cons (car name-list) 'nil))))
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
         (assoc-equal
          path2
          (hifat-tar-name-list-alist fs path1 name-list entry-count))))))
     (:rewrite
      :corollary
      (implies
       (and (not (null path2))
            (prefixp (append path1 (list name))
                     path2)
            (not (member-equal name name-list)))
       (atom (assoc-equal
              path2
              (hifat-tar-name-list-alist fs path1 name-list entry-count))))
      :hints (("goal" :in-theory (enable atom))))))

  (local (include-book "std/basic/inductions" :dir :system))
  (local (include-book "std/lists/intersectp" :dir :system))

  (defthm
    no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-7
    (implies
     (and
      (not (zp n))
      (not (member-equal name
                         name-list1)))
     (not
      (prefixp
       (append path1 (list name))
       (nth (+ -1 n)
            (strip-cars (hifat-tar-name-list-alist fs path1 name-list1
                                                   (+ -1 entry-count)))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable (:rewrite prefixp-of-append-arg1)
                          (:rewrite nth-under-iff-1))
      :use
      (:instance
       no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-6
       (path2
        (nth (+ -1 n)
             (strip-cars (hifat-tar-name-list-alist fs path1 name-list1
                                                    (+ -1 entry-count)))))
       (name name)
       (path1 path1)
       (name-list name-list1)
       (fs fs)
       (entry-count (- entry-count 1))))))

  (local
   (defthmd
     lemma-1
     (implies
      (not (member-equal name
                         name-list1))
      (not
       (intersectp-equal
        (take n
              (strip-cars (hifat-tar-name-list-alist fs path1 name-list1
                                                     (+ -1 entry-count))))
        (strip-cars
         (hifat-tar-name-list-alist
          fs (append path1 (list name))
          name-list2
          (+ -1 entry-count))))))
     :hints
     (("goal"
       :induct (dec-induct n)
       :in-theory (e/d (take-as-append-and-nth) (take))))))

  (defthm
    no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-8
    (implies
     (not (member-equal name
                        name-list1))
     (not
      (intersectp-equal
       (strip-cars (hifat-tar-name-list-alist fs path1 name-list1
                                              (+ -1 entry-count)))
       (strip-cars
        (hifat-tar-name-list-alist
         fs (append path1 (list name))
         name-list2
         (+ -1 entry-count))))))
    :hints
    (("goal" :do-not-induct t
      :use (:instance lemma-1
                      (n
                       (len
                        (strip-cars (hifat-tar-name-list-alist fs path1 name-list1
                                                               (+ -1
                                                                  entry-count)))))))))

  (defthm
    no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-9
    (implies
     (and
      (not (consp path1))
      (not (member-equal name
                         name-list1))
      (equal
       name
       (car (nth (+ -1 n)
                 (strip-cars (hifat-tar-name-list-alist fs path1 name-list1
                                                        (+ -1 entry-count)))))))
     (not
      (consp
       (nth (+ -1 n)
            (strip-cars (hifat-tar-name-list-alist fs path1 name-list1
                                                   (+ -1 entry-count)))))))
    :hints
    (("goal"
      :use
      (:instance
       no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-6
       (path2
        (nth (+ -1 n)
             (strip-cars (hifat-tar-name-list-alist fs path1 name-list1
                                                    (+ -1 entry-count)))))
       (name-list name-list1)
       (entry-count (- entry-count 1))
       (name name)))))

  (local
   (defthmd
     lemma-2
     (implies
      (and (not (consp path1))
           (not (member-equal name
                              name-list1)))
      (not
       (intersectp-equal
        (take n
              (strip-cars (hifat-tar-name-list-alist fs path1 name-list1
                                                     (+ -1 entry-count))))
        (strip-cars
         (hifat-tar-name-list-alist
          fs (list name)
          name-list2
          (+ -1 entry-count))))))
     :hints
     (("goal"
       :induct (dec-induct n)
       :expand
       (:with
        take-as-append-and-nth
        (take n
              (strip-cars (hifat-tar-name-list-alist fs path1 name-list1
                                                     (+ -1 entry-count)))))))))

  (defthm
    no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-10
    (implies
     (and (not (consp path1))
          (not (member-equal name
                             name-list1)))
     (not
      (intersectp-equal
       (strip-cars (hifat-tar-name-list-alist fs path1 name-list1
                                              (+ -1 entry-count)))
       (strip-cars
        (hifat-tar-name-list-alist
         fs (list name)
         name-list2
         (+ -1 entry-count))))))
    :hints
    (("goal"
      :do-not-induct t
      :use (:instance lemma-2 (n
                               (len (hifat-tar-name-list-alist fs path1 name-list1
                                                               (+ -1 entry-count)))))))))

(defthm
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-11
  (implies
   (m1-directory-file-p
    (mv-nth
     0
     (hifat-find-file fs
                      (file-table-element->fid
                       (cdr (assoc-equal (cdr (assoc-equal fd (fd-table-fix fd-table)))
                                         (file-table-fix file-table)))))))
   (> (mv-nth 2
              (hifat-pread fd count offset fs fd-table file-table))
      0))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-pread)))
  :rule-classes :linear)

(defthm
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-12
  (implies
   (and
    (consp (assoc-equal fd (fd-table-fix fd-table)))
    (consp (assoc-equal (cdr (assoc-equal fd (fd-table-fix fd-table)))
                        (file-table-fix file-table)))
    (not
     (m1-directory-file-p
      (mv-nth
       0
       (hifat-find-file
        fs
        (file-table-element->fid
         (cdr (assoc-equal (cdr (assoc-equal fd (fd-table-fix fd-table)))
                           (file-table-fix file-table))))))))
    (equal
     (mv-nth
      1
      (hifat-find-file
       fs
       (file-table-element->fid
        (cdr (assoc-equal (cdr (assoc-equal fd (fd-table-fix fd-table)))
                          (file-table-fix file-table))))))
     0))
   (equal (mv-nth 2
                  (hifat-pread fd count offset fs fd-table file-table))
          0))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-pread))))

(defthm
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-13
  (implies (and (not (zp (mv-nth 1 (hifat-find-file fs path))))
                (consp path))
           (equal (hifat-tar-name-list-alist fs path name-list entry-count)
                  nil))
  :hints (("goal" :in-theory (e/d (alist-shift hifat-pread
                                               hifat-tar-name-list-alist)
                                  ()))))

(defthm
  not-consp-assoc-nil-hifat-tar-name-list-alist
  (not
   (consp
    (assoc-equal nil
                 (hifat-tar-name-list-alist fs path name-list entry-count))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable hifat-tar-name-list-alist))))

(defthm
  natp-of-cdr-of-assoc-of-hifat-tar-name-list-alist
  (implies
   (consp
    (assoc-equal path2
                 (hifat-tar-name-list-alist fs path1 name-list entry-count)))
   (natp
    (cdr (assoc-equal
          path2
          (hifat-tar-name-list-alist fs path1 name-list entry-count)))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable hifat-tar-name-list-alist))))

(defthm
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-15
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

(defthm
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-16
  (not
   (consp
    (assoc-equal nil
                 (hifat-tar-name-list-alist fs path name-list entry-count))))
  :hints (("goal" :in-theory (enable hifat-tar-name-list-alist alist-shift)))
  :rule-classes :type-prescription)

(defthm
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-17
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
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-18
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
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-21
  (implies (not (m1-directory-file-p (mv-nth 0 (hifat-find-file fs path))))
           (equal (hifat-tar-name-list-alist fs path name-list entry-count)
                  nil))
  :hints (("goal" :in-theory (enable hifat-tar-name-list-alist alist-shift
                                     hifat-lstat hifat-find-file))))

(defthm no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-22
  (implies (zp (hifat-entry-count fs))
           (not (consp (assoc-equal name (hifat-file-alist-fix fs)))))
  :hints (("goal" :in-theory (enable hifat-entry-count
                                     hifat-file-alist-fix)))
  :rule-classes :type-prescription)

(defthm
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-24
  (implies (equal (hifat-entry-count fs) 0)
           (iff (subsetp-equal x (strip-cars fs))
                (not (consp x))))
  :hints (("goal" :in-theory (enable hifat-entry-count subsetp-equal))))

(defthm
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-23
  (implies (and (not (atom path1))
                (< 0 (mv-nth 1 (hifat-find-file fs path1)))
                (fat32-filename-list-prefixp path1 path2))
           (not (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2)))))
  :hints (("goal" :in-theory (enable hifat-find-file))))

(defthm no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-25
  (implies (not (consp path1))
           (equal (hifat-find-file fs path1)
                  (mv (make-m1-file) *enoent*)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-find-file))))

(defthm
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-30
  (implies
   (not (member-equal (nth (len path1) path2)
                      name-list))
   (not
    (consp (assoc-equal
            path2
            (hifat-tar-name-list-alist fs path1 name-list entry-count)))))
  :hints
  (("goal"
    :induct
    (hifat-tar-name-list-string fs path1 name-list fd-table
                                file-table dir-stream-table entry-count)
    :expand
    ((hifat-tar-name-list-alist fs path1 name-list entry-count)
     (hifat-tar-name-list-string fs path1 name-list fd-table
                                 file-table dir-stream-table entry-count)
     (hifat-tar-name-list-alist fs path1 nil entry-count))
    :in-theory
    (e/d
     ((:induction hifat-tar-name-list-string)
      (:induction hifat-tar-name-list-alist)
      hifat-open hifat-lstat
      hifat-opendir get-names-from-dirp-alt
      painful-debugging-lemma-21
      length-of-empty-list
      hifat-entry-count member-equal)
     (member-of-strip-cars append-of-cons binary-append
                           string-append take-of-too-many
                           (:rewrite nthcdr-when->=-n-len-l)
                           (:rewrite take-of-len-free)
                           (:linear position-equal-ac-when-member)
                           (:definition position-equal-ac)
                           (:rewrite consp-of-nthcdr)
                           (:rewrite dir-stream-table-p-when-subsetp-equal)
                           (:rewrite hifat-to-lofat-inversion-lemma-2)
                           (:rewrite <<-sort-consp)
                           (:definition strip-cars)
                           (:rewrite m1-directory-file-p-when-m1-file-p)
                           (:rewrite true-listp-when-string-list)
                           (:rewrite hifat-find-file-correctness-3)
                           (:definition string-listp)
                           (:rewrite string-listp-when-fat32-filename-list-p)
                           (:linear len-when-hifat-bounded-file-alist-p . 2)
                           (:linear len-when-hifat-bounded-file-alist-p . 1)
                           (:rewrite m1-regular-file-p-correctness-1)
                           (:definition nthcdr)
                           (:definition atom)
                           (:definition min)
                           (:definition nfix)
                           (:definition natp))))))

(defthm
  no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist
  (implies
   (no-duplicatesp-equal name-list)
   (no-duplicatesp-equal
    (strip-cars (hifat-tar-name-list-alist fs path1 name-list entry-count))))
  :hints
  (("goal"
    :in-theory (e/d (;; Enabling the definition lemma just leads to sadness with
                     ;; regards to hifat-tar-name-list-string-reduction. The small
                     ;; number of subgoals which need the definition should be
                     ;; handled with expand hints.
                     (:induction hifat-tar-name-list-string)
                     hifat-tar-name-list-alist
                     hifat-open hifat-lstat
                     ;; I don't know if I can justify enabling every system call,
                     ;; but this one has to be enabled on account of really stupid
                     ;; subgoals.
                     hifat-opendir painful-debugging-lemma-21)
                    (take-when-prefixp
                     prefixp-of-cons-right
                     take-of-cons
                     append-of-cons
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
                     (:definition natp))))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-22
  (implies (and (equal (nth 0 path2) (car name-list))
                (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2))))
           (equal (mv-nth 1
                          (hifat-find-file fs (list (car name-list))))
                  0))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-find-file nth))))

;; This should have been proved a while ago...
(defthm hifat-tar-name-list-alist-correctness-lemma-23
  (implies (and (m1-file-alist-p alist)
                (not (fat32-filename-p x)))
           (not (consp (assoc-equal x alist))))
  :hints (("goal" :in-theory (enable m1-file-alist-p))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-25
  (implies (consp (assoc-equal name (m1-file->contents x)))
           (and (m1-file-alist-p (m1-file->contents x))
                (fat32-filename-p name)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (m1-file-contents-p)
                    ((:rewrite m1-file-contents-p-of-m1-file->contents)))
    :use (:rewrite m1-file-contents-p-of-m1-file->contents)))
  :rule-classes :forward-chaining)

(defthm hifat-tar-name-list-alist-correctness-lemma-24
  (implies
   (and (not (equal (mv-nth 1
                            (hifat-find-file fs (list (car name-list))))
                    0))
        (m1-file-alist-p fs)
        (subsetp-equal name-list (strip-cars fs))
        (member-equal (nth 0 path2)
                      (cdr name-list)))
   nil)
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-find-file)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (m1-file-alist-p fs)
      (subsetp-equal name-list (strip-cars fs))
      (member-equal (nth 0 path2)
                    (cdr name-list)))
     (equal (mv-nth 1
                    (hifat-find-file fs (list (car name-list))))
            0)))))

(defthm hifat-tar-name-list-alist-correctness-lemma-29
  (implies
   (and (not (equal (mv-nth 1
                            (hifat-find-file fs (list (car name-list))))
                    0))
        (m1-file-alist-p fs)
        (subsetp-equal name-list (strip-cars fs))
        (member-equal (nth 0 path2) name-list))
   nil)
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-find-file)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (m1-file-alist-p fs)
      (subsetp-equal name-list (strip-cars fs))
      (member-equal (nth 0 path2) name-list))
     (equal (mv-nth 1
                    (hifat-find-file fs (list (car name-list))))
            0)))))

(defthm hifat-tar-name-list-alist-correctness-lemma-26
  (implies (prefixp x y)
           (<= (len (fat32-path-to-path x))
               (len (fat32-path-to-path y))))
  :hints (("goal" :in-theory (enable fat32-path-to-path)
           :induct (fat32-filename-list-prefixp x y)))
  :rule-classes :linear)

(defthm
  hifat-tar-name-list-alist-correctness-lemma-33
  (implies (and (consp path1)
                (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2)))
                (prefixp path1 path2))
           (equal (mv-nth 1 (hifat-find-file fs path1))
                  0))
  :hints (("goal" :in-theory (enable hifat-find-file)
           :induct (mv (fat32-filename-list-prefixp path1 path2)
                       (mv-nth 0 (hifat-find-file fs path1))))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-34
  (implies
   (and
    (consp name-list)
    (m1-directory-file-p (mv-nth 0 (hifat-find-file fs path1)))
    (subsetp-equal
     name-list
     (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs path1))))))
   (equal
    (mv-nth 1
            (hifat-find-file
             (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
             (list (car name-list))))
    0))
  :hints (("goal" :in-theory (enable hifat-find-file))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-35
  (implies
   (and
    (fat32-filename-p (nth (len path1) path2))
    (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2)))
    (prefixp path1 path2))
   (m1-directory-file-p (mv-nth 0 (hifat-find-file fs path1))))
  :hints (("goal" :in-theory (enable hifat-find-file prefixp nth)
           :induct (mv (fat32-filename-list-prefixp path1 path2)
                       (mv-nth 0 (hifat-find-file fs path1)))
           :do-not-induct t)))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-38
  (implies
   (and
    (fat32-filename-list-p name-list)
    (member-equal (nth (len path1) path2)
                  (cdr name-list))
    (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2)))
    (prefixp path1 path2))
   (m1-directory-file-p (mv-nth 0 (hifat-find-file fs path1))))
  :hints
  (("goal" :in-theory (disable hifat-tar-name-list-alist-correctness-lemma-35)
    :use hifat-tar-name-list-alist-correctness-lemma-35
    :do-not-induct t)))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-39
  (implies (and (equal (nth 0 path2) name)
                (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2)))
                (<= (len (fat32-path-to-path path2))
                    100))
           (<= (len (fat32-path-to-path (list name)))
               100))
  :instructions
  (:promote (:dive 1 2)
            (:apply-linear hifat-tar-name-list-alist-correctness-lemma-26
                           ((y path2)))
            :top
            :bash (:bash ("goal" :in-theory (enable nth))))
  :rule-classes :linear)

(defthm
  hifat-tar-name-list-alist-correctness-1
  (implies
   (and
    (fat32-filename-list-p name-list)
    (consp
     (assoc-equal path2
                  (hifat-tar-name-list-alist fs path1 name-list entry-count))))
   (and
    (equal
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
     (hifat-tar-reg-file-string fs
                                (implode (fat32-path-to-path path2))))
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
                                 dir-stream-table entry-count))
    :in-theory
    (e/d (;; Enabling the definition rules for these two, below, just
          ;; leads to sadness with regards to
          ;; hifat-tar-name-list-string-reduction. The small number of
          ;; subgoals which need the definition should be handled with
          ;; expand hints and specific rules.
          (:induction hifat-tar-name-list-string)
          (:induction hifat-tar-name-list-alist)
          ;; There are too many lemmas which need these syscall
          ;; definitions to be opened up.
          hifat-open hifat-lstat hifat-opendir
          get-names-from-dirp-alt
          painful-debugging-lemma-21
          length-of-empty-list)
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
          ;; It's dubious how much labour is saved by disabling these,
          ;; but it's worth a shot.
          (:definition atom)
          (:definition min)
          (:definition nfix)
          (:definition natp)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (fat32-filename-list-p name-list)
      (consp
       (assoc-equal path2
                    (hifat-tar-name-list-alist fs path1 name-list entry-count))))
     (equal
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
      (hifat-tar-reg-file-string fs
                                 (implode (fat32-path-to-path path2))))))
   (:linear
    :corollary
    (implies
     (and
      (fat32-filename-list-p name-list)
      (consp
       (assoc-equal path2
                    (hifat-tar-name-list-alist fs path1 name-list entry-count))))
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
                                   (implode (fat32-path-to-path path2))))))))))

;; Inductive, so left enabled.
(defthm
  hifat-tar-name-list-alist-correctness-lemma-40
  (implies
   (and
    (fat32-filename-list-p name-list)
    (consp
     (assoc-equal path2
                  (hifat-tar-name-list-alist fs path1 name-list entry-count))))
   (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2))))
  :hints
  (("goal"
    :induct
    (hifat-tar-name-list-string fs path1 name-list fd-table
                                file-table dir-stream-table entry-count)
    :expand
    ((:free (path1)
            (hifat-tar-name-list-alist fs path1 name-list entry-count))
     (hifat-tar-name-list-string fs path1 name-list fd-table file-table
                                 dir-stream-table entry-count))
    :in-theory
    (e/d
     ((:induction hifat-tar-name-list-string)
      (:induction hifat-tar-name-list-alist)
      hifat-open hifat-lstat
      hifat-opendir get-names-from-dirp-alt
      painful-debugging-lemma-21
      length-of-empty-list
      hifat-entry-count member-equal)
     (member-of-strip-cars append-of-cons binary-append
                           string-append take-of-too-many
                           (:rewrite nthcdr-when->=-n-len-l)
                           (:rewrite take-of-len-free)
                           (:linear position-equal-ac-when-member)
                           (:definition position-equal-ac)
                           (:rewrite consp-of-nthcdr)
                           (:rewrite dir-stream-table-p-when-subsetp-equal)
                           (:rewrite hifat-to-lofat-inversion-lemma-2)
                           (:rewrite <<-sort-consp)
                           (:definition strip-cars)
                           (:rewrite m1-directory-file-p-when-m1-file-p)
                           (:rewrite true-listp-when-string-list)
                           (:rewrite hifat-find-file-correctness-3)
                           (:definition string-listp)
                           (:rewrite string-listp-when-fat32-filename-list-p)
                           (:linear len-when-hifat-bounded-file-alist-p . 2)
                           (:linear len-when-hifat-bounded-file-alist-p . 1)
                           (:rewrite m1-regular-file-p-correctness-1)
                           (:definition nthcdr)
                           (:definition atom)
                           (:definition min)
                           (:definition nfix)
                           (:definition natp)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (fat32-filename-list-p name-list)
      (consp
       (assoc-equal path2
                    (hifat-tar-name-list-alist fs path1 name-list entry-count))))
     (not (m1-directory-file-p (mv-nth 0 (hifat-find-file fs path2))))))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-1
  (implies
   (and
    (consp name-list)
    (m1-directory-file-p (mv-nth 0 (hifat-find-file fs path1)))
    (< 100
       (len (fat32-path-to-path (append path1 (list (car name-list))))))
    (subsetp-equal
     name-list
     (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
    (equal (nth (len path1) path2)
           (car name-list))
    (prefixp path1 path2))
   (< 100 (len (fat32-path-to-path path2))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable (:linear hifat-tar-name-list-alist-correctness-lemma-26))
    :use (:instance (:linear hifat-tar-name-list-alist-correctness-lemma-26)
                    (y path2)
                    (x (append path1 (list (car name-list)))))))
  :rule-classes :linear)

(defthm
  hifat-tar-name-list-alist-correctness-lemma-2
  (implies
   (and
    (consp
     (assoc-equal (car name-list)
                  (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
    (equal (nth (len path1) path2)
           (car name-list))
    (prefixp path1 path2)
    (<= (len (fat32-path-to-path path2))
        100))
   (<= (len (fat32-path-to-path (append path1 (list (car name-list)))))
       100))
  :instructions
  (:promote (:dive 1 2)
            (:apply-linear hifat-tar-name-list-alist-correctness-lemma-26
                           ((y path2)))
            :top
            :bash :bash)
  :rule-classes :linear)

(defthm
  hifat-no-dups-p-of-remove-assocs-equal
  (implies (and (hifat-no-dups-p alist)
                (m1-file-alist-p alist))
           (hifat-no-dups-p (remove-assocs-equal keys alist)))
  :hints (("goal" :in-theory (enable remove-assocs-equal hifat-no-dups-p))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-3
  (implies (m1-file-alist-p alist)
           (<= (hifat-entry-count (remove-assocs-equal keys alist))
               (hifat-entry-count (remove-assocs-equal (remove-equal x keys)
                                                       alist))))
  :hints (("goal" :in-theory (enable remove-assocs-equal hifat-entry-count)))
  :rule-classes :linear)

(defthm
  hifat-tar-name-list-alist-correctness-lemma-4
  (implies (and (member-equal x keys)
                (consp (assoc-equal x alist))
                (m1-file-alist-p alist))
           (< (hifat-entry-count (remove-assocs-equal keys alist))
              (hifat-entry-count (remove-assocs-equal (remove-equal x keys)
                                                      alist))))
  :hints (("goal" :in-theory (enable remove-assocs-equal hifat-entry-count)))
  :rule-classes :linear)

(defthm
  hifat-tar-name-list-alist-correctness-lemma-5
  (implies
   (and (member-equal x (set-difference-equal keys y))
        (consp (assoc-equal x alist))
        (m1-file-alist-p alist))
   (< (hifat-entry-count (remove-assocs-equal (set-difference-equal keys y)
                                              alist))
      (hifat-entry-count
       (remove-assocs-equal (set-difference-equal (remove-equal x keys)
                                                  y)
                            alist))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable hifat-tar-name-list-alist-correctness-lemma-4)
    :use (:instance hifat-tar-name-list-alist-correctness-lemma-4
                    (keys (set-difference-equal keys y)))))
  :rule-classes :linear)

(defthm
  hifat-tar-name-list-alist-correctness-lemma-6
  (implies
   (m1-directory-file-p file)
   (true-listp
    (m1-file->contents file)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable true-listp-when-m1-file-alist-p)
    :use
    (:instance
     true-listp-when-m1-file-alist-p
     (x (m1-file->contents$inline
         file))))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-7
  (implies
   (and (m1-file-alist-p fs)
        (hifat-no-dups-p fs)
        (consp (assoc-equal name fs))
        (m1-directory-file-p (cdr (assoc-equal name fs))))
   (< (hifat-entry-count (m1-file->contents (cdr (assoc-equal name fs))))
      (hifat-entry-count fs)))
  :hints (("goal" :in-theory (enable hifat-find-file hifat-entry-count)))
  :rule-classes :linear)

(defthm
  hifat-tar-name-list-alist-correctness-lemma-11
  (implies
   (and
    (not (nth 1 path2))
    (m1-directory-file-p (mv-nth 0
                                 (hifat-find-file fs (list (car name-list)))))
    (fat32-filename-list-p path2)
    (equal (nth 0 path2) (car name-list))
    (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2))))
   (not
    (atom
     (assoc-equal
      path2
      (hifat-tar-name-list-alist
       fs (list (car name-list))
       (<<-sort
        (strip-cars
         (m1-file->contents
          (mv-nth 0
                  (hifat-find-file fs (list (car name-list)))))))
       (+ -1 entry-count))))))
  :hints
  (("goal"
    :do-not-induct t
    :expand
    ((:free (path1)
            (hifat-tar-name-list-alist fs path1 name-list entry-count))
     (hifat-tar-name-list-string fs path1 name-list fd-table
                                 file-table dir-stream-table entry-count)
     (:with (:definition set-difference$-redefinition)
            (:free (l1)
                   (set-difference-equal l1 name-list)))
     (nth 1 path2))
    :in-theory
    (e/d
     ((:induction hifat-tar-name-list-string)
      (:induction hifat-tar-name-list-alist)
      hifat-open hifat-lstat
      hifat-opendir get-names-from-dirp-alt
      painful-debugging-lemma-21
      length-of-empty-list
      hifat-entry-count member-equal
      subsetp-equal remove-assocs-equal nth)
     (append-of-cons binary-append
                     string-append take-of-too-many
                     (:rewrite nthcdr-when->=-n-len-l)
                     (:rewrite take-of-len-free)
                     (:linear position-equal-ac-when-member)
                     (:definition position-equal-ac)
                     (:rewrite dir-stream-table-p-when-subsetp-equal)
                     (:rewrite hifat-to-lofat-inversion-lemma-2)
                     (:rewrite <<-sort-consp)
                     (:definition strip-cars)
                     (:rewrite m1-directory-file-p-when-m1-file-p)
                     (:rewrite true-listp-when-string-list)
                     (:rewrite hifat-find-file-correctness-3)
                     (:definition string-listp)
                     (:rewrite string-listp-when-fat32-filename-list-p)
                     (:linear len-when-hifat-bounded-file-alist-p . 2)
                     (:linear len-when-hifat-bounded-file-alist-p . 1)
                     (:rewrite m1-regular-file-p-correctness-1)
                     (:definition nthcdr)
                     (:linear hifat-tar-name-list-alist-correctness-lemma-1)
                     (:linear hifat-entry-count-when-hifat-subsetp)
                     (:definition hifat-subsetp)
                     (:definition atom)
                     (:definition min)
                     (:definition nfix)
                     (:definition natp)
                     nth-under-iff-1)))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-13
  (implies
   (and
    (not
     (consp (assoc-equal
             (nth 1 path2)
             (m1-file->contents
              (mv-nth 0
                      (hifat-find-file fs (list (car name-list))))))))
    (fat32-filename-list-p path2)
    (equal (nth 0 path2) (car name-list))
    (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2))))
   (equal
    (mv-nth
     2
     (hifat-pread
      0 2097152 0 fs '((0 . 0))
      (list (cons 0
                  (file-table-element 0 (list (car name-list)))))))
    0))
  :hints (("goal" :do-not-induct t
           :in-theory (enable nth hifat-find-file))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-14
  (implies
   (and
    (not (zp entry-count))
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (fat32-filename-list-p path2)
    (equal (nth 0 path2) (car name-list))
    (<= (hifat-entry-count
         (remove-assocs-equal
          (set-difference-equal (remove-equal (car name-list)
                                              (strip-cars fs))
                                (cdr name-list))
          fs))
        entry-count)
    (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2)))
    (<
     0
     (mv-nth
      2
      (hifat-pread
       0 2097152 0 fs '((0 . 0))
       (list (cons 0
                   (file-table-element 0 (list (car name-list))))))))
    (atom
     (assoc-equal
      path2
      (hifat-tar-name-list-alist
       fs (list (car name-list))
       (<<-sort
        (strip-cars
         (m1-file->contents
          (mv-nth 0
                  (hifat-find-file fs (list (car name-list)))))))
       (+ -1 entry-count)))))
   (>= (+ -1 entry-count)
       (hifat-entry-count
        (m1-file->contents
         (mv-nth 0
                 (hifat-find-file fs (list (car name-list))))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (hifat-find-file)
                    ((:linear hifat-tar-name-list-alist-correctness-lemma-7)))
    :use
    (:instance (:linear hifat-tar-name-list-alist-correctness-lemma-7)
               (fs (remove-assocs-equal
                    (set-difference-equal (remove-equal (car name-list)
                                                        (strip-cars fs))
                                          (cdr name-list))
                    fs))
               (name (fat32-filename-fix (car name-list))))))
  :rule-classes :linear)

;; Inductive, hence kept.
(defthm
  hifat-tar-name-list-alist-correctness-lemma-15
  (implies (and (hifat-no-dups-p fs)
                (m1-file-alist-p fs))
           (hifat-subsetp (remove-assocs-equal keys fs)
                          fs))
  :hints (("goal" :in-theory (enable remove-assocs-equal hifat-subsetp
                                     hifat-equiv-of-cons-lemma-4)))
  :rule-classes
  (:rewrite
   (:linear
    :corollary (implies (and (hifat-no-dups-p fs)
                             (m1-file-alist-p fs))
                        (<= (hifat-entry-count (remove-assocs-equal keys fs))
                            (hifat-entry-count fs))))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-16
  (implies
   (and
    (m1-directory-file-p
     (mv-nth 0
             (hifat-find-file
              (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
              (list (car name-list)))))
    (consp
     (assoc-equal (car name-list)
                  (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
    (<=
     (hifat-entry-count
      (remove-assocs-equal
       (set-difference-equal
        (remove-equal
         (car name-list)
         (strip-cars
          (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
        (cdr name-list))
       (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
     entry-count))
   (>=
    (+ -1 entry-count)
    (hifat-entry-count
     (m1-file->contents
      (mv-nth 0
              (hifat-find-file
               (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
               (list (car name-list))))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (hifat-find-file)
                    ((:linear hifat-tar-name-list-alist-correctness-lemma-7)))
    :use
    (:instance
     (:linear hifat-tar-name-list-alist-correctness-lemma-7)
     (fs
      (remove-assocs-equal
       (set-difference-equal
        (remove-equal
         (car name-list)
         (strip-cars
          (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
        (cdr name-list))
       (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
     (name (car name-list)))))
  :rule-classes :linear)

(defthm
  hifat-tar-name-list-alist-correctness-lemma-17
  (implies
   (and
    (equal (len path2) (+ 1 (len path1)))
    (m1-directory-file-p
     (mv-nth 0
             (hifat-find-file
              (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
              (list (car name-list)))))
    (<
     0
     (mv-nth
      2
      (hifat-pread
       (find-new-index (strip-cars (fd-table-fix fd-table)))
       2097152 0 fs
       (cons (cons (find-new-index (strip-cars (fd-table-fix fd-table)))
                   (find-new-index (strip-cars (file-table-fix file-table))))
             fd-table)
       (cons (cons (find-new-index (strip-cars (file-table-fix file-table)))
                   (file-table-element 0
                                       (append path1 (list (car name-list)))))
             file-table))))
    (fat32-filename-list-p path2)
    (consp
     (assoc-equal (car name-list)
                  (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
    (equal (nth (len path1) path2)
           (car name-list))
    (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2)))
    (prefixp path1 path2)
    (atom
     (assoc-equal
      path2
      (hifat-tar-name-list-alist
       fs (append path1 (list (car name-list)))
       (<<-sort
        (strip-cars
         (m1-file->contents
          (mv-nth
           0
           (hifat-find-file
            (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
            (list (car name-list)))))))
       (+ -1 entry-count)))))
   (not t))
 :instructions
 (:promote
  (:claim (equal (cdr (nthcdr (+ -1 (len path1)) path2))
                 (nthcdr (len path1) path2))
          :hints :none)
  (:bash
   ("goal" :do-not-induct t
    :expand (nthcdr (len path1) path2)
    :in-theory (e/d (hifat-find-file hifat-pread nthcdr)
                    (append-when-prefixp (:rewrite nthcdr-of-nthcdr)))
    :use ((:instance append-when-prefixp
                     (x (append path1 (list (car name-list))))
                     (y path2)))))
  :bash (:dive 1)
  (:= (nthcdr 1 (nthcdr (+ -1 (len path1)) path2)))
  (:rewrite nthcdr-of-nthcdr)
  :top (:claim (>= (+ -1 (len path1)) 0))
  :s)
 :rule-classes
 ((:rewrite
   :corollary
   (implies
    (and
     (equal (len path2) (+ 1 (len path1)))
     (m1-directory-file-p
      (mv-nth 0
              (hifat-find-file
               (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
               (list (car name-list)))))
     (<
      0
      (mv-nth
       2
       (hifat-pread
        (find-new-index (strip-cars (fd-table-fix fd-table)))
        2097152 0 fs
        (cons (cons (find-new-index (strip-cars (fd-table-fix fd-table)))
                    (find-new-index (strip-cars (file-table-fix file-table))))
              fd-table)
        (cons (cons (find-new-index (strip-cars (file-table-fix file-table)))
                    (file-table-element 0
                                        (append path1 (list (car name-list)))))
              file-table))))
     (fat32-filename-list-p path2)
     (consp
      (assoc-equal (car name-list)
                   (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
     (equal (nth (len path1) path2)
            (car name-list))
     (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2)))
     (prefixp path1 path2))
    (not
     (atom
      (assoc-equal
       path2
       (hifat-tar-name-list-alist
        fs (append path1 (list (car name-list)))
        (<<-sort
         (strip-cars
          (m1-file->contents
           (mv-nth
            0
            (hifat-find-file
             (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
             (list (car name-list)))))))
        (+ -1 entry-count)))))))
  (:rewrite
   :corollary
   (implies
    (and
     (equal (len path2) (+ 1 (len path1)))
     (m1-directory-file-p
      (mv-nth 0
              (hifat-find-file
               (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
               (list (car name-list)))))
     (<
      0
      (mv-nth
       2
       (hifat-pread
        (find-new-index (strip-cars (fd-table-fix fd-table)))
        2097152 0 fs
        (cons (cons (find-new-index (strip-cars (fd-table-fix fd-table)))
                    (find-new-index (strip-cars (file-table-fix file-table))))
              fd-table)
        (cons (cons (find-new-index (strip-cars (file-table-fix file-table)))
                    (file-table-element 0
                                        (append path1 (list (car name-list)))))
              file-table))))
     (fat32-filename-list-p path2)
     (consp
      (assoc-equal (car name-list)
                   (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
     (equal (nth (len path1) path2)
            (car name-list))
     (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2)))
     (prefixp path1 path2))
    (consp
     (assoc-equal
      path2
      (hifat-tar-name-list-alist
       fs (append path1 (list (car name-list)))
       (<<-sort
        (strip-cars
         (m1-file->contents
          (mv-nth
           0
           (hifat-find-file
            (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
            (list (car name-list)))))))
       (+ -1 entry-count))))))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-18
  (implies
   (and
    (< (+ 1 (len path1)) (len path2))
    (fat32-filename-list-p path2)
    (consp
     (assoc-equal (car name-list)
                  (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
    (equal (nth (len path1) path2)
           (car name-list))
    (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2)))
    (prefixp path1 path2))
   (consp
    (assoc-equal
     (nth (+ 1 (len path1)) path2)
     (m1-file->contents
      (mv-nth 0
              (hifat-find-file
               (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
               (list (car name-list))))))))
  :instructions
  (:promote
   (:bash
    ("goal"
     :do-not-induct t
     :in-theory
     (e/d
      (hifat-find-file hifat-pread nthcdr)
      (append-when-prefixp
       (:rewrite
        no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-1)
       (:rewrite hifat-find-file-of-append-1)))
     :use ((:instance append-when-prefixp
                      (x (append path1 (list (car name-list))))
                      (y path2))
           (:instance (:rewrite hifat-find-file-of-append-1)
                      (y (cons (car name-list)
                               (cdr (nthcdr (len path1) path2))))
                      (x path1)
                      (fs fs)))))
   (:claim (equal (nth (+ 1 (len path1)) path2)
                  (cadr (nthcdr (len path1) path2)))
           :hints :none)
   (:bash
    ("goal"
     :do-not-induct t
     :in-theory
     (e/d
      (hifat-find-file hifat-pread nthcdr)
      (append-when-prefixp
       (:rewrite
        no-duplicatesp-of-strip-cars-of-hifat-tar-name-list-alist-lemma-1)))
     :expand
     (hifat-find-file
      (m1-file->contents
       (cdr (assoc-equal
             (car name-list)
             (m1-file->contents (mv-nth 0 (hifat-find-file fs path1))))))
      (cdr (nthcdr (len path1) path2)))))
   (:dive 2 1)
   (:= (nthcdr 1 (nthcdr (len path1) path2)))
   (:rewrite nthcdr-of-nthcdr)
   :up (:rewrite car-of-nthcdr)
   :top :bash))

(defthm hifat-tar-name-list-alist-correctness-lemma-19
  (implies
   (and
    (not (equal path2 (list (car name-list))))
    (fat32-filename-list-p path2)
    (equal (nth 0 path2) (car name-list))
    (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2))))
   (not
    (stringp
     (m1-file->contents (mv-nth 0
                                (hifat-find-file fs (list (car name-list))))))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hifat-find-file) nil)
           :expand (hifat-find-file fs path2))))

(defthm
  hifat-tar-name-list-alist-correctness-lemma-20
  (implies
   (and
    (stringp
     (m1-file->contents
      (mv-nth 0
              (hifat-find-file
               (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
               (list (car name-list))))))
    (fat32-filename-list-p path2)
    (consp
     (assoc-equal (car name-list)
                  (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
    (equal (nth (len path1) path2)
           (car name-list))
    (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2)))
    (prefixp path1 path2))
   (equal path2
          (append path1 (list (car name-list)))))
  :instructions
  (:promote
   (:claim (equal (consp (cdr (nthcdr (len path1) path2)))
                  (< (nfix (+ 1 (len path1)))
                     (len path2)))
           :hints :none)
   (:bash ("goal" :in-theory (e/d (hifat-find-file)
                                  ((:rewrite hifat-find-file-of-append-1)
                                   append-when-prefixp))
           :use ((:instance append-when-prefixp (x path1)
                            (y path2))
                 (:instance (:rewrite hifat-find-file-of-append-1)
                            (y (nthcdr (len path1) path2))
                            (x path1)
                            (fs fs)))))
   (:dive 1)
   := :top :bash
   (:= (nthcdr (len path1) path2)
       (cons (car (nthcdr (len path1) path2))
             (cdr (nthcdr (len path1) path2)))
       :hints :none)
   (:rewrite cons-equal)
   :bash (:dive 2)
   (:rewrite cons-car-cdr)
   :top :bash (:dive 1 1)
   (:= (nthcdr 1 (nthcdr (len path1) path2)))
   (:rewrite nthcdr-of-nthcdr)
   :up (:rewrite consp-of-nthcdr)
   :top :bash)
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (not
       (equal path2
              (append path1 (list (car name-list)))))
      (fat32-filename-list-p path2)
      (consp
       (assoc-equal (car name-list)
                    (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
      (equal (nth (len path1) path2)
             (car name-list))
      (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2)))
      (prefixp path1 path2))
     (not
      (stringp
       (m1-file->contents
        (mv-nth 0
                (hifat-find-file
                 (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
                 (list (car name-list)))))))))))

;; Hypotheses minimised.
(defthm
  hifat-tar-name-list-alist-correctness-2
  (b*
      ((contents1
        (if
            (consp path1)
            (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))
          fs)))
    (implies
     (and
      (m1-file-alist-p fs)
      (hifat-no-dups-p fs)
      (fat32-filename-list-p path2)
      (fat32-filename-list-p name-list)
      (no-duplicatesp-equal name-list)
      (subsetp-equal name-list (strip-cars contents1))
      (member-equal
       (nth (len path1) path2) name-list)
      (<= (hifat-entry-count
           (remove-assocs-equal (set-difference-equal (strip-cars contents1) name-list) contents1))
          (nfix entry-count))
      (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path2)))
      (prefixp path1 path2)
      (>= 100
          (len (fat32-path-to-path path2))))
     (consp
      (assoc-equal path2
                   (hifat-tar-name-list-alist fs path1 name-list entry-count)))))
  :hints
  (("goal"
    :induct
    (hifat-tar-name-list-string fs path1 name-list fd-table
                                file-table dir-stream-table entry-count)
    :expand
    ((:free
      (path1)
      (hifat-tar-name-list-alist fs path1 name-list entry-count))
     (hifat-tar-name-list-string fs path1 name-list fd-table file-table
                                 dir-stream-table entry-count)
     (:with
      (:definition set-difference$-redefinition)
      (:free (l1)
             (set-difference-equal l1 name-list))))
    :in-theory
    (e/d (;; enabling the definition rules for these two, below, just
          ;; leads to sadness with regards to
          ;; hifat-tar-name-list-string-reduction. the small number of
          ;; subgoals which need the definition should be handled with
          ;; expand hints and specific rules.
          (:induction hifat-tar-name-list-string)
          (:induction hifat-tar-name-list-alist)
          ;; there are too many lemmas which need these syscall
          ;; definitions to be opened up.
          hifat-open hifat-lstat hifat-opendir
          get-names-from-dirp-alt
          painful-debugging-lemma-21
          length-of-empty-list
          hifat-entry-count
          member-equal
          subsetp-equal
          remove-assocs-equal)
         (append-of-cons
          binary-append
          string-append
          take-of-too-many
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite take-of-len-free)
          (:linear position-equal-ac-when-member)
          (:definition position-equal-ac)
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
          (:linear
           hifat-tar-name-list-alist-correctness-lemma-1)
          (:linear hifat-entry-count-when-hifat-subsetp)
          ;; it's dubious how much labour is saved by disabling these,
          ;; but it's worth a shot.
          (:definition atom)
          (:definition min)
          (:definition nfix)
          (:definition natp))))
   ("subgoal *1/5"
    :expand
    ((hifat-entry-count
      (remove-assocs-equal (set-difference-equal (strip-cars fs)
                                                 name-list)
                           fs))
     (hifat-entry-count
      (remove-assocs-equal
       (set-difference-equal
        (remove-equal
         (car name-list)
         (strip-cars
          (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
        (cdr name-list))
       (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
     (hifat-entry-count
      (remove-assocs-equal
       (set-difference-equal
        (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs path1))))
        name-list)
       (m1-file->contents (mv-nth 0 (hifat-find-file fs path1)))))
     (hifat-entry-count
      (cdr (remove-assocs-equal (set-difference-equal (strip-cars fs)
                                                      name-list)
                                fs)))))))
