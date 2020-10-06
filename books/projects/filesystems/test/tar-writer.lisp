(include-book "../tar-stuff")

(local (in-theory (disable mod ceiling floor)))

(defund
  tar-header-block (path len typeflag)
  (declare
   (xargs :guard (and (characterp typeflag)
                      (stringp path)
                      (>= 100 (length path))
                      (natp len))
          :guard-hints
          (("goal" :in-theory (disable make-list-ac-removal)))))
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

(defthm
  length-of-tar-header-block
  (implies (>= 100 (length (str-fix path)))
           (equal (len (explode (tar-header-block path len typeflag)))
                  512))
  :hints (("goal" :in-theory (enable tar-header-block))))

(defund tar-reg-file-string (fat32-in-memory path)
  (declare (xargs :guard (and (lofat-fs-p fat32-in-memory)
                              (stringp path))
                  :stobjs fat32-in-memory
                  :guard-debug t
                  :guard-hints (("Goal" :in-theory (disable MAKE-LIST-AC-REMOVAL)) )
                  :verify-guards nil))
  (b*
      ((fat32-path (path-to-fat32-path (coerce path 'list)))
       ((unless (fat32-filename-list-p fat32-path)) "")
       ((mv val & &) (lofat-lstat fat32-in-memory fat32-path))
       (file-length (struct-stat->st_size val))
       ((mv fd-table file-table fd &)
        (lofat-open fat32-path nil nil))
       ((unless (>= fd 0)) "")
       ((mv contents & &)
        (lofat-pread
         fd file-length 0 fat32-in-memory fd-table file-table))
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
      'string))))

(defund
  tar-dir-ent-list-string
  (fat32-in-memory path dir-ent-list)
  (declare
   (xargs
    :guard (and (lofat-fs-p fat32-in-memory)
                (useful-dir-ent-list-p dir-ent-list)
                (stringp path))
    :stobjs fat32-in-memory
    :guard-debug t
    :guard-hints
    (("goal"
      :in-theory (e/d (lofat-to-hifat-helper
                       lofat-to-hifat-helper-correctness-4)
                      (make-list-ac-removal))))
    :verify-guards nil
    :measure
    (mv-nth
     1
     (lofat-to-hifat-helper fat32-in-memory dir-ent-list
                            (max-entry-count fat32-in-memory)))
    :hints
    (("goal"
      :expand
      (lofat-to-hifat-helper fat32-in-memory dir-ent-list
                             (max-entry-count fat32-in-memory))
      :in-theory
      (enable lofat-to-hifat-helper-correctness-4)))))
  (b*
      (((unless
         (mbe :exec (consp dir-ent-list)
              :logic (and (consp dir-ent-list)
                          (useful-dir-ent-list-p dir-ent-list))))
        "")
       ((mv & & & error-code)
        (lofat-to-hifat-helper fat32-in-memory dir-ent-list
                               (max-entry-count fat32-in-memory)))
       ((unless (zp error-code)) "")
       (head (car dir-ent-list))
       (head-path
        (concatenate
         'string path "/"
         (coerce
          (fat32-name-to-name (coerce (dir-ent-filename head) 'list))
          'string)))
       ((unless (dir-ent-directory-p head))
        (concatenate
         'string
         (tar-reg-file-string fat32-in-memory head-path)
         (tar-dir-ent-list-string fat32-in-memory
                                  path (cdr dir-ent-list))))
       ((mv head-clusterchain-contents &)
        (dir-ent-clusterchain-contents fat32-in-memory head)))
    (concatenate
     'string
     (tar-header-block head-path 0 *tar-dirtype*)
     (tar-dir-ent-list-string
      fat32-in-memory head-path
      (make-dir-ent-list head-clusterchain-contents))
     (tar-dir-ent-list-string fat32-in-memory
                              path (cdr dir-ent-list)))))

(b*
    (((mv & disk-image-location state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory disk-image-location state))
     ((mv & input-path state)
      (getenv$ "TAR_INPUT" state))
     ((mv & val state)
      (getenv$ "TAR_OUTPUT" state))
     (output-path (path-to-fat32-path (coerce val 'list)))
     ((mv root-dir-ent-list &) (root-dir-ent-list fat32-in-memory))
     ((mv file error-code)
      (lofat-find-file fat32-in-memory root-dir-ent-list
                       (path-to-fat32-path (coerce input-path 'list))))
     ((unless (zp error-code))
      (mv fat32-in-memory state))
     (file-text
      (if
          (lofat-regular-file-p file)
          (tar-reg-file-string fat32-in-memory input-path)
        (concatenate
         'string
         (tar-header-block input-path 0 *tar-dirtype*)
         (tar-dir-ent-list-string
          fat32-in-memory input-path (lofat-file->contents file)))))
     ((mv fd-table file-table fd &)
      (lofat-open output-path nil nil))
     ((mv fat32-in-memory & &)
      (lofat-pwrite fd file-text 0 fat32-in-memory fd-table file-table))
     ((mv state &)
      (lofat-to-disk-image
       fat32-in-memory disk-image-location state)))
  (mv fat32-in-memory state))
