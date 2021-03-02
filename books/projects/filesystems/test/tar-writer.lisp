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

(defund tar-reg-file-string (fat32$c path)
  (declare (xargs :guard (and (lofat-fs-p fat32$c)
                              (stringp path))
                  :stobjs fat32$c
                  :guard-debug t
                  :guard-hints (("Goal" :in-theory (disable MAKE-LIST-AC-REMOVAL)) )
                  :verify-guards nil))
  (b*
      ((fat32-path (path-to-fat32-path (coerce path 'list)))
       ((unless (fat32-filename-list-p fat32-path)) "")
       ((mv val & &) (lofat-lstat fat32$c fat32-path))
       (file-length (struct-stat->st_size val))
       ((mv fd-table file-table fd &)
        (lofat-open fat32-path nil nil))
       ((unless (>= fd 0)) "")
       ((mv contents & &)
        (lofat-pread
         fd file-length 0 fat32$c fd-table file-table))
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
  tar-d-e-list-string
  (fat32$c path d-e-list)
  (declare
   (xargs
    :guard (and (lofat-fs-p fat32$c)
                (useful-d-e-list-p d-e-list)
                (stringp path))
    :stobjs fat32$c
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
     (lofat-to-hifat-helper fat32$c d-e-list
                            (max-entry-count fat32$c)))
    :hints
    (("goal"
      :expand
      (lofat-to-hifat-helper fat32$c d-e-list
                             (max-entry-count fat32$c))
      :in-theory
      (enable lofat-to-hifat-helper-correctness-4)))))
  (b*
      (((unless
         (mbe :exec (consp d-e-list)
              :logic (and (consp d-e-list)
                          (useful-d-e-list-p d-e-list))))
        "")
       ((mv & & & error-code)
        (lofat-to-hifat-helper fat32$c d-e-list
                               (max-entry-count fat32$c)))
       ((unless (zp error-code)) "")
       (head (car d-e-list))
       (head-path
        (concatenate
         'string path "/"
         (coerce
          (fat32-name-to-name (coerce (d-e-filename head) 'list))
          'string)))
       ((unless (d-e-directory-p head))
        (concatenate
         'string
         (tar-reg-file-string fat32$c head-path)
         (tar-d-e-list-string fat32$c
                                  path (cdr d-e-list))))
       ((mv head-cc-contents &)
        (d-e-cc-contents fat32$c head)))
    (concatenate
     'string
     (tar-header-block head-path 0 *tar-dirtype*)
     (tar-d-e-list-string
      fat32$c head-path
      (make-d-e-list head-cc-contents))
     (tar-d-e-list-string fat32$c
                              path (cdr d-e-list)))))

(b*
    (((mv & disk-image-location state)
      (getenv$ "DISK" state))
     ((mv fat32$c &)
      (disk-image-to-lofat
       fat32$c disk-image-location state))
     ((mv & input-path state)
      (getenv$ "TAR_INPUT" state))
     ((mv & val state)
      (getenv$ "TAR_OUTPUT" state))
     (output-path (path-to-fat32-path (coerce val 'list)))
     ((mv root-d-e-list &) (root-d-e-list fat32$c))
     ((mv file error-code)
      (lofat-find-file fat32$c root-d-e-list
                       (path-to-fat32-path (coerce input-path 'list))))
     ((unless (zp error-code))
      (mv fat32$c state))
     (file-text
      (if
          (lofat-regular-file-p file)
          (tar-reg-file-string fat32$c input-path)
        (concatenate
         'string
         (tar-header-block input-path 0 *tar-dirtype*)
         (tar-d-e-list-string
          fat32$c input-path (lofat-file->contents file)))))
     ((mv fd-table file-table fd &)
      (lofat-open output-path nil nil))
     ((mv fat32$c & &)
      (lofat-pwrite fd file-text 0 fat32$c fd-table file-table))
     ((mv state &)
      (lofat-to-disk-image
       fat32$c disk-image-location state)))
  (mv fat32$c state))
