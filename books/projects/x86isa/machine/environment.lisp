;; AUTHORS:
;; Shilpi Goel <shigoel@cs.utexas.edu>
;; Soumava Ghosh <soumava@cs.utexas.edu>
;; Matt Kaufmann <kaufmann@cs.utexas.edu>

(in-package "X86ISA")

(include-book "top-level-memory" :ttags (:undef-flg))

;; ======================================================================

(defsection environment
  :parents (machine)
  :short "Defining the environment field for reasoning about
  non-deterministic computations"
  )

;; ======================================================================

(defsection converting-between-strings-and-bytes

  :parents (environment)

  (define bytes-to-charlist (bytes)
    :guard (byte-listp bytes)
    :returns (lst character-listp
                  :hyp (force (byte-listp bytes))
                  :rule-classes :type-prescription)
    (if (endp bytes)
        nil
      (cons (code-char (car bytes))
            (bytes-to-charlist (cdr bytes)))))

  (define charlist-to-bytes (charlist)
    :guard (character-listp charlist)
    :returns (lst byte-listp
                  :hyp (force (character-listp bytes))
                  :rule-classes :type-prescription)
    (if (endp charlist)
        nil
      (cons (char-code (car charlist))
            (charlist-to-bytes (cdr charlist))))
    ///
    (defthm same-length-of-byte-and-character-lists
      (implies (character-listp charlist)
               (equal (len (charlist-to-bytes charlist))
                      (len charlist)))))

  (define string-to-bytes (str)
    :guard (stringp str)
    :returns (lst byte-listp
                  :hyp (force (stringp str))
                  :rule-classes :type-prescription
                  :hints (("Goal" :in-theory (e/d ()
                                                  (str::coerce-to-list-removal)))))
    (charlist-to-bytes (coerce str 'LIST)))

  (define bytes-to-string (bytes)
    :guard (byte-listp bytes)
    :returns (lst stringp :hyp (force (byte-listp bytes))
                  :rule-classes :type-prescription)
    (coerce (bytes-to-charlist bytes) 'STRING))

  (local
   (include-book "std/lists/take" :dir :system))

  (define read-n-bytes-from-string (n str)
    :guard (and (natp n) (stringp str))
    (let* ((bytes (string-to-bytes str))
           (n-bytes (take n bytes)))
      n-bytes)
    ///
    (defthm take-byte-listp
      (implies (and (byte-listp xs)
                    (natp n)
                    (<= n (len xs)))
               (byte-listp (take n xs)))
      :hints (("Goal" :induct (ACL2::simpler-take-induction n x))))

    (defthm byte-listp-read-n-bytes-from-string
      (implies (and (natp n)
                    (< n (len (string-to-bytes str)))
                    (stringp str))
               (byte-listp (read-n-bytes-from-string n str)))
      :rule-classes :type-prescription))

  (define read-n-bytes-from-string-as-string (n str)
    :guard (and (natp n) (stringp str))
    (b* ((n-bytes (read-n-bytes-from-string n str))
         ((when (not (byte-listp n-bytes)))
          nil)
         (new-charlist (bytes-to-charlist n-bytes))
         (new-str (coerce new-charlist 'STRING)))
        new-str)
    ///
    (defthm stringp-read-n-bytes-from-string-as-string
      (implies (and (natp n)
                    (< n (len (string-to-bytes str)))
                    (stringp str))
               (stringp (read-n-bytes-from-string-as-string n str)))
      :rule-classes :type-prescription)))

;; ======================================================================

;; Now follow some functions that take x86 as an argument and/or
;; modify it:

(defsection reading-memory-as-strings-or-bytes

  :parents (environment)

  (local (xdoc::set-default-parents reading-memory-as-strings-or-bytes))

  (define read-memory-zero-terminated
    ((ptr :type (signed-byte 49))
     x86 acc)
    :short "Read memory as bytes till a zero is encountered"
    :long "<p>Returns a list of bytes (byte at the smallest address is
    the first byte of the list).</p>"
    :measure (nfix (- *2^47* ptr))
    :guard (and (integerp ptr)
                ;; NOT (signed-byte-p 48).
                (<= (- *2^47*) ptr)
                (<= ptr *2^47*)
                (nat-listp acc))

    (if (signed-byte-p 48 ptr)

        (b* (((mv flg (the (unsigned-byte 8) mem-val) x86)
              (rml08 ptr :r x86))
             ((when flg)
              (mv flg acc x86)))

          (if (equal 0 mem-val)
              (mv nil (append (reverse acc) '(0)) x86)

            (read-memory-zero-terminated
             (the (signed-byte 49) (1+ ptr))
             x86 (cons mem-val acc))))

      (mv t (reverse acc) x86))

    ///

    (defthm byte-listp-mv-nth-1-read-memory-zero-terminated
      (implies (and (x86p x86)
                    (byte-listp acc))
               (byte-listp (mv-nth 1 (read-memory-zero-terminated ptr x86 acc))))
      :rule-classes :type-prescription)

    (defthm x86p-mv-nth-2-read-memory-zero-terminated
      (implies (x86p x86)
               (x86p (mv-nth 2 (read-memory-zero-terminated ptr x86 acc))))))

  (define read-string-zero-terminated
    ((ptr :type (signed-byte 49))
     x86)
    :guard (and (integerp ptr)
                (<= (- *2^47*) ptr)
                (<= ptr *2^47*))
    :short "Read memory as a string till a zero is encountered"

    (b* (((mv flg bytes x86)
          (read-memory-zero-terminated ptr x86 nil))
         ((when flg)
          (mv flg "nil" x86))
         (charlist (bytes-to-charlist bytes)))
      (mv nil (coerce charlist 'string) x86))

    ///

    (defthm stringp-mv-nth-1-read-string-zero-terminated
      (implies (force (x86p x86))
               (stringp (mv-nth 1 (read-string-zero-terminated ptr x86))))
      :rule-classes :type-prescription)

    (defthm x86p-mv-nth-2-read-string-zero-terminated
      (implies (x86p x86)
               (x86p (mv-nth 2 (read-string-zero-terminated ptr x86))))))

  (define read-bytes-from-memory
    ((ptr    :type (signed-byte #.*max-linear-address-size+1*))
     (nbytes :type (unsigned-byte #.*max-linear-address-size*))
     x86 acc)
    :short "Read @('nbytes') bytes from memory"
    :long "<p>Returns a list of bytes (byte at the smallest address is
    the first byte of the list).</p>"

    :measure (nfix nbytes)
    :guard (and (integerp nbytes)
                (<= 0 nbytes)
                (integerp ptr)
                (<= (- *2^47*) ptr)
                (< (+ ptr nbytes) *2^47*)
                (nat-listp acc))
    :split-types t

    (if (mbt (and (integerp nbytes)
                  (integerp ptr)
                  (<= (- *2^47*) ptr)
                  (< (+ ptr nbytes) *2^47*)))

        (if (zp nbytes)
            (mv nil (reverse acc) x86)
          (b* (((mv flg (the (unsigned-byte 8) byte) x86)
                (rml08 ptr :r x86))
               ((when flg)
                (mv flg nil x86)))
            (read-bytes-from-memory (the (signed-byte 49) (1+ ptr))
                                    (the (unsigned-byte 48) (1- nbytes))
                                    x86
                                    (cons byte acc))))
      (mv t (reverse acc) x86))

    ///

    (defthm byte-listp-mv-nth-1-read-bytes-from-memory
      (implies (forced-and (x86p x86)
                           (byte-listp acc))
               (byte-listp (mv-nth 1 (read-bytes-from-memory ptr nbytes x86 acc))))
      :rule-classes :type-prescription)

    (defthm x86p-mv-nth-2-read-bytes-from-memory
      (implies (x86p x86)
               (x86p (mv-nth 2 (read-bytes-from-memory ptr nbytes x86 acc))))))

  (define read-string-from-memory
    ((ptr    :type (signed-byte #.*max-linear-address-size+1*))
     (nbytes :type (signed-byte #.*max-linear-address-size*))
     x86)
    :short "Read @('nbytes') bytes from memory as a string"
    :guard (and (integerp nbytes)
                (<= 0 nbytes)
                (integerp ptr)
                (<= (- *2^47*) ptr)
                (< (+ ptr nbytes) *2^47*))

    (b* (((mv flg bytes x86)
          (read-bytes-from-memory ptr nbytes x86 nil))
         ((when flg)
          (mv flg "nil" x86))
         (charlist (bytes-to-charlist bytes)))
      (mv nil (coerce charlist 'string) x86))

    ///

    (defthm stringp-mv-nth-1-read-string-from-memory
      (implies (force (x86p x86))
               (stringp (mv-nth 1 (read-string-from-memory ptr nbytes x86))))
      :rule-classes :type-prescription)

    (defthm x86p-mv-nth-2-read-string-from-memory
      (implies (x86p x86)
               (x86p (mv-nth 2 (read-string-from-memory ptr nbytes x86)))))))

;; ======================================================================

(defsection writing-strings-or-bytes-to-memory

  :parents (environment)

  (local (xdoc::set-default-parents writing-strings-or-bytes-to-memory))

  (local (in-theory (e/d () (str::coerce-to-list-removal))))

  (define write-bytes-to-memory
    ((ptr :type (signed-byte #.*max-linear-address-size+1*))
     bytes x86)
    :short "The byte at the smallest address should be the last byte
    of bytes."
    :measure (len bytes)
    :split-types t
    :guard (and (integerp ptr)
                (<= (- *2^47*) ptr)
                (byte-listp bytes)
                (< (+ -1 (len bytes) ptr) *2^47*))
    :returns (mv flg
                 (x86 x86p :hyp (x86p x86)))

    (if (mbt (and (integerp ptr)
                  (<= (- *2^47*) ptr)
                  (byte-listp bytes)
                  (< (+ -1 (len bytes) ptr) *2^47*)))

        (if (endp bytes)
            (mv nil x86)
          (b* (((mv flg x86)
                (wml08 ptr (the (unsigned-byte 8) (car bytes)) x86))
               ((when flg)
                (mv flg x86)))
            (write-bytes-to-memory
             (the (signed-byte 49) (1+ ptr))
             (cdr bytes) x86)))

      (mv t x86))

    ///

    (local (include-book "centaur/bitops/ihs-extensions" :dir :system))

    (defthm rewrite-write-bytes-to-memory-to-wb
      (implies (and (app-view x86)
                    (canonical-address-p (+ -1 (len bytes) addr))
                    (canonical-address-p addr)
                    (byte-listp bytes))
               (and
                (equal (mv-nth 0 (write-bytes-to-memory addr bytes x86))
                       (mv-nth 0 (wb (len bytes) addr :w (combine-bytes bytes) x86)))
                (equal (mv-nth 1 (write-bytes-to-memory addr bytes x86))
                       (mv-nth 1 (wb (len bytes) addr :w (combine-bytes bytes) x86)))))
      :hints (("Goal" :in-theory (e/d* (wb
                                        wb-1
                                        wb-1-opener-theorem
                                        wml08
                                        canonical-address-p
                                        signed-byte-p)
                                       ())))))

  (define write-string-to-memory
    ((ptr :type (signed-byte #.*max-linear-address-size+1*))
     str x86)
    :split-types t
    :guard-hints
    (("Goal" :in-theory (e/d (string-to-bytes) ())))
    :guard (and (stringp str)
                (integerp ptr)
                (<= (- *2^47*) ptr)
                (< (+ -1 ptr (length str)) *2^47*))

    :returns (mv flg
                 (x86 x86p :hyp (x86p x86)))

    (let ((bytes (string-to-bytes str)))
      (write-bytes-to-memory ptr bytes x86))))

;; ======================================================================

(defsection components-of-the-environment-field

  :parents (environment)

  :long "<p>We don't check for ill-formed environment very rigorously.
  For example, one can have <tt>STANDARD-INPUT</tt>'s mode as
  <tt>O_WRONLY</tt>, and it'll still be a good @('env-alistp').</p>

<code>
  '((:FILE-DESCRIPTORS . ((0 . ((:NAME . \"STANDARD-INPUT\")
                                (:OFFSET . 0)
                                (:MODE . 0)))
                          (1 . ((:NAME . \"STANDARD-OUTPUT\")
                                (:OFFSET . 0)
                                (:MODE . 1)))
                          (2 . ((:NAME . \"ERROR\")
                                (:OFFSET . 0)
                                (:MODE . 2)))
                          (3 . ((:NAME . \"FOO.TXT\")
                                (:OFFSET . 0)
                                (:MODE . 8)))))

    (:FILE-CONTENTS    . ((\"STANDARD-INPUT\"  . ((:CONTENTS . \"Contents 0\")))
                          (\"STANDARD-OUTPUT\" . ((:CONTENTS . \"Contents 1\")))
                          (\"ERROR\"           . ((:CONTENTS . \"Contents 2\")))
                          (\"FOO.TXT\"         . ((:CONTENTS . \"Contents 3\")))
                          ))

    (:ORACLE           . ((1 . ((-1 . \"hello\") 5000))
                          (2 . (0)))))
</code>"

  (local (xdoc::set-default-parents components-of-the-environment-field))

  (defthm alistp-put-assoc-equal-equal
    (implies (force (alistp x))
             (alistp (put-assoc-equal i y x)))
    :rule-classes :type-prescription)

  (defthm alistp-delete-assoc-equal-equal
    (implies (force (alistp x))
             (alistp (delete-assoc-equal i x)))
    :rule-classes :type-prescription)

  (define env-read-logic (x86)
    :enabled t
    (env x86))

  (define env-read (x86)
    :inline nil
    :enabled t
    ;; Important for this function to not be inline because it's
    ;; definition will be smashed under the hood (see
    ;; environment-and-syscalls-raw.lsp).
    (env-read-logic x86)
    ///
    (defthm env-alistp-env-read
      (implies (x86p x86)
               (env-alistp (env-read x86)))
      :hints (("Goal" :in-theory (e/d  (env-read-logic) (env-alistp))))
      :rule-classes :forward-chaining))

  (define env-write-logic (env x86)
    :enabled t
    :guard (env-alistp env)
    (!env env x86))

  (define env-write (env x86)
    :enabled t
    :inline nil
    :guard (env-alistp env)
    (env-write-logic env x86)
    ///
    (local (in-theory (e/d (env-write-logic) ())))
    (defthm x86p-env-write
      (implies (and (x86p x86)
                    (env-alistp env))
               (x86p (env-write env x86)))))


  ;; File descriptor field:

  (define read-x86-file-des-logic (id x86)

    :short "Read File Descriptor Field"

    :long "<p>Read the field entry corresponding to key @('id') in the
    @(':FILE-DESCRIPTORS') field of the environment.</p>"

    :guard (integerp id)
    :guard-hints (("Goal" :in-theory (e/d (x86p env envp xr env*) ())))

    (b* ((env (env-read x86))
         (file-des-field (assoc-equal :file-descriptors env))
         (fd-name-field (if (atom file-des-field)
                            nil
                          (assoc-equal id (cdr file-des-field))))
         (name-field (if (atom fd-name-field)
                         nil
                       (cdr fd-name-field))))
        name-field))

  (define read-x86-file-des (id x86)
    :inline nil
    :guard (integerp id)
    (read-x86-file-des-logic id x86))

  (defthm read-x86-file-des-xw
    (implies (not (equal fld :env))
             (equal (read-x86-file-des id (xw fld index value x86))
                    (read-x86-file-des id x86)))
    :hints (("Goal" :in-theory (e/d* (read-x86-file-des
                                      read-x86-file-des-logic)
                                     ()))))

  (define write-x86-file-des-logic (fd fd-field x86)

    :long "<p>Replacing the value associated with the @('fd') key by
     @('fd-field') in the @(':FILE-DESCRIPTORS') field of the
     environment.</p>"

    :guard (integerp fd)
    :guard-hints (("Goal" :in-theory (e/d (x86p envp env env-alistp
                                                env* !env* xw xr)
                                          ())))
    (b* ((env (env-read x86))
         (file-des-field  (cdr (assoc-equal :file-descriptors env)))
         (x86
          (env-write
           (acons ':file-descriptors (put-assoc-equal fd fd-field file-des-field)
                  (acons ':file-contents (cdr (assoc-equal :file-contents env))
                         (acons ':oracle (cdr (assoc-equal :oracle env)) nil)))
           x86)))
        x86))

  (define write-x86-file-des (fd fd-field x86)
    :inline nil
    :guard (integerp fd)
    (write-x86-file-des-logic fd fd-field x86)
    ///
    (defthm x86p-write-x86-file-des
      (implies (and (x86p x86)
                    (integerp fd))
               (x86p (write-x86-file-des fd fd-field x86)))
      :hints (("Goal" :in-theory (e/d (x86p env !env envp
                                            write-x86-file-des-logic
                                            env-alistp
                                            env* !env* xr xw)
                                      ())))))

  (defthm xr-write-x86-file-des
    (implies (not (equal fld :env))
             (equal (xr fld index (write-x86-file-des fd fd-field x86))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (write-x86-file-des
                                      write-x86-file-des-logic)
                                     ()))))

  ;; Contributed by Alessandro Coglio
  (defrule 64-bit-modep-of-write-x86-file-des
    (equal (64-bit-modep (write-x86-file-des fd fd-field x86))
           (64-bit-modep x86))
    :hints (("Goal" :in-theory (e/d* (write-x86-file-des
                                      write-x86-file-des-logic)
                                     ()))))

  (defthm write-x86-file-des-xw
    (implies (not (equal fld :env))
             (equal (write-x86-file-des i v (xw fld index value x86))
                    (xw fld index value (write-x86-file-des i v x86))))
    :hints (("Goal" :in-theory (e/d* (write-x86-file-des
                                      write-x86-file-des-logic)
                                     ()))))

  (define delete-x86-file-des-logic (fd x86)

    :long "<p>Delete the fd key-value pair in the :FILE-DESCRIPTORS
     field of the environment.</p>"

    :guard (integerp fd)
    :guard-hints (("Goal" :in-theory
                   (e/d (x86p envp env env* env-alistp xr)
                        ())))
    (b* ((env (env-read x86))
         (file-des-field  (cdr (assoc-equal :file-descriptors env)))
         (x86
          (env-write
           (acons ':file-descriptors (delete-assoc-equal fd file-des-field)
                  (acons ':file-contents (cdr (assoc-equal :file-contents env))
                         (acons ':oracle (cdr (assoc-equal :oracle env)) nil)))
           x86)))
        x86))

  (define delete-x86-file-des (fd x86)
    :inline nil
    :guard (integerp fd)
    (delete-x86-file-des-logic fd x86)
    ///
    (defthm x86p-delete-x86-file-des
      (implies (and (x86p x86)
                    (integerp fd))
               (x86p (delete-x86-file-des fd x86)))
      :hints (("Goal" :in-theory (e/d (x86p env env* !env !env* envp
                                            env-alistp
                                            xr xw
                                            delete-x86-file-des-logic)
                                      ())))))

  (defthm xr-delete-x86-file-des
    (implies (not (equal fld :env))
             (equal (xr fld index (delete-x86-file-des fd x86))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (delete-x86-file-des
                                      delete-x86-file-des-logic)
                                     ()))))

  (defthm delete-x86-file-des-xw
    (implies (not (equal fld :env))
             (equal (delete-x86-file-des i (xw fld index value x86))
                    (xw fld index value (delete-x86-file-des i x86))))
    :hints (("Goal" :in-theory (e/d* (delete-x86-file-des
                                      delete-x86-file-des-logic)
                                     ()))))

  ;; File contents field:

  (define read-x86-file-contents-logic (name x86)
    :short "Read File Contents Field"
    :long "<p> Read the field entry corresponding to key @('name') in
    the @(':FILE-CONTENTS') field of the environment.</p>"

    :guard (stringp name)
    :guard-hints (("Goal" :in-theory (e/d (x86p envp env env* !env* xr xw)
                                          ())))
    (b* ((env (env-read x86))
         (name-file-contents-field (assoc-equal :file-contents env))
         (file-contents-field
          (if (atom name-file-contents-field)
              nil
            (cdr (assoc-equal name (cdr name-file-contents-field))))))
        file-contents-field))

  (define read-x86-file-contents (name x86)
    :inline nil
    :guard (stringp name)
    (read-x86-file-contents-logic name x86))

  (defthm read-x86-file-contents-xw
    (implies (not (equal fld :env))
             (equal (read-x86-file-contents name (xw fld index value x86))
                    (read-x86-file-contents name x86)))
    :hints (("Goal" :in-theory (e/d* (read-x86-file-contents
                                      read-x86-file-contents-logic)
                                     ()))))

  (define write-x86-file-contents-logic (name contents-field x86)

    :long "<p>Replacing the value associated with the name key by
     contents-field in the :FILE-CONTENTS field of the
     environment.</p>"

    :guard (stringp name)
    :guard-hints (("Goal" :in-theory
                   (e/d (x86p envp env env-alistp env* !env* xr xw)
                        ())))
    (b* ((env (env-read x86))
         (file-contents-field  (cdr (assoc-equal :file-contents env)))
         (x86
          (env-write
           (acons ':file-descriptors (cdr (assoc-equal :file-descriptors env))
                  (acons ':file-contents
                         (put-assoc-equal name contents-field file-contents-field)
                         (acons ':oracle (cdr (assoc-equal :oracle env)) nil)))
           x86)))
        x86))

  (define write-x86-file-contents (name contents x86)
    :inline nil
    :guard (stringp name)
    (write-x86-file-contents-logic name contents x86)
    ///
    (defthm x86p-write-x86-file-contents
      (implies (and (x86p x86)
                    (stringp name))
               (x86p (write-x86-file-contents name contents x86)))
      :hints (("Goal" :in-theory (e/d (x86p env !env envp env-alistp
                                            write-x86-file-contents-logic
                                            env* !env* xr xw)
                                      ())))))

  (defthm xr-write-x86-file-contents
    (implies (not (equal fld :env))
             (equal (xr fld index (write-x86-file-contents name contents x86))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (write-x86-file-contents
                                      write-x86-file-contents-logic)
                                     ()))))

  (defthm write-x86-file-contents-xw
    (implies (not (equal fld :env))
             (equal (write-x86-file-contents i v (xw fld index value x86))
                    (xw fld index value (write-x86-file-contents i v x86))))
    :hints (("Goal" :in-theory (e/d* (write-x86-file-contents
                                      write-x86-file-contents-logic)
                                     ()))))

  (define delete-x86-file-contents-logic (name x86)
    :long "<p>Deleting the name key-value pair in the :FILE-CONTENTS
     field of the environment.</p>"
    :guard (stringp name)
    :guard-hints (("Goal" :in-theory
                   (e/d (x86p envp env env-alistp
                              env* !env* xr xw)
                        ())))
    (b* ((env (env-read x86))
         (file-contents-field  (cdr (assoc-equal :file-contents env)))
         (x86
          (env-write
           (acons ':file-descriptors (cdr (assoc-equal :file-descriptors env))
                  (acons ':file-contents
                         (delete-assoc-equal name file-contents-field)
                         (acons ':oracle (cdr (assoc-equal :oracle env)) nil)))
           x86)))
        x86))

  (define delete-x86-file-contents (name x86)
    :inline nil
    :guard (stringp name)
    (delete-x86-file-contents-logic name x86)
    ///
    (defthm x86p-delete-x86-file-contents
      (implies (and (x86p x86)
                    (stringp name))
               (x86p (delete-x86-file-contents name x86)))
      :hints (("Goal" :in-theory (e/d (x86p env !env envp env-alistp
                                            delete-x86-file-contents-logic
                                            env* !env* xr xw)
                                      ())))))

  (defthm xr-delete-x86-file-contents
    (implies (not (equal fld :env))
             (equal (xr fld index (delete-x86-file-contents name x86))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (delete-x86-file-contents
                                      delete-x86-file-contents-logic)
                                     ()))))

  (defthm delete-x86-file-contents-xw
    (implies (not (equal fld :env))
             (equal (delete-x86-file-contents i (xw fld index value x86))
                    (xw fld index value (delete-x86-file-contents i x86))))
    :hints (("Goal" :in-theory (e/d* (delete-x86-file-contents
                                      delete-x86-file-contents-logic)
                                     ()))))

  ;; Oracle Field:

  (encapsulate
   ()

   (local (in-theory (e/d (rip-ret-alistp) ())))

   (local
    (defthm pop-x86-oracle-guard-helper-0
      (implies (and (x86p x86)
                    (rip-ret-alistp oracle)
                    (consp (assoc-equal (rip* x86) oracle))
                    (consp (cdr (assoc-equal (rip* x86) oracle))))
               (rip-ret-alistp
                (put-assoc-equal
                 (rip* x86)
                 (cddr (assoc-equal (rip* x86) oracle))
                 oracle)))
      :hints (("Goal" :in-theory (e/d (x86p ripp rip)
                                      ())))))

   (local
    (defthm pop-x86-oracle-guard-helper
      (implies
       (and (x86$ap x86)
            (consp (assoc-equal (rip* x86)
                                (cdr (assoc-equal :oracle (nth *env* x86)))))
            (consp (cdr (assoc-equal (rip* x86)
                                     (cdr (assoc-equal :oracle (nth *env* x86)))))))
       (env-alistp
        (list
         (cons
          :file-descriptors (cdr (assoc-equal :file-descriptors (nth *env* x86))))
         (cons :file-contents (cdr (assoc-equal :file-contents (nth *env* x86))))
         (cons :oracle
               (put-assoc-equal
                (rip* x86)
                (cddr (assoc-equal (rip* x86)
                                   (cdr (assoc-equal :oracle (nth *env* x86)))))
                (cdr (assoc-equal :oracle (nth *env* x86))))))))
      :hints (("Goal" :in-theory (e/d (env-alistp x86p envp)
                                      (pop-x86-oracle-guard-helper-0))
               :use ((:instance pop-x86-oracle-guard-helper-0
                                (oracle
                                 (cdr (assoc-equal :oracle (nth *env* x86))))))))))

   (define pop-x86-oracle-logic (x86)
     :guard-hints
     (("Goal" :in-theory (e/d (x86p envp env env-alistp
                                    rip-ret-alistp
                                    env* !env* xr xw)
                              ())))
     (b* ((rip (rip x86))
          (env (env-read x86))
          (oracle (cdr (assoc-equal :oracle env)))
          (vals (assoc-equal rip oracle))
          (lst (if (consp vals)
                   (if (consp (cdr vals))
                       (cdr vals)
                     nil)
                 nil))
          ((mv val x86)
           (if (atom lst)
               (let ((x86 (!ms (list :syscall-oracle-pop-empty rip) x86)))
                 (mv -1 x86))
             (let ((x86
                    (env-write
                     (acons ':file-descriptors (cdr (assoc-equal :file-descriptors env))
                            (acons ':file-contents (cdr (assoc-equal :file-contents env))
                                   (acons ':oracle
                                          (put-assoc-equal rip (cdr lst)
                                                           oracle)
                                          nil)))
                     x86)))
               (mv (car lst) x86)))))
         (mv val x86)))

   (define pop-x86-oracle (x86)
     :inline nil
     :prepwork ((local (in-theory (e/d (xr) ()))))
     (pop-x86-oracle-logic x86)
     ///

     (defthm x86p-mv-nth-1-pop-x86-oracle
       (implies (x86p x86)
                (x86p (mv-nth 1 (pop-x86-oracle x86))))
       :hints (("Goal" :in-theory (e/d (pop-x86-oracle-logic
                                        env-alistp)
                                       (env-alistp-env))
                :use ((:instance env-alistp-env))))))

   ;; Relating pop-x86-oracle and xr/xw:

   (defthm xr-pop-x86-oracle-state
     (implies (and (not (equal fld :env))
                   (not (equal fld :ms)))
              (equal (xr fld index (mv-nth 1 (pop-x86-oracle x86)))
                     (xr fld index x86)))
     :hints (("Goal" :in-theory (e/d* (pop-x86-oracle
                                       pop-x86-oracle-logic)
                                      ()))))

   (defthm pop-x86-oracle-xw
     (implies (and (not (equal fld :env))
                   (not (equal fld :rip)))
              (equal (mv-nth 0 (pop-x86-oracle (xw fld index value x86)))
                     (mv-nth 0 (pop-x86-oracle x86))))
     :hints (("Goal" :in-theory (e/d* (pop-x86-oracle
                                       pop-x86-oracle-logic)
                                      ()))))


   (defthm xw-pop-x86-oracle-state
     ;; Keep pop-x86-oracle inside all other nests of writes.
     (implies (and (not (equal fld :env))
                   (not (equal fld :rip))
                   (not (equal fld :ms)))
              (equal (mv-nth 1 (pop-x86-oracle (xw fld index value x86)))
                     (xw fld index value (mv-nth 1 (pop-x86-oracle x86)))))
     :hints (("Goal" :in-theory (e/d* (pop-x86-oracle
                                       pop-x86-oracle-logic)
                                      ())))))


  )

;; ======================================================================
