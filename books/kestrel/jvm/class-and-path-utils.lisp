; Utilities for class hierarchies
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ;todo use jvm

(include-book "kestrel/jvm/classes" :dir :system)

(defthmd stringp-when-class-namep
  (implies (jvm::class-namep name)
           (stringp name)))

(local (in-theory (enable stringp-when-class-namep)))

(defund package-of-class-name (fully-qualified-class-name)
  (declare (xargs :guard (stringp fully-qualified-class-name)))
  (if (< 0 (count #\. fully-qualified-class-name))
      (substring-before-last-occurrence fully-qualified-class-name #\.)
    ""))

(defthm stringp-of-package-of-class-name
  (stringp (package-of-class-name fully-qualified-class-name))
  :hints (("Goal" :in-theory (enable package-of-class-name))))

(defund turn-dots-into-slashes (str)
  (declare (xargs :guard (stringp str)))
  (substitute #\/ #\. str))

(defthm stringp-of-turn-dots-into-slashes
  (implies (stringp str)
           (stringp (turn-dots-into-slashes str)))
  :hints (("Goal" :in-theory (enable turn-dots-into-slashes))))

(defund unqualified-class-name (fully-qualified-class-name)
  (declare (xargs :guard (stringp fully-qualified-class-name)))
  (if (< 0 (count #\. fully-qualified-class-name))
      (mv-let (first rest)
        (read-string-to-last-terminator fully-qualified-class-name #\.)
        (declare (ignore first))
        rest)
    ;; No dots, so the whole thing is the unqualified name
    fully-qualified-class-name))

;todo
(defthm class-namep-of-unqualified-class-name
  (implies (jvm::class-namep name)
           (jvm::class-namep (unqualified-class-name name)))
  :hints (("Goal" :in-theory (enable unqualified-class-name jvm::class-namep))))

(defund path-of-class-file-within-dir (fully-qualified-class-name)
  (declare (xargs :guard (jvm::class-namep fully-qualified-class-name)
;                  :verify-guards nil ;todo
                  ))
  (let* ((unqualified-class-name (unqualified-class-name fully-qualified-class-name))
         (package-name (package-of-class-name fully-qualified-class-name)))
    (if (equal "" package-name)
        (concatenate 'string
                     unqualified-class-name
                     ".class")
      (concatenate 'string
                   (turn-dots-into-slashes package-name)
                   "/"
                   unqualified-class-name
                   ".class"))))
