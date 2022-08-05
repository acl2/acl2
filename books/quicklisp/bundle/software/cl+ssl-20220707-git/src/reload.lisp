;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) 2001, 2003  Eric Marsden
;;; Copyright (C) 2005  David Lichteblau
;;; "the conditions and ENSURE-SSL-FUNCALL are by Jochen Schmidt."
;;;
;;; See LICENSE for details.

;;; We do this in an extra file so that it happens
;;;   - before ssl.lisp is loaded, which needs the library at compilation
;;;     time on some implemenations
;;;   - but not every time ffi.lisp is re-loaded as would happen if we
;;;     put this directly into ffi.lisp

#+xcvb (module (:depends-on ("package")))

(in-package :cl+ssl)

;; The default OS-X libssl seems have had insufficient crypto algos
;; (missing TLSv1_[1,2]_XXX methods,
;; see https://github.com/cl-plus-ssl/cl-plus-ssl/issues/56)
;; so first try to load possible custom installations of libssl.
;; However, macOS can crash the process if we try to load
;; an unexisting path, see
;; https://github.com/cl-plus-ssl/cl-plus-ssl/issues/138
;; and the discussion in
;; https://github.com/cl-plus-ssl/cl-plus-ssl/issues/114.
;; Therefore we first detect the presence of custom installations,
;; remember them as special *features* flags, which we then use
;; as conditions in the CFFI library definitions.

(defun detect-macos-custom-openssl-installations ()
  (dolist (dir-feature '(("/opt/local/lib/" :cl+ssl-macports-found)
                         ("/sw/lib/" :cl+ssl-fink-found)
                         ("/usr/local/opt/openssl/lib/" :cl+ssl-homebrew-found)
                         ("/opt/homebrew/opt/openssl/lib/" :cl+ssl-homebrew-arm64-found)
                         ("/usr/local/lib/" :cl+ssl-personalized-install-found)))
    (destructuring-bind (dir feature) dir-feature
      (if (and (probe-file (concatenate 'string dir "libssl.dylib"))
               (probe-file (concatenate 'string dir "libcrypto.dylib")))
          (pushnew feature *features*)
          (setf *features* (remove feature *features*))))))

(defun detect-custom-openssl-installations-if-macos ()
  ;; Instead of a read-time conditional we use
  ;; a run-time check, so that it works even
  ;; for compiled code or images built on another
  ;; platform and then reloaded on macOS.
  (when (member :darwin *features*)
    (detect-macos-custom-openssl-installations)))

(detect-custom-openssl-installations-if-macos)

#|

A manual test that I used on Linux for the above
macOS OpenSSL custom installation detection code.

sudo mkdir -p /sw/lib
sudo touch /sw/lib/libssl.dylib /sw/lib/libcrypto.dylib

sudo touch /usr/local/lib/libcrypto.dylib /usr/local/lib/libssl.dylib

(detect-macos-custom-openssl-installations)
(remove-if-not (lambda (f) (search "cl+ssl" (string-downcase f)))
               *features*)

sudo rm -rf /sw/
sudo rm /usr/local/lib/libcrypto.dylib /usr/local/lib/libssl.dylib

|#


;; Windows builds have been naming librypto and libssl DLLs
;; in several different ways:
;;
;; - libeay32.dll, libssl32.dll
;; - libeay32.dll, ssleay32.dll
;;
;; Note, the above names were used both for 32 and 64 -bit versions.
;;
;; - libcrypto-1_1-x64.dll, libssl-1_1-x64.dll
;;
;; The above are used for 64-bit only.
;;
;; - libcrypto-1_1.dll, libssl-1_1.dll
;;
;; These are 32-bit only.

(unless cl+ssl/config::*libcrypto-override*
  (cffi:define-foreign-library libcrypto
    (:windows (:or #+(and windows x86-64) "libcrypto-1_1-x64.dll"
                   #+(and windows x86) "libcrypto-1_1.dll"
                   "libeay32.dll"))
    ;; Unlike some other systems, OpenBSD linker,
    ;; when passed library name without versions at the end,
    ;; will locate the library with highest major.minor version,
    ;; so we can just use just "libssl.so".
    ;; More info at https://github.com/cl-plus-ssl/cl-plus-ssl/pull/2.
    (:openbsd "libcrypto.so")

    ((:and :darwin :cl+ssl-macports-found) "/opt/local/lib/libcrypto.dylib")
    ((:and :darwin :cl+ssl-fink-found) "/sw/lib/libcrypto.dylib")
    ((:and :darwin :cl+ssl-homebrew-found) "/usr/local/opt/openssl/lib/libcrypto.dylib")
    ((:and :darwin :cl+ssl-homebrew-arm64-found) "/opt/homebrew/opt/openssl/lib/libcrypto.dylib")
    ((:and :darwin :cl+ssl-personalized-install-found) "/usr/local/lib/libcrypto.dylib")
    (:darwin (:or ;; System-provided libraries. Must be loaded from files with
                  ;; names that include version explicitly, instead of any
                  ;; versionless symlink file. Otherwise macOS crushes the
                  ;; process (starting from macOS > 10.15 that was just a
                  ;; warning, and finally macOS >= 11 crashes the process with a
                  ;; fatal error) Please note that in macOS >= 11.0, these paths
                  ;; may not exist in the file system anymore, but trying to
                  ;; load them via dlopen will work. This is because macOS ships
                  ;; all system-provided libraries as a single dyld_shared_cache
                  ;; bundle.
                  "/usr/lib/libcrypto.46.dylib"
                  "/usr/lib/libcrypto.44.dylib"
                  "/usr/lib/libcrypto.42.dylib"
                  "/usr/lib/libcrypto.41.dylib"
                  "/usr/lib/libcrypto.35.dylib"

                  ;; The default old system libcrypto, versionless file name,
                  ;; which may have insufficient crypto and can cause process
                  ;; crash on macOS >= 11. Currently we are protected from the
                  ;; crash by the presence of the versioned paths above, but in
                  ;; a few years, when those versions are not available anymore,
                  ;; the crash may re-appear. So eventually we will need to
                  ;; delete the unversioned paths. Keeping them for a while for
                  ;; compatibility. See
                  ;; https://github.com/cl-plus-ssl/cl-plus-ssl/pull/115
                  "libcrypto.dylib"
                  "/usr/lib/libcrypto.dylib"))
    ((and :unix (not :cygwin)) (:or "libcrypto.so.1.1"
                                    "libcrypto.so.1.0.0"
                                    "libcrypto.so.3"
                                    "libcrypto.so"))
    (:cygwin (:or "cygcrypto-1.1.dll" "cygcrypto-1.0.0.dll"))))

(unless cl+ssl/config::*libssl-override*
  (cffi:define-foreign-library libssl
    (:windows (:or #+(and windows x86-64) "libssl-1_1-x64.dll"
                   #+(and windows x86) "libssl-1_1.dll"
                   "libssl32.dll"
                   "ssleay32.dll"))

    ((:and :darwin :cl+ssl-macports-found) "/opt/local/lib/libssl.dylib")
    ((:and :darwin :cl+ssl-fink-found) "/sw/lib/libssl.dylib")
    ((:and :darwin :cl+ssl-homebrew-found) "/usr/local/opt/openssl/lib/libssl.dylib")
    ((:and :darwin :cl+ssl-homebrew-arm64-found) "/opt/homebrew/opt/openssl/lib/libssl.dylib")
    ((:and :darwin :cl+ssl-personalized-install-found) "/usr/local/lib/libssl.dylib")
    (:darwin (:or ;; System-provided libraries, with version in the file name.
                  ;; See the comment for the libcryto equivalents above.
                  "/usr/lib/libssl.48.dylib"
                  "/usr/lib/libssl.46.dylib"
                  "/usr/lib/libssl.44.dylib"
                  "/usr/lib/libssl.43.dylib"
                  "/usr/lib/libssl.35.dylib"

                  ;; Default system libssl, versionless file name.
                  ;; See the coment for the corresponding libcrypto.
                  "libssl.dylib"
                  "/usr/lib/libssl.dylib"))
    (:solaris (:or "/lib/64/libssl.so"
                   "libssl.so.0.9.8" "libssl.so" "libssl.so.4"))
    ;; Unlike some other systems, OpenBSD linker,
    ;; when passed library name without versions at the end,
    ;; will locate the library with highest major.minor version,
    ;; so we can just use just "libssl.so".
    ;; More info at https://github.com/cl-plus-ssl/cl-plus-ssl/pull/2.
    (:openbsd "libssl.so")
    ((and :unix (not :cygwin)) (:or "libssl.so.1.1"
                                    "libssl.so.1.0.2m"
                                    "libssl.so.1.0.2k"
                                    "libssl.so.1.0.2"
                                    "libssl.so.1.0.1l"
                                    "libssl.so.1.0.1j"
                                    "libssl.so.1.0.1f"
                                    "libssl.so.1.0.1e"
                                    "libssl.so.1.0.1"
                                    "libssl.so.1.0.0q"
                                    "libssl.so.1.0.0"
                                    "libssl.so.0.9.8ze"
                                    "libssl.so.0.9.8"
                                    "libssl.so.10"
                                    "libssl.so.4"
                                    "libssl.so.3"
                                    "libssl.so"))
    (:cygwin (:or "cygssl-1.1.dll" "cygssl-1.0.0.dll"))
    (t (:default "libssl3"))))

(unless (member :cl+ssl-foreign-libs-already-loaded
                *features*)
  (cffi:use-foreign-library libcrypto)
  (cffi:use-foreign-library libssl))
