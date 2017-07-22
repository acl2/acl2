;;; Copyright (C) 2001, 2003  Eric Marsden
;;; Copyright (C) 2005  David Lichteblau
;;; "the conditions and ENSURE-SSL-FUNCALL are by Jochen Schmidt."
;;;
;;; See LICENSE for details.

;;; We do this in an extra file so that it happens
;;;   - after the asd file has been loaded, so that users can
;;;     customize *libssl-pathname* between loading the asd and LOAD-OPing
;;;     the actual sources
;;;   - before ssl.lisp is loaded, which needs the library at compilation
;;;     time on some implemenations
;;;   - but not every time ffi.lisp is re-loaded as would happen if we
;;;     put this directly into ffi.lisp

#+xcvb (module (:depends-on ("package")))

(in-package :cl+ssl)

;; OpenBSD needs to load libcrypto before libssl
#+openbsd
(progn
  (cffi:define-foreign-library libcrypto
    (:openbsd "libcrypto.so"))
  (cffi:use-foreign-library libcrypto))

(cffi:define-foreign-library libssl
  (:windows (:or "libssl32.dll" "ssleay32.dll"))
  (:darwin (:or "libssl.dylib" "/usr/lib/libssl.dylib"))
  (:solaris (:or "/lib/64/libssl.so"
                 "libssl.so.0.9.8" "libssl.so" "libssl.so.4"))
  ;; Unlike some other systems, OpenBSD linker,
  ;; when passed library name without versions at the end,
  ;; will locate the library with highest macro.minor version,
  ;; so we can just use just "libssl.so".
  ;; More info at https://github.com/cl-plus-ssl/cl-plus-ssl/pull/2.
  (:openbsd "libssl.so")
  ((and :unix (not :cygwin)) (:or "libssl.so.1.0.2"
                                  "libssl.so.1.0.1l"
                                  "libssl.so.1.0.1e"
                                  "libssl.so.1.0.1j"
                                  "libssl.so.1.0.1"
                                  "libssl.so.1.0.0q"
                                  "libssl.so.1.0.0"
                                  "libssl.so.0.9.8ze"
                                  "libssl.so.0.9.8"
                                  "libssl.so"
                                  "libssl.so.4"
                                  "libssl.so.10"))
  (:cygwin "cygssl-1.0.0.dll")
  (t (:default "libssl3")))

(cffi:use-foreign-library libssl)

(cffi:define-foreign-library libeay32
  (:windows "libeay32.dll"))

(cffi:use-foreign-library libeay32)
