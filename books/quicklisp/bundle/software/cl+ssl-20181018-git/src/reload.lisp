;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
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

(cffi:define-foreign-library libcrypto
  (:openbsd "libcrypto.so")
  (:darwin (:or "/opt/local/lib/libcrypto.dylib" ;; MacPorts
                "/sw/lib/libcrypto.dylib"        ;; Fink
                "/usr/local/opt/openssl/lib/libcrypto.dylib" ;; Homebrew
                "/usr/local/lib/libcrypto.dylib" ;; personalized install
                "libcrypto.dylib"                ;; default system libcrypto, which may have insufficient crypto
                "/usr/lib/libcrypto.dylib")))

(cffi:define-foreign-library libssl
  (:windows (:or "libssl32.dll" "ssleay32.dll"))
  ;; The default OS-X libssl seems have had insufficient crypto algos
  ;; (missing TLSv1_[1,2]_XXX methods,
  ;; see https://github.com/cl-plus-ssl/cl-plus-ssl/issues/56)
  ;; so first try to load possible custom installations of libssl
  (:darwin (:or "/opt/local/lib/libssl.dylib" ;; MacPorts
                "/sw/lib/libssl.dylib"        ;; Fink
                "/usr/local/opt/openssl/lib/libssl.dylib" ;; Homebrew
                "/usr/local/lib/libssl.dylib" ;; personalized install
                "libssl.dylib"                ;; default system libssl, which may have insufficient crypto
                "/usr/lib/libssl.dylib"))
  (:solaris (:or "/lib/64/libssl.so"
                 "libssl.so.0.9.8" "libssl.so" "libssl.so.4"))
  ;; Unlike some other systems, OpenBSD linker,
  ;; when passed library name without versions at the end,
  ;; will locate the library with highest macro.minor version,
  ;; so we can just use just "libssl.so".
  ;; More info at https://github.com/cl-plus-ssl/cl-plus-ssl/pull/2.
  (:openbsd "libssl.so")
  ((and :unix (not :cygwin)) (:or "libssl.so.1.0.2m"
                                  "libssl.so.1.0.2k"
                                  "libssl.so.1.0.2"
                                  "libssl.so.1.0.1l"
                                  "libssl.so.1.0.1j"
                                  "libssl.so.1.0.1e"
                                  "libssl.so.1.0.1"
                                  "libssl.so.1.0.0q"
                                  "libssl.so.1.0.0"
                                  "libssl.so.0.9.8ze"
                                  "libssl.so.0.9.8"
                                  "libssl.so.10"
                                  "libssl.so.4"
                                  "libssl.so"))
  (:cygwin "cygssl-1.0.0.dll")
  (t (:default "libssl3")))

(cffi:define-foreign-library libeay32
  (:windows "libeay32.dll"))


(unless (member :cl+ssl-foreign-libs-already-loaded
                *features*)
  (cffi:use-foreign-library libcrypto)
  (cffi:use-foreign-library libssl)
  (cffi:use-foreign-library libeay32))
