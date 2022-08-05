;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) 2021  Tomas Zellerin (zellerin@gmail.com, https://github.com/zellerin)
;;; Copyright (C) 2021  Anton Vodonosov (avodonosov@yandex.ru, https://github.com/avodonosov)
;;;
;;; See LICENSE for details.

(in-package :cl+ssl.test)

(def-suite :cl+ssl.bio :in :cl+ssl
  :description "Bio interface test")

(in-suite :cl+ssl.bio)

(cl+ssl::define-crypto-function ("BIO_write" bio-write)
  :int
  (bio :pointer)
  (text :string)
  (len :int))

(cl+ssl::define-crypto-function ("BIO_read" bio-read)
  :int
  (bio :pointer)
  (text :pointer)
  (len :int))

(cl+ssl::define-crypto-function ("BIO_gets" bio-gets)
  :int
  (bio :pointer)
  (text :pointer)
  (len :int))

(cl+ssl::define-crypto-function ("BIO_puts" bio-puts)
  :int
  (bio :pointer)
  (text :string))

(test bio-read
  (is (equalp
       '("Hel" "lo")
       (cl+ssl::with-bio-input-from-string (bio "Hello")
         (cffi:with-foreign-object (array :char 32)
           (flet ((bio-read-to-string (len)
                    (let ((size (bio-read bio array len)))
                      (assert (< size 31))
                      (setf (cffi:mem-ref array :unsigned-char size) 0)
                      (cffi:foreign-string-to-lisp array))))
             (list
              (bio-read-to-string 3)
              (bio-read-to-string 32))))))))

(test bio-gets
  (cffi:with-foreign-object (array :char 32)
    (is (equalp
         '(6 "Hello
" 3 "bar")
         (cl+ssl::with-bio-input-from-string (bio "Hello
bar")
           (list
            (bio-gets bio array 32)
            (cffi:foreign-string-to-lisp array)
            (bio-gets bio array 32)
            (cffi:foreign-string-to-lisp array)))
         ))

    ;; check that the array is zero terminated
    ;; and thus the max number of chars read is len - 1.
    (setf (cffi:mem-ref array :unsigned-char 4) 7) ; will be replaced by zero terminator
    (is (= 4 (cl+ssl::with-bio-input-from-string (bio "1234567")
               (bio-gets bio array 5))))
    (is (= 0 (cffi:mem-ref array :unsigned-char 4)))

    ;; when the len 0, the return value is 0, and the array is still
    (setf (cffi:mem-ref array :unsigned-char 0) 7) ; will be replaced by zero terminator
    (is (= 0 (cl+ssl::with-bio-input-from-string (bio "zzz")
               (bio-gets bio array 0))))
    (is (= 0 (cffi:mem-ref array :unsigned-char 0)))))

(test bio-write-puts
  (is (equalp
       "Hello Hi
Hallo"
       (cl+ssl::with-bio-output-to-string (bio)
         (bio-write bio  #1="Hello " (length #1#))
         (bio-puts bio "Hi")
         (bio-write bio  #2="Hallo" (length #2#))))))
