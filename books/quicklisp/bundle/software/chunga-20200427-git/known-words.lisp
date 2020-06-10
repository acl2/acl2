;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: CHUNGA; Base: 10 -*-
;;; $Header: /usr/local/cvsrep/chunga/known-words.lisp,v 1.3 2008/05/29 22:21:09 edi Exp $

;;; Copyright (c) 2006-2010, Dr. Edmund Weitz.  All rights reserved.

;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:

;;;   * Redistributions of source code must retain the above copyright
;;;     notice, this list of conditions and the following disclaimer.

;;;   * Redistributions in binary form must reproduce the above
;;;     copyright notice, this list of conditions and the following
;;;     disclaimer in the documentation and/or other materials
;;;     provided with the distribution.

;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
;;; OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
;;; DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
;;; GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

(in-package :chunga)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (define-constant +known-words+
    '(;; headers including WebDAV and some de facto standard headers
      "Accept"
      "Accept-Charset"
      "Accept-Encoding"
      "Accept-Language"
      "Accept-Ranges"
      "Age"
      "Allow"
      "Authorization"
      "Cache-Control"
      "Connection"
      "Content-Encoding"
      "Content-Language"
      "Content-Length"
      "Content-Location"
      "Content-MD5"
      "Content-Range"
      "Content-Type"
      "DAV"
      "Date"
      "Depth"
      "Destination"
      "ETag"
      "Expect"
      "Expires"
      "From"
      "Host"
      "If"
      "If-Match"
      "If-Modified-Since"
      "If-None-Match"
      "If-Range"
      "If-Unmodified-Since"
      "Last-Modified"
      "Location"
      "Lock-Token"
      "Max-Forwards"
      "Overwrite"
      "Pragma"
      "Proxy-Authenticate"
      "Proxy-Authorization"
      "Range"
      "Referer"
      "Retry-After"
      "Server"
      "TE"
      "TimeOut"
      "Trailer"
      "Transfer-Encoding"
      "Upgrade"
      "User-Agent"
      "Vary"
      "Via"
      "WWW-Authenticate"
      "Warning"
      ;; methods including WebDAV
      "CONNECT"
      "COPY"
      "DELETE"
      "GET"
      "HEAD"
      "LOCK"
      "MKCOL"
      "MOVE"
      "OPTIONS"
      "POST"
      "PROPFIND"
      "PROPPATCH"
      "PUT"
      "TRACE"
      "UNLOCK"
      ;; protocols
      "HTTP/1.1"
      "HTTP/1.0"
      ;; only a few and only the "preferred MIME names" - see
      ;; <http://www.iana.org/assignments/character-sets> for a
      ;; complete list
      "US-ASCII"
      "ISO-8859-1"
      "UTF-8"
      "UTF-16"
      "UTF-32BE"
      "UTF-32LE")
    "A list of words \(headers, methods, protocols, character sets)
that are typically seen in HTTP communication.  Mostly from RFC 2616,
but includes WebDAV stuff and other things as well."))

(define-constant +string-to-keyword-hash+
  (let ((hash (make-hash-table :test 'equal :size (length +known-words+))))
    (loop for word in +known-words+
          do (setf (gethash word hash) (make-keyword word nil)))
    hash)
  "A hash table which case-insensitively maps the strings from
+KNOWN-WORDS+ to keywords.")

(define-constant +keyword-to-string-hash+
  (let ((hash (make-hash-table :test 'eq :size (length +known-words+))))
    (loop for word in +known-words+
          do (setf (gethash (make-keyword word nil) hash)
                   (string-capitalize word)))
    hash)
  "A hash table which maps keywords derived from +KNOWN-WORDS+ to
capitalized strings.")

(defun as-keyword (string &key (destructivep t))
  "Converts the string STRING to a keyword where all characters are
uppercase or lowercase, taking into account the current readtable
case.  Might destructively modify STRING if DESTRUCTIVEP is true which
is the default.  \"Knows\" several HTTP header names and methods and
is optimized to not call INTERN for these."
  (or (gethash string +string-to-keyword-hash+)
      (make-keyword string destructivep)))

(defun as-capitalized-string (keyword)
  "Kind of the inverse of AS-KEYWORD.  Has essentially the same effect
as STRING-CAPITALIZE but is optimized for \"known\" keywords like
:CONTENT-LENGTH or :GET."
  (or (gethash keyword +keyword-to-string-hash+)
      (string-capitalize keyword)))
