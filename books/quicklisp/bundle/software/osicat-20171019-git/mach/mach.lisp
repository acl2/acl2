;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; mach.lisp --- Low-level interface to the Mach API.
;;;
;;; Copyright (c) 2007, Luis Oliveira  <loliveira@common-lisp.net>
;;;
;;; Permission is hereby granted, free of charge, to any person
;;; obtaining a copy of this software and associated documentation
;;; files (the "Software"), to deal in the Software without
;;; restriction, including without limitation the rights to use, copy,
;;; modify, merge, publish, distribute, sublicense, and/or sell copies
;;; of the Software, and to permit persons to whom the Software is
;;; furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be
;;; included in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;; NONINFRINGEMENT.  IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;; WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;; DEALINGS IN THE SOFTWARE.

(in-package #:osicat-mach)

(defctype kern-return :int)
(defctype clock-res :int)
(defctype clock-id :int)
(defctype port :unsigned-int) ; not sure
(defctype clock-serv port)

(defconstant kern-success 0)

(defconstant system-clock 0)
(defconstant calendar-clock 1)
(defconstant realtime-clock 0)

(defcstruct timespec
  (tv-sec :unsigned-int)
  (tv-nsec clock-res))

(defcfun "mach_host_self" port)

(defcfun ("host_get_clock_service" %host-get-clock-service) kern-return
  (host port)
  (id clock-id)
  (clock-name (:pointer clock-serv)))

(defun host-get-clock-service (id &optional (host (mach-host-self)))
  (with-foreign-object (clock 'clock-serv)
    (%host-get-clock-service host id clock)
    (mem-ref clock :int)))

(defcfun ("clock_get_time" %clock-get-time) kern-return
  (clock-serv clock-serv)
  (cur-time timespec))

(defun clock-get-time (clock-service)
  (with-foreign-object (time 'timespec)
    (%clock-get-time clock-service time)
    (with-foreign-slots ((tv-sec tv-nsec) time timespec)
      (values tv-sec tv-nsec))))
