; Event Macros Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defenum" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defenum evmac-input-print-p (nil :error :result :info :all)
  :parents (event-macros)
  :short "Recognize a valid @(':print') input of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee event-macro-screen-printing).")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-input-print-< ((x evmac-input-print-p) (y evmac-input-print-p))
  :parents (evmac-input-print-p)
  :returns (yes/no booleanp)
  :short "Less-than ordering on print levels."
  (case x
    (nil (or (eq y :error)
             (eq y :result)
             (eq y :info)
             (eq y :all)))
    (:error (or (eq y :result)
                (eq y :info)
                (eq y :all)))
    (:result (or (eq y :info)
                 (eq y :all)))
    (:info (eq y :all))
    (:all nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-input-print-<= ((x evmac-input-print-p) (y evmac-input-print-p))
  :parents (evmac-input-print-p)
  :returns (yes/no booleanp)
  :short "Less-than-or-equal-to ordering on print levels."
  (or (evmac-input-print-< x y)
      (equal x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-input-print-> ((x evmac-input-print-p) (y evmac-input-print-p))
  :parents (evmac-input-print-p)
  :returns (yes/no booleanp)
  :short "Greater-than ordering on print levels."
  (evmac-input-print-< y x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-input-print->= ((x evmac-input-print-p) (y evmac-input-print-p))
  :parents (evmac-input-print-p)
  :returns (yes/no booleanp)
  :short "Greater-than-or-equal-to ordering on print levels."
  (evmac-input-print-<= y x))
