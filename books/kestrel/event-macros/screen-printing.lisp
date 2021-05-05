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

(defxdoc event-macro-screen-printing
  :parents (event-macros)
  :short "Screen printing performed by event macros."
  :long
  (xdoc::topstring
   (xdoc::p
    "Event macros normally print messages on then screen when they run.
     At a minimum, they should print error messages,
     e.g. when user inputs do not pass validation.
     Event macros are run to produce "
    (xdoc::seetopic "event-macro-results" "results")
    ", namely events and sometimes files,
     which should be typically printed on the screen
     to confirm that the event macro has done its job,
     and also to inform the user of some details of the results.
     Sometimes it is useful to have event macros
     print additional information as they run,
     about their internal operation,
     e.g. to help debug when they do not seem to behave as expected.
     Furthermore, a user may sometimes want to see
     the complete output produced by ACL2 in response to
     the events produced by an event macro,
     not just the external (i.e. exported) events,
     but also the internal (i.e. local) events.
     In certain cases, a user may want to suppress all screen output,
     including any error messages.")
   (xdoc::p
    "The above discussion suggests five ordered levels of screen printing,
     specified by the @(':print') input of
     the event macros that adhere to this convention,
     i.e. the event macros whose user documentation references this manual page.
     The ordered printing levels,
     which are the possible values of the @(':print') input,
     are")
   (xdoc::codeblock
    "nil < :error < :result < :info < :all")
   (xdoc::p
    "where the amount of printed material increases monotonically.")
   (xdoc::p
    "When @(':print') is @('nil'),
     nothing is printed (not even errors).")
   (xdoc::p
    "When @(':print') is @(':error'),
     only errors (if any) are printed.")
   (xdoc::p
    "When @(':print') is @(':result'),
     besides errors (if any),
     also the "
    (xdoc::seetopic "event-macro-results" "results")
    " of the event macro are printed,
     as described in the manual page just referenced.")
   (xdoc::p
    "When @(':print') is @(':info'),
     besides errors (if any) and results,
     also some additional information about the event macro's operation
     is printed.")
   (xdoc::p
    "When @(':print') is @(':all'),
     besides errors (if any), results, and additional information,
     also all the ACL2 output in response to the submitted events is printed")))

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
