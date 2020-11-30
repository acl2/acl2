; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc event-macro-results
  :parents (event-macros)
  :short "Results of event macros."
  :long
  (xdoc::topstring
   (xdoc::p
    "Many event macros generate events in the ACL2 @(see world).
     Some event macros may also generate files,
     e.g. macros that generate code in other programming languages from ACL2.
     We refer to these generated events, and possibly files,
     as results of the event macro.")
   (xdoc::p
    "This nomenclature is particular relevant to
     the screen printing performed by the event macros:
     see @(tsee evmac-input-print-p).
     When the @(':print') option is @(':result') or higher,
     generated events are normally printed on screen as Lisp forms.
     However, in some cases only their names and short descriptions are printed
     (e.g. when they are large and thus not necessarily useful
     to see in their entirety every time,
     or when they have a regular predictable structure);
     in these cases, the Lisp forms can be seen, if desired,
     by querying the ACL2 @(see world) (e.g. with @(tsee pe)).
     When an event macro generates files
     and @(':print') is @(':result') or higher,
     the file paths are normally printed, but not the file contents,
     which can be seen by opening the files.")))
