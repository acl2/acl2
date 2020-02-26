; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ input-processors
  :parents (utilities)
  :short "Utilities to process inputs
          that are common to multiple APT transformations."
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-new-name (new-name (old symbolp) ctx state)
  :returns (mv erp (new-name$ "A @(tsee symbolp).") state)
  :mode :program
  :short "Process the @(':new-name') input of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(':new-name') input of an APT transformations must be
     either @(':auto') or another (non-keyword) symbol.
     In the first case, the name of the new function
     is obtained from the name of the old function (in the argument @('old')),
     by incrementing its (explicit or implicit) numbered name index.
     In the second case, the name of the new function
     is the directly specified symbol,
     which must therefore be a valid name for a new function."))
  (b* (((er &) (ensure-symbol$ new-name "The :NEW-NAME input" t nil))
       (new-name (case new-name
                   (:auto (next-numbered-name old (w state)))
                   (t new-name)))
       (description (msg "The name ~x0 of the new function, ~@1,"
                         new-name
                         (if (eq new-name :auto)
                             "automatically generated ~
                              since the :NEW-NAME input ~
                              is (perhaps by default) :AUTO"
                           "supplied as the :NEW-NAME input")))
       ((er &) (ensure-symbol-new-event-name$ new-name description t nil)))
    (value new-name)))
