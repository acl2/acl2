; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "decimal-integer-literals")
(include-book "hexadecimal-integer-literals")
(include-book "octal-integer-literals")
(include-book "binary-integer-literals")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ integer-literals
  :parents (syntax)
  :short "Java integer literals [JLS:3.10.1]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum integer-literal
  :short "Fixtype of integer literals."
  (:hex ((get hex-integer-literal)))
  (:dec ((get dec-integer-literal)))
  (:oct ((get oct-integer-literal)))
  (:bin ((get bin-integer-literal))))
