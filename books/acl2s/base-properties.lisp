#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

; Any properties that should be in base ACL2s can be added here, as
; long as they aren't needed to build ACL2s.
; 
; At some point, consider moving properties into this file, as the
; property form does more checking than defthm.

(in-package "ACL2S")
(include-book "acl2s/properties" :dir :system :ttags :all)

(property in-over-append (e :all x y :tl)
  (== (in e (append x y))
      (or (in e x) (in e y))))

