(ubt! 1)
(certify-book "top-with-meta")
:u
(certify-book "ordinal-definitions")
:u
(certify-book "ordinal-total-order")
:u
(certify-book "ordinal-basic-thms")
:u
(certify-book "ordinal-addition")
:u
(certify-book "ordinal-multiplication")
:u
(certify-book "ordinal-exponentiation")
:u
(certify-book "limits")
:u
(certify-book "ordinal-isomorphism")
:u
(certify-book "ordinal-counter-examples")
:u
(certify-book "e0-ordinal")
:u
(certify-book "ordinals")
:u
(certify-book "ordinals-without-arithmetic")
:u
(certify-book "lexicographic-ordering")
:u
(defpkg "ORD" (set-difference-eq *acl2-exports*
				 '(o< o<= o-p)))
(certify-book "proof-of-well-foundedness" 1)
:u
:u