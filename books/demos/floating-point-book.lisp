(in-package "ACL2")
(assert-event
(identical-files-p "floating-point-log.txt" "floating-point-log.out"))

; As of this writing we have tested in CCL, SBCL, and LispWorks.  The CCL and
; SBCL tests passed, and the LispWorks tests would have passed except for
; slight discrepancies in floating-point values (see multi-line comment below),
; which is not unexpected.  Because of those discrepancies, the diff failed
; between floating-point-log.txt and floating-point-log.out.  It seems safest
; to exclude not only LispWorks but also Allegro CL, CMUCL, and GCL, since
; those three are not frequently tested.

; cert_param: (non-lispworks, non-allegro, non-cmucl, non-gcl)

; Values that differered for LispWorks shown from the generated
; floating-point-log.out:
#|
ACL2 !>>(RIZE *2PI*)
491701844/78256779

ACL2 !>>(DF-SIN (DF-2PI))
#d-2.4492127076447545E-16

ACL2 !>>(DF-RATIONALIZE (DF-SIN (DF-2PI)))
-1/4082944682095961

ACL2 !>>(DF-SIN *2PI*)
#d-2.4492127076447545E-16

ACL2 !>>(DF-SIN *PI/6*)
#d0.49999999999999995

ACL2 !>>(DF-RATIONALIZE (DF-SIN *PI/6*))
4503599627370495/9007199254740991

ACL2 !>>(DF-SQRT 2)
#d1.4142135623730952

ACL2 !>>(DF* (DF-SQRT 2) (DF-SQRT 2))
#d2.0000000000000005
|#
