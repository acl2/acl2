#|
(certify-book "symbols" 0)
|#

;; Sun Dec 21 02:00:42 2003

(in-package "ACL2")

; Define symbols that will be shared among BCV, DJVM, M6

(defconst *jvm-symbols*
  '(class 
    field 
    int 
    long 
    float 
    double 
    string 
    array 
    frame
    null 
    reference 
    oneword 
    twoword 
    topx  ;; we will use this?? Sat May 21 19:42:28 2005. 
    void  ;; Sat May 21 19:44:07 2005. Let me use it!! 
    ;; value used in the BCV to represent unknown type 
    ;; there are type checking rules associated with it. 
    ;; top definition. 
    
    *interface*
    locals 
    stack 
    flags
    uninitialized 
    uninitializedThis
    ))

;;; Expect constant update. 
