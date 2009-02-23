(in-package "STR")

(defun stringp (x)
  (declare (xargs :guard t))
  (or (acl2::stringp x)
      (and (consp x)
           (eq (car x) 'rstring)
           (character-listp (cdr x)))
      (character-listp x)))

(defun rstringp (x)
  (declare (xargs :guard (stringp x)))
  (and (consp x)
       (eq (car x) 'rstring)))

(defun acl2chars (x)
  (declare (xargs :guard (stringp x)))
  (cond ((acl2::stringp x)
         (coerce x 'list))
        ((rstringp x)
         (acl2::reverse (cdr x)))
        (t
         x)))

(defun acl2string (x)
  (declare (xargs :guard (stringp x)))
  (mbe :logic (coerce (acl2chars x) 'string)
       :exec
       (cond ((acl2::stringp x)
              x)
             ((rstringp x)
              (coerce (acl2::reverse (cdr x)) 'string))
             (t
              (coerce x 'string)))))



        
      
 