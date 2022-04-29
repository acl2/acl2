; Tools for processing parsed executables
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "mach-o-tools")
(include-book "pe-tools")

(defund parsed-executable-type (parsed-executable)
  (if (equal '(:MAGIC . :MH_MAGIC_64)
             (assoc-eq :magic parsed-executable))
      :mach-o-64
    (if (equal '(:MAGIC . :MH_MAGIC)
               (assoc-eq :magic parsed-executable))
        :mach-o-32
      (if (assoc-eq :MS-DOS-STUB parsed-executable)
          (let* ((coff-file-header (lookup-eq-safe :COFF-FILE-HEADER parsed-executable))
                 (machine-type (lookup-eq-safe :machine coff-file-header)))
            (if (eq machine-type :IMAGE_FILE_MACHINE_I386)
                :pe-32
              (if (eq machine-type :IMAGE_FILE_MACHINE_AMD64)
                  :pe-64
                (er hard 'parsed-executable-type
                    "Unknown PE executable type: ~x0" machine-type))))
        (er hard? 'parsed-executable-type
            "Unknown executable type.  Magic is: ~x0"
            (assoc-eq :magic parsed-executable))))))

;; Throws an error if SUBROUTINE-NAME is not found in PARSED-EXECUTABLE
;; todo: move out of this file since not just for 64-bit?
(defund ensure-target-exists-in-executable (subroutine-name
                                            parsed-executable)
  (let ((executable-type (parsed-executable-type parsed-executable)))
    (case executable-type
      ((:mach-o-64 :mach-o-32) (subroutine-address-mach-o subroutine-name parsed-executable)) ; throws an error if not found
      (:pe-64 (acl2::subroutine-address-within-text-section-pe-64 subroutine-name parsed-executable))
      (:pe-32 (acl2::subroutine-offset-pe-32 subroutine-name parsed-executable) ; throws an error if not found
              )
      (t (er hard? 'ensure-target-exists-in-executable "Unknown executable type: ~x0." executable-type)))))
