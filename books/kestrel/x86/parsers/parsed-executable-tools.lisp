; Tools for processing parsed executables
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "mach-o-tools")
(include-book "pe-tools")

(defun parsed-executable-type (parsed-executable)
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
        (er hard 'parsed-executable-type
            "Unknown executable type.  Magic is: ~x0"
            (assoc-eq :magic parsed-executable))))))
