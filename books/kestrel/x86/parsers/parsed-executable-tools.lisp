; Tools for processing parsed executables
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: add and verify guards

(include-book "elf-tools")
(include-book "mach-o-tools")
(include-book "pe-tools")

;; Returns one of :elf-32, :elf-64, :mach-o-32, :mach-o-64, :pe-32, or :pe-64
;; (or throws an error).
(defund parsed-executable-type (parsed-executable)
  (let ((magic (lookup-eq :magic parsed-executable)))
    (if (member-eq magic '(:elf-32 :elf-64))
        magic
      (if (eq :MH_MAGIC magic)
          :mach-o-32
        (if (eq :MH_MAGIC_64 magic)
            :mach-o-64
          (if (assoc-eq :MS-DOS-STUB parsed-executable)
              (let* ((coff-file-header (lookup-eq-safe :COFF-FILE-HEADER parsed-executable))
                     (machine-type (lookup-eq-safe :machine coff-file-header)))
                (if (eq machine-type :IMAGE_FILE_MACHINE_I386)
                    :pe-32
                  (if (eq machine-type :IMAGE_FILE_MACHINE_AMD64)
                      :pe-64
                    (er hard 'parsed-executable-type
                        "Unknown PE executable type: ~x0" machine-type))))
            (er hard? 'parsed-executable-type "Unknown executable type.  Magic is: ~x0" magic)))))))

;; Throws an error if SUBROUTINE-NAME is not found in PARSED-EXECUTABLE
(defund ensure-target-exists-in-executable (subroutine-name
                                            parsed-executable)
  (let ((executable-type (parsed-executable-type parsed-executable)))
    (case executable-type
      ((:mach-o-64 :mach-o-32) (subroutine-address-mach-o subroutine-name parsed-executable)) ; throws an error if not found
      ((:elf-64 :elf-32) (subroutine-address-elf subroutine-name parsed-executable)) ; throws an error if not found
      (:pe-64 (acl2::subroutine-address-within-text-section-pe-64 subroutine-name parsed-executable))
      (:pe-32 (acl2::subroutine-offset-pe-32 subroutine-name parsed-executable) ; throws an error if not found
              )
      (t (er hard? 'ensure-target-exists-in-executable "Unknown executable type: ~x0." executable-type)))))

; Throws an error if the executable is not an x86 executable.
(defund ensure-x86 (parsed-executable)
  (let ((executable-type (parsed-executable-type parsed-executable)))
    (if (member-eq executable-type '(:mach-o-32 :mach-o-64))
        (let ((cpu-type (mach-o-cpu-type parsed-executable)))
          (if (not (member-eq cpu-type '(:CPU_TYPE_X86 :CPU_TYPE_X86_64)))
              (er hard? 'ensure-x86 "Non-x86 executable detected.  CPU type is ~x0" cpu-type)
            nil))
      (if (member-eq executable-type '(:elf-32 :elf-64))
          (let ((cpu-type (parsed-elf-cpu-type parsed-executable)))
            (if (not (member-eq cpu-type '(:EM_386 :EM_X86_64)))
                (er hard? 'ensure-x86 "Non-x86 executable detected.  CPU type is ~x0" cpu-type)
              nil))
        ;; must be a PE:
        (let ((cpu-type (pe-cpu-type parsed-executable)))
            (if (not (member-eq cpu-type '(:IMAGE_FILE_MACHINE_I386 :IMAGE_FILE_MACHINE_AMD64)))
                (er hard? 'ensure-x86 "Non-x86 executable detected.  CPU type is ~x0" cpu-type)
              nil))))))
