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

;; A parsed executable (must be either ELF, MACH-O, or PE)
(defund parsed-executablep (e)
  (declare (xargs :guard t))
  (or (parsed-elfp e)
      (parsed-mach-o-p e)
      (parsed-pe-p e)))

;; Returns one of :elf-32, :elf-64, :mach-o-32, :mach-o-64, :pe-32, or :pe-64
;; (or throws an error).
;; todo: guard proof
(defund parsed-executable-type (parsed-executable)
  (declare (xargs :guard (parsed-executablep parsed-executable)))
  (let ((executable-type (lookup-eq :executable-type parsed-executable))) ; valid for all 3 kinds of executable
    (if (member-eq executable-type '(:elf-32 :elf-64 :mach-o-32 :mach-o-64 :pe-32 :pe-64))
        executable-type
      (prog2$ (er hard? 'parsed-executable-type "Unknown/unsupported executable type: ~x0" executable-type)
              executable-type))))

(defthm parsed-elfp-when-parsed-executablep
  (implies (parsed-executablep parsed-executable)
           (iff (parsed-elfp parsed-executable)
                (member-equal (parsed-executable-type parsed-executable) '(:elf-32 :elf-64))))
  :hints (("Goal" :in-theory (enable parsed-executablep parsed-elfp parsed-executable-type parsed-mach-o-p parsed-pe-p))))

(defthm parsed-mach-o-p-when-parsed-executablep
  (implies (parsed-executablep parsed-executable)
           (iff (parsed-mach-o-p parsed-executable)
                (member-equal (parsed-executable-type parsed-executable) '(:mach-o-32 :mach-o-64))))
  :hints (("Goal" :in-theory (enable parsed-executablep parsed-elfp parsed-executable-type parsed-mach-o-p parsed-pe-p))))

(defthm parsed-pe-p-when-parsed-executablep
  (implies (parsed-executablep parsed-executable)
           (iff (parsed-pe-p parsed-executable)
                (member-equal (parsed-executable-type parsed-executable) '(:pe-32 :pe-64 :pe-unknown))))
  :hints (("Goal" :in-theory (enable parsed-executablep parsed-elfp parsed-executable-type parsed-mach-o-p parsed-pe-p))))


;; Throws an error if SUBROUTINE-NAME is not found in PARSED-EXECUTABLE
(defund ensure-target-exists-in-executable (subroutine-name
                                            parsed-executable)
  (declare (xargs :guard (and (stringp subroutine-name)
                              (parsed-executablep parsed-executable))))
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
  (declare (xargs :guard (parsed-executablep parsed-executable)))
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
        (if (member-eq executable-type '(:pe-32 :pe-64))
            (let ((cpu-type (pe-cpu-type parsed-executable)))
              (if (not (member-eq cpu-type '(:IMAGE_FILE_MACHINE_I386 :IMAGE_FILE_MACHINE_AMD64)))
                  (er hard? 'ensure-x86 "Non-x86 executable detected.  CPU type is ~x0" cpu-type)
                nil))
          (er hard? 'ensure-x86 "Unknown kind of executable detected: ~x0" executable-type))))))

(defund ensure-risc-v (parsed-executable)
  (declare (xargs :guard (parsed-executablep parsed-executable)))
  (let ((executable-type (parsed-executable-type parsed-executable)))
    (if (not (eq executable-type :elf-32))
        ;; todo: handle :elf-64 and maybe other executable-types
        (er hard? 'ensure-risc-v "Non-ELF-32 executable detected.  Executable type is ~x0" executable-type)
      (let ((cpu-type (parsed-elf-cpu-type parsed-executable)))
        (if (not (eq :em_riscv cpu-type))
            (er hard? 'ensure-risc-v "Non-RISC-V executable detected.  CPU type is ~x0" cpu-type)
          nil)))))
