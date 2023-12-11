;
; To use the x86-ISA emulator, do:

;  Start ACL2:
;   ~/f/projects/x86-emulator/acl2-x86-boot/saved_acl2

; Load the commands below

(include-book "tools/execution/top")
(defttag :include-raw)
; (include-book "tools/include-raw" :dir :system)
(include-raw "console-raw.lisp")

; The form above will "hang"; then we need to start (in another shell):
;   gnc localhost 6444

(restore-x86 "x86-state.bak" x86)

(b* ((tlb (tlb x86))
     (tlb (make-fast-alist tlb))
     (x86 (!tlb tlb x86)))
    x86)

; And then, start the x86-ISA interpreter

; (x86-run-steps <big-number> x86)

; At the prompt, one may (for instance) type:

;  mount /dev/blkx86isa <mount_point>

; do:  ls -la /bin   to see what commands exist.

; Linux version be used is "alpinelinux.org".  Only taking "rootfs"; that is
; the contents mounted under "/" directly.

; Note, that the commands are provided by "busybox.net"
