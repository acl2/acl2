(include-book "tools/execution/top")
(init-sys-view #x10000000 x86)
(linux-load "../../../../bzImage" "../../../../alpine-root.img" "rootfstype=ramfs console=ttyx86isa ignore_loglevel root=/dev/ram0 init=/bin/bash" x86 state)
