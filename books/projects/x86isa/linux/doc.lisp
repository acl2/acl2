; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2024 Intel Corporation
; Copyright (C) 2024 Yahya Sohail

; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Yahya Sohail        <yahya@yahyasohail.com>

(in-package "X86ISA")

(include-book "xdoc/top" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(make-event
  `(defconst *linux-artifacts-checksums*
             ,(read-file-into-string "artifacts.sha512")))

(make-event
  `(defconst *linux-init-script*
             ,(read-file-into-string "init")))

(defxdoc running-linux
         :parents (x86isa)
         :short "Running Linux on the @('x86isa') model."

         :long
         (xdoc::topstring
           "<p>The x86isa model is capable of running a slightly modified
           version of Linux. This version of Linux is modified to add support for
           our timer and TTY devices and a few other minor changes.</p>

           <p>To run Linux, you need to certify the books, as described in @(see
           x86isa-build-instructions). If you wish to interact with the model over a TCP
           socket, you need to use ACL2 built with Clozure Common Lisp (CCL). You
           must also obtain a Linux kernel image and a rootfs (root filesystem)
           image. We provide instructions to build your own in @(see
           building-linux) and @(see building-rootfs) and provide images
           available to download <a
           href=\"http://www.cs.utexas.edu/users/hunt/x86-ISA/linux\">here</a>
           with the following SHA512 checksums (available at
           @('books/projects/x86isa/linux/artifacts.sha512') in the ACL2 source
           tree):</p>"

           (xdoc::@{} *linux-artifacts-checksums*)

           "<p>The provided @('bzImage') is the kernel in Linux's bzImage format,
           which is what we'll use to boot. @('vmlinux') is the kernel provided
           in ELF format, which isn't used to boot, but useful for debugging. We
           provide two rootfs images, @('alpine.img'), which contains Alpine
           Linux's rootfs with just the software that comes with Alpine Linux and
           @('alpine-gcc.img'), which is Alpine Linux's rootfs with GCC
           installed.</p>

           <p>While it isn't required, we recommend using the @(tsee
           bigmem-asymmetric::bigmem-asymmetric) memory model because it gives
           better performance. See @(tsee physical-memory-model). You can
           execute the following in ACL2, before doing anything else, to
           switch:</p>

           @({
              (include-book \"centaur/bigmems/bigmem-asymmetric/bigmem-asymmetric\" :dir :system)
              (attach-stobj bigmem::mem bigmem-asymmetric::mem)
           })

           <p>To load Linux, run the following in an ACL2 session (assuming
           you're in the @('books/projects/x86isa') directory in the ACL2
           source tree):</p>
           <code>
           (include-book \"tools/execution/top\")
           ;; This writes out some identity mapped page tables
           (init-sys-view #xF0000000 x86)
           ;; Enable peripherals and exception handling
           (!enable-peripherals t x86)
           (!handle-exceptions t x86)
           ;; This function serves as our bootloader
           (linux-load \"&lt;path to kernel bzImage&gt;\"
                       \"&lt;path to rootfs archive&gt;\"
                       ;; The following is the kernel command line. Unless you
                       ;; know what you're doing, you don't have much reason to
                       ;; touch this
                       \"rootfstype=ramfs console=ttyprintk ignore_loglevel root=/dev/ram0\" x86
                       state)
           </code>

           <p>This will load Linux into the model. Optionally, if you wish to be
           able to interact with a shell on the machine over a TCP socket, you can
           run:</p>
           <code>
           (defttag :tty-raw)
           (include-raw \"machine/tty-raw.lsp\")
           </code>
           <p>After submitting the second form, the ACL2 session will hang. At
           this point you can connect to localhost on TCP port 6444 using socat.
           Execute the following in a shell:</p>
           <code>
           socat file:`tty`,rawer tcp-connect:localhost:6444
           </code>
           <p>Once you connect, ACL2 should continue. Note: this utility only
           works in CCL and is unsound. Don't include it in proofs.</p>

           <p>Now, all you have to do is start execution. Submit the following form to ACL2:</p>
           <code>
           (x86-run-steps &lt;n&gt; x86)
           </code>
           <p>This will tell ACL2 to execute @('<n>') instructions. Booting Linux
           takes on the order of 600 million instructions. I usually just put in
           some large number (though you probably want to keep it a fixnum).</p>

           <p>As Linux boots, you should see the kernel log being printed in ACL2.
           Eventually, once Linux is done starting, it'll start @('/init'). The
           stdout of @('/init') will be printed to the kernel log. If you're using
           @('tty-raw.lsp'), you'll be able to interact with it over the
           socket.</p>

           <p>The modified Linux kernel has support for a block device called
           @('blkx86isa'). This device is essentially a view into the gigabyte of
           physical memory at address @('0x100000000'). This could be useful for
           transfering files into and out of the Linux system running in the
           model. You can mount it like any other drive on a Linux system.</p>"))

(defxdoc building-linux
         :parents (running-linux)
         :short "How to build a patched Linux kernel for the x86isa model."

         :long "<p>The @('x86isa') model is capable of booting a slightly
         modified Linux kernel, which includes modifications to add support for
         our @(see timer) and @(see tty) and removes Linux's dependence on
         unimplemented peripherals. Here we describe how to obtain a copy of
         the Linux source, patch it, and build the kernel. We assume you're
         using a Linux system with a \"Linux-style\" file system.</p>

         <p>First, we obtain the Linux source via @('git'). Execute the
         following in a terminal:</p>
         <code>
         git clone https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git
         cd linux
         </code>

         <p>This will clone the Linux source tree into a folder called
         @('linux') in your current working directory and then @('cd') into it.
         Our patch was tested on version @('v6.12'), so we'll checkout that
         version:</p>
         <code>
         git checkout v6.12
         </code>

         <p>Now, we need to patch the kernel. We include the patch at
         @('books/projects/x86isa/linux/x86isa-linux.patch') in the ACL2 source
         tree. To apply it run</p>
         @({
         git am <path to patch>
         })
         <p>in your copy of the linux source, substituting @('<path to patch>')
         for the path to the given @('x86isa-linux.patch') file.</p>

         <p>Normally, at this point you'd run @('make menuconfig') to configure
         the kernel for your machine, but we included a @('.config') file in
         the patch that configures the kernel to work with the @('x86isa')
         model, so you don't need to worry too much about the config. However,
         run</p>
         <code>
         make olddefconfig
         </code>
         <p>to update the config with details dependent on your compiler</p>

         <p>Finally, we can compile the kernel. Run:</p>
         <code>
         make
         </code>

         <p>Using multiple cores can increase build speed. Use</p>
         <code>
         make -j
         </code>
         <p>or</p>
         <code>
         make -j&lt;nprocs&gt;
         </code>
         <p>to use as many threads as you have logical processors or
         @('<nprocs>') threads to build respectively.</p>

         <p>This will build a @('bzImage') in @('arch/x86/boot/bzImage'), which
         is the kernel in Linux's bzImage format. This is the file we will load
         into the model. It also produces a @('vmlinux') file in the root of
         the Linux source tree, which contains the kernel in ELF format. While
         this isn't used to boot, it can be useful when debugging.</p>")

(defxdoc building-rootfs
         :parents (running-linux)
         :short "How to build a rootfs (root filesystem) image for running
                 Linux on the x86isa model."

         :long
         (xdoc::topstring
           "<p>Most modern Linux machines boot by first loading an initramfs as
         the file system mounted on @('/'). This, as the name suggests, is an
         initial file system which resides in RAM. The kernel then starts
         @('/init'), which mounts the \"real\" root file system, usually from a
         disk. Then it uses the @('pivot_root') syscall to make it the new
         @('/'). This allows Linux to dynamically link in the appropriate kernel
         modules from the initramfs, including disk and file system drivers
         necessary to mount the \"real\" disk.</p>

         <p>On our machine, we choose to use the initramfs as our root
         file system and don't @('pivot_root'). This makes it so that we don't
         have to use a disk device to boot. Linux requires the initramfs to be
         a (potentially compressed) @('cpio') archive.</p>

         <p>We assume you're following this using a Linux system with a
         \"Linux-style\" file system. While this should work with other Linux
         distributions, we've tested the model with Alpine Linux's rootfs
         (version 3.21, the latest as of writing). We chose this distribution
         because it is small, making it easy to quickly recreate the cpio
         archive as needed when testing and because they provide a download
         link on their website for a tarball of their rootfs, rather than
         having to bootstrap the rootfs using a tool like Arch Linux's
         @('pacstrap').</p>

         <p>Alpine Linux version 3.21 for x86_64 can be downloaded <a
         href=\"https://dl-cdn.alpinelinux.org/alpine/v3.21/releases/x86_64/\">here</a>.
         From that page, download the file
         @('alpine-minirootfs-3.21.0-x86_64.tar.gz').</p>

         <p>Once you've downloded the Alpine mini root file system, do the
         following to extract it:</p>

         <code>
         mkdir alpine
         cd alpine
         # Note: the Alpine tarball will extract into your current directory,
         # so you should create a directory to contain the files, as shown
         # above
         tar xvf &lt;downloaded Alpine tarball path&gt;
         </code>

         <p>Now, we need to add an @('init') script. This is what the kernel
         will start once it is done booting. We provide the following simple
         init script:</p>"

         (xdoc::@{} *linux-init-script*)

         "<p>at @('books/projects/x86isa/linux/init') in the ACL2 source tree.
         It mounts some file systems that are expected to be present by many
         programs, sets the system hostname and the @('HOME') environment
         variable, and then starts a login shell for us to use. Copy it to the
         root of your alpine rootfs and make sure it has executable
         permissions.</p>

         <p>If you wish to install additional software, you can @('chroot')
         into your alpine rootfs and install your software like usual.</p>

         <p>The last step is to create the cpio archive. We'll use libarchive's
         implementation of @('tar'), which in addition to tar, supports a
         number of archive formats, including cpio. On Linux systems, it's
         usually installed as @('bsdtar'). Run the following command in the
         alpine rootfs directory to create your rootfs image:</p>
         <code>
         bsdtar --format newc --uid 0 --gid 0 -cvf &lt;archive path&gt;.img *
         </code>

         <p>Make sure you aren't saving your archive in the rootfs directory.
         Once that is done you should have a cpio archive @('<archive
         path>.img') containing your rootfs, which can be used to boot
         Linux.</p>"))
