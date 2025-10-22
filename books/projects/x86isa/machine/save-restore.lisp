; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) May - August 2023, Regents of the University of Texas
; Copyright (C) August 2023 - May 2024, Yahya Sohail
; Copyright (C) May 2024 - August 2024, Intel Corporation

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
; Yahya Sohail        <yahya.sohail@intel.com>

(in-package "X86ISA")

;; I apologize to anyone who has to read this code. I returned to this code
;; well after writing it to fix some bugs in it, and while I did manage to fix
;; the bugs, I have realized I have no idea how this works.

(include-book "state")

(defun without-docs (data)
  (declare (xargs :mode :program))
  (b* (((when (equal data nil)) nil)
       (curr (car data))
       ((when (equal (car curr) :doc)) (without-docs (cdr data))))
      (cons curr (without-docs (cdr data)))))

(defun field-array-p (field)
  (declare (xargs :mode :program))
  (b* ((typ (cadr (assoc-keyword :type (cdr field)))))
      (and (consp typ)
           (equal 'array
                  (car typ)))))

;; Define functions to serialize and deserialize the x86 stobj to a cons based object
(defun serialize-arr-fn (accessor len idx)
  (declare (xargs :mode :program))
  (if (equal len idx)
    nil
    `(b* ((val (,accessor ,idx x86)))
         (cons val ,(serialize-arr-fn accessor len (1+ idx))))))

(defmacro serialize-arr (accessor len)
  (serialize-arr-fn accessor len 0))

(defun deserializer-name (fld-name)
  (acl2::packn (list 'deserialize- fld-name)))

(defun rev-if-list (x)
  (declare (xargs :guard t))
  (if (true-listp x)
    (reverse x)
    x))

(defmacro deserialize-arr (fld-name len)
  `(,(deserializer-name fld-name) ,len (rev-if-list val) x86))

(defun field-array-length (field)
  (declare (xargs :mode :program))
  (caaddr (cadr (assoc-keyword :type (cdr field)))))

(defun field-accessor (field)
  (declare (xargs :mode :program))
  (b* ((accessor (cadr (assoc-keyword :accessor (cdr field))))
       ((when accessor) accessor)
       (arr? (field-array-p field))
       ((when arr?) (acl2::packn (list (car field) 'i))))
      (car field)))

(defun field-updater (field)
  (declare (xargs :mode :program))
  (b* ((updater (cadr (assoc-keyword :updater (cdr field))))
       ((when updater) updater)
       (arr? (field-array-p field))
       ((when arr?) (acl2::packn (list '! (car field) 'i))))
      (acl2::packn (list '! (car field)))))

(defmacro serialize-scalar (accessor)
  `(,accessor x86))

(defmacro deserialize-scalar (fld-name)
  `(,(deserializer-name fld-name) val x86))

(defun serialize-field (field)
  (declare (xargs :mode :program))
  (b* ((accessor (field-accessor field)))
      (cond ((field-array-p field) `(serialize-arr ,accessor ,(field-array-length field)))
            (t `(serialize-scalar ,accessor)))))

(defun deserialize-field (field)
  (declare (xargs :mode :program))
  (b* ((fld-name (intern (symbol-name (car field)) "KEYWORD")))
      (cond ((field-array-p field) `(deserialize-arr ,fld-name ,(field-array-length field)))
            (t `(deserialize-scalar ,fld-name)))))

(defun serialize-x86-fields (fields)
  (declare (xargs :mode :program))
  (if (not fields)
    nil
    (if (equal (caar fields) 'mem)
      (serialize-x86-fields (cdr fields))
      (cons (serialize-field (car fields))
            (serialize-x86-fields (cdr fields))))))

(defun deserialize-x86-fields (fields)
  (declare (xargs :mode :program))
  (if (not fields)
    nil
    (if (equal (caar fields) 'mem)
      (deserialize-x86-fields (cdr fields))
      (cons (deserialize-field (car fields))
            (deserialize-x86-fields (cdr fields))))))

(defun exec-and-cons-together (code)
  (declare (xargs :mode :program))
  (if (not code)
    nil
    `(b* ((val ,(car code)))
         (cons val ,(exec-and-cons-together (cdr code))))))

(defun consume-from-list (code)
  (declare (xargs :mode :program))
  (if (not code)
    'x86
    `(b* (((unless (consp obj)) x86)
          ((list* ?val ?obj) obj)
          (x86 ,(car code)))
         ,(consume-from-list (cdr code)))))

(defun define-deserializer (field)
  (declare (xargs :mode :program))
  (b* ((fld-name (car field))
       (deserializer-name (deserializer-name fld-name))
       (updater (field-updater field)))
      (if (field-array-p field)
        `(defun ,deserializer-name (len obj x86)
          (declare (xargs :stobjs (x86)
                          :guard (and (natp len)
                                      (<= len ,(field-array-length field)))))
          (if (mbt (natp len))
            (b* (((when (or (equal len 0)
                            (not (consp obj)))) x86)
                 ((list* el obj) obj)
                 (el (x86-elem-fix ,(intern (symbol-name (car field)) "KEYWORD") el))
                 (x86 (,updater (1- len) el x86)))
                (,deserializer-name (1- len) obj x86))
            x86))
        `(defun ,deserializer-name (obj x86)
           (declare (xargs :stobjs (x86)
                           :guard t))
           (b* ((obj (x86-elem-fix ,(intern (symbol-name (car field)) "KEYWORD") obj))
                 (x86 (,updater obj x86)))
                x86)))))

(defun define-deserializers (fields)
  (declare (xargs :mode :program))
  (b* (((when (not fields)) nil)
       ((list* field tail) fields)
       ((unless (and (not (equal (car field)
                                 'mem)))) (define-deserializers tail))
       (deserializer (define-deserializer field)))
      (cons deserializer (define-deserializers tail))))

(make-event `(progn ,@(define-deserializers (without-docs *x86isa-state*))))

(defmacro serialize-x86-body ()
  (b* ((serialization-code (serialize-x86-fields (without-docs *x86isa-state*))))
      (exec-and-cons-together serialization-code)))

(defmacro deserialize-x86-body ()
  (b* ((deserialization-code (deserialize-x86-fields (without-docs *x86isa-state*))))
      (consume-from-list deserialization-code)))

(defund serialize-x86 (x86)
  (declare (xargs :stobjs (x86)))
  (serialize-x86-body))

(defund deserialize-x86 (obj x86)
  (declare (xargs :stobjs (x86)))
  (deserialize-x86-body))

(local (defthm unsigned-byte-p-8-of-mem
               (unsigned-byte-p 8 (xr :mem addr x86))))

(local (defthm unsigned-byte-p-8-is-between-0-and-256
               (implies (unsigned-byte-p 8 x)
                        (and (integerp x)
                             (<= 0 x)
                             (< x 256)))))

(defthm xr-mem-between-0-and-256
        (and (integerp (xr :mem addr x86))
             (<= 0 (xr :mem addr x86))
             (< (xr :mem addr x86) 256)))

(local (include-book "std/io/top" :dir :system))

(define write-mem-to-channel ((size natp)
                              (channel symbolp)
                              x86
                              state)
  :guard (and (<= size *mem-size-in-bytes*)
              (open-output-channel-p channel :byte state))
  (if (mbt (natp size))
    (b* (((when (equal size 0)) state)
         (state (write-byte$ (memi (1- size) x86) channel state)))
        (write-mem-to-channel (1- size) channel x86 state))
    state)
  ///
  (defthm write-mem-to-channel-leaves-channel-open
          (implies (open-output-channel-p1 channel :byte state)
                   (open-output-channel-p1 channel :byte (write-mem-to-channel size channel x86 state))))
  (defthm write-mem-to-channel-returns-state-p1
          (implies (and (state-p1 state)
                        (symbolp channel)
                        (open-output-channel-p1 channel :byte state))
                   (state-p1 (write-mem-to-channel size channel x86 state)))))

(defxdoc save-restore
         :parents (x86isa-state)
         :short "Tools for saving and restoring the x86 state"
         :long "<p>While most ACL2 objects can be serialized using @(see
         acl2::serialize), stobjs can not. The @('x86') state is an absstobj,
so we can't directly use serialize. Instead, we convert the state, excluding
the memory, into a cons tree and write that out to a file with serialize. Then,
we write the low n bytes, where n is user specified, of memory out to disk in
another file, thereby avoiding constructing a potentially very large cons tree.
Restoring the state is essentially the process in reverse.</p>")

(define save-x86 ((filename stringp "The name of the file to write the
                            non-memory state out to. The memory will be written
                            out to &lt;filename&gt;.mem.")
                  (memsize natp "The number of bytes of memory to save.")
                  x86
                  state)
  :parents (save-restore)
  :guard (<= memsize *mem-size-in-bytes*)
  (b* ((serialized-x86 (serialize-x86 x86))
       (state (serialize-write filename serialized-x86))
       (memfilename (concatenate 'string filename ".mem"))
       ((mv memchannel state) (open-output-channel memfilename :byte state))
       ((unless memchannel) state)
       (state (write-mem-to-channel memsize memchannel x86 state))
       (state (close-output-channel memchannel state)))
      state))

(define read-mem-from-channel ((size natp)
                               (channel symbolp)
                               x86
                               state)
  :guard (and (<= size *mem-size-in-bytes*)
              (open-input-channel-p channel :byte state))
  (if (mbt (natp size))
    (b* (((when (equal size 0)) (mv x86 state))
        ((mv byt state) (read-byte$ channel state))
        ((unless byt) (mv x86 state))
        (x86 (if (not (= byt 0))
               (!memi (1- size) byt x86)
               x86)))
       (read-mem-from-channel (1- size) channel x86 state))
    (mv x86 state))
  ///
  (defthm read-mem-from-channel-leaves-channel-open
          (implies (open-input-channel-p1 channel :byte state)
                   (open-input-channel-p1 channel :byte (mv-nth 1 (read-mem-from-channel size channel x86 state)))))
  (defthm read-mem-from-channel-returns-state-p1
          (implies (and (state-p1 state)
                        (symbolp channel)
                        (open-input-channel-p1 channel :byte state))
                   (state-p1 (mv-nth 1 (read-mem-from-channel size channel x86 state))))))

(define restore-x86 ((filename stringp "The name of the file to read the
                               non-memory state from. The memory will be read
                               from &lt;filename&gt;.mem.")
                     (memsize natp "The number of bytes to read out of the memory file and into the memory")
                     x86
                     state)
  :parents (save-restore)
  :guard (<= memsize *mem-size-in-bytes*)
  (b* (((mv read-in-x86 state) (serialize-read filename))
       (x86 (deserialize-x86 read-in-x86 x86))
       (memfilename (concatenate 'string filename ".mem"))
       ((mv memchannel state) (open-input-channel memfilename :byte state))
       ((unless memchannel) (mv x86 state))
       ((mv x86 state) (read-mem-from-channel memsize memchannel x86 state))
       (state (close-input-channel memchannel state)))
      (mv x86 state)))
