; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
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
; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>
; Shilpi Goel         <shigoel@cs.utexas.edu>

;; Constants from MACOS 10.8.5 file:  "/usr/include/mach-o/loader.h"

;; ==================================================================-

(in-package "X86ISA")
(include-book "../sdlf-utils" :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

;; ======================================================================

;; #define _MACHO_LOADER_H_

(defconst *MH_MAGIC*                                                #xfeedface) ;;              /* the mach magic number */
(defconst *MH_CIGAM*                                                #xcefaedfe) ;;              /* NXSwapInt(MH_MAGIC) */
(defconst *MH_MAGIC_64*                                             #xfeedfacf) ;;              /* the 64-bit mach magic number */
(defconst *MH_CIGAM_64*                                             #xcffaedfe) ;;              /* NXSwapInt(MH_MAGIC_64) */
(defconst *MH_OBJECT*                                               #x1) ;;                     /* relocatable object file */
(defconst *MH_EXECUTE*                                              #x2) ;;                     /* demand paged executable file */
(defconst *MH_FVMLIB*                                               #x3) ;;                     /* fixed VM shared library file */
(defconst *MH_CORE*                                                 #x4) ;;                     /* core file */
(defconst *MH_PRELOAD*                                              #x5) ;;                     /* preloaded executable file */
(defconst *MH_DYLIB*                                                #x6) ;;                     /* dynamically bound shared library */
(defconst *MH_DYLINKER*                                             #x7) ;;                     /* dynamic link editor */
(defconst *MH_BUNDLE*                                               #x8) ;;                     /* dynamically bound bundle file */
(defconst *MH_DYLIB_STUB*                                           #x9) ;;                     /* shared library stub for static */
(defconst *MH_DSYM*                                                 #xa) ;;                     /* companion file with only debug */
(defconst *MH_KEXT_BUNDLE*                                          #xb) ;;                     /* x86_64 kexts */
(defconst *MH_NOUNDEFS*                                             #x1) ;;                     /* the object file has no undefined */
(defconst *MH_INCRLINK*                                             #x2) ;;                     /* the object file is the output of an */
(defconst *MH_DYLDLINK*                                             #x4) ;;                     /* the object file is input for the */
(defconst *MH_BINDATLOAD*                                           #x8) ;;                     /* the object file's undefined */
(defconst *MH_PREBOUND*                                             #x10) ;;                    /* the file has its dynamic undefined */
(defconst *MH_SPLIT_SEGS*                                           #x20) ;;                    /* the file has its read-only and */
(defconst *MH_LAZY_INIT*                                            #x40) ;;                    /* the shared library init routine is */
(defconst *MH_TWOLEVEL*                                             #x80) ;;                    /* the image is using two-level name */
(defconst *MH_FORCE_FLAT*                                           #x100) ;;                   /* the executable is forcing all images */
(defconst *MH_NOMULTIDEFS*                                          #x200) ;;                   /* this umbrella guarantees no multiple */
(defconst *MH_NOFIXPREBINDING*                                      #x400) ;;                   /* do not have dyld notify the */
(defconst *MH_PREBINDABLE*                                          #x800) ;;                   /* the binary is not prebound but can */
(defconst *MH_ALLMODSBOUND*                                         #x100) ;;                   /* indicates that this binary binds to */
(defconst *MH_SUBSECTIONS_VIA_SYMBOLS*                              #x2000) ;;                  /* safe to divide up the sections into */
(defconst *MH_CANONICAL*                                            #x4000) ;;                  /* the binary has been canonicalized */
(defconst *MH_WEAK_DEFINES*                                         #x8000) ;;                  /* the final linked image contains */
(defconst *MH_BINDS_TO_WEAK*                                        #x10000) ;;                 /* the final linked image uses */
(defconst *MH_ALLOW_STACK_EXECUTION*                                #x20000) ;;                 /* When this bit is set, all stacks */
(defconst *MH_ROOT_SAFE*                                            #x40000) ;;                 /* When this bit is set, the binary */
(defconst *MH_SETUID_SAFE*                                          #x80000) ;;                 /* When this bit is set, the binary */
(defconst *MH_NO_REEXPORTED_DYLIBS*                                 #x100000) ;;                /* When this bit is set on a dylib, */
(defconst *MH_PIE*                                                  #x200000) ;;                /* When this bit is set, the OS will */
(defconst *MH_DEAD_STRIPPABLE_DYLIB*                                #x400000) ;;                /* Only for use on dylibs.  When */
(defconst *MH_HAS_TLV_DESCRIPTORS*                                  #x800000) ;;                /* Contains a section of type */
(defconst *MH_NO_HEAP_EXECUTION*                                    #x1000000) ;;               /* When this bit is set, the OS will */
(defconst *LC_REQ_DYLD*                                             #x80000000) ;;
(defconst *LC_SEGMENT*                                              #x1) ;;                     /* segment of this file to be mapped */
(defconst *LC_SYMTAB*                                               #x2) ;;                     /* link-edit stab symbol table info */
(defconst *LC_SYMSEG*                                               #x3) ;;                     /* link-edit gdb symbol table info (obsolete) */
(defconst *LC_THREAD*                                               #x4) ;;                     /* thread */
(defconst *LC_UNIXTHREAD*                                           #x5) ;;                     /* unix thread (includes a stack) */
(defconst *LC_LOADFVMLIB*                                           #x6) ;;                     /* load a specified fixed VM shared library */
(defconst *LC_IDFVMLIB*                                             #x7) ;;                     /* fixed VM shared library identification */
(defconst *LC_IDENT*                                                #x8) ;;                     /* object identification info (obsolete) */
(defconst *LC_FVMFILE*                                              #x9) ;;                     /* fixed VM file inclusion (internal use) */
(defconst *LC_PREPAGE*                                              #xa) ;;                     /* prepage command (internal use) */
(defconst *LC_DYSYMTAB*                                             #xb) ;;                     /* dynamic link-edit symbol table info */
(defconst *LC_LOAD_DYLIB*                                           #xc) ;;                     /* load a dynamically linked shared library */
(defconst *LC_ID_DYLIB*                                             #xd) ;;                     /* dynamically linked shared lib ident */
(defconst *LC_LOAD_DYLINKER*                                        #xe) ;;                     /* load a dynamic linker */
(defconst *LC_ID_DYLINKER*                                          #xf) ;;                     /* dynamic linker identification */
(defconst *LC_PREBOUND_DYLIB*                                       #x10) ;;                    /* modules prebound for a dynamically */
(defconst *LC_ROUTINES*                                             #x11) ;;                    /* image routines */
(defconst *LC_SUB_FRAMEWORK*                                        #x12) ;;                    /* sub framework */
(defconst *LC_SUB_UMBRELLA*                                         #x13) ;;                    /* sub umbrella */
(defconst *LC_SUB_CLIENT*                                           #x14) ;;                    /* sub client */
(defconst *LC_SUB_LIBRARY*                                          #x15) ;;                    /* sub library */
(defconst *LC_TWOLEVEL_HINTS*                                       #x16) ;;                    /* two-level namespace lookup hints */
(defconst *LC_PREBIND_CKSUM*                                        #x17) ;;                    /* prebind checksum */
(defconst *LC_LOAD_WEAK_DYLIB*                                      (logior #x18 *LC_REQ_DYLD*))
(defconst *LC_SEGMENT_64*                                           #x19) ;;                    /* 64-bit segment of this file to be */
(defconst *LC_ROUTINES_64*                                          #x1a) ;;                    /* 64-bit image routines */
(defconst *LC_UUID*                                                 #x1b) ;;                    /* the uuid */
(defconst *LC_RPATH*                                                (logior #x1c *LC_REQ_DYLD*)) ;;    /* runpath additions */
(defconst *LC_CODE_SIGNATURE*                                       #x1d) ;;                    /* local of code signature */
(defconst *LC_SEGMENT_SPLIT_INFO*                                   #x1e) ;;                    /* local of info to split segments */
(defconst *LC_REEXPORT_DYLIB*                                       (logior #x1f *LC_REQ_DYLD*)) ;;    /* load and re-export dylib */
(defconst *LC_LAZY_LOAD_DYLIB*                                      #x20) ;;                    /* delay load of dylib until first use */
(defconst *LC_ENCRYPTION_INFO*                                      #x21) ;;                    /* encrypted segment information */
(defconst *LC_DYLD_INFO*                                            #x22) ;;                    /* compressed dyld information */
(defconst *LC_DYLD_INFO_ONLY*                                       (logior #x22 *LC_REQ_DYLD*)) ;;    /* compressed dyld information only */
(defconst *LC_LOAD_UPWARD_DYLIB*                                    (logior #x23 *LC_REQ_DYLD*)) ;;    /* load upward dylib */
(defconst *LC_VERSION_MIN_MACOSX*                                   #x24) ;;                    /* build for MacOSX min OS version */
(defconst *LC_VERSION_MIN_IPHONEOS*                                 #x25) ;;                    /* build for iPhoneOS min OS version */
(defconst *LC_FUNCTION_STARTS*                                      #x26) ;;                    /* compressed table of function start addresses */
(defconst *LC_DYLD_ENVIRONMENT*                                     #x27) ;;                    /* string for dyld to treat */
(defconst *LC_MAIN*                                                 (logior #x28 *LC_REQ_DYLD*)) ;;      /* replacement for LC_UNIXTHREAD */
(defconst *LC_DATA_IN_CODE*                                         #x29) ;;                    /* table of non-instructions in __text */
(defconst *LC_SOURCE_VERSION*                                       #x2A) ;;                    /* source version used to build binary */
(defconst *LC_DYLIB_CODE_SIGN_DRS*                                  #x2B) ;;                    /* Code signing DRs copied from linked dylibs */
(defconst *SG_HIGHVM*                                               #x1) ;;                     /* the file contents for this segment is for */
(defconst *SG_FVMLIB*                                               #x2) ;;                     /* this segment is the VM that is allocated by */
(defconst *SG_NORELOC*                                              #x4) ;;                     /* this segment has nothing that was relocated */
(defconst *SG_PROTECTED_VERSION_1*                                  #x8) ;;                     /* This segment is protected.  If the */
(defconst *SECTION_TYPE*                                            #x000000ff) ;;              /* 256 section types */
(defconst *SECTION_ATTRIBUTES*                                      #xffffff00) ;;              /* 24 section attributes */
(defconst *S_REGULAR*                                               #x0) ;;                     /* regular section */
(defconst *S_ZEROFILL*                                              #x1) ;;                     /* zero fill on demand section */
(defconst *S_CSTRING_LITERALS*                                      #x2) ;;                     /* section with only literal C strings*/
(defconst *S_4BYTE_LITERALS*                                        #x3) ;;                     /* section with only 4 byte literals */
(defconst *S_8BYTE_LITERALS*                                        #x4) ;;                     /* section with only 8 byte literals */
(defconst *S_LITERAL_POINTERS*                                      #x5) ;;                     /* section with only pointers to */
(defconst *S_NON_LAZY_SYMBOL_POINTERS*                              #x6) ;;                     /* section with only non-lazy */
(defconst *S_LAZY_SYMBOL_POINTERS*                                  #x7) ;;                     /* section with only lazy symbol */
(defconst *S_SYMBOL_STUBS*                                          #x8) ;;                     /* section with only symbol */
(defconst *S_MOD_INIT_FUNC_POINTERS*                                #x9) ;;                     /* section with only function */
(defconst *S_MOD_TERM_FUNC_POINTERS*                                #xa) ;;                     /* section with only function */
(defconst *S_COALESCED*                                             #xb) ;;                     /* section contains symbols that */
(defconst *S_GB_ZEROFILL*                                           #xc) ;;                     /* zero fill on demand section */
(defconst *S_INTERPOSING*                                           #xd) ;;                     /* section with only pairs of */
(defconst *S_16BYTE_LITERALS*                                       #xe) ;;                     /* section with only 16 byte */
(defconst *S_DTRACE_DOF*                                            #xf) ;;                     /* section contains */
(defconst *S_LAZY_DYLIB_SYMBOL_POINTER*                             #x10) ;;                    /* section with only lazy */
(defconst *S_THREAD_LOCAL_REGULAR*                                  #x11) ;;                    /* template of initial */
(defconst *S_THREAD_LOCAL_ZEROFILL*                                 #x12) ;;                    /* template of initial */
(defconst *S_THREAD_LOCAL_VARIABLES*                                #x13) ;;                    /* TLV descriptors */
(defconst *S_THREAD_LOCAL_VARIABLE_POINTERS*                        #x14) ;;                    /* pointers to TLV */
(defconst *S_THREAD_LOCAL_INIT_FUNCTION_POINTERS*                   #x15) ;;                    /* functions to call */
(defconst *SECTION_ATTRIBUTES_USR*                                  #xff000000) ;;              /* User setable attributes */
(defconst *S_ATTR_PURE_INSTRUCTIONS*                                #x80000000) ;;              /* section contains only true */
(defconst *S_ATTR_NO_TOC*                                           #x40000000) ;;              /* section contains coalesced */
(defconst *S_ATTR_STRIP_STATIC_SYMS*                                #x20000000) ;;              /* ok to strip static symbols */
(defconst *S_ATTR_NO_DEAD_STRIP*                                    #x10000000) ;;              /* no dead stripping */
(defconst *S_ATTR_LIVE_SUPPORT*                                     #x08000000) ;;              /* blocks are live if they */
(defconst *S_ATTR_SELF_MODIFYING_CODE*                              #x04000000) ;;              /* Used with i386 code stubs */
(defconst *S_ATTR_DEBUG*                                            #x02000000) ;;              /* a debug section */
(defconst *SECTION_ATTRIBUTES_SYS*                                  #x00ffff00) ;;              /* system setable attributes */
(defconst *S_ATTR_SOME_INSTRUCTIONS*                                #x00000400) ;;              /* section contains some */
(defconst *S_ATTR_EXT_RELOC*                                        #x00000200) ;;              /* section has external */
(defconst *S_ATTR_LOC_RELOC*                                        #x00000100) ;;              /* section has local */
(defconst *SEG_PAGEZERO*                                            "__PAGEZERO") ;;            /* the pagezero segment which has no */
(defconst *SEG_TEXT*                                                "__TEXT") ;;                /* the tradition UNIX text segment */
(defconst *SECT_TEXT*                                               "__text") ;;                /* the real text part of the text */
(defconst *SECT_FVMLIB_INIT0*                                       "__fvmlib_init0") ;;        /* the fvmlib initialization */
(defconst *SECT_FVMLIB_INIT1*                                       "__fvmlib_init1") ;;        /* the section following the */
(defconst *SEG_DATA*                                                "__DATA") ;;                /* the tradition UNIX data segment */
(defconst *SECT_DATA*                                               "__data") ;;                /* the real initialized data section */
(defconst *SECT_BSS*                                                "__bss") ;;                 /* the real uninitialized data section*/
(defconst *SECT_COMMON*                                             "__common") ;;              /* the section common symbols are */
(defconst *SEG_OBJC*                                                "__OBJC") ;;                /* objective-C runtime segment */
(defconst *SECT_OBJC_SYMBOLS*                                       "__symbol_table") ;;        /* symbol table */
(defconst *SECT_OBJC_MODULES*                                       "__module_info") ;;         /* module information */
(defconst *SECT_OBJC_STRINGS*                                       "__selector_strs") ;;       /* string table */
(defconst *SECT_OBJC_REFS*                                          "__selector_refs") ;;       /* string table */
(defconst *SEG_ICON*                                                "__ICON") ;;                /* the icon segment */
(defconst *SECT_ICON_HEADER*                                        "__header") ;;              /* the icon headers */
(defconst *SECT_ICON_TIFF*                                          "__tiff") ;;                /* the icons in tiff format */
(defconst *SEG_LINKEDIT*                                            "__LINKEDIT") ;;            /* the segment containing all structs */
(defconst *SEG_UNIXSTACK*                                           "__UNIXSTACK") ;;           /* the unix stack segment */
(defconst *SEG_IMPORT*                                              "__IMPORT") ;;              /* the segment for the self (dyld) */
(defconst *INDIRECT_SYMBOL_LOCAL*                                   #x80000000)
(defconst *INDIRECT_SYMBOL_ABS*                                     #x40000000)
(defconst *REBASE_TYPE_POINTER*                                     1)
(defconst *REBASE_TYPE_TEXT_ABSOLUTE32*                             2)
(defconst *REBASE_TYPE_TEXT_PCREL32*                                3)
(defconst *REBASE_OPCODE_MASK*                                      #xF0)
(defconst *REBASE_IMMEDIATE_MASK*                                   #x0F)
(defconst *REBASE_OPCODE_DONE*                                      #x00)
(defconst *REBASE_OPCODE_SET_TYPE_IMM*                              #x10)
(defconst *REBASE_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB*               #x20)
(defconst *REBASE_OPCODE_ADD_ADDR_ULEB*                             #x30)
(defconst *REBASE_OPCODE_ADD_ADDR_IMM_SCALED*                       #x40)
(defconst *REBASE_OPCODE_DO_REBASE_IMM_TIMES*                       #x50)
(defconst *REBASE_OPCODE_DO_REBASE_ULEB_TIMES*                      #x60)
(defconst *REBASE_OPCODE_DO_REBASE_ADD_ADDR_ULEB*                   #x70)
(defconst *REBASE_OPCODE_DO_REBASE_ULEB_TIMES_SKIPPING_ULEB*        #x80)
(defconst *BIND_TYPE_POINTER*                                       1)
(defconst *BIND_TYPE_TEXT_ABSOLUTE32*                               2)
(defconst *BIND_TYPE_TEXT_PCREL32*                                  3)
(defconst *BIND_SPECIAL_DYLIB_SELF*                                  0)
(defconst *BIND_SPECIAL_DYLIB_MAIN_EXECUTABLE*                      -1)
(defconst *BIND_SPECIAL_DYLIB_FLAT_LOOKUP*                          -2)
(defconst *BIND_SYMBOL_FLAGS_WEAK_IMPORT*                           #x1)
(defconst *BIND_SYMBOL_FLAGS_NON_WEAK_DEFINITION*                   #x8)
(defconst *BIND_OPCODE_MASK*                                        #xF0)
(defconst *BIND_IMMEDIATE_MASK*                                     #x0F)
(defconst *BIND_OPCODE_DONE*                                        #x00)
(defconst *BIND_OPCODE_SET_DYLIB_ORDINAL_IMM*                       #x10)
(defconst *BIND_OPCODE_SET_DYLIB_ORDINAL_ULEB*                      #x20)
(defconst *BIND_OPCODE_SET_DYLIB_SPECIAL_IMM*                       #x30)
(defconst *BIND_OPCODE_SET_SYMBOL_TRAILING_FLAGS_IMM*               #x40)
(defconst *BIND_OPCODE_SET_TYPE_IMM*                                #x50)
(defconst *BIND_OPCODE_SET_ADDEND_SLEB*                             #x60)
(defconst *BIND_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB*                 #x70)
(defconst *BIND_OPCODE_ADD_ADDR_ULEB*                               #x80)
(defconst *BIND_OPCODE_DO_BIND*                                     #x90)
(defconst *BIND_OPCODE_DO_BIND_ADD_ADDR_ULEB*                       #xA0)
(defconst *BIND_OPCODE_DO_BIND_ADD_ADDR_IMM_SCALED*                 #xB0)
(defconst *BIND_OPCODE_DO_BIND_ULEB_TIMES_SKIPPING_ULEB*            #xC0)
(defconst *EXPORT_SYMBOL_FLAGS_KIND_MASK*                           #x03)
(defconst *EXPORT_SYMBOL_FLAGS_KIND_REGULAR*                        #x00)
(defconst *EXPORT_SYMBOL_FLAGS_KIND_THREAD_LOCAL*                   #x01)
(defconst *EXPORT_SYMBOL_FLAGS_WEAK_DEFINITION*                     #x04)
(defconst *EXPORT_SYMBOL_FLAGS_REEXPORT*                            #x08)
(defconst *EXPORT_SYMBOL_FLAGS_STUB_AND_RESOLVER*                   #x10)
(defconst *DICE_KIND_DATA*                                          #x0001) ;;                  /* L$start$data$...  label */
(defconst *DICE_KIND_JUMP_TABLE8*                                   #x0002) ;;                  /* L$start$jt8$...   label */
(defconst *DICE_KIND_JUMP_TABLE16*                                  #x0003) ;;                  /* L$start$jt16$...  label */
(defconst *DICE_KIND_JUMP_TABLE32*                                  #x0004) ;;                  /* L$start$jt32$...  label */
(defconst *DICE_KIND_ABS_JUMP_TABLE32*                              #x0005) ;;                  /* L$start$jta32$... label */


;; ======================================================================
;; Some more constants (not from "/usr/include/mach-o/loader.h"):

(defconst *MACH-O-TEXT*
  (combine-bytes (string-to-bytes "__TEXT")))

(defconst *TEXT-text*
  (combine-bytes (string-to-bytes "__text")))

(defconst *TEXT-cstring*
  (combine-bytes (string-to-bytes "__cstring")))

(defconst *TEXT-const*
  (combine-bytes (string-to-bytes "__const")))

(defconst *MACH-O-DATA*
  (combine-bytes (string-to-bytes "__DATA")))

(defconst *DATA-data*
  (combine-bytes (string-to-bytes "__data")))

(defconst *DATA-dyld*
  (combine-bytes (string-to-bytes "__dyld")))

(defconst *DATA-const*
  (combine-bytes (string-to-bytes "__const")))

(defconst *DATA-bss*
  (combine-bytes (string-to-bytes "__bss")))

(defconst *DATA-common*
  (combine-bytes (string-to-bytes "__common")))

;; ======================================================================
