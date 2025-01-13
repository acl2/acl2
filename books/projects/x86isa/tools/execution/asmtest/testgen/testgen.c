// http://opensource.org/licenses/BSD-3-Clause

// Copyright (C) 2025, Yahya Sohail

// All rights reserved.

// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:

// o Redistributions of source code must retain the above copyright
//   notice, this list of conditions and the following disclaimer.

// o Redistributions in binary form must reproduce the above copyright
//   notice, this list of conditions and the following disclaimer in the
//   documentation and/or other materials provided with the distribution.

// o Neither the name of the copyright holders nor the names of its
//   contributors may be used to endorse or promote products derived
//   from this software without specific prior written permission.

// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

// Original Author(s):
// Yahya Sohail        <yahya@yahyasohail.com>

#include <argp.h>
#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <xed/xed-interface.h>

const char *argp_program_version = "testgen 0.0.1";
const char *argp_program_bug_address = "<yahya@yahyasohail.com>";

/* Program documentation */
static char doc[] = "Test generator for asmtest";

/* A description of the arguments we accept */
static char args_doc[] = "";

/* The options we understand */
static struct argp_option options[] = {
    {"asm-output", 'a', "FILE", 0, "Output assembly file (required)"},
    {"text-output", 't', "FILE", 0, "Output text file (required)"},
    {0}};

/* Used by main to communicate with parse_opt */
struct arguments {
  char *asm_file;
  char *text_file;
};

/* Parse a single option */
static error_t parse_opt(int key, char *arg, struct argp_state *state) {
  struct arguments *arguments = state->input;

  switch (key) {
  case 'a':
    arguments->asm_file = arg;
    break;
  case 't':
    arguments->text_file = arg;
    break;
  case ARGP_KEY_END:
    if (!arguments->asm_file || !arguments->text_file) {
      argp_error(state, "Both --asm-output and --text-output are required");
    }
    break;
  default:
    return ARGP_ERR_UNKNOWN;
  }
  return 0;
}

/* Our argp parser */
static struct argp argp = {options, parse_opt, args_doc, doc};

struct frame_record_reg_entry {
  xed_reg_enum_t reg;
};

struct frame_record_imm_entry {
  uint8_t width;
};

struct frame_record {
  bool has_flags;
  uint64_t flags_mask;

  size_t reg_size;
  size_t reg_capacity;
  struct frame_record_reg_entry *reg_entries;

  size_t imm_size;
  size_t imm_capacity;
  struct frame_record_imm_entry *imm_entries;
};

void frame_record_init(struct frame_record *rec) {
  rec->has_flags = false;

  rec->reg_size = 0;
  rec->reg_capacity = 1;
  rec->reg_entries = malloc(sizeof(struct frame_record_reg_entry));

  rec->imm_size = 0;
  rec->imm_capacity = 1;
  rec->imm_entries = malloc(sizeof(struct frame_record_reg_entry));
}

void frame_record_cleanup(struct frame_record *rec) {
  free(rec->reg_entries);
  free(rec->imm_entries);
}

void frame_record_insert_reg(struct frame_record *rec, xed_reg_enum_t reg) {
  if (rec->reg_size == rec->reg_capacity) {
    rec->reg_entries =
        realloc(rec->reg_entries,
                sizeof(struct frame_record_reg_entry) * rec->reg_capacity * 2);
    rec->reg_capacity *= 2;
  }

  rec->reg_entries[rec->reg_size].reg = reg;
  rec->reg_size++;
}

void frame_record_insert_imm(struct frame_record *rec, uint8_t width) {
  if (rec->imm_size == rec->imm_capacity) {
    rec->imm_entries =
        realloc(rec->imm_entries,
                sizeof(struct frame_record_imm_entry) * rec->imm_capacity * 2);
    rec->imm_capacity *= 2;
  }

  rec->imm_entries[rec->imm_size].width = width;
  rec->imm_size++;
}

void frame_record_add_flags(struct frame_record *rec, uint64_t mask) {
  rec->has_flags = true;
  rec->flags_mask = mask;
}

void frame_record_clear(struct frame_record *rec) {
  rec->has_flags = false;
  rec->reg_size = 0;
  rec->imm_size = 0;
}

// given a register number 0 - 15, returns the gpr register of
// corresponding width. For 8-bits, where we have 2 options, we return the lower
// register
xed_reg_enum_t get_width_reg(uint8_t regno, uint8_t width) {
  assert(regno < 16);

  switch (width) {
  case 8:
    return XED_REG_AL + regno;

  case 16:
    return XED_REG_AX + regno;

  case 32:
    return XED_REG_EAX + regno;

  case 64:
    return XED_REG_RAX + regno;
  }

  assert(false);
}

bool inst_frame_records(const xed_inst_t *inst, struct frame_record *in_rec,
                        xed_reg_enum_t operand_allocations[16],
                        struct frame_record *out_rec) {
  xed_iclass_enum_t iclass = xed_inst_iclass(inst);
  xed_isa_set_enum_t isa_set = xed_inst_isa_set(inst);
  xed_category_enum_t category = xed_inst_category(inst);

#define UNSUPPORTED_ATTRIBUTE(attr)                                            \
  if (xed_inst_get_attribute(inst, attr))                                      \
    return true;
#define UNSUPPORTED_ISA_SET(iset)                                              \
  if (isa_set == iset)                                                         \
    return true;
#define UNSUPPORTED_ISA_SET_RANGE(start, end)                                  \
  if (start <= isa_set && isa_set <= end)                                      \
    return true;
#define UNSUPPORTED_ICLASS(class)                                              \
  if (iclass == class)                                                         \
    return true;
#define UNSUPPORTED_CATEGORY(cat)                                              \
  if (category == cat)                                                         \
    return true;

#include "unsupported.h"

#undef UNSUPPORTED_ATTRIBUTE
#undef UNSUPPORTED_ISA_SET
#undef UNSUPPORTED_ISA_SET_RANGE
#undef UNSUPPORTED_ICLASS
#undef UNSUPPORTED_CATEGORY

  unsigned int noperands = xed_inst_noperands(inst);

  if (noperands == 0)
    return true;

  bool allocated_gpr[16] = {false};
  bool allocated_xmm[32] = {false};

  // Allocate rdi and rsi (which hold in and out memory regions) and sysv abi
  // caller saved registers
  allocated_gpr[XED_REG_RSI - XED_REG_RAX] = true;
  allocated_gpr[XED_REG_RDI - XED_REG_RAX] = true;
  allocated_gpr[XED_REG_RBX - XED_REG_RAX] = true;
  allocated_gpr[XED_REG_RSP - XED_REG_RAX] = true;
  allocated_gpr[XED_REG_RBP - XED_REG_RAX] = true;
  allocated_gpr[XED_REG_R12 - XED_REG_RAX] = true;
  allocated_gpr[XED_REG_R13 - XED_REG_RAX] = true;
  allocated_gpr[XED_REG_R14 - XED_REG_RAX] = true;
  allocated_gpr[XED_REG_R15 - XED_REG_RAX] = true;

  size_t allocation_idx = 0;
  size_t n_output = 0;

  for (unsigned int j = 0; j < noperands; j++) {
    const xed_operand_t *op = xed_inst_operand(inst, j);
    const xed_operand_enum_t opname = xed_operand_name(op);
    const bool read = xed_operand_read(op);
    const bool written = xed_operand_written(op);
    const xed_reg_enum_t reg = xed_operand_reg(op);
    const xed_reg_class_enum_t class = xed_reg_class(reg);

    // Don't support if memory operand
    if (opname == XED_OPERAND_MEM0 || opname == XED_OPERAND_MEM1)
      return true;

    if (written)
      n_output++;

    if (reg == XED_REG_FLAGS) {
      // We handle flags separately after encoding because XED only lets us get
      // at flag information for decoded instructions
      continue;
    }

    if (xed_operand_imm(op)) {
      // Immediates aren't written
      frame_record_insert_imm(in_rec, xed_operand_width_bits(op, 3) / 8);
      continue;
    }

    if (class == XED_REG_CLASS_GPR) {
      allocated_gpr[xed_get_largest_enclosing_register(reg) - XED_REG_RAX] =
          true;
      if (read)
        frame_record_insert_reg(in_rec, reg);
      if (written)
        frame_record_insert_reg(out_rec, reg);
      continue;
    } else if (class == XED_REG_CLASS_XMM) {
      allocated_xmm[reg - XED_REG_XMM0] = true;
      if (read)
        frame_record_insert_reg(in_rec, reg);
      if (written)
        frame_record_insert_reg(out_rec, reg);
      continue;
    }

    if (reg != XED_REG_INVALID) {
      // Don't support other registers atm
      return true;
    }

    xed_nonterminal_enum_t nonterminal = xed_operand_nonterminal_name(op);

    if (XED_NONTERMINAL_GPR16_B <= nonterminal &&
        nonterminal <= XED_NONTERMINAL_GPRZ_R) {
      // Find unallocated register
      uint8_t regno = 8;
      while (allocated_gpr[regno]) {
        regno++;
        assert(regno < 16);
      }
      allocated_gpr[regno] = true;

      const xed_reg_enum_t reg =
          get_width_reg(regno, xed_operand_width_bits(op, 3));
      operand_allocations[allocation_idx++] = reg;
      if (read)
        frame_record_insert_reg(in_rec, reg);
      if (written)
        frame_record_insert_reg(out_rec, reg);
      continue;
    } else if (XED_NONTERMINAL_XMM_B <= nonterminal &&
               nonterminal <= XED_NONTERMINAL_XMM_SE64) {
      // Find unallocated register
      uint8_t regno = 8;
      while (allocated_xmm[regno]) {
        regno++;
        assert(regno < 32);
      }
      allocated_xmm[regno] = true;

      const xed_reg_enum_t reg = XED_REG_XMM0 + regno;
      operand_allocations[allocation_idx++] = reg;
      if (read)
        frame_record_insert_reg(in_rec, reg);
      if (written)
        frame_record_insert_reg(out_rec, reg);
      continue;
    }

    if (nonterminal == XED_NONTERMINAL_RFLAGS) {
      // handle rflags later
      continue;
    }

    // Unsupported operand
    return true;
  }

  return n_output == 0;
}

bool encode_inst(const xed_inst_t *inst,
                 const xed_reg_enum_t operand_allocations[16], uint8_t buf[15],
                 unsigned int *enc_len, xed_state_t *state) {
  unsigned int noperands = xed_inst_noperands(inst);

  // Encode the instruction
  xed_encoder_request_t enc_req;
  xed_encoder_request_zero_set_mode(&enc_req, state);
  xed_encoder_request_set_effective_operand_width(&enc_req, 64);
  xed_encoder_request_set_iclass(&enc_req, xed_inst_iclass(inst));

  // Set operands
  size_t allocation_idx = 0;
  for (unsigned int i = 0; i < noperands; i++) {
    const xed_operand_t *op = xed_inst_operand(inst, i);

    if (xed_operand_operand_visibility(op) == XED_OPVIS_SUPPRESSED)
      continue;

    if (xed_operand_operand_visibility(op) == XED_OPVIS_IMPLICIT)
      xed_encoder_request_set_reg(&enc_req, xed_operand_name(op),
                                  xed_operand_reg(op));
    else
      // XED_OPVIS_EXPLICIT
      if (xed_operand_name(op) == XED_OPERAND_IMM0) {
        xed_encoder_request_set_uimm0(&enc_req, 0,
                                      xed_operand_width_bits(op, 3) / 8);
      } else if (xed_operand_name(op) == XED_OPERAND_IMM1) {
        xed_encoder_request_set_uimm1(&enc_req, 0);
      } else {
        xed_encoder_request_set_reg(&enc_req, xed_operand_name(op),
                                    operand_allocations[allocation_idx++]);
      }

    xed_encoder_request_set_operand_order(&enc_req, i, xed_operand_name(op));
  }

  // Encode
  xed_error_enum_t enc_error = xed_encode(&enc_req, buf, 15, enc_len);

  if (enc_error != XED_ERROR_NONE) {
    fprintf(stderr, "Error %s encoding instruction %s\n",
            xed_error_enum_t2str(enc_error),
            xed_iclass_enum_t2str(xed_inst_iclass(inst)));
    fputs("skipping\n", stderr);

    return true;
  }

  return false;
}

void frame_record_flags(uint8_t inst_buf[15], struct frame_record *in_rec,
                        struct frame_record *out_rec, xed_state_t *state) {
  // We must decode our encoded instruction to get at the flag info
  xed_decoded_inst_t xedd;
  xed_decoded_inst_zero(&xedd);
  xed_decoded_inst_set_mode(&xedd, state->mmode, state->stack_addr_width);

  xed_error_enum_t xed_error = xed_decode(&xedd, inst_buf, 15);
  if (xed_error != XED_ERROR_NONE) {
    assert(false);
  }

  const xed_simple_flag_t *flags = xed_decoded_inst_get_rflags_info(&xedd);
  if (!flags)
    return;

  uint64_t read_mask =
      xed_flag_set_mask(xed_simple_flag_get_read_flag_set(flags));
  if (read_mask)
    frame_record_add_flags(in_rec, read_mask);

  uint64_t written_mask =
      xed_flag_set_mask(xed_simple_flag_get_written_flag_set(flags)) &
      ~xed_flag_set_mask(xed_simple_flag_get_undefined_flag_set(flags));

  if (written_mask)
    frame_record_add_flags(out_rec, written_mask);
}

void write_test_asm(uint8_t inst_buf[15], unsigned int inst_len,
                    const struct frame_record *in_rec,
                    const struct frame_record *out_rec, size_t i,
                    FILE *stream) {
  fprintf(stream, "global testgen_%lu\ntestgen_%lu:\n", i, i);

  // Write the preamble
  size_t offset = 0;
  for (size_t j = 0; j < in_rec->imm_size; j++) {
    uint8_t width = in_rec->imm_entries[j].width;

    fputs("push rax\n", stream);

    // loading the 8 or 16-bit registers doesn't clear the rest, so load the
    // corresponding 32-bit register with zero extension
    if (width == 1) {
      fprintf(stream, "movzx eax, BYTE [rdi + 0x%lx]\n", offset);
      fprintf(stream, "mov [testgen_inst_end_%ld - %ld], al\n", i,
              offset + width);
    } else if (width == 2) {
      fprintf(stream, "movzx eax, WORD [rdi + 0x%lx]\n", offset);
      fprintf(stream, "mov [testgen_inst_end_%ld - %ld], ax\n", i,
              offset + width);
    } else if (width == 4) {
      fprintf(stream, "mov eax, [rdi + 0x%lx]\n", offset);
      fprintf(stream, "mov [testgen_inst_end_%ld - %ld], eax\n", i,
              offset + width);
    } else if (width == 8) {
      fprintf(stream, "mov rax, [rdi + 0x%lx]\n", offset);
      fprintf(stream, "mov [testgen_inst_end_%ld - %ld], rax\n", i,
              offset + width);
    } else {
      assert(false);
    }

    fputs("pop rax\n", stream);

    offset += width;
  }

  if (in_rec->has_flags) {
    fputs("push rax\n", stream);

    fprintf(stream, "mov rax, [rdi + 0x%lx]\n", offset);
    fprintf(stream, "and rax, 0x%lx\n", in_rec->flags_mask);
    fputs("push rax\n", stream);
    fputs("popfq\n", stream);

    fputs("pop rax\n", stream);
    offset += 8;
  }

  for (size_t j = 0; j < in_rec->reg_size; j++) {
    const struct frame_record_reg_entry *entry = in_rec->reg_entries + j;

    size_t width = xed_get_register_width_bits64(entry->reg) / 8;

    // loading the 8 or 16-bit registers doesn't clear the rest, so load the
    // corresponding 32-bit register with zero extension
    if (width == 1) {
      fprintf(stream, "movzx %s, BYTE [rdi + 0x%lx]\n",
              xed_reg_enum_t2str((entry->reg - XED_REG_AL) + XED_REG_EAX),
              offset);
    } else if (width == 2) {
      fprintf(stream, "movzx %s, WORD [rdi + 0x%lx]\n",
              xed_reg_enum_t2str((entry->reg - XED_REG_AX) + XED_REG_EAX),
              offset);
    } else if (xed_reg_class(entry->reg) == XED_REG_CLASS_XMM) {
      fprintf(stream, "movdqu %s, [rdi + 0x%lx]\n",
              xed_reg_enum_t2str(entry->reg), offset);
    } else {
      fprintf(stream, "mov %s, [rdi + 0x%lx]\n", xed_reg_enum_t2str(entry->reg),
              offset);
    }

    offset += width;
  }

  // Write instruction
  fputs("db ", stream);
  for (size_t j = 0; j < inst_len; j++) {
    fprintf(stream, "0x%02x, ", inst_buf[j]);
  }
  fprintf(stream, "\ntestgen_inst_end_%lu:\n", i);

  // Write epilogue
  offset = 0;
  if (out_rec->has_flags) {
    fputs("push rax\n", stream);

    fputs("pushfq\n", stream);
    fputs("pop rax\n", stream);
    fprintf(stream, "and rax, 0x%lx\n", out_rec->flags_mask);
    fprintf(stream, "mov [rsi + 0x%lx], rax\n", offset);

    fputs("pop rax\n", stream);
    offset += 8;
  }

  for (size_t j = 0; j < out_rec->reg_size; j++) {
    const struct frame_record_reg_entry *entry = out_rec->reg_entries + j;
    if (xed_reg_class(entry->reg) == XED_REG_CLASS_XMM) {
      fprintf(stream, "movdqu [rsi + 0x%lx], %s\n", offset,
              xed_reg_enum_t2str(entry->reg));
    } else {
      assert(entry->reg != XED_REG_INVALID);
      fprintf(stream, "mov [rsi + 0x%lx], %s\n", offset,
              xed_reg_enum_t2str(entry->reg));

      offset += xed_get_register_width_bits64(entry->reg) / 8;
    }
  }

  fputs("ret\n", stream);
}

size_t get_frame_record_size(const struct frame_record *rec) {
  size_t size = 0;

  if (rec->has_flags)
    size += 8;

  for (size_t i = 0; i < rec->reg_size; i++) {
    size += xed_get_register_width_bits64(rec->reg_entries[i].reg) / 8;
  }

  for (size_t i = 0; i < rec->imm_size; i++) {
    size += rec->imm_entries[i].width;
  }

  return size;
}

void write_snippets(const struct frame_record *in_rec,
                    const struct frame_record *out_rec, size_t i,
                    FILE *stream) {
  fprintf(stream, "testgen_%lu\t%lu\t%lu\n", i, get_frame_record_size(in_rec),
          get_frame_record_size(out_rec));
}

int main(int argc, char **argv) {
  struct arguments arguments;

  /* Initialize to NULL to detect missing arguments */
  arguments.asm_file = NULL;
  arguments.text_file = NULL;

  /* Parse arguments */
  argp_parse(&argp, argc, argv, 0, 0, &arguments);

  xed_tables_init();

  xed_state_t state;
  xed_state_zero(&state);

  /* Initialize for 64-bit mode */
  xed_state_init2(&state, XED_MACHINE_MODE_LONG_64, XED_ADDRESS_WIDTH_64b);

  struct frame_record in_rec;
  struct frame_record out_rec;
  frame_record_init(&in_rec);
  frame_record_init(&out_rec);

  FILE *asm_file = fopen(arguments.asm_file, "w");
  if (!asm_file) {
    fprintf(stderr, "Error: Could not open %s for writing\n",
            arguments.asm_file);
    return 1;
  }

  FILE *snippets_file = fopen(arguments.text_file, "w");
  if (!snippets_file) {
    fprintf(stderr, "Error: Could not open %s for writing\n",
            arguments.text_file);
    fclose(asm_file);
    return 1;
  }

  fputs("; Generated file -- do not edit\ndefault rel\nsection .testgen exec "
        "write\n",
        asm_file);
  fputs("# Generated file -- do not edit", snippets_file);

  const xed_inst_t *table = xed_inst_table_base();
  for (size_t i = 0; i < XED_MAX_INST_TABLE_NODES; i++) {
    const xed_inst_t *inst = &table[i];
    xed_reg_enum_t operand_allocations[16];
    uint8_t inst_buf[15];
    unsigned int inst_len;

    bool fail =
        inst_frame_records(inst, &in_rec, operand_allocations, &out_rec);
    if (fail)
      goto cont;

    fail = encode_inst(inst, operand_allocations, inst_buf, &inst_len, &state);
    if (fail)
      goto cont;

    frame_record_flags(inst_buf, &in_rec, &out_rec, &state);

    write_test_asm(inst_buf, inst_len, &in_rec, &out_rec, i, asm_file);
    write_snippets(&in_rec, &out_rec, i, snippets_file);

  cont:
    frame_record_clear(&in_rec);
    frame_record_clear(&out_rec);
  }

  fclose(asm_file);
  fclose(snippets_file);

  frame_record_cleanup(&in_rec);
  frame_record_cleanup(&out_rec);
  return 0;
}
