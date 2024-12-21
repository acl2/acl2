// x86isa assembly snippet testing framework
//
// X86ISA Library
// Copyright (C) 2024 Kestrel Technology, LLC
//
// License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
//
// Author: Sol Swords (sswords@gmail.com)

#ifndef SNIPPETS_TYPE_H
#define SNIPPETS_TYPE_H

#include <stdlib.h>
typedef struct {
  char *name;
  size_t input_size;
  size_t output_size;
  void (*snippet)(void *input_data, void *output_data);
} snippet_data;


#endif
