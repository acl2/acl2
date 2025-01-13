// x86isa assembly snippet testing framework
//
// X86ISA Library
// Copyright (C) 2024 Kestrel Technology, LLC
//
// License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
//
// Author: Sol Swords (sswords@gmail.com)

#include "asmtest.h"
#include "snippets.h"
#include <argp.h>
#include <string.h>

const char *argp_program_version = "0.0.1";
const char *argp_program_bug_address = "<sswords@gmail.com>";

static const char doc[] =
  "help message placeholder";

static const char args_doc[] = "snippet_name";


static const struct argp_option options[] = {
  {"input", 'i',  "FILE", 0, "file of inputs for the snippet -- default name_ins.bin, required if name not provided"},
  {"output", 'o', "FILE", 0, "file to write snippet outputs to -- default name_out.bin, required if name not provided"},
  {"conf", 'c', "FILE", 0, "file to write test summary to -- default name.conf"},
  {"name", 'n', "NAME", 0, "names this test: sets defaults for input/output/conf files"},
  { 0 }
};

struct arguments {
  char *snippet;
  char *input;
  char *output;
  char *name;  
  char *conf;  
};

char *my_str_concat(const char *str1, const char *str2, const char *ctx) {
  int len1 = strlen(str1);
  int len2 = strlen(str2);
  char *res = (char *)malloc(len1+len2+1);
  if (!res) {
    fprintf(stderr, "Failed to allocate %s\n", ctx);
    exit(1);
  }
  strncpy(res, str1, len1);
  strncpy(res+len1, str2, len2);
  res[len1+len2]=(char)0;
  return res;
}
  
static error_t
parse_opt (int key, char *arg, struct argp_state *state) {

  struct arguments *arguments = state->input;
  switch(key) {
  case 'i': arguments->input  = arg; break;
  case 'o': arguments->output = arg; break;
  case 'c': arguments->conf = arg; break;
  case 'n': arguments->name = arg; break;
  case ARGP_KEY_ARG:
    if (arguments->snippet) {
      argp_usage(state);
    } else {
      arguments->snippet = arg;
    }
    break;
  case ARGP_KEY_END:
    if (!arguments->snippet || (!arguments->name && (!arguments->input || !arguments->output))) {
      argp_usage(state);
    }
    if (!arguments->input) {
      arguments->input = my_str_concat(arguments->name, "_ins.bin", "input filename buffer");
    }
    if (!arguments->output) {
      arguments->output = my_str_concat(arguments->name, "_out.bin", "output filename buffer");
    }
    if (arguments->name && !arguments->conf) {
      arguments->conf = my_str_concat(arguments->name, ".conf", "conf filename buffer");
    }
    break;
  default:
    return ARGP_ERR_UNKNOWN;
  }
  return 0;
}


static struct argp argp = { options, parse_opt, args_doc, doc };
int main (int argc, char* argv[]) {
  struct arguments arguments;
  arguments.snippet = NULL;
  arguments.input = NULL;
  arguments.output = NULL;
  arguments.name = NULL;
  arguments.conf = NULL;
  
  argp_parse(&argp, argc, argv, 0, 0, &arguments);

  FILE *infile = fopen(arguments.input, "r");
  if (infile == NULL) {
    fprintf(stderr, "Failed to open input file\n");
    exit(1);
  }
  FILE *outfile = fopen(arguments.output, "w");
  if (outfile == NULL) {
    fprintf(stderr, "Failed to open output file\n");
    exit(1);
  }

  const snippet_data *snip;
  int i;
  
  for (i=0; i<snippet_count; i++) {
    snip = &snippets[i];
    if (!strcmp(snip->name, arguments.snippet))
      break;
  }

  if (i==snippet_count) {
    fprintf(stderr, "Snippet named %s not found\n", arguments.snippet);
    exit(1);
  }

  void *indata = malloc(snip->input_size);
  if (indata == NULL) {
    fprintf(stderr, "Failed to allocate input data buffer\n");
    exit(1);
  }
  void *outdata = malloc(snip->output_size);
  if (outdata == NULL) {
    fprintf(stderr, "Failed to allocate output data buffer\n");
    exit(1);
  }
  while (1) {
    size_t count = fread(indata, snip->input_size, 1, infile);
    if (!count) break;

    snip->snippet(indata, outdata);

    count = fwrite(outdata, snip->output_size, 1, outfile);
    if (count != 1) {
      fprintf(stderr, "Failed to write to output file\n");
      exit(1);
    }
  }
  fclose(infile);
  fclose(outfile);

  if (arguments.conf) {
    FILE *conffile = fopen(arguments.conf, "w");
    if (conffile == NULL) {
      fprintf(stderr, "Failed to open conf file\n");
      exit(1);
    }
    fprintf(conffile, "snippet: %s\ninput: %s\noutput: %s\n", arguments.snippet, arguments.input, arguments.output);
    fclose(conffile);
  }
    
  
  exit(0);
  
}



