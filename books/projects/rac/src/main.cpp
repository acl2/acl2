#include <fstream>
#include <iostream>
#include <string.h>
#include <string>

#include "argparse.h"

#include "program/parser/parser.h"
#include "program/program.h"

int main(int argc, char **argv) {

  CommandLine cl;
  auto args = cl.parse(argc, argv);
  if (!args) {
    return 1;
  }

  if (!args->file) {
    return 0;
  }

  auto parsed_ast = parse(*args->file + ".i", args->trace_parser);
  if (!parsed_ast) {
    return 1;
  }

  auto processed_ast =
      Program::process(std::move(*parsed_ast), args->all_warnings);
  if (!processed_ast) {
    return 1;
  }

  if (args->dump_ast) {
    processed_ast->dumpAsDot();
  }

  if (args->mode) {
    const std::string ext = *args->mode == DispMode::acl2 ? ".ast.lsp" : ".pc";
    const std::string out = *args->file + ext;

    std::fstream fout;
    fout.open(out, std::fstream::out);
    if (!fout.is_open()) {
      std::cerr << "Failed to open file " << out << ": " << strerror(errno)
                << '\n';
    }

    processed_ast->display(fout, *args->mode);
  }

  return 0;
}
