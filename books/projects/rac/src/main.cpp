#include <fstream>
#include <iostream>
#include <stdio.h>
#include <string>

#include "parser.h"

int
main (int argc, char **argv)
{
  ++argv, --argc; /* skip over program name */

  if (argc == 0)
    {
      std::cout
          << "Usage:\n"
             "  parse file           check that file.cpp is well formed\n"
             "  parse file -rac      convert to RAC pseudocode and write to "
             "file.pc\n\n"
             "  parse file -acl2     write ACL2 translation to "
             "output.lisp\n\n";
      return 0;
    }

  std::string buf (argv[0]);
  buf += ".i";
  yyin = fopen (buf.c_str (), "r");
  if (yyin == nullptr)
    {
      std::cerr << "Failed to open file " << buf << ": " << strerror (errno)
                << '\n';
      ;
      return 1;
    }

  yylineno = 1;
  if (yyparse ())
    {
      return 1;
    }

  fclose (yyin);

  // Restore basename
  buf.pop_back ();
  buf.pop_back ();

  if (prog.isEmpty ())
    puts ("Warning: no function definitions found,"
          " maybe you forgot the `// RAC begin` guard");

  std::fstream fout;

  if (argc > 1)
    {
      DispMode type;
      if (!strcmp (argv[1], "-acl2"))
        {
          buf += ".ast.lsp";
          type = DispMode::acl2;
        }
      else if (!strcmp (argv[1], "-rac"))
        {
          buf += ".pc";
          type = DispMode::rac;
        }
      else
        {
          std::cerr << "Unknown option `" << argv[1]
                    << "`, for a list of available options, type `parse`";
          return 1;
        }

      fout.open (buf, fstream::out);
      if (!fout.is_open ())
        std::cerr << "Failed to open file " << buf << ": " << strerror (errno)
                  << '\n';
      ;

      prog.display (fout, type);
    }
}
