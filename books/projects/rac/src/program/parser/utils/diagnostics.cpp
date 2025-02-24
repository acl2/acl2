#include "diagnostics.h"
#include "utils.h"

#include <cassert>

std::ostream &operator<<(std::ostream &os, const Location &loc) {

  os << loc.file_name << ':';

  os << loc.first_line;
  if (loc.first_line != loc.last_line)
    os << '-' << loc.last_line;

  os << " (" << loc.first_column << '-' << loc.last_column << "):";

  return os;
}

void DiagnosticHandler::show_code_at(const Location &context,
                                     const Location &error) {

  assert(file_ &&
         "DiagnosticHandler::setup should be called before with a valid "
         "pointer");

  long saved_pos = std::ftell(file_);

  // f_pos is the begining of the first token of context. We recover the
  // begining of the line to display the code.
  long cur_pos = context.f_pos - context.first_column;

  // Move the cursor to the begin of the area we need to report.
  assert(fseek(file_, cur_pos, SEEK_SET) == 0);

  char *buffer = nullptr;
  size_t size = 0;

  // By default, we show all the context...
  int first_line_to_display = context.first_line;
  int last_line_to_display = context.last_line;

  // ... but if it is too long, we only show the error...
  if (last_line_to_display - first_line_to_display > 5) {
    first_line_to_display = error.first_line;
    last_line_to_display = error.last_line;
    // Move the cursor to the begin of the area we need to report.
    cur_pos = error.f_pos - error.first_column;
    assert(fseek(file_, cur_pos, SEEK_SET) == 0);
  }

  // ... unless if it is also too big, in that case we only show the first 5
  // lines.
  if (last_line_to_display - first_line_to_display > 5) {
    std::cerr << "(Too much context, show only the 5 first lines)\n";
    last_line_to_display = first_line_to_display + 5;
  }

  for (int line = first_line_to_display; line <= last_line_to_display; ++line) {
    // Display the code.
    size = getline(&buffer, &size, file_);
    cur_pos += size;
    std::string lno_str = std::to_string(line);
    std::cerr << format(" %s | %s", lno_str.c_str(), buffer);

    // If we are not in the part responsible for the error, skip the rest.
    if (line < error.first_line || line > error.last_line) {
      continue;
    }

    std::cerr << std::string(lno_str.length(), ' ') << "  | ";

    int col = 0;
    if (line == error.first_line) {
      for (; col < error.first_column; ++col) {
        std::cerr << ' ';
      }
    }

    int stop_at;
    if (line == error.last_line) {
      stop_at = error.last_column;
    } else {
      stop_at = size;
    }

    for (; col < stop_at; ++col) {
      std::cerr << '^';
    }

    std::cerr << '\n';
  }

  std::free(buffer);
  assert(std::fseek(file_, saved_pos, SEEK_SET) == 0);
}

void DiagnosticHandler::Diagnostic::report() {

  std::cout << std::flush;

  if (!dh_.first_error_reported_)
    std::cerr << '\n';
  dh_.first_error_reported_ = false;

  std::cerr << error_loc_ << ' ' << error_msg_ << '\n';

  dh_.show_code_at(context_.value_or(error_loc_), error_loc_);

  if (note_msg_) {
    std::cerr << "note: " << note_msg_->get() << '\n';
  }

  if (note_loc_) {
    dh_.show_code_at(note_loc_->get(), *note_loc_);
  }
}
