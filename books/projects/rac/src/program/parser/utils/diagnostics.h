#ifndef DIAGNOSTICS_H
#define DIAGNOSTICS_H

#include <iostream>
#include <optional>
#include <string>

class Expression;
class Statement;

struct Location {

  inline static Location from_file(const std::string &f) {
    return Location{0, 0, 0, 0, 0, 0, f};
  }

  // Used for AST nodes which don't have a clear location (and where it should
  // not matter !!).
  inline static Location dummy() {
    return Location{-1, -1, -1, -1, -1, -1, ""};
  }

  int first_line, last_line, first_column, last_column;
  // Position relative to the begining of the file.
  long f_pos, f_pos_end;

  // TODO replace this by the string view ?
  std::string file_name;

  friend std::ostream &operator<<(std::ostream &os, const Location &loc);
};

class DiagnosticHandler {

public:
  DiagnosticHandler() = default;
  DiagnosticHandler(const DiagnosticHandler &) = delete;
  DiagnosticHandler(DiagnosticHandler &&other) : file_(other.file_) {
    other.file_ = nullptr;
  }

  ~DiagnosticHandler() {
    if (file_)
      std::fclose(file_);
  }

  class Diagnostic {
  public:
    [[nodiscard]] Diagnostic &context(const Location &loc) {
      context_ = loc;
      return *this;
    }

    [[nodiscard]] Diagnostic &note(const std::string &msg) {
      note_msg_ = {msg};
      return *this;
    }

    [[nodiscard]] Diagnostic &note_location(const Location &loc) {
      note_loc_ = {loc};
      return *this;
    }

    void report();

    friend DiagnosticHandler;

  private:
    Diagnostic(DiagnosticHandler &dh, const Location &loc,
               const std::string &msg)
        : dh_(dh), error_loc_(loc), error_msg_(msg) {}

    DiagnosticHandler &dh_;

    const Location &error_loc_;
    const std::string &error_msg_;

    std::optional<std::reference_wrapper<const Location>> context_;
    std::optional<std::reference_wrapper<const Location>> note_loc_;
    std::optional<std::reference_wrapper<const std::string>> note_msg_;
  };

  void setup(FILE *f) { file_ = f; }

  // TODO
  // enum class Severity { Error, Warning };
  // #define ERROR_NAME_IMPL() __FILE_NAME__[0] + std::to_string(__COUNTER__)

  [[nodiscard]] Diagnostic new_error(const Location &loc,
                                     const std::string &msg) {
    return Diagnostic(*this, loc, msg);
  }

private:
  // Display the code at context and highlight the are delimited by error
  // like that:
  //
  //  4 | context context error context
  //    |                 ^^^^^
  //
  // The error location should be inside or equal to the area delimited by
  // context.
  void show_code_at(const Location &context, const Location &error);

  FILE *file_ = nullptr;
  // If it is not the first error, we add a new line between error messages.
  bool first_error_reported_ = true;
};

#endif // DIAGNOSTICS_H
