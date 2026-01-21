#ifndef NODES_ID_H
#define NODES_ID_H

#include <cassert>
#include <type_traits>

#define APPLY(CLASS, _) class CLASS;
#include "astnodes.def"
#include "types.def"
#undef APPLY

// Enumeration representing each AST node type (used for the visitor dispatch).
enum class NodesId {
#define APPLY(CLASS, _) CLASS,
#include "astnodes.def"
#include "types.def"
#undef APPLY
};

// Return the type of a node.
template <typename NodeType> constexpr NodesId idOf(const NodeType *) {
  if constexpr (false) {
  }
#define APPLY(CLASS, _)                                                        \
  else if constexpr (std::is_same_v<NodeType, CLASS>) return NodesId::CLASS;
#include "astnodes.def"
#include "types.def"
#undef APPLY
  else
    assert(!"Unknown type");
}

#endif // NODES_ID_H
