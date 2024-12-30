#ifndef FWD_H
#define FWD_H

#define APPLY(CLASS, PARENT) class CLASS;
#include "astnodes.def"
#undef APPLY

class Type;
class PrimType;
class DefinedType;
class IntType;
class ArrayType;
class StructField;
class StructType;
class MvType;
class InitializerType;
class ErrorType;

#endif // FWD_H
