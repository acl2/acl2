// Hi-lock: (("[FF]ieldDeclaratorsRest:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[II]dentifier:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[MM]ethodOrFieldRest:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[MM]ethodOrFieldDecl:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[MM]ethodOrFieldDecl:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[MM]emberDecl:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[CC]lassBodyDeclaration:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[CC]lassBody:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[EE]lementValues:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[EE]lementValue:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[EE]lementValuePair:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[EE]lementValuePairs:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[AA]nnotationElement:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[AA]nnotations:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[MM]odifier: " (0 (quote hi-yellow) t)))
// Hi-lock: (("[BB]ound:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[TT]ypeParameter:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[TT]ypeParameters:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[TT]ypeArgumentsOrDiamond:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[TT]ypeList:" (0 (quote hi-yellow) t)))
// Hi-lock: (("[NN]onWildcardTypeArguments:" (0 (quote hi-yellow) t)))




M-s h l	highlight-lines-matching-regexp	Highlights all lines matching
a regular expression

If you create highlights interactively you can tell Emacs to insert
those patterns into the active buffer by running M-s h w.

Emacs will not highlight patterns found in a file automatically. You
must explicitly tell it to do so by manually invoking
M-x hi-lock-mode


Identifier:
    IDENTIFIER

QualifiedIdentifier:
    Identifier { . Identifier }

QualifiedIdentifierList:
    QualifiedIdentifier { , QualifiedIdentifier }

# not supporting annotations
CompilationUnit:
    [[Annotations] package QualifiedIdentifier ;]
                                {ImportDeclaration} {TypeDeclaration}

ImportDeclaration:
    import [static] Identifier { . Identifier } [. *] ;

TypeDeclaration:
    ClassOrInterfaceDeclaration
    ;

ClassOrInterfaceDeclaration:
    {Modifier} (ClassDeclaration | InterfaceDeclaration)

ClassDeclaration:
    NormalClassDeclaration
    EnumDeclaration

InterfaceDeclaration:
    NormalInterfaceDeclaration
    AnnotationTypeDeclaration


NormalClassDeclaration:
    class Identifier [TypeParameters]
                                [extends Type] [implements TypeList] ClassBody

EnumDeclaration:
    enum Identifier [implements TypeList] EnumBody

NormalInterfaceDeclaration:
    interface Identifier [TypeParameters] [extends TypeList] InterfaceBody

AnnotationTypeDeclaration:
    @ interface Identifier AnnotationTypeBody

Type:
    BasicType {[]}
    ReferenceType  {[]}

BasicType:
    byte
    short
    char
    int
    long
    float
    double
    boolean

ReferenceType:
    Identifier [TypeArguments] { . Identifier [TypeArguments] }

TypeArguments:
    < TypeArgument { , TypeArgument } >

# The use of [ and ] is as optional in java.g
TypeArgument:
    ReferenceType
    ? [ (extends | super) ReferenceType ]

NonWildcardTypeArguments:
    < TypeList >

TypeList:
    ReferenceType { , ReferenceType }



TypeArgumentsOrDiamond:
    < >
    TypeArguments

NonWildcardTypeArgumentsOrDiamond:
    < >
    NonWildcardTypeArguments



TypeParameters:
    < TypeParameter { , TypeParameter } >

TypeParameter:
    Identifier [extends Bound]

Bound:
    ReferenceType { & ReferenceType }

Modifier:
    Annotation
    public
    protected
    private
    static
    abstract
    final
    native
    synchronized
    transient
    volatile
    strictfp

# This one is so simple that we do not need an AnnotationRag.  It
# already is a Rag!
Annotations:
    Annotation {Annotation}

# Not really sure what is up with the [] below
Annotation:
    @ QualifiedIdentifier [ ( [AnnotationElement] ) ]

AnnotationElement:
    ElementValuePairs
    ElementValue

# Another case where we do not need a Rag
ElementValuePairs:
    ElementValuePair { , ElementValuePair }

ElementValuePair:
    Identifier = ElementValue

ElementValue:
    Annotation
    Expression1
    ElementValueArrayInitializer

# This one is done wrong, because it really needs to be converted to a
# Rag, and I do not know how to read it.  Flat out broken.  I could
# code the comma below, but it seems like it could lead to ambiguous
# parse trees.
ElementValueArrayInitializer:
    { [ElementValues] [,] }

# Do not need to create a Rag for this one, because it is easy to just
# write the equivalent grammar.
ElementValues:
    ElementValue { , ElementValue }

ClassBody:
    { { ClassBodyDeclaration } }

ClassBodyDeclaration:
    ;
    {Modifier} MemberDecl
    [static] Block

MemberDecl:
    MethodOrFieldDecl
    void Identifier VoidMethodDeclaratorRest
    Identifier ConstructorDeclaratorRest
    GenericMethodOrConstructorDecl
    ClassDeclaration
    InterfaceDeclaration

MethodOrFieldDecl:
    Type Identifier MethodOrFieldRest

MethodOrFieldRest:
    FieldDeclaratorsRest ;
    MethodDeclaratorRest

FieldDeclaratorsRest:
    VariableDeclaratorRest { , VariableDeclarator }


# this one was ugly, but I think I got it right
MethodDeclaratorRest:
    FormalParameters {[]} [throws QualifiedIdentifierList] (Block | ;)

VoidMethodDeclaratorRest:
    FormalParameters [throws QualifiedIdentifierList] (Block | ;)

ConstructorDeclaratorRest:
    FormalParameters [throws QualifiedIdentifierList] Block

GenericMethodOrConstructorDecl:
    TypeParameters GenericMethodOrConstructorRest

GenericMethodOrConstructorRest:
    (Type | void) Identifier MethodDeclaratorRest
    Identifier ConstructorDeclaratorRest

InterfaceBody:
    { { InterfaceBodyDeclaration } }

InterfaceBodyDeclaration:
    ;
    {Modifier} InterfaceMemberDecl

InterfaceMemberDecl:
    InterfaceMethodOrFieldDecl
    void Identifier VoidInterfaceMethodDeclaratorRest
    InterfaceGenericMethodDecl
    ClassDeclaration
    InterfaceDeclaration

InterfaceMethodOrFieldDecl:
    Type Identifier InterfaceMethodOrFieldRest

InterfaceMethodOrFieldRest:
    ConstantDeclaratorsRest ;
    InterfaceMethodDeclaratorRest

ConstantDeclaratorsRest:
    ConstantDeclaratorRest { , ConstantDeclarator }

ConstantDeclaratorRest:
    {[]} = VariableInitializer

ConstantDeclarator:
    Identifier ConstantDeclaratorRest

InterfaceMethodDeclaratorRest:
    FormalParameters {[]} [throws QualifiedIdentifierList] ;

VoidInterfaceMethodDeclaratorRest:
    FormalParameters [throws QualifiedIdentifierList] ;

InterfaceGenericMethodDecl:
    TypeParameters (Type | void) Identifier InterfaceMethodDeclaratorRest

FormalParameters:
    ( [FormalParameterDecls] )

FormalParameterDecls:
    {VariableModifier}  Type FormalParameterDeclsRest

VariableModifier:
    final
    Annotation

FormalParameterDeclsRest:
    VariableDeclaratorId [, FormalParameterDecls]
    ... VariableDeclaratorId



VariableDeclaratorId:
    Identifier {[]}



VariableDeclarators:
    VariableDeclarator { , VariableDeclarator }

VariableDeclarator:
    Identifier VariableDeclaratorRest

VariableDeclaratorRest:
    {[]} [ = VariableInitializer ]

VariableInitializer:
    ArrayInitializer
    Expression

# NOTIMPLEMENTED
ArrayInitializer:
    { [ VariableInitializer { , VariableInitializer } [,] ] }

# I am making a very strange judgement call for Block and
# BlockStatements.  I am assuming that the brackets in Block are because
# programmers can use brackets.  And, I am assuming that the brackets in
# BlockStatements are of the notation like [], (|), and {}.  If I am
# right about that it, would mean that the Oracle Syntax is ambiguous.
# It is hard to imagine that such a large product would have such
# ambiguous syntax, so I concede that it is more likely that I am
# wrong.  However, I do not currently have a way of determining the
# right intepretation without experimenting.  Thus, we continue the experiment.

Block:
    { BlockStatements }

BlockStatements:
    { BlockStatement }

BlockStatement:
    LocalVariableDeclarationStatement
    ClassOrInterfaceDeclaration
    [Identifier :] Statement

LocalVariableDeclarationStatement:
    { VariableModifier }  Type VariableDeclarators ;

# Interpreted the { } in switch as literals
Statement:
    Block
    ;
    Identifier : Statement
    StatementExpression ;
    if ParExpression Statement [else Statement]
    assert Expression [: Expression] ;
    switch ParExpression { SwitchBlockStatementGroups }
    while ParExpression Statement
    do Statement while ParExpression ;
    for ( ForControl ) Statement
    break [Identifier] ;
    continue [Identifier] ;
    return [Expression] ;
    throw Expression ;
    synchronized ParExpression Block
    try Block (Catches | [Catches] Finally)
    try ResourceSpecification Block [Catches] [Finally]

StatementExpression:
    Expression

# Intepreted the { } below as non-literals based on knowledge of Java
Catches:
    CatchClause { CatchClause }

CatchClause:
    catch ( {VariableModifier} CatchType Identifier ) Block

# Need to tease apart vertical bars, amperstands, and other dilineators in 
# thing that preprocesses characters
# The way I resolved this in oracle-grammar.txt should be fine
CatchType:
    QualifiedIdentifier { | QualifiedIdentifier }

Finally:
    finally Block

ResourceSpecification:
    ( Resources [;] )

Resources:
    Resource { ; Resource }

Resource:
    {VariableModifier} ReferenceType VariableDeclaratorId = Expression

SwitchBlockStatementGroups:
    { SwitchBlockStatementGroup }

SwitchBlockStatementGroup:
    SwitchLabels BlockStatements

SwitchLabels:
    SwitchLabel { SwitchLabel }

SwitchLabel:
    case Expression :
    case EnumConstantName :
    default :

EnumConstantName:
    Identifier



ForControl:
    ForVarControl
    ForInit ; [Expression] ; [ForUpdate]

ForVarControl:
    {VariableModifier} Type VariableDeclaratorId  ForVarControlRest

# We translate the below use of ForVariableDeclaratorsRest
# differently
ForVarControlRest:
    ForVariableDeclaratorsRest ; [Expression] ; [ForUpdate]
    : Expression

ForVariableDeclaratorsRest:
    [= VariableInitializer] { , VariableDeclarator }

# not sure I did ForInit correctly
ForInit:
ForUpdate:
    StatementExpression { , StatementExpression }

Expression:
    Expression1 [AssignmentOperator Expression1]

AssignmentOperator:
    =
    +=
    -=
    *=
    /=
    &=
    |=
    ^=
    %=
    <<=
    >>=
    >>>=

Expression1:
    Expression2 [Expression1Rest]

Expression1Rest:
    ? Expression : Expression1

Expression2:
    Expression3 [Expression2Rest]

# Another example of the "rag" approach.
Expression2Rest:
    { InfixOp Expression3 }
    instanceof Type

InfixOp:
    ||
    &&
    |
    ^
    &
    ==
    !=
    <
    >
    <=
    >=
    <<
    >>
    >>>
    +
    -
    *
    /
    %

# I did this one correctly. It is a good example to follow for dealing
# with curly braces.  I picked the word "rag", because it is unlikely
# to be used elsewhere.
Expression3:
    PrefixOp Expression3
    ( (Expression | Type) ) Expression3
    Primary { Selector } { PostfixOp }

PrefixOp:
    ++
    --
    !
    ~
    +
    -

PostfixOp:
    ++
    --

# I skipped the Identifier and BasicType lines
Primary:
    Literal
    ParExpression
    this [Arguments]
    super SuperSuffix
    new Creator
    NonWildcardTypeArguments (ExplicitGenericInvocationSuffix | this Arguments)
    Identifier { . Identifier } [IdentifierSuffix]
    BasicType {[]} . class
    void . class



Literal:
    IntegerLiteral
    FloatingPointLiteral
    CharacterLiteral
    StringLiteral
    BooleanLiteral
    NullLiteral

ParExpression:
    ( Expression )

# skipping for now
Arguments:
    ( [ Expression { , Expression } ] )

SuperSuffix:
    Arguments
    . Identifier [Arguments]

ExplicitGenericInvocationSuffix:
    super SuperSuffix
    Identifier Arguments

Creator:
    NonWildcardTypeArguments CreatedName ClassCreatorRest
    CreatedName (ClassCreatorRest | ArrayCreatorRest)

CreatedName:
    Identifier [TypeArgumentsOrDiamond] { . Identifier [TypeArgumentsOrDiamond] }

ClassCreatorRest:
    Arguments [ClassBody]

ArrayCreatorRest:
    [ (] {[]} ArrayInitializer  |  Expression ] {[ Expression ]} {[]})

# skipping for now
IdentifierSuffix:
    [ ({[]} . class | Expression) ]
    Arguments
    . (class | ExplicitGenericInvocation | this | super Arguments |
                                new [NonWildcardTypeArguments] InnerCreator)

ExplicitGenericInvocation:
    NonWildcardTypeArguments ExplicitGenericInvocationSuffix

InnerCreator:
    Identifier [NonWildcardTypeArgumentsOrDiamond] ClassCreatorRest


# The use of [ Expression ] below is dangerous, because it really
# means that Selector should be able to resolve to an empty string,
# which we do not currently have a way of specifying
Selector:
    . Identifier [Arguments]
    . ExplicitGenericInvocation
    . this
    . super SuperSuffix
    . new [NonWildcardTypeArguments] InnerCreator
    [ Expression ]

# referenced java.g to get this one
EnumBody:
    { [EnumConstants] [,] [EnumBodyDeclarations] }

# this rule is written backwards.  I fixed it
EnumConstants:
    EnumConstant
    EnumConstants , EnumConstant

EnumConstant:
    [Annotations] Identifier [Arguments] [ClassBody]

# It is weird that this rule can resolve to a single semi-colon
EnumBodyDeclarations:
    ; {ClassBodyDeclaration}



AnnotationTypeBody:
    { [AnnotationTypeElementDeclarations] }

AnnotationTypeElementDeclarations:
    AnnotationTypeElementDeclaration
    AnnotationTypeElementDeclarations AnnotationTypeElementDeclaration

AnnotationTypeElementDeclaration:
    {Modifier} AnnotationTypeElementRest

AnnotationTypeElementRest:
    Type Identifier AnnotationMethodOrConstantRest ;
    ClassDeclaration
    InterfaceDeclaration
    EnumDeclaration
    AnnotationTypeDeclaration

AnnotationMethodOrConstantRest:
    AnnotationMethodRest
    ConstantDeclaratorsRest

AnnotationMethodRest:
    ( ) [[]] [default ElementValue]
