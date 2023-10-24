#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Host.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <queue>
#include <string.h>
#include <string>
#include <system_error>
#include <utility>
#include <vector>

using namespace llvm;
using namespace llvm::sys;

FILE *pFile;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns one of these for known things.
enum TOKEN_TYPE
{

  IDENT = -1,        // [a-zA-Z_][a-zA-Z_0-9]*
  ASSIGN = int('='), // '='

  // delimiters
  LBRA = int('{'),  // left brace
  RBRA = int('}'),  // right brace
  LPAR = int('('),  // left parenthesis
  RPAR = int(')'),  // right parenthesis
  SC = int(';'),    // semicolon
  COMMA = int(','), // comma

  // types
  INT_TOK = -2,   // "int"
  VOID_TOK = -3,  // "void"
  FLOAT_TOK = -4, // "float"
  BOOL_TOK = -5,  // "bool"

  // keywords
  EXTERN = -6,  // "extern"
  IF = -7,      // "if"
  ELSE = -8,    // "else"
  WHILE = -9,   // "while"
  RETURN = -10, // "return"
  // TRUE   = -12,     // "true"
  // FALSE   = -13,     // "false"

  // literals
  INT_LIT = -14,   // [0-9]+
  FLOAT_LIT = -15, // [0-9]+.[0-9]+
  BOOL_LIT = -16,  // "true" or "false" key words

  // logical operators
  AND = -17, // "&&"
  OR = -18,  // "||"

  // operators
  PLUS = int('+'),    // addition or unary plus
  MINUS = int('-'),   // substraction or unary negative
  ASTERIX = int('*'), // multiplication
  DIV = int('/'),     // division
  MOD = int('%'),     // modular
  NOT = int('!'),     // unary negation

  // comparison operators
  EQ = -19,      // equal
  NE = -20,      // not equal
  LE = -21,      // less than or equal to
  LT = int('<'), // less than
  GE = -23,      // greater than or equal to
  GT = int('>'), // greater than

  // special tokens
  EOF_TOK = 0, // signal end of file

  // invalid
  INVALID = -100 // signal invalid token
};

// TOKEN struct is used to keep track of information about a token
struct TOKEN
{
  int type = -100;
  std::string lexeme;
  int lineNo;
  int columnNo;
};

static std::string IdentifierStr; // Filled in if IDENT
static int IntVal;                // Filled in if INT_LIT
static bool BoolVal;              // Filled in if BOOL_LIT
static float FloatVal;            // Filled in if FLOAT_LIT
static std::string StringVal;     // Filled in if String Literal
static int lineNo, columnNo;

static TOKEN returnTok(std::string lexVal, int tok_type)
{
  TOKEN return_tok;
  return_tok.lexeme = lexVal;
  return_tok.type = tok_type;
  return_tok.lineNo = lineNo;
  return_tok.columnNo = columnNo - lexVal.length() - 1;
  return return_tok;
}

// Read file line by line -- or look for \n and if found add 1 to line number
// and reset column number to 0
/// gettok - Return the next token from standard input.
static TOKEN gettok()
{

  static int LastChar = ' ';
  static int NextChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar))
  {
    if (LastChar == '\n' || LastChar == '\r')
    {
      lineNo++;
      columnNo = 1;
    }
    LastChar = getc(pFile);
    columnNo++;
  }

  if (isalpha(LastChar) ||
      (LastChar == '_'))
  { // identifier: [a-zA-Z_][a-zA-Z_0-9]*
    IdentifierStr = LastChar;
    columnNo++;

    while (isalnum((LastChar = getc(pFile))) || (LastChar == '_'))
    {
      IdentifierStr += LastChar;
      columnNo++;
    }

    if (IdentifierStr == "int")
      return returnTok("int", INT_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "float")
      return returnTok("float", FLOAT_TOK);
    if (IdentifierStr == "void")
      return returnTok("void", VOID_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "extern")
      return returnTok("extern", EXTERN);
    if (IdentifierStr == "if")
      return returnTok("if", IF);
    if (IdentifierStr == "else")
      return returnTok("else", ELSE);
    if (IdentifierStr == "while")
      return returnTok("while", WHILE);
    if (IdentifierStr == "return")
      return returnTok("return", RETURN);
    if (IdentifierStr == "true")
    {
      BoolVal = true;
      return returnTok("true", BOOL_LIT);
    }
    if (IdentifierStr == "false")
    {
      BoolVal = false;
      return returnTok("false", BOOL_LIT);
    }

    return returnTok(IdentifierStr.c_str(), IDENT);
  }

  if (LastChar == '=')
  {
    NextChar = getc(pFile);
    if (NextChar == '=')
    { // EQ: ==
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("==", EQ);
    }
    else
    {
      LastChar = NextChar;
      columnNo++;
      return returnTok("=", ASSIGN);
    }
  }

  if (LastChar == '{')
  {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("{", LBRA);
  }
  if (LastChar == '}')
  {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("}", RBRA);
  }
  if (LastChar == '(')
  {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("(", LPAR);
  }
  if (LastChar == ')')
  {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(")", RPAR);
  }
  if (LastChar == ';')
  {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(";", SC);
  }
  if (LastChar == ',')
  {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(",", COMMA);
  }

  if (isdigit(LastChar) || LastChar == '.')
  { // Number: [0-9]+.
    std::string NumStr;

    if (LastChar == '.')
    { // Floatingpoint Number: .[0-9]+
      do
      {
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      FloatVal = strtof(NumStr.c_str(), nullptr);
      return returnTok(NumStr, FLOAT_LIT);
    }
    else
    {
      do
      { // Start of Number: [0-9]+
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      if (LastChar == '.')
      { // Floatingpoint Number: [0-9]+.[0-9]+)
        do
        {
          NumStr += LastChar;
          LastChar = getc(pFile);
          columnNo++;
        } while (isdigit(LastChar));

        FloatVal = strtof(NumStr.c_str(), nullptr);
        return returnTok(NumStr, FLOAT_LIT);
      }
      else
      { // Integer : [0-9]+
        IntVal = strtod(NumStr.c_str(), nullptr);
        return returnTok(NumStr, INT_LIT);
      }
    }
  }

  if (LastChar == '&')
  {
    NextChar = getc(pFile);
    if (NextChar == '&')
    { // AND: &&
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("&&", AND);
    }
    else
    {
      LastChar = NextChar;
      columnNo++;
      return returnTok("&", int('&'));
    }
  }

  if (LastChar == '|')
  {
    NextChar = getc(pFile);
    if (NextChar == '|')
    { // OR: ||
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("||", OR);
    }
    else
    {
      LastChar = NextChar;
      columnNo++;
      return returnTok("|", int('|'));
    }
  }

  if (LastChar == '!')
  {
    NextChar = getc(pFile);
    if (NextChar == '=')
    { // NE: !=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("!=", NE);
    }
    else
    {
      LastChar = NextChar;
      columnNo++;
      return returnTok("!", NOT);
      ;
    }
  }

  if (LastChar == '<')
  {
    NextChar = getc(pFile);
    if (NextChar == '=')
    { // LE: <=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("<=", LE);
    }
    else
    {
      LastChar = NextChar;
      columnNo++;
      return returnTok("<", LT);
    }
  }

  if (LastChar == '>')
  {
    NextChar = getc(pFile);
    if (NextChar == '=')
    { // GE: >=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok(">=", GE);
    }
    else
    {
      LastChar = NextChar;
      columnNo++;
      return returnTok(">", GT);
    }
  }

  if (LastChar == '/')
  { // could be division or could be the start of a comment
    LastChar = getc(pFile);
    columnNo++;
    if (LastChar == '/')
    { // definitely a comment
      do
      {
        LastChar = getc(pFile);
        columnNo++;
      } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

      if (LastChar != EOF)
        return gettok();
    }
    else
      return returnTok("/", DIV);
  }

  // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF)
  {
    columnNo++;
    return returnTok("0", EOF_TOK);
  }

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  std::string s(1, ThisChar);
  LastChar = getc(pFile);
  columnNo++;
  return returnTok(s, int(ThisChar));
}

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static TOKEN CurTok;
static std::deque<TOKEN> tok_buffer;

static TOKEN getNextToken()
{

  if (tok_buffer.size() == 0)
    tok_buffer.push_back(gettok());

  TOKEN temp = tok_buffer.front();
  tok_buffer.pop_front();

  return CurTok = temp;
}

static void putBackToken(TOKEN tok) { tok_buffer.push_front(tok); }

static void eatEverythingElse() {
  printf("Running on empty...\n");
  while(CurTok.type != EOF_TOK) {
    getNextToken();
  }
}

// Parser Error method
static void parserErr(std::string production, std::string expected) {
  std::string header = "-------------------------------ERROR LOG-------------------------------";
  std::string footer = "-----------------------------------------------------------------------";
  fprintf(stderr,
          "%s\nRow Number: %d, Column Number: %d, Production: %s\nGot: %s\nExpected: %s\n%s\n",
          header.c_str(),
          CurTok.lineNo, CurTok.columnNo, production.c_str(),
          CurTok.lexeme.c_str(),
          expected.c_str(), 
          footer.c_str()
  );
  exit(1);
}


// Parser Success method
static void parserSuccess(std::string production) {
  fprintf(stdout,
          "Parsed Token: %s :at Production: %s\n", CurTok.lexeme.c_str(),
          production.c_str());
}

//===----------------------------------------------------------------------===//
// AST nodes
//===----------------------------------------------------------------------===//

/// ASTnode - Base class for all AST nodes.
class ASTnode
{
public:
  virtual ~ASTnode() {}
  virtual Value *codegen() = 0;
  virtual std::string to_string() const {};
};

/// IntASTnode - Class for integer literals like 1, 2, 10,
class IntASTnode : public ASTnode
{
  int Val;

public:
  IntASTnode(int val) : Val(val) {}
  virtual Value *codegen() override;
  // virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};

// // FloatASTnode - Class for float literals like 1.0, 2.0, 10.0
// class FloatASTnode : public ASTnode {
//   double Val;

// public:
//   FloatASTnode(double Val) :Val(Val) {}
//   virtual Value *codegen() override; 
// };

// //BoolASTnode - Class for boolean literals
// class BoolASTnode : public ASTnode {
//   bool Bool;

//   public:
//     BoolASTnode(bool Bool) : Bool(Bool) {}
//     virtual Value *codegen() override;
// };

// // VariableASTnode - Class for identifiers 
// class VariableASTnode : public ASTnode
// {
//   std::string Val;

// public:
//   VariableASTnode(const std::string &val) : Val(val) {}
//   virtual Value *codegen() override;
// };

// // BinaryASTnode - Class for binary
// class BinaryASTnode : public ASTnode {
//   std::unique_ptr<ASTnode> LHS;
//   std::string Op;
//   std::unique_ptr<ASTnode> RHS;

// public:
//   BinaryASTnode(const std::string &Op, std::unique_ptr<ASTnode> LHS,
//                 std::unique_ptr<ASTnode> RHS)
//       :Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}
//   virtual Value *codegen() override;
// };

// // UnaryASTnode - Class for unary
// class UnaryASTnode : public ASTnode {
//   std::string Op;
//   std::unique_ptr<ASTnode> Val;

// public:
//   UnaryASTnode(const std::string &Op, std::unique_ptr<ASTnode> Val)
//       :Op(Op), Val(std::move(Val)) {}
//   virtual Value *codegen() override;
// };

// // ArgsASTnode - Code for args
// class ArgsASTnode : public ASTnode {
//   std::vector<std::unique_ptr<ASTnode>> ArgList;

// public:
//   ArgsASTnode(std::vector<std::unique_ptr<ASTnode>> argList) 
//   : ArgList(std::move(argList)) {}
//   virtual Value *codegen() override;
// };

// // CallExprASTnode - Code for function calls
// class CallExprASTnode : public ASTnode {
//   std::string Callee;
//   std::unique_ptr<ArgsASTnode> Args;

// public:
//   CallExprASTnode(const std::string &Callee,
//               std::unique_ptr<ArgsASTnode> Args)
//       : Callee(Callee), Args(std::move(Args)) {}
//   virtual Value *codegen() override;
// };


// // LocalDeclASTnode - calls for localDecl function calls
// class LocalDeclASTnode : public ASTnode {
//   std::string VarType;
//   std::string Identifier;

//   public:
//     LocalDeclASTnode(const std::string &varType,
//               std::string &identifier)
//       : VarType(varType), Identifier(identifier) {}
//   virtual Value *codegen() override;
// };

// // ReturnStmtASTnode - call for return statements
// class ReturnStmtASTnode : public ASTnode {
//   std::unique_ptr<ASTnode> Expr;
//   public:
//     ElseStmtASTnode(std::unique_ptr<ASTnode> expr) : Expr(std::move(expr));
//   virtual Value *codegen() override;
// }

// // IftStmtASTnode - calls for If statement calls
// class IfStmtASTnode : public ASTnode {
//   std::unique_ptr<ASTnode> Expr;
//   std::unique_ptr<BlockASTnode> Block;
//   std::unique_ptr<BlockASTnode> ElseStmt;

//   public:
//     IfStmtASTnode(std::unique_ptr<ASTnode> expr, 
//               std::unique_ptr<BlockASTnode> block, std::unique_ptr<BlockASTnode> elseStmt)
//       : Expr(std::move(expr)), Block(std::move(block)), ElseStmt(std::move(elseStmt)) {}
//   virtual Value *codegen() override;
// };

// // WhileStmtASTnode - calls for While statemnt calls
// class WhileStmtASTnode : public ASTnode {
//   std::unique_ptr<ASTnode> Expr;
//   std::unique_ptr<ASTnode> Stmt;

//   public:
//     WhileStmtASTnode(std::unique_ptr<ASTnode> expr, std::unique_ptr<ASTnode> stmt)
//       : Expr(std::move(expr)), Stmt(std::move(stmt)) {}
//       virtual Value *codegen() override;
// }

// // BlockASTnode - code for Block calls
// class BlockASTnode : public ASTnode {
//   std::vector<std::unique_ptr<LocalDeclASTnode>> LocalDecls;
//   std::vector<std::unique_ptr<ASTnode>> StmtList;

//   public:
//     BlockASTnode(std::vector<std::unique_ptr<LocalDeclASTnode>> localDecls,
//               std::vector<std::unique_ptr<ASTnode>> stmtList)
//       : LocalDecls(localDecls), StmtList(stmtList) {}
//   virtual Value *codegen() override;
// };

// /// PrototypeAST - This class represents the "prototype" for a function,
// /// which captures its name, and its argument names (thus implicitly the number
// /// of arguments the function takes).
// class PrototypeASTnode : public ASTnode {
//   std::string Name;
//   std::vector<std::string> Args;

// public:
//   PrototypeASTnode(const std::string &Name, std::vector<std::string> Args)
//       : Name(Name), Args(std::move(Args)) {}
   
//   virtual Value *codegen() override;

//   const std::string &getName() const { return Name; }
// };

// // FunctionAST - This class represents a function definition itself.
// class FunctionAST : public ASTnode {
//   std::unique_ptr<PrototypeAST> Proto;
//   std::unique_ptr<ASTnode> Body;

// public:
//   FunctionASTnode(std::unique_ptr<PrototypeAST> Proto,
//               std::unique_ptr<ASTnode> Body)
//       : Proto(std::move(Proto)), Body(std::move(Body)) {}

//   virtual Value *codegen() override;
// };

/* add other AST nodes as nessasary */

//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

/* Add function calls for each production */

/** DELCARATIONS FOR LOOPING FUNCTIONS **/


static void stmt();
static void localDecls();
static void stmtList();
static void expr();
static void argBlock();


/** PRODUCTIONS **/

/*
  literal ::= INT_LIT 
  | FLOAT_LIT 
  | BOOL_LIT
*/
static void literal() {
  std::string production = "literal";
  if(
    CurTok.type == INT_LIT
    || CurTok.type == FLOAT_LIT
    || CurTok.type == BOOL_LIT
  ) {
    parserSuccess(production);
    getNextToken(); // eat INT_LIT / FLOAT_LIT / BOOL_LIT 
    return;
  } else {
    parserErr(production, "INT_LIT, FLOAT_LIT, BOOL_LIT");
  }
}

/*
  arg_list ::= "," expr arg_list
  | epsilon
*/
static void argList() {
  std::string production = "argList";
  std::string first = "COMMA, IDENT, (, -, !, INT_LIT, FLOAT_LIT, BOOL_LIT";
  std::string follow = ")";
  if(CurTok.type == COMMA) {
    parserSuccess(production);
    getNextToken(); // eat ","

    expr();

    argList();

    return;

  } else if (CurTok.type != RPAR) {
    parserErr(production, first + ", " + follow);
  }
}

/*
  args ::= expr arg_list
  | epsilon
*/
static void args() {
  std::string production = "args";
  std::string first = "IDENT, (, -, !, INT_LIT, FLOAT_LIT, BOOL_LIT";
  std::string follow = ")";
  std::vector<std::unique_ptr<ASTnode>> listOfArgs;
  if(
    CurTok.type == IDENT
    || CurTok.type == LPAR
    || CurTok.type == MINUS
    || CurTok.type == NOT
    || CurTok.type == INT_LIT
    || CurTok.type == FLOAT_LIT
    || CurTok.type == BOOL_LIT
  ) {

    expr();

    argList();

    return;

  } else if (CurTok.type != RPAR) {
    parserErr(production, first + ", " + follow);
  }
}


/*
  arg_block ::= "(" args ")" 
  | epsilon
*/
static void argBlock() {
  std::string production = "argBlock";
  std::string first = "(";
  std::string follow = "), ;, COMMA, ||, &&, ==, !=, <=, <, >=, >, +, -, *, /, %, INT_LIT, FLOAT_LIT, BOOL_LIT";
  std::string expected[] = {first + ", " + follow, ")"};
  int errIndex = 0;
  if(CurTok.type == LPAR) {
    parserSuccess(production);
    getNextToken(); // eat "("
    errIndex++;
    
    args();

    if(CurTok.type == RPAR) {
      parserSuccess(production);
      getNextToken(); // eat ")"
      return;
    }
  } else if(
    CurTok.type != IDENT
    && CurTok.type != LPAR
    && CurTok.type != RPAR
    && CurTok.type != SC
    && CurTok.type != COMMA
    && CurTok.type != OR
    && CurTok.type != AND
    && CurTok.type != EQ
    && CurTok.type != NE
    && CurTok.type != LE
    && CurTok.type != LT
    && CurTok.type != GE
    && CurTok.type != GT
    && CurTok.type != MINUS
    && CurTok.type != PLUS
    && CurTok.type != ASTERIX
    && CurTok.type != DIV
    && CurTok.type != MOD
    && CurTok.type != INT_LIT
    && CurTok.type != FLOAT_LIT
    && CurTok.type != BOOL_LIT
  ) {
    parserErr(production, expected[errIndex]);
  }
}

/*
  identifier ::= IDENT arg_block
  | literal 
*/
static void identifier() {
  std::string production = "identifier";
  std::string first = "IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT";
  if(CurTok.type == IDENT) {
    parserSuccess(production);
    getNextToken(); // eat IDENT

    argBlock();

  } else if(
    CurTok.type == INT_LIT
    || CurTok.type == FLOAT_LIT
    || CurTok.type == BOOL_LIT
  ) {
    literal();
  } else {
    parserErr(production, first);
  }
}

/*
  bracketed_expr ::= "(" expr ")"
  | identifier
*/
static void bracketedExpr() {
  std::string production = "bracketedExpr";
  std::string first = "(, INT_LIT, FLOAT_LIT, BOOL_LIT";
  std::string expected[2] = {first, ")"};
  int errIndex = 0;
  if(CurTok.type == LPAR) {
    parserSuccess(production);
    getNextToken(); // eat "("
    errIndex++;

    expr();

    if(CurTok.type == RPAR) {
      parserSuccess(production);
      getNextToken(); // eat ")"

      return;
    }
  } else if(
    CurTok.type == IDENT
    || CurTok.type == INT_LIT
    || CurTok.type == FLOAT_LIT
    || CurTok.type == BOOL_LIT
  ) {

    identifier(); 
    return;
  }

  parserErr(production, expected[errIndex]);
}

/*
  unary ::= "-" bracketed_expr 
  | "!" bracketed_expr
  | bracketed_expr
*/
static void unary() {
  std::string production = "unary";
  std::string first = "IDENT, (, -, !, INT_LIT, FLOAT_LIT, BOOL_LIT";
  if(
    CurTok.type == MINUS
    || CurTok.type == NOT
  ) {
    parserSuccess(production);
    getNextToken(); // eat "-" / "!"

    bracketedExpr();
    return;

  } else if(
    CurTok.type == IDENT
    || CurTok.type == LPAR
    || CurTok.type == INT_LIT
    || CurTok.type == FLOAT_LIT
    || CurTok.type == BOOL_LIT
  ) {
    bracketedExpr();
    return;
  } else {
    parserErr(production, first);
  }
}

/*
  term ::= "*" unary term
  | "/" unary term
  | "%" unary term
  | epsilon
*/
static void term() {
  std::string production = "term";
  std::string first = "*, /, %";
  std::string follow = "), ;, COMMA, ||, &&, ==, !=, <=, <, >=, >, +, -";
    if(
      CurTok.type == ASTERIX
      || CurTok.type == DIV
      ||CurTok.type == MOD
      ) {
    parserSuccess(production);
    std::string op = CurTok.lexeme.c_str();
    getNextToken(); // eat "*" / "/" / "%"

    unary();

    term();

  } else if(
    CurTok.type != RPAR
    && CurTok.type != SC
    && CurTok.type != COMMA
    && CurTok.type != OR
    && CurTok.type != AND
    && CurTok.type != EQ
    && CurTok.type != NE
    && CurTok.type != LE
    && CurTok.type != LT
    && CurTok.type != GE
    && CurTok.type != GT
    && CurTok.type != MINUS
    && CurTok.type != PLUS
  ) {
    parserErr(production, first + ", " + follow);
  }
}

/*
  terms ::= unary term  
*/
static void terms() {
  unary();
  term();
}

/*
  arithmetic ::= "+" terms arithmetic
  | "-" terms arithmetic
  | epsilon
*/
static void arithmetic() {
  std::string production = "arithmetic";
  std::string first = "+, -";
  std::string follow = "), ;, COMMA, ||, &&, ==, !=, <=, <, >=, >";
    if(
      CurTok.type == PLUS
      || CurTok.type == MINUS
      ) {
    parserSuccess(production);
    getNextToken(); // eat "+" / "-"


    terms();

    arithmetic();

  } else if(
    CurTok.type != RPAR
    && CurTok.type != SC
    && CurTok.type != COMMA
    && CurTok.type != OR
    && CurTok.type != AND
    && CurTok.type != EQ
    && CurTok.type != NE
    && CurTok.type != LE
    && CurTok.type != LT
    && CurTok.type != GE
    && CurTok.type != GT
  ) {
    parserErr(production, first + ", " + follow);
  }
}


/*
  arithmetics ::= terms arithmetic
*/
static void arithmetics() {
  terms();
  arithmetic();
}

/*
  comparison ::= "<=" arithmetics comparison
  | "<" arithmetics comparison
  | ">=" arithmetics comparison
  | ">" arithmetics comparison
  | epsilon
*/
static void comparison() {
  std::string production = "comparison";
  std::string first = "<=, <, >=, >";
  std::string follow = "), ;, COMMA, ||, &&, ==, !=";
    if(
      CurTok.type == LE
      || CurTok.type == LT
      || CurTok.type == GE
      || CurTok.type == GT
      ) {
    parserSuccess(production);
    getNextToken(); // eat "<=" / "<" / ">=" / ">"
    return;

  } else if(
    CurTok.type != RPAR
    && CurTok.type != SC
    && CurTok.type != COMMA
    && CurTok.type != OR
    && CurTok.type != AND
    && CurTok.type != EQ
    && CurTok.type != NE
  ) {
    parserErr(production, first + ", " + follow);
  }
}

/*
  comparisons ::= arithmetics comparison
*/
static void comparisons() {
  arithmetics();
  comparison();
}

/*
  equality ::= "==" comparisons equality
  | "!=" comparisons equality
  | epsilon
*/
static void equality() {
  std::string production = "equality";
  std::string first = "==, !=";
  std::string follow = "), ;, COMMA, ||, &&";
    if(
      CurTok.type == EQ
      || CurTok.type == NE
      ) {
    parserSuccess(production);
    std::string op = CurTok.lexeme.c_str();
    getNextToken(); // eat "=="

    comparisons();

    equality(); 
    
    return;

  } else if(
    CurTok.type != RPAR
    && CurTok.type != SC
    && CurTok.type != COMMA
    && CurTok.type != OR
    && CurTok.type != AND
  ) {
    parserErr(production, first + ", " + follow);
  }
}

/*
  equalities ::= comparisons equality
*/
static void equalities() {
  comparisons();
  equality();
}

/*
  and_expr ::= "&&" equalities and_expr
  | epsilon
*/
static void andExpr() {
  std::string production = "andExpr";
  std::string first = "&&";
  std::string follow = "), ;, COMMA, ||";
  if(CurTok.type == AND) {
    parserSuccess(production);
    std::string op = CurTok.lexeme.c_str();
    getNextToken(); // eat "&&"

    equalities();

    andExpr(); 

    return;

  } else if(
    CurTok.type != RPAR
    && CurTok.type != SC
    && CurTok.type != COMMA
    && CurTok.type != OR
  ) {
    parserErr(production, first + ", " + follow);
  }
}

/*
  and_exprs ::= equalities and_expr
*/
static void andExprs() {
  equalities();
  andExpr();
}

/*
  or_expr ::= "||" and_exprs or_expr
  | epsilon
*/
static void orExpr() {
  std::string production = "orExpr";
  std::string first = "||";
  std::string follow = "), ;, COMMA";
  if(CurTok.type == OR) {
    parserSuccess(production);
    getNextToken(); // eat ||

    andExprs();

    orExpr();

    return;

  } else if(
    CurTok.type != RPAR
    && CurTok.type != SC
    && CurTok.type != COMMA
  ) {
    parserErr(production, first + ", " + follow);
  }
}

/*
  or_exprs ::= and_exprs or_expr
*/
static void orExprs() {
  andExprs();
  orExpr();
}

static void backToTree() {
  std::string production = "backToTree";
  std::string first = "&&, ||, ==, !=, <=, <, >=, >, +, -, *, /, %";
  std::string follow = "), COMMA, ;";
  if(
    CurTok.type == AND
    || CurTok.type == OR
    || CurTok.type == EQ
    || CurTok.type == NE
    || CurTok.type == LE
    || CurTok.type == LT
    || CurTok.type == GE
    || CurTok.type == GT
    || CurTok.type == PLUS
    || CurTok.type == MINUS
    || CurTok.type == ASTERIX
    || CurTok.type == DIV
    || CurTok.type == MOD
    ) {
    parserSuccess(production);
    getNextToken(); // eat binary operator

    orExprs();
    return;

  } else if(
    CurTok.type != RPAR
    && CurTok.type != SC
    && CurTok.type != COMMA
  ) {
    parserErr(production, first + ", " + follow);
  }
}

/*
  expr_identified = "=" expr
  | arg_block back_to_tree
*/
static void exprIdentified() {
  std::string production = "exprIdentified";
  if(CurTok.type == ASSIGN) {
    parserSuccess(production);
    getNextToken(); // eat "="

    expr();
    
  } else if(
    CurTok.type == LPAR
    || CurTok.type != IDENT
    || CurTok.type != LPAR
    || CurTok.type != RPAR
    || CurTok.type != SC
    || CurTok.type != COMMA
    || CurTok.type != OR
    || CurTok.type != AND
    || CurTok.type != EQ
    || CurTok.type != NE
    || CurTok.type != LE
    || CurTok.type != LT
    || CurTok.type != GE
    || CurTok.type != GT
    || CurTok.type != MINUS
    || CurTok.type != PLUS
    || CurTok.type != ASTERIX
    || CurTok.type != DIV
    || CurTok.type != MOD
    || CurTok.type != INT_LIT
    || CurTok.type != FLOAT_LIT
    || CurTok.type != BOOL_LIT
    ) {
    argBlock();
    backToTree();
  } else {
    parserErr(production, "=, ("); // not correct
  }
}

/*
  expr ::= IDENT expr_identified
  | or_exprs
*/
static void expr() {
  std::string production = "expr";
  std::string first = "IDENT, (, -, !, INT_LIT, FLOAT_LIT, BOOL_LIT";
  if(CurTok.type == IDENT) {
    parserSuccess(production);
    getNextToken(); // eat IDENT

    exprIdentified();
    return;
  } else if(
    CurTok.type == LPAR
    || CurTok.type == MINUS
    || CurTok.type == NOT
    || CurTok.type == INT_LIT
    || CurTok.type == FLOAT_LIT
    || CurTok.type == BOOL_LIT
  ) {
    orExprs();
  } else {
    parserErr(production, first);
  }
}

/* 
  expr_stmt ::= ";"
  | expr ";"
*/
static void exprStmt() {
  std::string production = "exprStmt";
  if(CurTok.type == SC) {
    parserSuccess(production);
    getNextToken(); // eat ";"
  } else if(
    CurTok.type == IDENT
    || CurTok.type == LPAR
    || CurTok.type == SC
    || CurTok.type == MINUS
    || CurTok.type == NOT
    || CurTok.type == INT_LIT
    || CurTok.type == FLOAT_LIT
    || CurTok.type == BOOL_LIT
    ) {

      expr();

      if(CurTok.type == SC) {
        parserSuccess(production);
        getNextToken(); // eat ";"
      }
  } else {
    parserErr(production , "IDENT, (, ;, -, !, INT_LIT, FLOAT_LIT, BOOL_LIT");
  }
}

/*
  block ::= "{" local_decls stmt_list "}"
*/
static void block() {
  std::string production = "block";
  std::string expected[2] = {"{", "}"};
  int errIndex = 0;
  if(CurTok.type == LBRA) {
    parserSuccess(production);
    getNextToken(); // eat "{"
    errIndex++;

    localDecls();

    stmtList();

    if(CurTok.type == RBRA) {
      parserSuccess(production);
      getNextToken(); // eat "}"
      return;
    }
  }

  parserErr(production, expected[errIndex]);
}

/*
  return_stmt ::= "return" expr_stmt
*/
static void returnStmt() {
  std::string production = "returnStmt";
  if(CurTok.type == RETURN) {
    parserSuccess(production);
    getNextToken(); // eat "return"

    exprStmt();
  } else {
    parserErr(production, "return");
  }
}

/*
  else_stmt ::= "else" block
  | epsilon
*/
static void elseStmt() {
  std::string production = "elseStmt";
  std::string first = "else";
  std::string follow = "IDENT, (, ;, {, }, while, if, return, -, !, INT_LIT, FLOAT_LIT, BOOL_LIT";
  if(CurTok.type == ELSE) {
    parserSuccess(production);
    getNextToken(); // eat "else"

    block();

  } else if(
    CurTok.type != IDENT
    && CurTok.type != LPAR
    && CurTok.type != SC
    && CurTok.type != LBRA
    && CurTok.type != RBRA
    && CurTok.type != WHILE
    && CurTok.type != IF
    && CurTok.type != RETURN
    && CurTok.type != MINUS
    && CurTok.type != NOT
    && CurTok.type != INT_LIT
    && CurTok.type != FLOAT_LIT
    && CurTok.type != BOOL_LIT
  ) {
    parserErr(production, first + ", " + follow);
  }
}

/*
  if_stmt ::= "if" "(" expr ")" block else_stmt
*/
static void ifStmt() {
  std::string production = "ifStmt";
  std::string expected[3] = {"if", "(", ")"};
  int errIndex = 0;
  if(CurTok.type == IF) {
    parserSuccess(production);
    getNextToken(); // eat "if"
    errIndex++;

    if(CurTok.type == LPAR) {
      parserSuccess(production);
      getNextToken(); // eat "("
      errIndex++;

      expr();

      if(CurTok.type == RPAR) {
        parserSuccess(production);
        getNextToken(); // eat ")"

        block();

        elseStmt();

        return;
      }
    }
  }

  parserErr(production, expected[errIndex]);
}

/*
  while_stmt ::= "while" "(" expr ")" stmt
*/
static void whileStmt() {
  std::string production = "whileStmt";
  std::string expected[3] = {"while", "(", ")"};
  int errIndex = 0;
  if(CurTok.type == WHILE) {
    parserSuccess(production);
    getNextToken(); // eat "while"
    errIndex++;

    if(CurTok.type == LPAR) {
      parserSuccess(production);
      getNextToken(); // eat "("

      expr();

      if(CurTok.type == RPAR) {
        parserSuccess(production);
        getNextToken(); // eat ")"

        stmt();

        return;
      }
    }
  }

  parserErr(production, expected[errIndex]);
}

static void stmt() {
  std::string production = "stmt";
  if(CurTok.type == LBRA) {
    block();
  } else if(CurTok.type == WHILE) {
    whileStmt();
  } else if(CurTok.type == IF) {
    ifStmt();
  } else if(CurTok.type == RETURN) {
    returnStmt();
  } else if(
    CurTok.type == SC
    || CurTok.type == MINUS
    || CurTok.type == NOT
    || CurTok.type == LPAR
    || CurTok.type == INT_LIT
    || CurTok.type == FLOAT_LIT
    || CurTok.type == BOOL_LIT
    || CurTok.type == IDENT
    ) {
      exprStmt();
    } else {
      parserErr(production, "IDENT, (, ;, {, while, if, return, -, !, INT_LIT, FLOAT_LIT, BOOL_LIT");
    }

}

/*
  stmt ::= block
  | if_stmt
  | while_stmt
  | return_stmt
  | expr_stmt
*/
static void stmtList() {
  std::string production = "stmtList";
  std::string first = "IDENT, (, ;, {, while, if, return, -, !, INT_LIT, FLOAT_LIT, BOOL_LIT";
  std::string follow = "}";
  if(
    CurTok.type == IDENT
    || CurTok.type == LPAR
    || CurTok.type == SC
    || CurTok.type == LBRA
    || CurTok.type == WHILE
    || CurTok.type == IF
    || CurTok.type == RETURN
    || CurTok.type == MINUS
    || CurTok.type == NOT
    || CurTok.type == INT_LIT
    || CurTok.type == FLOAT_LIT
    || CurTok.type == BOOL_LIT
  ) {

    stmt();

    stmtList();

  } else if(CurTok.type != RBRA) {
      parserErr(production, first + ", " + follow);
  }
}

/*
  var_type ::= "int" 
  | "float" 
  | "bool"
*/
static void varType() {
  std::string production = "varType";
  if(
    CurTok.type == INT_TOK
    || CurTok.type == FLOAT_TOK
    || CurTok.type == BOOL_TOK
  ) {
    parserSuccess(production);
    getNextToken(); //eat "int"/"float"/"tok"
  } else {
    parserErr(production, "int, float, bool");
  }
}

/*
  local_decl ::= var_type IDENT ";"
*/
static void localDecl() {
  std::string production = "localDecl";
  std::string expected[2] = {"IDENT", ";"};
  int errIndex = 0;

  varType();
  if(CurTok.type == IDENT) {
    parserSuccess(production);
    getNextToken(); // eat IDENT
    errIndex++;

    if(CurTok.type == SC) {
      parserSuccess(production);
      getNextToken(); // eat ";"
      return;
    }
  }

  parserErr(production, expected[errIndex]);
}

/*
  more_local_decls ::= local_decl more_local_decls
  | epsilon
*/
static void moreLocalDecls() {
  std::string production = "moreLocalDecls";
  std::string first = "int, float, bool";
  std::string follow = "IDENT, (, ;, {, }, while, if, return, -, !, INT_LIT, FLOAT_LIT, BOOL_LIT";
  if(
    CurTok.type == INT_TOK
    || CurTok.type == FLOAT_TOK
    || CurTok.type == BOOL_TOK
    ) {

    localDecl();

    moreLocalDecls();

  } else if(
    CurTok.type != IDENT 
    && CurTok.type != RPAR
    && CurTok.type != SC
    && CurTok.type != RBRA
    && CurTok.type != LBRA
    && CurTok.type != WHILE
    && CurTok.type != IF
    && CurTok.type != RETURN
    && CurTok.type != MINUS
    && CurTok.type != NOT
    && CurTok.type != INT_LIT
    && CurTok.type != FLOAT_LIT
    && CurTok.type != BOOL_LIT
  ) {
    parserErr(production, first + ", " + follow);
  }
}

/*
  local_decls ::= local_decl
  | more_local_decls
*/
static void localDecls() {
  //localDecl();
  moreLocalDecls();
}

/*
  param ::= var_type IDENT
*/
static void param() {
  std::string production = "param";
  varType();
  if(CurTok.type == IDENT) {
    parserSuccess(production);
    getNextToken(); // eat IDENT
  } else {
    parserErr(production, "IDENT");
  }
}

/*
  param_list ::= "," param param_list
  | epsilon
*/
static void paramList() {
  std::string production = "paramList";
  if(CurTok.type == COMMA) {
    parserSuccess(production);
    getNextToken(); //eat ","

    param();
    paramList();
  } else if(
    CurTok.type != RPAR
  ) {
    parserErr(production, "COMMA, )");
  }
}

/*
  param_lists ::= param param_list
*/
static void paramLists() {
  param();
  paramList();
}

/*
  params ::= param_lists
  | "void" 
  | epsilon
*/
static void params() {
  std::string production = "params";
  if(CurTok.type == VOID_TOK) {
    parserSuccess(production);
    getNextToken(); // eat "void"
  } else if(
    CurTok.type == INT_TOK
    || CurTok.type == FLOAT_TOK
    || CurTok.type == BOOL_TOK
    )
  {
    paramLists();    

  } else if(CurTok.type != RPAR) {
    parserErr(production, "void, int, float, bool, )");
  }
}

/* 
  fun_decl ::= "(" params ")" block
*/
static void funDecl() {
  std::string production = "funDecl";
  std::string expected[2] = {"(", ")"};
  int errIndex = 0;
  if(CurTok.type == LPAR) {
    parserSuccess(production);
    getNextToken(); // eat "("
    errIndex++;

    params();

    if(CurTok.type == RPAR) {
      parserSuccess(production);
      getNextToken(); // eat ")"
    }

    block();

    return;
  }

  parserErr(production, expected[errIndex]);
}

/*
  type_spec ::= "void"
  | var_type
*/
static void typeSpec() {
  std::string production = "typeSpec";
  if(CurTok.type == VOID_TOK) {
    parserSuccess(production);
    getNextToken();// eat "void"
  } else if(
    CurTok.type == INT_TOK 
    || CurTok.type == FLOAT_TOK
    || CurTok.type == BOOL_TOK
  ) {
    varType();
  } else {
    parserErr(production, "void, int, float, bool");
  }
}

/*
  identified_decl ::= ";"
  | fun_decl
*/
static void identifiedDecl() {
  std::string production = "identifiedDecl";
  if(CurTok.type == SC) {
    parserSuccess(production);
    getNextToken(); // eat ","
  } else if(
    CurTok.type == LPAR
  ) {
    funDecl();
  } else {
    parserErr(production, "COMMA, (");
  }
}

/* 
  decl ::= "void" IDENT fun_decl
  | var_type IDENT identified_decl 
*/
static void decl() {
  std::string production = "decl";
  std::string expected[2] = {
    "void, int, float, bool", 
    "IDENT", 
    };
  int errIndex = 0;

  if(CurTok.type == VOID_TOK) {
    parserSuccess(production);
    getNextToken(); // eat "void"
    errIndex++;

    if(CurTok.type == IDENT) {
      parserSuccess(production);
      getNextToken(); //eat IDENT

      funDecl();
      return;
    }
  } else if(CurTok.type == INT_TOK
          || CurTok.type == FLOAT_TOK
          || CurTok.type == BOOL_TOK) {
      varType();
      errIndex++;

      if(CurTok.type == IDENT) {
        parserSuccess(production);
        getNextToken(); // eat IDENT
        identifiedDecl();
        return;
      }       
    }

    parserErr(production, expected[errIndex]);
}

/*
  decl_list ::= decl decl_list
  | epsilon
*/
static void declList() {
  std::string production = "declList";
  if(CurTok.type == VOID_TOK 
          || CurTok.type == INT_TOK 
          || CurTok.type == FLOAT_TOK 
          || CurTok.type == BOOL_TOK         
          ) {
    decl();
    declList();
  } else if(CurTok.type != EOF_TOK) {
    parserErr(production, "void, int, float, bool, eof");
  }
}

/*
  decl_lists ::= decl decl_list
*/
static void declLists() {
  decl();
  declList();
}

// extern ::= "extern" type_spec IDENT "(" params ")" ";"
static void externProd() {
  std::string production = "externProd";
  std::string expected[5] = {"extern", "IDENT", "LPAR", "RPAR", ";"};
  int errIndex = 0;
  if (CurTok.type == EXTERN) {
    parserSuccess(production);
    getNextToken(); // eat "extern"
    errIndex++;
    
    typeSpec(); 

    if(CurTok.type == IDENT) {
      parserSuccess(production);
      getNextToken(); // eat IDENT
      errIndex++;

      if(CurTok.type == LPAR) {
        parserSuccess(production);
        getNextToken(); // eat "("
        errIndex++;

        params();

        if(CurTok.type == RPAR) {
          parserSuccess(production);
          getNextToken(); // eat ")"  
          errIndex++;

        } if(CurTok.type == SC) {
          parserSuccess(production);
          getNextToken(); //eat ";"
          return;
        }
      }
    }
  }

  parserErr(production, expected[errIndex]);
}

// extern_lists ::= extern extern_list
static void externList() {
  std::string production = "externList";
  if (CurTok.type == EXTERN) {
    externProd();
    externList();
  } else if(CurTok.type != VOID_TOK 
          && CurTok.type != INT_TOK 
          && CurTok.type != FLOAT_TOK 
          && CurTok.type != BOOL_TOK   
          && CurTok.type != EOF_TOK      
  ) 
  {
    parserErr(production, "extern, void, int, float, bool, eof");
  }
}

// extern_lists ::= extern extern_list
static void externLists() {
  externProd();
  externList();
}

// program ::= extern_lists decl_lists
static void parser() {
  // add body
  std::string production = "parser";
  getNextToken();
  if(CurTok.type == EXTERN) {
    externLists();
    declLists();
  } else if(
    CurTok.type == VOID_TOK
    || CurTok.type == INT_TOK
    || CurTok.type == FLOAT_TOK
    || CurTok.type == BOOL_TOK
    ) {
      declLists();
    }

  if(CurTok.type == EOF_TOK) {
    parserSuccess(production);
    return;
  } else {
    parserErr(production, "eof");
  }
}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
                                     const ASTnode &ast)
{
  os << ast.to_string();
  return os;
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main(int argc, char **argv)
{
  if (argc == 2)
  {
    pFile = fopen(argv[1], "r");
    if (pFile == NULL)
      perror("Error opening file");
  }
  else
  {
    std::cout << "Usage: ./code InputFile\n";
    return 1;
  }

  // initialize line number and column numbers to zero
  lineNo = 1;
  columnNo = 1;

  // get the first token
  // getNextToken();
  // while (CurTok.type != EOF_TOK)
  // {
  //   fprintf(stderr, "Token: %s with type %d\n", CurTok.lexeme.c_str(),
  //           CurTok.type);
  //   getNextToken();
  // }
  // fprintf(stderr, "Lexer Finished\n");

  // Make the module, which holds all the code.
  TheModule = std::make_unique<Module>("mini-c", TheContext);

  // Run the parser now.
  fprintf(stderr, "-------------------------------PARSER LOG-------------------------------\n");
  parser();
  fprintf(stderr, "Parsing Finished\n");
    fprintf(stderr, "------------------------------------------------------------------------\n");

  //********************* Start printing final IR **************************
  // Print out all of the generated code into a file called output.ll
  auto Filename = "output.ll";
  std::error_code EC;
  raw_fd_ostream dest(Filename, EC, sys::fs::OF_None);

  if (EC)
  {
    errs() << "Could not open file: " << EC.message();
    return 1;
  }
  // TheModule->print(errs(), nullptr); // print IR to terminal
  TheModule->print(dest, nullptr);
  //********************* End printing final IR ****************************

  fclose(pFile); // close the file that contains the code that was parsed
  return 0;
}
