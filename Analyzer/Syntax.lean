namespace Analyzer

inductive Expr where
  | const : Int → Expr -- Integer only constant for now
  | var   : String → Expr -- variable
  | add   : Expr → Expr → Expr
  | sub   : Expr → Expr → Expr
  deriving BEq, Hashable, Repr
/-
  The 'C' in CESK:
  We use an inductive type so we can use "Pattern Matching" in our
  transition function. Small-step semantics (CESK) treats these
  statements as 'configurations' that transform piece-by-piece.
-/
inductive Stmt where
  | skip    : Stmt -- does nothing
  | assign  : String → Expr → Stmt -- store change bridge between Expr and Addr
  | seq     : Stmt → Stmt → Stmt -- connects two statment into one
  | ite     : Expr → Stmt → Stmt → Stmt -- if then else
  | while   : Expr → Stmt → Stmt
  deriving BEq, Hashable, Repr

end Analyzer
