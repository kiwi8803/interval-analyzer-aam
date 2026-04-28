import Analyzer.State

namespace Analyzer.Concrete

inductive StoreVal where
  | vInt  : Int → StoreVal
  | vKont : Kont → StoreVal
  deriving BEq, Repr

def Env := Batteries.RBMap String Addr compare
def Store := Batteries.RBMap Addr StoreVal compare


-- Provide Repr for RBMap by converting to List
instance : Repr Env where
  reprPrec m _ := repr m.toList

instance : Repr Store where
  reprPrec m _ := repr m.toList

-- Provide BEq for RBMap by comparing sorted lists
instance : BEq Env where
  beq m₁ m₂ := m₁.toList == m₂.toList

instance : BEq Store where
  beq m₁ m₂ := m₁.toList == m₂.toList

structure Config where
  stmt : Stmt
  env  : Env
  store: Store
  kptr : Addr
  deriving BEq, Repr

/- 2. Concrete Expression Evaluation
   This returns an `Option Int`. It fails if a variable is missing. -/
def evalExpr (e : Expr) (env : Env) (store : Store) : Option Int :=
  match e with
  | .const n => some n
  | .var x =>
      match env.find? x with
      | some addr =>
          match store.find? addr with
          | some (.vInt i) => some i
          | _ => none
      | none => none
  | .add e1 e2 =>
      match evalExpr e1 env store, evalExpr e2 env store with
      | some v1, some v2 => some (v1 + v2)
      | _, _ => none
  | .sub e1 e2 =>
      match evalExpr e1 env store, evalExpr e2 env store with
      | some v1, some v2 => some (v1 - v2)
      | _, _ => none

/- 3. Concrete Step Function
   This is the "standard" interpreter. It returns a single `Option Config`. -/
def step (conf : Config) : Option Config :=
  match conf.stmt with
  | .assign x e =>
      match evalExpr e conf.env conf.store with
      | some v =>
          match conf.env.find? x with
          | some addr =>
              let newStore := conf.store.insert addr (.vInt v)
              match conf.store.find? conf.kptr with
              | some (.vKont (.kSeq next s_next)) =>
                  some { conf with stmt := next, store := newStore, kptr := s_next }
              | _ => none -- Halt/Error
          | none => none
      | none => none
  | .seq s1 s2 =>
      let kAddr := Addr.mk ("k_" ++ toString (hash s2))
      let newStore := conf.store.insert kAddr (.vKont (.kSeq s2 conf.kptr))
      some { conf with stmt := s1, store := newStore, kptr := kAddr }
  | .while e body =>
      match evalExpr e conf.env conf.store with
      | some v =>
          if v ≠ 0 then -- True branch
            let kAddr := Addr.mk ("k_while_" ++ toString (hash conf.stmt))
            let newStore := conf.store.insert kAddr (.vKont (.kWhile e body conf.kptr))
            some { conf with stmt := body, store := newStore, kptr := kAddr }
          else -- False branch: Exit loop
            match conf.store.find? conf.kptr with
            | some (.vKont (.kSeq next s_next)) => some { conf with stmt := next, kptr := s_next }
            | _ => none
      | none => none
  | .ite e s1 s2 =>
      match evalExpr e conf.env conf.store with
      | some v =>
          if v ≠ 0 then some { conf with stmt := s1 }
          else         some { conf with stmt := s2 }
      | none => none
  | .skip =>
      match conf.store.find? conf.kptr with
      | some (.vKont (.kSeq next s_next)) =>
          some { conf with stmt := next, kptr := s_next }
      | some (.vKont (.kWhile e body s_exit)) =>
          some { conf with stmt := (.while e body), kptr := s_exit }
      | some (.vKont .kDone) => none
      | _ => none

/-- Multi-step concrete execution as an inductive relation.
    `BigStep c c'` means: starting from `c`, the machine eventually halts at `c'`. -/
inductive BigStep : Config → Config → Prop where
  | done {c}           : step c = none → BigStep c c
  | step {c c_mid c'}  : step c = some c_mid → BigStep c_mid c' → BigStep c c'

end Analyzer.Concrete
