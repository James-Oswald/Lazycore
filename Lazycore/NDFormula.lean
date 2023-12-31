
import Mathlib.Data.Multiset.Basic

-- α is the type of identifiers
inductive NDFormula (α : Type) where
| prop : α -> NDFormula α
| and : NDFormula α -> NDFormula α -> NDFormula α
| or : NDFormula α -> NDFormula α -> NDFormula α
| not : NDFormula α -> NDFormula α
| imp : NDFormula α -> NDFormula α -> NDFormula α
| iff : NDFormula α -> NDFormula α -> NDFormula α


-- Representational Conveninces ==========================================

notation:max "¬ₙ" p:40 => NDFormula.not p
infixr:35 " ∧ₙ " => NDFormula.and
infixr:30 " ∨ₙ " => NDFormula.or
infixr:25 " →ₙ " => NDFormula.imp
infixr:25 " ->ₙ " => NDFormula.imp
infixr:20 " ↔ₙ " => NDFormula.iff
infixr:20 " <->ₙ " => NDFormula.iff

/-
Any type can be coerced to an atomic predicate of
that type
-/
instance : Coe α (NDFormula α) where
coe a := NDFormula.prop a

def NDFormula.str [ToString α] (f : NDFormula α) : String :=
match f with
| .prop p => toString p
| .and a b => str a ++ " ∧ₙ " ++ str b
| .or a b => str a ++ " ∨ₙ " ++ str b
| .not a => "¬ₙ" ++ str a
| .imp a b => str a ++ " →ₙ " ++ str b
| .iff a b => str a ++ " ↔ₙ " ++ str b

instance [ToString α] : ToString (NDFormula α) where
toString := NDFormula.str

instance [ToString α] : Repr (NDFormula α) where
reprPrec f _ := NDFormula.str f

/-
A standalone ND formula can be coreced
to a list of ND formulae with 1 elm
-/
instance : Coe (NDFormula α) (List (NDFormula α)) where
coe a := [a]

/-
A standalone ND formula can be coreced to a multiset of ND
formulae with 1 elmement
-/
instance : Coe (NDFormula α) (Multiset (NDFormula α)) where
coe a := Multiset.ofList [a]

-- Semantical Defintions ================================================


def instNDFormulaBeq [BEq α] (φ ψ : NDFormula α) : Bool :=
match φ, ψ with
| .prop p, .prop q => p == q
| .and a b, .and c d => instNDFormulaBeq a c && instNDFormulaBeq b d
| .or a b, .or c d => instNDFormulaBeq a c && instNDFormulaBeq b d
| .imp a b, .imp c d => instNDFormulaBeq a c && instNDFormulaBeq b d
| .iff a b, .iff c d => instNDFormulaBeq a c && instNDFormulaBeq b d
| .not a, .not b => instNDFormulaBeq a b
| _, _ => false

instance [BEq α] : BEq (NDFormula α) where
  beq := instNDFormulaBeq

deriving instance DecidableEq for NDFormula

/-
The definition of union for multisets of formulae
-/
instance [DecidableEq α] : Union (Multiset (NDFormula α)) where
  union := Multiset.union 

/-
Semantics for ND formulae, satisfiability under some assignment of 
atomic propostions to truth values.
-/
def NDFormula.sat [DecidableEq α] (interpretation : α -> Prop)
  (formula : NDFormula α) : Prop :=
let i := interpretation
match formula with
  | prop a => interpretation a
  | and f1 f2 => sat i f1 ∧ sat i f2
  | or f1 f2 => sat i f1 ∨ sat i f2
  | not f => ¬sat i f
  | imp f1 f2 => sat i f1 -> sat i f2
  | iff  f1 f2 => sat i f1 <-> sat i f2

infix:15 " ⊨ₙ " => NDFormula.sat
infix:15 " |=ₙ " => NDFormula.sat

/-
A formulae is valid iff it is satisfiable under all interpretations
-/
def NDFormula.valid [DecidableEq α] (formula : NDFormula α) : Prop := 
∀ (interpretation : α -> Prop), NDFormula.sat interpretation formula

prefix:15 " ⊨ₙ  " => NDFormula.valid
prefix:15 " |=ₙ " => NDFormula.valid