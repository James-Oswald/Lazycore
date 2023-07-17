import Lazycore.Sequent

/-
An inference rule consists of 
a set of premicies, a conclusion,
and a set of aditional restrictions that may be placed on
the premices and conclusions.
-/
structure InfrenceRule (α  : Type) where
premises : List (Sequent α)
conclusion : Sequent α
restrictions : List (Sequent α) -> Sequent α -> Prop

--Most infrence rules have no additional restrictions on their premises or conclusion
def InfrenceRule.noRestrictions : List (Sequent α) -> Sequent α -> Prop 
:= fun _ => (fun _ => True)

/-
We can construct an infrence rule as a pair with the premises and conclusion
and provide InfrenceRule.noRestrictions as a default restriction
-/
instance: Coe (Prod (List (Sequent α)) (Sequent α)) (InfrenceRule α) where
coe a := ⟨a.fst, a.snd, InfrenceRule.noRestrictions⟩  

/-
An infrence rule is satisfiable in some interpretation iff
its premises and restrictions imply its conclusion
-/
def InfrenceRule.sat [DecidableEq α] (interpretation : α -> Prop) (r : InfrenceRule α) : Prop :=
(∀ (s : Sequent α), s ∈ r.premises -> (interpretation ⊨ₛ s)) -> 
r.restrictions r.premises r.conclusion ->
(interpretation ⊨ₛ r.conclusion)

infix:15 " ⊨ᵢ " => InfrenceRule.sat
infix:15 " |=ᵢ " => InfrenceRule.sat

/-
An infrence rule is valid (satisfiable over all interpetations) iff
its premises and restrictions imply its conclusion under any assignment
-/
def InfrenceRule.valid [DecidableEq α] (rule : InfrenceRule α) : Prop :=
∀ (interpretation : α -> Prop), InfrenceRule.sat interpretation rule

prefix:15 " ⊨ᵢ " => InfrenceRule.valid
prefix:15 " |=ᵢ " => InfrenceRule.valid