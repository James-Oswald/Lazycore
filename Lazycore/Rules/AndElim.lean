import Lazycore.NDFormula
import Lazycore.InferenceRule
import Mathlib.Data.Multiset.Basic

def InfrenceRule.AndElimLeft [DecidableEq α] (φ ψ : NDFormula α)
(Γ : Multiset (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ⊢ₛ φ ∧ₙ ψ], Γ ⊢ₛ φ, InfrenceRule.noRestrictions⟩

def InfrenceRule.AndElimRight [DecidableEq α] (φ ψ : NDFormula α)
(Γ : Multiset (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ⊢ₛ φ ∧ₙ ψ], Γ ⊢ₛ ψ, InfrenceRule.noRestrictions⟩

theorem InfrenceRule.AndElimLeft.Valid [DecidableEq α]
(φ ψ : NDFormula α) (Γ : Multiset (NDFormula α)) :
⊨ᵢ (InfrenceRule.AndElimLeft φ ψ Γ) :=
by{
  unhygienic
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  rw [AndElimLeft] at *;
  simp at *;
  rw [Sequent.sat] at *;
  intros H;
  simp at *;
  have H2 := s H;
  rw [NDFormula.sat] at H2;
  cases H2;
  exact left;
}

theorem InfrenceRule.AndElimRight.Valid [DecidableEq α] 
(φ ψ : NDFormula α) (Γ : Multiset (NDFormula α)) :
⊨ᵢ (InfrenceRule.AndElimRight φ ψ Γ) :=
by{
  unhygienic
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  rw [AndElimRight] at *;
  simp at *;
  rw [Sequent.sat] at *;
  intros H;
  simp at *;
  have H2 := s H;
  rw [NDFormula.sat] at H2;
  cases H2;
  exact right;
}