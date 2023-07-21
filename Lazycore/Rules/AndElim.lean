import Lazycore.NDFormula
import Lazycore.InferenceRule
import Mathlib.Data.Multiset.Basic

-- Left =======================================================================

def InfrenceRule.AndElimLeft [DecidableEq α] (φ ψ : NDFormula α)
(Γ : Multiset (NDFormula α)) :
InfrenceRule α := 
[Γ ⊢ₛ φ ∧ₙ ψ] ⊢ᵢ Γ ⊢ₛ φ

alias InfrenceRule.AndElimLeft ← AndEₗ

theorem InfrenceRule.AndElimLeft.Valid [DecidableEq α]
(φ ψ : NDFormula α) (Γ : Multiset (NDFormula α)) :
⊨ᵢ AndEₗ φ ψ Γ :=
by{
  unhygienic
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  rw [AndEₗ, InfrenceRule.AndElimLeft] at *;
  simp at *;
  rw [Sequent.sat] at *;
  intros H;
  simp at *;
  have H2 := s H;
  rw [NDFormula.sat] at H2;
  cases H2;
  exact left;
}

-- Right =======================================================================

def InfrenceRule.AndElimRight [DecidableEq α] (φ ψ : NDFormula α)
(Γ : Multiset (NDFormula α)) :
InfrenceRule α := 
[Γ ⊢ₛ φ ∧ₙ ψ] ⊢ᵢ Γ ⊢ₛ ψ

alias InfrenceRule.AndElimRight ← AndEᵣ

theorem InfrenceRule.AndElimRight.Valid [DecidableEq α] 
(φ ψ : NDFormula α) (Γ : Multiset (NDFormula α)) :
⊨ᵢ AndEᵣ φ ψ Γ :=
by{
  unhygienic
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  rw [AndEᵣ, InfrenceRule.AndElimRight] at *;
  simp at *;
  rw [Sequent.sat] at *;
  intros H;
  simp at *;
  have H2 := s H;
  rw [NDFormula.sat] at H2;
  cases H2;
  exact right;
}