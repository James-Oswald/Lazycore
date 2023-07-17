
import Lazycore.NDFormula
import Lazycore.InferenceRule
import Mathlib.Data.Multiset.Basic

def InfrenceRule.OrElim [DecidableEq α] (φ ψ χ : NDFormula α)
(Γ Δ Χ : Multiset (NDFormula α)) :
InfrenceRule α := 
⟨[Χ ⊢ₛ φ ∨ₙ ψ, Γ ∪ φ ⊢ₛ χ, Δ ∪ ψ ⊢ₛ χ], Γ ∪ Δ ∪ Χ ⊢ₛ χ, InfrenceRule.noRestrictions⟩

def InfrenceRule.OrElimValid [DecidableEq α] (φ ψ χ : NDFormula α)
(Γ Δ Χ : Multiset (NDFormula α)) :
⊨ᵢ (InfrenceRule.OrElim φ ψ χ Γ Δ Χ) 
:= by{
  unhygienic
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  clear inp;
  rw [OrElim] at *;
  simp at *;
  cases s;
  cases right;
  rw [Sequent.sat] at *;
  simp at *;
  intro H;
  

  


  -- intros H;
  -- apply Or.elim _ right_1 left_1;
  -- apply Or.inl;
  -- intro f fd;
  -- cases fd;
  -- {
  --   apply H;
  --   apply Or.inl;
  --   apply Or.inr;
  --   exact h;
  -- };
  -- {

  -- }

  
  --apply left_1;
  -- intro f fOr;
  -- cases fOr;{
  --   apply H;
  --   apply Or.inl;
  --   apply Or.inl;
  --   exact h;
  -- };{
  --   rw [h];
  --   apply Or.elim;
  -- }
  
} 