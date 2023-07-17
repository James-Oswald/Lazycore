
import Lazycore.NDFormula
import Lazycore.InferenceRule
import Mathlib.Data.Multiset.Basic

def InfrenceRule.OrIntroLeft [DecidableEq α] (φ ψ : NDFormula α)
(Γ : Multiset (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ⊢ₛ φ], Γ ⊢ₛ ψ ∨ₙ φ, InfrenceRule.noRestrictions⟩

def InfrenceRule.OrIntroRight [DecidableEq α] (φ ψ : NDFormula α)
(Γ : Multiset (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ⊢ₛ φ], Γ ⊢ₛ φ ∨ₙ ψ, InfrenceRule.noRestrictions⟩

theorem InfrenceRule.OrIntroLeft.valid [DecidableEq α] 
(φ ψ : NDFormula α) (Γ : Multiset (NDFormula α)) :
⊨ᵢ (InfrenceRule.OrIntroLeft φ ψ Γ) 
:= by{
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  rw [OrIntroLeft] at *;
  simp at *;
  rw [Sequent.sat] at *;
  simp at *;
  intros H;
  rw [NDFormula.sat];
  have H2 := s H;
  apply Or.inr;
  assumption;
}

theorem InfrenceRule.OrIntroRight.valid [DecidableEq α] 
(φ ψ : NDFormula α) (Γ : Multiset (NDFormula α)) :
⊨ᵢ (InfrenceRule.OrIntroRight φ ψ Γ) 
:= by{
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  rw [OrIntroRight] at *;
  simp at *;
  rw [Sequent.sat] at *;
  simp at *;
  intros H;
  rw [NDFormula.sat];
  have H2 := s H;
  apply Or.inl;
  assumption;
}
