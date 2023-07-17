import Lazycore.NDFormula
import Lazycore.InferenceRule
import Mathlib.Data.Multiset.Basic

def InfrenceRule.AndIntro [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ⊢ₛ φ, Δ ⊢ₛ ψ], Γ ∪ Δ ⊢ₛ φ ∧ₙ ψ, InfrenceRule.noRestrictions⟩

theorem InfrenceRule.AndIntro.Valid [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) :
⊨ᵢ (InfrenceRule.AndIntro φ ψ Γ Δ) 
:= by{
  unhygienic
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  rw [AndIntro] at *;
  simp at *;
  cases s;
  rw [Sequent.sat] at *;
  intros H;
  simp at *;
  rw [NDFormula.sat];
  apply And.intro;
  {
    apply left;
    intro f fg;
    apply H f;
    apply Or.inl;
    exact fg;
  };
  {
    apply right;
    intro f fd;
    apply H f;
    apply Or.inr;
    exact fd;
  }
}