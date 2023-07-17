import Lazycore.NDFormula
import Lazycore.InferenceRule
import Mathlib.Data.Multiset.Basic

def InfrenceRule.NotIntro [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ∪ φ ⊢ₛ ψ, Δ ⊢ₛ ¬ₙψ], Γ ∪ Δ ⊢ₛ ¬ₙφ, InfrenceRule.noRestrictions⟩

theorem InfrenceRule.NotIntro.Valid [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) : 
⊨ᵢ (InfrenceRule.NotIntro φ ψ Γ Δ) 
:= by{
  unhygienic
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  rw [NotIntro] at *;
  simp at *;
  cases s;
  rw [Sequent.sat] at *;
  intros H;
  simp at *;
  rw [NDFormula.sat] at *;
  rw [Not];
  intro N;
  apply right;
  {
    intros f fd;
    have H2 := H f;
    apply H2;
    apply Or.inr;
    exact fd;
  };{
    apply left;
    intros f fc;
    have H2 := H f;
    cases fc;{
      apply H2;
      apply Or.inl;
      assumption;
    };{
      rw [h];
      exact N;
    }
  }
}
