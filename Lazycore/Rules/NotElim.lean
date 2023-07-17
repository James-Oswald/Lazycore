import Lazycore.NDFormula
import Lazycore.InferenceRule
import Mathlib.Data.Multiset.Basic

def InfrenceRule.NotElim [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ∪ ¬ₙφ ⊢ₛ ψ, Δ ⊢ₛ ¬ₙψ], Γ ∪ Δ ⊢ₛ φ, InfrenceRule.noRestrictions⟩

theorem InfrenceRule.NotElim.Valid [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) : 
⊨ᵢ (InfrenceRule.NotElim φ ψ Γ Δ) 
:= by{
  unhygienic
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  rw [NotElim] at *;
  simp at *;
  cases s;
  rw [Sequent.sat] at *;
  intros H;
  simp at *;
  rw [NDFormula.sat] at *;
  rw [Not] at *;
  apply Classical.byContradiction;
  intros H2;
  apply right;
  {
    intro f fd;
    apply H;
    apply Or.inr;
    exact fd;
  };
  {
    apply left;
    intro f fg;
    cases fg;{
      apply H;
      apply Or.inl;
      exact h;
    };{
      rw [h, NDFormula.sat];
      exact H2;
    }
  }
}
