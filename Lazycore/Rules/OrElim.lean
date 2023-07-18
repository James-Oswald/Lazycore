
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
  have left_special :  (∀ (f : NDFormula α), f ∈ Χ → (i |=ₙ f))  := by {
    intro f2 fe;
    have H3 := H f2;
    apply H3;
    apply Or.inr;
    exact fe;
  }
  rw [NDFormula.sat] at *;
  have H3 := left left_special;
  cases H3;{
    apply left_1;
    intros f fe;
    cases fe;{
      apply H;
      apply Or.inl;
      apply Or.inl;
      exact h_1;
    };{
      rw [h_1];
      exact h;
    }
  };{
    apply right_1;
    intros f fe;
    cases fe;{
      apply H;
      apply Or.inl;
      apply Or.inr;
      exact h_1;
    };{
      rw [h_1];
      exact h;
    }
  }
}
