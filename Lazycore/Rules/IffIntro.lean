import Lazycore.InferenceRule
import Lazycore.NDFormula
import Lazycore.Sequent

def InfrenceRule.IffIntro [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ∪ φ ⊢ₛ ψ, Δ ∪ ψ ⊢ₛ φ], Γ ∪ Δ ⊢ₛ φ ↔ₙ ψ, InfrenceRule.noRestrictions⟩

def InfrenceRule.IffIntro.Valid [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) :
⊨ᵢ (InfrenceRule.IffIntro φ ψ Γ Δ)
:= by{
  unhygienic
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  clear inp;
  rw [IffIntro] at *;
  simp at *;
  rw [Sequent.sat] at *;
  simp at *;
  intro f;
  rw [NDFormula.sat];
  apply Iff.intro;
  {
    intro i;
    cases s;
    apply left;
    intros f2 fOr;
    cases fOr;{
      apply f;
      apply Or.inl;
      exact h;
    };{
      rw [h];
      exact i;
    }
  };{
    intro i;
    cases s;
    apply right;
    simp at *;
    intros f2 fOr;
    cases fOr;{
      apply f;
      apply Or.inr;
      exact h;
    };{
      rw [h];
      exact i;
    }
  }
}