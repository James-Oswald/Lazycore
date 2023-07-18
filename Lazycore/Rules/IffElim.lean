import Lazycore.InferenceRule
import Lazycore.NDFormula
import Lazycore.Sequent

def InfrenceRule.IffElimLeft [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ⊢ₛ φ ↔ₙ ψ, Δ ⊢ₛ φ], Γ ∪ Δ ⊢ₛ ψ, InfrenceRule.noRestrictions⟩

def InfrenceRule.IffElimRight [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ⊢ₛ φ ↔ₙ ψ, Δ ⊢ₛ ψ], Γ ∪ Δ ⊢ₛ φ, InfrenceRule.noRestrictions⟩

def InfrenceRule.IffElimLeft.Valid [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) :
⊨ᵢ (InfrenceRule.IffElimLeft φ ψ Γ Δ)
:= by{
  unhygienic
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  clear inp;
  rw [IffElimLeft] at *;
  simp at *;
  cases s;
  rw [Sequent.sat] at *;
  simp at *;
  intro f;
  have H : (∀ (f : NDFormula α), f ∈ Γ → (i |=ₙ f)) := by{
    intro f2 fe;
    apply f;
    apply Or.inl;
    exact fe;
  }
  have H2 := left H;
  rw [NDFormula.sat] at H2;
  cases H2;
  apply mp;
  apply right;
  intro f2 fe;
  apply f;
  apply Or.inr;
  exact fe;
}

def InfrenceRule.IffElimRight.Valid [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) :
⊨ᵢ (InfrenceRule.IffElimRight φ ψ Γ Δ)
:= by{
  unhygienic
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  clear inp;
  rw [IffElimRight] at *;
  simp at *;
  cases s;
  rw [Sequent.sat] at *;
  simp at *;
  intro f;
  have H : (∀ (f : NDFormula α), f ∈ Γ → (i |=ₙ f)) := by{
    intro f2 fe;
    apply f;
    apply Or.inl;
    exact fe;
  }
  have H2 := left H;
  rw [NDFormula.sat] at H2;
  cases H2;
  apply mpr;
  apply right;
  intro f2 fe;
  apply f;
  apply Or.inr;
  exact fe;
}