import Lazycore.NDFormula

#check ("a" ->ₙ "b" : NDFormula String)

-- The interpretation in which all atomic propositions are true 
-- satisfies the tautology a ∧ₙ b ->ₙ a
example [DecidableEq α] (a b : NDFormula α): (fun _ => True) ⊨ₙ a ∧ₙ b ->ₙ a  := 
by{
  rw [NDFormula.sat];
  intros H;
  rw [NDFormula.sat] at H;
  cases H;
  assumption;
}

-- for any NDFormulae a,b, the ND formulae a ∧ₙ b ->ₙ a
-- is valid (a tautology)
example [DecidableEq α] (a b : NDFormula α): ⊨ₙ a ∧ₙ b ->ₙ a := 
by{
  rw [NDFormula.valid];
  intro i;
  rw [NDFormula.sat];
  intros H;
  rw [NDFormula.sat] at H;
  cases H;
  trivial;
}