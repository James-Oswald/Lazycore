
import Lazycore.NDFormula
import Lazycore.InferenceRule

import Lazycore.Rules.Assumption
import Lazycore.Rules.AndIntro
import Lazycore.Rules.AndElim
import Lazycore.Rules.OrIntro
import Lazycore.Rules.OrElim
import Lazycore.Rules.NotIntro
import Lazycore.Rules.NotElim
import Lazycore.Rules.IfIntro
import Lazycore.Rules.IfElim
import Lazycore.Rules.IffIntro
import Lazycore.Rules.IffElim

import Mathlib.Data.Finset.Basic

inductive Justification where
| Assumption
| AndIntro
| AndElim
| OrIntro
| OrElim
| NotIntro
| IfIntro
| IffElim
deriving Repr, BEq, DecidableEq


structure ProofNode (α : Type) where
formula : NDFormula α
justification : Justification

structure Proof (idt α: Type) where
nodes : idt -> ProofNode α
--links is in the form of a map from nodeIDs to the finite set of parents
links : idt -> List idt


def verifyAssumption [DecidableEq α] (p : Proof idt α) (id : idt) : Sum String (Multiset (NDFormula α)) :=
let node := p.nodes id
if node.justification != Justification.Assumption then
  Sum.inl "Not Justified as an Assumption"
else
  if (p.links id).length = 0 then
    Sum.inl "Assumption has parents but should not"
  else
    Sum.inr (InfrenceRule.Assumption node.formula).conclusion.anticendents


def verifyAndIntro [DecidableEq α] (p : Proof idt α) (id : idt) : Sum String (Multiset (NDFormula α)) :=
let node := p.nodes id
let links := p.links id
if node.justification != Justification.Assumption then
  Sum.inl "Not Justified as AndIntro"
else
  if links.length = 2 then
    let leftNode := (p.links id)[0]
    let rightNode := (p.links id)[1]'simp
    Sum.inr (InfrenceRule.AndIntro) 
  else
    Sum.inl "AndIntro node must have 2 parents but does not"



-- def getAssumptions {idt : Type} : List (idt × ProofNode) -> List idt
-- | [] => []
-- | h :: t =>
--   let t_assumptions := getAssumptions t
--   if h.snd.justification == Justification.Assumption then
--     h.fst :: t_assumptions
--   else
--     t_assumptions

-- def verify (p : Proof) : Bool :=
--   let assumptions := getAssumptions p.nodes
--   if assumptions.length == 0 then
--     false
--   else
