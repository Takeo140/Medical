import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

namespace CancerRepair

inductive Base : Type
  | A | T | G | C
  deriving Repr, DecidableEq, Inhabited

def Base.weight : Base → Nat
  | .A => 5 | .G => 6 | .C => 3 | .T => 0

inductive FuncClass : Type
  | aromatic | hydrophobic | flexible | polar | positive | negative | stop
  deriving Repr, DecidableEq

structure Codon where
  p1 : Base; p2 : Base; p3 : Base
  deriving Repr, DecidableEq, Inhabited

def Codon.funcClass : Codon → FuncClass
  | ⟨.G, .G, _⟩ => .flexible
  | ⟨.G, .T, _⟩ | ⟨.C, .T, _⟩ | ⟨.T, .T, .A⟩ | ⟨.T, .T, .G⟩
  | ⟨.A, .T, _⟩ | ⟨.G, .C, _⟩ | ⟨.C, .C, _⟩ => .hydrophobic
  | ⟨.T, .T, .T⟩ | ⟨.T, .T, .C⟩ | ⟨.T, .G, .G⟩
  | ⟨.T, .A, .T⟩ | ⟨.T, .A, .C⟩ => .aromatic
  | ⟨.A, .A, .A⟩ | ⟨.A, .A, .G⟩ | ⟨.C, .G, _⟩
  | ⟨.A, .G, .A⟩ | ⟨.A, .G, .G⟩ => .positive
  | ⟨.G, .A, .T⟩ | ⟨.G, .A, .C⟩ | ⟨.G, .A, .A⟩ | ⟨.G, .A, .G⟩ => .negative
  | ⟨.T, .A, .A⟩ | ⟨.T, .A, .G⟩ | ⟨.T, .G, .A⟩ => .stop
  | _ => .polar

def fd_score (wt mut : Codon) : Nat :=
  (if wt.funcClass = mut.funcClass then 0 else 4) +
  (if wt.p1.weight = mut.p1.weight then 0 else 3) +
  (if wt.p2.weight = mut.p2.weight then 0 else 2) +
  (if wt.p3.weight = mut.p3.weight then 0 else 1)

/-- 自己スコアはゼロ -/
lemma fd_score_self (c : Codon) : fd_score c c = 0 := by
  simp [fd_score]

def is_safe_repair (wt mut repair : Codon) : Prop :=
  fd_score wt repair < fd_score wt mut ∧ repair.funcClass = wt.funcClass

theorem exist_safe_repair (wt mut : Codon) (h : fd_score wt mut ≥ 6) :
    ∃ r, is_safe_repair wt mut r := by
  exact ⟨wt, by simp [is_safe_repair, fd_score_self]; linarith⟩

/-! 実例検証 -/
def kras_wt  : Codon := ⟨.G, .G, .T⟩
def kras_mut : Codon := ⟨.G, .A, .T⟩

example : fd_score kras_wt kras_mut = 6 := by decide

example : ∃ r, is_safe_repair kras_wt kras_mut r :=
  exist_safe_repair _ _ (by decide)

end CancerRepair
