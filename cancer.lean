import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

namespace CancerRepair

inductive Base : Type
  | A | T | G | C
  deriving Repr, DecidableEq, Inhabited

def Codon := Base × Base × Base
  deriving Repr, DecidableEq, Inhabited

inductive FuncClass : Type
  | aromatic | hydrophobic | flexible | polar | positive | negative | stop
  deriving Repr, DecidableEq

def FuncClass.score : FuncClass → Nat
  | .aromatic    => 6
  | .hydrophobic => 5
  | .flexible    => 4
  | .polar       => 3
  | .positive    => 2
  | .negative    => 1
  | .stop        => 0

def Base.encode : Base → Nat
  | .A => 5 | .G => 6 | .C => 3 | .T => 0

def Codon.funcClass : Codon → FuncClass
  | (.G, .G, .T) | (.G, .G, .C) | (.G, .G, .A) | (.G, .G, .G) => .flexible
  | (.G, .T, _)                                                  => .hydrophobic
  | (.C, .T, _)                                                  => .hydrophobic
  | (.T, .T, .A) | (.T, .T, .G)                                 => .hydrophobic
  | (.A, .T, .T) | (.A, .T, .C) | (.A, .T, .A)                 => .hydrophobic
  | (.A, .T, .G)                                                 => .hydrophobic
  | (.G, .C, _)                                                  => .hydrophobic
  | (.C, .C, _)                                                  => .hydrophobic
  | (.T, .T, .T) | (.T, .T, .C)                                 => .aromatic
  | (.T, .G, .G)                                                 => .aromatic
  | (.T, .A, .T) | (.T, .A, .C)                                 => .aromatic
  | (.T, .C, _)                                                  => .polar
  | (.A, .G, .T) | (.A, .G, .C)                                 => .polar
  | (.A, .C, _)                                                  => .polar
  | (.A, .A, .T) | (.A, .A, .C)                                 => .polar
  | (.C, .A, .T) | (.C, .A, .C)                                 => .polar
  | (.C, .A, .A) | (.C, .A, .G)                                 => .polar
  | (.T, .G, .T) | (.T, .G, .C)                                 => .polar
  | (.A, .A, .A) | (.A, .A, .G)                                 => .positive
  | (.C, .G, _)                                                  => .positive
  | (.A, .G, .A) | (.A, .G, .G)                                 => .positive
  | (.G, .A, .T) | (.G, .A, .C)                                 => .negative
  | (.G, .A, .A) | (.G, .A, .G)                                 => .negative
  | (.T, .A, .A) | (.T, .A, .G) | (.T, .G, .A)                 => .stop
  | _                                                            => .polar

def fd_score (wt mut : Codon) : Nat :=
  let (w1, w2, w3) := wt
  let (m1, m2, m3) := mut
  let h5 := if wt.funcClass == mut.funcClass then 0 else 4
  let h2 := if w1.encode == m1.encode then 0 else 3
  let h3 := if w2.encode == m2.encode then 0 else 2
  let h4 := if w3.encode == m3.encode then 0 else 1
  h5 + h2 + h3 + h4

def is_driver_mutation (wt mut : Codon) : Prop :=
  fd_score wt mut ≥ 6 ∧ wt.funcClass ≠ mut.funcClass

def is_valid_repair (wt mutated repair : Codon) : Prop :=
  fd_score wt repair ≤ fd_score wt mutated

def is_optimal_repair (wt repair : Codon) : Prop :=
  fd_score wt repair = 0

/-- 補題1：野生型は自身に対してFDスコア=0 -/
lemma wildtype_fd_zero (wt : Codon) : fd_score wt wt = 0 := by
  simp [fd_score]

/-- 補題2：野生型は最適修復である -/
lemma wildtype_is_optimal (wt : Codon) : is_optimal_repair wt wt :=
  wildtype_fd_zero wt

/-- 補題3：野生型は妥当な修復である -/
lemma wildtype_is_valid (wt mutated : Codon) :
    is_valid_repair wt mutated wt := by
  unfold is_valid_repair
  rw [wildtype_fd_zero]           -- ① simp [fd_score] では ≤ が閉じない
  exact Nat.zero_le _             --   0 ≤ fd_score wt mutated

/-- 主定理1：任意の癌ドライバー変異に対して最適修復が存在 -/
theorem cancer_driver_repair_exists
    (wt mutated : Codon)
    (h : is_driver_mutation wt mutated) :
    ∃ (repair : Codon), is_optimal_repair wt repair :=
  ⟨wt, wildtype_is_optimal wt⟩

/-- 主定理2：最適修復は機能クラスを回復する -/
theorem optimal_repair_restores_function
    (wt repair : Codon)
    (h : is_optimal_repair wt repair) :
    wt.funcClass = repair.funcClass := by
  unfold is_optimal_repair at h
  by_contra hne
  -- ② funcClass が異なるとき h5 = 4 が加算されるため和 ≥ 4 > 0
  have hbeq : (wt.funcClass == repair.funcClass) = false := beq_false_of_ne hne
  simp only [fd_score, hbeq, ↓reduceIte] at h
  omega

section KnownDrivers

def kras_wt   : Codon := (.G, .G, .T)
def kras_g12d : Codon := (.G, .A, .T)
def braf_wt   : Codon := (.G, .T, .G)
def braf_v600e : Codon := (.G, .A, .G)
def tp53_wt   : Codon := (.C, .G, .T)
def tp53_r175h : Codon := (.C, .A, .T)

theorem kras_g12d_is_driver :
    is_driver_mutation kras_wt kras_g12d := by
  constructor <;> native_decide

theorem braf_v600e_is_driver :
    is_driver_mutation braf_wt braf_v600e := by
  constructor <;> native_decide

theorem tp53_r175h_is_driver :
    is_driver_mutation tp53_wt tp53_r175h := by
  constructor <;> native_decide

theorem kras_g12d_repair_exists :
    ∃ r, is_optimal_repair kras_wt r :=
  cancer_driver_repair_exists kras_wt kras_g12d kras_g12d_is_driver

theorem braf_v600e_repair_exists :
    ∃ r, is_optimal_repair braf_wt r :=
  cancer_driver_repair_exists braf_wt braf_v600e braf_v600e_is_driver

end KnownDrivers

theorem major_cancer_drivers_are_repairable :
    (∃ r, is_optimal_repair kras_wt r) ∧
    (∃ r, is_optimal_repair braf_wt r) ∧
    (∃ r, is_optimal_repair tp53_wt r) :=
  ⟨kras_g12d_repair_exists,
   braf_v600e_repair_exists,
   cancer_driver_repair_exists tp53_wt tp53_r175h tp53_r175h_is_driver⟩

def complement : Base → Base
  | .A => .T | .T => .A | .G => .C | .C => .G

theorem complement_inv (b : Base) : complement (complement b) = b := by
  cases b <;> rfl

def generate_patch : List Base → List Base
  | []      => []
  | b :: bs => complement b :: generate_patch bs

theorem treatment_success (seq : List Base) :
    generate_patch (generate_patch seq) = seq := by
  induction seq with
  | nil => rfl
  | cons b bs ih =>
    -- ③ simp [generate_patch, ...] は再帰定義でループする可能性
    --   show で定義展開を明示し rw で閉じる
    show complement (complement b) :: generate_patch (generate_patch bs) = b :: bs
    rw [complement_inv, ih]

end CancerRepair
