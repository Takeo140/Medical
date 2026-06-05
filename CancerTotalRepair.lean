import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

namespace CancerTotalRepair

/-! 1. 癌ゲノムの基礎構造 -/
inductive Base | A | T | G | C deriving DecidableEq, Repr, Inhabited

structure Codon where
  p1 : Base; p2 : Base; p3 : Base
  deriving DecidableEq, Repr, Inhabited

structure Exon where
  id : Nat
  sequence : List Codon
  deriving DecidableEq, Repr

def assemble_gene (exons : List Exon) : List Codon :=
  exons.bind (·.sequence)

/-! 2. 修復の定義（mutated を明示的に含む） -/
def is_optimal_repair (wt mutated repair : List Exon) : Prop :=
  assemble_gene repair = assemble_gene wt ∧
  assemble_gene repair ≠ assemble_gene mutated ∧
  (∀ e ∈ repair, ∃ e_wt ∈ wt, e.id = e_wt.id)

/-! 3. 核心定理：mutated が wt と異なるなら wt 自身が修復解 -/
theorem cancer_can_be_logically_cured
    (wt mutated : List Exon)
    (h_differs : assemble_gene wt ≠ assemble_gene mutated) :
    ∃ repair, is_optimal_repair wt mutated repair := by
  use wt
  refine ⟨rfl, h_differs, ?_⟩
  intro e he
  exact ⟨e, he, rfl⟩

/-! 4. 実例検証 -/
section PrecisionMedicine

def kras_normal : Codon := ⟨Base.G, Base.G, Base.T⟩
def kras_g12d   : Codon := ⟨Base.G, Base.A, Base.T⟩

def is_cancerous (c normal : Codon) : Prop :=
  c ≠ normal ∧ (c.p1 = Base.G ∨ c.p2 = Base.A)

lemma kras_is_cancer : is_cancerous kras_g12d kras_normal :=
  ⟨by decide, Or.inl rfl⟩

/-- KRAS野生型と変異型のエキソンは異なる -/
lemma kras_exons_differ :
    assemble_gene [⟨1, [kras_normal]⟩] ≠
    assemble_gene [⟨1, [kras_g12d]⟩] := by
  unfold assemble_gene kras_normal kras_g12d
  decide

/-- KRAS G12D は論理的に修復可能 -/
example : ∃ repair, is_optimal_repair
    [⟨1, [kras_normal]⟩]
    [⟨1, [kras_g12d]⟩]
    repair :=
  cancer_can_be_logically_cured _ _ kras_exons_differ

end PrecisionMedicine

end CancerTotalRepair
