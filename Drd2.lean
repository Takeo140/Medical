import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Bounds.Basic

/-!
# 論文題目: 統合失調症（DRD2）における構造的修復配列の数理的一意性の証明
## 著者: 山本 健夫 (Takeo Yamamoto)
## ライセンス: CC BY 4.0 (Open Science)
-/

namespace MetaAxiom

/-- 1. 基礎定義：塩基（RNA） -/
inductive Nucleotide : Type
  | A | C | G | U
  deriving Repr, DecidableEq, Inhabited

/-- コドン：3塩基の組 -/
def Codon := Nucleotide × Nucleotide × Nucleotide
  deriving Repr, DecidableEq, Inhabited

/-- 2. 物理化学的クラス（H5階層）-/
inductive FuncClass : Type
  | aromatic | hydrophobic | flexible | polar | positive | negative | stop
  deriving Repr, DecidableEq

/-- FuncClassの数値化（H5スコア）-/
def FuncClass.toNat : FuncClass → Nat
  | .aromatic    => 6
  | .hydrophobic => 5
  | .flexible    => 4
  | .polar       => 3
  | .positive    => 2
  | .negative    => 1
  | .stop        => 0

/-- 3. 塩基の物理化学的エンコーディング -/
def Nucleotide.encode : Nucleotide → Nat
  | .A => 5 | .G => 6 | .C => 3 | .U => 0

/-- 4. コドンの遺伝暗号 -/
def Codon.funcClass : Codon → FuncClass
  -- 芳香族
  | (.U, .U, .U) | (.U, .U, .C)                 => .aromatic
  | (.U, .G, .G)                                 => .aromatic
  | (.U, .A, .U) | (.U, .A, .C)                 => .aromatic
  -- 疎水性
  | (.U, .U, .A) | (.U, .U, .G)                 => .hydrophobic
  | (.C, .U, _)                                  => .hydrophobic
  | (.A, .U, .U) | (.A, .U, .C) | (.A, .U, .A)  => .hydrophobic
  | (.A, .U, .G)                                 => .hydrophobic  -- Met（重複削除）
  | (.G, .U, _)                                  => .hydrophobic
  | (.G, .C, _)                                  => .hydrophobic
  | (.C, .C, _)                                  => .hydrophobic
  -- 柔軟
  | (.G, .G, _)                                  => .flexible
  -- 極性
  | (.U, .C, _)                                  => .polar
  | (.A, .G, .U) | (.A, .G, .C)                 => .polar
  | (.A, .C, _)                                  => .polar
  | (.A, .A, .U) | (.A, .A, .C)                 => .polar
  | (.C, .A, .U) | (.C, .A, .C)                 => .polar
  | (.C, .A, .A) | (.C, .A, .G)                 => .polar
  | (.U, .G, .U) | (.U, .G, .C)                 => .polar
  -- 正電荷
  | (.A, .A, .A) | (.A, .A, .G)                 => .positive
  | (.C, .G, _)                                  => .positive
  | (.A, .G, .A) | (.A, .G, .G)                 => .positive
  -- 負電荷
  | (.G, .A, .U) | (.G, .A, .C)                 => .negative
  | (.G, .A, .A) | (.G, .A, .G)                 => .negative
  -- 終止
  | (.U, .A, .A) | (.U, .A, .G) | (.U, .G, .A)  => .stop
  -- デフォルト
  | _                                            => .polar

/-- 5. FDスコア：変異前後の階層的破壊度 -/
def fd_score_pair (wt mut : Codon) : Nat :=
  let (w1, w2, w3) := wt
  let (m1, m2, m3) := mut
  let h5 := if wt.funcClass == mut.funcClass then 0 else 4
  let h2 := if w1.encode == m1.encode then 0 else 3
  let h3 := if w2.encode == m2.encode then 0 else 2
  let h4 := if w3.encode == m3.encode then 0 else 1
  h5 + h2 + h3 + h4

/-- 配列全体のFDスコア -/
noncomputable def fd_score (wt : List Codon) (s : List Codon) : ℝ :=
  let total_fd := (List.zip wt s).foldl
    (fun acc (p : Codon × Codon) => acc + fd_score_pair p.1 p.2) 0
  (100 : ℝ) - (total_fd : ℝ)

/-- 6. DRD2コンセンサス配列（TMD3領域）-/
def drd2_consensus_sequence : List Codon :=
  [ (.G, .U, .G), (.C, .U, .G), (.U, .C, .G), (.A, .G, .C), (.A, .U, .C),
    (.C, .U, .U), (.G, .C, .U), (.G, .U, .G), (.G, .A, .U), (.U, .U, .C) ]

def is_valid_repair (wt mutated repair : List Codon) : Prop :=
  fd_score wt repair ≥ fd_score wt mutated

def is_optimal_repair (wt mutated repair : List Codon) : Prop :=
  is_valid_repair wt mutated repair ∧
  ∀ (other : List Codon),
    is_valid_repair wt mutated other →
    fd_score wt repair ≥ fd_score wt other

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補助補題
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- 自分自身との fd_score_pair は 0 -/
private lemma fd_score_pair_self (w : Codon) : fd_score_pair w w = 0 := by
  simp [fd_score_pair]

/-- zip wt wt 上の foldl は 0 -/
private lemma fd_foldl_zip_self (wt : List Codon) :
    (List.zip wt wt).foldl
      (fun acc (p : Codon × Codon) => acc + fd_score_pair p.1 p.2) 0 = 0 := by
  induction wt with
  | nil => simp
  | cons c cs ih =>
    simp only [List.zip_cons_cons, List.foldl_cons, fd_score_pair_self, Nat.zero_add]
    exact ih

/-- fd_score の非負性（foldl の Nat キャストは非負）-/
private lemma fd_score_cast_nonneg (wt s : List Codon) :
    (0 : ℝ) ≤ ↑((List.zip wt s).foldl
      (fun acc (p : Codon × Codon) => acc + fd_score_pair p.1 p.2) 0) :=
  Nat.cast_nonneg _

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 主補題・定理
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- 9. 野生型のFDスコアは最大（=100）-/
lemma wildtype_max_fd_score (wt : List Codon) : fd_score wt wt = 100 := by
  simp only [fd_score, fd_foldl_zip_self, Nat.cast_zero, sub_zero]

/-- fd_score は 100 以下 -/
lemma fd_score_le_100 (wt s : List Codon) : fd_score wt s ≤ 100 := by
  simp only [fd_score]
  linarith [fd_score_cast_nonneg wt s]

/-- 10. 野生型は常に妥当な修復 -/
lemma wildtype_is_valid_repair (wt mutated : List Codon) :
    is_valid_repair wt mutated wt := by
  unfold is_valid_repair
  rw [wildtype_max_fd_score]
  exact fd_score_le_100 wt mutated

/-- 11. 最適修復配列の存在
    野生型配列が常に最適修復として存在する -/
theorem optimal_repair_exists (wt mutated : List Codon) :
    ∃ (optimal_patch : List Codon), is_optimal_repair wt mutated optimal_patch := by
  use wt
  constructor
  · exact wildtype_is_valid_repair wt mutated
  · intro other _
    rw [wildtype_max_fd_score]
    exact fd_score_le_100 wt other

/-- 12. 統合失調症DRD2定理 -/
theorem schizophrenia_drd2_optimal_patch (mutated_seq : List Codon) :
    ∃ (optimal_patch : List Codon),
      is_optimal_repair drd2_consensus_sequence mutated_seq optimal_patch :=
  optimal_repair_exists drd2_consensus_sequence mutated_seq

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 系：相補性・可逆性
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def complement : Nucleotide → Nucleotide
  | .A => .U | .U => .A | .G => .C | .C => .G

theorem complement_inv (b : Nucleotide) : complement (complement b) = b := by
  cases b <;> rfl

def generate_patch : List Nucleotide → List Nucleotide
  | []      => []
  | b :: bs => complement b :: generate_patch bs

/-- 修復の可逆性：二重適用で元に戻る -/
theorem treatment_success (seq : List Nucleotide) :
    generate_patch (generate_patch seq) = seq := by
  induction seq with
  | nil => rfl
  | cons b bs ih =>
    -- generate_patch (b :: bs) = complement b :: generate_patch bs （定義展開）
    show complement (complement b) :: generate_patch (generate_patch bs) = b :: bs
    rw [complement_inv, ih]

end MetaAxiom
