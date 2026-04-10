import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

namespace MetaRepair

open Classical

/-- 塩基 -/
inductive Base : Type
  | A | T | G | C
  deriving Repr, DecidableEq, Inhabited

-- FIX 1: `def` に `deriving` は使えない。`abbrev` に変更する。
-- `Base` が DecidableEq/Inhabited を持つため、積型のインスタンスは自動導出される。
/-- コドン -/
abbrev Codon := Base × Base × Base

/-- アミノ酸 -/
inductive AminoAcid : Type
  | aa1 | aa2 | aa3 | aa4
  deriving Repr, DecidableEq, Inhabited

/-- 翻訳 -/
def translate : Codon → AminoAcid
  | (Base.A, _, _) => AminoAcid.aa1
  | (Base.T, _, _) => AminoAcid.aa2
  | (Base.G, _, _) => AminoAcid.aa3
  | (Base.C, _, _) => AminoAcid.aa4

def translate_seq (s : List Codon) : List AminoAcid :=
  s.map translate

/-- アミノ酸距離（重み付き）-/
def aa_dist (a b : AminoAcid) : ℝ :=
  if a = b then 0 else 1

/-- 位置ごとの重要度（重み）-/
def weight (i : ℕ) : ℝ :=
  1 + (i : ℝ) / 10

-- FIX 2: `fun acc ⟨i, p⟩ =>` はラムダでの無名コンストラクタパターンとして
-- コンパイル失敗する可能性がある。`fun acc ip =>` に変更して `.1`/`.2` でアクセス。
/-- 重み付きタンパク質距離 -/
def protein_distance_w : List AminoAcid → List AminoAcid → ℝ
  | xs, ys =>
    (List.zip xs ys).enum.foldl
      (fun acc ip => acc + weight ip.1 * aa_dist ip.2.1 ip.2.2)
      0

/-- 機能距離 -/
def functional_distance (x y : List Codon) : ℝ :=
  protein_distance_w (translate_seq x) (translate_seq y)

/-- 発現効率（確率的モデル簡略化）-/
def expression_efficiency (m : List Codon) : ℝ :=
  1 / (1 + (m.length : ℝ))

/-- 安全性ペナルティ（長さ依存など）-/
def safety_penalty (m : List Codon) : ℝ :=
  (m.length : ℝ) / 100

/-- 総合コスト関数（これが核心）-/
def total_cost (target m : List Codon) : ℝ :=
  functional_distance target m - expression_efficiency m + safety_penalty m

/-- 最適パッチ（定義）-/
def is_optimal
    (target : List Codon)
    (candidates : List (List Codon))
    (m : List Codon) : Prop :=
  m ∈ candidates ∧
  ∀ c ∈ candidates, total_cost target m ≤ total_cost target c

/-- 非空有限集合では最適解が存在 -/
theorem optimal_exists
    (target : List Codon)
    (candidates : List (List Codon))
    (h : candidates ≠ []) :
    ∃ m, is_optimal target candidates m := by
  induction candidates with
  | nil => contradiction
  | cons c cs ih =>
    by_cases hcs : cs = []
    · -- FIX 4 (partial): ?h2 の inl ケースで `simp [hx]` は不安定。
      --   `subst` + `le_refl` を使う。
      subst hcs
      refine ⟨c, List.mem_cons_self c [], ?_⟩
      intro x hx
      simp [List.mem_cons, List.mem_nil_iff] at hx
      subst hx
      exact le_refl _
    · obtain ⟨m, hm1, hm2⟩ := ih hcs
      by_cases hcmp : total_cost target c ≤ total_cost target m
      · refine ⟨c, List.mem_cons_self c cs, ?_⟩
        intro x hx
        simp [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact le_refl _
        · exact le_trans hcmp (hm2 x hx)
      · refine ⟨m, List.mem_cons_of_mem c hm1, ?_⟩
        intro x hx
        simp [List.mem_cons] at hx
        rcases hx with rfl | hx
        · -- FIX 5: `le_of_not_ge` は Mathlib に存在しない。
          --   `not_le.mp` で `<` を得て `le_of_lt` で `≤` に変換。
          exact le_of_lt (not_le.mp hcmp)
        · exact hm2 x hx

/-- ε許容解 -/
def is_feasible (target m : List Codon) (ε : ℝ) : Prop :=
  functional_distance target m ≤ ε

/-- 制約付き最適化 -/
def is_constrained_optimal
    (target : List Codon)
    (candidates : List (List Codon))
    (ε : ℝ)
    (m : List Codon) : Prop :=
  is_feasible target m ε ∧
  m ∈ candidates ∧
  ∀ c ∈ candidates, is_feasible target c ε → total_cost target m ≤ total_cost target c

/-- 制約付き最適解の存在 -/
theorem constrained_optimal_exists
    (target : List Codon)
    (candidates : List (List Codon))
    (ε : ℝ)
    (h : ∃ m ∈ candidates, is_feasible target m ε) :
    ∃ m, is_constrained_optimal target candidates ε m := by
  rcases h with ⟨m0, hm0, hfeas0⟩
  -- FIX 3: `decide (is_feasible ...)` は ℝ 上の述語なので Decidable インスタンスがない。
  --   Classical.propDecidable で強制的に Bool に変換する。
  let p : List Codon → Bool := fun m =>
    @decide _ (Classical.propDecidable (is_feasible target m ε))
  let feasible := candidates.filter p
  -- m0 が feasible に属することを示す
  have hm0f : m0 ∈ feasible := by
    apply List.mem_filter.mpr
    refine ⟨hm0, ?_⟩
    simp [p, @decide_eq_true_eq _ (Classical.propDecidable _)]
    exact hfeas0
  have hne : feasible ≠ [] := List.ne_nil_of_mem hm0f
  obtain ⟨m, hm_mem, hm_best⟩ := optimal_exists target feasible hne
  -- filter メンバーシップから候補集合メンバーシップと feasibility を取り出す
  have hm_filter : m ∈ candidates ∧ p m = true := List.mem_filter.mp hm_mem
  have hm_cand : m ∈ candidates := hm_filter.1
  have hm_feas : is_feasible target m ε := by
    have := hm_filter.2
    simp [p, @decide_eq_true_eq _ (Classical.propDecidable _)] at this
    exact this
  refine ⟨m, hm_feas, hm_cand, ?_⟩
  intro c hc hfc
  have hcf : c ∈ feasible := by
    apply List.mem_filter.mpr
    refine ⟨hc, ?_⟩
    simp [p, @decide_eq_true_eq _ (Classical.propDecidable _)]
    exact hfc
  exact hm_best c hcf

end MetaRepair
