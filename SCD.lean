import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

namespace SickleCellDisease

open Classical

/-!
## 鎌状赤血球症（SCD）治療最適化フレームワーク
HBB遺伝子 Glu6Val 変異（GAG→GTG）を起点とする
ヘモグロビン組成・鎌状化・臓器保護の統合モデル
-/

/-- ヘモグロビン型 -/
inductive HbType : Type
  | HbA   -- 正常成人ヘモグロビン（α2β2）
  | HbS   -- 鎌状ヘモグロビン（β Glu6Val）
  | HbF   -- 胎児ヘモグロビン（α2γ2）：鎌状化抑制
  | HbA2  -- 微量成人型（α2δ2）
  deriving Repr, DecidableEq, Inhabited

/-- 患者のヘモグロビン組成（各比率 ∈ [0,1]、合計=1） -/
structure HbComposition where
  hbA  : ℝ   -- HbA 分率
  hbS  : ℝ   -- HbS 分率（高いほど重篤）
  hbF  : ℝ   -- HbF 分率（高いほど保護的）
  hbA2 : ℝ   -- HbA2 分率
  deriving Repr, Inhabited

/-- 組成の妥当性：合計≒1、各成分≥0 -/
def HbComposition.valid (c : HbComposition) : Prop :=
  c.hbA ≥ 0 ∧ c.hbS ≥ 0 ∧ c.hbF ≥ 0 ∧ c.hbA2 ≥ 0 ∧
  c.hbA + c.hbS + c.hbF + c.hbA2 = 1

/-- 鎌状化指数（HbS比率が支配的、HbFが抑制）
    Sunshine ら empirical: sickling ∝ HbS / (HbS + HbF) -/
def sickling_index (c : HbComposition) : ℝ :=
  c.hbS / (c.hbS + c.hbF + 1)   -- +1 で 0除算回避

/-- 酸素親和性スコア（HbF高いほど酸素放出が低下→組織保護） -/
def oxygen_affinity (c : HbComposition) : ℝ :=
  1 - c.hbS / 2

/-- 治療モダリティ -/
inductive TherapyType : Type
  | HydroxyureaHU     -- ヒドロキシウレア：HbF誘導
  | BCL11AInhibitor   -- BCL11A抑制：γグロビン脱抑制
  | BaseEditing       -- 塩基編集（ABE8e）：HbS→HbA直接修正
  | GeneTherapy       -- レンチウイルスβA-T87Q導入
  | AlloSCT           -- 同種造血幹細胞移植
  deriving Repr, DecidableEq, Inhabited

/-- 治療候補パラメータ -/
structure Therapy where
  modality     : TherapyType
  hbF_delta    : ℝ   -- HbF上昇量（治療効果）
  hbS_delta    : ℝ   -- HbS低下量（≤0）
  toxicity     : ℝ   -- 毒性スコア [0,1]
  accessibility : ℝ  -- アクセス可能性 [0,1]（費用・施設依存）
  deriving Repr, Inhabited

/-- 治療後ヘモグロビン組成を推定 -/
def apply_therapy (base : HbComposition) (t : Therapy) : HbComposition :=
  { hbA  := base.hbA
    hbS  := max 0 (base.hbS + t.hbS_delta)
    hbF  := min 1 (base.hbF + t.hbF_delta)
    hbA2 := base.hbA2 }

/-- 臨床的有効性：鎌状化指数の低下量 -/
def clinical_efficacy
  (base : HbComposition)
  (t : Therapy) : ℝ :=
  sickling_index base - sickling_index (apply_therapy base t)

/-- HbF閾値（≥20%で血管閉塞クリーゼ頻度が有意に低下）-/
def hbF_threshold : ℝ := 0.20

/-- 閾値達成判定 -/
def meets_hbF_target
  (base : HbComposition)
  (t : Therapy) : Prop :=
  (apply_therapy base t).hbF ≥ hbF_threshold

/-- 総合治療コスト（最小化対象）-/
def treatment_cost
  (base : HbComposition)
  (t : Therapy) : ℝ :=
  - clinical_efficacy base t          -- 有効性最大化 → 符号反転
  + t.toxicity                         -- 毒性ペナルティ
  + (1 - t.accessibility)             -- アクセス障壁

/-- 最適治療候補（定義）-/
def is_optimal_therapy
  (base : HbComposition)
  (candidates : List Therapy)
  (t : Therapy) : Prop :=
  t ∈ candidates ∧
  ∀ c ∈ candidates,
    treatment_cost base t ≤ treatment_cost base c

/-- 非空候補集合では最適治療が存在 -/
theorem optimal_therapy_exists
  (base : HbComposition)
  (candidates : List Therapy)
  (h : candidates ≠ []) :
  ∃ t, is_optimal_therapy base candidates t := by
  classical
  induction candidates with
  | nil => contradiction
  | cons c cs ih =>
    by_cases hcs : cs = []
    · subst hcs
      exact ⟨c, by simp, fun x hx => by simp at hx; subst hx⟩
    · obtain ⟨m, hm⟩ := ih hcs
      by_cases hcmp :
        treatment_cost base c ≤ treatment_cost base m
      · refine ⟨c, by simp, fun x hx => ?_⟩
        simp at hx
        cases hx with
        | inl hx => subst hx
        | inr hx => exact le_trans hcmp (hm.2 x hx)
      · refine ⟨m, by simp [hm.1], fun x hx => ?_⟩
        simp at hx
        cases hx with
        | inl hx =>
          subst hx
          exact le_trans (hm.2 c (by simp)) (le_of_not_ge hcmp)
        | inr hx => exact hm.2 x hx

/-- HbF閾値制約付き最適治療 -/
def is_constrained_optimal_therapy
  (base : HbComposition)
  (candidates : List Therapy)
  (t : Therapy) : Prop :=
  meets_hbF_target base t ∧
  t ∈ candidates ∧
  ∀ c ∈ candidates,
    meets_hbF_target base c →
    treatment_cost base t ≤ treatment_cost base c

/-- HbF閾値制約付き最適治療の存在 -/
theorem constrained_therapy_exists
  (base : HbComposition)
  (candidates : List Therapy)
  (h : ∃ t ∈ candidates, meets_hbF_target base t) :
  ∃ t, is_constrained_optimal_therapy base candidates t := by
  classical
  rcases h with ⟨t0, ht0mem, ht0hbF⟩
  let feasible :=
    candidates.filter
      (fun t => decide (meets_hbF_target base t))
  have hne : feasible ≠ [] := by
    have : t0 ∈ feasible := by
      simp [feasible, ht0mem, ht0hbF]
    intro hnil; simp [hnil] at this
  obtain ⟨t, ht⟩ := optimal_therapy_exists base feasible hne
  refine ⟨t, ?_, ?_, ?_⟩
  · have := ht.1; simp [feasible] at this; exact this.2
  · have := ht.1; simp [feasible] at this; exact this.1
  · intro c hc hfeas
    have hc' : c ∈ feasible := by simp [feasible, hc, hfeas]
    exact ht.2 c hc'

end SickleCellDisease
