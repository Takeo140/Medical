import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

namespace DuchenneMD

open Classical

/-- ジストロフィン遺伝子のエクソン番号（1–79）-/
def ExonIndex := Fin 79

/-- エクソンの状態 -/
inductive ExonState : Type
  | present   -- 正常発現
  | deleted   -- 欠失（DMD変異）
  | skipped   -- アンチセンス治療でスキップ
  deriving Repr, DecidableEq, Inhabited

/-- エクソン構造：番号 + 状態 + コドン長（フレーム計算用）-/
structure Exon where
  index  : ℕ
  state  : ExonState
  length : ℕ   -- コドン数（フレームシフト判定）
  deriving Repr, Inhabited

/-- リーディングフレーム：0, 1, 2 -/
def Frame := Fin 3

/-- エクソン列からフレームを累積計算 -/
def frame_of (exons : List Exon) : ℕ :=
  (exons.foldl (fun acc e =>
    if e.state == ExonState.present || e.state == ExonState.skipped
    then acc  -- skipped = 長さ0として扱う（スキップ後除外）
    else acc + e.length) 0) % 3

/-- フレーム内（インフレーム）判定 -/
def is_inframe (exons : List Exon) : Prop :=
  frame_of exons = 0

/-- アンチセンスオリゴ（AON）治療候補 -/
structure AON where
  target_exon : ℕ        -- スキップ対象エクソン
  efficacy    : ℝ        -- スキップ効率 [0,1]
  off_target  : ℝ        -- オフターゲットスコア（低いほど良）
  deriving Repr, Inhabited

/-- AON適用：対象エクソンをskipped状態に変更 -/
def apply_aon (aon : AON) (exons : List Exon) : List Exon :=
  exons.map (fun e =>
    if e.index = aon.target_exon
    then { e with state := ExonState.skipped }
    else e)

/-- 機能的ジストロフィン近似
    Becker型（短縮版）でも部分的機能を保持 -/
def dystrophin_function
  (exons : List Exon)
  (aon : AON) : ℝ :=
  let treated := apply_aon aon exons
  let present_count :=
    (treated.filter (fun e => e.state == ExonState.present)).length
  if is_inframe treated
  then (present_count : ℝ) / (exons.length : ℝ)  -- インフレーム：部分機能
  else 0                                            -- フレームシフト：機能なし

/-- 安全性スコア（オフターゲット・投与量依存）-/
def safety_score (aon : AON) : ℝ :=
  1 / (1 + aon.off_target)

/-- 投与負担（efficacy高いほど必要量少）-/
def dosage_burden (aon : AON) : ℝ :=
  1 / (1 + aon.efficacy)

/-- 総合治療コスト（最小化対象）-/
def treatment_cost
  (exons : List Exon)
  (aon : AON) : ℝ :=
  - dystrophin_function exons aon   -- 機能回復を最大化 → 符号反転
  + (1 - safety_score aon)          -- 安全性ペナルティ
  + dosage_burden aon               -- 投与負担

/-- 最適AON候補（定義）-/
def is_optimal_aon
  (exons : List Exon)
  (candidates : List AON)
  (aon : AON) : Prop :=
  aon ∈ candidates ∧
  ∀ c ∈ candidates,
    treatment_cost exons aon ≤ treatment_cost exons c

/-- 非空候補集合では最適AONが存在 -/
theorem optimal_aon_exists
  (exons : List Exon)
  (candidates : List AON)
  (h : candidates ≠ []) :
  ∃ aon, is_optimal_aon exons candidates aon := by
  classical
  induction candidates with
  | nil => contradiction
  | cons c cs ih =>
    by_cases hcs : cs = []
    · subst hcs
      exact ⟨c, by simp, fun x hx => by simp at hx; subst hx⟩
    · obtain ⟨m, hm⟩ := ih hcs
      by_cases hcmp :
        treatment_cost exons c ≤ treatment_cost exons m
      · refine ⟨c, by simp, fun x hx => ?_⟩
        simp at hx
        cases hx with
        | inl hx => subst hx
        | inr hx =>
          exact le_trans hcmp (hm.2 x hx)
      · refine ⟨m, by simp [hm.1], fun x hx => ?_⟩
        simp at hx
        cases hx with
        | inl hx =>
          subst hx
          exact le_trans (hm.2 c (by simp)) (le_of_not_ge hcmp)
        | inr hx => exact hm.2 x hx

/-- インフレーム制約付き最適AON -/
def is_constrained_optimal_aon
  (exons : List Exon)
  (candidates : List AON)
  (aon : AON) : Prop :=
  (is_inframe (apply_aon aon exons)) ∧
  aon ∈ candidates ∧
  ∀ c ∈ candidates,
    is_inframe (apply_aon c exons) →
    treatment_cost exons aon ≤ treatment_cost exons c

/-- インフレーム制約付き最適AONの存在 -/
theorem constrained_aon_exists
  (exons : List Exon)
  (candidates : List AON)
  (h : ∃ aon ∈ candidates,
       is_inframe (apply_aon aon exons)) :
  ∃ aon, is_constrained_optimal_aon exons candidates aon := by
  classical
  rcases h with ⟨a0, ha0mem, ha0frame⟩
  let feasible :=
    candidates.filter
      (fun a => decide (is_inframe (apply_aon a exons)))
  have hne : feasible ≠ [] := by
    have : a0 ∈ feasible := by
      simp [feasible, ha0mem, ha0frame]
    intro hnil; simp [hnil] at this
  obtain ⟨aon, haon⟩ := optimal_aon_exists exons feasible hne
  refine ⟨aon, ?_, ?_, ?_⟩
  · have := haon.1; simp [feasible] at this; exact this.2
  · have := haon.1; simp [feasible] at this; exact this.1
  · intro c hc hframe
    have hc' : c ∈ feasible := by simp [feasible, hc, hframe]
    exact haon.2 c hc'

end DuchenneMD
