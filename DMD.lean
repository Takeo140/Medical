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
  length : ℕ
  deriving Repr, Inhabited

/-- リーディングフレーム：0, 1, 2 -/
def Frame := Fin 3

/-- エクソン列からフレームを累積計算 -/
def frame_of (exons : List Exon) : ℕ :=
  (exons.foldl (fun acc e =>
    if e.state == ExonState.present || e.state == ExonState.skipped
    then acc
    else acc + e.length) 0) % 3

/-- フレーム内（インフレーム）判定 -/
def is_inframe (exons : List Exon) : Prop :=
  frame_of exons = 0

-- Decidable インスタンスを明示（dystrophin_function の if 分岐に必要）
instance (exons : List Exon) : Decidable (is_inframe exons) :=
  inferInstance

/-- アンチセンスオリゴ（AON）治療候補 -/
structure AON where
  target_exon : ℕ
  efficacy    : ℝ
  off_target  : ℝ
  deriving Repr, Inhabited

/-- AON適用：対象エクソンをskipped状態に変更 -/
def apply_aon (aon : AON) (exons : List Exon) : List Exon :=
  exons.map (fun e =>
    if e.index = aon.target_exon
    then { e with state := ExonState.skipped }
    else e)

/-- 機能的ジストロフィン近似 -/
def dystrophin_function (exons : List Exon) (aon : AON) : ℝ :=
  let treated := apply_aon aon exons
  let present_count :=
    (treated.filter (fun e => e.state == ExonState.present)).length
  if is_inframe treated
  then (present_count : ℝ) / (exons.length : ℝ)
  else 0

/-- 安全性スコア -/
def safety_score (aon : AON) : ℝ :=
  1 / (1 + aon.off_target)

/-- 投与負担 -/
def dosage_burden (aon : AON) : ℝ :=
  1 / (1 + aon.efficacy)

/-- 総合治療コスト -/
def treatment_cost (exons : List Exon) (aon : AON) : ℝ :=
  - dystrophin_function exons aon
  + (1 - safety_score aon)
  + dosage_burden aon

/-- 最適AON候補（定義）-/
def is_optimal_aon
    (exons : List Exon) (candidates : List AON) (aon : AON) : Prop :=
  aon ∈ candidates ∧
  ∀ c ∈ candidates, treatment_cost exons aon ≤ treatment_cost exons c

/-- 非空候補集合では最適AONが存在 -/
theorem optimal_aon_exists
    (exons : List Exon) (candidates : List AON) (h : candidates ≠ []) :
    ∃ aon, is_optimal_aon exons candidates aon := by
  induction candidates with
  | nil => contradiction
  | cons c cs ih =>
    by_cases hcs : cs = []
    · -- cs = [] のとき c が唯一の候補
      subst hcs
      refine ⟨c, List.mem_cons_self c [], fun x hx => ?_⟩
      simp at hx
      subst hx
    · -- cs 非空：帰納仮定から最適 m を取得
      obtain ⟨m, hm⟩ := ih hcs
      by_cases hcmp : treatment_cost exons c ≤ treatment_cost exons m
      · -- c のコストが m 以下 → c が新しい最適
        refine ⟨c, List.mem_cons_self c cs, fun x hx => ?_⟩
        simp [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact le_refl _                          -- x = c の場合
        · exact le_trans hcmp (hm.2 x hx)         -- x ∈ cs の場合
      · -- m のコストが c より小さい → m を継続採用
        refine ⟨m, List.mem_cons_of_mem c hm.1, fun x hx => ?_⟩
        simp [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact (not_le.mp hcmp).le               -- x = c の場合：hcmp を le に変換
        · exact hm.2 x hx                         -- x ∈ cs の場合

/-- インフレーム制約付き最適AON -/
def is_constrained_optimal_aon
    (exons : List Exon) (candidates : List AON) (aon : AON) : Prop :=
  (is_inframe (apply_aon aon exons)) ∧
  aon ∈ candidates ∧
  ∀ c ∈ candidates,
    is_inframe (apply_aon c exons) →
    treatment_cost exons aon ≤ treatment_cost exons c

/-- インフレーム制約付き最適AONの存在 -/
theorem constrained_aon_exists
    (exons : List Exon) (candidates : List AON)
    (h : ∃ aon ∈ candidates, is_inframe (apply_aon aon exons)) :
    ∃ aon, is_constrained_optimal_aon exons candidates aon := by
  rcases h with ⟨a0, ha0mem, ha0frame⟩
  -- インフレームを満たす候補のみ抽出
  let feasible :=
    candidates.filter (fun a => decide (is_inframe (apply_aon a exons)))
  -- feasible が非空であることを示す
  have hne : feasible ≠ [] := by
    apply List.ne_nil_of_mem (a := a0)
    simp only [feasible, List.mem_filter, decide_eq_true_eq]
    exact ⟨ha0mem, ha0frame⟩
  -- feasible 上の最適 AON を取得
  obtain ⟨aon, haon⟩ := optimal_aon_exists exons feasible hne
  -- aon の feasible メンバーシップを分解
  have haon_feas := haon.1
  simp only [feasible, List.mem_filter, decide_eq_true_eq] at haon_feas
  -- 制約付き最適性を構築
  refine ⟨haon_feas.2, haon_feas.1, fun c hc hframe => ?_⟩
  apply haon.2
  simp only [feasible, List.mem_filter, decide_eq_true_eq]
  exact ⟨hc, hframe⟩

end DuchenneMD
