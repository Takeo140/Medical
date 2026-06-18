import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

namespace ImmunotherapyOS

/-- 1. 受容体・リガンドの結合状態（免疫エスケープ状態）の定義 -/
inductive ReceptorState where
  | Evading     -- PD-L1が結合し、T細胞にブレーキがかかって隠れている状態（バグ）
  | Neutralized -- 治療用パッチ（抗体）が結合し、ブレーキを無効化した状態
  deriving Repr, DecidableEq

structure TCellInteraction where
  id    : Nat
  state : ReceptorState

/-- 2. 評価関数：免疫エスケープ・スコア（腫瘍がどれだけ免疫から逃げ延びているか） -/
def total_evasion_score : List TCellInteraction → Nat
  | [] => 0
  | x :: xs => (if x.state = .Evading then 10 else 0) + total_evasion_score xs

/-- 3. 免疫療法パッチ（チェックポイント阻害剤の論理コード）
    エスケープ状態（Evading）にある受容体を、強制的に中和状態（Neutralized）へ書き換える -/
def checkpoint_inhibitor_patch : List TCellInteraction → List TCellInteraction
  | [] => []
  | x :: xs =>
    (if x.state = .Evading then { x with state := .Neutralized } else x)
    :: checkpoint_inhibitor_patch xs

/-- 4. 【数学的証明】パッチを適用すると、免疫エスケープ・スコアは「確実に 0 」になる -/
theorem patch_completely_neutralizes (l : List TCellInteraction) :
  total_evasion_score (checkpoint_inhibitor_patch l) = 0 := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
    simp [checkpoint_inhibitor_patch, total_evasion_score]
    split_ifs with h1
    · -- ケースA: head.state = .Evading の場合
      -- パッチによって .Neutralized に書き換わるため、スコア加算は 0 になり、帰納法の仮定(ih)へ収束する
      exact ih
    · -- ケースB: head.state ≠ .Evading の場合
      -- 元からエスケープしていないためスコアは 0 であり、そのまま帰納法の仮定(ih)へ収束する
      exact ih

/-- 5. メイン定理：この免疫療法は「決定論的に有効（Guaranteed Effective）」である -/
def is_effective_immunotherapy (before after : List TCellInteraction) : Prop :=
  (total_evasion_score before > 0 → total_evasion_score after = 0)

theorem immunotherapy_is_guaranteed (l : List TCellInteraction) :
  is_effective_immunotherapy l (checkpoint_inhibitor_patch l) := by
  unfold is_effective_immunotherapy
  intro _
  exact patch_completely_neutralizes l

end ImmunotherapyOS
