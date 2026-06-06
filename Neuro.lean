import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
  # ニューロダイバーシティの数理モデル (Neurodiversity Framework)
  
  Licensed under Apache 2.0 (Author: Takeo Yamamoto / 山本健夫)
  
  神経学的多様性は、単なる社会的配慮ではなく、集団としての情報処理能力を
  極大化させ、環境変動（バグ）に対する系の堅牢性を保証する「情報の冗長性」
  および「検索空間の拡張」である。
-/

namespace Neurodiversity

/-- 
  集団の適応度（Fitness）
  - `μ`  : 標準的思考スキーム（標準個体群の処理効率）
  - `σ`  : 思考スキームの多様性（差異の広がり）
  - `E`  : 環境の複雑性（解決すべき課題の未知数）
-/
structure Population where
  μ : ℝ
  σ : ℝ
  E : ℝ
  μ_pos : 0 < μ
  σ_pos : 0 ≤ σ
  E_pos : 0 < E

/-- 
  集団の課題解決能力関数 (Collective Problem Solving Capacity)
  多様性（σ）が環境の複雑性（E）と噛み合うことで、単一の標準的効率（μ）
  を超越した「創発的な解」を生み出す。
-/
noncomputable def collective_capacity (pop : Population) : ℝ :=
  pop.μ + (pop.σ * pop.E)

/-- 
  標準化バイアス（Normalization Bias）
  社会OSが、多様性（σ）を「非効率なノイズ」として排除し、μのみを強制する状態。
  このとき、集団の capacity は標準的な μ に縮退する。
-/
def standardized_capacity (pop : Population) : ℝ :=
  pop.μ

---

### ニューロダイバーシティの根本定理

/-- 
  【定理：多様性のレバレッジ】
  環境の複雑性（E）が正である限り、思考の多様性（σ > 0）を排除する
  標準化社会（standardized_capacity）は、常にニューロダイバーシティを
  許容する社会（collective_capacity）に対して、知的な解決能力において
  劣後することを証明する。
-/
theorem diversity_leverage_theorem (pop : Population) (h_div : 0 < pop.σ) (h_env : 0 < pop.E) :
    standardized_capacity pop < collective_capacity pop := by
  unfold standardized_capacity collective_capacity
  -- μ < μ + σ * E 
  -- 両辺から μ を引くと 0 < σ * E
  have h_gain : 0 < pop.σ * pop.E := mul_pos h_div h_env
  linarith

/-- 
  【定理：システム堅牢性（堅牢なエコシステム）】
  環境が急激に変化する際（E の増大）、σ を持たない社会は単一の失敗モード
  （陳腐化）に陥るが、多様性を持つ系は、異なるモードの解決策を保持することで
  システム全体のエントロピー増大を抑制する。
-/
theorem robustness_advantage (pop : Population) (h_div : 0 < pop.σ) :
    ∀ E₁ E₂ : ℝ, E₁ < E₂ → 
    (collective_capacity {pop with E := E₁}) < (collective_capacity {pop with E := E₂}) := by
  intro E₁ E₂ h_env
  unfold collective_capacity
  simp
  linarith [h_div, h_env]

end Neurodiversity
