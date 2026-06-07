-- Author: Takeo Yamamoto / 山本健夫
-- License: Apache 2.0
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
/-!
  # ニューロダイバーシティの数理モデル (Neurodiversity Framework)

  神経学的多様性は、集団としての情報処理能力を極大化させ、
  環境変動に対する系の堅牢性を保証する「情報の冗長性」および
  「検索空間の拡張」である。
-/
namespace Neurodiversity

structure Population where
  μ : ℝ
  σ : ℝ
  E : ℝ
  μ_pos : 0 < μ
  σ_pos : 0 ≤ σ
  E_pos : 0 < E

/-- 集団の課題解決能力: μ + σ * E -/
noncomputable def collective_capacity (pop : Population) : ℝ :=
  pop.μ + pop.σ * pop.E

/-- 標準化バイアス下での能力: μ のみ -/
noncomputable def standardized_capacity (pop : Population) : ℝ :=  -- ← ③修正
  pop.μ

/-- 【定理：多様性のレバレッジ】σ > 0, E > 0 ならば標準化社会は多様性社会に劣後する -/
theorem diversity_leverage_theorem
    (pop : Population) (h_div : 0 < pop.σ) (h_env : 0 < pop.E) :
    standardized_capacity pop < collective_capacity pop := by
  unfold standardized_capacity collective_capacity
  have h_gain : 0 < pop.σ * pop.E := mul_pos h_div h_env
  linarith

/-- 【定理：システム堅牢性】環境複雑性 E の増大に対し、多様性集団の能力は単調増加する -/
theorem robustness_advantage
    (pop : Population) (h_div : 0 < pop.σ) :
    ∀ E₁ E₂ : ℝ, 0 < E₁ → E₁ < E₂ →         -- ← ①修正: E₁ > 0 の前提を追加
    collective_capacity { pop with E := E₁,
                                   E_pos := by assumption } 
    collective_capacity { pop with E := E₂,
                                   E_pos := by linarith } := by
  intro E₁ E₂ hE₁ hE₂
  unfold collective_capacity
  simp only [Population.mk.injEq]              -- ← ②修正: simp の代わりに明示展開
  nlinarith [h_div, hE₁, hE₂]

end Neurodiversity
