import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.MetricSpace.Basic

namespace UniversalOptimizationKernel

@[ext]
structure BioState where
  genomic_integrity   : ℝ
  metabolic_balance   : ℝ
  proteostatic_health : ℝ
  immune_calibration  : ℝ

def is_wildtype (s : BioState) : Prop :=
  s.genomic_integrity > 0.99 ∧
  s.metabolic_balance ∈ Set.Icc 0.8 1.2 ∧
  s.proteostatic_health > 0.9 ∧
  s.immune_calibration > 0.9

noncomputable def optimization_potential (s : BioState) : ℝ :=
  (1 - s.genomic_integrity)^2 +
  (1 - s.metabolic_balance)^2 +
  (1 - s.proteostatic_health)^2 +
  (1 - s.immune_calibration)^2

lemma V_nonneg (s : BioState) : 0 ≤ optimization_potential s := by
  unfold optimization_potential; positivity

/-- 指数減衰パス：各成分が wildtype（= 1）へ指数収束 -/
noncomputable def decay_path (b : BioState) (t : ℝ) : BioState where
  genomic_integrity   := 1 + (b.genomic_integrity   - 1) * Real.exp (-t)
  metabolic_balance   := 1 + (b.metabolic_balance   - 1) * Real.exp (-t)
  proteostatic_health := 1 + (b.proteostatic_health - 1) * Real.exp (-t)
  immune_calibration  := 1 + (b.immune_calibration  - 1) * Real.exp (-t)

lemma decay_path_at_zero (b : BioState) : decay_path b 0 = b := by
  ext <;> simp [decay_path, Real.exp_zero]

/-- V(path t) = V(initial) * exp(-2t) という具体形 -/
lemma potential_along_decay (b : BioState) (t : ℝ) :
    optimization_potential (decay_path b t) =
    optimization_potential b * Real.exp (-2 * t) := by
  simp only [optimization_potential, decay_path]
  have h : (Real.exp (-t)) ^ 2 = Real.exp (-2 * t) := by
    rw [← Real.exp_natCast]; norm_num [Real.exp_mul, Real.exp_neg, Real.exp_two]
  simp only [h]
  ring

theorem universal_recovery_possible (initial : BioState) :
    ∃ path : ℝ → BioState,
      path 0 = initial ∧
      Filter.Tendsto (fun t => optimization_potential (path t))
        Filter.atTop (nhds 0) := by
  refine ⟨decay_path initial, decay_path_at_zero initial, ?_⟩
  simp_rw [potential_along_decay]
  -- exp(-2t) → 0 as t → ∞
  have h_exp : Filter.Tendsto (fun t : ℝ => Real.exp (-2 * t))
      Filter.atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot_nhds_zero.comp (tendsto_neg_atTop_iff.mpr tendsto_atTop_id)
  exact mul_zero (optimization_potential initial) ▸
    Filter.Tendsto.mul_const h_exp (optimization_potential initial)

end UniversalOptimizationKernel
