import Mathlib.Data.Real.Basic

namespace MetaConflictDetector

structure SafetyStandard where
  max_qt_interval : ℝ := 0.44
  min_hbF_level   : ℝ := 0.20
  max_toxicity    : ℝ := 5.0

structure SystemHealth where
  qt_val            : ℝ
  hbF_val           : ℝ
  cancer_cell_count : ℝ

def is_conflicting
    (standard : SafetyStandard)
    (before after : SystemHealth) : Prop :=
  (after.qt_val > standard.max_qt_interval ∧ before.qt_val ≤ standard.max_qt_interval) ∨
  (after.hbF_val < standard.min_hbF_level  ∧ before.hbF_val ≥ standard.min_hbF_level)

def is_safe_and_effective
    (standard : SafetyStandard)
    (before after : SystemHealth) : Prop :=
  after.cancer_cell_count < before.cancer_cell_count ∧
  ¬ is_conflicting standard before after

/-- 定理：治療前が正常範囲内 かつ 安全な治療であれば、治療後も正常範囲内に収まる
    ※ hb（治療前の正常性）は定理の成立に論理的に必須な仮定 -/
theorem approval_logic
    (standard : SafetyStandard)
    (before after : SystemHealth)
    (h  : is_safe_and_effective standard before after)
    (hb : before.qt_val ≤ standard.max_qt_interval) :   -- ← 追加：必須仮定
    after.qt_val ≤ standard.max_qt_interval := by
  obtain ⟨_, h_nc⟩ := h
  unfold is_conflicting at h_nc
  -- ¬(P ∨ Q) → (P → ⊥) ∧ (Q → ⊥) の形に変換
  push_neg at h_nc
  obtain ⟨h_qt, _⟩ := h_nc
  -- h_qt : after.qt_val > max_qt_interval → ¬(before.qt_val ≤ max_qt_interval)
  by_contra h_contra
  push_neg at h_contra
  -- h_contra : after.qt_val > max_qt_interval → h_qt が hb を否定 → 矛盾
  exact absurd hb (h_qt h_contra)

def test_anti_cancer_patch (before : SystemHealth) : SystemHealth :=
  { qt_val            := before.qt_val + 0.05,
    hbF_val           := before.hbF_val,
    cancer_cell_count := before.cancer_cell_count - 1000.0 }

example :
    let std := SafetyStandard.mk 0.44 0.20 5.0
    let b   := SystemHealth.mk 0.40 0.25 5000.0
    let a   := test_anti_cancer_patch b
    is_conflicting std b a := by
  simp [is_conflicting, test_anti_cancer_patch]
  left
  constructor <;> norm_num   -- 0.45 > 0.44 かつ 0.40 ≤ 0.44 を数値計算で解決

end MetaConflictDetector
