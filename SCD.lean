import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

namespace SickleCellDisease

open Classical

inductive HbType : Type
  | HbA | HbS | HbF | HbA2
  deriving Repr, DecidableEq, Inhabited

structure HbComposition where
  hbA  : ℝ
  hbS  : ℝ
  hbF  : ℝ
  hbA2 : ℝ
  deriving Repr, Inhabited

def HbComposition.valid (c : HbComposition) : Prop :=
  c.hbA ≥ 0 ∧ c.hbS ≥ 0 ∧ c.hbF ≥ 0 ∧ c.hbA2 ≥ 0 ∧
  c.hbA + c.hbS + c.hbF + c.hbA2 = 1

def sickling_index (c : HbComposition) : ℝ :=
  c.hbS / (c.hbS + c.hbF + 1)

def oxygen_affinity (c : HbComposition) : ℝ :=
  1 - c.hbS / 2

inductive TherapyType : Type
  | HydroxyureaHU | BCL11AInhibitor | BaseEditing | GeneTherapy | AlloSCT
  deriving Repr, DecidableEq, Inhabited

structure Therapy where
  modality      : TherapyType
  hbF_delta     : ℝ
  hbS_delta     : ℝ
  toxicity      : ℝ
  accessibility : ℝ
  deriving Repr, Inhabited

def apply_therapy (base : HbComposition) (t : Therapy) : HbComposition :=
  { hbA  := base.hbA
    hbS  := max 0 (base.hbS + t.hbS_delta)
    hbF  := min 1 (base.hbF + t.hbF_delta)
    hbA2 := base.hbA2 }

def clinical_efficacy (base : HbComposition) (t : Therapy) : ℝ :=
  sickling_index base - sickling_index (apply_therapy base t)

def hbF_threshold : ℝ := 0.20

def meets_hbF_target (base : HbComposition) (t : Therapy) : Prop :=
  (apply_therapy base t).hbF ≥ hbF_threshold

def treatment_cost (base : HbComposition) (t : Therapy) : ℝ :=
  - clinical_efficacy base t
  + t.toxicity
  + (1 - t.accessibility)

def is_optimal_therapy
    (base : HbComposition) (candidates : List Therapy) (t : Therapy) : Prop :=
  t ∈ candidates ∧
  ∀ c ∈ candidates, treatment_cost base t ≤ treatment_cost base c

theorem optimal_therapy_exists
    (base : HbComposition) (candidates : List Therapy) (h : candidates ≠ []) :
    ∃ t, is_optimal_therapy base candidates t := by
  induction candidates with
  | nil => contradiction
  | cons c cs ih =>
    by_cases hcs : cs = []
    · subst hcs
      refine ⟨c, List.mem_cons_self c [], fun x hx => ?_⟩
      simp at hx; subst hx
    · obtain ⟨m, hm⟩ := ih hcs
      by_cases hcmp : treatment_cost base c ≤ treatment_cost base m
      · refine ⟨c, List.mem_cons_self c cs, fun x hx => ?_⟩
        simp [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact le_refl _                      -- ① subst 後のゴールを閉じる
        · exact le_trans hcmp (hm.2 x hx)
      · refine ⟨m, List.mem_cons_of_mem c hm.1, fun x hx => ?_⟩
        simp [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact (not_le.mp hcmp).le            -- ② le_of_not_ge → not_le.mp + .le
        · exact hm.2 x hx

def is_constrained_optimal_therapy
    (base : HbComposition) (candidates : List Therapy) (t : Therapy) : Prop :=
  meets_hbF_target base t ∧
  t ∈ candidates ∧
  ∀ c ∈ candidates,
    meets_hbF_target base c →
    treatment_cost base t ≤ treatment_cost base c

theorem constrained_therapy_exists
    (base : HbComposition) (candidates : List Therapy)
    (h : ∃ t ∈ candidates, meets_hbF_target base t) :
    ∃ t, is_constrained_optimal_therapy base candidates t := by
  rcases h with ⟨t0, ht0mem, ht0hbF⟩
  let feasible :=
    candidates.filter (fun t => decide (meets_hbF_target base t))
  have hne : feasible ≠ [] := by
    apply List.ne_nil_of_mem (a := t0)
    simp only [feasible, List.mem_filter, decide_eq_true_eq]  -- ③ let 展開 + decide↔Prop
    exact ⟨ht0mem, ht0hbF⟩
  obtain ⟨t, ht⟩ := optimal_therapy_exists base feasible hne
  have ht_feas := ht.1
  simp only [feasible, List.mem_filter, decide_eq_true_eq] at ht_feas
  refine ⟨ht_feas.2, ht_feas.1, fun c hc hfeas => ?_⟩
  apply ht.2
  simp only [feasible, List.mem_filter, decide_eq_true_eq]
  exact ⟨hc, hfeas⟩

end SickleCellDisease
