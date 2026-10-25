import Submission.Obl.k4_scalar_candidate_original_return.Core.Globalize
import Submission.Obl.k4_scalar_candidate_original_return.SplitInterfaces
import Submission.Lib.K4FinitePlankAtlases.Assignments

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set
open Submission.Lib.K4FinitePlankAtlases

private theorem threshold_to_fixed {α β : Type*} [MeasurableSpace α]
    {F : β → Set α} {t : β → ℝ} {η : ℝ} {μ : Measure α} {l : List β}
    (h : ThresholdGreedySequence F t μ l) (hf : ∀ b ∈ l, η ≤ t b) :
    GreedySequence F η μ l := by
  revert hf
  induction h with
  | nil μ => intro _; exact .nil μ
  | @cons μ b l hb ht ih =>
    intro hf
    exact .cons ((hf b (by simp)).trans hb)
      (ih (fun c hc => hf c (by simp [hc])))

private theorem fixed_length_le {α β : Type*} [MeasurableSpace α]
    {F : β → Set α} {η : ℝ} {μ : Measure α} {l : List β}
    (hF : ∀ b, MeasurableSet (F b)) (h : GreedySequence F η μ l) :
    ∀ [IsFiniteMeasure μ], (l.length : ℝ) * η ≤ μ.real univ := by
  induction h with
  | nil μ => intro _; simp
  | @cons μ b l hb ht ih =>
    intro hμ
    have hh : (l.length : ℝ) * η ≤ (μ.restrict (F b)ᶜ).real univ := ih
    rw [measureReal_restrict_apply_univ, measureReal_compl (hF b)] at hh
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

namespace PreparedData

variable {a : PreparedData} (ha : a.Valid)
include ha

/-- The original dominated incidence mass of a full block has its full-prior budget. -/
lemma plank_real_le_prior (k : ℕ) (ℓ : Fin (a.ct k)) (i : Fin (a.ls k ℓ).n) :
    (a.plankMeasure k ℓ i).real univ ≤
      (ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i)).toReal /
        (2 : ℝ) ^ (a.ls k ℓ).T := by
  let q := a.ls k ℓ
  have hν := ((ha.exact k).2.1 (a.sm k)).2.2.2.1 (q.world i)
  haveI : IsProbabilityMeasure (ν (a.p k) (a.sm k) (q.world i)) := hν.1
  have hvol : volume (I q.T (q.time i)) = ENNReal.ofReal ((2 : ℝ) ^ q.T)⁻¹ := by
    change volume (Icc (((q.time i : ℕ) : ℝ) / (2 : ℝ) ^ q.T)
      ((((q.time i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ q.T)) = _
    rw [Real.volume_Icc]
    have he : (((q.time i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ q.T -
        ((q.time i : ℕ) : ℝ) / (2 : ℝ) ^ q.T = ((2 : ℝ) ^ q.T)⁻¹ := by ring
    rw [he, ENNReal.ofReal_inv_of_pos (by positivity)]
  have hmass : a.ρ k (q.world i) (a.plank k ℓ i) ≤
      ν (a.p k) (a.sm k) (q.world i) (q.prior i) *
        ENNReal.ofReal ((2 : ℝ) ^ q.T)⁻¹ := by
    calc _ ≤ mu (a.p k) (a.sm k) (q.world i) (a.plank k ℓ i) := ha.rho_le _ _ _
      _ ≤ ((ν (a.p k) (a.sm k) (q.world i)).prod volume) (a.plank k ℓ i) :=
        Measure.restrict_le_self _
      _ = _ := by rw [plank, Measure.prod_prod, hvol]
  have hfinite : ν (a.p k) (a.sm k) (q.world i) (q.prior i) *
      ENNReal.ofReal ((2 : ℝ) ^ q.T)⁻¹ ≠ ⊤ := by finiteness
  have ht := ENNReal.toReal_mono hfinite hmass
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at ht
  unfold plankMeasure
  rw [measureReal_restrict_apply_univ]
  simpa only [measureReal_def, div_eq_mul_inv] using ht

/-- The full-prior floor controls the greedy count without conditioning its prior. -/
lemma greedy_length_le (θ : ℝ) (hθ : 0 < θ) (σ : Scenario) (hc : 0 < σ.c₀)
    (k : ℕ) (ℓ : Fin (a.ct k)) (i : Fin (a.ls k ℓ).n) :
    ((a.greedy θ σ k ℓ i).length : ℝ) ≤ a.tangent k ^ (a.rd * σ.c₀ + 2 * θ * σ.c₀) := by
  classical
  let l := a.greedy θ σ k ℓ i
  change (l.length : ℝ) ≤ a.tangent k ^ (a.rd * σ.c₀ + 2 * θ * σ.c₀)
  have hN : 2 ≤ a.tangent k := ha.tangent_input.1 k
  have hN0 : 0 < a.tangent k := by linarith
  have hN1 : 1 ≤ a.tangent k := by linarith
  by_cases hl : l = []
  · simp only [hl, List.length_nil, Nat.cast_zero]
    positivity
  have hlen : 0 < l.length := List.ne_nil_iff_length_pos.mp hl
  let j : Fin l.length := ⟨0, hlen⟩
  have hthr : 0 < a.thr θ σ k ℓ i := (greedy_entry ha θ σ k ℓ i j).2.1
  have hf : ∀ P ∈ l, a.thr θ σ k ℓ i ≤ a.greedyThr θ σ k ℓ i P := by
    intro P hP
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hP
    have he := greedy_entry ha θ σ k ℓ i j
    have hcond : a.Admissible σ k (l.get j) ∧ 0 < a.thr θ σ k ℓ i := ⟨he.1, he.2.1⟩
    simp only [greedyThr, if_pos hcond, le_refl]
  have hg := threshold_to_fixed (greedy_spec ha θ σ k ℓ i).1 hf
  haveI := rho_finite ha k ((a.ls k ℓ).world i)
  haveI : IsFiniteMeasure (a.plankMeasure k ℓ i) := by unfold plankMeasure; infer_instance
  have hm := (fixed_length_le (candSet_measurable ha θ σ k ℓ i) hg).trans
    (plank_real_le_prior ha k ℓ i)
  let B := (ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i)).toReal /
    (2 : ℝ) ^ (a.ls k ℓ).T
  let t := a.tangent k ^ (a.rd * σ.c₀ + θ * σ.c₀)
  have ht : 0 < t := Real.rpow_pos_of_pos hN0 _
  have hid : a.thr θ σ k ℓ i = B / t := by
    dsimp only [thr, B, t]
    rw [show -a.rd * σ.c₀ - θ * σ.c₀ = -(a.rd * σ.c₀ + θ * σ.c₀) by ring,
      Real.rpow_neg hN0.le]
    ring
  have hB : 0 < B := by
    rw [hid] at hthr
    exact (div_pos_iff_of_pos_right ht).mp hthr
  have hm' : (l.length : ℝ) * (B / t) ≤ B := by simpa only [hid] using hm
  have hn : (l.length : ℝ) ≤ t := by
    apply (mul_le_mul_iff_right₀ hB).mp
    calc B * (l.length : ℝ) = ((l.length : ℝ) * (B / t)) * t := by field_simp
      _ ≤ B * t := mul_le_mul_of_nonneg_right hm' ht.le
  exact hn.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith))

end PreparedData
end Submission.Obl.k4_scalar_candidate_original_return
