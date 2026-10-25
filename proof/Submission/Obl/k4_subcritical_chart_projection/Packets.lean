import Submission.Obl.k4_subcritical_chart_projection.Admissible
import Submission.Obl.k4_subcritical_chart_projection.Numerics
import Submission.Obl.k4_horizontal_supercritical_three_projections.HeavyCharts
import Submission.Obl.k4_horizontal_supercritical_three_projections.ChartNumerics
import Submission.Obl.k4_horizontal_supercritical_three_projections.ScalarUse

set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory
open scoped ENNReal BigOperators
open Submission.Obl.k4_horizontal_supercritical_three_projections
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- Apply Scalar in every retained chart. The full ensemble, its whole
domain floors, and its weighted success mass use the unchanged original prior. -/
theorem corrected_chart_packets {α : Type} [MeasurableSpace α]
    {N K d κ s₀ M ξ η τ cut η₀ Bmax : ℝ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hκ : 0 < κ) (hs₀ : 0 < s₀) (hξ : 0 < ξ)
    (hd : d < 1) (depth : Fin 3 → ℝ) (h : Fin 3)
    (hdepth : s₀ < depth h) (hmax : depth h ≤ Bmax)
    (ν : Measure α) [IsProbabilityMeasure ν] (μ ρ ζ : Measure (α × ℝ))
    (π : Measure ℝ) [IsFiniteMeasure π] (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (hρμ : ρ ≤ μ) (hμdom : μ ≤ ENNReal.ofReal K • (ν.prod volume))
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) (hρmass : ρ univ ≤ ENNReal.ofReal K)
    (hnative : OriginalJointCaps N K d M Bmax μ π b)
    (hnum : InputEstimates N K κ s₀ (depth h) M ξ η τ cut η₀)
    (hscalar : ∀ (νs : Measure α) (μs : Measure (α × ℝ)) (bs : α → Fin 5 → ℝ) (cs : ℝ),
      ScalarAdmissible N η d (depth h - s₀) (20 * s₀) 1 1 s₀ cs νs bs μs →
      ENNReal.ofReal (N ^ (-η)) ≤ μs univ →
      Nonempty (ScalarPackets N d (depth h - s₀) (20 * s₀) cs τ μs bs))
    (C : Charts b ρ π (N ^ (-M)) (N ^ (-(2 * κ * s₀))) (N ^ (-s₀))
      (N ^ (-(20 * s₀))) d (N ^ ξ) (N ^ (-ξ))
      (fun h => N ^ (-(depth h - s₀))))
    (hζ : ζ ≤ C.law) (hmass : ENNReal.ofReal (N ^ (-η₀)) ≤ ζ univ) :
    ∃ S : Finset (Fin C.n), ∃ F : (i : S) →
      ScalarPackets N d (depth h - s₀) (20 * s₀)
        (chartReference π (N ^ (-M)) (N ^ (-(2 * κ * s₀))) (N ^ (-s₀)) d (C.q i.val) /
          (ν (C.G i.val)).toReal) τ (chartLaw ν ζ (C.G i.val))
        (fun l => scalarCoefficients (N ^ (-(2 * κ * s₀))) (N ^ (-s₀))
          (C.q i.val 1) (C.q i.val 2) (C.g i.val) (b l)),
      (∀ i : S, ν (C.G i.val) ≠ 0) ∧
      (∀ i : S, 0 < π (Ico ((C.q i.val 0 : ℝ) * N ^ (-M))
        (((C.q i.val 0 : ℝ) + 1) * N ^ (-M)))) ∧
      (∀ (i : S) (j : Fin (F i).n), (F i).A j ⊆ C.G i.val) ∧
      ENNReal.ofReal (N ^ (-2 * τ)) ≤ ζ {p | ∃ (i : S) (j : Fin (F i).n), p.1 ∈ (F i).A j} := by
  classical
  let D := N ^ (-(2 * κ * s₀))
  let χ := N ^ (-M)
  let a := N ^ (-s₀)
  let H := N ^ ξ
  let W := fun c => chartReference π χ D a d (C.q c)
  let δ := N ^ (-cut)
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hK₀ : 0 < K := by linarith
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN₀ _
  have ha : 0 < a := Real.rpow_pos_of_pos hN₀ _
  have hH : 0 < H := Real.rpow_pos_of_pos hN₀ _
  have hW (c) : 0 ≤ W c := chartReference_nonneg π ha.le _
  have hζρ : ζ ≤ ρ := hζ.trans C.le
  have hζμ : ζ ≤ μ := hζρ.trans hρμ
  have hdom := hζμ.trans hμdom
  have hsuppζ : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
    le_antisymm ((hζμ _).trans_eq hsupp) bot_le
  have : IsFiniteMeasure ζ := ⟨(hζρ univ).trans_lt (hρmass.trans_lt ENNReal.ofReal_lt_top)⟩
  have hbudget : ∑ c, W c ≤ H * K := C.reference_budget ha hH (by linarith) hρmass
  have hcap : ∀ c, μ (C.G c ×ˢ univ) ≤ ENNReal.ofReal (N ^ (10 * ξ) * W c) :=
    corrected_chart_upper_cap hN hs₀ hκ (by linarith) hd.le hξ hnum.large hnum.xi_half
      depth h hdepth hmax μ ρ π b C hsupp hnative hnum.mesh hnum.variation hnum.whole
  obtain ⟨S, hS, hretained⟩ := select_dense_charts ν ζ μ C.G C.measurable C.disjoint
    W hW hK₀ (Real.rpow_pos_of_pos hN₀ (10 * ξ)) hδ hbudget hζμ hdom hsuppζ hcap
  have hfull : ζ {p | ∃ c, p.1 ∈ C.G c} = ζ univ := by
    apply measure_congr
    filter_upwards [ae_mono hζ C.cover] with p hp
    apply propext
    exact ⟨fun _ => mem_univ _, fun _ => hp⟩
  rw [hfull] at hretained
  have hhalf : ENNReal.ofReal (N ^ (-η₀) / 2) ≤ ζ {p | ∃ c ∈ S, p.1 ∈ C.G c} := by
    apply ENNReal.le_of_add_le_add_right (ENNReal.ofReal_ne_top :
      ENNReal.ofReal (N ^ (-η₀) / 2) ≠ ⊤)
    calc
      _ = ENNReal.ofReal (N ^ (-η₀)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ _ := hmass.trans hretained
      _ ≤ _ := add_le_add le_rfl (ENNReal.ofReal_le_ofReal hnum.prune)
  have hadm (i : S) : ∃ F : ScalarPackets N d (depth h - s₀) (20 * s₀)
      (W i.val / (ν (C.G i.val)).toReal) τ (chartLaw ν ζ (C.G i.val))
      (fun l => scalarCoefficients D a (C.q i.val 1) (C.q i.val 2) (C.g i.val) (b l)),
      ∀ j, F.A j ⊆ C.G i.val := by
    have hactive := hS i.val i.property
    have hKten : K ≤ N ^ (10 * ξ) := hnum.K_le.trans
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
    have hratio := active_chart_scalar_bounds hN hKten hnum.cut_eta hnum.ten_xi_eta
      hnum.ratio_one (by linarith [hnum.support_budget]) hactive.2.2.2.2.1 hactive.2.2.2.2.2.1
    have hdomη : ζ ≤ ENNReal.ofReal (N ^ η) • (ν.prod volume) := by
      apply hdom.trans
      intro E
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hnum.K_eta) le_rfl
    have hsupport : H ≤ N ^ η * (W i.val / (ν (C.G i.val)).toReal)⁻¹ :=
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith : ξ ≤ 10 * ξ)).trans hratio.2.2.2.2.2
    have hiadm := corrected_scalar_admissible hN hs₀ hκ hξ (by linarith)
      depth h hdepth hmax ν μ ρ ζ π b hb C hζ hζμ hdomη hsupp hnative
      hnum.mesh hnum.mesh_square hnum.variation hnum.pure hnum.coefficient i.val
      hactive.1 hratio.2.1 hratio.2.2.1 hsupport
    have hmassnorm : ENNReal.ofReal (N ^ (-η)) ≤ chartLaw ν ζ (C.G i.val) univ :=
      (ENNReal.ofReal_le_ofReal hratio.2.2.2.1).trans hactive.2.2.2.2.2.2
    let bs := fun l => scalarCoefficients D a (C.q i.val 1) (C.q i.val 2) (C.g i.val) (b l)
    obtain ⟨F⟩ := hscalar (ProbabilityTheory.cond ν (C.G i.val)) (chartLaw ν ζ (C.G i.val))
      (padCoefficients (C.G i.val) bs) (W i.val / (ν (C.G i.val)).toReal) hiadm hmassnorm
    let F' := F.trim (C.measurable i.val) (chartLaw_supported ν ζ (C.measurable i.val))
      (fun l hl => padCoefficients_eq bs hl)
    exact ⟨F', fun j l hl => hl.2⟩
  choose F hFsub using hadm
  have hpalette (i : S) : 0 < π (Ico ((C.q i.val 0 : ℝ) * χ)
      (((C.q i.val 0 : ℝ) + 1) * χ)) := by
    by_contra hn
    have hz : π (Ico ((C.q i.val 0 : ℝ) * χ)
        (((C.q i.val 0 : ℝ) + 1) * χ)) = 0 := le_antisymm (le_of_not_gt hn) zero_le
    have hh := (hS i.val i.property).2.1
    simp only [W, chartReference, hz, ENNReal.toReal_zero, zero_mul, lt_self_iff_false] at hh
  have hν (i : S) : ν (C.G i.val) ≠ 0 := (hS i.val i.property).1
  refine ⟨S, F, hν, hpalette, hFsub, ?_⟩
  let A := fun i : S => {p : α × ℝ | ∃ j, p.1 ∈ (F i).A j}
  have hA (i : S) : MeasurableSet (A i) := by
    simp only [A, Set.ofPred_exists]
    exact MeasurableSet.iUnion fun j => ((F i).measurable j).preimage measurable_fst
  have hdisj : Pairwise (fun i j : S => Disjoint (C.G i.val) (C.G j.val)) := by
    intro i j hij
    exact C.disjoint i.val j.val (fun heq => hij (Subtype.ext heq))
  have hdA : Pairwise (fun i j : S => Disjoint (A i) (A j)) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro p ⟨a, ha⟩ ⟨a', ha'⟩
    exact disjoint_left.mp (hdisj hij) (hFsub i a ha) (hFsub j a' ha')
  have hsum : (∑ i : S, ENNReal.ofReal ((ν (C.G i.val)).toReal * N ^ (-τ))) ≤
      ζ {p | ∃ (i : S) (j : Fin (F i).n), p.1 ∈ (F i).A j} := by
    have hcov : {p : α × ℝ | ∃ (i : S) (j : Fin (F i).n), p.1 ∈ (F i).A j} = ⋃ i, A i := by
      ext p
      simp only [A, mem_ofPred_eq, mem_iUnion]
    rw [hcov, measure_iUnion hdA hA, tsum_fintype]
    apply Finset.sum_le_sum
    intro i _
    exact ((F i).restore ν ζ (C.G i.val) (hν i) _).2
  have hmass' := scalar_ensemble_mass ν ζ (fun i : S => C.G i.val)
    (fun i => C.measurable i.val) hdisj hK₀ (Real.rpow_nonneg hN₀.le (-τ))
    hdom hsuppζ {p | ∃ (i : S) (j : Fin (F i).n), p.1 ∈ (F i).A j} hsum
  have heq : {p : α × ℝ | ∃ i : S, p.1 ∈ C.G i.val} =
      {p | ∃ c ∈ S, p.1 ∈ C.G c} := by
    ext p
    simp only [exists_prop, Subtype.exists]
  rw [heq] at hmass'
  calc
    _ ≤ ENNReal.ofReal ((N ^ (-τ) / K) * (N ^ (-η₀) / 2)) :=
      ENNReal.ofReal_le_ofReal hnum.success
    _ = ENNReal.ofReal (N ^ (-τ) / K) * ENNReal.ofReal (N ^ (-η₀) / 2) :=
      ENNReal.ofReal_mul (by positivity)
    _ ≤ _ := (mul_le_mul' le_rfl hhalf).trans hmass'

end Submission.Obl.k4_subcritical_chart_projection
