-- Adapted from: here:o202 (session x0952), Regularization/BinRegularization.lean.
import Submission.Lib.K4CoefficientBinRegularization.CoefficientCover
import Submission.Lib.K4CoefficientBinRegularization.LightBins

namespace Submission.Lib.K4CoefficientBinRegularization.Reg

open MeasureTheory Set FirstJet
open scoped ENNReal Classical

noncomputable section

/-- The coefficient resolution in the relative cap. -/
def dyadicWidth (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℤ))

theorem dyadicWidth_pos (n : ℕ) : 0 < dyadicWidth n := by dsimp [dyadicWidth]; positivity

theorem dyadicWidth_le_one (n : ℕ) : dyadicWidth n ≤ 1 := by
  dsimp [dyadicWidth]
  rw [zpow_neg, zpow_natCast]
  apply (inv_le_one₀ (by positivity)).mpr
  exact one_le_pow₀ (by norm_num)

theorem dyadicWidth_rpow (n : ℕ) (σ : ℝ) :
    dyadicWidth n ^ σ = ((2 : ℝ) ^ (-σ)) ^ n := by
  dsimp [dyadicWidth]
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

theorem coefficientCode_eq_iff {Ω : Type*} (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ)
    (r : ℝ) (l : Ω) (b : Fin 4 → ℤ) : coefficientCode y β γ r l = b ↔
      ⌊y l 0 / r⌋ = b 0 ∧ ⌊y l 1 / r⌋ = b 1 ∧ ⌊β l / r⌋ = b 2 ∧ ⌊γ l / r⌋ = b 3 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    ext i
    fin_cases i <;> assumption

/-- Relative dyadic coefficient-bin caps from a geometrically summable deletion.
Every denominator is the original prior of the entire coefficient bin. -/
theorem exists_bin_regularization {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν]
    {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ δ σ θ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ)
    (hSlope : SlopeComparison y β γ E K ζ) (hK : 1 ≤ K)
    (hζ : 0 < ζ) (hδ : 0 < δ) (hσ : 0 < σ) (hθ : 0 < θ) :
    ∃ E' : Set (Ω × ℝ), E' ⊆ E ∧ MeasurableSet E' ∧
      (ν.prod volume) (E \ E') ≤ ENNReal.ofReal
        (δ + ((packingBound K / δ) * θ) / (1 - (2 : ℝ) ^ (-σ))) ∧
      BinCaps ν y β γ E' d (K / (θ * ζ ^ σ)) ζ := by
  classical
  let L := longLabels E δ
  let code : ℕ → Ω → Fin 4 → ℤ := fun n => coefficientCode y β γ (dyadicWidth n)
  let τ : ℕ → ℝ := fun n => θ * dyadicWidth n ^ (2 + d + σ)
  let bad : Set Ω := ⋃ n : ℕ, if ζ ≤ dyadicWidth n then
    lightCodeSet ν (code n) (fun _ => ENNReal.ofReal (τ n)) else ∅
  let E' := E ∩ (L \ bad) ×ˢ univ
  have hK0 : 0 < K := by linarith
  have hL : MeasurableSet L := measurableSet_longLabels hU.measurableSet_E δ
  have hcode : ∀ n, Measurable (code n) := fun n =>
    measurable_coefficientCode hU.measurable_y hU.measurable_β hU.measurable_γ _
  have hbad : MeasurableSet bad := by
    apply MeasurableSet.iUnion
    intro n
    split_ifs
    · exact measurableSet_lightCodeSet ν (code n) _
        (hcode n)
    · exact MeasurableSet.empty
  have hE' : MeasurableSet E' := hU.measurableSet_E.inter ((hL.diff hbad).prod MeasurableSet.univ)
  have hρ : (2 : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hσ)
  have hρ0 : 0 < 1 - (2 : ℝ) ^ (-σ) := sub_pos.mpr hρ
  have hcost : ν (L ∩ bad) ≤ ENNReal.ofReal
      (((packingBound K / δ) * θ) / (1 - (2 : ℝ) ^ (-σ))) := by
    apply geometric_light_code_mass ν code L (fun n => ζ ≤ dyadicWidth n) τ
      (by dsimp [packingBound]; positivity) (Real.rpow_nonneg (by norm_num) _) hρ
    intro n hn
    obtain ⟨C, hC, hcover⟩ := exists_coefficient_cover hU hSlope hK hζ hn
      (dyadicWidth_le_one n) hδ
    have htau : 0 ≤ τ n := mul_nonneg hθ.le (Real.rpow_nonneg (dyadicWidth_pos n).le _)
    refine (light_code_mass ν (code n) L C htau hcover).trans
      (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ ((packingBound K / δ) * dyadicWidth n ^ (-2 - d)) * τ n :=
        mul_le_mul_of_nonneg_right hC htau
      _ = ((packingBound K / δ) * θ) * ((2 : ℝ) ^ (-σ)) ^ n := by
        dsimp [τ]
        rw [← dyadicWidth_rpow]
        have heq : dyadicWidth n ^ (-2 - d) * dyadicWidth n ^ (2 + d + σ) =
            dyadicWidth n ^ σ := by
          rw [← Real.rpow_add (dyadicWidth_pos n)]
          congr 1
          ring
        calc
          _ = ((packingBound K / δ) * θ) *
              (dyadicWidth n ^ (-2 - d) * dyadicWidth n ^ (2 + d + σ)) := by ring
          _ = _ := by rw [heq]
  refine ⟨E', inter_subset_left, hE', ?_, ?_⟩
  · have hsub : E \ E' ⊆ Submission.Lib.K4IncidenceWitnesses.shortTimeIncidences E δ ∪
        (L ∩ bad) ×ˢ Icc (0 : ℝ) 1 := by
      rintro ⟨l, t⟩ ⟨hp, hp'⟩
      by_cases hl : l ∈ L
      · right
        have hb : l ∈ bad := by
          by_contra hb
          exact hp' ⟨hp, ⟨hl, hb⟩, mem_univ t⟩
        exact ⟨⟨hl, hb⟩, (hU.subset_E hp).2⟩
      · left
        exact ⟨hp, lt_of_not_ge hl⟩
    have hshort := Submission.Lib.K4IncidenceWitnesses.shortTimeIncidences_mass
      ν (ν.prod volume) (C := 1) (by norm_num) (by simp) hU.measurableSet_E δ
    simp only [one_mul] at hshort
    calc
      _ ≤ (ν.prod volume) (Submission.Lib.K4IncidenceWitnesses.shortTimeIncidences E δ ∪
          (L ∩ bad) ×ˢ Icc (0 : ℝ) 1) := measure_mono hsub
      _ ≤ (ν.prod volume) (Submission.Lib.K4IncidenceWitnesses.shortTimeIncidences E δ) +
          (ν.prod volume) ((L ∩ bad) ×ˢ Icc (0 : ℝ) 1) := measure_union_le _ _
      _ ≤ ENNReal.ofReal δ + ν (L ∩ bad) := by
        rw [Measure.prod_prod]
        simp only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
        exact add_le_add hshort le_rfl
      _ ≤ ENNReal.ofReal δ + ENNReal.ofReal
          (((packingBound K / δ) * θ) / (1 - (2 : ℝ) ^ (-σ))) := add_le_add le_rfl hcost
      _ = _ := (ENNReal.ofReal_add hδ.le (by dsimp [packingBound]; positivity)).symm
  · intro q n hq hqn b t z
    let r := dyadicWidth n
    have hr0 : 0 < r := dyadicWidth_pos n
    have hζr : ζ ≤ r := hq.trans hqn
    have hq0 : 0 < q := hζ.trans_le hq
    have hq1 : q ≤ 1 := hqn.trans (dyadicWidth_le_one n)
    have hτ0 : 0 < τ n := mul_pos hθ (Real.rpow_pos_of_pos (dyadicWidth_pos n) _)
    let B : Set Ω := {l | coefficientCode y β γ r l = b}
    have heq : B = {l | ⌊y l 0 / r⌋ = b 0 ∧ ⌊y l 1 / r⌋ = b 1 ∧
        ⌊β l / r⌋ = b 2 ∧ ⌊γ l / r⌋ = b 3} := by
      ext l
      exact coefficientCode_eq_iff y β γ r l b
    change ν {l | (⌊y l 0 / r⌋ = b 0 ∧ ⌊y l 1 / r⌋ = b 1 ∧
      ⌊β l / r⌋ = b 2 ∧ ⌊γ l / r⌋ = b 3) ∧ (l, t) ∈ E' ∧
      ⌊xbar β γ l t / q⌋ = z 0 ∧ ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} ≤
      ENNReal.ofReal ((K / (θ * ζ ^ σ)) * (q / r) ^ (2 + d)) *
        ν {l | ⌊y l 0 / r⌋ = b 0 ∧ ⌊y l 1 / r⌋ = b 1 ∧ ⌊β l / r⌋ = b 2 ∧ ⌊γ l / r⌋ = b 3}
    simp_rw [← coefficientCode_eq_iff y β γ r]
    change ν {l | l ∈ B ∧ (l, t) ∈ E' ∧ ⌊xbar β γ l t / q⌋ = z 0 ∧
      ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} ≤
      ENNReal.ofReal ((K / (θ * ζ ^ σ)) * (q / r) ^ (2 + d)) * ν B
    by_cases hlight : ν B < ENNReal.ofReal (τ n)
    · have hempty : {l | l ∈ B ∧ (l, t) ∈ E' ∧ ⌊xbar β γ l t / q⌋ = z 0 ∧
          ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro l ⟨hlB, hlE, _⟩
        have hbadl : l ∈ bad := by
          apply mem_iUnion.mpr
          refine ⟨n, ?_⟩
          rw [if_pos hζr]
          change ν {l' | code n l' = code n l} < ENNReal.ofReal (τ n)
          change coefficientCode y β γ r l = b at hlB
          change ν {l' | coefficientCode y β γ r l' = coefficientCode y β γ r l} < _
          rw [hlB]
          exact hlight
        exact hlE.2.1.2 hbadl
      rw [hempty, measure_empty]
      exact bot_le
    have hfloor : ENNReal.ofReal (τ n) ≤ ν B := le_of_not_gt hlight
    have hfactor : 0 ≤ (K / (θ * ζ ^ σ)) * (q / r) ^ (2 + d) := by positivity
    have hcompare : K * q ^ (2 + d) ≤
        ((K / (θ * ζ ^ σ)) * (q / r) ^ (2 + d)) * τ n := by
      have hζσ : ζ ^ σ ≤ r ^ σ := Real.rpow_le_rpow hζ.le hζr hσ.le
      have hratio : 1 ≤ r ^ σ / ζ ^ σ := (le_div_iff₀ (Real.rpow_pos_of_pos hζ _)).mpr (by simpa using hζσ)
      calc
        _ ≤ (K * q ^ (2 + d)) * (r ^ σ / ζ ^ σ) :=
          le_mul_of_one_le_right (by positivity) hratio
        _ = _ := by
          dsimp [τ]
          change K * q ^ (2 + d) * (r ^ σ / ζ ^ σ) =
            (K / (θ * ζ ^ σ) * (q / r) ^ (2 + d)) * (θ * r ^ (2 + d + σ))
          rw [Real.div_rpow hq0.le hr0.le]
          simp only [Real.rpow_add hr0, Real.rpow_two]
          field_simp
          <;> ring
    calc
      _ ≤ ν {l | (l, t) ∈ E ∧ ⌊xbar β γ l t / q⌋ = z 0 ∧
          ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} := by
        apply measure_mono
        rintro l ⟨_, hl, hz⟩
        exact ⟨hl.1, hz⟩
      _ ≤ ENNReal.ofReal (K * q ^ (2 + d)) := absCap_of_mixedCap hU hζ t q hq hq1 z
      _ ≤ ENNReal.ofReal (((K / (θ * ζ ^ σ)) * (q / r) ^ (2 + d)) * τ n) :=
        ENNReal.ofReal_le_ofReal hcompare
      _ = ENNReal.ofReal ((K / (θ * ζ ^ σ)) * (q / r) ^ (2 + d)) * ENNReal.ofReal (τ n) :=
        ENNReal.ofReal_mul hfactor
      _ ≤ _ := mul_le_mul_right hfloor _

end
end Submission.Lib.K4CoefficientBinRegularization.Reg
