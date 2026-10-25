/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarObservationLocalFit.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarObservationLocalFit.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCollisionModelConstruction
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarOriginalLocalFit
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLocalFitConstants

/-! Local affine fitting directly from the original observed scalar event. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

theorem original_scalar_observation_affine_fit (hproj : ProjectionDichotomy)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ η p₀ : ℝ, 0 < η ∧ 0 < p₀ ∧ ∀ {Λ : Type*} [MeasurableSpace Λ]
      (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
      {d : ℝ} (p K δ error N : ℝ) (n : ℕ), μ ≤ volume →
      0 < p → p ≤ p₀ → p ≤ 1 → 1 ≤ K → 0 < δ → 0 ≤ error →
      d ≤ 1 - σ →
      11 ≤ N → 16 * (2 * K + 1) + 3 ≤ N → 33 * N < p ^ (ε - 1) →
      11 ≤ p ^ (-η) → 4 * (K + 1) + 3 ≤ p ^ (-η) →
      (2 * (n : ℝ) + 3) * K * (1 + 2 * (n : ℝ)) ^ (1 - σ) ≤ p ^ (-η) →
      (1 + 2 * error) + 6 * K + 2 * K ^ 2 + 1 ≤ (n : ℝ) →
      4 * (N ^ 3 * p ^ (η - 3)) * (scalarCollisionPairCeiling p K d K (1 + 2 * error) * p) ≤
        scalarNormalizedCollisionMass p K d δ →
      ∀ (E : Set (ℝ × Λ)) (A : Set Λ) (v Z : Λ → ℝ) (F : ℝ × Λ → ℝ) (f G : ℝ → ℝ)
        (S : ℝ → Set ℝ) (S₀ : Set ℝ),
      MeasurableSet E → E ⊆ Icc (-1 : ℝ) 1 ×ˢ A → Measurable v → Measurable Z → Measurable F →
      f 0 = 0 → (∀ u t, |f u - f t| ≤ |u - t|) →
      (∀ v w, |G v - G w| ≤ K * |v - w|) →
      (∀ l ∈ A, |v l| ≤ K ∧ |G (v l)| ≤ K) →
      (∀ t, IntervalAD p d K (S t)) → IntervalAD p d K S₀ →
      (∀ u l, (u, l) ∈ E → F (u, l) ∈ S u ∩ Icc (-K) K) →
      (∀ l ∈ A, Z l ∈ S₀ ∩ Icc (-K) K) →
      (∀ u l, (u, l) ∈ E → |F (u, l) - (Z l + u * G (v l) + f u * v l)| ≤ error * p) →
      (∀ a b r : ℝ, p ≤ r →
        ν.real {l | l ∈ A ∧ v l ∈ Icc a (a + r) ∧ Z l ∈ Icc b (b + r)} ≤ K * r ^ (1 + d)) →
      δ ≤ (μ.prod ν).real E →
      ∃ (T : Set ℝ) (a slope : ℝ), MeasurableSet T ∧ T ⊆ Icc (-1 : ℝ) 1 ∧
        (∀ u ∈ T, ∃ l, (u, l) ∈ E) ∧
        ENNReal.ofReal (scalarNormalizedActiveLength p K d error δ * p ^ (ε - 1)) ≤ volume T ∧
        |a| ≤ 9 ∧ |slope| ≤ 4 ∧ ∀ u ∈ T, |f u - (a + slope * u)| ≤ 13 * p := by
  classical
  obtain ⟨η, p₀, hη, hp₀, hfit⟩ := original_active_scalar_affine_fit hproj hσ hσ1 hε
  refine ⟨η, p₀, hη, hp₀, ?_⟩
  intro Λ _ μ _ ν _ d p K δ error N n hμ hp hpmax hp1 hK hδ he hd hNA hNB hlarge
    hbudgetA hbudgetB hbudgetD hn hdensity E A v Z F f G S S₀ hE hEsub hv hZ hF
    hf0 hf hG hbound hS hS₀ hsupport hstart hmodel hjoint hmass
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hpR : p ≤ 2 * K := by linarith
  have hsup : ∀ u l, (u, l) ∈ E → F (u, l) ∈ S u ∩ Icc (-K) (-K + 2 * K) := by
    intro u l hl
    obtain ⟨hs, hlo, hhi⟩ := hsupport u l hl
    exact ⟨hs, hlo, by linarith⟩
  have hstart' : ∀ u l, (u, l) ∈ E → Z l ∈ S₀ ∩ Icc (-K) (-K + 2 * K) := by
    intro u l hl
    obtain ⟨hs, hlo, hhi⟩ := hstart l (hEsub hl).2
    exact ⟨hs, hlo, by linarith⟩
  obtain ⟨b, hbmeas, hbmass⟩ := original_heavy_starting_collision μ ν hE hF hZ hp hpR hpR
    hKpos hKpos hδ hmass S S₀ hS hS₀ hsup hstart'
  obtain ⟨D, hDA, hDv, hDZ, hDf, hDG, hDS, hDP, hDt, hDJ⟩ :=
    scalar_collision_model_from_original_observations ν hp hK hE hEsub hv hZ hF f G hf0 hf hG hbound
      S₀ (fun l hl => (hstart l hl).1) hmodel hjoint b
  let cap := scalarCollisionPairCeiling p K d K (1 + 2 * error)
  let M := scalarNormalizedCollisionMass p K d δ
  let Qu := (2 * K / p + 3) ^ 2 * cap
  let Tu := 2 / p + 4
  let ell := scalarNormalizedActiveLength p K d error δ
  have he0 : 0 ≤ 1 + 2 * error := by linarith
  have hcap : 0 < cap := scalarCollisionPairCeiling_pos hp hK hKpos he0
  have hM : 0 < M := by dsimp [M, scalarNormalizedCollisionMass]; positivity
  have hQu : 0 < Qu := by dsimp [Qu]; positivity
  have hTu : 0 < Tu := by dsimp [Tu]; positivity
  have hell : 0 < ell := div_pos hM (mul_pos (mul_pos (by norm_num) hQu) hTu)
  have hellEq : ell * (4 * Qu * Tu) = M :=
    div_mul_cancel₀ M (ne_of_gt (mul_pos (mul_pos (by norm_num) hQu) hTu))
  have hcost : ((D.velocityGrid.card : ℝ) ^ 2 * cap) * (ell * (D.timeGrid.card : ℝ)) ≤ M / 4 := by
    calc
      _ ≤ Qu * (ell * Tu) := by
        dsimp only [Qu, Tu]
        have hJnonneg : 0 ≤ (D.velocityGrid.card : ℝ) := Nat.cast_nonneg _
        have hTbound : (D.timeGrid.card : ℝ) ≤ 2 / p + 4 := by linarith
        gcongr
      _ = (ell * (4 * Qu * Tu)) / 4 := by ring
      _ = M / 4 := by rw [hellEq]
  have hPmass : M ≤ (μ.prod (ν.prod ν)).real D.pairEvent := by
    rw [hDP]
    exact hbmass
  have hfitmass : 2 * (N ^ 3 * p ^ (η - 3)) * (cap * p) +
      ((D.velocityGrid.card : ℝ) ^ 2 * cap) * (ell * (D.timeGrid.card : ℝ)) ≤
        (μ.prod (ν.prod ν)).real D.pairEvent := by
    change 4 * (N ^ 3 * p ^ (η - 3)) * (cap * p) ≤ M at hdensity
    linarith
  have hDAD : IntervalAD p (1 - σ) K D.scalarSupport := by
    rw [hDS]
    exact intervalAD_mono_exponent hp hKpos.le hd hS₀
  obtain ⟨T, a, slope, hTm, hactive, hvol, ha, hslope, hrow⟩ := hfit μ ν p K K K (1 + 2 * error)
    ell N n hμ hp hpmax hp1 hK hKpos hKpos.le he0 hell.le D hNA hNB hlarge hbudgetA hbudgetB
      hbudgetD hn hDAD hfitmass
  refine ⟨T, a, slope, hTm, ?_, ?_, hvol, ha, hslope, ?_⟩
  · intro u hu
    exact abs_le.mp (hactive hu).2
  · intro u hu
    have hpos := (hactive hu).1
    obtain ⟨q, hq⟩ := nonempty_of_measure_ne_zero (ne_of_gt hpos)
    have hq' : (u, q) ∈ scalarStartingCollisionEvent E F Z p b := hDP ▸ hq
    exact ⟨q.1, hq'.1.1⟩
  · simpa only [hDf] using hrow

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
