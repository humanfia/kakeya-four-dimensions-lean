import Submission.Obl.k4_finite_projected_horizontal_candidates.ContactCandidates
import Submission.Obl.k4_finite_projected_horizontal_candidates.Model

namespace Submission.Obl.k4_finite_projected_horizontal_candidates

open MeasureTheory Filter Set
open Submission.Lib.K4ChartLifting (timeBlock)

/-- A finite range can contain any fixed positive depth and gain. -/
theorem exists_gain_range {s v : ℝ} (hs : 0 < s) (hv : 0 < v) :
    ∃ R : ℝ, 1 < R ∧ R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R := by
  let R : ℝ := 2 + s + v + s⁻¹ + v⁻¹
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hvi : 0 < v⁻¹ := inv_pos.mpr hv
  have hR : 1 < R := by dsimp [R]; linarith
  have hRs : s⁻¹ ≤ R := by dsimp [R]; linarith
  have hRv : v⁻¹ ≤ R := by dsimp [R]; linarith
  exact ⟨R, hR, inv_le_of_inv_le₀ hs hRs, by dsimp [R]; linarith,
    inv_le_of_inv_le₀ hv hRv, by dsimp [R]; linarith⟩

/-- The complete candidate conclusion in the strict contact regime follows
from the original assignment budget and major packet geometry alone. -/
theorem strict_contact_candidates : StrictContactPrinciple := by
  unfold StrictContactPrinciple
  intro N K hN hNt hK d kap ell S U e0 hd hd1 hkap hkap1 hell hgap hS hS1 hU he0
    hreg hhor α inst ν μ ρ π b P T n j A B c F hcontact hbasic hcaps hparents hnest
  obtain ⟨s, v, hs, hv, hsv, hstrict, hacc⟩ := exists_contact_gain hell hgap hU he0
  obtain ⟨R, hR, hRs, hsR, hRv, hvR⟩ := exists_gain_range hs hv
  have hν (k) : IsProbabilityMeasure (ν k) := (hbasic k).2.1
  have hρ (k) : ρ k ≤ μ k := (hbasic k).2.2.2.2.1
  have hmass (k) : ENNReal.ofReal ((K k)⁻¹) ≤ ρ k univ := (hbasic k).2.2.2.2.2.2.1
  have hvel (k) : ∀ᵐ p ∂μ k, |b k p.1 3| ≤ K k := by
    obtain ⟨hbmeas, hνk, hπk, hdom, hρk, hsupp, hmk, hP, hbν, hbμ⟩ := hbasic k
    apply ae_mono hdom
    apply Measure.ae_smul_measure
    have hvν : ∀ᵐ l ∂ν k, |b k l 3| ≤ K k := by
      filter_upwards [hbν] with l hl
      linarith [abs_nonneg (b k l 0), abs_nonneg (b k l 1), abs_nonneg (b k l 4)]
    exact (Measure.quasiMeasurePreserving_fst (μ := ν k) (ν := (volume : Measure ℝ))).ae hvν
  have hsU : s ≤ U := by linarith
  have hprep : ∀ᶠ k in atTop,
      N k ^ (kap * s) / K k ≤ (2 : ℝ) ^ T k s ∧
      (∀ i, MeasurableSet (A k s i) ∧ B k s i ⊆ A k s i) ∧
      (∀ i i', i ≠ i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧
      (∀ i, |c k s i 0| ≤ K k ∧ |c k s i 1| ≤ K k) ∧
      (∀ i l, l ∈ A k s i → ∀ t ∈ timeBlock (T k s) (j k s i),
        |b k l 0 + t * b k l 3 - c k s i 0 - t * c k s i 1| ≤
          K k * ((2 : ℝ) ^ T k s)⁻¹) ∧
      (∀ᵐ p ∂μ k, ∃ i, p.1 ∈ B k s i ∧ p.2 ∈ timeBlock (T k s) (j k s i)) := by
    filter_upwards [hparents R hR] with k hk
    have hks := hk s hRs hsU
    simp only [zpow_neg, zpow_natCast] at hks
    obtain ⟨htl, htu, hm, hdj, hlabel, hcover, hang⟩ := hks
    refine ⟨htl, fun i => ⟨(hm i).1, (hm i).2.2⟩, hdj, ?_, ?_, hcover⟩
    · intro i
      have hc := (hlabel i).2.2.2.1
      exact ⟨hc 0, hc 1⟩
    · intro i l hl t ht
      exact ((hlabel i).2.2.2.2.2.1 l hl t ht).1
  have hp := contact_packet_power_gain N K ν μ ρ b (fun k => T k s) (fun k => n k s)
    (fun k => j k s) (fun k => A k s) (fun k => B k s) (fun k => c k s)
    hN hNt hK.1 hK.2 hstrict hacc (lt_trans zero_lt_one hR) hν hρ hmass
    (fun k => (hcontact k).and (hvel k)) hprep
  refine ⟨R, hR, ?_⟩
  intro ε hε
  apply (hp ε hε).frequently.mono
  rintro k ⟨i, z, hz, hm⟩
  refine ⟨s, v, i, hRs, hsR, hRv, hvR, hsv, Or.inr ⟨z, hz, ?_⟩⟩
  exact hm

end Submission.Obl.k4_finite_projected_horizontal_candidates
