/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarNormalizedSupport.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarNormalizedSupport.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalData

/-! Actual centered observations, events and scalar supports. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

def scalarCenteredLift {Λ : Type*} (c H : ℝ) (p : ℝ × Λ) : Λ × ℝ := (p.2, c + H * p.1)

theorem scalarCenteredLift_measurable {Λ : Type*} [MeasurableSpace Λ] (c H : ℝ) :
    Measurable (scalarCenteredLift (Λ := Λ) c H) :=
  measurable_snd.prodMk (measurable_const.add (measurable_const.mul measurable_fst))

def scalarCenteredEvent {Λ : Type*} (E : Set (Λ × ℝ)) (A : Set Λ) (c H : ℝ) : Set (ℝ × Λ) :=
  scalarCenteredLift c H ⁻¹' E ∩ (univ ×ˢ A)

theorem scalarCenteredEvent_measurable {Λ : Type*} [MeasurableSpace Λ]
    {E : Set (Λ × ℝ)} (hE : MeasurableSet E) {A : Set Λ} (hA : MeasurableSet A) (c H : ℝ) :
    MeasurableSet (scalarCenteredEvent E A c H) :=
  (hE.preimage (scalarCenteredLift_measurable c H)).inter (MeasurableSet.univ.prod hA)

theorem scalarCenteredEvent_unit {Λ : Type*} {E : Set (Λ × ℝ)} {A : Set Λ}
    {s c H : ℝ} (hH : 0 < H) (hc : c ∈ Icc s (s + H))
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) :
    scalarCenteredEvent E A c H ⊆ Icc (-1 : ℝ) 1 ×ˢ A := by
  intro p hp
  have ht := (hblock hp.1).2
  change s ≤ c + H * p.1 ∧ c + H * p.1 ≤ s + H at ht
  exact ⟨⟨by nlinarith [ht.1, hc.2], by nlinarith [ht.2, hc.1]⟩, hp.2.2⟩

noncomputable def scalarNormalizedValue {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (F : ℝ → ℝ) (c H : ℝ) (b : ℤ) (p : ℝ × Λ) : ℝ :=
  (D.scalar F p.2 (c + H * p.1) - H * b) / H

theorem scalarNormalizedValue_measurable {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) {F : ℝ → ℝ} (hF : Measurable F) (c H : ℝ) (b : ℤ) :
    Measurable (scalarNormalizedValue D F c H b) :=
  (((D.measurable_scalar hF).comp (scalarCenteredLift_measurable c H)).sub_const (H * b)).div_const H

def scalarNormalizedSupport (S : ℝ → Set ℝ) (c H : ℝ) (b : ℤ) (u : ℝ) : Set ℝ :=
  (fun z => H⁻¹ * z - (b : ℝ)) '' S (c + H * u)

theorem scalarNormalizedSupport_AD {S : ℝ → Set ℝ} {ζ d C c H p : ℝ}
    (hζ : 0 < ζ) (hH : 0 < H) (hfloor : ζ ≤ H * p)
    (hS : ∀ t, IntervalAD ζ d C (S t)) (b : ℤ) (u : ℝ) :
    IntervalAD p d C (scalarNormalizedSupport S c H b u) := by
  have h := intervalAD_affine (a := H⁻¹) (b := -(b : ℝ)) hζ (inv_pos.mpr hH) (hS (c + H * u))
  have hf : H⁻¹ * ζ ≤ p := by
    have hh : ζ / H ≤ p := (div_le_iff₀ hH).mpr (by simpa only [mul_comm] using hfloor)
    simpa only [div_eq_mul_inv, mul_comm] using hh
  intro r R a hpr hrR
  simpa only [scalarNormalizedSupport, sub_eq_add_neg] using h r R a (hf.trans hpr) hrR

theorem scalarNormalizedSupport_mem {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {S : ℝ → Set ℝ} {K ζ d c H u : ℝ} (h : ScalarNormalHyp D ν E F S K ζ d)
    (hH : 0 < H) (b : ℤ) (l : Λ) (hl : (l, c + H * u) ∈ E) :
    scalarNormalizedValue D F c H b (u, l) ∈ scalarNormalizedSupport S c H b u := by
  refine ⟨D.scalar F l (c + H * u), h.support_mem _ hl, ?_⟩
  dsimp [scalarNormalizedValue]
  field_simp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
