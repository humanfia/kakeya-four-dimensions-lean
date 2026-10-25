import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripNormal
import Submission.Obl.k4_finite_positive_mixed_cover_realization.CellBallCaps
import Submission.Obl.k4_finite_positive_mixed_cover_realization.PairCharge
import Submission.Lib.K4AngularCharge.XAngularCharge

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_forest_width_selection
open Submission.Obl.k4_native_finite_terminal_atlas_lift
open scoped RealInnerProductSpace

/-- Projectively close strip parameters; opposite unit normals describe the same strip. -/
def CoverData.Aligned {W : ℕ} {p : PathData W} (c : CoverData p)
    (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ) (gap : ℝ)
    (b : Fin c.n) (d : Fin p.C) : Prop :=
  ‖c.unitNormal b - normal d‖ + |c.bias b - bias d| ≤ gap ∨
    ‖c.unitNormal b + normal d‖ + |c.bias b + bias d| ≤ gap

/-- The analytical pair labels retain the actual world and actual ancestor.
They are used only for estimating discarded original mass. -/
def CoverData.misalignedPair {W : ℕ} {p : PathData W} (c : CoverData p)
    (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ) (gap : ℝ)
    (j : ℕ) (w : Fin W) (bd : Fin c.n × Fin p.C) : Set Incidence :=
  {z | (p.world bd.2 = w ∧ p.world (c.old bd.1) = w ∧ p.lev bd.2 = j ∧
      c.old bd.1 = forestAncestor p.lev p.par bd.2 c.level ∧
      ¬ c.Aligned normal bias gap bd.1 bd.2) ∧
    z ∈ c.interior bd.1 ∧ z ∈ p.counted bd.2}

/-- The geometric strip intersection estimate and the exact original path lists
bound misaligned pair mass directly under one unchanged world law. Original
density exceptions are excluded in the set being charged. -/
theorem CoverData.Valid.misaligned_pair_charge
    {W m Mp Dp Mg Dg j : ℕ} {p : PathData W} {c : CoverData p}
    {ℓ Nk L κ₁ δ₀ σ d₁ ρ gain ε gap fit width a b : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε) (ht : c.time = false)
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 1 ≤ Nk) (hrj : 0 ≤ p.r j) (hrjL : p.r j ≤ L)
    (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ)
    (hn : ∀ d, ‖normal d‖ = 1)
    (hdeep : ∀ d, p.lev d = j → ∀ l ∈ p.assigned d,
      |inner ℝ (((2 : ℝ) ^ p.T c.level)⁻¹ • Matrix.toEuclideanLin
        (p.frame (forestAncestor p.lev p.par d c.level))⁻¹
        (gv l - p.velocity (forestAncestor p.lev p.par d c.level))) (normal d) - bias d| ≤ fit)
    (hcandidate : Nk ^ (4 * ρ * c.gain * L + 4 * ε) * Nk ^ (-c.gain * L) ≤ fit)
    (hwidth : 0 < width) (hgap : 0 < gap) (hsmall : 4 * fit ≤ gap)
    (hscale : p.κ * (32 * (1 + 2 * p.κ) * fit / gap) ≤ width)
    (w : Fin W) (hν : IsProbabilityMeasure (ν w))
    (hE : E w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (g : Observation → ENNReal) (hg : Measurable g)
    (hlaw : Measure.map (gobs (B w) (gδ Nk L)) (((ν w).prod volume).restrict (E w)) =
      (volume.prod Measure.count).withDensity g)
    (G : Observation × (Fin 2 → ℤ) → ENNReal) (hG : Measurable G)
    (hjoint : Measure.map (fun z : Incidence =>
        (gobs (B w) (gδ Nk L) z, fun e : Fin 2 => ⌊(gv z.1) e / width⌋))
      (((ν w).prod volume).restrict (E w)) =
        ((volume.prod Measure.count).prod Measure.count).withDensity G)
    (ha : 0 ≤ a) (hb : 0 < b) :
    (∑ bd : Fin c.n × Fin p.C,
      (((ν w).prod volume).restrict (E w))
        {z | z ∈ c.misalignedPair normal bias gap j w bd ∧
          G (gobs (B w) (gδ Nk L) z, fun e : Fin 2 => ⌊(gv z.1) e / width⌋) ≤
            ENNReal.ofReal a ∧
          ENNReal.ofReal b ≤ g (gobs (B w) (gδ Nk L) z)}) ≤
      ENNReal.ofReal (a * 9 / b) *
        ENNReal.ofReal (p.κ * Nk ^ (4 * ρ * c.gain * L + 4 * ε)) *
        (((ν w).prod volume).restrict (E w)) univ := by
  classical
  letI : IsProbabilityMeasure (ν w) := hν
  letI : IsFiniteMeasure (((ν w).prod volume).restrict (E w)) :=
    Submission.Lib.K4AngularCharge.finite_restrict_prod hE
  have hκ : 0 ≤ p.κ := by linarith [hp.one_le_slack]
  have hcells (bd : Fin c.n × Fin p.C) : ∃ C : Finset (Fin 2 → ℤ),
      (C.card : ℝ) ≤ 9 ∧ ∀ z ∈ c.misalignedPair normal bias gap j w bd,
        (fun e : Fin 2 => ⌊(gv z.1) e / width⌋) ∈ C := by
    by_cases hcond : p.world bd.2 = w ∧ p.world (c.old bd.1) = w ∧ p.lev bd.2 = j ∧
        c.old bd.1 = forestAncestor p.lev p.par bd.2 c.level ∧
        ¬ c.Aligned normal bias gap bd.1 bd.2
    · obtain ⟨C, hC, hsupport⟩ := original_strip_overlap_velocity_cells
        (fun z : Incidence => gv z.1) (c.misalignedPair normal bias gap j w bd)
        (δ := width) (q := ((2 : ℝ) ^ p.T c.level)⁻¹) (κ := p.κ)
        (r := fit) (gap := gap) (V := 2 * p.κ)
        (Q := p.frame (c.old bd.1)) (u := p.velocity (c.old bd.1))
        (n := c.unitNormal bd.1) (m := normal bd.2) (β := c.bias bd.1) (γ := bias bd.2)
        hwidth (by positivity) (hp.chart (c.old bd.1)).1 hκ
        (by simpa only [frameSize, hc.old_level bd.1, div_eq_mul_inv] using
          (hp.chart (c.old bd.1)).2.2.2.1)
        (hc.normal_unit ht bd.1) (hn bd.2) (by positivity) hgap hsmall
        (show gap ≤ ‖c.unitNormal bd.1 - normal bd.2‖ + |c.bias bd.1 - bias bd.2| from
          (lt_of_not_ge (fun h => hcond.2.2.2.2 (Or.inl h))).le)
        (show gap ≤ ‖c.unitNormal bd.1 + normal bd.2‖ + |c.bias bd.1 + bias bd.2| from
          (lt_of_not_ge (fun h => hcond.2.2.2.2 (Or.inr h))).le)
        (by
          intro z hz
          have hzA := (hc.counted_support bd.1 hz.2.1.1).2.1
          have htrue := hdeep bd.2 hcond.2.2.1 z.1 (hp.counted_support bd.2 z hz.2.2).2.1
          rw [← hcond.2.2.2.1] at htrue
          exact ⟨hc.normalized_velocity_bound hp bd.1 z.1 hzA,
            (hc.normal_fit ht bd.1 z.1 hzA).trans hcandidate, htrue⟩)
        hscale
      exact ⟨C, by exact_mod_cast hC.le, hsupport⟩
    · refine ⟨∅, by simp, ?_⟩
      intro z hz
      exact (hcond hz.1).elim
  choose cells hcard hvelocity using hcells
  have hmeas (bd : Fin c.n × Fin p.C) :
      MeasurableSet (c.misalignedPair normal bias gap j w bd) := by
    by_cases hcond : p.world bd.2 = w ∧ p.world (c.old bd.1) = w ∧ p.lev bd.2 = j ∧
        c.old bd.1 = forestAncestor p.lev p.par bd.2 c.level ∧
        ¬ c.Aligned normal bias gap bd.1 bd.2
    · have hFd : MeasurableSet (p.counted bd.2) := (hp.chart bd.2).2.2.2.2.2.2.2.1
      have heq : c.misalignedPair normal bias gap j w bd = c.interior bd.1 ∩ p.counted bd.2 := by
        ext z
        exact ⟨fun hz => hz.2, fun hz => ⟨hcond, hz⟩⟩
      rw [heq]
      exact (hc.interior_measurable bd.1).inter hFd
    · have heq : c.misalignedPair normal bias gap j w bd = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun z hz => hcond hz.1
      rw [heq]
      exact MeasurableSet.empty
  apply known_parented_pair_velocity_charge
    (((ν w).prod volume).restrict (E w)) (volume.prod Measure.count)
    (gobs (B w) (gδ Nk L)) (fun z : Incidence => fun e : Fin 2 => ⌊(gv z.1) e / width⌋)
    (Submission.Lib.K4AngularCharge.measurable_gobs _ _)
    (Submission.Lib.K4AngularCharge.measurable_gcell _)
    g hg hlaw G hG hjoint (c.misalignedPair normal bias gap j w) hmeas cells hvelocity
    c.old (fun d => forestAncestor p.lev p.par d c.level) (p.terminalLists Nk L j w)
    (by
      intro bd z hz
      refine ⟨?_, hz.1.2.2.2.1⟩
      have hknown := hp.terminal_known hNk hz.1.2.2.1 hrj hrjL hz.2.2
      simpa only [hz.1.1] using hknown)
    ha hb (by norm_num : (0 : ℝ) ≤ 9)
    (by positivity : 0 ≤ Nk ^ (4 * ρ * c.gain * L + 4 * ε)) hcard
    (fun o => hp.terminal_list_bound j w o) ?_
  intro d
  have hcoun := hc.2.2.2.2.2.2.2.2.1 (forestAncestor p.lev p.par d c.level)
  simp only [ht, Bool.false_eq_true, ↓reduceIte] at hcoun
  convert hcoun using 1
  apply congrArg (fun n : ℕ => (n : ℝ))
  apply congrArg Finset.card
  ext a
  simp

end Submission.Obl.k4_finite_positive_mixed_cover_realization
