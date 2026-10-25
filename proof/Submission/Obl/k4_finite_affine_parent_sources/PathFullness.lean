-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.PathMass
import Submission.Lib.K4AngularCharge.LargestAxis

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4XInterface
open scoped Classical ENNReal

noncomputable section

/-- Largest-axis deficiency is tested on the actual full frame of a
supplied label. No selected-incidence or conditional prior enters it. -/
def PathData.axisDeficient {W : ℕ} (p : PathData W) (ρ : ℝ) (b : Fin p.C) : Prop :=
  (∑ e : Fin 2, ∑ f : Fin 2, |p.frame b e f|) ≤
    ρ * p.κ / (2 : ℝ) ^ p.T (p.lev b)

/-- The accepted angular charging estimate controls every deficient
label of one supplied path level, with the unchanged original masses.
The only loss is its common velocity-cell count and the two original
density exceptions. -/
theorem PathData.Valid.deficient_level_mass_le
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    [hν : ∀ w, IsProbabilityMeasure (ν w)]
    (hE : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hNk : 1 ≤ Nk) (i : ℕ) (hr : 0 ≤ p.r i) (hrL : p.r i ≤ L)
    (u : ℝ) (hu : 0 < u) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (g : Fin W → Observation → ℝ≥0∞) (hg : ∀ w, Measurable (g w))
    (hmap : ∀ w, Measure.map (gobs (B w) (gδ Nk L))
      (((ν w).prod volume).restrict (E w)) =
        (volume.prod Measure.count).withDensity (g w))
    (G : Fin W → Observation × (Fin 2 → ℤ) → ℝ≥0∞)
    (hG : ∀ w, Measurable (G w))
    (hmapG : ∀ w, Measure.map (fun z : Incidence =>
      (gobs (B w) (gδ Nk L) z, fun e : Fin 2 => ⌊gv z.1 e / u⌋))
      (((ν w).prod volume).restrict (E w)) =
        ((volume.prod Measure.count).prod Measure.count).withDensity (G w))
    (Kc M : ℕ) (hKc : p.κ ≤ Kc)
    (hM : (4 * p.κ ^ 2 * ρ / u + 4) ^ 2 ≤ M)
    (α β : ℝ≥0∞) (hβ : β ≠ 0) :
    (∑ b, if p.lev b = i ∧ p.axisDeficient ρ b then
      ENNReal.ofReal (ω (p.world b)) * (ν (p.world b)).prod volume (p.counted b) else 0) ≤
      ((Kc : ℝ≥0∞) * M * (α / β)) *
        ∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w)) univ +
      Kc * ∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w))
        {z | α < G w (gobs (B w) (gδ Nk L) z, fun e : Fin 2 => ⌊gv z.1 e / u⌋) ∨
          g w (gobs (B w) (gδ Nk L) z) < β} := by
  classical
  let bad (b : Fin p.C) : Prop := p.lev b = i ∧ p.axisDeficient ρ b
  let Fbad (b : Fin p.C) : Set Incidence := if bad b then p.counted b else ∅
  have hκ : 0 ≤ p.κ := zero_le_one.trans hp.one_le_slack
  have hex (b : Fin p.C) (hb : bad b) :
      ∃ V : Finset (Fin 2 → ℤ), (V.card : ℝ) ≤ (4 * p.κ ^ 2 * ρ / u + 4) ^ 2 ∧
        ∀ l ∈ p.assigned b, (fun e : Fin 2 => ⌊gv l e / u⌋) ∈ V :=
    Submission.Lib.K4AngularCharge.gchart_cells_deficient (hp.chart b) hρ hb.2 hu hκ
  let V (b : Fin p.C) : Finset (Fin 2 → ℤ) :=
    if hb : bad b then (hex b hb).choose else ∅
  have hF (b : Fin p.C) : MeasurableSet (Fbad b) := by
    dsimp only [Fbad]
    split_ifs
    · exact hp.counted_measurable b
    · exact MeasurableSet.empty
  have hFE (b : Fin p.C) : Fbad b ⊆ E (p.world b) := by
    intro z hz
    dsimp only [Fbad] at hz
    split_ifs at hz with hb
    · exact (hp.counted_support b z hz).1
    · exact hz.elim
  have hknown (b : Fin p.C) (z : Incidence) (hz : z ∈ Fbad b) :
      b ∈ p.lists i (p.world b) (gobs (B (p.world b)) (gδ Nk (p.r i)) z) := by
    dsimp only [Fbad] at hz
    split_ifs at hz with hb
    · simpa only [hb.1] using hp.known b z hz
    · exact hz.elim
  have hlist (w : Fin W) (o : Observation) : (p.lists i w o).card ≤ Kc := by
    exact_mod_cast (hp.list_bound i w o).trans hKc
  have hV (b : Fin p.C) (z : Incidence) (hz : z ∈ Fbad b) :
      (fun e : Fin 2 => ⌊gv z.1 e / u⌋) ∈ V b := by
    dsimp only [Fbad] at hz
    split_ifs at hz with hb
    · dsimp only [V]
      rw [dite_eq_left hb]
      exact (hex b hb).choose_spec.2 z.1 (hp.counted_support b z hz).2.1
    · exact hz.elim
  have hcard (b : Fin p.C) : (V b).card ≤ M := by
    have hh : ((V b).card : ℝ) ≤ (M : ℝ) := by
      dsimp only [V]
      split_ifs with hb
      · exact (hex b hb).choose_spec.1.trans hM
      · simp
    exact_mod_cast hh
  have h := Submission.Lib.K4AngularCharge.level_mass_le_coarse ω ν E hE B hNk
    hr hrL u g hg hmap G hG hmapG p.world Fbad hF hFE (p.lists i) hknown
    Kc hlist V hV M hcard α β hβ
  convert h using 1
  apply Finset.sum_congr rfl
  intro b _
  dsimp only [Fbad, bad]
  split_ifs <;> simp_all only [measure_empty, mul_zero]

end

end Submission.Obl.k4_finite_affine_parent_sources
