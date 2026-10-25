import Submission.Obl.k4_tempered_grid_selection.DensityTransfer
import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter Set
open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- Dominating the selected incidence law dominates its sampled upper tails,
for arbitrary measurable versions of both observation densities. -/
theorem weighted_upper_tail_mono {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (ρ : Measure Y) [SigmaFinite ρ] {W : ℕ}
    (μ μ₀ : Fin W → Measure Ω) (hμ : ∀ b, μ₀ b ≤ μ b)
    (obs : Fin W → Ω → Y) (hobs : ∀ b, Measurable (obs b))
    (g g₀ : Fin W → Y → ENNReal) (hg : ∀ b, Measurable (g b)) (hg₀ : ∀ b, Measurable (g₀ b))
    (hlaw : ∀ b, (μ b).map (obs b) = ρ.withDensity (g b))
    (hlaw₀ : ∀ b, (μ₀ b).map (obs b) = ρ.withDensity (g₀ b))
    (w : Fin W → ENNReal) (hi : ENNReal) :
    (∑ b, w b * μ₀ b {z | hi < g₀ b (obs b z)}) ≤
      ∑ b, w b * μ b {z | hi < g b (obs b z)} := by
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul' le_rfl
  refine (measure_mono_ae ?_).trans (hμ b _)
  filter_upwards [Submission.Obl.k4_tempered_grid_selection.ae_observed_density_mono
    ρ (μ b) (μ₀ b) (hμ b) (obs b) (hobs b) (g b) (g₀ b) (hg b) (hg₀ b) (hlaw b) (hlaw₀ b)]
    with z hz hbad
  exact hbad.trans_le hz

/-- Restriction of each incidence event preserves a weighted density band,
with error at most epsilon times the original weighted total mass. -/
theorem weighted_density_band_bound {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (ρ : Measure Y) [SigmaFinite ρ] {W : ℕ}
    (μ μ₀ : Fin W → Measure Ω) (hμ : ∀ b, μ₀ b ≤ μ b)
    (obs : Fin W → Ω → Y) (hobs : ∀ b, Measurable (obs b))
    (g g₀ : Fin W → Y → ENNReal) (hg : ∀ b, Measurable (g b)) (hg₀ : ∀ b, Measurable (g₀ b))
    (hlaw : ∀ b, (μ b).map (obs b) = ρ.withDensity (g b))
    (hlaw₀ : ∀ b, (μ₀ b).map (obs b) = ρ.withDensity (g₀ b))
    (w : Fin W → ENNReal) (hmass : (∑ b, w b * μ b univ) ≤ 1)
    (lo hi ε : ENNReal) :
    (∑ b, w b * μ₀ b {z | g₀ b (obs b z) < ε * lo ∨ hi < g₀ b (obs b z)}) ≤
      (∑ b, w b * μ b {z | g b (obs b z) < lo ∨ hi < g b (obs b z)}) + ε := by
  have hband (b : Fin W) := Submission.Obl.k4_tempered_grid_selection.observed_density_band_bound
    ρ (μ b) (μ₀ b) (hμ b) (obs b) (hobs b) (g b) (g₀ b) (hg b) (hg₀ b) (hlaw b) (hlaw₀ b)
    {z | g b (obs b z) < lo ∨ hi < g b (obs b z)} lo hi ε
    (Eventually.of_forall fun z hz => by simpa only [mem_ofPred_eq, not_or, not_lt] using hz)
  calc
    _ ≤ ∑ b, w b * (μ b {z | g b (obs b z) < lo ∨ hi < g b (obs b z)} + ε * μ b univ) :=
      Finset.sum_le_sum fun b _ => mul_le_mul' le_rfl (hband b)
    _ = (∑ b, w b * μ b {z | g b (obs b z) < lo ∨ hi < g b (obs b z)}) +
        ε * ∑ b, w b * μ b univ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      simpa only [mul_one] using mul_le_mul' (le_rfl (a := ε)) hmass

/-- Weighted typicality survives every dominated incidence selection of total
source mass at most one. Priors and within-world normalization are unchanged. -/
theorem weighted_typical_of_domination {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (W : ℕ → ℕ)
    (ρ : Measure Y) [SigmaFinite ρ]
    (μ μ₀ : (k : ℕ) → Fin (W k) → Measure Ω) (hμ : ∀ k b, μ₀ k b ≤ μ k b)
    (obs : (k : ℕ) → Fin (W k) → Ω → Y) (hobs : ∀ k b, Measurable (obs k b))
    (g g₀ : (k : ℕ) → Fin (W k) → Y → ENNReal)
    (hg : ∀ k b, Measurable (g k b)) (hg₀ : ∀ k b, Measurable (g₀ k b))
    (hlaw : ∀ k b, (μ k b).map (obs k b) = ρ.withDensity (g k b))
    (hlaw₀ : ∀ k b, (μ₀ k b).map (obs k b) = ρ.withDensity (g₀ k b))
    (w : (k : ℕ) → Fin (W k) → ENNReal) (hmass : ∀ k, (∑ b, w k b * μ k b univ) ≤ 1)
    (e : ℝ) (htyp : ∀ τ : ℝ, 0 < τ → IsPowerSmall N (fun k =>
      ∑ b, w k b * μ k b {z | g k b (obs k b z) < ENNReal.ofReal (N k ^ (-e - τ)) ∨
        ENNReal.ofReal (N k ^ (-e + τ)) < g k b (obs k b z)})) :
    ∀ τ : ℝ, 0 < τ → IsPowerSmall N (fun k =>
      ∑ b, w k b * μ₀ k b {z | g₀ k b (obs k b z) < ENNReal.ofReal (N k ^ (-e - τ)) ∨
        ENNReal.ofReal (N k ^ (-e + τ)) < g₀ k b (obs k b z)}) := by
  intro τ hτ
  let η := τ / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have herr : IsPowerSmall N (fun k => ENNReal.ofReal (N k ^ (-η))) :=
    ⟨η, hη, Eventually.of_forall fun _ => le_rfl⟩
  apply ((htyp η hη).add hNt herr).mono
  apply Eventually.of_forall
  intro k
  have hn0 : 0 < N k := by linarith [hN k]
  have hlo : ENNReal.ofReal (N k ^ (-e - τ)) ≤
      ENNReal.ofReal (N k ^ (-η)) * ENNReal.ofReal (N k ^ (-e - η)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hn0.le _), ← Real.rpow_add hn0]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hN k) (by dsimp [η]; linarith))
  have hhi : ENNReal.ofReal (N k ^ (-e + η)) ≤ ENNReal.ofReal (N k ^ (-e + τ)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hN k) (by dsimp [η]; linarith))
  refine (Finset.sum_le_sum fun b _ => mul_le_mul' le_rfl (measure_mono ?_)).trans
    (weighted_density_band_bound ρ (μ k) (μ₀ k) (hμ k) (obs k) (hobs k) (g k) (g₀ k)
      (hg k) (hg₀ k) (hlaw k) (hlaw₀ k) (w k) (hmass k)
      (ENNReal.ofReal (N k ^ (-e - η))) (ENNReal.ofReal (N k ^ (-e + η)))
      (ENNReal.ofReal (N k ^ (-η))))
  intro z hz
  exact hz.elim (fun hl => Or.inl (hl.trans_le hlo)) (fun hh => Or.inr (hhi.trans_lt hh))

end Submission.Obl.k4_remainder_pure_profile_normalization
