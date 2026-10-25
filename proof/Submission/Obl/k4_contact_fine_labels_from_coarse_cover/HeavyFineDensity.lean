-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/HeavyFineDensity.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelFineCaps
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.FixedNativeCaps
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.FineMesh

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set Filter MeasureTheory MvPolynomial
open Submission.Lib.K4AffineMeshCaps (baseMesh)
open Submission.Lib.K4ContactNormalization (affineBase)
open Submission.Obl.k4_stable_native_signal_oscillation

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- Every regular quadratic on an original heavy state has the recovered
fine base density `320*K^4*a^d`. The coarse affine coefficients are unrestricted. -/
theorem eventually_heavy_fine_density (hp : p.Valid)
    (H : ℕ → ℝ) (hH : ∀ k, 1 ≤ H k)
    (hHsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ k in atTop, ∀ C : Set (α × ℝ), MeasurableSet C →
      ENNReal.ofReal (p.N k ^ (-6 * s)) ≤ p.μ k C →
      ∀ (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ), F.totalDegree ≤ 2 →
      (∀ u ∈ C, p.GoodPoint k u) →
      (∀ u ∈ C, |p.x k u.1 u.2 3 - eval (p.x k u.1 u.2) (affineBase L)| ≤ H k) →
      (∀ u ∈ C, |eval (p.x k u.1 u.2) F| ≤ p.K k * p.a k s ∧
        |eval (p.x k u.1 u.2) (pderiv 3 F)| ≤ p.K k ∧
        |eval (p.x k u.1 u.2) (pderiv 3 (pderiv 3 F))| ≤ p.K k / p.a k s ∧
        (p.K k)⁻¹ ≤ |eval (p.x k u.1 u.2) (pderiv 3 F)|) →
      ∀ r : Fin 3 → ℤ, p.μ k {u |
        baseMesh (p.N k ^ (-100 * s)) (p.base k u) = r ∧ u ∈ C} ≤
        ENNReal.ofReal ((320 * p.K k ^ 4 * p.a k s ^ p.d) *
          (p.N k ^ (-100 * s)) ^ (3 : ℕ)) := by
  obtain ⟨C₀, hC₀, hcal⟩ := exists_mesh_calibration
  filter_upwards [eventually_shifted_quadratic_calibration p hp hC₀ hcal H hH hHsub hs,
    eventually_fine_freezing_mesh p hp H hH hHsub hs,
    eventually_native_scalar_caps_at p hp (show 0 < 100 * s by linarith) hs.le]
    with k hcoeff hmesh hcaps
  intro C hC hmass L F hF hgood hclose hfit r
  have hN := Valid.N_pos p hp k
  have hK := Valid.K_pos p hp k
  have ha := Valid.a_pos p hp k s
  have ha1 : p.a k s ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.N_ge k]) (by linarith)
  have hδ : 0 < p.N k ^ (-100 * s) := Real.rpow_pos_of_pos hN _
  have hδ1 : p.N k ^ (-100 * s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.N_ge k]) (by linarith)
  let τ := (p.μ k).restrict C
  have hτ : τ ≤ p.μ k := Measure.restrict_le_self
  have hmassτ : ENNReal.ofReal (p.N k ^ (-6 * s)) ≤ τ univ := by
    simpa only [τ, Measure.restrict_apply_univ] using hmass
  have hmem : ∀ᵐ u ∂τ, u ∈ C := ae_restrict_mem hC
  have hclose' (u : α × ℝ) (hu : u ∈ C) :
      |eval (p.x k u.1 u.2) (affineBase L) - p.x k u.1 u.2 3| ≤ H k := by
    simpa only [abs_sub_comm] using hclose u hu
  obtain ⟨hFγ, hFβ⟩ := hcoeff τ hτ hmassτ (p.a k s) le_rfl ha1 L F hF
    (hmem.mono (fun u hu =>
      ⟨(hfit u hu).1, (hfit u hu).2.1, (hfit u hu).2.2.1, hclose' u hu⟩))
  have hPfit : ∀ᵐ u ∂τ,
      |eval (p.x k u.1 u.2) (p.P k)| ≤ p.K k * 1 ∧
      |eval (p.x k u.1 u.2) (pderiv 3 (p.P k))| ≤ p.K k ∧
      |eval (p.x k u.1 u.2) (pderiv 3 (pderiv 3 (p.P k)))| ≤ p.K k / 1 ∧
      |eval (p.x k u.1 u.2) (affineBase L) - p.x k u.1 u.2 3| ≤ H k := by
    filter_upwards [hmem] with u hu
    have h := (hgood u hu).fit u.2 (hgood u hu).time
    exact ⟨by simpa only [mul_one] using h.1, h.2.1,
      by simpa only [div_one] using h.2.2, hclose' u hu⟩
  obtain ⟨hPγ, hPβ⟩ := hcoeff τ hτ hmassτ 1 ha1 le_rfl L (p.P k)
    (hp.basic k).2.2.2.2.2.2.2.1 hPfit
  have hgrow : p.N k ^ (39 * s) ≤ p.N k ^ (40 * s) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [hp.N_ge k]) (by linarith)
  have h := original_shifted_fine_cell_cap p hp C L F hF ha ha1
    (Real.rpow_nonneg hN.le (40 * s)) hδ hδ1 (by linarith [hH k])
    (fun e => (hFγ e).trans hgrow) (fun e => (hFβ e).trans hgrow)
    (fun e => (hPγ e).trans hgrow) (fun e => (hPβ e).trans hgrow)
    hmesh hgood hclose (fun u hu => ⟨(hfit u hu).1, (hfit u hu).2.2.2⟩)
    (fun _ => ENNReal.ofReal (p.K k * (p.N k ^ (-100 * s)) ^ (3 : ℕ) * p.a k s ^ p.d))
    (by simpa only [neg_mul] using hcaps) r
  apply h.trans_eq
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 320 * p.K k ^ 3)]
  congr 1
  ring

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
