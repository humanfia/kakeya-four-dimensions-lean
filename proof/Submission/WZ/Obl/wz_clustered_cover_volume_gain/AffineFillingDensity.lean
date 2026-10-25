-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.AffineFillingDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AffineDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ThinNeighborhood

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox volume_orthogonalBox)

/-- A transverse filling in a thin normalized box forces a large physical
ball-density class at every radius whose normalized image fits its short width. -/
theorem affine_filling_forces_ball_density {a b θ q lam r L J : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (haθ : a ≤ 2 * θ * b) (hq : 0 ≤ q) (hlam : 0 ≤ lam)
    (hr : 0 < r) (hL : 0 ≤ L) (hLr : L * r ≤ θ * b) (hJ : 0 < J)
    (f : V ≃ᵃ[ℝ] V) (z : V) (u : OrthonormalBasis (Fin 3) ℝ V) (F U : Set V)
    (hvol : ∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q)
    (hLip : ∀ p q, dist (f.symm p) (f.symm q) ≤ L * dist p q)
    (hbox : F ⊆ orthogonalBox ![3 * a + 2 * θ * b, 4 * b, 1] z u)
    (hFU : f '' F ⊆ U) (hUball : U ⊆ ball (0 : V) 1)
    (hfill : ENNReal.ofReal (q * θ * b ^ 2) ≤ volume F)
    (hupper : ∀ p ∈ f '' F, volume (U ∩ ball p r) ≤ ENNReal.ofReal (lam * r ^ 3)) :
    q ≤ 46080 * lam := by
  have htb : TotallyBounded (f '' F) :=
    (isCompact_closedBall (0 : V) 1).totallyBounded.subset
      ((hFU.trans hUball).trans ball_subset_closedBall)
  have hden := affine_ball_density_mass_in_box hr hL htb hFU f
    ![3 * a + 2 * θ * b, 4 * b, 1] z u hLip (image_mono hbox) hupper
  have hθb : θ * b ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hθ1 hb.le
    nlinarith
  have hsub : orthogonalBox (fun j => (![3 * a + 2 * θ * b, 4 * b, 1] : Fin 3 → ℝ) j + L * r) z u ⊆
      orthogonalBox ![9 * θ * b, 5 * b, 2] z u := by
    intro p hp j
    have hh := hp j
    fin_cases j
    · change |inner ℝ (u 0) (p - z)| ≤ 9 * θ * b
      change |inner ℝ (u 0) (p - z)| ≤ 3 * a + 2 * θ * b + L * r at hh
      linarith
    · change |inner ℝ (u 1) (p - z)| ≤ 5 * b
      change |inner ℝ (u 1) (p - z)| ≤ 4 * b + L * r at hh
      nlinarith [mul_le_mul_of_nonneg_right hθ1 hb.le]
    · change |inner ℝ (u 2) (p - z)| ≤ 2
      change |inner ℝ (u 2) (p - z)| ≤ 1 + L * r at hh
      linarith
  have hboxvol : volume (orthogonalBox
      (fun j => (![3 * a + 2 * θ * b, 4 * b, 1] : Fin 3 → ℝ) j + L * r) z u) ≤
      ENNReal.ofReal (720 * θ * b ^ 2) := by
    apply (measure_mono hsub).trans_eq
    rw [volume_orthogonalBox]
    · congr 1
      norm_num [Fin.prod_univ_three]
      ring
    · intro j
      fin_cases j <;> simp <;> positivity
  have hh : ENNReal.ofReal J * ENNReal.ofReal (q * θ * b ^ 2) ≤
      ENNReal.ofReal (64 * lam) * (ENNReal.ofReal J * ENNReal.ofReal (720 * θ * b ^ 2)) := by
    calc
      _ ≤ ENNReal.ofReal J * volume F := mul_le_mul' le_rfl hfill
      _ = volume (f '' F) := (hvol F).symm
      _ ≤ _ := hden.trans (by rw [hvol]; exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hboxvol))
  rw [← ENNReal.ofReal_mul hJ.le, ← ENNReal.ofReal_mul hJ.le,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 64 * lam)] at hh
  have hreal : J * (q * θ * b ^ 2) ≤ 64 * lam * (J * (720 * θ * b ^ 2)) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  apply (mul_le_mul_iff_left₀ (show 0 < J * θ * b ^ 2 by positivity)).mp
  nlinarith

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
