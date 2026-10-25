-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.AngularFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NormalClasses
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SlabFilling

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover

/-- A family whose normals have angles in `[θ,B*θ]` from the anchor fills a
slab of width `O(a+B*θ*b)` with volume proportional to `θ*b^3`. The constant
depends on the relative angular range `B`, not on the small angle `θ`. -/
theorem angular_slab_filling {n B : ℕ} (hn : 0 < n) (hB : 1 ≤ B)
    {a b h θ r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hh : 0 < h) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 0 < r)
    (c : Fin n → V) (u : Fin n → Fin 3 → V) (H : Fin n → Set V)
    (c₀ x : V) (u₀ : Fin 3 → V) (A : Set V)
    (hu : ∀ i, Orthonormal ℝ (u i)) (hHm : ∀ i, MeasurableSet (H i))
    (hHU : ∀ i, H i ⊆ prism a b (c i) (u i))
    (hregular : ∀ i p, p ∈ H i →
      O h * μ (prism a b (c i) (u i) ∩ ball p b) ≤ μ (H i ∩ ball p b))
    (hu₀ : Orthonormal ℝ u₀) (hA : A ⊆ prism a b c₀ u₀ ∩ ball x b)
    (hcover : A ⊆ ⋃ i, H i) (hmass : O (r * a * b ^ 2) ≤ μ A)
    (hangle : ∀ i, θ ≤ pd (u i 0) (u₀ 0) ∧ pd (u i 0) (u₀ 0) ≤ B * θ) :
    O (r * h ^ 2 * θ * b ^ 3 /
      (409600000 * (((128 * B + 1) ^ 4 : ℕ) : ℝ) * (1 + Real.log (b / a)))) ≤
      μ ({p | |inner ℝ (u₀ 0) (p - c₀)| ≤ 3 * a + (B * θ) * b} ∩
        (ball x (2 * b) ∩ ⋃ i, H i)) := by
  classical
  have hb0 : 0 < b := ha.trans_le hab
  have hL : 0 < 1 + Real.log (b / a) := by
    have := Real.log_nonneg ((one_le_div ha).mpr hab)
    linarith
  obtain ⟨F, hclose, hretain⟩ := clustered_normal_pigeonhole hn hB hθ
    (fun i => sgnNormal (u i 0)) (u₀ 0) H A hcover
    (fun i => by rw [pd_sgnNormal_left]; exact (hangle i).2)
  let C : ℝ := ((128 * B + 1) ^ 4 : ℕ)
  have hC : 0 < C := by dsimp [C]; positivity
  let A' := A ∩ ⋃ i ∈ F, H i
  have hretain' : μ A ≤ O C * μ A' := by
    simpa only [C, O, ENNReal.ofReal_natCast] using hretain
  have hdense : O ((r / C) * a * b ^ 2) ≤ μ A' := by
    have hp : O C * O ((r / C) * a * b ^ 2) ≤ O C * μ A' := by
      rw [← ENNReal.ofReal_mul hC.le]
      have he : C * (r / C * a * b ^ 2) = r * a * b ^ 2 := by field_simp
      rw [he]
      exact hmass.trans hretain'
    have hi := mul_le_mul' (le_refl (O C)⁻¹) hp
    have hC0 : O C ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hC)
    simpa only [← mul_assoc, ENNReal.inv_mul_cancel hC0 ENNReal.ofReal_ne_top, one_mul] using hi
  have hA'pos : μ A' ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hdense).ne'
  obtain ⟨p₀, hp₀⟩ := nonempty_of_measure_ne_zero hA'pos
  obtain ⟨i₀, hi₀, _⟩ := mem_iUnion₂.mp hp₀.2
  have hnorm : ‖sgnNormal (u i₀ 0)‖ = 1 := by rw [norm_sgnNormal]; exact (hu i₀).1 0
  obtain ⟨v, hv, hperp, hdot⟩ := exists_good_direction (hu₀.1 0) hnorm hθ.le
    (by rw [pd_sgnNormal_left]; exact (hangle i₀).1)
  obtain ⟨w, hframe⟩ := exists_frame (hu₀.1 0) hv hperp
  have htrans : ∀ i ∈ F, θ / 4 ≤ inner ℝ (sgnNormal (u i 0)) v := by
    intro i hi
    have hbnd := real_inner_le_norm (sgnNormal (u i₀ 0) - sgnNormal (u i 0)) v
    rw [inner_sub_left, hv, mul_one] at hbnd
    linarith [hclose i₀ hi₀ i hi]
  have hfill := clustered_slab_filling F ha hab hb hh hθ hθ1 (div_pos hr hC)
    (by positivity : 0 ≤ (B : ℝ) * θ) c u H c₀ x w v u₀ A'
    (fun i _ => hu i) (fun i _ => hHm i) (fun i _ => hHU i)
    (fun i _ => hregular i) hu₀ hframe (inter_subset_left.trans hA)
    inter_subset_right hdense htrans hclose
    (fun i _ => by rw [pd_symm]; exact (hangle i).2)
  calc
    _ = O ((r / C) * h ^ 2 * θ * b ^ 3 / (409600000 * (1 + Real.log (b / a)))) := by
      congr 1
      change r * h ^ 2 * θ * b ^ 3 / (409600000 * C * (1 + Real.log (b / a))) = _
      field_simp [ne_of_gt hC, ne_of_gt hL]
    _ ≤ μ ({p | |inner ℝ (u₀ 0) (p - c₀)| ≤ 3 * a + (B * θ) * b} ∩
        (ball x (2 * b) ∩ ⋃ i ∈ F, H i)) := hfill
    _ ≤ _ := by
      apply measure_mono
      intro p hp
      obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hp.2.2
      exact ⟨hp.1, hp.2.1, mem_iUnion.mpr ⟨i, hi⟩⟩

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
