import Submission.Obl.k4_general_parent_projected_layers.Support.WorldCaps
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedModelCap
import Submission.Obl.k4_general_parent_projected_layers.Support.ScalarGoodCrop

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_uncapped_native_capping (scalarX scalarY)

noncomputable section

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- Joint native mesh caps give pure scalar caps in every original coefficient
world, uniformly over all current submeasures of the native law. -/
theorem eventually_scalar_world_caps (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (hcommon : a.Common p) (hcaps : a.Caps p) {s M m : ℝ}
    (hs : 0 ≤ s) (hM : 0 < M) (hm : 0 < m) :
    ∀ᶠ k in atTop, ∀ ζ : Measure (α × ℝ), ζ ≤ a.mu k → ∀ u : Fin 4 → ℤ,
      a.nu k (projectedWorldCrop (a.scalarGoodLabels p k) (a.b k)
        (p.N k ^ (-m)) (narrow p k s) u) ≠ 0 →
      ∀ r : ℝ, 0 ≤ r → r ≤ s → ∀ (q : Fin 2 → ℤ) (j : ℤ),
      scalarCropLaw (a.nu k) ζ (projectedWorldCrop (a.scalarGoodLabels p k) (a.b k)
        (p.N k ^ (-m)) (narrow p k s) u)
        {z | (![⌊z.2 / p.N k ^ (-M)⌋,
          ⌊scalarY (worldScalarCoefficients (a.P k) (a.b k) (p.K k)
            (p.N k ^ (-m)) (narrow p k s) (a.scalarGoodLabels p k) u z.1) z.2 /
              p.N k ^ (-M)⌋] : Fin 2 → ℤ) = q ∧
            ⌊scalarX (worldScalarCoefficients (a.P k) (a.b k) (p.K k)
              (p.N k ^ (-m)) (narrow p k s) (a.scalarGoodLabels p k) u z.1) z.2 /
                p.N k ^ (-r)⌋ = j} ≤
        ENNReal.ofReal (1200 * p.K k * (p.N k ^ (-M)) ^ 2 *
          ((p.N k ^ (-m)) * narrow p k s *
            (a.pi k {v | ⌊v / p.N k ^ (-m)⌋ = u 0}).toReal /
            (a.nu k (projectedWorldCrop (a.scalarGoodLabels p k) (a.b k)
              (p.N k ^ (-m)) (narrow p k s) u)).toReal) * (p.N k ^ (-r)) ^ p.d) := by
  let r₀ := m + M + p.ell * s + 2
  have hel : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have hr₀ : 0 < r₀ := by dsimp [r₀]; nlinarith [mul_nonneg hel.le hs]
  let R := 2 + r₀ + r₀⁻¹ + m + m⁻¹ + s
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hr₀, inv_pos.mpr hm]
  have hRr : r₀ ≤ R := by dsimp [R]; linarith [inv_pos.mpr hr₀, inv_pos.mpr hm]
  have hRm : m ≤ R := by dsimp [R]; linarith [inv_pos.mpr hr₀, inv_pos.mpr hm]
  have hRs : s ≤ R := by dsimp [R]; linarith [inv_pos.mpr hr₀, inv_pos.mpr hm]
  have hri : R⁻¹ ≤ r₀ := by
    have hh : r₀⁻¹ ≤ R := by dsimp [R]; linarith [inv_pos.mpr hr₀, inv_pos.mpr hm]
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hr₀) hh
  have hmi : R⁻¹ ≤ m := by
    have hh : m⁻¹ ≤ R := by dsimp [R]; linarith [inv_pos.mpr hr₀, inv_pos.mpr hm]
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hm) hh
  filter_upwards [hcaps R hR, hp.2.2.1.2 1 zero_lt_one] with k hk hKN
  intro ζ hζ u hu r hr hrs q j
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hN1 : 1 ≤ p.N k := by linarith [hp.1 k]
  have hK : 0 ≤ p.K k := by linarith [hp.2.2.1.1 k]
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  have hc : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hN _
  have hσ : 0 < p.N k ^ (-M) := Real.rpow_pos_of_pos hN _
  have hδ : 0 < p.N k ^ (-r₀) := Real.rpow_pos_of_pos hN _
  have hgσ : narrow p k s * p.N k ^ (-M) = p.N k ^ (-p.ell * s - M) := by
    unfold narrow
    rw [← Real.rpow_add hN]
    congr 1 <;> ring
  have hdr : p.N k ^ (-r₀) ≤ p.N k ^ (-M) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [r₀]; nlinarith [mul_nonneg hel.le hs])
  have hdχ : p.N k ^ (-r₀) ≤ p.N k ^ (-m) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [r₀]; nlinarith [mul_nonneg hel.le hs])
  have hdy : p.N k ^ (-r₀) ≤ narrow p k s * p.N k ^ (-M) := by
    rw [hgσ]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    dsimp [r₀]
    linarith
  have hmove : p.K k * p.N k ^ (-r₀) ≤ p.N k ^ (1 - r₀) := by
    calc
      _ ≤ p.N k ^ (1 : ℝ) * p.N k ^ (-r₀) := mul_le_mul_of_nonneg_right hKN hδ.le
      _ = _ := by rw [← Real.rpow_add hN]; congr 1 <;> ring
  have hmχ : p.K k * p.N k ^ (-r₀) ≤ 2 * p.N k ^ (-m) := by
    apply hmove.trans
    have hh : p.N k ^ (1 - r₀) ≤ p.N k ^ (-m) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [r₀]; nlinarith [mul_nonneg hel.le hs])
    linarith
  have hmy : p.K k * p.N k ^ (-r₀) ≤ narrow p k s * p.N k ^ (-M) := by
    apply hmove.trans
    rw [hgσ]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    dsimp [r₀]
    linarith
  rcases hcommon k with ⟨hb, hν, hπ, hdom, hρ, htime, hmass, hP, hbase, hjet⟩
  letI := hν
  letI := hπ
  have hunit : ∀ᵐ z ∂a.mu k, z.2 ∈ Icc (0 : ℝ) 1 := by
    exact (ae_iff.mpr htime).mono fun _ hz => hz.2
  apply scalar_world_cap (a.nu k) (a.mu k) ζ (a.pi k) (a.P k) hP (a.b k) hb
    hc hg (Real.rpow_pos_of_pos hN _) (by positivity)
    (a.scalarGoodLabels p k) (a.measurableSet_scalarGoodLabels p k hb) (fun l hl => hl.1)
    u hu hζ hunit q j
  exact prepared_projected_cell_cap p a k hN hK hπ r₀ r m (p.N k ^ (-M)) (narrow p k s)
    (p.K k) _ _ _ _ hσ hg hdr (by linarith) hdy hK
    (projectedWorldRepresentatives_bound hK u 0)
    (projectedWorldRepresentatives_bound hK u 3) hmχ hmy
    (fun q' j' v' => (hk r₀ r m hri hRr hr (hrs.trans hRs) hmi hRm).2.2 true q' j' v') q j (u 0)

end PreparedModel

end

end Submission.Obl.k4_general_parent_projected_layers
