-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.PowerSlopeProjection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.PowerProjectionMoment
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.CartesianPowerFrostman
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.FamilyGain
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.SlopeProjection
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.DenseSlopes

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

/-- A power-counting Cartesian set has a large projection in any
one-dimensional indexed family of slopes. -/
theorem cartesian_power_projection {δ C D E σ τ s γ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C) (hD : 1 ≤ D) (hE : 1 ≤ E)
    (hs : 0 < s) (hsexp : s ≤ σ + τ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hprod : s * γ ≤ 1)
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAF : RealFiniteFrostman δ C σ A) (hBF : RealFiniteFrostman δ D τ B)
    (I : Type) [Fintype I] [Nonempty I] (t : I → ℝ)
    (ht : IndexedRealFrostman δ E t) (htrange : ∀ i, |t i| ≤ 1) :
    ∃ i, ∀ (m : ℕ) (cc : Fin m → ℝ),
      Covers δ ((fun p : ℝ × ℝ => p.1 + t i * p.2) ''
        (↑(A ×ˢ B) : Set (ℝ × ℝ))) cc →
      1 ≤ (64 * C * D * E * energyConstant γ * δ ^ (s * γ)) * (m : ℝ) := by
  classical
  let F := (A ×ˢ B).image cartesianPoint
  have hFne : F.Nonempty := (hA.product hB).image _
  have hF : ClosedFinitePowerFrostman δ (C * D) s F := cartesian_power_frostman hδ hC hD hs.le hsexp hAF hBF
  have hdir := indexedFrostman_unitSlope hδ (by linarith : 0 ≤ E) htrange ht
  have hCD : 1 ≤ C * D := by nlinarith
  have hm := sum_indexed_power_projectionEnergy_le hF hdir hδ hδ1 hCD (by linarith : 1 ≤ 8 * E)
    hs (fun i => unitSlope_norm (t i)) hγ hγ1 hprod
  obtain ⟨i, hi⟩ := fiber_gain_of_moment F (fun _ : I => F) (fun i => unitSlope (t i))
    (by norm_num : (0 : ℝ) < 1) (fun _ => Finset.Subset.rfl)
    ⟨Classical.arbitrary I, hFne⟩ (by simp) hm
  refine ⟨i, ?_⟩
  intro m cc hcov
  have hc := Covers.unitSlope_linear hδ.le hcov
  have hc' : Covers δ ((fun x => inner ℝ (unitSlope (t i)) x) '' (↑F : Set Plane))
      (fun j => ‖cartesianPoint (1, t i)‖⁻¹ * cc j) := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    apply hc
    refine ⟨p, hp, ?_⟩
    simp [plane_inner, cartesianPoint]
  have hh := hi m _ hc'
  change (1 : ℝ) ^ 2 ≤
    8 * (C * D) * (8 * E) * energyConstant γ * δ ^ (s * γ) * (m : ℝ) at hh
  convert hh using 1 <;> ring

/-- Below one half, dense slopes detect a Cartesian projection of
exponent three halves of the one-dimensional exponent. -/
theorem dense_slope_low_projection {δ C σ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 2)
    (A : Finset ℝ) (hA : A.Nonempty) (hAF : RealFiniteFrostman δ C σ A)
    (T : Set ℝ)
    (hdense : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ T, t ∈ Set.Icc (0 : ℝ) 1 ∧ dist t x ≤ δ) :
    ∃ t ∈ T, t ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ (m : ℕ) (cc : Fin m → ℝ),
      Covers δ ((fun p : ℝ × ℝ => p.1 + t * p.2) ''
        (↑(A ×ˢ A) : Set (ℝ × ℝ))) cc →
      1 ≤ (320 * C ^ 2 * energyConstant (3 / 4) * δ ^ (3 * σ / 2)) * (m : ℝ) := by
  classical
  obtain ⟨N, t, hN, ht, hf⟩ := exists_frostman_slopes_of_dense hδ T hdense
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨i, hi⟩ := cartesian_power_projection (s := 2 * σ) (γ := 3 / 4)
    hδ hδ1 hC hC (by norm_num : (1 : ℝ) ≤ 5) (by positivity) (by linarith)
    (by norm_num) (by norm_num) (by linarith) A A hA hA hAF hAF (Fin N) t hf
    (fun i => by rw [abs_of_nonneg (ht i).2.1]; exact (ht i).2.2)
  refine ⟨t i, (ht i).1, (ht i).2, ?_⟩
  intro m cc hc
  convert hi m cc hc using 1 <;> ring_nf

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
