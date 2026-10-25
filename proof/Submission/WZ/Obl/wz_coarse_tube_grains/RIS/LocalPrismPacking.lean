-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.LocalPrismPacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PrismPacking

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- The common container for prisms meeting a slab inside a ball of radius r. -/
theorem prism_enclosure_of_meeting_local_slab {a b c r w t : ℝ} {z p₀ : V}
    (e : V ≃ₗᵢ[ℝ] V) (hb : b ≤ r) (hc : c ≤ r)
    (hmeet : (P a b c z e ∩ (ball p₀ r ∩ {p | |e (p - p₀) 0 - t| ≤ w})).Nonempty) :
    P a b c z e ⊆ P (2 * (w + a)) (4 * r) (4 * r)
      (p₀ + e.symm (EuclideanSpace.single 0 t)) e := by
  obtain ⟨q, hqP, hqball, hqslab⟩ := hmeet
  intro p hp
  change |e (q - p₀) 0 - t| ≤ w at hqslab
  have hqnorm : ‖q - p₀‖ < r := by simpa only [mem_ball, dist_eq_norm] using hqball
  have hcoord (i : Fin 3) : |e (q - p₀) i| ≤ r :=
    (abs_rotated_coord_le e (q - p₀) i).trans hqnorm.le
  have he (i : Fin 3) :
      e (p - z) i - e (q - z) i + e (q - p₀) i = e (p - p₀) i := by
    simp only [map_sub]
    change (e p i - e z i) - (e q i - e z i) + (e q i - e p₀ i) = e p i - e p₀ i
    ring
  have h0 : |e (p - p₀) 0 - t| ≤ w + a := by
    rw [← he 0]
    calc
      |e (p - z) 0 - e (q - z) 0 + e (q - p₀) 0 - t| =
          |(e (p - z) 0 - e (q - z) 0) + (e (q - p₀) 0 - t)| := by ring_nf
      _ ≤ |e (p - z) 0 - e (q - z) 0| + |e (q - p₀) 0 - t| := abs_add_le _ _
      _ ≤ (|e (p - z) 0| + |e (q - z) 0|) + |e (q - p₀) 0 - t| :=
        add_le_add (abs_sub _ _) le_rfl
      _ ≤ w + a := by
        have hp0 : |e (p - z) 0| ≤ a / 2 := hp.1
        have hq0 : |e (q - z) 0| ≤ a / 2 := hqP.1
        linarith only [hp0, hq0, hqslab]
  have hshort (i : Fin 3) (s : ℝ) (hs : s ≤ r)
      (hp' : |e (p - z) i| ≤ s / 2) (hq' : |e (q - z) i| ≤ s / 2) :
      |e (p - p₀) i| ≤ 2 * r := by
    rw [← he i]
    have hsum := abs_add_le (e (p - z) i - e (q - z) i) (e (q - p₀) i)
    have hdiff := abs_sub (e (p - z) i) (e (q - z) i)
    linarith [hcoord i]
  have h1 := hshort 1 b hb hp.2.1 hqP.2.1
  have h2 := hshort 2 c hc hp.2.2 hqP.2.2
  change |e (p - (p₀ + e.symm (EuclideanSpace.single 0 t))) 0| ≤ 2 * (w + a) / 2 ∧
    |e (p - (p₀ + e.symm (EuclideanSpace.single 0 t))) 1| ≤ (4 * r) / 2 ∧
    |e (p - (p₀ + e.symm (EuclideanSpace.single 0 t))) 2| ≤ (4 * r) / 2
  rw [show p - (p₀ + e.symm (EuclideanSpace.single 0 t)) =
      (p - p₀) - e.symm (EuclideanSpace.single 0 t) by abel, map_sub, e.apply_symm_apply]
  norm_num [show (4 * r) / 2 = 2 * r by ring]
  simpa only [map_sub, PiLp.sub_apply] using And.intro h0 (And.intro h1 h2)

/-- Local slab packing loses no power of the ball radius: the total prism
volume is at most 32(w+a)r^2. -/
theorem prism_packing_in_local_slab {a b c r w t : ℝ} {p₀ : V}
    (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hr : 0 ≤ r) (hw : 0 ≤ w)
    (hb : b ≤ r) (hc : c ≤ r) (e : V ≃ₗᵢ[ℝ] V) (F : Finset V)
    (hdisj : (↑F : Set V).PairwiseDisjoint (fun z => P a b c z e))
    (hmeet : ∀ z ∈ F,
      (P a b c z e ∩ (ball p₀ r ∩ {p | |e (p - p₀) 0 - t| ≤ w})).Nonempty) :
    o ((F.card : ℝ) * (a * b * c)) ≤ o (32 * (w + a) * r ^ 2) := by
  let W := P (2 * (w + a)) (4 * r) (4 * r) (p₀ + e.symm (EuclideanSpace.single 0 t)) e
  have hsub : (⋃ z ∈ F, P a b c z e) ⊆ W := by
    intro p hp
    obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
    exact prism_enclosure_of_meeting_local_slab e hb hc (hmeet z hz) hpz
  have hvol (z : V) : μ (P a b c z e) = o (a * b * c) :=
    Factor.box_volume ha hb0 hc0 z e
  have hvolW : μ W = o (32 * (w + a) * r ^ 2) := by
    have hvol0 : μ W = o ((2 * (w + a)) * (4 * r) * (4 * r)) :=
      Factor.box_volume (by positivity) (by positivity) (by positivity)
        (p₀ + e.symm (EuclideanSpace.single 0 t)) e
    rw [hvol0]
    congr 1
    ring
  calc
    o ((F.card : ℝ) * (a * b * c)) = ∑ z ∈ F, μ (P a b c z e) := by
      simp only [hvol, Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.ofReal_mul (Nat.cast_nonneg F.card) |>.trans
        (by rw [ENNReal.ofReal_natCast]; rfl)
    _ = μ (⋃ z ∈ F, P a b c z e) :=
      (measure_biUnion_finset hdisj (fun z _ => measurableSet_prism _ _ _ z e)).symm
    _ ≤ μ W := measure_mono hsub
    _ = _ := hvolW

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
