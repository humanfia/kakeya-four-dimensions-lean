import Submission.WZ.Obl.wz_tube_estimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.PointwiseEstimate
import Submission.WZ.Obl.wz_small_slab_error_removal.Basic

/-!
The unweighted set input for the plank estimate. The imported Wang--Zahl
endpoint permits arbitrary convex and slab constants. At exponent zero the
slab factor disappears, and convex counting itself supplies a slab constant.
The imported pointwise estimate also removes essential distinctness.
-/

namespace Submission.Obl.k4_plank_estimate

open MeasureTheory

private theorem endpoint_zero :
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces.E 0 0 := by
  have hE : WangZahlLot.Obl.wz_tube_estimate.E 0 0 :=
    WangZahlLot.wz_endpoint_bootstrap
      WangZahlLot.Obl.wz_tube_estimate.D WangZahlLot.Obl.wz_tube_estimate.E
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
      WangZahlLot.wz_hairbrush_seed WangZahlLot.wz_estimate_equivalence
      WangZahlLot.wz_strict_improvement
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hE ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 m l hm hl n x v Y hA
  rcases hA with ⟨hn, hf, hs, hd, hK, hF⟩
  exact h δ hδ hδ100 m l hm hl n x v Y hn
    (fun i => (hf i).1) (fun i => (hf i).2.1) hs
    (fun i => (hf i).2.2.1) (fun i => (hf i).2.2.2) hd hK hF

/-- A convex-clustered indexed family obeys the Kakeya set estimate.
There is no separation hypothesis, and repetitions of tubes are allowed.
The density and convex-clustering tolerances depend only on `ε`. -/
theorem unweighted_set_estimate :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ c : ℝ, 0 < c ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → EuclideanSpace ℝ (Fin 3))
        (Y : Fin n → Set (EuclideanSpace ℝ (Fin 3))),
      (∀ i, ‖v i‖ = 1) →
      (∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
        Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) →
      (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
      (∀ W : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W →
        ENNReal.ofReal ((Set.ncard {i : Fin n |
          Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℝ) * δ ^ 2) ≤
          ENNReal.ofReal (δ ^ (-η)) * volume W) →
      ENNReal.ofReal (c * δ ^ ε * ((n : ℝ) * δ ^ 2)) ≤ volume (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨c, hc, η₀, hη₀, h⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces.pointwise_dense_estimate
      endpoint_zero (ε / 2) (by positivity)
  let η := min η₀ (ε / 4)
  have hη : 0 < η := lt_min hη₀ (by positivity)
  refine ⟨η, hη, c, hc, ?_⟩
  intro δ hδ hδ100 n x v Y hv hb hm hY hd hK
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hδ1 : δ ≤ 1 := by linarith
  let m := δ ^ (-η)
  have hm1 : 1 ≤ m := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    hδ hδ1 (by linarith)
  have hK' : WangZahlLot.Obl.wz_endpoint_bootstrap.Katz δ m x v := hK
  let l := max 1 (m / ((n : ℝ) * δ ^ 2))
  have hF : WangZahlLot.Obl.wz_endpoint_bootstrap.Frostman δ l x v :=
    (WangZahlLot.Obl.wz_small_slab_error_removal.frostman_of_katz hδ hnpos hK').mono
      (le_max_right _ _)
  have hd' (i : Fin n) : ENNReal.ofReal (δ ^ η₀ * δ ^ 2) ≤ volume (Y i) := by
    apply le_trans (ENNReal.ofReal_le_ofReal _) (hd i)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (min_le_left _ _)
  have hh := h δ hδ hδ100 m l hm1 (le_max_left _ _) n x v Y hnpos
    (fun i => ⟨hv i, hb i, hm i, hY i⟩) hd' hK hF
  simp only [zero_add, neg_zero, Real.rpow_zero, mul_one] at hh
  apply le_trans (ENNReal.ofReal_le_ofReal _) hh
  have hηε : 2 * η ≤ ε / 2 := by
    have hh' : η ≤ ε / 4 := min_le_right _ _
    linarith
  have hpow : δ ^ ε ≤ δ ^ (ε / 2) * (m⁻¹) ^ 2 := by
    have heq : δ ^ (ε / 2) * (m⁻¹) ^ 2 = δ ^ (ε / 2 + 2 * η) := by
      dsimp only [m]
      rw [Real.rpow_neg hδ.le, inv_inv, ← Real.rpow_natCast,
        ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
      congr 1
      ring
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  calc
    _ ≤ c * (δ ^ (ε / 2) * (m⁻¹) ^ 2) * ((n : ℝ) * δ ^ 2) := by gcongr
    _ = _ := by ring

end Submission.Obl.k4_plank_estimate
