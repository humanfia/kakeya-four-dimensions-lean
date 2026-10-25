/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/DensityPreparedLaw.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_balanced_native_packet_transport.UWE).
-/
import Submission.Obl.k4_balanced_native_packet_transport.UWE.FiniteDensityMasks
import Submission.Obl.k4_balanced_native_packet_transport.UWE.NativeAngularProblem

noncomputable section

namespace Submission.Obl.k4_balanced_native_packet_transport.UWE

open MeasureTheory Set

theorem Problem.Valid.measurableSet_densityPreparationBad {p : Problem} {S η : ℝ}
    (hp : p.Valid S η) (R A : Finset ℝ)
    (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L) (hA : ∀ u ∈ A, 0 < u ∧ u ≤ η * p.L)
    (τ : ℝ) (k : ℕ) (γ : Fin (p.W k)) :
    MeasurableSet (densityPreparationBad p S R A τ k γ) := by
  rcases hp with ⟨_, _, _, hL, _, _, _, _, _, hg, hG, _⟩
  apply MeasurableSet.union
  · apply Finset.measurableSet_biUnion
    intro r hr
    have hr' : 0 ≤ r ∧ r ≤ p.L := by
      rcases Finset.mem_insert.mp hr with hr | hr
      · subst r; exact ⟨hL.le, le_rfl⟩
      · exact hR r hr
    have hm := (hg k γ r hr'.1 hr'.2).1.comp
      (show Measurable (obs (p.B k γ) (δ (p.N k) r)) by unfold obs x; fun_prop)
    exact (measurableSet_lt hm measurable_const).union (measurableSet_lt measurable_const hm)
  · apply Finset.measurableSet_biUnion
    intro u hu
    have hm := (hG k γ u (hA u hu).1 (hA u hu).2).1.comp
      (show Measurable (fun z : Incidence =>
        (obs (p.B k γ) (δ (p.N k) p.L) z, fun j => ⌊v z.1 j / δ (p.N k) u⌋)) by
          unfold obs x v; fun_prop)
    exact measurableSet_lt measurable_const hm

/-- A common analytical restriction of each original incidence law. -/
def Problem.preparedIncidence (p : Problem) (S : ℝ) (R A : Finset ℝ) (τ : ℝ)
    (k : ℕ) (γ : Fin (p.W k)) : Measure Incidence :=
  (p.incidenceMeasure k γ).restrict (densityPreparationBad p S R A τ k γ)ᶜ

theorem Problem.preparedIncidence_le (p : Problem) (S : ℝ) (R A : Finset ℝ) (τ : ℝ)
    (k : ℕ) (γ : Fin (p.W k)) :
    p.preparedIncidence S R A τ k γ ≤ p.incidenceMeasure k γ :=
  Measure.restrict_le_self

theorem Problem.pure_density_band_of_not_bad (p : Problem) (S : ℝ) (R A : Finset ℝ)
    (τ : ℝ) (k : ℕ) (γ : Fin (p.W k)) (z : Incidence)
    (hz : z ∉ densityPreparationBad p S R A τ k γ)
    {r : ℝ} (hr : r ∈ insert p.L R) :
    ENNReal.ofReal (p.N k ^ (-p.f r - τ)) ≤ p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z) ∧
      p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z) ≤ ENNReal.ofReal (p.N k ^ (-p.f r + τ)) := by
  have hnot : z ∉ pureDensityBad p k γ r τ := by
    intro hbad
    exact hz (Or.inl (mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hr, hbad⟩⟩))
  exact ⟨le_of_not_gt (not_or.mp hnot).1, le_of_not_gt (not_or.mp hnot).2⟩

/-- The absolute profile offset cancels in the original terminal joint/pure
ratio, using the terminal LOWER mask and the angular upper mask. -/
theorem Problem.angular_ratio_of_not_bad (p : Problem) (S : ℝ) (R A : Finset ℝ)
    (τ : ℝ) (k : ℕ) (γ : Fin (p.W k)) (hN : 0 < p.N k) (z : Incidence)
    (hz : z ∉ densityPreparationBad p S R A τ k γ) {u : ℝ} (hu : u ∈ A) :
    p.G k γ u (obs (p.B k γ) (δ (p.N k) p.L) z, nativeAngularBin (δ (p.N k) u) z) ≤
      ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ)) *
        p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) z) := by
  have hnot : z ∉ angularDensityBad p S k γ u τ := by
    intro hbad
    exact hz (Or.inr (mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨hu, hbad⟩⟩))
  have hupper : p.G k γ u
      (obs (p.B k γ) (δ (p.N k) p.L) z, nativeAngularBin (δ (p.N k) u) z) ≤
      ENNReal.ofReal (p.N k ^ (-p.f p.L - S * u + τ)) := le_of_not_gt hnot
  have hlower := (p.pure_density_band_of_not_bad S R A τ k γ z hz (Finset.mem_insert_self _ _)).1
  have hpow : ENNReal.ofReal (p.N k ^ (-p.f p.L - S * u + τ)) =
      ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ)) *
        ENNReal.ofReal (p.N k ^ (-p.f p.L - τ)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), ← Real.rpow_add hN]
    congr 2
    ring
  exact hupper.trans (hpow.trans_le (mul_le_mul' le_rfl hlower))

theorem Problem.Valid.ae_prepared_density_masks {p : Problem} {S η : ℝ}
    (hp : p.Valid S η) (R A : Finset ℝ)
    (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L) (hA : ∀ u ∈ A, 0 < u ∧ u ≤ η * p.L)
    (τ : ℝ) (k : ℕ) (γ : Fin (p.W k)) :
    ∀ᵐ z ∂p.preparedIncidence S R A τ k γ,
      (∀ r ∈ insert p.L R,
        ENNReal.ofReal (p.N k ^ (-p.f r - τ)) ≤ p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z) ∧
        p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z) ≤ ENNReal.ofReal (p.N k ^ (-p.f r + τ))) ∧
      ∀ u ∈ A,
        p.G k γ u (obs (p.B k γ) (δ (p.N k) p.L) z, nativeAngularBin (δ (p.N k) u) z) ≤
          ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ)) *
            p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) z) := by
  have hbad := hp.measurableSet_densityPreparationBad R A hR hA τ k γ
  filter_upwards [ae_restrict_mem hbad.compl] with z hz
  exact ⟨fun r hr => p.pure_density_band_of_not_bad S R A τ k γ z hz hr,
    fun u hu => p.angular_ratio_of_not_bad S R A τ k γ (by linarith only [hp.1 k]) z hz hu⟩

end Submission.Obl.k4_balanced_native_packet_transport.UWE
