import Submission.Obl.k4_stable_native_signal_oscillation.GoodSet

namespace Submission.Obl.k4_stable_native_signal_oscillation
open MvPolynomial MeasureTheory Set

lemma pullback_signal_partition (μ : Measure NativePoint) (f : NativePoint → NativePoint)
    (hf : Measurable f) (hbase : ∀ p, nativeBase (f p) = nativeBase p)
    (S : MvPolynomial (Fin 4) ℝ) (G : Set NativePoint) (hGm : MeasurableSet G)
    (hG : ∀ᵐ p ∂μ, p ∈ G) {M a L : ℝ}
    (hfit : ∀ p ∈ G, |value S (f p) - value S p| ≤ M * a)
    {n : ℕ} (F : Fin n → Set NativePoint)
    (hFm : ∀ i, MeasurableSet (F i))
    (hFd : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (hFl : ∀ i p, p ∈ F i → ∀ q, q ∈ F i →
      |value S p - value S q| ≤ L * ‖nativeBase p - nativeBase q‖) :
    ∃ E : Fin n → Set NativePoint,
      (∀ i, MeasurableSet (E i)) ∧
      (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
      μ (⋃ i, E i)ᶜ ≤ (Measure.map f μ) (⋃ i, F i)ᶜ ∧
      ∀ i p, p ∈ E i → ∀ q, q ∈ E i →
        |value S p - value S q| ≤ 2 * M * a + L * ‖nativeBase p - nativeBase q‖ := by
  let E : Fin n → Set NativePoint := fun i => G ∩ f ⁻¹' F i
  refine ⟨E, (fun i => hGm.inter ((hFm i).preimage hf)), ?_, ?_, ?_⟩
  · intro i j hij
    exact Set.disjoint_left.mpr (fun p hp hq => Set.disjoint_left.mp (hFd i j hij) hp.2 hq.2)
  · calc
      μ (⋃ i, E i)ᶜ ≤ μ (f ⁻¹' (⋃ i, F i)ᶜ) := by
        apply measure_mono_ae
        filter_upwards [hG] with p hp
        intro hpn hpf
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpf
        exact hpn (Set.mem_iUnion.mpr ⟨i, hp, hi⟩)
      _ = (Measure.map f μ) (⋃ i, F i)ᶜ :=
        (Measure.map_apply hf (MeasurableSet.iUnion hFm).compl).symm
  · intro i p hp q hq
    have h1 := hfit p hp.1
    have h2 := hfit q hq.1
    have h3 := hFl i (f p) hp.2 (f q) hq.2
    rw [hbase, hbase] at h3
    calc
      _ = |(value S p - value S (f p)) + (value S (f p) - value S (f q)) +
          (value S (f q) - value S q)| := by congr 1; ring
      _ ≤ |value S p - value S (f p)| + |value S (f p) - value S (f q)| +
          |value S (f q) - value S q| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ M * a + L * ‖nativeBase p - nativeBase q‖ + M * a := by
        rw [abs_sub_comm (value S p) (value S (f p))]
        exact add_le_add (add_le_add h1 h3) h2
      _ = 2 * M * a + L * ‖nativeBase p - nativeBase q‖ := by ring

lemma base_density_rootLift (μ : Measure NativePoint) (P : MvPolynomial (Fin 4) ℝ) {K L : ℝ}
    (hKL : K ≤ L) (hd : Measure.map nativeBase μ ≤ ENNReal.ofReal K • volume) :
    Measure.map nativeBase (Measure.map (rootLift P) μ) ≤ ENNReal.ofReal L • volume := by
  rw [Measure.map_map measurable_nativeBase (measurable_rootLift P)]
  have heq : nativeBase ∘ rootLift P = nativeBase := funext (nativeBase_rootLift P)
  rw [heq]
  apply hd.trans
  apply Measure.le_iff.mpr
  intro T _
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hKL) bot_le

end Submission.Obl.k4_stable_native_signal_oscillation
