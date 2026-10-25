-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.BodyDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyMultiplicity

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

/-- Removing entries below half the mean retains a quantitative number of entries. -/
theorem dense_entries_card {n : ℕ} (a : Fin n → ℝ) {d t V : ℝ}
    (hV : 0 < V) (ht : 0 ≤ t) (htd : 2 * t ≤ d)
    (ha : ∀ i, a i ≤ V) (hmass : d * n * V ≤ ∑ i, a i) :
    d * n / 2 ≤ ({i : Fin n | t * V ≤ a i}.ncard : ℝ) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun i => t * V ≤ a i
  have hsum : ∑ i, a i ≤ (S.card : ℝ) * V + n * (t * V) := by
    calc
      _ ≤ ∑ i, ((if i ∈ S then V else 0) + t * V) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ S
        · simp only [ite_eq_left hi]
          exact (ha i).trans (le_add_of_nonneg_right (mul_nonneg ht hV.le))
        · have hi' : a i < t * V := by
            simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hi
          simp only [ite_eq_right hi, zero_add]
          exact hi'.le
      _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_ite_mem]
  have hcount : d * n / 2 ≤ (S.card : ℝ) := by
    have hnd : (n : ℝ) * (2 * t) ≤ n * d :=
      mul_le_mul_of_nonneg_left htd (Nat.cast_nonneg n)
    nlinarith [hmass.trans hsum]
  simpa only [S, ncard_eq_toFinset_card', Set.toFinset_ofPred] using hcount

/-- Geometry survives an injective restriction of the index set. -/
theorem body_geometry_restrict {n k : ℕ} {U : Fin n → Set Space}
    {x : Fin n → Space} {δ B w : ℝ} (hG : BodyGeometry U x δ B w)
    (f : Fin k → Fin n) : BodyGeometry (U ∘ f) (x ∘ f) δ B w where
  compact i := hG.compact (f i)
  convex i := hG.convex (f i)
  bounded i := hG.bounded (f i)
  interior i := hG.interior (f i)
  diameter i := hG.diameter (f i)
  width i := hG.width (f i)
  volume_bounds i := hG.volume_bounds (f i)

/-- The convex count loses no constant under restriction. -/
theorem body_convex_count_restrict {n k : ℕ} {U : Fin n → Set Space}
    {w m : ℝ} (hw : 0 ≤ w) (hK : BodyConvexCount U w m)
    (f : Fin k → Fin n) (hf : Function.Injective f) :
    BodyConvexCount (U ∘ f) w m := by
  intro Q hQ
  apply (ENNReal.ofReal_le_ofReal _).trans (hK Q hQ)
  apply mul_le_mul_of_nonneg_right _ hw
  apply Nat.cast_le.mpr
  exact Set.ncard_le_ncard_of_injOn f (fun _ hi => hi) hf.injOn

/-- Average density suffices to select a nonempty family with individual density.
The count loss is explicit and is linear in the original density. -/
theorem select_dense_bodies {n : ℕ} {U Y : Fin n → Set Space} {w D t : ℝ}
    (hn : 0 < n) (hw : 0 < w) (hD : 0 < D) (ht : 0 ≤ t) (htD : 768 * t ≤ D)
    (hYU : ∀ i, Y i ⊆ U i)
    (hvol : ∀ i, volume (U i) ≤ ENNReal.ofReal (384 * w))
    (hmass : ENNReal.ofReal (D * n * w) ≤ ∑ i, volume (Y i)) :
    ∃ (k : ℕ) (f : Fin k → Fin n), Function.Injective f ∧ 0 < k ∧
      D * n / 768 ≤ (k : ℝ) ∧
      ∀ i, ENNReal.ofReal t * volume (U (f i)) ≤ volume (Y (f i)) := by
  classical
  have hYfinite : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((measure_mono (hYU i)).trans (hvol i))
  let a : Fin n → ℝ := fun i => (volume (Y i)).toReal
  have ha : ∀ i, a i ≤ 384 * w := by
    intro i
    have hi := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((measure_mono (hYU i)).trans (hvol i))
    simpa only [a, ENNReal.toReal_ofReal (by positivity : 0 ≤ 384 * w)] using hi
  have hmassR : (D / 384) * n * (384 * w) ≤ ∑ i, a i := by
    have hi := ENNReal.toReal_mono
      (ENNReal.sum_ne_top.mpr (fun i _ => hYfinite i)) hmass
    rw [ENNReal.toReal_sum (fun i _ => hYfinite i),
      ENNReal.toReal_ofReal (by positivity)] at hi
    convert hi using 1 <;> ring
  have hcard := dense_entries_card a (by positivity : 0 < 384 * w) ht
    (by linarith : 2 * t ≤ D / 384) ha hmassR
  let S : Finset (Fin n) := {i | t * (384 * w) ≤ a i}.toFinset
  have hcardS : D * n / 768 ≤ (S.card : ℝ) := by
    calc
      D * n / 768 = (D / 384) * n / 2 := by ring
      _ ≤ _ := by simpa only [S, ncard_eq_toFinset_card'] using hcard
  let f : Fin S.card → Fin n := fun i => (S.equivFin.symm i).val
  have hf : Function.Injective f := Subtype.val_injective.comp S.equivFin.symm.injective
  have hcountpos : (0 : ℝ) < S.card :=
    (by positivity : (0 : ℝ) < D * n / 768).trans_le hcardS
  refine ⟨S.card, f, hf, Nat.cast_pos.mp hcountpos, hcardS, ?_⟩
  intro i
  have hi : t * (384 * w) ≤ a (f i) := by
    simpa only [S, Set.mem_toFinset, Set.mem_setOf_eq] using (S.equivFin.symm i).property
  calc
    _ ≤ ENNReal.ofReal t * ENNReal.ofReal (384 * w) :=
      mul_le_mul' le_rfl (hvol (f i))
    _ = ENNReal.ofReal (t * (384 * w)) := (ENNReal.ofReal_mul ht).symm
    _ ≤ _ := (ENNReal.ofReal_le_iff_le_toReal (hYfinite (f i))).mpr hi

/-- Convex-body volume gain in the average-density form present in the grains
configuration. The loss is the original density, with no logarithmic factor. -/
theorem convex_body_estimate_average {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (U Y : Fin n → Set Space)
        (x : Fin n → Space) (B w m D : ℝ),
      0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → δ ≤ B → 0 < w → 1 ≤ m → 0 < D →
      768 * δ ^ η ≤ D → BodyGeometry U x δ B w → (∀ i, U i ⊆ ball (0 : Space) 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      ENNReal.ofReal (D * n * w) ≤ ∑ i, volume (Y i) → BodyConvexCount U w m →
      ENNReal.ofReal (A * δ ^ ε * B ^ ω * m ^ (-1 - σ / 2) * D * n * w ^ (1 + σ / 2)) ≤
        volume (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ :=
    convex_body_estimate hσ hσhalf hω hE ε hε
  refine ⟨A / 768, η, d₀, by positivity, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n U Y x B w m D hn hcount hδB hw hm hD htD hG hball hYm hYU hden hK
  obtain ⟨k, f, hf, hk, hkcount, hfdense⟩ := select_dense_bodies hn hw hD
    (Real.rpow_nonneg hδ.le η) htD hYU (fun i => (hG.volume_bounds i).2) hden
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_injective f hf
  have hv := H δ hδ hδd k (U ∘ f) (Y ∘ f) (x ∘ f) B w m hk
    ((Nat.cast_le.mpr hkn).trans hcount) hδB hw hm (body_geometry_restrict hG f)
    (fun i => hball (f i)) (fun i => hYm (f i)) (fun i => hYU (f i)) hfdense
    (body_convex_count_restrict hw.le hK f hf)
  apply le_trans _ (hv.trans (measure_mono (iUnion_subset fun i => subset_iUnion Y (f i))))
  apply ENNReal.ofReal_le_ofReal
  have hB : 0 < B := hδ.trans_le hδB
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hfac : 0 ≤ A * δ ^ ε * B ^ ω * m ^ (-1 - σ / 2) * w ^ (1 + σ / 2) := by
    positivity
  convert mul_le_mul_of_nonneg_left hkcount hfac using 1 <;> ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
