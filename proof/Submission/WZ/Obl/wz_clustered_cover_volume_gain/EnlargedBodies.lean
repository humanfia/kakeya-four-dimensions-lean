-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.EnlargedBodies.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SquareRootPacking

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

theorem convex_count_of_enlargement {n : ℕ} {V U : Fin n → Set Space} {v w m : ℝ}
    (hv : 0 < v) (hw : 0 ≤ w) (hm : 0 ≤ m) (hVU : ∀ i, V i ⊆ U i)
    (hc : BodyConvexCount V v m) : BodyConvexCount U w (m * w / v) := by
  intro Q hQ
  have hcard : ({i | U i ⊆ Q}.ncard : ℝ) ≤ ({i | V i ⊆ Q}.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard (fun i hi => (hVU i).trans hi)
  calc
    ENNReal.ofReal (({i | U i ⊆ Q}.ncard : ℝ) * w) =
        ENNReal.ofReal (w / v) * ENNReal.ofReal (({i | U i ⊆ Q}.ncard : ℝ) * v) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal (w / v) * ENNReal.ofReal (({i | V i ⊆ Q}.ncard : ℝ) * v) := by
      apply mul_le_mul' le_rfl
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hv.le)
    _ ≤ ENNReal.ofReal (w / v) * (ENNReal.ofReal m * volume Q) := mul_le_mul' le_rfl (hc Q hQ)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

theorem slab_count_of_enlargement {n : ℕ} {V U : Fin n → Set Space} {l : ℝ}
    (hVU : ∀ i, V i ⊆ U i) (hs : BodySlabCount V l) : BodySlabCount U l := by
  intro ν t r hν hr
  apply le_trans _ (hs ν t r hν hr)
  apply ENNReal.ofReal_le_ofReal
  exact_mod_cast Set.ncard_le_ncard (fun i hi => (hVU i).trans hi)

/-- Applying E to enlarged bodies produces a gain from their volume ratio.
The original convex and slab counts suffice; no separation of the enlarged
bodies is required. -/
theorem enlarged_body_estimate {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (V U Y : Fin n → Set Space)
        (x : Fin n → Space) (B v w m l : ℝ),
      0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → δ ≤ B → 0 < v → v ≤ w → 1 ≤ m → 1 ≤ l →
      BodyGeometry U x δ B w → (∀ i, V i ⊆ U i) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      (∀ i, ENNReal.ofReal (δ ^ η) * volume (U i) ≤ volume (Y i)) →
      BodyConvexCount V v m → BodySlabCount V l →
      ENNReal.ofReal (A * δ ^ ε * B ^ ω *
        (m ^ (-1 + σ) * l ^ (-σ) * n ^ (1 - σ) * v ^ (1 - σ / 2) * (w / v) ^ (σ / 2))) ≤
        volume (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ :=
    body_estimate_of_tube_estimate hσ hσhalf hω hE ε hε
  refine ⟨A, η, d₀, hA, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n V U Y x B v w m l hn hnmax hδB hv hvw hm hl G hVU hYm hYU hden hK hslab
  have hw : 0 < w := hv.trans_le hvw
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hM : 1 ≤ m * w / v := by
    apply (le_div_iff₀ hv).mpr
    nlinarith [mul_le_mul_of_nonneg_right hm hw.le]
  have hM0 : 0 < m * w / v := by positivity
  have hK' := convex_count_of_enlargement hv hw.le hm0.le hVU hK
  have hpack := sqrt_packing_of_convex_count hw hM0 (fun i => (G.volume_bounds i).1) hK'
  have hf := H δ hδ hδd n U Y x B w (m * w / v) l (Real.sqrt (m * w / v))
    hn hnmax hδB hw hM hl (Real.one_le_sqrt.mpr hM) G hYm hYU hden hK'
    (slab_count_of_enlargement hVU hslab) hpack
  rwa [enlarged_body_weight hv hw hm0 (zero_lt_one.trans_le hl) (Nat.cast_pos.mpr hn)] at hf

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
