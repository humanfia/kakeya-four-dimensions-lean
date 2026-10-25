-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.NeighborhoodEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.TubeEnlargement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BallDensity

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

lemma enlarged_tube_factor {d r m l n σ ω : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hm : 0 < m) (hl : 0 < l) (hn : 0 < n) :
    (r / 8) ^ ω * (m ^ (-1 + σ) * (8 * l) ^ (-σ) * n ^ (1 - σ) *
      (d ^ 2 / 512) ^ (1 - σ / 2) * ((r ^ 2 / 8) / (d ^ 2 / 512)) ^ (σ / 2)) =
    ((1 / 8 : ℝ) ^ ω * (8 : ℝ) ^ (-σ) * (1 / 512 : ℝ) ^ (1 - σ / 2) *
      (512 / 8 : ℝ) ^ (σ / 2)) *
    (r ^ ω * m ^ (-1 + σ) * l ^ (-σ) * n ^ (1 - σ) * d ^ (2 - σ) * (r / d) ^ σ) := by
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow, Real.log_one]
  ring

/-- E supplies a quantitative estimate for a thickened union using the
original fine-family counts. The enlarged family need not be separated. -/
theorem tube_neighborhood_estimate {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ (D d r : ℝ), 0 < D → D ≤ d₀ → 0 < d → d ≤ r → r ≤ 1 → D ≤ r / 8 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (m l : ℝ),
      0 < n → (n : ℝ) ≤ D ^ (-100 : ℝ) → 1 ≤ m → 1 ≤ l →
      (∀ i, ‖v i‖ = 1) → (∀ i, Tube d (x i) (v i) ⊆ ball 0 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube d (x i) (v i)) →
      (∀ i, ENNReal.ofReal (64 * D ^ η * d ^ 2) ≤ volume (Y i)) →
      BodyConvexCount (fun i => Tube d (x i) (v i)) (d ^ 2) m →
      BodySlabCount (fun i => Tube d (x i) (v i)) l →
      ENNReal.ofReal (A * D ^ ε *
        (r ^ ω * m ^ (-1 + σ) * l ^ (-σ) * n ^ (1 - σ) * d ^ (2 - σ) * (r / d) ^ σ)) ≤
        volume (thickening (3 * r) (⋃ i, Y i)) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ := enlarged_body_estimate hσ hσhalf hω hE ε hε
  let C : ℝ := (1 / 8 : ℝ) ^ ω * (8 : ℝ) ^ (-σ) * (1 / 512 : ℝ) ^ (1 - σ / 2) *
    (512 / 8 : ℝ) ^ (σ / 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨512 * A * C, η, d₀, by positivity, hη, hd₀, hd₀small, ?_⟩
  intro D d r hD hDd hd hdr hr1 hDr n x v Y m l hn hnmax hm hl hv hball hYm hYT hden hK hF
  have hr : 0 < r := hd.trans_le hdr
  choose u hu using fun i => WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first (hv i)
  obtain ⟨U, Z, c, hG, hTU, hZm, hZU, hZden, hsub⟩ :=
    tube_enlargement_data hd hdr hr1 (by linarith : D ≤ r / 4)
      (Real.rpow_pos_of_pos hD η).le x u Y
      (fun i => by simpa only [hu i] using hball i) hYm
      (fun i => by simpa only [hu i] using hYT i) hden
  have hweight : 0 < d ^ 2 / 512 := by positivity
  have hweight_le : d ^ 2 / 512 ≤ r ^ 2 / 8 := by
    have hsq : d ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hd.le hdr 2
    nlinarith [sq_nonneg r]
  have hK' : BodyConvexCount (fun i => eighthEquiv '' Tube d (x i) (u i 0)) (d ^ 2 / 512) m := by
    have hh := hK.affine_image (sq_nonneg d) (by norm_num : (0 : ℝ) < 1 / 512)
      eighthEquiv eighthEquiv_volume
    convert hh using 1
    · congr 1
      funext i
      rw [hu i]
    · ring
  have hF' : BodySlabCount (fun i => eighthEquiv '' Tube d (x i) (u i 0)) (8 * l) := by
    simpa only [hu] using body_slab_eighth hF
  have hh := H D hD hDd n (fun i => eighthEquiv '' Tube d (x i) (u i 0)) U Z c
    (r / 8) (d ^ 2 / 512) (r ^ 2 / 8) m (8 * l) hn hnmax hDr hweight hweight_le
    hm (by linarith) hG hTU hZm hZU hZden hK' hF'
  have hmass := hh.trans (measure_mono hsub)
  rw [eighthEquiv_volume] at hmass
  have hfactor := enlarged_tube_factor (σ := σ) (ω := ω) hd hr (zero_lt_one.trans_le hm)
    (zero_lt_one.trans_le hl) (Nat.cast_pos.mpr hn)
  have he : A * D ^ ε * (r / 8) ^ ω *
      (m ^ (-1 + σ) * (8 * l) ^ (-σ) * (n : ℝ) ^ (1 - σ) *
        (d ^ 2 / 512) ^ (1 - σ / 2) * ((r ^ 2 / 8) / (d ^ 2 / 512)) ^ (σ / 2)) =
      A * D ^ ε * C *
        (r ^ ω * m ^ (-1 + σ) * l ^ (-σ) * n ^ (1 - σ) * d ^ (2 - σ) * (r / d) ^ σ) := by
    rw [mul_assoc (A * D ^ ε), hfactor]
    dsimp [C]
    ring
  rw [he] at hmass
  have hmul := mul_le_mul' (le_refl (ENNReal.ofReal (512 : ℝ))) hmass
  convert hmul using 1
  · rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 512)]
    congr 1
    ring
  · rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 512)]
    norm_num

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
