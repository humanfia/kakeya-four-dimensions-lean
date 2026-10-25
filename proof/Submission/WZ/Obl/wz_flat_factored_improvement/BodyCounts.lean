-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.BodyCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyPackets
import Submission.WZ.Obl.wz_unit_segment_convex_slab_cover.Geometry
import Submission.WZ.Obl.wz_affine_packet_counting_transfer.Counting

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open Module MeasureTheory Set Metric
open scoped ENNReal

def BodyConvexCount {n : ℕ} (U : Fin n → Set Space) (w m : ℝ) : Prop :=
  ∀ Q : Set Space, Convex ℝ Q →
    ENNReal.ofReal ((Set.ncard {i | U i ⊆ Q} : ℝ) * w) ≤ ENNReal.ofReal m * volume Q

def BodySlabCount {n : ℕ} (U : Fin n → Set Space) (l : ℝ) : Prop :=
  ∀ (ν : Space) (s r : ℝ), ‖ν‖ = 1 → 0 < r →
    ENNReal.ofReal (Set.ncard {i | U i ⊆ {p | |inner ℝ ν p - s| ≤ r}} : ℝ) ≤
      ENNReal.ofReal (l * (n : ℝ) * r)

def BodyPacking {n : ℕ} (U : Fin n → Set Space) (w P : ℝ) : Prop :=
  ∀ Q : Set Space, Convex ℝ Q →
    ENNReal.ofReal (Real.sqrt (Set.ncard {i | U i ⊆ Q} : ℝ) * w) ≤
      ENNReal.ofReal P * volume Q

/-- A diameter lower bound replaces the unit-segment hypothesis in the slab lemma. -/
theorem diameter_thin_slab {W : Set Space} (hW : Convex ℝ W) {s : ℝ} (hs : 0 < s)
    (hvol : volume W ≤ ENNReal.ofReal s)
    (hdiam : ∃ x ∈ W, ∃ y ∈ W, (1 / 16 : ℝ) ≤ dist x y) :
    ∃ (ν : Space) (a : ℝ), ‖ν‖ = 1 ∧
      W ⊆ {p | |inner ℝ ν p - a| ≤ 32 * Real.sqrt s} := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hdiam
  have hd : 0 < ‖y - x‖ := by rw [dist_eq_norm, norm_sub_rev] at hxy; linarith
  let v := ‖y - x‖⁻¹ • (y - x)
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), inv_mul_cancel₀ hd.ne']
  obtain ⟨b, hb⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hv
  obtain ⟨ν, hν, hthin⟩ :=
    WangZahlLot.Obl.wz_unit_segment_convex_slab_cover.slab_of_determinant_bound
      (r := 32 * Real.sqrt s) b x W
      (mul_pos (by norm_num) (Real.sqrt_pos.mpr hs)) (by
        intro p hp q hq
        have hdet := WangZahlLot.Obl.wz_unit_segment_convex_slab_cover.determinant_le_volume
          hW hx (show x + (y - x) ∈ W by simpa using hy) hp hq b hs.le hvol
        have he : b.toBasis.det ![b 0, p - x, q - x] =
            ‖y - x‖⁻¹ * b.toBasis.det ![y - x, p - x, q - x] := by
          rw [hb]
          simp only [v, Basis.det_apply, Matrix.det_fin_three, Basis.toMatrix_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, map_smul,
            Finsupp.smul_apply, smul_eq_mul]
          ring
        have hinv : ‖y - x‖⁻¹ ≤ 16 := by
          rw [inv_eq_one_div, div_le_iff₀ hd]
          rw [dist_eq_norm, norm_sub_rev] at hxy
          linarith
        rw [he, abs_mul, abs_of_pos (inv_pos.mpr hd), mul_pow, Real.sq_sqrt hs.le]
        have hh := mul_le_mul hinv hdet (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 16)
        norm_num at hh ⊢
        nlinarith only [hh])
  exact ⟨ν, inner ℝ ν x, hν, hthin⟩

theorem body_convex_transfer {n N q : ℕ} {U : Fin n → Set Space} {w m D ρ : ℝ}
    (hw : 0 < w) (hm : 0 ≤ m) (hD : 0 < D) (hρ : 0 < ρ) (hq : 0 < q)
    (f : Space ≃ᵃ[ℝ] Space) (z v : Fin N → Space) (F : Fin N → Finset (Fin n))
    (hcard : ∀ j, (F j).card = q) (hdisj : ∀ j k, j ≠ k → Disjoint (F j) (F k))
    (hwhole : ∀ j, ∀ i ∈ F j, U i ⊆ f '' Tube ρ (z j) (v j))
    (hvol : ∀ Q : Set Space, volume (f '' Q) = ENNReal.ofReal D * volume Q)
    (hc : BodyConvexCount U w m) :
    ConvexCount ρ (m * D * ρ ^ 2 / ((q : ℝ) * w)) N z v := by
  intro Q hQ
  let S : Set (Fin N) := {j | Tube ρ (z j) (v j) ⊆ Q}
  let A : Set (Fin n) := {i | U i ⊆ f '' Q}
  have hcount := WangZahlLot.Obl.wz_affine_packet_counting_transfer.fiber_count F hcard hdisj S A
    (fun j hj i hi => (hwhole j i hi).trans (image_mono hj))
  have hcount' : (S.ncard : ℝ) * (q : ℝ) ≤ A.ncard := by exact_mod_cast hcount
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hmass : ENNReal.ofReal ((S.ncard : ℝ) * q * w) ≤ ENNReal.ofReal (m * D) * volume Q := by
    calc
      _ ≤ ENNReal.ofReal ((A.ncard : ℝ) * w) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcount' hw.le)
      _ ≤ ENNReal.ofReal m * volume (f '' Q) := hc _ (hQ.affine_image f.toAffineMap)
      _ = _ := by rw [hvol, ENNReal.ofReal_mul hm, mul_assoc]
  change ENNReal.ofReal ((S.ncard : ℝ) * ρ ^ 2) ≤ _
  calc
    _ = ENNReal.ofReal (ρ ^ 2 / ((q : ℝ) * w)) * ENNReal.ofReal ((S.ncard : ℝ) * q * w) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal (ρ ^ 2 / ((q : ℝ) * w)) * (ENNReal.ofReal (m * D) * volume Q) :=
      mul_le_mul' le_rfl hmass
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

theorem body_packing_fiber {n q : ℕ} {U : Fin n → Set Space} {w P D ρ : ℝ}
    (hw : 0 < w) (hP : 0 ≤ P) (hD : 0 < D) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (f : Space ≃ᵃ[ℝ] Space) (z v : Space) (hv : ‖v‖ = 1) (F : Finset (Fin n))
    (hcard : F.card = q) (hwhole : ∀ i ∈ F, U i ⊆ f '' Tube ρ z v)
    (hvol : ∀ Q : Set Space, volume (f '' Q) = ENNReal.ofReal D * volume Q)
    (hp : BodyPacking U w P) :
    Real.sqrt (q : ℝ) * w ≤ P * D * (384 * ρ ^ 2) := by
  let Q := f '' Tube ρ z v
  have hconv : Convex ℝ Q :=
    (WangZahlLot.Obl.wz_affine_packet_counting_transfer.convex_tube _ _ _).affine_image f.toAffineMap
  have hc : q ≤ Set.ncard {i | U i ⊆ Q} := by
    rw [← hcard, ← ncard_coe_finset F]
    exact ncard_le_ncard (fun i hi => hwhole i hi)
  have hc' : (q : ℝ) ≤ (Set.ncard {i | U i ⊆ Q} : ℝ) := by exact_mod_cast hc
  have hupper : volume Q ≤ ENNReal.ofReal (D * (384 * ρ ^ 2)) := by
    change volume (f '' Tube ρ z v) ≤ _
    rw [hvol, ENNReal.ofReal_mul hD.le]
    exact mul_le_mul' le_rfl
      (WangZahlLot.Obl.wz_affine_packet_counting_transfer.tube_volume_upper hρ hρ1 z v hv)
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  calc
    ENNReal.ofReal (Real.sqrt (q : ℝ) * w) ≤
        ENNReal.ofReal (Real.sqrt (Set.ncard {i | U i ⊆ Q} : ℝ) * w) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hc') hw.le
    _ ≤ ENNReal.ofReal P * volume Q := hp Q hconv
    _ ≤ ENNReal.ofReal P * ENNReal.ofReal (D * (384 * ρ ^ 2)) := mul_le_mul' le_rfl hupper
    _ = _ := by rw [← ENNReal.ofReal_mul hP]; congr 1; ring

theorem body_slab_transfer {n N q : ℕ} {U : Fin n → Set Space} {l D ρ : ℝ}
    (hl : 0 ≤ l) (hD : 0 < D) (hN : 0 < N) (hq : 0 < q)
    (f : Space ≃ᵃ[ℝ] Space) (z v : Fin N → Space) (F : Fin N → Finset (Fin n))
    (hcard : ∀ j, (F j).card = q) (hdisj : ∀ j k, j ≠ k → Disjoint (F j) (F k))
    (hwhole : ∀ j, ∀ i ∈ F j, U i ⊆ f '' Tube ρ (z j) (v j))
    (hbounded : ∀ j, Tube ρ (z j) (v j) ⊆ ball (0 : Space) 1)
    (hdiam : ∀ i, ∃ p ∈ U i, ∃ q ∈ U i, (1 / 16 : ℝ) ≤ dist p q)
    (hvol : ∀ Q : Set Space, volume (f '' Q) = ENNReal.ofReal D * volume Q)
    (hs : BodySlabCount U l) :
    (N : ℝ) * (q : ℝ) ≤ 128 * l * (n : ℝ) * Real.sqrt D := by
  let Q := f '' ball (0 : Space) 1
  have hQ : Convex ℝ Q := (convex_ball (0 : Space) 1).affine_image f.toAffineMap
  have hUQ : ∀ j, ∀ i ∈ F j, U i ⊆ Q :=
    fun j i hi => (hwhole j i hi).trans (image_mono (hbounded j))
  have hQvol : volume Q ≤ ENNReal.ofReal (8 * D) := by
    change volume (f '' ball (0 : Space) 1) ≤ _
    rw [hvol]
    calc
      _ ≤ ENNReal.ofReal D * 8 := mul_le_mul' le_rfl
        ((measure_mono ball_subset_closedBall).trans
          WangZahlLot.Obl.wz_regular_transverse_affine_cells.volume_unit_closedBall_upper)
      _ = _ := by
        rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul hD.le]
        congr 1
        ring
  have hQdiam : ∃ p ∈ Q, ∃ q ∈ Q, (1 / 16 : ℝ) ≤ dist p q := by
    let j : Fin N := ⟨0, hN⟩
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (F j).card by rw [hcard]; exact hq)
    obtain ⟨p, hp, q, hq, hpq⟩ := hdiam i
    exact ⟨p, hUQ j i hi hp, q, hUQ j i hi hq, hpq⟩
  obtain ⟨ν, a, hν, hthin⟩ := diameter_thin_slab hQ (by positivity : 0 < 8 * D) hQvol hQdiam
  let A : Set (Fin n) := {i | U i ⊆ {p | |inner ℝ ν p - a| ≤ 32 * Real.sqrt (8 * D)}}
  have hcount : N * q ≤ A.ncard := by
    simpa using WangZahlLot.Obl.wz_affine_packet_counting_transfer.fiber_count F hcard hdisj
      Set.univ A (fun j _ i hi => (hUQ j i hi).trans hthin)
  have hcount' : (N : ℝ) * (q : ℝ) ≤ A.ncard := by exact_mod_cast hcount
  have hraw : (N : ℝ) * (q : ℝ) ≤ l * (n : ℝ) * (32 * Real.sqrt (8 * D)) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    exact (ENNReal.ofReal_le_ofReal hcount').trans (hs ν a _ hν (by positivity))
  have hroot : 32 * Real.sqrt (8 * D) ≤ 128 * Real.sqrt D := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    have h8 : Real.sqrt (8 : ℝ) ≤ 4 := by
      exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    nlinarith [mul_le_mul_of_nonneg_right h8 (Real.sqrt_nonneg D)]
  exact hraw.trans (by nlinarith only [mul_le_mul_of_nonneg_left hroot (mul_nonneg hl (Nat.cast_nonneg n))])

end WangZahlLot.Obl.wz_flat_factored_improvement
