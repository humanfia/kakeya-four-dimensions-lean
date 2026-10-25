-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.AnisotropicPlanarPacket.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.AnisotropicPrismPieces
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PlanarFrame

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- Physical crossing prisms from a planar ellipsoidal cell. The volume
budget preserves the transverse coarse scale rho. -/
theorem anisotropic_planar_packet_prisms :
    ∃ D : ℕ, 0 < D ∧ ∀ (δ ρ c lam density t r : ℝ), 0 < δ → 0 < ρ → 0 < r →
      ρ ≤ 1 / 256 → 0 < c → c ≤ 1 / 256 → 512 * c ≤ r → 16 * δ ≤ 128 * ρ * c →
      2560 * c ≤ lam → 0 ≤ density →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (y w u p₀ : V),
      ‖w‖ = 1 → ‖u‖ = 1 →
      {i | (Y i).Nonempty}.Nonempty →
      (∀ i, ‖v i‖ = 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ T δ (x i) (v i)) →
      (∀ i, (Y i).Nonempty → T δ (x i) (v i) ⊆ T ρ y w) →
      (∀ i, Y i ⊆ {p | ‖(p - p₀) - (inner ℝ w (p - p₀)) • w‖ ≤ ρ * r ∧
        |inner ℝ w (p - p₀)| ≤ r ∧ |inner ℝ u p - t| ≤ 20 * δ}) →
      (∀ i, (Y i).Nonempty → |inner ℝ u (v i)| ≤ 2 * δ / r) →
      o (lam * n * δ ^ 2) ≤ ∑ i, μ (Y i) →
      o (density * ((16 * δ) * ρ * r ^ 2)) ≤ μ (⋃ i, Y i) →
      ∀ M : ENNReal, M ≠ 0 → M ≠ ⊤ →
      (∀ p ∈ ⋃ i, Y i, M ≤ multiplicity Y p) →
      (∀ p, multiplicity Y p ≤ 2 * M) →
      ∃ (e : V ≃ₗᵢ[ℝ] V) (F : Finset V) (Z : Fin n → Set V) (H : V → Set V),
        (∀ p, e p 0 = inner ℝ u p) ∧
        (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2 ∧
        (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
        (↑F : Set V).PairwiseDisjoint (fun z => P (16 * δ) (128 * ρ * c) c z e) ∧
        (∀ z ∈ F, MeasurableSet (H z) ∧ H z ⊆ P (16 * δ) (128 * ρ * c) c z e ∧
          (H z).Nonempty ∧ P (16 * δ) (128 * ρ * c) c z e ⊆ T (2 * ρ) y w) ∧
        (⋃ z ∈ F, H z) = ⋃ i, Z i ∧
        (∑ i, μ (Y i)) ≤ (D : ENNReal) * ∑ i, μ (Z i) ∧
        o (density * F.card * ((16 * δ) * (128 * ρ * c) * c)) ≤
          (D : ENNReal) * ∑ z ∈ F, μ (H z) ∧
        (∀ i z, z ∈ F → (Z i ∩ H z).Nonempty →
          Z i ∩ P (16 * δ) (128 * ρ * c) c z e ⊆ H z ∧
          (∀ p ∈ T δ (x i) (v i) ∩ frontier (P (16 * δ) (128 * ρ * c) c z e),
            |e (p - z) 2| = c / 2) ∧
          (∀ s ∈ ({-c / 2, c / 2} : Set ℝ),
            ∃ p ∈ T δ (x i) (v i) ∩ P (16 * δ) (128 * ρ * c) c z e,
              e (p - z) 2 = s)) := by
  classical
  obtain ⟨D, hD, hpieces⟩ := anisotropic_planar_prism_piece_refinement
  refine ⟨D, hD, ?_⟩
  intro δ ρ c lam density t r hδ hρ hr hρ256 hc hc256 hcr hsize hbudget hdensity
    n x v Y y w u p₀ hw hu hQ hY hcover hslab hnormal hdense hvol M hM0 hMtop hlower hupper
  have hc2r : 2 * c ≤ r := by linarith
  have hδc : 16 * δ ≤ c := by
    have hh := mul_le_mul_of_nonneg_right hρ256 hc.le
    nlinarith
  have hbρ : 2 * (128 * ρ * c) ≤ ρ := by
    have hh := mul_le_mul_of_nonneg_left hc256 hρ.le
    nlinarith
  have hτρ : 2 * (2 * δ / r) ≤ ρ := by
    apply (le_of_mul_le_mul_right ?_ hr)
    have hh := mul_le_mul_of_nonneg_left hcr hρ.le
    have he : (2 * (2 * δ / r)) * r = 4 * δ := by field_simp; norm_num
    rw [he]
    nlinarith
  obtain ⟨e, he0, hew, hdir⟩ := exists_coarse_frame_from_normals hδ hρ hτρ
    (by linarith) hu hw {i | (Y i).Nonempty} hQ (fun i _ => (hY i).1)
    (fun i hi => hcover i hi) (fun i hi => hnormal i hi)
  have hframe : |e w 1| ≤ 10 * ρ := by
    nlinarith [sq_nonneg (e w 0), sq_abs (e w 1), abs_nonneg (e w 1)]
  obtain ⟨i₀, hi₀⟩ := hQ
  change (Y i₀).Nonempty at hi₀
  let j : Fin n → Fin n := fun i => if (Y i).Nonempty then i else i₀
  have hj (i : Fin n) : (Y (j i)).Nonempty := by
    by_cases hi : (Y i).Nonempty
    · simpa only [j, if_pos hi] using hi
    · simpa only [j, if_neg hi] using hi₀
  have hj_eq (i : Fin n) (hi : (Y i).Nonempty) : j i = i := by simp [j, hi]
  have hY' (i : Fin n) : ‖v (j i)‖ = 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ T δ (x (j i)) (v (j i)) := by
    refine ⟨(hY (j i)).1, (hY i).2.1, ?_⟩
    intro p hp
    rw [hj_eq i ⟨p, hp⟩]
    exact (hY i).2.2 hp
  have hslab' : (⋃ i, Y i) ⊆ {p | ‖(p - p₀) - (inner ℝ w (p - p₀)) • w‖ ≤ ρ * r ∧
      |inner ℝ w (p - p₀)| ≤ r ∧ |e (p - p₀) 0 - (t - inner ℝ u p₀)| ≤ 20 * δ} := by
    intro p hp
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
    have hh := hslab i hpi
    refine ⟨hh.1, hh.2.1, ?_⟩
    have he : e (p - p₀) 0 - (t - inner ℝ u p₀) = inner ℝ u p - t := by
      rw [he0, inner_sub_right]
      ring
    rw [he]
    exact hh.2.2
  have hbounded : TotallyBounded (⋃ i, Y i) := by
    apply (isCompact_closedBall p₀ (2 * r)).totallyBounded.subset
    intro p hp
    have hh := hslab' hp
    have he : p - p₀ = ((p - p₀) - (inner ℝ w (p - p₀)) • w) +
        (inner ℝ w (p - p₀)) • w := by module
    have hnorm : ‖p - p₀‖ ≤ 2 * r := by
      calc
        _ = ‖((p - p₀) - (inner ℝ w (p - p₀)) • w) + (inner ℝ w (p - p₀)) • w‖ := congrArg norm he
        _ ≤ ‖(p - p₀) - (inner ℝ w (p - p₀)) • w‖ + ‖(inner ℝ w (p - p₀)) • w‖ := norm_add_le _ _
        _ ≤ ρ * r + r := by
          rw [norm_smul, Real.norm_eq_abs, hw, mul_one]
          exact add_le_add hh.1 hh.2.1
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hρ256 hr.le]
    exact mem_closedBall.mpr (by simpa only [dist_eq_norm] using hnorm)
  have hdir' (i : Fin n) : 1 / 2 ≤ |e (v (j i)) 2| ∧
      c * |e (v (j i)) 0| ≤ (16 * δ) / 16 ∧
      c * |e (v (j i)) 1| ≤ (128 * ρ * c) / 16 := by
    have hh := hdir (j i) (hj i)
    refine ⟨hh.1, ?_, ?_⟩
    · have hn : c * (2 * δ / r) ≤ δ := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hr).mpr
        nlinarith [mul_le_mul_of_nonneg_right hc2r hδ.le]
      have h := (mul_le_mul_of_nonneg_left hh.2.1 hc.le).trans hn
      simpa using h
    · have hm := mul_le_mul_of_nonneg_left hh.2.2 hc.le
      nlinarith
  obtain ⟨F, Z, H, hZ, hdisj, hH, hunion, hmass, hden, hcross⟩ :=
    hpieces δ ρ (16 * δ) (128 * ρ * c) c lam density (20 * δ) (t - inner ℝ u p₀) r
      hδ hr.le (by gcongr; linarith) (by linarith) (by positivity) (by linarith)
      le_rfl hsize hδc (by linarith) hbρ (by linarith) hbudget hdensity
      e n (fun i => x (j i)) (fun i => v (j i)) Y y w p₀ hw hframe hY'
      (fun i => hcover (j i) (hj i)) hbounded hslab' hdense hvol hdir' M hM0 hMtop hlower hupper
  refine ⟨e, F, Z, H, he0, hew, hZ, hdisj, hH, hunion, hmass, hden, ?_⟩
  intro i z hz hmeet
  have hi : (Y i).Nonempty := by
    obtain ⟨p, hpZi, -⟩ := hmeet
    exact ⟨p, (hZ i).2 hpZi⟩
  simpa only [hj_eq i hi] using hcross i z hz hmeet

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
