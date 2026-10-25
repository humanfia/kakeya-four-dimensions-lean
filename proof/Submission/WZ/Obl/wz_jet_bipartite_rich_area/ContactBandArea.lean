-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactBandArea.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactBandGraph
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGraphBound
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactMesh
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGridArea
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactScale

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set MeasureTheory
open scoped Classical
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- A time mesh at any slope above the natural scale is no longer than the
natural contact interval. -/
theorem contact_mesh_le_natural_length {δ D s : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (hs : 0 < s) (hnat : δ * D ≤ s ^ 2) :
    δ / s ≤ Real.sqrt (δ / D) := by
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hD).mpr
  have hh := mul_le_mul_of_nonneg_left hnat hδ.le
  nlinarith only [hh]

/-- Uniform area bound for one slope band in a curvature-ordered short
window. The finite graph, the contact mesh, and short-window cases are
constructed internally. -/
theorem volume_contact_band_le {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (hsep : ∀ i j, i ≠ j → 0 < dist (q i) (q j))
    (A B : Finset (Fin n)) {δ D lower s l u M base : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (hs : 0 < s)
    (hl : -1 ≤ l) (hu : u ≤ 1) (hlu : l ≤ u) (hshort : u - l ≤ 1 / 10000)
    (hbase : 1 < base) (hratio : 2 * M * base ≤ D / 120)
    (hdiamA : ∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ 2 * D)
    (hcrossdist : ∀ i ∈ A, ∀ j ∈ B, dist (q i) (q j) ≤ 2 * D)
    (hwithinA : ∀ i ∈ A, ∀ j ∈ A, ∀ x ∈ Icc l u,
      |deriv (deriv (g i)) x - deriv (deriv (g j)) x| ≤ M)
    (hwithinB : ∀ i ∈ B, ∀ j ∈ B, ∀ x ∈ Icc l u,
      |deriv (deriv (g i)) x - deriv (deriv (g j)) x| ≤ M)
    (hcross : (∀ i ∈ A, ∀ j ∈ B, ∀ x ∈ Icc l u,
        D / 120 ≤ deriv (deriv (g i)) x - deriv (deriv (g j)) x) ∨
      (∀ i ∈ A, ∀ j ∈ B, ∀ x ∈ Icc l u,
        D / 120 ≤ deriv (deriv (g j)) x - deriv (deriv (g i)) x))
    (hnat : δ * D ≤ s ^ 2) (hband : lower = s / 2 ∨ s ^ 2 ≤ δ * D)
    (E : Set (ℝ × ℝ))
    (hE : ∀ p ∈ E, p.2 ∈ Icc l u ∧ ∃ i ∈ A, ∃ j ∈ B,
      |p.1 - g i p.2| ≤ δ ∧ |p.1 - g j p.2| ≤ δ ∧
      lower ≤ |deriv (g i) p.2 - deriv (g j) p.2| ∧
      |deriv (g i) p.2 - deriv (g j) p.2| ≤ s) :
    volume E ≤ ENNReal.ofReal (30000000000000000 *
      ((4 : ℝ) ^ (windowLensHeight base (10000 * s / D) l u + 1) + 1) *
      (((Nat.log 2 (A.card + B.card) + 1 : ℕ) : ℝ) ^ 3) *
      δ * Real.sqrt (δ / D) * ((A.card : ℝ) + B.card) *
      Real.sqrt ((A.card : ℝ) + B.card)) := by
  classical
  by_cases hne : E.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
    exact bot_le
  obtain ⟨p, hp⟩ := hne
  obtain ⟨_, i₀, hi₀, j₀, hj₀, _⟩ := hE p hp
  have hA : A.Nonempty := ⟨i₀, hi₀⟩
  have hB : B.Nonempty := ⟨j₀, hj₀⟩
  let N : ℝ := (A.card : ℝ) + B.card
  let F : ℝ := ((4 : ℝ) ^ (windowLensHeight base (10000 * s / D) l u + 1) + 1) *
    (((Nat.log 2 (A.card + B.card) + 1 : ℕ) : ℝ) ^ 3)
  have hN : 1 ≤ N := by
    have hh : 1 ≤ A.card := Finset.card_pos.mpr hA
    dsimp [N]
    exact_mod_cast (show 1 ≤ A.card + B.card by omega)
  have hF : 1 ≤ F := by
    have hL : (1 : ℝ) ≤ ((Nat.log 2 (A.card + B.card) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left 1 (Nat.log 2 (A.card + B.card))
    have hpow : (1 : ℝ) ≤ (4 : ℝ) ^ (windowLensHeight base (10000 * s / D) l u + 1) :=
      one_le_pow₀ (by norm_num)
    have hcub := one_le_pow₀ hL (n := 3)
    dsimp [F]
    nlinarith
  have hN0 : 0 ≤ N := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hrootN : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
  have hnatural := contact_mesh_le_natural_length hδ hD hs hnat
  suffices hfinal : volume E ≤ ENNReal.ofReal
      (30000000000000000 * F * δ * Real.sqrt (δ / D) * N * Real.sqrt N) by
    convert hfinal using 1
    congr 1
    dsimp [F, N]
    ring
  by_cases hsmall : u - l ≤ δ / s
  · have hfirst := volume_interval_strip_union_le A (fun i _ => (hg i).continuous) hδ.le
      (fun p hp => by
        obtain ⟨ht, i, hi, j, hj, hv, _⟩ := hE p hp
        exact ⟨ht, i, hi, hv⟩)
    have hac : (A.card : ℝ) ≤ N * Real.sqrt N := by
      have hh : (A.card : ℝ) ≤ N := le_add_of_nonneg_right (Nat.cast_nonneg _)
      have hh' := mul_le_mul_of_nonneg_left hrootN hN0
      nlinarith
    have hconst : (2 : ℝ) ≤ 30000000000000000 * F := by nlinarith
    apply hfirst.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      2 * δ * (u - l) * A.card ≤ 2 * δ * Real.sqrt (δ / D) * (N * Real.sqrt N) := by
        gcongr
        exact hsmall.trans hnatural
      _ = 2 * δ * Real.sqrt (δ / D) * N * Real.sqrt N := by ring
      _ ≤ _ := by gcongr
  · have hwidth : 0 < u - l := (div_pos hδ hs).trans (lt_of_not_ge hsmall)
    obtain ⟨ℓ, hℓ, hlo, hhi, T, hT, hcover⟩ := exists_interval_contact_mesh
      (by linarith : l < u) (div_pos hδ hs) (le_of_lt (lt_of_not_ge hsmall))
    have hlin : s * ℓ ≤ δ := by nlinarith [(le_div_iff₀ hs).mp hhi]
    have hmesh : δ ≤ 2 * s * ℓ := by
      have hh := mul_le_mul_of_nonneg_right hlo (by positivity : 0 ≤ 2 * s)
      have heq : δ / s / 2 * (2 * s) = δ := by field_simp
      rw [heq] at hh
      nlinarith
    have hstep : D * ℓ ≤ s := by
      apply (mul_le_mul_iff_right₀ hs).mp
      have hh := mul_le_mul_of_nonneg_left hlin hD.le
      nlinarith
    have hinterval : Icc l u ⊆ Icc (-1 : ℝ) 1 := fun x hx =>
      ⟨hl.trans hx.1, hx.2.trans hu⟩
    have hcurv : ∀ i ∈ A, ∀ j ∈ B, ∀ x ∈ Icc l u,
        D / 120 ≤ |deriv (deriv (g i)) x - deriv (deriv (g j)) x| := by
      intro i hi j hj x hx
      rcases hcross with h | h
      · exact (h i hi j hj x hx).trans (le_abs_self _)
      · rw [abs_sub_comm]
        exact (h i hi j hj x hx).trans (le_abs_self _)
    obtain ⟨R, time, htag, hHA, hHB, harea⟩ := exists_band_contact_graph hg hjet
      A B hA hB i₀ T hδ hs hℓ hD (fun i hi => hdiamA i hi i₀ hi₀)
      hcrossdist hinterval (fun k hk => hinterval (hT k hk)) hcover
      hlin hstep hmesh hnat hband hcurv E hE
    have hscale := contact_scale_separation hδ hD hs hnat
    have hcrowd := contactCrowding_bounds hδ hD hs hℓ.le hnat hmesh hlin
    have hcross' : (∀ (a : A) (b : B) x, x ∈ Icc l u →
        D / 120 ≤ deriv (deriv (g a)) x - deriv (deriv (g b)) x) ∨
      (∀ (a : A) (b : B) x, x ∈ Icc l u →
        D / 120 ≤ deriv (deriv (g b)) x - deriv (deriv (g a)) x) := by
      rcases hcross with h | h
      · exact Or.inl (fun a b x hx => h a a.2 b b.2 x hx)
      · exact Or.inr (fun a b x hx => h a a.2 b b.2 x hx)
    have hcount := incidence_le_of_crowded_near_contacts hg hjet hsep
      (Function.Embedding.subtype (fun i => i ∈ A))
      (Function.Embedding.subtype (fun i => i ∈ B)) R time
      hl hu hlu hshort (by positivity : 0 < D / 120) hbase hscale.1
      hratio hscale.2.1 hscale.2.2
      (fun a a' x hx => hwithinA a a.2 a' a'.2 x hx)
      (fun b b' x hx => hwithinB b b.2 b' b'.2 x hx)
      hcross' (fun a b hab => (htag a b hab).1)
      (fun a b hab => (htag a b hab).2) hcrowd.1 hHA hHB
    simp only [Fintype.card_coe] at hcount
    have hcancel : δ * ℓ * Real.sqrt (2 * contactCrowding δ D s) ≤
        80000 * δ * Real.sqrt (δ / D) := by
      have hh := contact_patch_sqrt_crowding hδ hD hs hℓ.le
        (by positivity : 0 ≤ (2 * contactCrowding δ D s : ℝ))
        (by norm_num : (0 : ℝ) ≤ 6000000000) (by nlinarith : ℓ * s ≤ δ)
        (by nlinarith [hcrowd.2.2] : (2 * contactCrowding δ D s : ℝ) * δ * D ≤ 6000000000 * s ^ 2)
      apply hh.trans
      gcongr
      norm_num [Real.sqrt_le_iff]
    apply harea.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ 18000000000 * δ * ℓ * (16 * F *
          Real.sqrt (2 * contactCrowding δ D s) * N * Real.sqrt N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        convert hcount using 1 <;> dsimp [F, N] <;> ring
      _ = 288000000000 * F * (δ * ℓ * Real.sqrt (2 * contactCrowding δ D s)) *
          N * Real.sqrt N := by ring
      _ ≤ 288000000000 * F * (80000 * δ * Real.sqrt (δ / D)) * N * Real.sqrt N := by
        gcongr
      _ ≤ _ := by
        have hc : (288000000000 : ℝ) * 80000 ≤ 30000000000000000 := by norm_num
        calc
          _ = (288000000000 * 80000) * F * δ * Real.sqrt (δ / D) * N * Real.sqrt N := by ring
          _ ≤ _ := by gcongr

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
