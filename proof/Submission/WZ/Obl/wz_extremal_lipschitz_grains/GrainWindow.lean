-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GrainWindow.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GrainChain

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- **Grain window bound**: if every point `q` of `E''` carries a grain `G q ⊆ E1` of volume at
least `m` inside `closedBall q A0` and the `u`-slab of half-width `h'` through `q`, and `E1` has
volume at most `U` in every closed ball of radius `r`, then the `u`-projection of `E''` near `p`
meets every window of length `R` in a set covered by an explicit number of `ρ0`-balls. -/
theorem grain_window_bound {u : Space} (hu : ‖u‖ = 1) {p : Space} {E1 E'' : Set Space}
    {G : Space → Set Space} {A0 h' m r U ρ0 R a rad : ℝ}
    (hρ0 : 0 < ρ0) (hh' : 0 < h') (hm : 0 < m) (hr : 0 < r) (hU : 0 ≤ U) (hA0 : 0 ≤ A0)
    (hR : 0 ≤ R) (hrad : 0 ≤ rad)
    (hGm : ∀ q ∈ E'', MeasurableSet (G q))
    (hGv : ∀ q ∈ E'', ENNReal.ofReal m ≤ volume (G q))
    (hGsub : ∀ q ∈ E'', G q ⊆ E1 ∩ closedBall q A0 ∩ {y | |inner ℝ u y - inner ℝ u q| ≤ h'})
    (hcube : ∀ c, volume (E1 ∩ closedBall c r) ≤ ENNReal.ofReal U) :
    ∃ (N : ℕ) (c : Fin N → ℝ),
      ((fun q => inner ℝ u q) '' (E'' ∩ ball p rad)) ∩ Icc a (a + R) ⊆
        ⋃ j, closedBall (c j) ρ0 ∧
      (N : ℝ) ≤ (8 * (2 * (rad + A0 + r)) ^ 2 * (R + 2 * h' + 2 * r) / r ^ 3 * U) / m *
        (2 * h' / ρ0 + 2) := by
  classical
  set P := ((fun q => inner ℝ u q) '' (E'' ∩ ball p rad)) ∩ Icc a (a + R) with hP
  have hPb : Bornology.IsBounded P := (Metric.isBounded_Icc a (a + R)).subset inter_subset_right
  have hwit : ∀ t ∈ P, ∃ q, q ∈ E'' ∩ ball p rad ∧ inner ℝ u q = t := by
    intro t ht
    obtain ⟨q, hq, hqt⟩ := ht.1
    exact ⟨q, hq, hqt⟩
  let qq : ℝ → Space := fun t => if h : t ∈ P then Classical.choose (hwit t h) else p
  have hqq : ∀ t ∈ P, qq t ∈ E'' ∩ ball p rad ∧ inner ℝ u (qq t) = t := by
    intro t ht
    simp only [qq, dif_pos ht]
    exact Classical.choose_spec (hwit t ht)
  set Ω := E1 ∩ (closedBall p (rad + A0) ∩ {y | inner ℝ u y ∈ Icc (a - h') (a + R + h')})
    with hΩ
  have hGΩ : ∀ t ∈ P, G (qq t) ⊆ Ω := by
    intro t ht y hy
    obtain ⟨⟨hqE, hqB⟩, hqt⟩ := hqq t ht
    obtain ⟨⟨hyE, hyq⟩, hyh⟩ := hGsub _ hqE hy
    refine ⟨hyE, ?_, ?_⟩
    · rw [mem_closedBall]
      calc dist y p ≤ dist y (qq t) + dist (qq t) p := dist_triangle _ _ _
        _ ≤ A0 + rad := add_le_add (mem_closedBall.1 hyq) (mem_ball.1 hqB).le
        _ = rad + A0 := by ring
    · simp only [mem_setOf_eq, mem_Icc] at hyh ⊢
      rw [hqt, abs_le] at hyh
      have := ht.2
      simp only [mem_Icc] at this
      constructor <;> linarith
  have hΩv := volume_window_le hu p (A := rad + A0) (α := a - h') (β := a + R + h')
    (r := r) (by linarith) (by linarith) hr (E := E1) hcube hU
  have e : a + R + h' - (a - h') + 2 * r = R + 2 * h' + 2 * r := by ring
  rw [e, show rad + A0 + r = rad + A0 + r from rfl] at hΩv
  obtain ⟨N, c, hcov, hN⟩ := window_count (G := fun t => G (qq t)) (Ω := Ω) hPb hh' hρ0 hm
    (by positivity) (fun t ht => hGm _ (hqq t ht).1.1) (fun t ht => hGv _ (hqq t ht).1.1)
    hGΩ hΩv (by
      intro t ht t' ht' hd
      rw [Set.disjoint_left]
      intro y hy hy'
      obtain ⟨⟨-, -⟩, h1⟩ := hGsub _ (hqq t ht).1.1 hy
      obtain ⟨⟨-, -⟩, h2⟩ := hGsub _ (hqq t' ht').1.1 hy'
      simp only [mem_setOf_eq] at h1 h2
      rw [(hqq t ht).2] at h1
      rw [(hqq t' ht').2] at h2
      rw [Real.dist_eq] at hd
      have : |t - t'| ≤ 2 * h' := by
        calc |t - t'| = |(inner ℝ u y - t') - (inner ℝ u y - t)| := by ring_nf
          _ ≤ |inner ℝ u y - t'| + |inner ℝ u y - t| := abs_sub _ _
          _ ≤ h' + h' := add_le_add h2 h1
          _ = 2 * h' := by ring
      linarith)
  exact ⟨N, c, hcov, hN⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- **Plane precision of coarse tubes**: a coarse grid cube reached by the contracted shading of a
fine tube of its fibre inherits the plane map through the fine point, up to the Lipschitz
displacement. -/
theorem coarse_plane_precision {n : ℕ} {v : Fin n → Space} {Y' : Fin n → Set Space}
    {wj : Space} {s ρc lam δ L : ℝ} {V : Space → Space} {E : Set Space}
    (hs : 0 < s) (hL : 0 ≤ L) (hv : ∀ i, ‖v i‖ = 1)
    (hVu : ∀ p ∈ E, ‖V p‖ = 1) (hVL : ∀ p ∈ E, ∀ q ∈ E, dist (V p) (V q) ≤ L * dist p q)
    (hY'E : ∀ i, Y' i ⊆ E) (hVp : ∀ i p, p ∈ Y' i → |inner ℝ (v i) (V p)| ≤ δ)
    (hball : ∀ i, ∀ p ∈ Y' i, ‖p‖ ≤ 1) (hlam : |1 - lam| ≤ 4 * ρc)
    {m : Fin 3 → ℤ} {i : Fin n} {p' : Space} (hp' : p' ∈ Y' i) (hm : lam • p' ∈ gridCube s m)
    (hdir : min ‖v i - wj‖ ‖v i + wj‖ ≤ ρc / 2) {p y : Space} (hp : p ∈ E)
    (hy : y ∈ gridCube s m) :
    |inner ℝ wj (V p)| ≤ ρc / 2 + δ + L * (dist p y + 2 * s + 4 * ρc) := by
  have hp'E : p' ∈ E := hY'E i hp'
  have hdist : dist p p' ≤ dist p y + 2 * s + 4 * ρc := by
    have h1 : dist y (lam • p') < 2 * s := diam_le_of_mem_gridCube hs hy hm
    have h2 : dist (lam • p') p' ≤ 4 * ρc := by
      rw [dist_eq_norm, show lam • p' - p' = (lam - 1) • p' by rw [sub_smul, one_smul],
        norm_smul, Real.norm_eq_abs, abs_sub_comm]
      calc |1 - lam| * ‖p'‖ ≤ 4 * ρc * 1 :=
            mul_le_mul hlam (hball i p' hp') (norm_nonneg _) (by
              have := abs_nonneg (1 - lam); linarith)
        _ = 4 * ρc := mul_one _
    calc dist p p' ≤ dist p y + dist y (lam • p') + dist (lam • p') p' := dist_triangle4 _ _ _ _
      _ ≤ dist p y + 2 * s + 4 * ρc := by linarith
  have hVpp : ‖V p - V p'‖ ≤ L * (dist p y + 2 * s + 4 * ρc) := by
    rw [← dist_eq_norm]
    exact (hVL p hp p' hp'E).trans (mul_le_mul_of_nonneg_left hdist hL)
  have hvi : |inner ℝ (v i) (V p)| ≤ δ + L * (dist p y + 2 * s + 4 * ρc) := by
    have e : inner ℝ (v i) (V p) = inner ℝ (v i) (V p') + inner ℝ (v i) (V p - V p') := by
      rw [inner_sub_right]; ring
    rw [e]
    have h1 : |inner ℝ (v i) (V p - V p')| ≤ L * (dist p y + 2 * s + 4 * ρc) := by
      calc |inner ℝ (v i) (V p - V p')| ≤ ‖v i‖ * ‖V p - V p'‖ := abs_real_inner_le_norm _ _
        _ ≤ L * (dist p y + 2 * s + 4 * ρc) := by rw [hv i, one_mul]; exact hVpp
    calc |inner ℝ (v i) (V p') + inner ℝ (v i) (V p - V p')|
        ≤ |inner ℝ (v i) (V p')| + |inner ℝ (v i) (V p - V p')| := abs_add_le _ _
      _ ≤ δ + L * (dist p y + 2 * s + 4 * ρc) := add_le_add (hVp i p' hp') h1
  have hVpn : ‖V p‖ = 1 := hVu p hp
  rcases min_le_iff.1 hdir with hd | hd
  · have e : inner ℝ wj (V p) = inner ℝ (v i) (V p) - inner ℝ (v i - wj) (V p) := by
      rw [inner_sub_left]; ring
    rw [e]
    have h2 : |inner ℝ (v i - wj) (V p)| ≤ ρc / 2 := by
      calc |inner ℝ (v i - wj) (V p)| ≤ ‖v i - wj‖ * ‖V p‖ := abs_real_inner_le_norm _ _
        _ ≤ ρc / 2 := by rw [hVpn, mul_one]; exact hd
    calc |inner ℝ (v i) (V p) - inner ℝ (v i - wj) (V p)|
        ≤ |inner ℝ (v i) (V p)| + |inner ℝ (v i - wj) (V p)| := abs_sub _ _
      _ ≤ ρc / 2 + δ + L * (dist p y + 2 * s + 4 * ρc) := by linarith
  · have e : inner ℝ wj (V p) = inner ℝ (v i + wj) (V p) - inner ℝ (v i) (V p) := by
      rw [inner_add_left]; ring
    rw [e]
    have h2 : |inner ℝ (v i + wj) (V p)| ≤ ρc / 2 := by
      calc |inner ℝ (v i + wj) (V p)| ≤ ‖v i + wj‖ * ‖V p‖ := abs_real_inner_le_norm _ _
        _ ≤ ρc / 2 := by rw [hVpn, mul_one]; exact hd
    calc |inner ℝ (v i + wj) (V p) - inner ℝ (v i) (V p)|
        ≤ |inner ℝ (v i + wj) (V p)| + |inner ℝ (v i) (V p)| := abs_sub _ _
      _ ≤ ρc / 2 + δ + L * (dist p y + 2 * s + 4 * ρc) := by linarith

/-- **Fine multiplicity upper bound** from a two-scale decomposition: every fine tube through `p`
lies in the fibre of a coarse tube through `λ p`. -/
theorem fineMult_le_of_fibres {n k : ℕ} {Y' : Fin n → Set Space} {Yt : Fin k → Set Space}
    {a : Fin n → Fin k} {lam B : ℝ} (hcontr : ∀ i, lam • Y' i ⊆ Yt (a i))
    (hfib : ∀ j p, ({i | a i = j ∧ p ∈ Y' i}.ncard : ℝ) ≤ B) (p : Space) :
    (fineMult Y' p : ℝ) ≤ (fineMult Yt (lam • p) : ℝ) * B := by
  classical
  set J := Finset.univ.filter fun j => lam • p ∈ Yt j with hJ
  have hsub : (Finset.univ.filter fun i => p ∈ Y' i) ⊆
      J.biUnion fun j => Finset.univ.filter fun i => a i = j ∧ p ∈ Y' i := by
    intro i hi
    rw [Finset.mem_filter] at hi
    refine Finset.mem_biUnion.2 ⟨a i, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, hi.2⟩⟩
    exact hcontr i ⟨p, hi.2, rfl⟩
  have h1 : (fineMult Y' p : ℝ) = ((Finset.univ.filter fun i => p ∈ Y' i).card : ℝ) := by
    rw [fineMult, ← Set.ncard_coe_finset]; congr 2; ext; simp
  have h2 : (fineMult Yt (lam • p) : ℝ) = (J.card : ℝ) := by
    rw [fineMult, hJ, ← Set.ncard_coe_finset]; congr 2; ext; simp
  rw [h1, h2]
  calc ((Finset.univ.filter fun i => p ∈ Y' i).card : ℝ)
      ≤ ((J.biUnion fun j => Finset.univ.filter fun i => a i = j ∧ p ∈ Y' i).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ j ∈ J, ((Finset.univ.filter fun i => a i = j ∧ p ∈ Y' i).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ J, B := by
        apply Finset.sum_le_sum
        intro j _
        have h := hfib j p
        have e : {i | a i = j ∧ p ∈ Y' i} =
            ↑(Finset.univ.filter fun i => a i = j ∧ p ∈ Y' i) := by ext; simp
        rwa [e, Set.ncard_coe_finset] at h
    _ = (J.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
