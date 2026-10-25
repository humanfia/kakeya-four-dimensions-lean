-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GrainStructure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GrainWindow

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

open Classical in
/-- **Grain structure at one scale** (structural form of sticky Lemmas 4.9-4.11).  From a
two-scale decomposition `(Y1, M)` with balanced cover and a cone-bounded refinement `Z` of the
coarse family, the fine shadings restricted to the contracted preimage of the twice-dense
trimmed cubes have an explicit mass, and their plane-map projections have explicitly bounded
covering numbers in every window, given any cube bound for the fine set. -/
theorem grain_structure {n k : ℕ} {x v : Fin n → Space} {Y Y1 : Fin n → Set Space}
    {V : Space → Space} {δ L ρc s θb μF μmax β B1 c θ μ2 D : ℝ} {N : ℕ} (hδ : 0 ≤ δ)
    (hv : ∀ i, ‖v i‖ = 1) (hY1m : ∀ i, MeasurableSet (Y1 i)) (hY1Y : ∀ i, Y1 i ⊆ Y i)
    (hYball : ∀ i, ∀ p ∈ Y i, ‖p‖ ≤ 1)
    (hVu : ∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1) (hVp : ∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ)
    (hVL : ∀ p ∈ ⋃ i, Y i, ∀ q ∈ ⋃ i, Y i, dist (V p) (V q) ≤ L * dist p q) (hL : 0 ≤ L)
    {z w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1) {M : Fin k → Finset (Fin 3 → ℤ)}
    {a : Fin n → Fin k} (hs : 0 < s) (hρc : 0 < ρc) (hρc8 : ρc ≤ 1 / 8)
    (hMT : ∀ j, cubeSet s (M j) ⊆ tube ρc (z j) (w j))
    (hcontr : ∀ i, (1 - 4 * ρc) • Y1 i ⊆ cubeSet s (M (a i)))
    (hdir : ∀ i, (Y1 i).Nonempty → min ‖v i - w (a i)‖ ‖v i + w (a i)‖ ≤ ρc / 2)
    (hR1 : ∀ j, ∀ m ∈ M j, ∃ i, a i = j ∧ ∃ p ∈ Y1 i, (1 - 4 * ρc) • p ∈ gridCube s m)
    (hθb : 0 < θb)
    (hbal : ∀ j, ∀ m ∈ M j, ENNReal.ofReal θb * volume (gridCube s m) ≤
      volume ((⋃ i, (1 - 4 * ρc) • Y1 i) ∩ gridCube s m))
    (hμF : ∀ p ∈ ⋃ i, Y1 i, μF ≤ (fineMult Y1 p : ℝ)) (hμF0 : 0 ≤ μF)
    (hμmax : ∀ m, (cubeLabels M m : ℝ) ≤ μmax) (hμ : 0 < μmax)
    {Z : Fin k → Set Space} (hZm : ∀ j, MeasurableSet (Z j)) (hZM : ∀ j, Z j ⊆ cubeSet s (M j))
    (hcone : ∀ (x u : Space), ‖u‖ = 1 → ((Finset.univ.filter fun j =>
      x ∈ Z j ∧ min ‖w j - u‖ ‖w j + u‖ ≤ β).card : ℝ) ≤ B1)
    (hc : 0 < c) (hθ : 0 < θ) (hμ2 : 0 < μ2) (hB1 : B1 / c ≤ μ2 / 2)
    (hN : 0 < N) (hNs : ρc ≤ (N : ℝ) * s) (h3 : 3 * ((N : ℝ) * s) ≤ 1)
    (hD : 0 < D) (h4D : 4 * ρc ≤ D) (hβD : 16 * ρc / D < β) :
    ∃ Y'' : Fin n → Set Space, (∀ i, Y'' i ⊆ Y1 i) ∧ (∀ i, MeasurableSet (Y'' i)) ∧
      ENNReal.ofReal (μF * θb * ((∑ j, (volume (Z j)).toReal) -
          c * (∑ j, ((M j).card : ℝ)) * s ^ 3 -
          2 * θ * (k : ℝ) * (3456 / ((N : ℝ) * s)) * s ^ 3 -
          μ2 * ((Finset.univ.biUnion M).card : ℝ) * s ^ 3) / μmax) ≤ ∑ i, volume (Y'' i) ∧
      ∀ p ∈ ⋃ i, Y'' i, ∀ (aw R r U ρ0 rad : ℝ), 0 < r → 0 ≤ U → 0 < ρ0 → 0 ≤ R → 0 ≤ rad →
        (∀ cc, volume ((⋃ i, Y1 i) ∩ closedBall cc r) ≤ ENNReal.ofReal U) →
        ∃ (Nn : ℕ) (cs : Fin Nn → ℝ),
          ((fun q => inner ℝ (V p) q) '' ((⋃ i, Y'' i) ∩ ball p rad)) ∩ Icc aw (aw + R) ⊆
            ⋃ j, closedBall (cs j) ρ0 ∧
          (Nn : ℝ) ≤ (8 * (2 * (rad + 2 * ((N : ℝ) * s) / (1 - 4 * ρc) + r)) ^ 2 *
              (R + 2 * ((2 * ((2 * ((N : ℝ) * s) + 2 * ρc) *
                (ρc / 2 + δ + L * (rad + 4 * ρc + 2 * ((N : ℝ) * s) + 2 * s + 4 * ρc)) +
                2 * ρc) + 2 * s) / (1 - 4 * ρc)) + 2 * r) / r ^ 3 * U) /
            (θb * ((θ * s ^ 3) ^ 2 * μ2 / (256 * (4 * (D + ρc) + ρc) * ρc ^ 2 * μmax))) *
            (2 * ((2 * ((2 * ((N : ℝ) * s) + 2 * ρc) *
                (ρc / 2 + δ + L * (rad + 4 * ρc + 2 * ((N : ℝ) * s) + 2 * s + 4 * ρc)) +
                2 * ρc) + 2 * s) / (1 - 4 * ρc)) / ρ0 + 2) := by
  obtain ⟨M1, M2, M3, hM32, hM21, hM1M, hcone2, hlo3, hP1, hP3, hcount⟩ :=
    coarse_fan_data hs hN hw M hMT hNs h3 hZm hZM hc hθ.le hμ2.le hcone
  set lam := 1 - 4 * ρc with hlam
  have hlam0 : 0 < lam := by rw [hlam]; linarith
  have hlam1 : lam ≤ 1 := by rw [hlam]; linarith
  have hlamne : lam ≠ 0 := hlam0.ne'
  set ω := (N : ℝ) * s with hω
  have hω0 : 0 < ω := mul_pos (by exact_mod_cast hN) hs
  set C3 := ⋃ j, cubeSet s (M3 j) with hC3
  have hC3m : MeasurableSet C3 := MeasurableSet.iUnion fun j => measurableSet_cubeSet s _
  set Y'' : Fin n → Set Space := fun i => Y1 i ∩ lam⁻¹ • C3 with hY''
  have hE1m : MeasurableSet (⋃ i, Y1 i) := MeasurableSet.iUnion hY1m
  have hlamE : (lam • ⋃ i, Y1 i) = ⋃ i, lam • Y1 i := Set.smul_set_iUnion _ _
  have hbal' : ∀ j, ∀ m ∈ M j, ENNReal.ofReal θb * volume (gridCube s m) ≤
      volume (lam • (⋃ i, Y1 i) ∩ gridCube s m) := by
    intro j m hm; rw [hlamE]; exact hbal j m hm
  refine ⟨Y'', fun i => inter_subset_left, fun i => (hY1m i).inter (hC3m.const_smul₀ _), ?_, ?_⟩
  · -- mass of the restricted shadings
    set U3 := Finset.univ.biUnion M3 with hU3
    have hC3U : C3 = ⋃ m ∈ U3, gridCube s m := by
      ext y
      simp only [hC3, mem_iUnion, cubeSet, hU3, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, m, hm, hy⟩; exact ⟨m, ⟨j, hm⟩, hy⟩
      · rintro ⟨m, ⟨j, hm⟩, hy⟩; exact ⟨j, m, hm, hy⟩
    have hsum3 : (∑ j, ((M3 j).card : ℝ)) ≤ (U3.card : ℝ) * μmax := by
      have h1 : ∀ j, ((M3 j).card : ℝ) = ∑ m ∈ U3, if m ∈ M3 j then (1 : ℝ) else 0 := by
        intro j
        rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 2
        apply (Finset.inter_eq_right.2 _).symm
        intro m hm
        exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hm⟩
      simp_rw [h1]
      rw [Finset.sum_comm]
      calc ∑ m ∈ U3, ∑ j, (if m ∈ M3 j then (1 : ℝ) else 0) ≤ ∑ _m ∈ U3, μmax := by
            apply Finset.sum_le_sum
            intro m _
            rw [Finset.sum_boole]
            refine le_trans ?_ (hμmax m)
            exact_mod_cast Finset.card_le_card (fun j hj => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
              exact hM1M j (hM21 j (hM32 j hj)))
        _ = (U3.card : ℝ) * μmax := by rw [Finset.sum_const, nsmul_eq_mul]
    have hbalU : ENNReal.ofReal θb * ((U3.card : ℝ≥0∞) * ENNReal.ofReal (s ^ 3)) ≤
        volume (lam • (⋃ i, Y1 i) ∩ C3) := by
      calc ENNReal.ofReal θb * ((U3.card : ℝ≥0∞) * ENNReal.ofReal (s ^ 3))
          = ∑ m ∈ U3, ENNReal.ofReal θb * volume (gridCube s m) := by
            simp only [volume_gridCube hs, Finset.sum_const, nsmul_eq_mul,
              ENNReal.ofReal_pow hs.le]; ring
        _ ≤ ∑ m ∈ U3, volume (lam • (⋃ i, Y1 i) ∩ gridCube s m) := by
            apply Finset.sum_le_sum
            intro m hm
            obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hm
            exact hbal' j m (hM1M j (hM21 j (hM32 j hj)))
        _ = volume (⋃ m ∈ U3, lam • (⋃ i, Y1 i) ∩ gridCube s m) := by
            rw [measure_biUnion_finset]
            · intro m _ m' _ hmm
              exact (gridCube_disjoint hs hmm).mono inter_subset_right inter_subset_right
            · intro m _; exact (hE1m.const_smul₀ lam).inter (measurableSet_gridCube s m)
        _ ≤ volume (lam • (⋃ i, Y1 i) ∩ C3) := by
            apply measure_mono
            intro y hy
            obtain ⟨m, hm, hyE, hyQ⟩ := mem_iUnion₂.1 hy
            exact ⟨hyE, by rw [hC3U]; exact mem_iUnion₂.2 ⟨m, hm, hyQ⟩⟩
    have hscale : volume (lam • (⋃ i, Y1 i) ∩ C3) ≤ volume ((⋃ i, Y1 i) ∩ lam⁻¹ • C3) := by
      have hset : (⋃ i, Y1 i) ∩ lam⁻¹ • C3 = lam⁻¹ • (lam • (⋃ i, Y1 i) ∩ C3) := by
        ext y
        simp only [mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hlamne),
          inv_inv, Set.smul_mem_smul_set_iff₀ hlamne]
      rw [hset, Measure.addHaar_smul]
      have hge : (1 : ℝ≥0∞) ≤ ENNReal.ofReal |lam⁻¹ ^ Module.finrank ℝ Space| := by
        rw [ENNReal.one_le_ofReal, abs_of_nonneg (by positivity)]
        exact one_le_pow₀ ((one_le_inv₀ hlam0).2 hlam1)
      calc volume (lam • (⋃ i, Y1 i) ∩ C3) = 1 * volume (lam • (⋃ i, Y1 i) ∩ C3) :=
            (one_mul _).symm
        _ ≤ _ := by gcongr
    have hmassY'' : ENNReal.ofReal μF * volume ((⋃ i, Y1 i) ∩ lam⁻¹ • C3) ≤
        ∑ i, volume (Y'' i) := by
      have := massMeasure_ge_mul hY1m hμF (hC3m.const_smul₀ lam⁻¹)
      rwa [massMeasure_apply hY1m (hC3m.const_smul₀ lam⁻¹)] at this
    refine le_trans ?_ hmassY''
    calc ENNReal.ofReal (μF * θb * ((∑ j, (volume (Z j)).toReal) -
          c * (∑ j, ((M j).card : ℝ)) * s ^ 3 -
          2 * θ * (k : ℝ) * (3456 / ((N : ℝ) * s)) * s ^ 3 -
          μ2 * ((Finset.univ.biUnion M).card : ℝ) * s ^ 3) / μmax)
        ≤ ENNReal.ofReal (μF * (θb * ((U3.card : ℝ) * s ^ 3))) := by
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_iff₀ hμ]
          have h1 := hcount
          have h2 : (∑ j, ((M3 j).card : ℝ)) * s ^ 3 ≤ (U3.card : ℝ) * μmax * s ^ 3 :=
            mul_le_mul_of_nonneg_right hsum3 (by positivity)
          have hμθ : 0 ≤ μF * θb := mul_nonneg hμF0 hθb.le
          nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hμθ]
      _ = ENNReal.ofReal μF * (ENNReal.ofReal θb * ((U3.card : ℝ≥0∞) * ENNReal.ofReal (s ^ 3))) := by
          rw [ENNReal.ofReal_mul hμF0, ENNReal.ofReal_mul hθb.le,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal μF * volume ((⋃ i, Y1 i) ∩ lam⁻¹ • C3) := by
          gcongr
          exact hbalU.trans hscale
  · -- the window bound
    intro p hp aw R r U ρ0 rad hr hU hρ0 hR hrad hcube
    have hpY : p ∈ ⋃ i, Y i := by
      obtain ⟨i, hi⟩ := mem_iUnion.1 hp
      exact mem_iUnion.2 ⟨i, hY1Y i hi.1⟩
    set u := V p with hu_def
    have hu : ‖u‖ = 1 := hVu p hpY
    set π := ρc / 2 + δ + L * (rad + 4 * ρc + 2 * ω + 2 * s + 4 * ρc) with hπ
    set h := 2 * ((2 * ω + 2 * ρc) * π + 2 * ρc) with hh
    set mf := θb * ((θ * s ^ 3) ^ 2 * μ2 / (256 * (4 * (D + ρc) + ρc) * ρc ^ 2 * μmax)) with hmf
    have hmf0 : 0 < mf := by positivity
    have hYTb : ∀ i, ∀ y ∈ Y1 i, ‖y‖ ≤ 1 := fun i y hy => hYball i y (hY1Y i hy)
    -- the grain of a point
    let G : Space → Set Space := fun q => (⋃ i, Y1 i) ∩ lam⁻¹ •
      (gridCube ω (blockOf N (cubeIndex s (lam • q))) ∩
        {y | |inner ℝ u (y - lam • q)| ≤ h + 2 * s})
    have hπ0 : 0 ≤ π := by positivity
    have hh0 : 0 < h + 2 * s := by positivity
    obtain ⟨Nn, cs, hcov, hNn⟩ := grain_window_bound (u := u) (p := p) (E1 := ⋃ i, Y1 i)
      (E'' := (⋃ i, Y'' i) ∩ ball p rad) (G := G) (A0 := 2 * ω / lam)
      (h' := (h + 2 * s) / lam) (m := mf) (r := r) (U := U) (ρ0 := ρ0) (R := R) (a := aw)
      (rad := rad) hu hρ0 (by positivity) hmf0 hr hU (by positivity) hR hrad
      (fun q _ => hE1m.inter (((measurableSet_gridCube ω _).inter
        (isClosed_le (continuous_abs.comp ((continuous_const.inner (continuous_id.sub
          continuous_const)))) continuous_const).measurableSet).const_smul₀ _))
      (by
        rintro q ⟨hqY'', hqp⟩
        obtain ⟨i0, hi0⟩ := mem_iUnion.1 hqY''
        have hq3 : lam • q ∈ C3 := by
          have := hi0.2
          rwa [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hlamne), inv_inv] at this
        obtain ⟨j0, hj0⟩ := mem_iUnion.1 hq3
        refine fine_grain_volume hs hN (r := ρc) (D := D) (β := β) (π := π) (μlo := μ2)
          (μmax := μmax) (θ := θ) (θb := θb) (lam := lam) hw hMT hM32 hM21 hM1M hρc hD h4D hβD
          hμmax hμ (fun m u' hu' => (hcone2 m u' hu').trans hB1) hlo3 hP1 hP3 hθ.le hθb.le hlam0 hlam1
          hE1m hbal' hj0 hu ?_
        -- plane precision on the block of `λ q`
        rintro j ⟨y, hyC, hyW⟩
        obtain ⟨m, hm, hym⟩ := mem_iUnion₂.1 hyC
        obtain ⟨i, hai, p', hp'Y, hp'm⟩ := hR1 j m (hM1M j hm)
        have hdir' := hdir i ⟨p', hp'Y⟩
        rw [hai] at hdir'
        have hq1 : q ∈ ⋃ i, Y1 i := mem_iUnion.2 ⟨i0, hi0.1⟩
        have hdpy : dist p y ≤ rad + 4 * ρc + 2 * ω := by
          have h1 : dist p q < rad := by rw [dist_comm]; exact mem_ball.1 hqp
          have h2 : dist q (lam • q) ≤ 4 * ρc := by
            have e : q - lam • q = (1 - lam) • q := by rw [sub_smul (1 : ℝ) lam q, one_smul]
            rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs]
            obtain ⟨i1, hi1⟩ := mem_iUnion.1 hq1
            have hn := hYTb i1 q hi1
            rw [hlam, show 1 - (1 - 4 * ρc) = 4 * ρc by ring, abs_of_pos (by positivity)]
            calc 4 * ρc * ‖q‖ ≤ 4 * ρc * 1 := mul_le_mul_of_nonneg_left hn (by positivity)
              _ = 4 * ρc := mul_one _
          have h3 : dist (lam • q) y ≤ 2 * ω := by
            have hb := gridCube_subset_block hs hN _ (mem_gridCube_cubeIndex hs (lam • q))
            exact dist_lt_of_mem_block hω0 hb hyW
          calc dist p y ≤ dist p q + dist q (lam • q) + dist (lam • q) y := dist_triangle4 _ _ _ _
            _ ≤ rad + 4 * ρc + 2 * ω := by linarith
        have hprec := coarse_plane_precision (v := v) (Y' := Y1) (wj := w j) (s := s) (ρc := ρc)
          (lam := lam) (δ := δ) (L := L) (V := V) (E := ⋃ i, Y i) hs hL hv hVu hVL
          (fun i => (hY1Y i).trans (subset_iUnion Y i)) (fun i p hp => hVp i p (hY1Y i hp))
          hYTb (by rw [hlam]; rw [show 1 - (1 - 4 * ρc) = 4 * ρc by ring,
            abs_of_pos (by positivity)]) hp'Y hp'm hdir' hpY hym
        calc |inner ℝ (w j) u| ≤ ρc / 2 + δ + L * (dist p y + 2 * s + 4 * ρc) := hprec
          _ ≤ π := by
              rw [hπ]
              have := mul_le_mul_of_nonneg_left (show dist p y + 2 * s + 4 * ρc ≤
                rad + 4 * ρc + 2 * ω + 2 * s + 4 * ρc by linarith) hL
              linarith)
      (by
        rintro q ⟨hqY'', hqp⟩ y ⟨hyE, hyS⟩
        rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hlamne), inv_inv] at hyS
        obtain ⟨hyW, hyh⟩ := hyS
        have hqW := gridCube_subset_block hs hN _ (mem_gridCube_cubeIndex hs (lam • q))
        refine ⟨⟨hyE, ?_⟩, ?_⟩
        · rw [mem_closedBall]
          have h1 := dist_lt_of_mem_block hω0 hyW hqW
          rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hlam0] at h1
          rw [le_div_iff₀ hlam0, mul_comm]; exact h1
        · simp only [mem_setOf_eq] at hyh ⊢
          rw [← smul_sub, inner_smul_right, abs_mul, abs_of_pos hlam0] at hyh
          rw [← inner_sub_right, le_div_iff₀ hlam0, mul_comm]
          exact hyh)
      hcube
    refine ⟨Nn, cs, ?_, ?_⟩
    · intro t ht
      apply hcov
      obtain ⟨⟨q, hq, rfl⟩, hta⟩ := ht
      exact ⟨⟨q, ⟨hq, hq.2⟩, rfl⟩, hta⟩
    · convert hNn using 3

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
