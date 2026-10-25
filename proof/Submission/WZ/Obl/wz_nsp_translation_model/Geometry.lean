-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_translation_model.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_nsp_translation_model

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal NNReal

abbrev Tube (r : ℝ) (x v : Space) : Set Space :=
  thickening r (segment ℝ x (x + v))

lemma finite_net {r ρ : ℝ} (hr : 0 < r) (hρ : 0 ≤ ρ) :
    ∃ (m : ℕ) (t : Fin m → Space), 0 < m ∧
      (∀ s, ‖t s‖ ≤ ρ) ∧
      (∀ s s', s ≠ s' → r < dist (t s) (t s')) ∧
      (ball (0 : Space) ρ ⊆ ⋃ s, ball (t s) (2 * r)) := by
  classical
  let ε : ℝ≥0 := ⟨r, hr.le⟩
  have hε : 0 < ε := hr
  let A : Set Space := closedBall 0 ρ
  obtain ⟨C, hCA, hCf, hCc⟩ := exists_finite_isCover_of_isCompact
    (ε := ε / 2) (by positivity) (isCompact_closedBall (0 : Space) ρ)
  have hp : packingNumber ε A ≠ ⊤ := by
    have hh := (packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A).trans
      hCc.externalCoveringNumber_le_encard
    have he : 2 * (ε / 2) = ε := by ring
    rw [he] at hh
    exact ne_of_lt (hh.trans_lt hCf.encard_lt_top)
  let S := maximalSeparatedSet ε A
  have hSA : S ⊆ A := maximalSeparatedSet_subset
  have hSf : S.Finite := encard_ne_top_iff.mp (by rw [encard_maximalSeparatedSet hp]; exact hp)
  have hSc : IsCover ε A S := isCover_maximalSeparatedSet hp
  have hSs : IsSeparated ε S := isSeparated_maximalSeparatedSet
  have hSne : S.Nonempty := hSc.nonempty ⟨0, mem_closedBall_self hρ⟩
  let := hSf.fintype
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun s => (e s).val, Fintype.card_pos_iff.mpr hSne.to_subtype, ?_, ?_, ?_⟩
  · intro s
    exact mem_closedBall_zero_iff.mp (hSA (e s).property)
  · intro s s' hss
    have hh := hSs (e s).property (e s').property
      (fun h => hss (e.injective (Subtype.ext h)))
    change (ε : ℝ≥0∞) < edist _ _ at hh
    rw [edist_nndist] at hh
    have hh' := ENNReal.coe_lt_coe.mp hh
    exact_mod_cast hh'
  · intro p hp
    obtain ⟨q, hqS, hpq⟩ := hSc (ball_subset_closedBall hp)
    refine mem_iUnion.mpr ⟨e.symm ⟨q, hqS⟩, ?_⟩
    have hd : dist p q ≤ r := by exact_mod_cast hpq
    simpa using hd.trans_lt (by linarith : r < 2 * r)

lemma ball_volume_lower {r : ℝ} (hr : 0 ≤ r) (p : Space) :
    r ^ 3 ≤ volume.real (ball p r) := by
  rw [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity)]
  nlinarith [Real.pi_gt_three, pow_nonneg hr 3]

lemma ball_volume_upper {r : ℝ} (hr : 0 ≤ r) (p : Space) :
    volume.real (ball p r) ≤ 16 * r ^ 3 := by
  rw [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity)]
  nlinarith [Real.pi_lt_four, pow_nonneg hr 3]

lemma net_card_lower {r ρ : ℝ} (hr : 0 < r) (hρ : 0 ≤ ρ)
    {m : ℕ} (t : Fin m → Space)
    (hcover : ball (0 : Space) ρ ⊆ ⋃ s, ball (t s) (2 * r)) :
    ρ ^ 3 ≤ 128 * (m : ℝ) * r ^ 3 := by
  calc
    ρ ^ 3 ≤ volume.real (ball (0 : Space) ρ) := ball_volume_lower hρ _
    _ ≤ volume.real (⋃ s, ball (t s) (2 * r)) := measureReal_mono hcover (by
      apply ne_of_lt
      exact (measure_iUnion_le _).trans_lt (by
        rw [tsum_fintype]
        exact ENNReal.sum_lt_top.mpr (fun _ _ => measure_ball_lt_top)))
    _ ≤ ∑ s, volume.real (ball (t s) (2 * r)) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _s : Fin m, 16 * (2 * r) ^ 3 :=
      Finset.sum_le_sum (fun _ _ => ball_volume_upper (by positivity) _)
    _ = 128 * (m : ℝ) * r ^ 3 := by simp; ring

lemma longitudinal_grid {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Q : ℕ, 0 < Q ∧ 1 ≤ (Q : ℝ) * (4 * ρ) ∧
      ∀ j : Fin Q, 0 ≤ 4 * ρ * (j : ℝ) ∧ 4 * ρ * (j : ℝ) ≤ 1 := by
  let q := ⌊(4 * ρ)⁻¹⌋₊
  have h4 : 0 < 4 * ρ := by positivity
  have hf : (q : ℝ) ≤ (4 * ρ)⁻¹ := Nat.floor_le (by positivity)
  have hq : (4 * ρ)⁻¹ < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨q + 1, by omega, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_right hq.le h4.le
    rw [inv_mul_cancel₀ h4.ne'] at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  · intro j
    refine ⟨by positivity, ?_⟩
    have hj : (j : ℝ) ≤ q := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
    calc
      4 * ρ * (j : ℝ) ≤ (4 * ρ) * (4 * ρ)⁻¹ := by gcongr; exact hj.trans hf
      _ = 1 := mul_inv_cancel₀ h4.ne'

lemma nat_abs_sub_ge_one {j l : ℕ} (h : j ≠ l) : 1 ≤ |(j : ℝ) - l| := by
  rcases lt_or_gt_of_ne h with hjl | hlj
  · have hh : (j : ℝ) + 1 ≤ l := by exact_mod_cast hjl
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hh : (l : ℝ) + 1 ≤ j := by exact_mod_cast hlj
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma grid_center_separation {r ρ : ℝ} (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    {m Q : ℕ} (t : Fin m → Space) (ht : ∀ s, ‖t s‖ ≤ ρ)
    (hsep : ∀ s s', s ≠ s' → r < dist (t s) (t s'))
    (x v : Space) (hv : ‖v‖ = 1)
    {j l : Fin Q} {s s' : Fin m} (hne : (j, s) ≠ (l, s')) :
    r ≤ dist (x + t s + (4 * ρ * (j : ℝ)) • v)
      (x + t s' + (4 * ρ * (l : ℝ)) • v) := by
  by_cases hj : j = l
  · subst l
    have hs : s ≠ s' := fun h => hne (Prod.ext rfl h)
    simpa only [dist_add_right, dist_add_left] using (hsep s s' hs).le
  · have habs := nat_abs_sub_ge_one (Fin.val_injective.ne hj)
    have hlong : 4 * ρ ≤ dist ((4 * ρ * (j : ℝ)) • v) ((4 * ρ * (l : ℝ)) • v) := by
      rw [dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.norm_eq_abs,
        ← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * ρ)]
      nlinarith
    have htri := dist_triangle4 ((4 * ρ * (j : ℝ)) • v)
      (t s + (4 * ρ * (j : ℝ)) • v)
      (t s' + (4 * ρ * (l : ℝ)) • v) ((4 * ρ * (l : ℝ)) • v)
    have he : dist (x + t s + (4 * ρ * (j : ℝ)) • v)
        (x + t s' + (4 * ρ * (l : ℝ)) • v) =
        dist (t s + (4 * ρ * (j : ℝ)) • v) (t s' + (4 * ρ * (l : ℝ)) • v) := by
      rw [add_assoc, add_assoc, dist_add_left]
    rw [he]
    have hts := ht s
    have hts' := ht s'
    have he1 : dist ((4 * ρ * (j : ℝ)) • v) (t s + (4 * ρ * (j : ℝ)) • v) = ‖t s‖ := by
      rw [dist_comm, dist_add_self_left]
    rw [he1, dist_add_self_left] at htri
    linarith

lemma successful_translations_bound {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ)
    {m : ℕ} (t : Fin m → Space) (ht : ∀ s, ‖t s‖ ≤ ρ)
    (hsep : ∀ s s', s ≠ s' → r < dist (t s) (t s'))
    (hcover : ball (0 : Space) ρ ⊆ ⋃ s, ball (t s) (2 * r))
    (x v : Space) (hv : ‖v‖ = 1) (W : Set Space) (hW : volume W ≠ ⊤) :
    (ncard {s : Fin m | Tube r (x + t s) v ⊆ W} : ℝ) * ρ ^ 2 ≤
      4096 * (m : ℝ) * volume.real W := by
  classical
  have hρ : 0 < ρ := hr.trans_le hrρ
  obtain ⟨Q, hQ, hQρ, hparam⟩ := longitudinal_grid hρ
  let F : Finset (Fin m) := Finset.univ.filter (fun s => Tube r (x + t s) v ⊆ W)
  let c : Fin Q × F → Space := fun q => x + t q.2 + (4 * ρ * (q.1 : ℝ)) • v
  have hdisj : Pairwise (fun q q' : Fin Q × F =>
      Disjoint (ball (c q) (r / 2)) (ball (c q') (r / 2))) := by
    intro q q' hne
    apply ball_disjoint_ball
    have hh := grid_center_separation hrρ hρ.le t ht hsep x v hv
      (j := q.1) (l := q'.1) (s := q.2) (s' := q'.2) (by
        intro he
        apply hne
        exact Prod.ext (congrArg (fun z : Fin Q × Fin m => z.1) he)
          (Subtype.ext (congrArg (fun z : Fin Q × Fin m => z.2) he)))
    change r / 2 + r / 2 ≤ dist (c q) (c q')
    dsimp [c] at *
    linarith
  have hsub : (⋃ q : Fin Q × F, ball (c q) (r / 2)) ⊆ W := by
    intro p hp
    obtain ⟨q, hp⟩ := mem_iUnion.mp hp
    have hs := (Finset.mem_filter.mp q.2.property).2
    apply hs
    apply mem_thickening_iff.mpr
    refine ⟨c q, ?_, (show dist p (c q) < r / 2 from hp).trans (by linarith)⟩
    rw [segment_eq_image']
    exact ⟨4 * ρ * (q.1 : ℝ), hparam q.1, by simp [c]⟩
  have hpack : (F.card : ℝ) * (Q : ℝ) * (r / 2) ^ 3 ≤ volume.real W := by
    calc
      _ = ∑ _q : Fin Q × F, (r / 2) ^ 3 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_coe, Nat.cast_mul, nsmul_eq_mul]
        ring
      _ ≤ ∑ q : Fin Q × F, volume.real (ball (c q) (r / 2)) :=
        Finset.sum_le_sum (fun _ _ => ball_volume_lower (by positivity) _)
      _ = volume.real (⋃ q : Fin Q × F, ball (c q) (r / 2)) :=
        (measureReal_iUnion_fintype hdisj (fun _ => measurableSet_ball)
          (fun _ => measure_ball_lt_top.ne)).symm
      _ ≤ volume.real W := measureReal_mono hsub hW
  have hstep : (F.card : ℝ) * r ^ 3 ≤ 32 * ρ * volume.real W := by
    have hh := mul_le_mul_of_nonneg_right hQρ (by positivity : 0 ≤ (F.card : ℝ) * r ^ 3)
    have hh' := mul_le_mul_of_nonneg_right hpack (by positivity : 0 ≤ 32 * ρ)
    nlinarith
  have hnet := net_card_lower hr hρ.le t hcover
  have hbound : (F.card : ℝ) * ρ ^ 2 ≤ 4096 * (m : ℝ) * volume.real W := by
    apply (mul_le_mul_iff_right₀ hρ).mp
    calc
      ρ * ((F.card : ℝ) * ρ ^ 2) = (F.card : ℝ) * ρ ^ 3 := by ring
      _ ≤ (F.card : ℝ) * (128 * (m : ℝ) * r ^ 3) := by gcongr
      _ = (128 * (m : ℝ)) * ((F.card : ℝ) * r ^ 3) := by ring
      _ ≤ (128 * (m : ℝ)) * (32 * ρ * volume.real W) := by gcongr
      _ = ρ * (4096 * (m : ℝ) * volume.real W) := by ring
  have hc : F.card = ncard {s : Fin m | Tube r (x + t s) v ⊆ W} := by
    rw [ncard_eq_toFinset_card']
    congr 1
    ext s
    simp [F]
  rwa [hc] at hbound

/-- One finite translation list works simultaneously for every direction and test set. -/
lemma translation_average {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) :
    ∃ (m : ℕ) (t : Fin m → Space), 0 < m ∧ (∀ s, ‖t s‖ ≤ ρ) ∧
      ∀ (x v : Space), ‖v‖ = 1 → ∀ W : Set Space, volume W ≠ ⊤ →
        (ncard {s : Fin m | Tube r (x + t s) v ⊆ W} : ℝ) * ρ ^ 2 ≤
          4096 * (m : ℝ) * volume.real W := by
  obtain ⟨m, t, hm, ht, hsep, hcover⟩ := finite_net hr (hr.le.trans hrρ)
  exact ⟨m, t, hm, ht, fun x v hv W hW =>
    successful_translations_bound hr hrρ t ht hsep hcover x v hv W hW⟩

end WangZahlLot.Obl.wz_nsp_translation_model
