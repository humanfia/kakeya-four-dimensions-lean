import Submission.Obl.k4_scalar_normalized_exact_refinement.ChartObs
import Submission.Obl.k4_crop_angular_finite_tail.Transfer
import Submission.Obl.k4_scalar_crop_profile_transport.LabelTail
import Submission.Obl.k4_scalar_grid_density_extension.GridRelation

/-!
# Density tails of one normalized chart world

Fix one retained chart label: an original world law `μ`, its selected incidence set `C`, and
the normalized law `μq = c • map (normInc t₀ dt θ) (μ|C)`, where `θ` satisfies the literal
normalization identities. With `κ = c * (dt J)` (which is `J / ν(A)` for the Refinement's `c`):

* `world_upper_tail`: `μq {κ 4 θ' < g ∘ obs_s} ≤ 4 c μ(C ∩ {θ' < H ∘ obs_(r+s)})`;
* `world_angular_tail`: the analogue for joint observations, with factor `8`;
* `world_lower_tail`: `μq {g ∘ obs_s < κ ε δ X}` is bounded by `c` times three masses: a
  relabelling loss `2 ε μ C`, the restriction loss `μ(C ∩ {D' < δ H})` and `μ(C ∩ {H < X})`.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis

open MeasureTheory Set
open scoped ENNReal

section Counting

/-- Counting measure on a product of two countable discrete types. -/
lemma count_prod_count {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    (Measure.count : Measure α).prod (Measure.count : Measure β) = Measure.count := by
  apply Measure.ext_of_singleton
  intro q
  rw [Measure.count_singleton, ← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.count_singleton, Measure.count_singleton, one_mul]

lemma map_prodAssoc_jointRef :
    JointRef.map MeasurableEquiv.prodAssoc =
      (volume : Measure (Fin 2 → ℝ)).prod (Measure.count : Measure (ℤ × ℤ)) := by
  unfold JointRef BaseRef
  rw [Measure.prodAssoc_prod, count_prod_count]

/-- Base preserving label maps do not enlarge the joint reference measure. -/
lemma joint_labelImage_cover (g : (Fin 2 → ℝ) × (ℤ × ℤ) → ℤ × ℤ) (hg : Measurable g)
    (G : Joint → Joint)
    (hG : ∀ o : Joint, G o = ((o.1.1, (g (o.1.1, (o.1.2, o.2))).1), (g (o.1.1, (o.1.2, o.2))).2))
    (A : Set Joint) (hA : MeasurableSet A) :
    ∃ M : Set Joint, MeasurableSet M ∧ G '' A ⊆ M ∧ JointRef M ≤ JointRef A := by
  let e : Joint ≃ᵐ (Fin 2 → ℝ) × (ℤ × ℤ) := MeasurableEquiv.prodAssoc
  let A' : Set ((Fin 2 → ℝ) × (ℤ × ℤ)) := e.symm ⁻¹' A
  have hA' : MeasurableSet A' := e.symm.measurable hA
  refine ⟨e ⁻¹' labelImage g A', e.measurable (measurableSet_labelImage hg hA'), ?_, ?_⟩
  · rintro _ ⟨o, ho, rfl⟩
    refine ⟨(o.1.2, o.2), ?_, ?_⟩
    · change e.symm ((e (G o)).1, (o.1.2, o.2)) ∈ A
      rw [hG o]
      exact ho
    · rw [hG o]
      rfl
  · have h1 : JointRef (e ⁻¹' labelImage g A') =
        (volume.prod Measure.count) (labelImage g A') := by
      rw [← Measure.map_apply e.measurable (measurableSet_labelImage hg hA')]
      exact congrArg (fun m : Measure _ => m (labelImage g A')) map_prodAssoc_jointRef
    have h2 : JointRef A = (volume.prod Measure.count) A' := by
      rw [← map_prodAssoc_jointRef, Measure.map_apply e.measurable hA']
      congr 1
    rw [h1, h2]
    exact prod_count_labelImage_le volume hg hA'

end Counting

section World

variable {N r t₀ dt u v J : ℝ} {P : MvPolynomial (Fin 2) ℝ} {θ : Line → Line}

/-- The selected chart restriction has a density under the shifted observation. -/
theorem shift_density_law (hN : 0 < N) (hdt : 0 < dt) (hJ : 0 < J) (hθ : Measurable θ)
    (hy : ∀ l t, Spec.y (θ l) ((t - t₀) / dt) = (Spec.y l t - u - t * v) / J)
    (hx : ∀ l t, Spec.x (θ l) ((t - t₀) / dt) =
      (Spec.x l t - MvPolynomial.eval ![t, Spec.y l t] P) / N ^ (-r))
    {μ μq : Measure Inc} {C : Set Inc} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcT : c ≠ ∞)
    (hμq : μq = c • (μ.restrict C).map (normInc t₀ dt θ))
    (s : ℝ) {g : Base → ℝ≥0∞} (hglaw : μq.map (obs N s) = BaseRef.withDensity g) :
    (μ.restrict C).map (shiftObs (N ^ (-(r + s))) P) =
      BaseRef.withDensity (fun o => c⁻¹ * (ENNReal.ofReal (dt * J))⁻¹ *
        g (baseEquiv t₀ dt u v J hdt.ne' hJ.ne' o)) :=
  k4_crop_angular_finite_tail.map_density_pullback (normInc t₀ dt θ)
    (measurable_normInc t₀ dt hθ) (baseEquiv t₀ dt u v J hdt.ne' hJ.ne')
    (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hdt hJ)) ENNReal.ofReal_ne_top
    (map_baseEquiv t₀ dt u v J hdt hJ) hμq hc0 hcT (measurable_obs N s)
    (measurable_shiftObs _ P) (obs_normInc hN hdt hJ hy hx s) hglaw

/-- The selected chart restriction has a joint density under the shifted joint observation. -/
theorem shift_joint_density_law (hN : 0 < N) (hdt : 0 < dt) (hJ : 0 < J) (hθ : Measurable θ)
    (hy : ∀ l t, Spec.y (θ l) ((t - t₀) / dt) = (Spec.y l t - u - t * v) / J)
    (hx : ∀ l t, Spec.x (θ l) ((t - t₀) / dt) =
      (Spec.x l t - MvPolynomial.eval ![t, Spec.y l t] P) / N ^ (-r))
    {μ μq : Measure Inc} {C : Set Inc} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcT : c ≠ ∞)
    (hμq : μq = c • (μ.restrict C).map (normInc t₀ dt θ))
    (s w : ℝ) {g : Joint → ℝ≥0∞} (hglaw : μq.map (aug N s w) = JointRef.withDensity g) :
    (μ.restrict C).map (fun z => (shiftObs (N ^ (-(r + s))) P z,
        ⌊(dt * (z.1.2 1 - v) / J) / N ^ (-w)⌋)) =
      JointRef.withDensity (fun o => c⁻¹ * (ENNReal.ofReal (dt * J))⁻¹ *
        g (jointEquiv t₀ dt u v J hdt.ne' hJ.ne' o)) :=
  k4_crop_angular_finite_tail.map_density_pullback (normInc t₀ dt θ)
    (measurable_normInc t₀ dt hθ) (jointEquiv t₀ dt u v J hdt.ne' hJ.ne')
    (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hdt hJ)) ENNReal.ofReal_ne_top
    (map_jointEquiv t₀ dt u v J hdt hJ) hμq hc0 hcT (measurable_aug N s w)
    ((measurable_shiftObs _ P).prodMk (by fun_prop)) (aug_normInc hN hdt hJ hy hx s w) hglaw

/-- Normalized masses are original selected masses. -/
lemma normalized_mass (hθ : Measurable θ) {μ μq : Measure Inc} {C : Set Inc} {c : ℝ≥0∞}
    (hμq : μq = c • (μ.restrict C).map (normInc t₀ dt θ)) {Z : Set Inc} (hZ : MeasurableSet Z) :
    μq Z = c * μ (C ∩ normInc t₀ dt θ ⁻¹' Z) := by
  rw [hμq, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_normInc t₀ dt hθ) hZ,
    Measure.restrict_apply ((measurable_normInc t₀ dt hθ) hZ), inter_comm]

lemma mul_lt_mul_iff_left' {κ a b : ℝ≥0∞} (h0 : κ ≠ 0) (hT : κ ≠ ∞) :
    κ * a < κ * b ↔ a < b :=
  ENNReal.mul_lt_mul_iff_right h0 hT

/-- Upper tails of a normalized chart world. -/
theorem world_upper_tail (hN : 0 < N) (hdt : 0 < dt) (hJ : 0 < J) (hθ : Measurable θ)
    (hy : ∀ l t, Spec.y (θ l) ((t - t₀) / dt) = (Spec.y l t - u - t * v) / J)
    (hx : ∀ l t, Spec.x (θ l) ((t - t₀) / dt) =
      (Spec.x l t - MvPolynomial.eval ![t, Spec.y l t] P) / N ^ (-r))
    {μ μq : Measure Inc} [IsFiniteMeasure μ] {C : Set Inc} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcT : c ≠ ∞)
    (hμq : μq = c • (μ.restrict C).map (normInc t₀ dt θ))
    (s : ℝ) {g : Base → ℝ≥0∞} (hg : Measurable g)
    (hglaw : μq.map (obs N s) = BaseRef.withDensity g)
    {H : Base → ℝ≥0∞} (hH : Measurable H) (hHlaw : μ.map (obs N (r + s)) = BaseRef.withDensity H)
    (θ' : ℝ≥0∞) :
    μq {z | c * ENNReal.ofReal (dt * J) * (4 * θ') < g (obs N s z)} ≤
      c * (4 * μ (C ∩ {z | θ' < H (obs N (r + s) z)})) := by
  set sJ : ℝ≥0∞ := ENNReal.ofReal (dt * J) with hsJ
  have hs0 : sJ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hdt hJ)
  have hsT : sJ ≠ ∞ := ENNReal.ofReal_ne_top
  set A := baseEquiv t₀ dt u v J hdt.ne' hJ.ne'
  set κ : ℝ≥0∞ := c⁻¹ * sJ⁻¹ with hκ
  have hκ0 : κ ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.mpr hcT) (ENNReal.inv_ne_zero.mpr hsT)
  have hκT : κ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0) (ENNReal.inv_ne_top.mpr hs0)
  have hκc : κ * (c * sJ) = 1 := by
    rw [hκ, mul_mul_mul_comm, ENNReal.inv_mul_cancel hc0 hcT, ENNReal.inv_mul_cancel hs0 hsT,
      one_mul]
  set D : Base → ℝ≥0∞ := fun o => κ * g (A o) with hDdef
  have hDm : Measurable D := measurable_const.mul (hg.comp A.measurable)
  have hD : (μ.restrict C).map (shiftObs (N ^ (-(r + s))) P) = BaseRef.withDensity D :=
    shift_density_law hN hdt hJ hθ hy hx hc0 hcT hμq s hglaw
  have hmeas : MeasurableSet {z | c * sJ * (4 * θ') < g (obs N s z)} :=
    measurableSet_lt measurable_const (hg.comp (measurable_obs N s))
  rw [normalized_mass hθ hμq hmeas]
  gcongr
  have hset : C ∩ normInc t₀ dt θ ⁻¹' {z | c * sJ * (4 * θ') < g (obs N s z)} =
      C ∩ {z | 4 * θ' < D (shiftObs (N ^ (-(r + s))) P z)} := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, obs_normInc hN hdt hJ hy hx s z]
    apply and_congr_right
    intro _
    rw [hDdef, ← mul_lt_mul_iff_left' hκ0 hκT (a := c * sJ * (4 * θ')), ← mul_assoc,
      hκc, one_mul]
  rw [hset]
  have hcover : ∀ z, ∃ j : Fin 2, obs N (r + s) z =
      unshift (N ^ (-(r + s))) P j (shiftObs (N ^ (-(r + s))) P z) :=
    fun z => obs_eq_unshift P z
  have h := cover_upper_tail BaseRef BaseRef μ (measurable_obs N (r + s))
    (measurable_shiftObs _ P) hH hHlaw C hDm hD (unshift (N ^ (-(r + s))) P) hcover
    (fun j A hA => by
      obtain ⟨M, hM, hAM, hMA⟩ := labelImage_cover (Y := Fin 2 → ℝ) (L₁ := ℤ) (L₂ := ℤ) volume
        (g := fun o : Base => o.2 - ⌊-MvPolynomial.eval o.1 P / N ^ (-(r + s))⌋ - (j : ℤ))
        ((measurable_unshift _ P j).snd) A hA
      exact ⟨M, hM, hAM, hMA⟩)
    (T := 4 * θ') (θ := θ') (by simp only [Fintype.card_fin]; norm_num)
  simpa only [Fintype.card_fin, Nat.cast_ofNat, show (2 : ℝ≥0∞) * 2 = 4 by norm_num] using h

/-- A real in a unit window above `a` has floor `⌊a⌋` or `⌊a⌋ + 1`. -/
lemma floor_window_cases {a x : ℝ} (h1 : a ≤ x) (h2 : x < a + 1) :
    ⌊x⌋ = ⌊a⌋ ∨ ⌊x⌋ = ⌊a⌋ + 1 := by
  have hlo : ⌊a⌋ ≤ ⌊x⌋ := Int.floor_mono h1
  have hhi : ⌊x⌋ ≤ ⌊a⌋ + 1 := by
    have : ⌊x⌋ ≤ ⌊a + 1⌋ := Int.floor_mono h2.le
    rwa [Int.floor_add_one] at this
  omega

/-- The original angular bin containing the left end of a normalized angular bin. -/
def angBase (v α wp : ℝ) (m : ℤ) : ℤ := ⌊(v + α * m) / wp⌋

/-- The relabelling of joint observations recovering original hidden and angular bins. -/
def jointUnshift (w : ℝ) (P : MvPolynomial (Fin 2) ℝ) (v α wp : ℝ) (j : Fin 2 × Fin 2)
    (o : Joint) : Joint :=
  (unshift w P j.1 o.1, angBase v α wp o.2 + (j.2 : ℤ))

lemma angular_cover {v α wp c : ℝ} (hα : 0 < α) (hαw : α ≤ wp) :
    ∃ j : Fin 2, ⌊c / wp⌋ = angBase v α wp ⌊(c - v) / α⌋ + (j : ℤ) := by
  have hwp : 0 < wp := hα.trans_le hαw
  set m := ⌊(c - v) / α⌋
  have h1 : (m : ℝ) ≤ (c - v) / α := Int.floor_le _
  have h2 : (c - v) / α < m + 1 := Int.lt_floor_add_one _
  have h1' : v + α * m ≤ c := by
    have := (le_div_iff₀ hα).mp h1
    linarith
  have h2' : c < v + α * m + wp := by
    have := (div_lt_iff₀ hα).mp h2
    nlinarith
  have hw1 : (v + α * m) / wp ≤ c / wp := div_le_div_of_nonneg_right h1' hwp.le
  have hw2 : c / wp < (v + α * m) / wp + 1 := by
    rw [div_add_one hwp.ne', div_lt_div_iff_of_pos_right hwp]
    exact h2'
  rcases floor_window_cases hw1 hw2 with h | h
  · exact ⟨0, by rw [angBase, h]; simp⟩
  · exact ⟨1, by rw [angBase, h]; simp⟩

/-- Upper tails of the joint law of a normalized chart world. -/
theorem world_angular_tail (hN : 0 < N) (hdt : 0 < dt) (hJ : 0 < J) (hθ : Measurable θ)
    (hy : ∀ l t, Spec.y (θ l) ((t - t₀) / dt) = (Spec.y l t - u - t * v) / J)
    (hx : ∀ l t, Spec.x (θ l) ((t - t₀) / dt) =
      (Spec.x l t - MvPolynomial.eval ![t, Spec.y l t] P) / N ^ (-r))
    {μ μq : Measure Inc} [IsFiniteMeasure μ] {C : Set Inc} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcT : c ≠ ∞)
    (hμq : μq = c • (μ.restrict C).map (normInc t₀ dt θ))
    (s uq up : ℝ) (hα : J / dt * N ^ (-uq) ≤ N ^ (-up))
    {g : Joint → ℝ≥0∞} (hg : Measurable g)
    (hglaw : μq.map (aug N s uq) = JointRef.withDensity g)
    {H : Joint → ℝ≥0∞} (hH : Measurable H)
    (hHlaw : μ.map (aug N (r + s) up) = JointRef.withDensity H) (θ' : ℝ≥0∞) :
    μq {z | c * ENNReal.ofReal (dt * J) * (8 * θ') < g (aug N s uq z)} ≤
      c * (8 * μ (C ∩ {z | θ' < H (aug N (r + s) up z)})) := by
  set sJ : ℝ≥0∞ := ENNReal.ofReal (dt * J) with hsJ
  have hs0 : sJ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hdt hJ)
  have hsT : sJ ≠ ∞ := ENNReal.ofReal_ne_top
  set A := jointEquiv t₀ dt u v J hdt.ne' hJ.ne'
  set κ : ℝ≥0∞ := c⁻¹ * sJ⁻¹ with hκ
  have hκ0 : κ ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.mpr hcT) (ENNReal.inv_ne_zero.mpr hsT)
  have hκT : κ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0) (ENNReal.inv_ne_top.mpr hs0)
  have hκc : κ * (c * sJ) = 1 := by
    rw [hκ, mul_mul_mul_comm, ENNReal.inv_mul_cancel hc0 hcT, ENNReal.inv_mul_cancel hs0 hsT,
      one_mul]
  set Ψ : Inc → Joint := fun z => (shiftObs (N ^ (-(r + s))) P z,
    ⌊(dt * (z.1.2 1 - v) / J) / N ^ (-uq)⌋) with hΨ
  have hΨm : Measurable Ψ := (measurable_shiftObs _ P).prodMk (by fun_prop)
  set D : Joint → ℝ≥0∞ := fun o => κ * g (A o) with hDdef
  have hDm : Measurable D := measurable_const.mul (hg.comp A.measurable)
  have hD : (μ.restrict C).map Ψ = JointRef.withDensity D :=
    shift_joint_density_law hN hdt hJ hθ hy hx hc0 hcT hμq s uq hglaw
  have hmeas : MeasurableSet {z | c * sJ * (8 * θ') < g (aug N s uq z)} :=
    measurableSet_lt measurable_const (hg.comp (measurable_aug N s uq))
  rw [normalized_mass hθ hμq hmeas]
  gcongr
  have hset : C ∩ normInc t₀ dt θ ⁻¹' {z | c * sJ * (8 * θ') < g (aug N s uq z)} =
      C ∩ {z | 8 * θ' < D (Ψ z)} := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, aug_normInc hN hdt hJ hy hx s uq z]
    apply and_congr_right
    intro _
    rw [hDdef, ← mul_lt_mul_iff_left' hκ0 hκT (a := c * sJ * (8 * θ')), ← mul_assoc,
      hκc, one_mul]
  rw [hset]
  have hαpos : 0 < J / dt * N ^ (-uq) := mul_pos (div_pos hJ hdt) (Real.rpow_pos_of_pos hN _)
  have hcover : ∀ z, ∃ j : Fin 2 × Fin 2, aug N (r + s) up z =
      jointUnshift (N ^ (-(r + s))) P v (J / dt * N ^ (-uq)) (N ^ (-up)) j (Ψ z) := by
    intro z
    obtain ⟨a, ha⟩ := obs_eq_unshift (N := N) (σ := r + s) P z
    obtain ⟨b, hb⟩ := angular_cover (v := v) (c := z.1.2 1) hαpos hα
    refine ⟨(a, b), ?_⟩
    unfold aug jointUnshift
    rw [← ha]
    congr 1
    rw [hb]
    congr 2
    rw [hΨ]
    simp only
    congr 1
    field_simp
  have h := cover_upper_tail JointRef JointRef μ (measurable_aug N (r + s) up) hΨm hH hHlaw C
    hDm hD (jointUnshift (N ^ (-(r + s))) P v (J / dt * N ^ (-uq)) (N ^ (-up))) hcover
    (fun j A hA => joint_labelImage_cover
      (fun q => (q.2.1 - ⌊-MvPolynomial.eval q.1 P / N ^ (-(r + s))⌋ - (j.1 : ℤ),
        angBase v (J / dt * N ^ (-uq)) (N ^ (-up)) q.2.2 + (j.2 : ℤ)))
      (by
        refine Measurable.prodMk ?_ ?_
        · have hP : Measurable (fun q : (Fin 2 → ℝ) × (ℤ × ℤ) => MvPolynomial.eval q.1 P) :=
            (MvPolynomial.continuous_eval P).measurable.comp measurable_fst
          exact ((measurable_snd.fst).sub ((hP.neg.div_const _).floor)).sub_const _
        · exact ((measurable_of_countable
            (fun m : ℤ => angBase v (J / dt * N ^ (-uq)) (N ^ (-up)) m)).comp
              measurable_snd.snd).add_const _)
      _ (fun o => rfl) A hA)
    (T := 8 * θ') (θ := θ') (by simp only [Fintype.card_prod, Fintype.card_fin]; norm_num)
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_ofNat,
    show (2 : ℝ≥0∞) * ((2 * 2 : ℕ) : ℝ≥0∞) = 8 by norm_num] using h

/-- Relabelling a chart restriction by the shifted hidden bin loses density by a factor `ε`
only on mass `2 ε μ C`. -/
theorem shift_relabel_low {μ : Measure Inc} {C : Set Inc} (hC : MeasurableSet C)
    (w : ℝ) (P : MvPolynomial (Fin 2) ℝ) {N σ : ℝ} (hw : w = N ^ (-σ))
    {D : Base → ℝ≥0∞} (hD : Measurable D)
    (hDlaw : (μ.restrict C).map (shiftObs w P) = BaseRef.withDensity D)
    {D' : Base → ℝ≥0∞} (hD' : Measurable D')
    (hD'law : (μ.restrict C).map (obs N σ) = BaseRef.withDensity D') (ε : ℝ≥0∞) :
    μ (C ∩ {z | D (shiftObs w P z) < ε * D' (obs N σ z)}) ≤ ε * 2 * μ C := by
  classical
  subst hw
  set w := N ^ (-σ)
  let ψ : Inc → Fin 2 → ℝ := fun z => ![z.2, Spec.y z.1 z.2]
  have hψ : Measurable ψ := by
    unfold ψ Spec.y
    fun_prop
  let ℓ₁ : Inc → ℤ := fun z => (shiftObs w P z).2
  let ℓ₂ : Inc → ℤ := fun z => (obs N σ z).2
  have hℓ₁ : Measurable ℓ₁ := (measurable_shiftObs w P).snd
  have hℓ₂ : Measurable ℓ₂ := (measurable_obs N σ).snd
  have hlaw₁ : (μ.restrict C).map (fun z => (ψ z, ℓ₁ z)) =
      ((volume : Measure (Fin 2 → ℝ)).prod Measure.count).withDensity D := hDlaw
  have hlaw₂ : (μ.restrict C).map (fun z => (ψ z, ℓ₂ z)) =
      ((volume : Measure (Fin 2 → ℝ)).prod Measure.count).withDensity D' := hD'law
  let R : (Fin 2 → ℝ) → ℤ → ℤ → Prop := fun b m₁ m₂ =>
    m₂ = m₁ - ⌊-MvPolynomial.eval b P / w⌋ - 0 ∨ m₂ = m₁ - ⌊-MvPolynomial.eval b P / w⌋ - 1
  have hRm : ∀ m₁ m₂, MeasurableSet {b | R b m₁ m₂} := by
    intro m₁ m₂
    have hf : Measurable (fun b : Fin 2 → ℝ => ⌊-MvPolynomial.eval b P / w⌋) :=
      (((MvPolynomial.continuous_eval P).measurable.neg).div_const w).floor
    exact (measurableSet_eq_fun measurable_const ((hf.const_sub m₁).sub_const 0)).union
      (measurableSet_eq_fun measurable_const ((hf.const_sub m₁).sub_const 1))
  have hR : ∀ᵐ z ∂μ.restrict C, R (ψ z) (ℓ₁ z) (ℓ₂ z) := by
    refine Filter.Eventually.of_forall fun z => ?_
    obtain ⟨j, hj⟩ := obs_eq_unshift (N := N) (σ := σ) P z
    have h2 : (obs N σ z).2 = (shiftObs w P z).2 - ⌊-MvPolynomial.eval (shiftObs w P z).1 P / w⌋
        - (j : ℤ) := by
      rw [hj]
      rfl
    fin_cases j
    · left
      simpa [ℓ₁, ℓ₂, ψ, shiftObs] using h2
    · right
      simpa [ℓ₁, ℓ₂, ψ, shiftObs] using h2
  have hcount : ∀ b m₂, ∑' m₁,
      (@ite _ (R b m₁ m₂) (Classical.propDecidable _) (1 : ℝ≥0∞) 0) ≤ 2 := by
    intro b m₂
    set σb := ⌊-MvPolynomial.eval b P / w⌋
    refine (k4_scalar_grid_density_extension.tsum_ite_one_le_card (R b · m₂)
      ({m₂ + σb, m₂ + σb + 1} : Finset ℤ) ?_).trans ?_
    · intro m₁ hm
      rcases hm with h | h
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        left
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        right
        omega
    · exact_mod_cast (Finset.card_insert_le _ _).trans (by simp)
  have hmain := relation_low_density_mass_dep (μ.restrict C) volume ψ ℓ₁ ℓ₂
    (fun m => measurableSet_eq_fun hℓ₂ measurable_const)
    (fun b m => D (b, m)) (fun b m => D' (b, m))
    (fun m => hD.comp (measurable_id.prodMk measurable_const))
    (fun m => hD'.comp (measurable_id.prodMk measurable_const))
    (fun m S hS => k4_scalar_crop_profile_transport.label_density_slice volume (μ.restrict C)
      ψ hψ ℓ₁ hℓ₁ D hD hlaw₁ m S hS)
    (fun m S hS => k4_scalar_crop_profile_transport.label_density_slice volume (μ.restrict C)
      ψ hψ ℓ₂ hℓ₂ D' hD' hlaw₂ m S hS)
    R hRm hR 2 hcount ε
  have hS : MeasurableSet {z | D (shiftObs w P z) < ε * D' (obs N σ z)} :=
    measurableSet_lt (hD.comp (measurable_shiftObs w P))
      (measurable_const.mul (hD'.comp (measurable_obs N σ)))
  have heq : {p | D (ψ p, ℓ₁ p) < ε * D' (ψ p, ℓ₂ p)} =
      {z | D (shiftObs w P z) < ε * D' (obs N σ z)} := rfl
  rw [heq, Measure.restrict_apply hS, Measure.restrict_apply_univ] at hmain
  rw [inter_comm]
  exact hmain

/-- Lower tails of a normalized chart world, through a relabelling, a restriction and a lower
tail of the original density. -/
theorem world_lower_tail (hN : 0 < N) (hdt : 0 < dt) (hJ : 0 < J) (hθ : Measurable θ)
    (hy : ∀ l t, Spec.y (θ l) ((t - t₀) / dt) = (Spec.y l t - u - t * v) / J)
    (hx : ∀ l t, Spec.x (θ l) ((t - t₀) / dt) =
      (Spec.x l t - MvPolynomial.eval ![t, Spec.y l t] P) / N ^ (-r))
    {μ μq : Measure Inc} {C : Set Inc} (hC : MeasurableSet C) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcT : c ≠ ∞)
    (hμq : μq = c • (μ.restrict C).map (normInc t₀ dt θ))
    (s : ℝ) {g : Base → ℝ≥0∞} (hg : Measurable g)
    (hglaw : μq.map (obs N s) = BaseRef.withDensity g)
    {H : Base → ℝ≥0∞} (hH : Measurable H)
    {D' : Base → ℝ≥0∞} (hD' : Measurable D')
    (hD'law : (μ.restrict C).map (obs N (r + s)) = BaseRef.withDensity D')
    (ε δ X : ℝ≥0∞) :
    μq {z | g (obs N s z) < c * ENNReal.ofReal (dt * J) * (ε * (δ * X))} ≤
      c * (ε * 2 * μ C + μ (C ∩ {z | D' (obs N (r + s) z) < δ * H (obs N (r + s) z)}) +
        μ (C ∩ {z | H (obs N (r + s) z) < X})) := by
  set sJ : ℝ≥0∞ := ENNReal.ofReal (dt * J) with hsJ
  have hs0 : sJ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hdt hJ)
  have hsT : sJ ≠ ∞ := ENNReal.ofReal_ne_top
  set A := baseEquiv t₀ dt u v J hdt.ne' hJ.ne'
  set κ : ℝ≥0∞ := c⁻¹ * sJ⁻¹ with hκ
  have hκ0 : κ ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.mpr hcT) (ENNReal.inv_ne_zero.mpr hsT)
  have hκT : κ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0) (ENNReal.inv_ne_top.mpr hs0)
  have hκc : κ * (c * sJ) = 1 := by
    rw [hκ, mul_mul_mul_comm, ENNReal.inv_mul_cancel hc0 hcT, ENNReal.inv_mul_cancel hs0 hsT,
      one_mul]
  set w := N ^ (-(r + s))
  set D : Base → ℝ≥0∞ := fun o => κ * g (A o) with hDdef
  have hDm : Measurable D := measurable_const.mul (hg.comp A.measurable)
  have hD : (μ.restrict C).map (shiftObs w P) = BaseRef.withDensity D :=
    shift_density_law hN hdt hJ hθ hy hx hc0 hcT hμq s hglaw
  have hmeas : MeasurableSet {z | g (obs N s z) < c * sJ * (ε * (δ * X))} :=
    measurableSet_lt (hg.comp (measurable_obs N s)) measurable_const
  rw [normalized_mass hθ hμq hmeas]
  gcongr
  have hset : C ∩ normInc t₀ dt θ ⁻¹' {z | g (obs N s z) < c * sJ * (ε * (δ * X))} ⊆
      (C ∩ {z | D (shiftObs w P z) < ε * D' (obs N (r + s) z)}) ∪
      (C ∩ {z | D' (obs N (r + s) z) < δ * H (obs N (r + s) z)}) ∪
      (C ∩ {z | H (obs N (r + s) z) < X}) := by
    rintro z ⟨hzC, hz⟩
    simp only [mem_preimage, mem_ofPred_eq, obs_normInc hN hdt hJ hy hx s z] at hz
    have hz' : D (shiftObs w P z) < ε * (δ * X) := by
      rw [hDdef]
      simp only
      rw [← mul_lt_mul_iff_left' hκ0 hκT (a := g _), ← mul_assoc, hκc, one_mul] at hz
      exact hz
    by_contra hcon
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq, not_or, not_and, not_lt] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    have := (h1 hzC).trans' (mul_le_mul' le_rfl ((h2 hzC).trans' (mul_le_mul' le_rfl (h3 hzC))))
    exact absurd hz' (not_lt.mpr this)
  refine (measure_mono hset).trans ((measure_union_le _ _).trans ?_)
  gcongr
  refine (measure_union_le _ _).trans ?_
  gcongr
  exact shift_relabel_low hC w P rfl hDm hD hD' hD'law ε

end World

end Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis
