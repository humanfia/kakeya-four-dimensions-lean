-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.SBBranch.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.TwoLevel

/-!
# The frozen `SB` from Katz–Tao fibres (the KT case of the non-sticky branch)

`SBpred` is the frozen `SB` of o071/o070 with `P j`, `R l` inlined. `SB_of_KTcase` derives it for
an aligned family on two nested radii `τ < ρ = m τ` from: common residue classes at both radii
(exact covers, `TwoLevel.two_level_cover`), balanced populations at both levels (`Regularize`),
Katz–Tao with constant `c` inside every `ρ`-cell, fullness, and global Frostman. This is the
bookkeeping of x0318's KT case (o070 thread, 15:05Z).
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

open MeasureTheory

/-- The frozen `SB` of o071 (and o070), with the coarse and fine tubes inlined. -/
def SBpred (ζ₁ ζ₂ δ : ℝ) (k : ℕ) (A : Fin k → Set Sp) : Prop :=
  ∃ τ ρ : ℝ, δ ≤ τ ∧ τ < ρ ∧ ρ ≤ 1 ∧ τ ≤ δ ^ ζ₁ * ρ ∧
    ∃ (p : ℕ) (y u : Fin p → Sp) (q : ℕ) (z w : Fin q → Sp),
      (∀ j, ‖u j‖ = 1) ∧ (∀ l, ‖w l‖ = 1) ∧
      (∀ j j', j ≠ j' → volume (Metric.thickening τ (segment ℝ (y j) (y j + u j)) ∩
          Metric.thickening τ (segment ℝ (y j') (y j' + u j'))) ≤
          1 / 2 * volume (Metric.thickening τ (segment ℝ (y j) (y j + u j)))) ∧
      (∀ l l', l ≠ l' → volume (Metric.thickening ρ (segment ℝ (z l) (z l + w l)) ∩
          Metric.thickening ρ (segment ℝ (z l') (z l' + w l'))) ≤
          1 / 2 * volume (Metric.thickening ρ (segment ℝ (z l) (z l + w l)))) ∧
      (∀ i, ∃! j, A i ⊆ Metric.thickening τ (segment ℝ (y j) (y j + u j))) ∧
      (∀ j, ∃ i, A i ⊆ Metric.thickening τ (segment ℝ (y j) (y j + u j))) ∧
      (∀ j, ∃! l, Metric.thickening τ (segment ℝ (y j) (y j + u j)) ⊆
          Metric.thickening ρ (segment ℝ (z l) (z l + w l))) ∧
      (∀ l, ∃ j, Metric.thickening τ (segment ℝ (y j) (y j + u j)) ⊆
          Metric.thickening ρ (segment ℝ (z l) (z l + w l))) ∧
      (∀ j j', (Set.ncard {i | A i ⊆ Metric.thickening τ (segment ℝ (y j) (y j + u j))} : ℝ) ≤
          δ ^ (-ζ₂) * Set.ncard {i | A i ⊆ Metric.thickening τ (segment ℝ (y j') (y j' + u j'))}) ∧
      (∀ l l', (Set.ncard {j | Metric.thickening τ (segment ℝ (y j) (y j + u j)) ⊆
          Metric.thickening ρ (segment ℝ (z l) (z l + w l))} : ℝ) ≤
          δ ^ (-ζ₂) * Set.ncard {j | Metric.thickening τ (segment ℝ (y j) (y j + u j)) ⊆
            Metric.thickening ρ (segment ℝ (z l') (z l' + w l'))}) ∧
      (∀ j (W : Set Sp), Convex ℝ W →
          ENNReal.ofReal (Set.ncard {i | A i ⊆ Metric.thickening τ (segment ℝ (y j) (y j + u j)) ∧
            A i ⊆ W} * τ ^ 2) ≤
          ENNReal.ofReal (δ ^ (-ζ₂) *
            Set.ncard {i | A i ⊆ Metric.thickening τ (segment ℝ (y j) (y j + u j))}) * volume W) ∧
      (∀ l (W : Set Sp), Convex ℝ W →
          ENNReal.ofReal (Set.ncard {j | Metric.thickening τ (segment ℝ (y j) (y j + u j)) ⊆
            Metric.thickening ρ (segment ℝ (z l) (z l + w l)) ∧
            Metric.thickening τ (segment ℝ (y j) (y j + u j)) ⊆ W} * τ ^ 2) ≤
          ENNReal.ofReal (δ ^ (-ζ₂)) * volume W) ∧
      (∀ l, δ ^ ζ₂ * (ρ / τ) ^ 2 ≤ Set.ncard {j | Metric.thickening τ (segment ℝ (y j) (y j + u j)) ⊆
          Metric.thickening ρ (segment ℝ (z l) (z l + w l))}) ∧
      (∀ W : Set Sp, Convex ℝ W →
          ENNReal.ofReal (Set.ncard {l | Metric.thickening ρ (segment ℝ (z l) (z l + w l)) ⊆ W}) ≤
          ENNReal.ofReal (δ ^ (-ζ₂) * q) * volume W)

/-- Scaling an `ENNReal` count bound: from `ofReal A ≤ ofReal c * μ W`, `B ≤ k A` and `k c ≤ d`
follows `ofReal B ≤ ofReal d * μ W`. -/
lemma ofReal_scale {A B k c d : ℝ} {V : ENNReal} (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hA : ENNReal.ofReal A ≤ ENNReal.ofReal c * V) (hB : B ≤ k * A) (hkc : k * c ≤ d) :
    ENNReal.ofReal B ≤ ENNReal.ofReal d * V := by
  calc ENNReal.ofReal B ≤ ENNReal.ofReal (k * A) := ENNReal.ofReal_le_ofReal hB
    _ = ENNReal.ofReal k * ENNReal.ofReal A := ENNReal.ofReal_mul hk
    _ ≤ ENNReal.ofReal k * (ENNReal.ofReal c * V) := by gcongr
    _ = ENNReal.ofReal (k * c) * V := by rw [← mul_assoc, ← ENNReal.ofReal_mul hk]
    _ ≤ ENNReal.ofReal d * V := by gcongr

/-- Disjoint fibres inside a finset: `Σ |fib j| ≤ |T|`. -/
lemma sum_card_le_of_disjoint {ι κ : Type*} [DecidableEq ι] (J : Finset κ) (fib : κ → Finset ι)
    (T : Finset ι) (hdisj : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → Disjoint (fib j) (fib j'))
    (hsub : ∀ j ∈ J, fib j ⊆ T) : ∑ j ∈ J, (fib j).card ≤ T.card := by
  classical
  rw [← Finset.card_biUnion (fun j hj j' hj' hne => hdisj j hj j' hj' hne)]
  exact Finset.card_le_card (Finset.biUnion_subset.2 hsub)

lemma ncard_fin_filter {p : ℕ} (Q : Fin p → Prop) [DecidablePred Q] :
    Set.ncard {j | Q j} = (Finset.univ.filter Q).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp

open Classical in
/-- The KT case of the non-sticky branch: the frozen `SB` for an aligned family on two nested
radii, from exact covers, balance, Katz–Tao inside the `ρ`-cells, fullness and global
Frostman. -/
theorem SB_of_KTcase {δ τ ρ ζ₁ ζ₂ c KF : ℝ} (hδ : 0 < δ) (hδτ : 2 * δ ≤ τ)
    {m : ℕ} (hm : 2 ≤ m) (hρm : ρ = (m : ℝ) * τ) (hρ : ρ ≤ 1 / 10000) (hsc : τ ≤ δ ^ ζ₁ * ρ)
    {n : ℕ} (x v : Fin n → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : ∀ i, x i = leftStart δ (x i) (v i)) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (hclsτ : ∀ i ∈ S, ∀ i' ∈ S, classKey 200000 τ (x i) (v i) = classKey 200000 τ (x i') (v i'))
    (hclsρ : ∀ i ∈ S, ∀ i' ∈ S, classKey 200000 ρ (x i) (v i) = classKey 200000 ρ (x i') (v i'))
    (a b : ℕ)
    (hbalτ : ∀ i ∈ S, 2 ^ a ≤ pop S (fun i => lineCell (τ / 20) (x i) (v i)) i ∧
      pop S (fun i => lineCell (τ / 20) (x i) (v i)) i < 2 ^ (a + 1))
    (hbalρ : ∀ i ∈ S, 2 ^ b ≤ pop S (fun i => lineCell (ρ / 20) (x i) (v i)) i ∧
      pop S (fun i => lineCell (ρ / 20) (x i) (v i)) i < 2 ^ (b + 1))
    (hc0 : 0 ≤ c)
    (hKT : ∀ i₀ ∈ S, ∀ W : Set Sp, Convex ℝ W →
      ENNReal.ofReal ((S.filter (fun i => lineCell (ρ / 20) (x i) (v i) =
          lineCell (ρ / 20) (x i₀) (v i₀) ∧
          Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card * δ ^ 2) ≤
        ENNReal.ofReal c * volume W)
    (hcτ : c * τ ^ 2 ≤ δ ^ (-ζ₂) * 2 ^ a * δ ^ 2)
    (hfull : δ ^ ζ₂ * (ρ / τ) ^ 2 * 2 ^ (a + 1) ≤ 2 ^ b)
    (hKF0 : 0 ≤ KF)
    (hFG : ∀ W : Set Sp, Convex ℝ W →
      ENNReal.ofReal ((S.filter (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card : ℝ) ≤
        ENNReal.ofReal (KF * S.card) * volume W)
    (hKF : 2 * KF ≤ δ ^ (-ζ₂)) (hζ₂ : 4 ≤ δ ^ (-ζ₂)) :
    SBpred ζ₁ ζ₂ δ S.card (fun j => Metric.thickening δ (segment ℝ (x (S.equivFin.symm j).1)
      (x (S.equivFin.symm j).1 + v (S.equivFin.symm j).1))) := by
  classical
  obtain ⟨p, y, u, q, z, w, hu, hw, hovP, hovR, hexuP, husedP, hPR1, hPR2, hexuR, hfibP, hfibR⟩ :=
    two_level_cover hδ hδτ hm hρm hρ x v hv hT hcan hanti S hS hclsτ hclsρ
  have hτ0 : 0 < τ := by linarith
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hτρ : τ < ρ := by rw [hρm]; nlinarith
  set A : Fin n → Set Sp := fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) with hAdef
  set P : Fin p → Set Sp := fun j => Metric.thickening τ (segment ℝ (y j) (y j + u j)) with hPdef
  set R : Fin q → Set Sp := fun l => Metric.thickening ρ (segment ℝ (z l) (z l + w l)) with hRdef
  set g : Fin S.card → Fin n := fun j => (S.equivFin.symm j).1 with hgdef
  have hgS : ∀ j, g j ∈ S := fun j => (S.equivFin.symm j).2
  have hgsurj : ∀ i (hi : i ∈ S), g (S.equivFin ⟨i, hi⟩) = i := by
    intro i hi; simp only [hgdef, Equiv.symm_apply_apply]
  let fibP : Fin p → Finset (Fin n) := fun j => S.filter (fun i => A i ⊆ P j)
  let fibR : Fin q → Finset (Fin n) := fun l => S.filter (fun i => A i ⊆ R l)
  -- the sizes of the fibres
  have hfibPcard : ∀ j, 2 ^ a ≤ (fibP j).card ∧ (fibP j).card < 2 ^ (a + 1) := by
    intro j
    obtain ⟨i₀, hi₀, -, -, hiff⟩ := hfibP j
    have he : fibP j = S.filter (fun i => lineCell (τ / 20) (x i) (v i) =
        lineCell (τ / 20) (x i₀) (v i₀)) := by
      ext i; simp only [fibP, Finset.mem_filter]
      constructor
      · rintro ⟨hi, h⟩; exact ⟨hi, (hiff i hi).1 h⟩
      · rintro ⟨hi, h⟩; exact ⟨hi, (hiff i hi).2 h⟩
    rw [he]
    exact hbalτ i₀ hi₀
  have hfibRcard : ∀ l, 2 ^ b ≤ (fibR l).card ∧ (fibR l).card < 2 ^ (b + 1) := by
    intro l
    obtain ⟨i₁, hi₁, -, -, hiff⟩ := hfibR l
    have he : fibR l = S.filter (fun i => lineCell (ρ / 20) (x i) (v i) =
        lineCell (ρ / 20) (x i₁) (v i₁)) := by
      ext i; simp only [fibR, Finset.mem_filter]
      constructor
      · rintro ⟨hi, h⟩; exact ⟨hi, (hiff i hi).1 h⟩
      · rintro ⟨hi, h⟩; exact ⟨hi, (hiff i hi).2 h⟩
    rw [he]
    exact hbalρ i₁ hi₁
  -- disjointness of the fibres
  have hdisjP : ∀ j j', j ≠ j' → Disjoint (fibP j) (fibP j') := by
    intro j j' hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨j₀, -, hj₀⟩ := hexuP i (Finset.mem_filter.1 hi).1
    exact hne ((hj₀ j (Finset.mem_filter.1 hi).2).trans (hj₀ j' (Finset.mem_filter.1 hi').2).symm)
  have hdisjR : ∀ l l', l ≠ l' → Disjoint (fibR l) (fibR l') := by
    intro l l' hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨l₀, -, hl₀⟩ := hexuR i (Finset.mem_filter.1 hi).1
    exact hne ((hl₀ l (Finset.mem_filter.1 hi).2).trans (hl₀ l' (Finset.mem_filter.1 hi').2).symm)
  -- the `P` inside `R l`
  let J : Fin q → Finset (Fin p) := fun l => Finset.univ.filter (fun j => P j ⊆ R l)
  have hJsub : ∀ l, ∀ j ∈ J l, fibP j ⊆ fibR l := by
    intro l j hj i hi
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hi).1,
      (Finset.mem_filter.1 hi).2.trans (Finset.mem_filter.1 hj).2⟩
  have hJcov : ∀ l, fibR l ⊆ (J l).biUnion fibP := by
    intro l i hi
    obtain ⟨hiS, hiR⟩ := Finset.mem_filter.1 hi
    obtain ⟨j, hj, -⟩ := hexuP i hiS
    obtain ⟨l', hl', -⟩ := hPR1 j
    obtain ⟨l₀, -, hl₀⟩ := hexuR i hiS
    have hll : l' = l := (hl₀ l' (hj.trans hl')).trans (hl₀ l hiR).symm
    rw [Finset.mem_biUnion]
    exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hll ▸ hl'⟩, Finset.mem_filter.2 ⟨hiS, hj⟩⟩
  have hJupper : ∀ l, (J l).card * 2 ^ a ≤ (fibR l).card := by
    intro l
    calc (J l).card * 2 ^ a = ∑ _j ∈ J l, 2 ^ a := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ j ∈ J l, (fibP j).card := Finset.sum_le_sum fun j _ => (hfibPcard j).1
      _ ≤ (fibR l).card := sum_card_le_of_disjoint (J l) fibP (fibR l)
          (fun j _ j' _ hne => hdisjP j j' hne) (hJsub l)
  have hJlower : ∀ l, (fibR l).card ≤ (J l).card * 2 ^ (a + 1) := by
    intro l
    calc (fibR l).card ≤ ((J l).biUnion fibP).card := Finset.card_le_card (hJcov l)
      _ ≤ ∑ j ∈ J l, (fibP j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ J l, 2 ^ (a + 1) := Finset.sum_le_sum fun j _ => (hfibPcard j).2.le
      _ = (J l).card * 2 ^ (a + 1) := by rw [Finset.sum_const, smul_eq_mul]
  -- counting translations
  have hcntP : ∀ j, Set.ncard {i | A (g i) ⊆ P j} = (fibP j).card := fun j =>
    ncard_enum S (fun i => A i ⊆ P j)
  have hcntJ : ∀ l, Set.ncard {j | P j ⊆ R l} = (J l).card := fun l =>
    ncard_fin_filter (fun j => P j ⊆ R l)
  have hdξ : (0 : ℝ) < δ ^ (-ζ₂) := by positivity
  refine ⟨τ, ρ, by linarith, hτρ, by linarith, hsc, p, y, u, q, z, w, hu, hw, hovP, hovR,
    fun i => hexuP (g i) (hgS i), fun j => ?_, hPR1, hPR2, fun j j' => ?_, fun l l' => ?_,
    fun j W hW => ?_, fun l W hW => ?_, fun l => ?_, fun W hW => ?_⟩
  · -- every `P j` contains a tube
    obtain ⟨i, hi, hsub⟩ := husedP j
    exact ⟨S.equivFin ⟨i, hi⟩, by simp only [Equiv.symm_apply_apply]; exact hsub⟩
  · -- balance of the fine fibres
    change (Set.ncard {i | A (g i) ⊆ P j} : ℝ) ≤ δ ^ (-ζ₂) * Set.ncard {i | A (g i) ⊆ P j'}
    rw [hcntP, hcntP]
    have h1 : ((fibP j).card : ℝ) < 2 ^ (a + 1) := by exact_mod_cast (hfibPcard j).2
    have h2 : (2 : ℝ) ^ a ≤ (fibP j').card := by exact_mod_cast (hfibPcard j').1
    calc ((fibP j).card : ℝ) ≤ 2 * 2 ^ a := by rw [pow_succ] at h1; linarith
      _ ≤ 2 * (fibP j').card := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ δ ^ (-ζ₂) * (fibP j').card :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  · -- balance of the numbers of fine tubes in the coarse tubes
    change (Set.ncard {j | P j ⊆ R l} : ℝ) ≤ δ ^ (-ζ₂) * Set.ncard {j | P j ⊆ R l'}
    rw [hcntJ, hcntJ]
    have hu1 : ((J l).card : ℝ) * 2 ^ a ≤ (fibR l).card := by exact_mod_cast hJupper l
    have hu2 : ((fibR l).card : ℝ) < 2 ^ (b + 1) := by exact_mod_cast (hfibRcard l).2
    have hl1 : ((fibR l').card : ℝ) ≤ (J l').card * 2 ^ (a + 1) := by exact_mod_cast hJlower l'
    have hl2 : (2 : ℝ) ^ b ≤ (fibR l').card := by exact_mod_cast (hfibRcard l').1
    have ha : (0 : ℝ) < 2 ^ a := by positivity
    have hJl : ((J l).card : ℝ) * 2 ^ a ≤ 2 * 2 ^ b := by rw [pow_succ] at hu2; linarith
    have hJl' : (2 : ℝ) ^ b ≤ (J l').card * (2 * 2 ^ a) := by rw [pow_succ] at hl1; linarith
    have : ((J l).card : ℝ) * 2 ^ a ≤ 4 * (J l').card * 2 ^ a := by nlinarith
    have hJ : ((J l).card : ℝ) ≤ 4 * (J l').card := le_of_mul_le_mul_right (by linarith) ha
    calc ((J l).card : ℝ) ≤ 4 * (J l').card := hJ
      _ ≤ δ ^ (-ζ₂) * (J l').card := mul_le_mul_of_nonneg_right hζ₂ (Nat.cast_nonneg _)
  · -- Frostman of the δ-tubes in `P j`
    obtain ⟨l₀, hl₀, -⟩ := hPR1 j
    obtain ⟨i₁, hi₁, -, -, hiffR⟩ := hfibR l₀
    set Fs := S.filter (fun i => lineCell (ρ / 20) (x i) (v i) = lineCell (ρ / 20) (x i₁) (v i₁) ∧
      A i ⊆ W) with hFs
    have hsubset : S.filter (fun i => A i ⊆ P j ∧ A i ⊆ W) ⊆ Fs := by
      intro i hi
      obtain ⟨hiS, hiP, hiW⟩ := Finset.mem_filter.1 hi
      exact Finset.mem_filter.2 ⟨hiS, (hiffR i hiS).1 (hiP.trans hl₀), hiW⟩
    have hcnt : Set.ncard {i | A (g i) ⊆ P j ∧ A (g i) ⊆ W} =
        (S.filter (fun i => A i ⊆ P j ∧ A i ⊆ W)).card :=
      ncard_enum S (fun i => A i ⊆ P j ∧ A i ⊆ W)
    change ENNReal.ofReal (Set.ncard {i | A (g i) ⊆ P j ∧ A (g i) ⊆ W} * τ ^ 2) ≤
      ENNReal.ofReal (δ ^ (-ζ₂) * Set.ncard {i | A (g i) ⊆ P j}) * volume W
    rw [hcnt, hcntP]
    have hFsle : ((S.filter (fun i => A i ⊆ P j ∧ A i ⊆ W)).card : ℝ) ≤ Fs.card := by
      exact_mod_cast Finset.card_le_card hsubset
    have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
    refine ofReal_scale (A := (Fs.card : ℝ) * δ ^ 2) (k := τ ^ 2 / δ ^ 2) (c := c) (by positivity) hc0
      (hKT i₁ hi₁ W hW) ?_ ?_
    · rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ hδ2.ne', mul_comm]
      exact mul_le_mul_of_nonneg_left hFsle (by positivity)
    · have h2a : (2 : ℝ) ^ a ≤ (fibP j).card := by exact_mod_cast (hfibPcard j).1
      rw [div_mul_eq_mul_div, div_le_iff₀ hδ2]
      calc τ ^ 2 * c = c * τ ^ 2 := by ring
        _ ≤ δ ^ (-ζ₂) * 2 ^ a * δ ^ 2 := hcτ
        _ ≤ δ ^ (-ζ₂) * (fibP j).card * δ ^ 2 := by gcongr
  · -- Katz–Tao of the `P` in `R l`
    obtain ⟨i₁, hi₁, -, -, hiffR⟩ := hfibR l
    set Fs := S.filter (fun i => lineCell (ρ / 20) (x i) (v i) = lineCell (ρ / 20) (x i₁) (v i₁) ∧
      A i ⊆ W) with hFs
    set JW := Finset.univ.filter (fun j => P j ⊆ R l ∧ P j ⊆ W) with hJW
    have hsum : ∑ j ∈ JW, (fibP j).card ≤ Fs.card := by
      apply sum_card_le_of_disjoint JW fibP Fs (fun j _ j' _ hne => hdisjP j j' hne)
      intro j hj i hi
      obtain ⟨-, hjR, hjW⟩ := Finset.mem_filter.1 hj
      obtain ⟨hiS, hiP⟩ := Finset.mem_filter.1 hi
      exact Finset.mem_filter.2 ⟨hiS, (hiffR i hiS).1 (hiP.trans hjR), hiP.trans hjW⟩
    have hJWcnt : JW.card * 2 ^ a ≤ Fs.card := by
      calc JW.card * 2 ^ a = ∑ _j ∈ JW, 2 ^ a := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ j ∈ JW, (fibP j).card := Finset.sum_le_sum fun j _ => (hfibPcard j).1
        _ ≤ Fs.card := hsum
    have hcnt : Set.ncard {j | P j ⊆ R l ∧ P j ⊆ W} = JW.card :=
      ncard_fin_filter (fun j => P j ⊆ R l ∧ P j ⊆ W)
    change ENNReal.ofReal (Set.ncard {j | P j ⊆ R l ∧ P j ⊆ W} * τ ^ 2) ≤
      ENNReal.ofReal (δ ^ (-ζ₂)) * volume W
    rw [hcnt]
    have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
    have ha : (0 : ℝ) < 2 ^ a := by positivity
    have hJWr : (JW.card : ℝ) * 2 ^ a ≤ Fs.card := by exact_mod_cast hJWcnt
    refine ofReal_scale (A := (Fs.card : ℝ) * δ ^ 2) (k := τ ^ 2 / (2 ^ a * δ ^ 2)) (c := c)
      (by positivity) hc0 (hKT i₁ hi₁ W hW) ?_ ?_
    · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      calc (JW.card : ℝ) * τ ^ 2 * (2 ^ a * δ ^ 2) = (JW.card * 2 ^ a) * (τ ^ 2 * δ ^ 2) := by ring
        _ ≤ Fs.card * (τ ^ 2 * δ ^ 2) := by gcongr
        _ = τ ^ 2 * (Fs.card * δ ^ 2) := by ring
    · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc τ ^ 2 * c = c * τ ^ 2 := by ring
        _ ≤ δ ^ (-ζ₂) * 2 ^ a * δ ^ 2 := hcτ
        _ = δ ^ (-ζ₂) * (2 ^ a * δ ^ 2) := by ring
  · -- fullness
    change δ ^ ζ₂ * (ρ / τ) ^ 2 ≤ (Set.ncard {j | P j ⊆ R l} : ℝ)
    rw [hcntJ]
    have hl1 : ((fibR l).card : ℝ) ≤ (J l).card * 2 ^ (a + 1) := by exact_mod_cast hJlower l
    have hl2 : (2 : ℝ) ^ b ≤ (fibR l).card := by exact_mod_cast (hfibRcard l).1
    have ha : (0 : ℝ) < 2 ^ (a + 1) := by positivity
    have : δ ^ ζ₂ * (ρ / τ) ^ 2 * 2 ^ (a + 1) ≤ (J l).card * 2 ^ (a + 1) := by linarith
    exact le_of_mul_le_mul_right this ha
  · -- Frostman of the coarse tubes
    set L := Finset.univ.filter (fun l => R l ⊆ W) with hLdef
    set FW := S.filter (fun i => A i ⊆ W) with hFW
    have hsum : ∑ l ∈ L, (fibR l).card ≤ FW.card := by
      apply sum_card_le_of_disjoint L fibR FW (fun l _ l' _ hne => hdisjR l l' hne)
      intro l hl i hi
      obtain ⟨hiS, hiR⟩ := Finset.mem_filter.1 hi
      exact Finset.mem_filter.2 ⟨hiS, hiR.trans (Finset.mem_filter.1 hl).2⟩
    have hLcnt : L.card * 2 ^ b ≤ FW.card := by
      calc L.card * 2 ^ b = ∑ _l ∈ L, 2 ^ b := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ l ∈ L, (fibR l).card := Finset.sum_le_sum fun l _ => (hfibRcard l).1
        _ ≤ FW.card := hsum
    -- `|S| < q 2^(b+1)`
    have hScov : S ⊆ Finset.univ.biUnion fibR := by
      intro i hi
      obtain ⟨l, hl, -⟩ := hexuR i hi
      exact Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, Finset.mem_filter.2 ⟨hi, hl⟩⟩
    have hScard : S.card ≤ q * 2 ^ (b + 1) := by
      calc S.card ≤ (Finset.univ.biUnion fibR).card := Finset.card_le_card hScov
        _ ≤ ∑ l, (fibR l).card := Finset.card_biUnion_le
        _ ≤ ∑ _l : Fin q, 2 ^ (b + 1) := Finset.sum_le_sum fun l _ => (hfibRcard l).2.le
        _ = q * 2 ^ (b + 1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hcnt : Set.ncard {l | R l ⊆ W} = L.card := ncard_fin_filter (fun l => R l ⊆ W)
    change ENNReal.ofReal (Set.ncard {l | R l ⊆ W} : ℝ) ≤ ENNReal.ofReal (δ ^ (-ζ₂) * q) * volume W
    rw [hcnt]
    have hb : (0 : ℝ) < 2 ^ b := by positivity
    have hLr : (L.card : ℝ) * 2 ^ b ≤ FW.card := by exact_mod_cast hLcnt
    have hSr : (S.card : ℝ) ≤ q * 2 ^ (b + 1) := by exact_mod_cast hScard
    refine ofReal_scale (A := (FW.card : ℝ)) (k := 1 / 2 ^ b) (c := KF * S.card) (by positivity)
      (mul_nonneg hKF0 (Nat.cast_nonneg _)) (hFG W hW) ?_ ?_
    · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hb]; exact hLr
    · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hb]
      calc KF * S.card ≤ KF * (q * 2 ^ (b + 1)) := mul_le_mul_of_nonneg_left hSr hKF0
        _ = (2 * KF) * q * 2 ^ b := by ring
        _ ≤ δ ^ (-ζ₂) * q * 2 ^ b :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKF (Nat.cast_nonneg _))
              hb.le

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
