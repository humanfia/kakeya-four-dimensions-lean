-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale.Regularization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0572, Multiscale/Regularization.lean; namespace renamed.
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Refinement

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale

attribute [local instance] Classical.propDecidable

open WangZahlLot.Obl.wz_tower_balanced_refinement
open scoped BigOperators ENNReal

/-- Simultaneously balance a finite family of partitions. Unlike nested
regularization, this permits unrelated point, line, and incidence partitions;
the price is a power of the number of size colors. -/
theorem regularize_finite_partitions {α I : Type*} [DecidableEq α]
    [Fintype I] [DecidableEq I] [Nonempty I]
    {Y : I → Type*} [∀ i, DecidableEq (Y i)]
    (H : Finset α) (hH : H.Nonempty) (f : ∀ i, α → Y i)
    {q : ℕ} (hq : 0 < q) (color : ℕ → Fin q)
    (hcolor : ∀ a b : ℕ, 0 < a → a ≤ H.card → 0 < b → b ≤ H.card →
      color a = color b → (a : ℝ) ≤ 2 * b) :
    ∃ S ⊆ H, S.Nonempty ∧
      (H.card : ℝ) ≤ 2 * (q : ℝ) ^ Fintype.card I * S.card ∧
      ∀ i, Balanced S (f i) (8 * Fintype.card I * (q : ℝ) ^ Fintype.card I) := by
  classical
  let Q := Fintype.card (I → Fin q)
  have hQ : 0 < Q := by simp only [Q, Fintype.card_fun, Fintype.card_fin]; positivity
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hJ : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  let e := Fintype.equivFin (I → Fin q)
  let c : α → Fin Q := fun x => e (fun i => color (leafFiber H (f i) x).card)
  obtain ⟨b, hb⟩ := weighted_color hQ H c (fun _ => 1)
  let U := H.filter (fun x => c x = b)
  have hUH : U ⊆ H := Finset.filter_subset _ _
  have hmass : (H.card : ℝ) ≤ (Q : ℝ) * U.card := by
    have hn : H.card ≤ Q * U.card := by
      have hh : (H.card : ENNReal) ≤ (Q : ENNReal) * U.card := by
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hb
      exact_mod_cast hh
    exact_mod_cast hn
  have hHp : 0 < (H.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hH
  have hUp : 0 < (U.card : ℝ) := by
    by_contra hn
    have hn' := not_lt.mp hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hQR.le hn'
    linarith
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (show 0 < U.card by exact_mod_cast hUp)
  have hsame (i : I) (x : α) (hx : x ∈ U) (y : α) (hy : y ∈ U) :
      color (leafFiber H (f i) x).card = color (leafFiber H (f i) y).card := by
    have hc : c x = c y := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    exact congrFun (e.injective hc) i
  have hcompare (i : I) (x : α) (hx : x ∈ U) (y : α) (hy : y ∈ U) :
      ((leafFiber H (f i) x).card : ℝ) ≤ 2 * (leafFiber H (f i) y).card :=
    hcolor _ _ (leafFiber_pos (f i) (hUH hx)) (leafFiber_card_le _ _ _)
      (leafFiber_pos (f i) (hUH hy)) (leafFiber_card_le _ _ _) (hsame i x hx y hy)
  let M : I → ℝ := fun i => (leafFiber H (f i) x₀).card
  have hM : ∀ i, 0 < M i := fun i => by
    dsimp [M]
    exact_mod_cast leafFiber_pos (f i) (hUH hx₀)
  have hfilt (T : Finset α) (i : I) (y : α) :
      T.filter (fun z => f i z = f i y) = leafFiber T (f i) y := by
    ext z
    simp [leafFiber]
  have himage (i : I) : M i * ((U.image (f i)).card : ℝ) ≤ 2 * H.card := by
    have hsum : (∑ a ∈ H.image (f i), ((H.filter (fun x => f i x = a)).card : ℝ)) = H.card := by
      exact_mod_cast (Finset.card_eq_sum_card_image (f i) H).symm
    have hsumle : (∑ a ∈ U.image (f i), ((H.filter (fun x => f i x = a)).card : ℝ)) ≤ H.card := by
      calc
        _ ≤ ∑ a ∈ H.image (f i), ((H.filter (fun x => f i x = a)).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_image hUH)
            (fun _ _ _ => Nat.cast_nonneg _)
        _ = _ := hsum
    calc
      M i * ((U.image (f i)).card : ℝ) = ∑ _a ∈ U.image (f i), M i := by simp [mul_comm]
      _ ≤ ∑ a ∈ U.image (f i), 2 * ((H.filter (fun x => f i x = a)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        rw [hfilt]
        exact hcompare i x₀ hx₀ x hx
      _ = 2 * ∑ a ∈ U.image (f i), ((H.filter (fun x => f i x = a)).card : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * H.card := mul_le_mul_of_nonneg_left hsumle (by norm_num)
  let t : I → ℝ := fun i => M i / (4 * Fintype.card I * Q)
  have hden : 0 < 4 * (Fintype.card I : ℝ) * Q := by positivity
  have ht : ∀ i, 0 ≤ t i := fun i => (div_pos (hM i) hden).le
  have hcost : (∑ i, t i * ((U.image (f i)).card : ℝ)) ≤ (U.card : ℝ) / 2 := by
    calc
      _ ≤ ∑ _i : I, (H.card : ℝ) / (2 * Fintype.card I * Q) := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          t i * ((U.image (f i)).card : ℝ) =
              (M i * ((U.image (f i)).card : ℝ)) / (4 * Fintype.card I * Q) := by dsimp [t]; ring
          _ ≤ (2 * H.card) / (4 * Fintype.card I * Q) :=
            div_le_div_of_nonneg_right (himage i) hden.le
          _ = _ := by ring
      _ = (H.card : ℝ) / (2 * Q) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
      _ ≤ (U.card : ℝ) / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * (Q : ℝ))).mpr
        nlinarith only [hmass]
  obtain ⟨S, hSU, hScard, hfiber⟩ :=
    WangZahlLot.Obl.wz_separated_projection_dichotomy.exists_dense_fiber_refinement U f t ht
  have hret : (U.card : ℝ) ≤ 2 * S.card := by linarith
  have hSp : 0 < (S.card : ℝ) := by linarith
  have hQeq : (Q : ℝ) = (q : ℝ) ^ Fintype.card I := by
    simp only [Q, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  refine ⟨S, hSU.trans hUH, Finset.card_pos.mp (by exact_mod_cast hSp), ?_, ?_⟩
  · rw [← hQeq]
    exact hmass.trans (by nlinarith only [mul_le_mul_of_nonneg_left hret hQR.le])
  · intro i x hx y hy
    have hlow := hfiber i y hy
    have hlow' : M i ≤ ((S.filter (fun z => f i z = f i y)).card : ℝ) *
        (4 * Fintype.card I * Q) := (div_le_iff₀ hden).mp hlow
    have hu : ((leafFiber S (f i) x).card : ℝ) ≤ 2 * M i := by
      calc
        _ ≤ ((leafFiber H (f i) x).card : ℝ) := by
          apply Nat.cast_le.mpr
          apply Finset.card_le_card
          intro z hz
          simp only [leafFiber, Finset.mem_filter] at hz ⊢
          exact ⟨hUH (hSU hz.1), hz.2⟩
        _ ≤ 2 * M i := hcompare i x (hSU hx) x₀ hx₀
    rw [← hQeq]
    rw [hfilt] at hlow'
    nlinarith only [hu, hlow']

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale
