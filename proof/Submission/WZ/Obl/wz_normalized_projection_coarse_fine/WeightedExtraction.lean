-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.WeightedExtraction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.DyadicExtraction

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A finite coloring has a color carrying the average real weight. -/
lemma weighted_color_real {α : Type*} [DecidableEq α] {q : ℕ} (hq : 0 < q)
    (S : Finset α) (c : α → Fin q) (w : α → ℝ) :
    ∃ b : Fin q, (∑ i ∈ S, w i) ≤ q * ∑ i ∈ S.filter (fun i => c i = b), w i := by
  classical
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun b : Fin q => ∑ i ∈ S.filter (fun i => c i = b), w i) Finset.univ_nonempty
  refine ⟨b, ?_⟩
  calc
    (∑ i ∈ S, w i) = ∑ b : Fin q, ∑ i ∈ S.filter (fun i => c i = b), w i := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
    _ ≤ ∑ _b : Fin q, ∑ i ∈ S.filter (fun i => c i = b), w i :=
      Finset.sum_le_sum fun a ha => hmax a ha
    _ = q * ∑ i ∈ S.filter (fun i => c i = b), w i := by simp

/-- Comparable weights turn a cardinality selection into a weighted selection. -/
lemma sum_le_of_card_le_of_comparable {α : Type*} [DecidableEq α]
    (S V : Finset α) (hVS : V ⊆ S) (w : α → ℝ) {R D : ℝ}
    (hD : 0 ≤ D) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hcomp : ∀ i ∈ S, ∀ j ∈ S, w i ≤ R * w j)
    (hcard : (S.card : ℝ) ≤ D * V.card) :
    (∑ i ∈ S, w i) ≤ R * D * ∑ i ∈ V, w i := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · have hV : V = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun i hi => by
      simpa using hVS hi
    simp [hV]
  obtain ⟨a, ha, hmax⟩ := S.exists_max_image w hS
  have hVsum : (V.card : ℝ) * w a ≤ R * ∑ i ∈ V, w i := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (fun i hi => hcomp a ha i (hVS hi))
  calc
    (∑ i ∈ S, w i) ≤ (S.card : ℝ) * w a := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i hi => hmax i hi)
    _ ≤ (D * V.card) * w a := mul_le_mul_of_nonneg_right hcard (hw a ha)
    _ = D * ((V.card : ℝ) * w a) := by ring
    _ ≤ D * (R * ∑ i ∈ V, w i) := mul_le_mul_of_nonneg_left hVsum hD
    _ = _ := by ring

/-- Uniform cardinality extraction on every subset gives weighted extraction.
There are only `q` weight bins once `R ^ q` exceeds twice the ambient cardinality. -/
theorem weighted_extraction_of_cardinality {α : Type*} [DecidableEq α]
    (U : Finset α) (w : α → ℝ) (P : Finset α → Prop)
    {q : ℕ} (hq : 0 < q) {R D : ℝ} (hR : 1 < R) (hD : 0 ≤ D)
    (hsize : 2 * (U.card : ℝ) < R ^ q)
    (hw : ∀ i ∈ U, 0 ≤ w i)
    (hselect : ∀ S ⊆ U, ∃ V ⊆ S, P V ∧ (S.card : ℝ) ≤ D * V.card) :
    ∃ V ⊆ U, P V ∧ (∑ i ∈ U, w i) ≤
      (2 * q * R * D) * ∑ i ∈ V, w i := by
  classical
  let W := ∑ i ∈ U, w i
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  by_cases hWp : 0 < W
  swap
  · obtain ⟨V, hVU, hPV, _⟩ := hselect U (Finset.Subset.refl _)
    refine ⟨V, hVU, hPV, ?_⟩
    have hsum : 0 ≤ ∑ i ∈ V, w i := Finset.sum_nonneg fun i hi => hw i (hVU hi)
    have hR0 : 0 ≤ R := by linarith
    exact (not_lt.mp hWp).trans (by positivity)
  have hUn : 0 < (U.card : ℝ) := by
    have hU : U.Nonempty := by
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      simp only [W, he, Finset.sum_empty] at hWp
      exact (lt_irrefl _ hWp)
    exact_mod_cast Finset.card_pos.mpr hU
  let τ := W / (2 * U.card)
  have hτ : 0 < τ := div_pos hWp (mul_pos (by norm_num) hUn)
  have hτeq : 2 * U.card * τ = W := by
    dsimp [τ]
    field_simp
  let E := U.filter fun i => τ ≤ w i
  have hEU : E ⊆ U := Finset.filter_subset _ _
  have hlow : (∑ i ∈ U \ E, w i) ≤ (U.card : ℝ) * τ := by
    calc
      _ ≤ ∑ _i ∈ U \ E, τ := Finset.sum_le_sum fun i hi => by
        obtain ⟨hiU, hiE⟩ := Finset.mem_sdiff.mp hi
        exact (not_le.mp (fun h => hiE (Finset.mem_filter.mpr ⟨hiU, h⟩))).le
      _ = ((U \ E).card : ℝ) * τ := by simp
      _ ≤ (U.card : ℝ) * τ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : U \ E ⊆ U)) hτ.le
  have hEmass : W ≤ 2 * ∑ i ∈ E, w i := by
    have he := Finset.sum_sdiff hEU (f := w)
    change (∑ i ∈ U \ E, w i) + ∑ i ∈ E, w i = W at he
    linarith
  have hbounds (i : α) (hi : i ∈ E) : 1 ≤ w i / τ ∧ w i / τ < R ^ q := by
    have hiU := hEU hi
    have hl : τ ≤ w i := (Finset.mem_filter.mp hi).2
    have hu : w i ≤ W := Finset.single_le_sum hw hiU
    refine ⟨(one_le_div hτ).mpr hl, ?_⟩
    apply lt_of_le_of_lt _ hsize
    apply (div_le_iff₀ hτ).mpr
    nlinarith [hτeq]
  have hex (i : α) (hi : i ∈ E) := exists_nat_pow_near (hbounds i hi).1 hR
  let c : α → Fin q := fun i => if hi : i ∈ E then
    ⟨Nat.find (hex i hi), by
      apply (pow_lt_pow_iff_right₀ hR).mp
      exact (Nat.find_spec (hex i hi)).1.trans_lt (hbounds i hi).2⟩
    else ⟨0, hq⟩
  have hcomp : ∀ i ∈ E, ∀ j ∈ E, c i = c j → w i ≤ R * w j := by
    intro i hi j hj hc
    have he : Nat.find (hex i hi) = Nat.find (hex j hj) := by
      simpa only [c, dite_eq_left hi, dite_eq_left hj] using congrArg Fin.val hc
    have hi' := (Nat.find_spec (hex i hi)).2
    have hj' := (Nat.find_spec (hex j hj)).1
    rw [he, pow_succ] at hi'
    have hR0 : 0 ≤ R := by linarith
    have hh : w i / τ ≤ R * (w j / τ) := by
      calc
        _ ≤ R ^ Nat.find (hex j hj) * R := hi'.le
        _ ≤ (w j / τ) * R := mul_le_mul_of_nonneg_right hj' hR0
        _ = _ := mul_comm _ _
    have hh' := (div_le_iff₀ hτ).mp hh
    calc
      w i ≤ (R * (w j / τ)) * τ := hh'
      _ = R * w j := by field_simp
  obtain ⟨b, hb⟩ := weighted_color_real hq E c w
  let S := E.filter fun i => c i = b
  have hSE : S ⊆ E := Finset.filter_subset _ _
  obtain ⟨V, hVS, hPV, hcard⟩ := hselect S (hSE.trans hEU)
  have hs : (∑ i ∈ S, w i) ≤ R * D * ∑ i ∈ V, w i :=
    sum_le_of_card_le_of_comparable S V hVS w hD
      (fun i hi => hw i (hEU (hSE hi)))
      (fun i hi j hj => hcomp i (hSE hi) j (hSE hj)
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)) hcard
  refine ⟨V, hVS.trans (hSE.trans hEU), hPV, ?_⟩
  calc
    W ≤ 2 * ∑ i ∈ E, w i := hEmass
    _ ≤ 2 * (q * ∑ i ∈ S, w i) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 2 * (q * (R * D * ∑ i ∈ V, w i)) := by gcongr
    _ = _ := by ring

/-- A dyadic family with linear quotas up to a factor `D` admits uniform
cardinality extraction on every subfamily. -/
theorem dyadic_cardinality_extraction {α : Type*} [DecidableEq α] {d : ℕ}
    (U : Finset α) (q : α → EuclideanSpace ℝ (Fin d)) (J : ℕ)
    {D : ℝ} (hD : 1 ≤ D)
    (hcount : ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
      ((U.filter (fun a => dyadicLabel k (q a) = l)).card : ℝ) ≤ D * (2 : ℝ) ^ (J - k))
    (S : Finset α) (hSU : S ⊆ U) :
    ∃ V ⊆ S, (S.card : ℝ) ≤ D * ((3 : ℝ) ^ d + 1) * V.card ∧
      (∀ a ∈ V, ∀ b ∈ V, a ≠ b → ((2 : ℝ) ^ J)⁻¹ ≤ dist (q a) (q b)) ∧
      ∀ (q₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ), ((2 : ℝ) ^ J)⁻¹ ≤ r → r ≤ 1 →
        ((V.filter (fun a => q a ∈ Metric.ball q₀ r)).card : ℝ) ≤
          2 * (3 : ℝ) ^ d * (r / ((2 : ℝ) ^ J)⁻¹) := by
  classical
  have hD0 : 0 < D := by linarith
  have hcap : ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
      (∑ _a ∈ S.filter (fun a => dyadicLabel k (q a) = l), 1 / D) ≤ (2 : ℝ) ^ (J - k) := by
    intro k hk l
    have hc : ((S.filter (fun a => dyadicLabel k (q a) = l)).card : ℝ) ≤
        D * (2 : ℝ) ^ (J - k) :=
      (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hSU))).trans
        (hcount k hk l)
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one_div] using
      (div_le_iff₀ hD0).mpr (by nlinarith :
        ((S.filter (fun a => dyadicLabel k (q a) = l)).card : ℝ) ≤ (2 : ℝ) ^ (J - k) * D)
  obtain ⟨Q, hQS, hmass, hQcap⟩ := dyadic_weighted_extraction S q J (fun _ => 1 / D)
    (fun _ _ => ⟨by positivity, (div_le_one hD0).mpr hD⟩) hcap
  have hSQ : (S.card : ℝ) ≤ D * Q.card := by
    have hm : (S.card : ℝ) / D ≤ Q.card := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one_div] using hmass
    have hh := (div_le_iff₀ hD0).mp hm
    nlinarith
  have hlocal (a : α) :
      (Q.filter (fun b => q b ∈ Metric.ball (q a) (((2 : ℝ) ^ J)⁻¹))).card ≤ 3 ^ d := by
    apply dyadic_extraction_ball_count Q q
    intro l
    simpa using hQcap J le_rfl l
  obtain ⟨V, hVQ, hVmass, hVsep⟩ := separated_weighted_subset Q q (fun _ => 1)
    (K := 3 ^ d) (fun a _ => hlocal a)
  have hQV : (Q.card : ℝ) ≤ ((3 : ℝ) ^ d + 1) * V.card := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one] using hVmass
  refine ⟨V, hVQ.trans hQS, ?_, hVsep, ?_⟩
  · calc
      (S.card : ℝ) ≤ D * Q.card := hSQ
      _ ≤ D * (((3 : ℝ) ^ d + 1) * V.card) := mul_le_mul_of_nonneg_left hQV hD0.le
      _ = _ := by ring
  · intro q₀ r hδr hr1
    have hc : (V.filter (fun a => q a ∈ Metric.ball q₀ r)).card ≤
        (Q.filter (fun a => q a ∈ Metric.ball q₀ r)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ hVQ)
    exact (Nat.cast_le.mpr hc).trans (dyadic_quotas_ball_count Q q hQcap q₀ hδr hr1)

/-- Weighted separated Katz--Tao extraction from dyadic quotas. -/
theorem dyadic_weighted_separated_extraction {α : Type*} [DecidableEq α] {d : ℕ}
    (U : Finset α) (p : α → EuclideanSpace ℝ (Fin d)) (J : ℕ) (w : α → ℝ)
    {D R : ℝ} (hD : 1 ≤ D) (hR : 1 < R) {q : ℕ} (hq : 0 < q)
    (hsize : 2 * (U.card : ℝ) < R ^ q) (hw : ∀ i ∈ U, 0 ≤ w i)
    (hcount : ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
      ((U.filter (fun a => dyadicLabel k (p a) = l)).card : ℝ) ≤ D * (2 : ℝ) ^ (J - k)) :
    ∃ V ⊆ U,
      (∑ i ∈ U, w i) ≤ (2 * q * R * (D * ((3 : ℝ) ^ d + 1))) * ∑ i ∈ V, w i ∧
      (∀ a ∈ V, ∀ b ∈ V, a ≠ b → ((2 : ℝ) ^ J)⁻¹ ≤ dist (p a) (p b)) ∧
      ∀ (p₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ), ((2 : ℝ) ^ J)⁻¹ ≤ r → r ≤ 1 →
        ((V.filter (fun a => p a ∈ Metric.ball p₀ r)).card : ℝ) ≤
          2 * (3 : ℝ) ^ d * (r / ((2 : ℝ) ^ J)⁻¹) := by
  classical
  let P : Finset α → Prop := fun V =>
    (∀ a ∈ V, ∀ b ∈ V, a ≠ b → ((2 : ℝ) ^ J)⁻¹ ≤ dist (p a) (p b)) ∧
      ∀ (p₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ), ((2 : ℝ) ^ J)⁻¹ ≤ r → r ≤ 1 →
        ((V.filter (fun a => p a ∈ Metric.ball p₀ r)).card : ℝ) ≤
          2 * (3 : ℝ) ^ d * (r / ((2 : ℝ) ^ J)⁻¹)
  have hD0 : 0 ≤ D := by linarith
  obtain ⟨V, hVU, hP, hm⟩ := weighted_extraction_of_cardinality U w P hq hR
    (by positivity : 0 ≤ D * ((3 : ℝ) ^ d + 1)) hsize hw (by
      intro S hSU
      obtain ⟨V, hVS, hc, hsep, hcount'⟩ := dyadic_cardinality_extraction U p J hD hcount S hSU
      exact ⟨V, hVS, ⟨hsep, hcount'⟩, hc⟩)
  exact ⟨V, hVU, hm, hP.1, hP.2⟩

/-- Sublinear Frostman counts imply linear quotas with an explicit common loss. -/
lemma dyadic_frostman_linear_quota {α : Type*} [DecidableEq α] {d : ℕ}
    (U : Finset α) (p : α → EuclideanSpace ℝ (Fin d)) (J : ℕ)
    {K s : ℝ} (hK : 0 ≤ K) (hs : s ≤ 1)
    (hcount : ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
      ((U.filter (fun a => dyadicLabel k (p a) = l)).card : ℝ) ≤
        K * (((2 : ℝ) ^ k)⁻¹) ^ s * U.card) :
    ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
      ((U.filter (fun a => dyadicLabel k (p a) = l)).card : ℝ) ≤
        (K * (((2 : ℝ) ^ J)⁻¹) ^ s * U.card) * (2 : ℝ) ^ (J - k) := by
  intro k hk l
  let δ := ((2 : ℝ) ^ J)⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have he : ((2 : ℝ) ^ k)⁻¹ / δ = (2 : ℝ) ^ (J - k) := by
    dsimp [δ]
    have hpow : (2 : ℝ) ^ J = 2 ^ k * 2 ^ (J - k) := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    rw [div_inv_eq_mul, hpow, inv_mul_cancel_left₀ (by positivity)]
  have hr : 1 ≤ ((2 : ℝ) ^ k)⁻¹ / δ := by
    rw [he]
    exact one_le_pow₀ (by norm_num)
  calc
    _ ≤ K * (((2 : ℝ) ^ k)⁻¹) ^ s * U.card := hcount k hk l
    _ = (K * δ ^ s * U.card) * ((((2 : ℝ) ^ k)⁻¹ / δ) ^ s) := by
      rw [Real.div_rpow (by positivity) hδ.le]
      field_simp
    _ ≤ (K * δ ^ s * U.card) * (((2 : ℝ) ^ k)⁻¹ / δ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hr hs) (by positivity)
    _ = _ := by rw [he]

/-- The weighted extraction form needed for light-cell removal estimates.
The loss is proportional to `K * delta ^ s * #U`, not a loss of retained shadings. -/
theorem dyadic_frostman_weighted_separated_extraction {α : Type*} [DecidableEq α] {d : ℕ}
    (U : Finset α) (p : α → EuclideanSpace ℝ (Fin d)) (J : ℕ) (w : α → ℝ)
    {K s R : ℝ} (hK : 0 ≤ K) (hs : s ≤ 1) (hR : 1 < R)
    {q : ℕ} (hq : 0 < q) (hsize : 2 * (U.card : ℝ) < R ^ q)
    (hmin : 1 ≤ K * (((2 : ℝ) ^ J)⁻¹) ^ s * U.card)
    (hw : ∀ i ∈ U, 0 ≤ w i)
    (hcount : ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
      ((U.filter (fun a => dyadicLabel k (p a) = l)).card : ℝ) ≤
        K * (((2 : ℝ) ^ k)⁻¹) ^ s * U.card) :
    ∃ V ⊆ U,
      (∑ i ∈ U, w i) ≤
        (2 * q * R * (K * (((2 : ℝ) ^ J)⁻¹) ^ s * U.card * ((3 : ℝ) ^ d + 1))) *
          ∑ i ∈ V, w i ∧
      (∀ a ∈ V, ∀ b ∈ V, a ≠ b → ((2 : ℝ) ^ J)⁻¹ ≤ dist (p a) (p b)) ∧
      ∀ (p₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ), ((2 : ℝ) ^ J)⁻¹ ≤ r → r ≤ 1 →
        ((V.filter (fun a => p a ∈ Metric.ball p₀ r)).card : ℝ) ≤
          2 * (3 : ℝ) ^ d * (r / ((2 : ℝ) ^ J)⁻¹) :=
  dyadic_weighted_separated_extraction U p J w hmin hR hq hsize hw
    (dyadic_frostman_linear_quota U p J hK hs hcount)

/-- A cubic estimate on all separated linear-count subsets controls the mass of
an entire weighted dyadic family. -/
theorem dyadic_weighted_cubic_bound {α : Type*} [DecidableEq α] {d : ℕ}
    (U : Finset α) (p : α → EuclideanSpace ℝ (Fin d)) (J : ℕ) (w : α → ENNReal)
    {D R : ℝ} (hD : 1 ≤ D) (hR : 1 < R) {q : ℕ} (hq : 0 < q)
    (hsize : 2 * (U.card : ℝ) < R ^ q) (hw : ∀ i ∈ U, w i ≠ ⊤)
    (hcount : ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
      ((U.filter (fun a => dyadicLabel k (p a) = l)).card : ℝ) ≤ D * (2 : ℝ) ^ (J - k))
    {B : ENNReal}
    (hclass : ∀ V ⊆ U,
      (∀ a ∈ V, ∀ b ∈ V, a ≠ b → ((2 : ℝ) ^ J)⁻¹ ≤ dist (p a) (p b)) →
      (∀ (p₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ), ((2 : ℝ) ^ J)⁻¹ ≤ r → r ≤ 1 →
        ((V.filter (fun a => p a ∈ Metric.ball p₀ r)).card : ℝ) ≤
          2 * (3 : ℝ) ^ d * (r / ((2 : ℝ) ^ J)⁻¹)) → (∑ i ∈ V, w i) ^ 3 ≤ B) :
    (∑ i ∈ U, w i) ^ 3 ≤
      ENNReal.ofReal (2 * q * R * (D * ((3 : ℝ) ^ d + 1))) ^ 3 * B := by
  obtain ⟨V, hVU, hm, hsep, hcount'⟩ := dyadic_weighted_separated_extraction U p J
    (fun i => (w i).toReal) hD hR hq hsize (fun _ _ => ENNReal.toReal_nonneg) hcount
  have hsum (S : Finset α) (hSU : S ⊆ U) :
      ENNReal.ofReal (∑ i ∈ S, (w i).toReal) = ∑ i ∈ S, w i := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl fun i hi => ENNReal.ofReal_toReal (hw i (hSU hi))
  have hD0 : 0 ≤ D := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hm' := ENNReal.ofReal_le_ofReal hm
  rw [hsum U (Finset.Subset.refl _), ENNReal.ofReal_mul (by positivity), hsum V hVU] at hm'
  calc
    _ ≤ (ENNReal.ofReal (2 * q * R * (D * ((3 : ℝ) ^ d + 1))) * ∑ i ∈ V, w i) ^ 3 :=
      pow_le_pow_left' hm' 3
    _ = ENNReal.ofReal (2 * q * R * (D * ((3 : ℝ) ^ d + 1))) ^ 3 * (∑ i ∈ V, w i) ^ 3 :=
      mul_pow _ _ _
    _ ≤ _ := mul_le_mul' le_rfl (hclass V hVU hsep hcount')

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
