-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BalancedSlab.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CoverSize

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open Finset MeasureTheory

noncomputable section

/-- A balanced assignment controls the number of selected target fibers. -/
theorem balanced_assignment_count {n L : ℕ} (S : Finset (Fin n)) (g : Fin n → Fin L)
    {K : ℝ} (hK : 0 ≤ K)
    (hbal : ∀ j j', ((S.filter fun i => g i = j).card : ℝ) ≤
      K * (S.filter fun i => g i = j').card) (B : Finset (Fin L)) :
    (B.card : ℝ) * S.card ≤ K * L * (S.filter fun i => g i ∈ B).card := by
  classical
  have hsum : (∑ j : Fin L, ((S.filter fun i => g i = j).card : ℝ)) = S.card := by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise
      (s := S) (t := univ) (f := g) (by intro i hi; exact mem_univ _)).symm
  have hlow (j' : Fin L) : (S.card : ℝ) ≤ K * L * (S.filter fun i => g i = j').card := by
    rw [← hsum]
    calc
      _ ≤ ∑ _j : Fin L, K * (S.filter fun i => g i = j').card :=
        sum_le_sum fun j _ => hbal j j'
      _ = _ := by simp; ring
  have hsumB : (∑ j ∈ B, ((S.filter fun i => g i = j).card : ℝ)) =
      (S.filter fun i => g i ∈ B).card := by
    exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter S B g
  calc
    _ = ∑ _j ∈ B, (S.card : ℝ) := by simp
    _ ≤ ∑ j ∈ B, K * L * (S.filter fun i => g i = j).card := sum_le_sum fun j _ => hlow j
    _ = _ := by rw [← mul_sum, hsumB]

/-- Comparable weights remain comparable after summation over balanced groups. -/
theorem comparable_group_sums {α : Type*} [DecidableEq α] (A B : Finset α)
    (hB : B.Nonempty) (a : α → ℝ) {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K)
    (ha : ∀ j ∈ B, 0 ≤ a j) (hcmp : ∀ i ∈ A, ∀ j ∈ B, a i ≤ H * a j)
    (hcard : (A.card : ℝ) ≤ K * B.card) :
    (∑ i ∈ A, a i) ≤ H * K * ∑ i ∈ B, a i := by
  obtain ⟨j, hj, hmin⟩ := exists_min_image B a hB
  have hlo : (B.card : ℝ) * a j ≤ ∑ i ∈ B, a i := by
    calc
      _ = ∑ _i ∈ B, a j := by simp
      _ ≤ _ := sum_le_sum fun i hi => hmin i hi
  calc
    _ ≤ ∑ _i ∈ A, H * a j := sum_le_sum fun i hi => hcmp i hi j hj
    _ = H * a j * A.card := by simp [mul_comm]
    _ ≤ H * a j * (K * B.card) :=
      mul_le_mul_of_nonneg_left hcard (mul_nonneg hH (ha j hj))
    _ = H * K * (B.card * a j) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (mul_nonneg hH hK)

/-- Composing two balanced assignments multiplies their errors. -/
theorem balanced_assignment_comp {n N L : ℕ} (S : Finset (Fin n)) (U : Finset (Fin N))
    (hU : U.Nonempty) (f : Fin n → Fin N) (g : Fin N → Fin L)
    {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) (hSU : ∀ i ∈ S, f i ∈ U)
    (hf : ∀ k ∈ U, ∀ k' ∈ U, ((S.filter fun i => f i = k).card : ℝ) ≤
      H * (S.filter fun i => f i = k').card)
    (hg : ∀ j j', ((U.filter fun k => g k = j).card : ℝ) ≤
      K * (U.filter fun k => g k = j').card) :
    ∀ j j', ((S.filter fun i => g (f i) = j).card : ℝ) ≤
      (H * K) * (S.filter fun i => g (f i) = j').card := by
  classical
  have hsum (j : Fin L) :
      (∑ k ∈ U.filter (fun k => g k = j), ((S.filter fun i => f i = k).card : ℝ)) =
        (S.filter fun i => g (f i) = j).card := by
    have he : (S.filter fun i => f i ∈ U.filter (fun k => g k = j)) =
        S.filter (fun i => g (f i) = j) := by
      ext i
      simp only [mem_filter]
      constructor
      · rintro ⟨hi, -, hg⟩; exact ⟨hi, hg⟩
      · rintro ⟨hi, hg⟩; exact ⟨hi, hSU i hi, hg⟩
    rw [← he]
    exact_mod_cast sum_card_fiberwise_eq_card_filter S (U.filter fun k => g k = j) f
  intro j j'
  obtain ⟨k', hk'U, hkj'⟩ := balanced_fibers_nonempty U hU g hg j'
  rw [← hsum j, ← hsum j']
  exact comparable_group_sums _ _ ⟨k', mem_filter.mpr ⟨hk'U, hkj'⟩⟩ _ hH hK
    (by intros; positivity)
    (fun k hk k' hk' => hf k (mem_filter.mp hk).1 k' (mem_filter.mp hk').1) (hg j j')

/-- Keeping complete intermediate fibers preserves the balance needed for composition. -/
theorem balanced_selected_assignment_comp {n N L : ℕ} (S : Finset (Fin n))
    (U : Finset (Fin N)) (hU : U.Nonempty) (f : Fin n → Fin N) (g : Fin N → Fin L)
    {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hf : ∀ k k', ((S.filter fun i => f i = k).card : ℝ) ≤
      H * (S.filter fun i => f i = k').card)
    (hg : ∀ j j', ((U.filter fun k => g k = j).card : ℝ) ≤
      K * (U.filter fun k => g k = j').card) :
    ∀ j j', (((S.filter fun i => f i ∈ U).filter fun i => g (f i) = j).card : ℝ) ≤
      (H * K) * ((S.filter fun i => f i ∈ U).filter fun i => g (f i) = j').card := by
  classical
  have he (k) (hk : k ∈ U) : ((S.filter fun i => f i ∈ U).filter fun i => f i = k) =
      S.filter (fun i => f i = k) := by
    ext i
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨hi, -⟩, hf⟩; exact ⟨hi, hf⟩
    · rintro ⟨hi, hf⟩; exact ⟨⟨hi, hf ▸ hk⟩, hf⟩
  apply balanced_assignment_comp _ U hU f g hH hK (fun i hi => (mem_filter.mp hi).2)
  · intro k hk k' hk'
    rw [he k hk, he k' hk']
    exact hf k k'
  · exact hg

namespace Interfaces

/-- The slab count passes from a retained fine family to any balanced covering family.
The targets may be long carriers and need not lie in the unit ball. -/
theorem slab_count_of_balanced_cover {δ l K D : ℝ} {n L : ℕ}
    {x v : Fin n → V} (S : Finset (Fin n)) (hS : S.Nonempty)
    (g : Fin n → Fin L) (W : Fin L → Set V)
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hl : 0 ≤ l)
    (hball : ∀ i ∈ S, T δ (x i) (v i) ⊆ I)
    (hcover : ∀ i ∈ S, T δ (x i) (v i) ⊆ W (g i))
    (hbal : ∀ j j', ((S.filter fun i => g i = j).card : ℝ) ≤
      K * (S.filter fun i => g i = j').card)
    (hcard : (n : ℝ) ≤ D * S.card) (hF : F δ l n x v) :
    ∀ (u : V) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      o (q {j | W j ⊆ {p | |inner ℝ u p - t| ≤ r}}) ≤
        o (K * D * l * L) * μ (I ∩ {p | |inner ℝ u p - t| ≤ r}) := by
  classical
  intro u t r hu hr
  let B := univ.filter fun j => W j ⊆ {p | |inner ℝ u p - t| ≤ r}
  let C := univ.filter fun i => T δ (x i) (v i) ⊆ I ∩ {p | |inner ℝ u p - t| ≤ r}
  let Vslab := I ∩ {p | |inner ℝ u p - t| ≤ r}
  have hvol : μ Vslab ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ball_lt_top : volume (Metric.ball (0 : V) 1) < ⊤).ne
      (measure_mono Set.inter_subset_left)
  have hcnt : (S.filter fun i => g i ∈ B).card ≤ C.card := by
    apply card_le_card
    intro i hi
    obtain ⟨hiS, hig⟩ := mem_filter.mp hi
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    exact Set.subset_inter (hball i hiS) ((hcover i hiS).trans (mem_filter.mp hig).2)
  have hs : (0 : ℝ) < S.card := Nat.cast_pos.mpr (card_pos.mpr hS)
  have hf : (C.card : ℝ) ≤ l * n * (μ Vslab).toReal := by
    have hh := hF u t r hu hr
    have he : {i | T δ (x i) (v i) ⊆ I ∩ {p | |inner ℝ u p - t| ≤ r}} = (C : Set (Fin n)) := by
      ext i
      simp [C]
    change ENNReal.ofReal (({i | T δ (x i) (v i) ⊆ I ∩ {p | |inner ℝ u p - t| ≤ r}}.ncard : ℝ)) ≤
      o (l * n) * μ Vslab at hh
    rw [he, Set.ncard_coe_finset] at hh
    have hn : o (l * n) * μ Vslab ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol
    have ht := ENNReal.toReal_mono hn hh
    simpa only [o, ENNReal.toReal_ofReal
      (by positivity : (0 : ℝ) ≤ (C.card : ℝ)), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ l * n)] using ht
  have hreal : (B.card : ℝ) ≤ K * D * l * L * (μ Vslab).toReal := by
    have hh : (B.card : ℝ) * S.card ≤ (K * D * l * L * (μ Vslab).toReal) * S.card := by
      calc
        _ ≤ K * L * (S.filter fun i => g i ∈ B).card := balanced_assignment_count S g hK hbal B
        _ ≤ K * L * C.card := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcnt) (by positivity)
        _ ≤ K * L * (l * n * (μ Vslab).toReal) := mul_le_mul_of_nonneg_left hf (by positivity)
        _ ≤ K * L * (l * (D * S.card) * (μ Vslab).toReal) := by gcongr
        _ = _ := by ring
    nlinarith
  have he : q {j | W j ⊆ {p | |inner ℝ u p - t| ≤ r}} = (B.card : ℝ) := by
    have hb : {j | W j ⊆ {p | |inner ℝ u p - t| ≤ r}} = (B : Set (Fin L)) := by
      ext j
      simp [B]
    simp only [q, hb, Set.ncard_coe_finset]
  rw [he]
  have hh := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hvol] at hh
  exact hh

end Interfaces

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
