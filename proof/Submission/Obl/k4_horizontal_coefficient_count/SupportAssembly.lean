import Submission.Obl.k4_horizontal_coefficient_count.DepthSignal

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace DepthData

variable {α : Type} [MeasurableSpace α] {D : DepthData α}

/-- Turn whole-label counts and the original scalar interval cover into
a finite support list. The count is weighted before the time scale cancels. -/
theorem supportCount_of_block_counts (h : D.Hyp) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ (g : ℤ × ℤ × ℤ) (j : Fin (2 ^ D.T)) (S : Finset (Fin D.n)),
      (∀ i ∈ S, D.j i = j ∧ ∃ l ∈ D.B i,
        l ∈ groupSet D.b D.χ D.a g ∩ goodSet D.b D.K D.χ) →
      (S.card : ℝ) * D.a ^ D.d ≤ C)
    (hbins : ∀ center a R : ℝ, 0 < a → 0 ≤ R →
      ∃ J : Finset ℤ, (J.card : ℝ) ≤ 2 * R + 2 ∧
        ∀ y : ℝ, |y - center| ≤ R * a → ⌊y / a⌋ ∈ J) :
    D.SupportCount (3 * 64 * C * D.K ^ 2) := by
  classical
  have ha := h.ha0
  have hq := h.q_pos
  have hK : 0 ≤ D.K := by linarith [h.hK]
  have hW : 0 < D.a ^ D.d := Real.rpow_pos_of_pos ha _
  intro g
  let S : Finset (Fin D.n) := Finset.univ.filter (fun i => ∃ l ∈ D.B i,
    l ∈ groupSet D.b D.χ D.a g ∩ goodSet D.b D.K D.χ)
  have hS : (S.card : ℝ) * D.a ^ D.d ≤ (2 : ℝ) ^ D.T * C := by
    have hcard : (S.card : ℝ) = ∑ j : Fin (2 ^ D.T),
        ((S.filter (fun i => D.j i = j)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise
        (s := S) (t := Finset.univ) (fun i _ => Finset.mem_univ (D.j i))
    rw [hcard, Finset.sum_mul]
    calc
      _ ≤ ∑ _j : Fin (2 ^ D.T), C := by
        apply Finset.sum_le_sum
        intro j _
        apply hcount g j
        intro i hi
        obtain ⟨hiS, hij⟩ := Finset.mem_filter.mp hi
        exact ⟨hij, (Finset.mem_filter.mp hiS).2⟩
      _ = (2 : ℝ) ^ D.T * C := by simp
  choose I hIcard hIcover using fun i : Fin D.n =>
    hbins (D.midpoint (D.j i)) D.a (D.q / (2 * D.a)) ha (by positivity)
  have hIcard' (i : Fin D.n) : ((I i).card : ℝ) ≤ D.q / D.a + 2 := by
    convert hIcard i using 1 <;> field_simp <;> ring
  choose J hJcard hJcover using fun (i : Fin D.n) (τ : ℤ) =>
    hbins (D.labelSignal g i τ) D.a (31 * D.K ^ 2) ha (by positivity)
  have hJcard' (i : Fin D.n) (τ : ℤ) : ((J i τ).card : ℝ) ≤ 64 * D.K ^ 2 := by
    have hh := hJcard i τ
    nlinarith [h.hK]
  let Fi (i : Fin D.n) : Finset (ℤ × ℤ) :=
    (I i).biUnion (fun τ => ({τ} : Finset ℤ) ×ˢ J i τ)
  have hFi (i : Fin D.n) : ((Fi i).card : ℝ) ≤ (D.q / D.a + 2) * (64 * D.K ^ 2) := by
    have hc : ((Fi i).card : ℝ) ≤ ∑ τ ∈ I i, ((J i τ).card : ℝ) := by
      have hh := Finset.card_biUnion_le (s := I i)
        (t := fun τ => ({τ} : Finset ℤ) ×ˢ J i τ)
      simp only [Finset.card_product, Finset.card_singleton, one_mul] at hh
      exact_mod_cast hh
    calc
      _ ≤ ∑ τ ∈ I i, ((J i τ).card : ℝ) := hc
      _ ≤ ∑ _τ ∈ I i, 64 * D.K ^ 2 := Finset.sum_le_sum (fun τ _ => hJcard' i τ)
      _ = ((I i).card : ℝ) * (64 * D.K ^ 2) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (hIcard' i) (by positivity)
  let F : Finset (ℤ × ℤ) := S.biUnion Fi
  have hF : (F.card : ℝ) ≤ (S.card : ℝ) * ((D.q / D.a + 2) * (64 * D.K ^ 2)) := by
    have hc : (F.card : ℝ) ≤ ∑ i ∈ S, ((Fi i).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le (s := S) (t := Fi)
    exact hc.trans ((Finset.sum_le_sum (fun i _ => hFi i)).trans_eq (by simp))
  have hFweighted : (F.card : ℝ) * (D.a * D.a ^ D.d) ≤ 3 * 64 * C * D.K ^ 2 := by
    calc
      _ ≤ ((S.card : ℝ) * ((D.q / D.a + 2) * (64 * D.K ^ 2))) *
          (D.a * D.a ^ D.d) := mul_le_mul_of_nonneg_right hF (by positivity)
      _ = 64 * D.K ^ 2 * ((S.card : ℝ) * D.a ^ D.d) * (D.q + 2 * D.a) := by
        field_simp <;> ring
      _ ≤ 64 * D.K ^ 2 * ((2 : ℝ) ^ D.T * C) * (3 * D.q) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hS (by positivity)
        · linarith [h.a_le_q]
        · positivity
        · positivity
      _ = 3 * 64 * C * D.K ^ 2 := by
        calc
          _ = (3 * 64 * C * D.K ^ 2) * (D.q * (2 : ℝ) ^ D.T) := by ring
          _ = _ := by rw [h.hqT, mul_one]
  have hrpow : D.a ^ (-1 - D.d) = (D.a * D.a ^ D.d)⁻¹ := by
    have heq : D.a * D.a ^ D.d = D.a ^ (1 + D.d) := by
      rw [Real.rpow_add ha, Real.rpow_one]
    rw [heq, ← Real.rpow_neg ha.le]
    congr 1
    ring
  refine ⟨F, ?_, ?_⟩
  · have hh := (le_div_iff₀ (mul_pos ha hW)).mpr hFweighted
    simpa only [div_eq_mul_inv, ← hrpow] using hh
  · intro l hl t ht hinc
    obtain ⟨i, hlB, htB⟩ := hinc
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, l, hlB, hl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hiS, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨⌊t / D.a⌋, ?_, ?_⟩
    · apply hIcover i t
      convert h.block_time_gap (D.j i) htB using 1 <;> field_simp <;> ring
    · exact Finset.mem_product.mpr ⟨Finset.mem_singleton_self _,
        hJcover i _ _ (h.scalar_near_label_signal g i hlB hl.1 hl.2 htB)⟩

end DepthData
end
end Submission.Obl.k4_horizontal_coefficient_count
