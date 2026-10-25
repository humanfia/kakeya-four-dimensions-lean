-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.ScaleClasses.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.CoverGeometry

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set

lemma real_size_color (q : ℕ) (R : ℝ) (hq : 0 < q) (hR : 1 < R) :
    ∃ color : ℝ → Fin q, ∀ a b : ℝ, 1 ≤ a → a < R ^ q → 1 ≤ b → b < R ^ q →
      color a = color b → a ≤ R * b := by
  classical
  have hex (a : ℝ) := exists_nat_pow_near (le_max_right a 1) hR
  let k : ℝ → ℕ := fun a => Nat.find (hex a)
  have hspec (a : ℝ) (ha : 1 ≤ a) : R ^ k a ≤ a ∧ a < R ^ (k a + 1) := by
    simpa only [k, max_eq_left ha] using Nat.find_spec (hex a)
  have hk (a : ℝ) (ha : 1 ≤ a) (haq : a < R ^ q) : k a < q :=
    (pow_lt_pow_iff_right₀ hR).mp ((hspec a ha).1.trans_lt haq)
  let color : ℝ → Fin q := fun a => if h : 1 ≤ a ∧ a < R ^ q then ⟨k a, hk a h.1 h.2⟩ else ⟨0, hq⟩
  refine ⟨color, ?_⟩
  intro a b ha haq hb hbq he
  have he' : k a = k b := by
    have hh := congrArg Fin.val he
    simpa [color, ha, haq, hb, hbq] using hh
  calc
    a ≤ R ^ (k a + 1) := (hspec a ha).2.le
    _ = R * R ^ k b := by rw [he', pow_succ, mul_comm]
    _ ≤ R * b := mul_le_mul_of_nonneg_left (hspec b hb).1 (by linarith)

/-- A bounded scale class retains a fixed share of leaves, including multiplicity
under their parent map. -/
theorem synchronize_scales {n m q : ℕ} (hn : 0 < n) (p : Fin n → Fin m)
    (ρ : Fin m → ℝ) {a b B : ℝ} (ha : 0 < a) (hq : 0 < q) (hB : 1 < B)
    (hρlo : ∀ i, a ≤ ρ i) (hρhi : ∀ i, ρ i ≤ b) (hab : b / a < B ^ q) :
    ∃ P : Finset (Fin m), P.Nonempty ∧ ∃ r : ℝ, 0 < r ∧
      (n : ℝ) ≤ q * (Finset.univ.filter (fun i => p i ∈ P)).card ∧
      1024 * a ≤ r ∧ r ≤ 1024 * b ∧
      ∀ i ∈ P, 1024 * ρ i ≤ r ∧ r ≤ 1024 * B * ρ i := by
  classical
  obtain ⟨color, hcolor⟩ := real_size_color q B hq hB
  obtain ⟨c, hc⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.weighted_color hq Finset.univ
    (fun i => color (ρ (p i) / a)) (fun _ => 1)
  let P := Finset.univ.filter fun i => color (ρ i / a) = c
  have hmass : (n : ℝ) ≤ q * (Finset.univ.filter (fun i => p i ∈ P)).card := by
    have he : Finset.univ.filter (fun i : Fin n => p i ∈ P) =
        Finset.univ.filter (fun i => color (ρ (p i) / a) = c) := by ext i; simp [P]
    rw [he]
    have hh : (n : ENNReal) ≤ (q : ENNReal) *
        (Finset.univ.filter (fun i : Fin n => color (ρ (p i) / a) = c)).card := by simpa using hc
    exact_mod_cast hh
  have hP : P.Nonempty := by
    by_contra he
    have he' : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have hh : (n : ℝ) ≤ 0 := by simpa only [he', Finset.notMem_empty, Finset.filter_false,
      Finset.card_empty, Nat.cast_zero, mul_zero] using hmass
    exact (not_le_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)) hh
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image P ρ hP
  refine ⟨P, hP, 1024 * ρ i, mul_pos (by norm_num) (ha.trans_le (hρlo i)), hmass,
    mul_le_mul_of_nonneg_left (hρlo i) (by norm_num),
    mul_le_mul_of_nonneg_left (hρhi i) (by norm_num), ?_⟩
  intro j hj
  refine ⟨mul_le_mul_of_nonneg_left (hmax j hj) (by norm_num), ?_⟩
  have hclass := hcolor (ρ i / a) (ρ j / a)
    ((one_le_div ha).mpr (hρlo i)) ((div_le_div_of_nonneg_right (hρhi i) ha.le).trans_lt hab)
    ((one_le_div ha).mpr (hρlo j)) ((div_le_div_of_nonneg_right (hρhi j) ha.le).trans_lt hab)
    ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have hcomp : ρ i ≤ B * ρ j := by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right ha] at hclass
    exact hclass
  nlinarith only [hcomp]

end WangZahlLot.Obl.wz_multiscale_finite_tower
