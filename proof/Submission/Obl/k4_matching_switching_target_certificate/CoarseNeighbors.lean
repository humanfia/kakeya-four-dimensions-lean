-- Adapted from this LOT tree, o080/x0272 commit 4d767e4, Submission/Obl/k4_matching_geometric_path_cover/CoarseNeighbors.lean.
-- Adapted within this LOT tree from o040, session x0115, commit 561995983838,
-- Submission/Obl/k4_matching_refinement_exponent/CoarseNeighbors.lean. Existing provenance comments below are preserved.
import Submission.Obl.k4_matching_homogeneous_records.Counting

open Set

namespace Submission.Obl.k4_matching_switching_target_certificate

/-- If one color is fixed during a traversal and the two colors are neighbors
at either end, neither color moves by more than twice the neighbor bound. -/
theorem two_color_bin_step {ι : Type*} (b c : Fin 2 → ι → ℤ) (G : ℕ)
    (hb : ∀ i, |b 0 i - b 1 i| ≤ (G : ℤ))
    (hc : ∀ i, |c 0 i - c 1 i| ≤ (G : ℤ))
    (hfixed : ∃ a, b a = c a) :
    ∀ a i, |c a i - b a i| ≤ 2 * (G : ℤ) := by
  obtain ⟨a, ha⟩ := hfixed
  intro d i
  have hbi := abs_le.mp (hb i)
  have hci := abs_le.mp (hc i)
  have hai := congrFun ha i
  apply abs_le.mpr
  fin_cases a <;> fin_cases d <;> dsimp at hai ⊢ <;> constructor <;> omega

/-- Coarse bins drift linearly with the number of refresh/traversal steps.
A refresh is covered by choosing either unchanged color. -/
theorem bin_walk_bound {Ω T ι : Type*} (S : Set Ω) (τ : Ω → T)
    (b : Ω → Fin 2 → ι → ℤ) (G n : ℕ) (x : ℕ → Ω)
    (hx : ∀ p, p ≤ n → x p ∈ S)
    (hgap : ∀ y ∈ S, ∀ i, |b y 0 i - b y 1 i| ≤ (G : ℤ))
    (hstep : ∀ p, p < n → τ (x p) = τ (x (p + 1)) ∧
      ∃ a, b (x p) a = b (x (p + 1)) a) :
    τ (x n) = τ (x 0) ∧
      ∀ a i, |b (x n) a i - b (x 0) a i| ≤ ((2 * n * G : ℕ) : ℤ) := by
  have hprefix : ∀ p, p ≤ n → τ (x p) = τ (x 0) ∧
      ∀ a i, |b (x p) a i - b (x 0) a i| ≤ ((2 * p * G : ℕ) : ℤ) := by
    intro p
    induction p with
    | zero => intro _; simp
    | succ p ih =>
      intro hp
      have hp' : p < n := by omega
      obtain ⟨ht, hb⟩ := ih (by omega)
      obtain ⟨ht', hfixed⟩ := hstep p hp'
      refine ⟨ht'.symm.trans ht, ?_⟩
      intro a i
      have hs := two_color_bin_step (b (x p)) (b (x (p + 1))) G
        (hgap _ (hx p (by omega))) (hgap _ (hx (p + 1) hp)) hfixed a i
      calc
        |b (x (p + 1)) a i - b (x 0) a i| ≤
            |b (x (p + 1)) a i - b (x p) a i| + |b (x p) a i - b (x 0) a i| :=
          abs_sub_le _ _ _
        _ ≤ 2 * (G : ℤ) + ((2 * p * G : ℕ) : ℤ) := add_le_add hs (hb a i)
        _ = ((2 * (p + 1) * G : ℕ) : ℤ) := by push_cast; ring
  exact hprefix n le_rfl

/-- Both colors remain near the first starting arm, which is the common
Taylor frame used in the normalized switching experiment. -/
theorem bin_walk_first_color_bound {Ω T ι : Type*} (S : Set Ω) (τ : Ω → T)
    (b : Ω → Fin 2 → ι → ℤ) (G n : ℕ) (x : ℕ → Ω)
    (hx : ∀ p, p ≤ n → x p ∈ S)
    (hgap : ∀ y ∈ S, ∀ i, |b y 0 i - b y 1 i| ≤ (G : ℤ))
    (hstep : ∀ p, p < n → τ (x p) = τ (x (p + 1)) ∧
      ∃ a, b (x p) a = b (x (p + 1)) a) :
    ∀ a i, |b (x n) a i - b (x 0) 0 i| ≤ (((2 * n + 1) * G : ℕ) : ℤ) := by
  have hb := (bin_walk_bound S τ b G n x hx hgap hstep).2
  have hs : ∀ a i, |b (x 0) a i - b (x 0) 0 i| ≤ (G : ℤ) := by
    intro a i
    fin_cases a
    · simp
    · change |b (x 0) 1 i - b (x 0) 0 i| ≤ (G : ℤ)
      rw [abs_sub_comm]
      exact hgap (x 0) (hx 0 (Nat.zero_le n)) i
  intro a i
  calc
    |b (x n) a i - b (x 0) 0 i| ≤
        |b (x n) a i - b (x 0) a i| + |b (x 0) a i - b (x 0) 0 i| := abs_sub_le _ _ _
    _ ≤ ((2 * n * G : ℕ) : ℤ) + G := add_le_add (hb a i) (hs a i)
    _ = (((2 * n + 1) * G : ℕ) : ℤ) := by push_cast; ring

/-- A fixed time cell and a bounded integer box for both colors determine
only polynomially many record values. The domain itself may be infinite. -/
theorem coarse_record_box_count {Ω T ι : Type*} [Fintype ι]
    (S : Set Ω) (τ : Ω → T) (b : Ω → Fin 2 → ι → ℤ) (F : Ω → ℕ)
    (hdet : ∀ x ∈ S, ∀ y ∈ S, τ x = τ y → b x = b y → F x = F y)
    (x₀ : Ω) (G : ℕ) :
    let B := {x | x ∈ S ∧ τ x = τ x₀ ∧
      ∀ a i, |b x a i - b x₀ a i| ≤ (G : ℤ)}
    (F '' B).Finite ∧ (F '' B).ncard ≤ (2 * G + 1) ^ (2 * Fintype.card ι) := by
  classical
  dsimp only
  let B := {x | x ∈ S ∧ τ x = τ x₀ ∧
    ∀ a i, |b x a i - b x₀ a i| ≤ (G : ℤ)}
  let P := Fin 2 → ι → {z : ℤ // z ∈ Finset.Icc (-(G : ℤ)) G}
  let code : B → P := fun x a i =>
    ⟨b x a i - b x₀ a i, Finset.mem_Icc.mpr (abs_le.mp (x.property.2.2 a i))⟩
  have hc : ∀ x y : B, code x = code y → F x = F y := by
    intro x y hxy
    apply hdet x x.property.1 y y.property.1
      (x.property.2.1.trans y.property.2.1.symm)
    funext a i
    have hh := congrArg (fun g : P => (g a i).val) hxy
    dsimp only [code] at hh
    omega
  obtain ⟨hfin, hcard⟩ :=
    Submission.Obl.k4_matching_homogeneous_records.finite_image_ncard_le_of_determines
      B F code hc
  refine ⟨hfin, hcard.trans_eq ?_⟩
  simp only [P, Fintype.card_fun, Fintype.card_fin,
    Submission.Obl.k4_matching_homogeneous_records.offset_card]
  rw [← pow_mul]
  congr 1
  omega

/-- Integer-bin proximity controls the original real values, uniformly in
the common positive scale. -/
theorem real_gap_of_floor_gap {w y z G : ℝ} (hw : 0 < w)
    (hgap : |(Int.floor (w * y) : ℝ) - (Int.floor (w * z) : ℝ)| ≤ G) :
    |y - z| ≤ (G + 1) / w := by
  have hy := Int.floor_le (w * y)
  have hy' := Int.lt_floor_add_one (w * y)
  have hz := Int.floor_le (w * z)
  have hz' := Int.lt_floor_add_one (w * z)
  have hg := abs_le.mp hgap
  rw [abs_le]
  constructor
  · rw [← neg_div, div_le_iff₀ hw]
    nlinarith
  · rw [le_div_iff₀ hw]
    nlinarith

end Submission.Obl.k4_matching_switching_target_certificate
