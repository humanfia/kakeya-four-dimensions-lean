import Submission.Obl.k4_quadratic_sheet_continuation.PowerJets
import Submission.Obl.k4_quadratic_sheet_continuation.TubeGeometry
import Submission.Obl.k4_quadratic_sheet_continuation.TaylorControl

/-!
# From directional jet propagation to endpoint norms and Fréchet jets

This is a calculus and geometry reduction. The algebraic data occur only in
the one-dimensional directional hypothesis.
-/

namespace Submission.Obl.k4_quadratic_sheet_continuation

open Set Metric Filter
open scoped Topology ContDiff

/-- A one-dimensional jet-to-endpoint bound on every admissible affine slice
implies the two-piece path comparison, uniformly in the base dimension. -/
theorem tube_norm_jet_comparison_of_directional (N s : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ q : ℕ, ∃ C : ℝ, s ≤ q ∧ N ≤ q ∧ 0 < C ∧
      ∀ (n : ℕ) (A : ℝ), 2 ≤ A →
        ∀ (a b c : EuclideanSpace ℂ (Fin n)), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 →
          ∀ (H : EuclideanSpace ℂ (Fin n) → ℂ),
            let U := thickening A⁻¹ (segment ℝ a b ∪ segment ℝ b c)
            ContDiffOn ℂ ∞ H U →
            (∀ (p v : EuclideanSpace ℂ (Fin n)),
              MapsTo (fun t : ℂ => p + t • v)
                (thickening ((8 * A)⁻¹) (segment ℝ (0 : ℂ) 1)) U →
              ∀ W : ℝ, 0 ≤ W →
                (∀ j : ℕ, j ≤ N → ‖iteratedDeriv j (fun t : ℂ => H (p + t • v)) 0‖ ≤ W) →
                ‖H (p + v)‖ ≤ (8 * A) ^ K * W) →
            ∀ V : ℝ, 0 ≤ V →
              ((∀ z ∈ closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ V) →
                (∀ z ∈ closedBall c ((8 * A)⁻¹), ‖H z‖ ≤ A ^ C * V) ∧
                ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ A ^ C * V) ∧
              ((∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ V) →
                ∀ z ∈ closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ A ^ C * V) := by
  let q := max s N
  have hNq : N ≤ q := le_max_right _ _
  obtain ⟨L, hL, hcauchy⟩ := exists_power_jet_ball_bound q
  let S : ℝ := 4 * K + ((2 * N : ℕ) : ℝ)
  have hS : 0 < S := by dsimp [S]; positivity
  let C : ℝ := L + (S + (L + (S + L)))
  refine ⟨q, C, le_max_left _ _, hNq, by dsimp [C]; positivity, ?_⟩
  intro n A hA a b c ha hb hc H U₀ hf hprop V hV
  let path := segment ℝ a b ∪ segment ℝ b c
  let U := thickening A⁻¹ path
  let r := (8 * A)⁻¹
  have hApos : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have hrhalf : r ≤ (1 : ℝ) / 2 := by
    have hprod : (8 * A) * r = 1 := by
      dsimp [r]
      rw [mul_inv_cancel₀ (by positivity : 8 * A ≠ 0)]
    nlinarith [mul_le_mul_of_nonneg_right hA hr.le]
  have h8r : 8 * r = A⁻¹ := by dsimp [r]; field_simp
  have hU : IsOpen U := isOpen_thickening
  have haPath : a ∈ path := Or.inl (left_mem_segment ℝ a b)
  have hbPath : b ∈ path := Or.inl (right_mem_segment ℝ a b)
  have hcPath : c ∈ path := Or.inr (right_mem_segment ℝ b c)
  have hcollapse (x y Z : ℝ) : A ^ x * (A ^ y * Z) = A ^ (x + y) * Z := by
    rw [Real.rpow_add hApos]
    ring
  have hfactor : (8 * A) ^ K ≤ A ^ (4 * K) := by
    have h8 : (8 : ℝ) ≤ A ^ 3 := by
      calc
        (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ A ^ 3 := pow_le_pow_left₀ (by norm_num) hA _
    have h8A : 8 * A ≤ A ^ 4 := by
      calc
        8 * A ≤ A ^ 3 * A := mul_le_mul_of_nonneg_right h8 hApos.le
        _ = A ^ 4 := by ring
    calc
      (8 * A) ^ K ≤ (A ^ (4 : ℕ)) ^ K := Real.rpow_le_rpow (by positivity) h8A hK.le
      _ = A ^ (4 * K) := by
        rw [← Real.rpow_natCast A 4, ← Real.rpow_mul hApos.le]
        norm_num
  have hpointU (p : EuclideanSpace ℂ (Fin n)) (hp : p ∈ path) : p ∈ U := by
    exact mem_thickening_iff.mpr ⟨p, hp, by simpa using inv_pos.mpr hApos⟩
  have hjetFromNorm (p : EuclideanSpace ℂ (Fin n)) (hp : p ∈ path)
      (M : ℝ) (hM : 0 ≤ M) (hnorm : ∀ z ∈ closedBall p r, ‖H z‖ ≤ M) :
      ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H p‖ ≤ A ^ L * M := by
    apply hcauchy n A hA p H M hM
    · exact hf.mono (ball_subset_thickening hp A⁻¹)
    · exact hnorm
  have hmove (p e : EuclideanSpace ℂ (Fin n)) (hp : ‖p‖ ≤ 1) (he : ‖e‖ ≤ 1)
      (hseg : segment ℝ p e ⊆ path) (W : ℝ) (hW : 0 ≤ W)
      (hjet : ∀ j : ℕ, j ≤ N → ‖iteratedFDeriv ℂ j H p‖ ≤ W) :
      ∀ d ∈ closedBall e (2 * r), ‖H d‖ ≤ A ^ S * W := by
    intro d hd
    obtain ⟨hv, hmap⟩ := perturbed_segment_slice_mapsTo hr hrhalf hp he hd
    have hmapU : MapsTo (fun t : ℂ => p + t • (d - p))
        (thickening ((8 * A)⁻¹) (segment ℝ (0 : ℂ) 1)) U := by
      intro t ht
      have hm := hmap ht
      rw [h8r] at hm
      obtain ⟨y, hy, hty⟩ := mem_thickening_iff.mp hm
      exact mem_thickening_iff.mpr ⟨y, hseg hy, hty⟩
    have hpU : p ∈ U := hpointU p (hseg (left_mem_segment ℝ p e))
    have hslice : ∀ j : ℕ, j ≤ N →
        ‖iteratedDeriv j (fun t : ℂ => H (p + t • (d - p))) 0‖ ≤
          A ^ (((2 * N : ℕ) : ℝ)) * W := by
      intro j hj
      rw [iteratedDeriv_affine_slice hU hf hpU (d - p) j, Real.rpow_natCast]
      have hvA : ‖d - p‖ ≤ A ^ 2 := hv.trans (by nlinarith)
      have hpow : ‖d - p‖ ^ j ≤ A ^ (2 * N) := by
        calc
          ‖d - p‖ ^ j ≤ (A ^ 2) ^ j := pow_le_pow_left₀ (norm_nonneg _) hvA _
          _ = A ^ (2 * j) := by rw [pow_mul]
          _ ≤ A ^ (2 * N) := pow_le_pow_right₀ hA1 (Nat.mul_le_mul_left 2 hj)
      calc
        ‖iteratedFDeriv ℂ j H p (fun _ => d - p)‖ ≤
            ‖iteratedFDeriv ℂ j H p‖ * ‖d - p‖ ^ j := by
          simpa only [Finset.prod_const, Finset.card_fin] using
            (iteratedFDeriv ℂ j H p).le_opNorm (fun _ => d - p)
        _ ≤ W * A ^ (2 * N) := mul_le_mul (hjet j hj) hpow (pow_nonneg (norm_nonneg _) _) hW
        _ = A ^ (2 * N) * W := mul_comm _ _
    have h := hprop p (d - p) hmapU (A ^ (((2 * N : ℕ) : ℝ)) * W)
      (by positivity) hslice
    simp only [add_sub_cancel] at h
    calc
      ‖H d‖ ≤ (8 * A) ^ K * (A ^ (((2 * N : ℕ) : ℝ)) * W) := h
      _ ≤ A ^ (4 * K) * (A ^ (((2 * N : ℕ) : ℝ)) * W) := by gcongr
      _ = A ^ S * W := hcollapse _ _ _
  have hsmallBig (p : EuclideanSpace ℂ (Fin n)) : closedBall p r ⊆ closedBall p (2 * r) :=
    closedBall_subset_closedBall (by linarith)
  have hsegAB : segment ℝ a b ⊆ path := subset_union_left
  have hsegBC : segment ℝ b c ⊆ path := subset_union_right
  have hsegCB : segment ℝ c b ⊆ path := by simpa only [segment_symm ℝ c b] using hsegBC
  have hsegBA : segment ℝ b a ⊆ path := by simpa only [segment_symm ℝ b a] using hsegAB
  constructor
  · intro hnorm
    have hja := hjetFromNorm a haPath V hV hnorm
    let M₁ := A ^ S * (A ^ L * V)
    have hM₁ : 0 ≤ M₁ := by dsimp [M₁]; positivity
    have hnormB : ∀ z ∈ closedBall b (2 * r), ‖H z‖ ≤ M₁ :=
      hmove a b ha hb hsegAB (A ^ L * V) (by positivity)
        (fun j hj => hja j (hj.trans hNq))
    have hjb := hjetFromNorm b hbPath M₁ hM₁ (fun z hz => hnormB z (hsmallBig b hz))
    let M₂ := A ^ S * (A ^ L * M₁)
    have hM₂ : 0 ≤ M₂ := by dsimp [M₂]; positivity
    have hnormC : ∀ z ∈ closedBall c (2 * r), ‖H z‖ ≤ M₂ :=
      hmove b c hb hc hsegBC (A ^ L * M₁) (by positivity)
        (fun j hj => hjb j (hj.trans hNq))
    have hjc := hjetFromNorm c hcPath M₂ hM₂ (fun z hz => hnormC z (hsmallBig c hz))
    have hfinal : A ^ L * M₂ = A ^ C * V := by
      simp only [M₂, M₁, C, hcollapse, add_assoc]
    have hAmp : 1 ≤ A ^ L := Real.one_le_rpow hA1 hL.le
    have hM₂final : M₂ ≤ A ^ C * V := by
      rw [← hfinal]
      nlinarith
    refine ⟨fun z hz => (hnormC z (hsmallBig c hz)).trans hM₂final, ?_⟩
    intro j hj
    exact (hjc j hj).trans_eq hfinal
  · intro hjet
    let M₁ := A ^ S * V
    have hM₁ : 0 ≤ M₁ := by dsimp [M₁]; positivity
    have hnormB : ∀ z ∈ closedBall b (2 * r), ‖H z‖ ≤ M₁ :=
      hmove c b hc hb hsegCB V hV (fun j hj => hjet j (hj.trans hNq))
    have hjb := hjetFromNorm b hbPath M₁ hM₁ (fun z hz => hnormB z (hsmallBig b hz))
    have hnormA := hmove b a hb ha hsegBA (A ^ L * M₁) (by positivity)
      (fun j hj => hjb j (hj.trans hNq))
    intro z hz
    calc
      ‖H z‖ ≤ A ^ S * (A ^ L * M₁) := hnormA z (hsmallBig a hz)
      _ = A ^ (S + (L + S)) * V := by simp only [M₁, hcollapse]
      _ ≤ A ^ C * V := by
        apply mul_le_mul_of_nonneg_right _ hV
        exact Real.rpow_le_rpow_of_exponent_le hA1 (by dsimp [C]; linarith)

end Submission.Obl.k4_quadratic_sheet_continuation
